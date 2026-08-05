#!/usr/bin/env python3
"""Unit tests for bump_autofix.py.

Missing a rename is cheap — the bump stays red as it was. An edit landing where the
compiler did not point is not: it burns an 85-minute rebuild, or, from a forged log,
writes outside the library. So most of what is asserted here is what the worker refuses
to touch. The fixture is the real diagnostic from run 30963915259, which stranded #1986,
with the prefix `gh run view --log-failed` puts on every line.

Run: python3 scripts/test_bump_autofix.py
"""

import os
import tempfile
import unittest

import bump_autofix as ba

# Two real diagnostics, with the log prefix they arrive with.
REAL_LOG = (
    "sandboxed-build\tUNKNOWN STEP\t2026-08-05T01:20:29.1227782Z error: "
    "TauCeti/NumberTheory/ModularForms/DiamondOperators.lean:99:8: "
    "`ModularForm.IsGLPos.coe_smul` has been deprecated: Use `FunLike.coe_smul` instead\n"
    "sandboxed-build\tUNKNOWN STEP\t2026-08-05T01:20:29.1231351Z error: "
    "TauCeti/NumberTheory/ModularForms/DiamondOperators.lean:187:8: "
    "`CuspForm.IsGLPos.coe_smul` has been deprecated: Use `FunLike.coe_smul` instead\n"
)


class ParseTest(unittest.TestCase):
    def test_parses_the_real_diagnostics(self):
        got = ba.renames_from_log(REAL_LOG)
        self.assertEqual(
            [(r.path, r.line, r.col, r.old, r.new) for r in got],
            [("TauCeti/NumberTheory/ModularForms/DiamondOperators.lean", 99, 8,
              "ModularForm.IsGLPos.coe_smul", "FunLike.coe_smul"),
             ("TauCeti/NumberTheory/ModularForms/DiamondOperators.lean", 187, 8,
              "CuspForm.IsGLPos.coe_smul", "FunLike.coe_smul")])

    def test_lowercase_use_is_accepted(self):
        log = ("warning: TauCeti/A.lean:3:0: `Old.name` has been deprecated: "
               "use `New.name` instead (since 2026-01-01)\n")
        self.assertEqual([r.new for r in ba.renames_from_log(log)], ["New.name"])

    def test_repeated_diagnostic_is_applied_once(self):
        self.assertEqual(len(ba.renames_from_log(REAL_LOG + REAL_LOG)), 2)

    def test_paths_outside_tauceti_are_ignored(self):
        # A mathlib-internal deprecation is not ours to rewrite.
        log = (".lake/packages/mathlib/Mathlib/X.lean:1:0: `A.b` has been "
               "deprecated: Use `C.d` instead\n")
        self.assertEqual(ba.renames_from_log(log), [])

    def test_deprecation_without_a_replacement_is_reported_not_fixed(self):
        log = ("TauCeti/A.lean:3:0: `Old.name` has been deprecated: "
               "this abstraction was a mistake\n")
        self.assertEqual(ba.renames_from_log(log), [])
        self.assertEqual([t[3] for t in ba.unfixable_from_log(log)], ["Old.name"])

    def test_unknown_identifier_is_reported_not_fixed(self):
        log = "TauCeti/A.lean:3:0: unknown identifier 'Foo.bar'\n"
        self.assertEqual(ba.renames_from_log(log), [])
        self.assertEqual([t[3] for t in ba.unfixable_from_log(log)], ["Foo.bar"])

    def test_a_fixed_deprecation_is_not_also_reported_unfixable(self):
        self.assertEqual(ba.unfixable_from_log(REAL_LOG), [])


class ApplyTest(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()

    def _write(self, rel, text):
        path = os.path.join(self.root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(text)
        return path

    def _read(self, rel):
        with open(os.path.join(self.root, rel), encoding="utf-8") as fh:
            return fh.read()

    def test_replaces_the_token_at_the_reported_position(self):
        rel = "TauCeti/NumberTheory/ModularForms/DiamondOperators.lean"
        self._write(rel, "\n" * 98 +
                    "    rw [ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash]\n")
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(REAL_LOG))
        self.assertEqual(len(applied), 1)      # line 187 is past this fixture's end
        self.assertEqual(len(skipped), 1)
        self.assertIn("    rw [FunLike.coe_smul, ModularForm.smul_slash]", self._read(rel))

    def test_other_occurrences_of_the_name_are_left_alone(self):
        # One diagnostic per occurrence, so anchoring still reaches them all — and a
        # file-wide substitution would rewrite the name in prose too.
        rel = "TauCeti/A.lean"
        self._write(rel, "-- Old.name was the old spelling.\nexact Old.name h\n")
        log = "TauCeti/A.lean:2:6: `Old.name` has been deprecated: Use `New.name` instead\n"
        applied, _ = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(len(applied), 1)
        self.assertEqual(self._read(rel), "-- Old.name was the old spelling.\nexact New.name h\n")

    def test_unqualified_occurrence_is_replaced_with_the_full_new_name(self):
        # The source may write a suffix; the replacement is fully qualified because the
        # worker cannot know what is open there.
        rel = "TauCeti/A.lean"
        self._write(rel, "  rw [IsGLPos.coe_smul]\n")
        log = ("TauCeti/A.lean:1:6: `ModularForm.IsGLPos.coe_smul` has been "
               "deprecated: Use `FunLike.coe_smul` instead\n")
        applied, _ = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(len(applied), 1)
        self.assertEqual(self._read(rel), "  rw [FunLike.coe_smul]\n")

    def test_refuses_a_partial_token(self):
        # `Old.named` starts with `Old.name`; rewriting its prefix invents `New.named`.
        rel = "TauCeti/A.lean"
        self._write(rel, "exact Old.named h\n")
        log = "TauCeti/A.lean:1:6: `Old.name` has been deprecated: Use `New.name` instead\n"
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(applied, [])
        self.assertIn("the source has moved", skipped[0][1])
        self.assertEqual(self._read(rel), "exact Old.named h\n")

    def test_refuses_when_the_log_is_stale(self):
        rel = "TauCeti/A.lean"
        self._write(rel, "exact something_else h\n")
        log = "TauCeti/A.lean:1:6: `Old.name` has been deprecated: Use `New.name` instead\n"
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(applied, [])
        self.assertEqual(self._read(rel), "exact something_else h\n")

    def test_missing_file_is_skipped_not_fatal(self):
        log = "TauCeti/Gone.lean:1:0: `A.b` has been deprecated: Use `C.d` instead\n"
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(applied, [])
        self.assertIn("not a regular file", skipped[0][1])

    def test_two_renames_on_one_line_both_land(self):
        # Right-to-left, so one edit cannot shift the next one's column.
        rel = "TauCeti/A.lean"
        self._write(rel, "rw [A.one, A.two]\n")
        log = ("TauCeti/A.lean:1:4: `A.one` has been deprecated: Use `B.uno` instead\n"
               "TauCeti/A.lean:1:11: `A.two` has been deprecated: Use `B.dos` instead\n")
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(len(applied), 2, skipped)
        self.assertEqual(self._read(rel), "rw [B.uno, B.dos]\n")

    def test_columns_are_codepoints_not_bytes(self):
        # Byte offsets would land mid-name on any line with a `ℂ` before the token.
        rel = "TauCeti/A.lean"
        self._write(rel, "  fun z : ℂ ↦ Old.name z\n")
        col = len("  fun z : ℂ ↦ ")   # 14 codepoints, 20 bytes
        log = (f"TauCeti/A.lean:1:{col}: `Old.name` has been deprecated: "
               f"Use `New.name` instead\n")
        applied, _ = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(len(applied), 1)
        self.assertEqual(self._read(rel), "  fun z : ℂ ↦ New.name z\n")

    def test_no_trailing_newline_is_not_invented(self):
        rel = "TauCeti/A.lean"
        self._write(rel, "exact Old.name h")
        log = "TauCeti/A.lean:1:6: `Old.name` has been deprecated: Use `New.name` instead\n"
        ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(self._read(rel), "exact New.name h")


class ContainmentTest(unittest.TestCase):
    """A forged log line must not steer an edit out of TauCeti/. The edits are committed
    with an App token, so "the path came from the log" is never sufficient."""

    def setUp(self):
        self.root = tempfile.mkdtemp()
        os.makedirs(os.path.join(self.root, "TauCeti", "A"), exist_ok=True)
        os.makedirs(os.path.join(self.root, "scripts"), exist_ok=True)

    def _write(self, rel, text):
        path = os.path.join(self.root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(text)

    def _log(self, path):
        return (f"{path}:1:6: `Old.name` has been deprecated: Use `New.name` instead\n")

    def test_a_malformed_name_cannot_insert_without_matching(self):
        # `_dot_suffixes(".")` yielded "", and `startswith("")` is true everywhere — so
        # this spliced the replacement in having matched no token at all.
        self._write("TauCeti/A.lean", "exact foo bar\n")
        log = "TauCeti/A.lean:1:5: `.` has been deprecated: Use `Injected.name` instead\n"
        self.assertEqual(ba.renames_from_log(log), [])
        applied, _ = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(applied, [])
        with open(os.path.join(self.root, "TauCeti/A.lean"), encoding="utf-8") as fh:
            self.assertEqual(fh.read(), "exact foo bar\n")

    def test_names_with_an_empty_component_are_refused(self):
        for bad in ("A..b", ".b", "a."):
            for tmpl in ("`{}` has been deprecated: Use `New.name` instead",
                         "`Old.name` has been deprecated: Use `{}` instead"):
                log = "TauCeti/A.lean:1:0: " + tmpl.format(bad) + "\n"
                self.assertEqual(ba.renames_from_log(log), [], log)

    def test_a_column_inside_a_longer_identifier_is_refused(self):
        # Without a left boundary a suffix matches partway through a name.
        self._write("TauCeti/A.lean", "exact Prefix.Old.name h\n")
        log = "TauCeti/A.lean:1:13: `Old.name` has been deprecated: Use `New.name` instead\n"
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(applied, [])
        self.assertIn("mid-identifier", skipped[0][1])

    def test_the_grammar_admits_no_traversal(self):
        for path in ("TauCeti/../scripts/Axioms.lean",
                     "TauCeti/../../etc/passwd.lean",
                     "TauCeti/./x.lean"):
            self.assertEqual(ba.renames_from_log(self._log(path)), [], path)

    def test_resolution_refuses_independently_of_the_grammar(self):
        for path in ("../scripts/Axioms.lean", "/etc/passwd", "TauCeti/../scripts/x.lean"):
            self.assertIsNone(ba._resolve_under(self.root, path), path)
        for path in ("TauCeti/A/B.lean", "TauCeti.lean"):
            self.assertIsNotNone(ba._resolve_under(self.root, path), path)

    def test_a_symlink_out_of_the_library_is_not_followed(self):
        self._write("scripts/Axioms.lean", "exact Old.name h\n")
        os.symlink(os.path.join(self.root, "scripts", "Axioms.lean"),
                   os.path.join(self.root, "TauCeti", "Escape.lean"))
        log = self._log("TauCeti/Escape.lean")
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(applied, [])
        self.assertEqual(len(skipped), 1)
        with open(os.path.join(self.root, "scripts", "Axioms.lean"), encoding="utf-8") as fh:
            self.assertEqual(fh.read(), "exact Old.name h\n")

    def test_applied_files_lists_only_what_was_edited(self):
        self._write("TauCeti/A/B.lean", "exact Old.name h\n")
        log, out = (os.path.join(self.root, n) for n in ("build.log", "applied.txt"))
        with open(log, "w", encoding="utf-8") as fh:
            fh.write(self._log("TauCeti/A/B.lean")
                     + self._log("TauCeti/../scripts/Axioms.lean"))
        self.assertEqual(0, ba.main(["bump_autofix.py", "--log", log, "--root", self.root,
                                     "--applied-files", out]))
        with open(out, encoding="utf-8") as fh:
            self.assertEqual(fh.read().split(), ["TauCeti/A/B.lean"])


class SummaryTest(unittest.TestCase):
    def test_summary_names_every_outcome(self):
        applied = ba.renames_from_log(REAL_LOG)[:1]
        skipped = [(ba.renames_from_log(REAL_LOG)[1], "the source has moved")]
        unfixable = [("TauCeti/A.lean", 3, 0, "Foo.bar", "unknown identifier")]
        text = ba.summary(applied, skipped, unfixable)
        self.assertIn("Applied 1 mechanical rename", text)
        self.assertIn("Skipped 1 rename", text)
        self.assertIn("need a human", text)
        self.assertIn("Foo.bar", text)

    def test_summary_when_nothing_applied(self):
        self.assertIn("Applied no renames.", ba.summary([], [], []))


if __name__ == "__main__":
    unittest.main()
