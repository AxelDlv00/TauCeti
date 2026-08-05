#!/usr/bin/env python3
"""Unit tests for the mechanical rename worker in bump_autofix.py.

The dangerous failure is not "missed a rename" -- pr-build catches that and the bump
stays red exactly as it was. It is an edit that lands somewhere the compiler did not
point: a name inside a comment, a longer identifier that merely starts with the
deprecated one, a line the log is stale about. Those turn a red bump into a differently
red bump and burn an 85-minute rebuild doing it. So most of what is asserted here is
what the worker REFUSES to touch.

The log fixture is the real diagnostic from run 30963915259, the merge-group rebuild
that stranded #1986, including the job/step/timestamp prefix `gh run view --log-failed`
puts on every line.

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
        # A mathlib-internal deprecation is not ours to rewrite, and the sandbox has no
        # writable copy of it anyway.
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
        # Lean emits one diagnostic per occurrence, so a position-anchored edit still
        # reaches them all -- while a file-wide substitution would also rewrite the name
        # in prose, which is not source and may be deliberately historical.
        rel = "TauCeti/A.lean"
        self._write(rel, "-- Old.name was the old spelling.\nexact Old.name h\n")
        log = "TauCeti/A.lean:2:6: `Old.name` has been deprecated: Use `New.name` instead\n"
        applied, _ = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(len(applied), 1)
        self.assertEqual(self._read(rel), "-- Old.name was the old spelling.\nexact New.name h\n")

    def test_unqualified_occurrence_is_replaced_with_the_full_new_name(self):
        # Inside `namespace ModularForm` the source writes the suffix, but Lean reports
        # the full name. The replacement is fully qualified because this worker cannot
        # know which namespaces are open there.
        rel = "TauCeti/A.lean"
        self._write(rel, "  rw [IsGLPos.coe_smul]\n")
        log = ("TauCeti/A.lean:1:6: `ModularForm.IsGLPos.coe_smul` has been "
               "deprecated: Use `FunLike.coe_smul` instead\n")
        applied, _ = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(len(applied), 1)
        self.assertEqual(self._read(rel), "  rw [FunLike.coe_smul]\n")

    def test_refuses_a_partial_token(self):
        # `Old.named` starts with `Old.name`. Rewriting its prefix would produce
        # `New.named`, a name nobody asked for, out of an edit that looked like a match.
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
        self.assertIn("file not found", skipped[0][1])

    def test_two_renames_on_one_line_both_land(self):
        # Applied right-to-left, so the first edit cannot shift the second one's column.
        rel = "TauCeti/A.lean"
        self._write(rel, "rw [A.one, A.two]\n")
        log = ("TauCeti/A.lean:1:4: `A.one` has been deprecated: Use `B.uno` instead\n"
               "TauCeti/A.lean:1:11: `A.two` has been deprecated: Use `B.dos` instead\n")
        applied, skipped = ba.apply_renames(self.root, ba.renames_from_log(log))
        self.assertEqual(len(applied), 2, skipped)
        self.assertEqual(self._read(rel), "rw [B.uno, B.dos]\n")

    def test_columns_are_codepoints_not_bytes(self):
        # Lean reports columns in codepoints and Lean source is full of non-ASCII. Byte
        # offsets would land mid-name on every line with a `ℂ` or an `↦` before the token.
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
