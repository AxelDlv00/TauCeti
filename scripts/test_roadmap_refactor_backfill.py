#!/usr/bin/env python3
"""Pure unit tests for the reversible refactor-roadmap migration."""

import pathlib
import tempfile
import unittest
from unittest import mock

import roadmap_refactor_backfill as migration


class BodyInsertion(unittest.TestCase):
    def test_inserts_before_codex_footer_without_changing_prefix(self):
        body = "This PR does a thing.\n\n:robot: Prepared with OpenAI Codex\n"
        expected = (
            "This PR does a thing.\n\nRoadmap: PDE\n\n"
            ":robot: Prepared with OpenAI Codex\n"
        )
        self.assertEqual(migration.insert_roadmap_line(body, "PDE"), expected)

    def test_inserts_before_claude_footer_and_preserves_marker(self):
        marker = '<!--tauceti-target:v1 {"focus":"PDE","id":"x"}-->'
        body = f"This PR does a thing.\r\n\r\n{marker}\r\n\r\n🤖 Prepared with Claude Code"
        result = migration.insert_roadmap_line(body, "PDE")
        self.assertIn(marker, result)
        self.assertEqual(result.count(marker), 1)
        self.assertTrue(result.endswith("🤖 Prepared with Claude Code"))
        self.assertIn("\r\nRoadmap: PDE\r\n\r\n🤖", result)

    def test_appends_without_footer(self):
        self.assertEqual(
            migration.insert_roadmap_line("This PR does a thing.", "PDE"),
            "This PR does a thing.\n\nRoadmap: PDE",
        )

    def test_existing_matching_line_is_idempotent(self):
        body = "This PR does a thing.\n\nRoadmap: PDE"
        self.assertEqual(migration.insert_roadmap_line(body, "PDE"), body)

    def test_existing_other_line_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "already contains"):
            migration.insert_roadmap_line("Roadmap: none", "PDE")


class ManifestValidation(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.roadmap_dir = pathlib.Path(self.temp.name)
        roadmap = self.roadmap_dir / "TauCetiRoadmap" / "PDE"
        roadmap.mkdir(parents=True)
        (roadmap / "README.md").write_text(
            "# PDE\n\n"
            "```sh\n#949 not a heading\n```\n\n"
            "## Lane A\n\nBuild the estimate.\n\n"
            "## Lane B\n\nSharpen the constant.\n",
            encoding="utf-8",
        )

    def tearDown(self):
        self.temp.cleanup()

    def record(self):
        old = "This PR does a thing."
        new = "This PR does a thing.\n\nRoadmap: PDE"
        return {
            "pr": 1,
            "roadmap": "PDE",
            "roadmap_file": "TauCetiRoadmap/PDE/README.md",
            "roadmap_heading": "Lane A",
            "roadmap_quote": "Build the estimate.",
            "provenance": ["#2"],
            "title": "refactor: share the estimate",
            "old_body": old,
            "old_body_sha256": migration.body_hash(old),
            "old_roadmap_labels": ["roadmap/none"],
            "new_body": new,
            "new_body_sha256": migration.body_hash(new),
        }

    def test_valid_record(self):
        migration.validate_manifest_record(self.record(), {"PDE"}, self.roadmap_dir)

    def test_matching_existing_area_label_is_valid_rollback_state(self):
        record = self.record()
        record["old_roadmap_labels"] = ["roadmap/PDE"]
        migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_tampered_body_fails(self):
        record = self.record()
        record["new_body"] += " changed"
        with self.assertRaisesRegex(ValueError, "new body hash"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_requires_evidence(self):
        record = self.record()
        record["roadmap_quote"] = ""
        with self.assertRaisesRegex(ValueError, "roadmap_quote"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_evidence_must_resolve_in_the_declared_roadmap(self):
        record = self.record()
        record["roadmap_heading"] = "Lane Z"
        with self.assertRaisesRegex(ValueError, "exact Markdown heading"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_quote_from_another_section_is_rejected(self):
        record = self.record()
        record["roadmap_quote"] = "Sharpen the constant."
        with self.assertRaisesRegex(ValueError, "under the cited roadmap_heading"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_fenced_hash_line_is_not_a_heading(self):
        record = self.record()
        record["roadmap_heading"] = "949 not a heading"
        record["roadmap_quote"] = "Build the estimate."
        with self.assertRaisesRegex(ValueError, "exact Markdown heading"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_free_text_provenance_is_rejected(self):
        record = self.record()
        record["provenance"] = ["garbage"]
        with self.assertRaisesRegex(ValueError, "not a #N or pull-request URL"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_provenance_cannot_cite_the_migrated_pr(self):
        record = self.record()
        record["provenance"] = ["#1"]
        with self.assertRaisesRegex(ValueError, "cannot cite the PR being migrated"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_evidence_path_cannot_escape_checkout(self):
        record = self.record()
        record["roadmap_file"] = "../README.md"
        with self.assertRaisesRegex(ValueError, "stay inside"):
            migration.validate_manifest_record(record, {"PDE"}, self.roadmap_dir)

    def test_tranche_limit(self):
        with self.assertRaisesRegex(ValueError, "between 1 and 20"):
            migration.select_tranche([], 0, 21)

    def test_revert_checks_applied_state_then_restores(self):
        record = self.record()
        with (
            mock.patch.object(migration, "check_current") as check,
            mock.patch.object(migration, "restore_record") as restore,
        ):
            migration.revert_record("owner/repo", record, {"PDE"})
        self.assertEqual(
            check.call_args_list,
            [
                mock.call("owner/repo", record, {"PDE"}, applied=True),
                mock.call("owner/repo", record, {"PDE"}, applied=False),
            ],
        )
        restore.assert_called_once_with("owner/repo", record, {"PDE"})


class ProvenanceResolution(unittest.TestCase):
    """`verify_provenance` is what stops a citation from being mere assertion."""

    def record(self, provenance=("#2",)):
        return {"pr": 1, "roadmap": "PDE", "provenance": list(provenance)}

    def source(self, **overrides):
        state = {
            "state": "MERGED",
            "title": "feat: build the estimate",
            "body": "This PR builds it.\n\nRoadmap: PDE",
            "files": [{"path": "TauCeti/PDE/Estimate.lean"}],
            "labels": [{"name": "roadmap/PDE"}],
        }
        state.update(overrides)
        return state

    def verify(self, state, target=("TauCeti/PDE/Estimate.lean",), provenance=("#2",)):
        with mock.patch.object(migration, "pr_state", return_value=state):
            migration.verify_provenance(
                "owner/repo", self.record(provenance), {"PDE"}, list(target))

    def test_merged_same_area_overlapping_pr_is_accepted(self):
        self.verify(self.source())

    def test_label_alone_suffices_when_the_body_predates_declarations(self):
        self.verify(self.source(body="This PR builds it."))

    def test_pr_attributed_elsewhere_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "not attributed to PDE"):
            self.verify(self.source(body="Roadmap: none", labels=[]))

    def test_unmerged_pr_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "not merged"):
            self.verify(self.source(state="OPEN"))

    def test_pr_sharing_no_file_with_the_target_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "does not connect it to PDE"):
            self.verify(self.source(), target=("TauCeti/Other/Thing.lean",))

    def test_foreign_repository_reference_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "not a owner/repo pull request"):
            self.verify(
                self.source(),
                provenance=("https://github.com/other/repo/pull/2",),
            )


if __name__ == "__main__":
    unittest.main()
