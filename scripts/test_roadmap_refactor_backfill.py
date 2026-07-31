#!/usr/bin/env python3
"""Pure unit tests for the reversible refactor-roadmap migration."""

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
        migration.validate_manifest_record(self.record(), {"PDE"})

    def test_tampered_body_fails(self):
        record = self.record()
        record["new_body"] += " changed"
        with self.assertRaisesRegex(ValueError, "new body hash"):
            migration.validate_manifest_record(record, {"PDE"})

    def test_requires_evidence(self):
        record = self.record()
        record["roadmap_quote"] = ""
        with self.assertRaisesRegex(ValueError, "roadmap_quote"):
            migration.validate_manifest_record(record, {"PDE"})

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


if __name__ == "__main__":
    unittest.main()
