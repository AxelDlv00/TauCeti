#!/usr/bin/env python3
"""Hermetic tests for scripts/pr_stats_graphs.py."""

from __future__ import annotations

import tempfile
import unittest
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch

import pr_stats_graphs as stats


UTC = timezone.utc


def timestamp(day: int, hour: int = 0) -> str:
    return datetime(2026, 1, day, hour, tzinfo=UTC).isoformat().replace("+00:00", "Z")


def pr(number, created_day, *, state="CLOSED", merged_day=None, author="alice",
       labels=(), cycles=0, is_draft=False):
    events = [
        {"created_at": timestamp(min(created_day + index, 14), 8),
         "label": "awaiting-review"}
        for index in range(cycles)
    ]
    if "awaiting-author" in labels:
        events.append({"created_at": timestamp(13, 12), "label": "awaiting-author"})
    if "review-in-progress" in labels and not cycles:
        events.append({"created_at": timestamp(13, 10), "label": "review-in-progress"})
    return {
        "number": number,
        "created_at": timestamp(created_day),
        "merged_at": timestamp(merged_day, 12) if merged_day else None,
        "closed_at": timestamp(merged_day, 12) if merged_day else None,
        "state": state,
        "is_draft": is_draft,
        "author": author,
        "labels": list(labels),
        "labeled_events": events,
    }


class MetricsTest(unittest.TestCase):
    def test_outer_pr_page_contains_no_nested_timeline(self):
        self.assertIn("pullRequests(first:100", stats.PR_PAGE_QUERY)
        self.assertNotIn("timelineItems", stats.PR_PAGE_QUERY)

    def test_direct_label_timeline_pagination_is_not_truncated(self):
        first_page = {
            "repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [{
                    "number": 42, "createdAt": timestamp(1), "mergedAt": None,
                    "closedAt": None, "state": "OPEN", "isDraft": False,
                    "author": {"login": "alice"}, "labels": {"nodes": []},
                }],
            }},
        }
        timeline_page = {
            "repository": {"pullRequest": {"timelineItems": {
                "pageInfo": {"hasNextPage": True, "endCursor": "events-100"},
                "nodes": [{"createdAt": timestamp(2),
                           "label": {"name": "awaiting-review"}}],
            }}},
        }
        timeline_extra = {
            "repository": {"pullRequest": {"timelineItems": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [{"createdAt": timestamp(3),
                           "label": {"name": "awaiting-review"}}],
            }}},
        }
        with patch.object(
            stats, "graphql", side_effect=[first_page, timeline_page, timeline_extra],
        ):
            prs = stats.fetch_prs("example/project")
        self.assertEqual(
            [event["label"] for event in prs[0]["labeled_events"]],
            ["awaiting-review", "awaiting-review"],
        )

    def test_closed_pr_uses_complete_direct_timeline(self):
        first_page = {
            "repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [{
                    "number": 42, "createdAt": timestamp(1), "mergedAt": None,
                    "closedAt": timestamp(14), "state": "CLOSED", "isDraft": False,
                    "author": {"login": "alice"},
                    "labels": {"nodes": [{"name": "roadmap/PDE"}]},
                }],
            }},
        }
        direct = {
            "repository": {"pullRequest": {"timelineItems": {
                "pageInfo": {"hasNextPage": False, "endCursor": None},
                "nodes": [
                    {"createdAt": timestamp(min(index + 1, 14)),
                     "label": {"name": "awaiting-review"}}
                    for index in range(9)
                ],
            }}},
        }
        with patch.object(stats, "graphql", side_effect=[first_page, direct]):
            prs = stats.fetch_prs("example/project")
        self.assertEqual(len(prs[0]["labeled_events"]), 9)

    def test_review_cycles_use_label_transitions_and_reach_seven(self):
        prs = [
            pr(1, 1, cycles=0),
            pr(2, 2, cycles=1),
            pr(3, 3, cycles=2),
            pr(4, 4, cycles=7),
        ]
        result = stats.review_cycle_metrics(prs)
        self.assertEqual(result["awaiting_review_transitions"], 10)
        self.assertEqual(result["reviewed_prs"], 3)
        self.assertEqual(
            [item["prs"] for item in result["reach"]],
            [3, 2, 1, 1, 1, 1, 1],
        )

    def test_queue_age_order_and_state_clocks(self):
        snapshot = datetime(2026, 1, 15, tzinfo=UTC)
        prs = [
            pr(1, 10, state="OPEN", labels=("awaiting-author",)),
            pr(2, 11, state="OPEN", labels=("review-in-progress",), cycles=2),
            pr(3, 12, state="OPEN", labels=("awaiting-CI",)),
            pr(4, 12, state="OPEN", labels=("awaiting-author",), is_draft=True),
        ]
        metrics = stats.queue_age_metrics(prs, snapshot)
        self.assertEqual(len(metrics["total_open_hours"]), 4)
        self.assertEqual(len(metrics["awaiting_author_hours"]), 1)
        self.assertEqual(len(metrics["in_review_hours"]), 1)
        self.assertEqual(metrics["other_open_prs"], 2)

    def test_generation_rejects_excessive_missing_state_transitions(self):
        prs = [
            pr(number, number, state="OPEN", labels=("awaiting-author",))
            for number in range(1, 4)
        ]
        for item in prs:
            item["labeled_events"] = []
        data = {
            "repo": "example/project", "fetched_at": timestamp(15),
            "prs": prs, "scoreboards": [],
        }
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, "matching label transitions"):
                stats.generate(data, Path(temporary))

    def test_thousands_of_contributors_are_bounded(self):
        start = datetime(2026, 1, 1, tzinfo=UTC)
        events = []
        for index in range(2_500):
            # Deterministic unequal totals make the selected top contributors stable.
            events.extend((start + timedelta(days=index % 7), f"user-{index:04d}")
                          for _ in range(1 + index % 3))
        dates, names, series, totals = stats.cumulative_chart_series(
            events, start.date(), date(2026, 1, 14), limit=12,
        )
        self.assertEqual(len(totals), 2_500)
        self.assertEqual(len(names), 13)  # top 12 + one bounded aggregate
        self.assertEqual(len(series), 13)
        self.assertTrue(names[-1].startswith("Other (2,488 contributors)"))
        self.assertTrue(all(len(values) == len(dates) for values in series.values()))


class RenderingTest(unittest.TestCase):
    def test_generate_writes_five_valid_svgs_with_requested_names(self):
        prs = [
            pr(1, 1, merged_day=2, author="alice", cycles=1),
            pr(2, 2, merged_day=5, author="bob", cycles=2),
            pr(3, 3, merged_day=9, author="alice", cycles=7),
            pr(4, 10, state="OPEN", labels=("awaiting-author",), author="carol"),
            pr(5, 11, state="OPEN", labels=("review-in-progress",), cycles=2,
               author="dave"),
            pr(6, 12, state="OPEN", labels=("awaiting-CI",), author="erin"),
        ]
        data = {
            "schema_version": 1,
            "repo": "example/project",
            "fetched_at": timestamp(15),
            "prs": prs,
            "scoreboards": [
                {"pr": 1, "created_at": timestamp(2), "updated_at": timestamp(2),
                 "user": "reviewer-a"},
                {"pr": 2, "created_at": timestamp(5), "updated_at": timestamp(5),
                 "user": "reviewer-b"},
            ],
        }
        expected = [
            "pr-queue-age.svg",
            "review-cycles-reached.svg",
            "rolling-seven-day-history.svg",
            "cumulative-merges-by-contributor.svg",
            "cumulative-reviews-by-contributor.svg",
        ]
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary)
            metrics = stats.generate(data, out, contributor_limit=2, history_days=30)
            for name in expected:
                ET.parse(out / name)
            self.assertTrue((out / "pr-stats.json").is_file())
            queue_svg = (out / "pr-queue-age.svg").read_text(encoding="utf-8")
            self.assertLess(queue_svg.index("Total time open"),
                            queue_svg.index("Awaiting author"))
            self.assertLess(queue_svg.index("Awaiting author"),
                            queue_svg.index("In review"))
            cycle_svg = (out / "review-cycles-reached.svg").read_text(encoding="utf-8")
            self.assertIn("Review cycle 7", cycle_svg)
            self.assertEqual(metrics["review_cycles"]["max_cycle"], 7)

    def test_render_failure_keeps_previous_asset_set(self):
        data = {
            "repo": "example/project", "fetched_at": timestamp(15),
            "prs": [pr(1, 1, merged_day=2, cycles=1)], "scoreboards": [],
        }
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / "assets"
            out.mkdir()
            existing = out / "pr-queue-age.svg"
            existing.write_text("previous", encoding="utf-8")
            with patch.object(
                stats, "render_review_cycles", side_effect=RuntimeError("boom"),
            ):
                with self.assertRaisesRegex(RuntimeError, "boom"):
                    stats.generate(data, out)
            self.assertEqual(existing.read_text(encoding="utf-8"), "previous")
            self.assertFalse((out / "review-cycles-reached.svg").exists())


if __name__ == "__main__":
    unittest.main()
