#!/usr/bin/env python3
"""Unit tests for the merge-queue reservation in bump_lock.py.

The two ways this can be wrong are not symmetric. Failing to hold the lock costs the
bump one day; holding it wrongly stops every merge in the repository. So the tests here
concentrate on the release conditions -- a queued bump never blocks itself, an old hold
expires, an unreadable queue fails open -- rather than on the happy path.

Pure logic: `decide` takes the GraphQL nodes as data, so nothing here touches a network.
Run: python3 scripts/test_bump_lock.py
"""

import datetime
import io
import unittest
from contextlib import redirect_stdout

import bump_lock as bl

NOW = datetime.datetime(2026, 8, 5, 12, 0, 0, tzinfo=datetime.timezone.utc)


def _ago(hours):
    return (NOW - datetime.timedelta(hours=hours)).strftime("%Y-%m-%dT%H:%M:%SZ")


def _entry(number, files=("lake-manifest.json",), hours=0.5,
           state="AWAITING_CHECKS", branch="bump-mathlib/fix-c003275"):
    return {"enqueuedAt": _ago(hours), "state": state,
            "pullRequest": {"number": number, "headRefName": branch,
                            "files": {"nodes": [{"path": p} for p in files]}}}


def _ordinary(number, hours=0.5):
    return _entry(number, files=("TauCeti/Analysis/Foo.lean",), hours=hours,
                  branch="roadmap/foo")


class HoldTest(unittest.TestCase):
    def test_queued_pin_bump_holds_the_lock(self):
        held, reason = bl.decide([_entry(1986)], subject=2000, now=NOW)
        self.assertTrue(held)
        self.assertIn("#1986", reason)

    def test_toolchain_only_bump_holds_the_lock(self):
        held, _ = bl.decide([_entry(1986, files=("lean-toolchain",))], subject=2000, now=NOW)
        self.assertTrue(held)

    def test_the_lkg_branch_holds_even_with_an_unreadable_file_list(self):
        # Name and property are both accepted, so the daily bump still reserves when the
        # files connection comes back empty.
        held, _ = bl.decide([_entry(9, files=(), branch=bl.LKG_BRANCH)],
                            subject=2000, now=NOW)
        self.assertTrue(held)

    def test_ordinary_prs_in_the_queue_hold_nothing(self):
        held, reason = bl.decide([_ordinary(2001), _ordinary(2002)], subject=2000, now=NOW)
        self.assertFalse(held)
        self.assertIn("no pin bump", reason)

    def test_empty_queue(self):
        held, _ = bl.decide([], subject=2000, now=NOW)
        self.assertFalse(held)

    def test_unknown_entry_state_still_holds(self):
        # A state we do not recognise still occupies the queue. Recognising states by
        # allowlist would silently stop reserving the moment GitHub adds one.
        held, _ = bl.decide([_entry(1986, state="SOMETHING_NEW")], subject=2000, now=NOW)
        self.assertTrue(held)


class NeverBlocksItselfTest(unittest.TestCase):
    def test_the_bump_asking_about_itself_is_free(self):
        held, reason = bl.decide([_entry(1986)], subject=1986, now=NOW)
        self.assertFalse(held)
        self.assertIn("reserved for it", reason)

    def test_subject_is_compared_numerically(self):
        # Workflows pass the PR number through as a string; a string/int mismatch here
        # would lock the bump out of the very queue the lock reserves for it.
        held, _ = bl.decide([_entry(1986)], subject="1986", now=NOW)
        self.assertFalse(held)

    def test_an_earlier_bump_entry_cannot_lock_a_later_one_out(self):
        # The subject check must span the whole queue, not stop at the first bump entry.
        held, _ = bl.decide([_entry(1985), _entry(1986)], subject=1986, now=NOW)
        self.assertFalse(held)


class ExpiryTest(unittest.TestCase):
    def test_hold_expires(self):
        held, reason = bl.decide([_entry(1986, hours=bl.MAX_HOLD_HOURS + 0.1)],
                                 subject=2000, now=NOW)
        self.assertFalse(held)
        self.assertIn("releasing the reservation", reason)

    def test_hold_survives_up_to_the_limit(self):
        held, _ = bl.decide([_entry(1986, hours=bl.MAX_HOLD_HOURS - 0.1)],
                            subject=2000, now=NOW)
        self.assertTrue(held)

    def test_a_fresh_bump_behind_an_expired_one_still_holds(self):
        held, reason = bl.decide([_entry(1985, hours=bl.MAX_HOLD_HOURS + 1),
                                  _entry(1986, hours=0.2)], subject=2000, now=NOW)
        self.assertTrue(held)
        self.assertIn("#1986", reason)

    def test_missing_enqueue_time_holds_but_is_not_unbounded(self):
        # No clock means we cannot expire it, so it holds for now -- but only until the
        # field is readable again. What must never happen is an unexpirable hold, so the
        # entry is treated as fresh rather than as infinitely old or infinitely young.
        entry = _entry(1986)
        del entry["enqueuedAt"]
        held, _ = bl.decide([entry], subject=2000, now=NOW)
        self.assertTrue(held)


class FailOpenTest(unittest.TestCase):
    def test_query_failure_reports_free(self):
        self.addCleanup(setattr, bl, "queue_entries", bl.queue_entries)
        bl.queue_entries = lambda: (_ for _ in ()).throw(RuntimeError("502 from GitHub"))
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = bl.main(["bump_lock.py"])
        self.assertEqual(rc, 0)
        self.assertIn("held=false", buf.getvalue())
        self.assertIn("failing open", buf.getvalue())

    def test_a_truncated_file_list_is_not_a_bump(self):
        # 100 files back means the list may be cut short, so a pin change could be hidden.
        # A PR that large is not a bump, and guessing "bump" would hold the queue on it.
        big = _entry(2001, files=tuple(f"TauCeti/F{i}.lean" for i in range(100)),
                     branch="roadmap/huge")
        self.assertFalse(bl.is_bump(big["pullRequest"]))


class EmitTest(unittest.TestCase):
    def test_reason_is_flattened_to_one_line(self):
        # GITHUB_OUTPUT is line-oriented: a newline inside a value would let the rest of
        # the reason be parsed as further outputs.
        buf = io.StringIO()
        with redirect_stdout(buf):
            bl.emit(True, "two\nlines  and   spaces")
        self.assertEqual(buf.getvalue().splitlines(),
                         ["held=true", "reason=two lines and spaces"])


if __name__ == "__main__":
    unittest.main()
