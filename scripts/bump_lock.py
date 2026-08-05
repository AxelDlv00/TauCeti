#!/usr/bin/env python3
"""bump_lock.py — reserve the merge queue for a mathlib bump.

The daily bump loses a race it cannot win on its own. Its merge-group rebuild takes
about 85 minutes because the new mathlib pin invalidates every one of TauCeti's own
oleans, and main merges roughly 90 PRs a day, so about eight more PRs land while that
rebuild runs. Any one of them can introduce a fresh use of a name the new mathlib
deprecates, which reddens the merge group and evicts the bump; the next attempt starts
against a main that has moved again. #1986 lost this race four times in a row against
four different main SHAs before a human fixed it by hand, and the delta the bump has to
cross grows every day it does not land.

This module is the head-of-line reservation that ends the race. While a pin-moving PR
occupies a merge-queue entry, `auto-merge.yml` and `merge-sweep.yml` ask here first and
enqueue nothing else, so no ordinary PR can land underneath the rebuild and none is
batched into the bump's merge group. At ~90 merges/day an 85-minute exclusive window
costs about 5% of throughput, in exchange for a bump that lands.

WHAT COUNTS AS A BUMP is the property that matters, not the branch name: a queued PR
that changes `lake-manifest.json` or `lean-toolchain`. That is exactly the class whose
rebuild starts from an empty cache and takes an hour and a half, and it catches the
hand-cut repair branches a wedged bump gets re-rolled onto (#1986 sat on
`bump-mathlib/fix-c003275`, not on the LKG branch) as well as the daily
`hopscotch/lkg-bump` PR, which is also matched by name so that a bump whose file list
we could not read still reserves.

Two properties matter more than the mechanism:

  * A queued bump never blocks ITSELF, so the reservation cannot deadlock the thing it
    exists to protect. A *second* pin-moving PR does wait behind the first, which is
    deliberate: two 85-minute rebuilds in one merge group is the batching this avoids.
  * The reservation EXPIRES. A bump wedged in the queue would otherwise freeze every
    merge in the repository indefinitely, turning one stuck PR into a stopped project.
    After MAX_HOLD_HOURS the lock releases and ordinary traffic resumes; the
    `stuck-bump` alert in scripts/pr_status/stuck_alerts.py escalates from there.

FAIL OPEN, unlike the watchdog. A watchdog that cannot read GitHub must keep alerting;
a lock that cannot read GitHub must let go. Losing the race costs one day of bump
progress, while a lock stuck "held" on an API blip stops every merge in the repository.
So any error -- a GraphQL failure, an unparseable response, a missing field -- reports
the lock free and says why.

Usage:
    bump_lock.py                # is the merge queue reserved for a bump right now?
    bump_lock.py --pr 1234      # ... as seen by PR #1234 (free if 1234 IS the bump)

Writes GITHUB_OUTPUT-shaped lines to stdout, for `>> "$GITHUB_OUTPUT"`:

    held=true|false
    reason=<one line, no newlines>

Exit status is 0 whenever a decision was reached (held or not); only a usage error
exits nonzero. Callers should still guard the invocation, since fail-open is only
honoured if this process runs at all.

Environment:
    GH_REPO                  default "TauCetiProject/TauCeti"
    GH_TOKEN / GITHUB_TOKEN  used by `gh` for the GitHub GraphQL API
"""

import argparse
import datetime
import json
import os
import subprocess
import sys

REPO = os.environ.get("GH_REPO", "TauCetiProject/TauCeti")
QUEUE_BRANCH = "main"
LKG_BRANCH = "hopscotch/lkg-bump"  # keep in sync with update.yml's LKG_BRANCH
# Changing either of these is what invalidates the whole build cache. They are also
# exactly the two files pr-build's scope guard treats as a Lake-pin bump.
PIN_FILES = {"lake-manifest.json", "lean-toolchain"}

# How long a bump may hold the queue before ordinary merges resume. The rebuild it
# protects is ~85 minutes, so this is roughly 3x one attempt: long enough to cover a
# rebuild plus the re-queue after a transient eviction, short enough that a genuinely
# wedged bump costs the repository a few hours rather than a day. Past this point the
# situation is no longer "the bump is landing" but "the bump is stuck", which is
# stuck_alerts.py's job (it fires at 12h), not this module's.
MAX_HOLD_HOURS = 4.0

# 20 entries is far more than the queue ever holds, and 100 files far more than a bump
# ever changes. A PR whose file list is truncated at 100 is not a bump, so treating a
# truncated list as "not a bump" is the fail-open direction.
_QUERY = """
query($owner: String!, $name: String!, $branch: String!) {
  repository(owner: $owner, name: $name) {
    mergeQueue(branch: $branch) {
      entries(first: 20) {
        nodes {
          enqueuedAt
          state
          pullRequest {
            number
            headRefName
            headRepository { nameWithOwner }
            files(first: 100) { nodes { path } }
          }
        }
      }
    }
  }
}
"""


def now_utc():
    return datetime.datetime.now(datetime.timezone.utc)


def parse_ts(s):
    """Parse a GitHub ISO-8601 UTC timestamp (e.g. 2026-07-20T19:06:08Z)."""
    return datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))


def hours_since(s, now=None):
    return ((now or now_utc()) - parse_ts(s)).total_seconds() / 3600.0


def queue_entries():
    """The merge queue's entries for the protected branch, newest field shapes as given.

    Returns `[{"enqueuedAt", "state", "pullRequest": {...}}]`, empty when the queue is
    empty or not configured. Raises on any transport or shape problem, so the caller can
    fail open with a stated reason.
    """
    owner, _, name = REPO.partition("/")
    out = subprocess.run(
        ["gh", "api", "graphql", "-f", f"query={_QUERY}",
         "-F", f"owner={owner}", "-F", f"name={name}", "-F", f"branch={QUEUE_BRANCH}"],
        capture_output=True, text=True)
    if out.returncode != 0:
        raise RuntimeError(f"gh api graphql failed: {out.stderr.strip()}")
    data = json.loads(out.stdout)
    if data.get("errors"):
        raise RuntimeError(f"GraphQL errors: {json.dumps(data['errors'])}")
    queue = (data["data"]["repository"] or {}).get("mergeQueue")
    if not queue:
        return []
    return queue["entries"]["nodes"]


def is_bump(pr):
    """Does this queued PR move a Lake pin (and so face the full 85-minute rebuild)?"""
    if not pr:
        return False
    # The branch-name shortcut only means anything for OUR branch: a fork is free to call
    # its branch `hopscotch/lkg-bump` too, and treating that as the bump would hand an
    # outsider the ability to reserve the queue. The pin test below has no such problem,
    # so a fork PR that really does move the pins still reserves, as it should.
    own = (pr.get("headRepository") or {}).get("nameWithOwner")
    if pr.get("headRefName") == LKG_BRANCH and own == REPO:
        return True
    files = ((pr.get("files") or {}).get("nodes")) or []
    return any(f.get("path") in PIN_FILES for f in files)


def decide(entries, subject=None, now=None):
    """(held, reason) for a caller asking on behalf of PR `subject` (None = anyone).

    Pure: `entries` is whatever queue_entries() returned, so the whole policy is testable
    without a network. `subject` is compared numerically, since a workflow passes it
    through as a string.
    """
    now = now or now_utc()
    subject = int(subject) if subject not in (None, "") else None
    bumps = [e for e in entries if is_bump(e.get("pullRequest"))]
    # A queued bump asking about itself. Checked across ALL bump entries before any hold
    # is considered, so no ordering of the queue can lock a bump out of the reservation
    # that exists for it.
    if subject is not None and any(e["pullRequest"]["number"] == subject for e in bumps):
        return False, f"PR #{subject} is the queued pin bump; the queue is reserved for it"
    expired = None
    for entry in bumps:
        number = entry["pullRequest"]["number"]
        at = entry.get("enqueuedAt")
        if not at:
            # No clock means no expiry, and an unbounded hold is the one outcome this module
            # must never produce -- a bump wedged in the queue would freeze every merge in
            # the repository. An entry we cannot time is therefore an entry we do not hold
            # for, which is the same fail-open direction as an unreadable queue.
            expired = (f"queue entry for PR #{number} has no enqueue time; cannot bound the "
                       f"hold, so not reserving")
            continue
        age = hours_since(at, now)
        if age >= MAX_HOLD_HOURS:
            expired = (f"pin-bump PR #{number} has held the queue for over "
                       f"{MAX_HOLD_HOURS:g}h; releasing the reservation so ordinary merges "
                       f"resume (see the stuck-bump alert)")
            continue
        state = entry.get("state") or "unknown"
        return True, (f"pin-bump PR #{number} is in the merge queue (state {state}); "
                      f"holding ordinary merges so nothing lands under its rebuild")
    if expired:
        return False, expired
    return False, "no pin bump in the merge queue"


def emit(held, reason):
    """GITHUB_OUTPUT-shaped lines. `reason` is flattened: a newline in an output value
    would let the rest of it be read as a separate output key."""
    print(f"held={'true' if held else 'false'}")
    print("reason=" + " ".join(reason.split()))


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--pr", default=None,
                    help="the PR the caller wants to enqueue (free if it IS the bump)")
    args = ap.parse_args(argv[1:])
    try:
        held, reason = decide(queue_entries(), subject=args.pr)
    except Exception as exc:  # fail open — see the module docstring
        emit(False, f"could not read the merge queue ({exc}); failing open")
        return 0
    emit(held, reason)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
