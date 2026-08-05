#!/usr/bin/env python3
"""bump_lock.py — reserve the merge queue for a mathlib bump.

A bump's merge-group rebuild takes ~85 minutes (the new pin invalidates every olean) and
main merges ~90 PRs a day, so ~8 land underneath it, any of which can use a name the new
mathlib deprecates. #1986 lost that race four times. While a pin-moving PR holds a queue
entry, auto-merge.yml and merge-sweep.yml enqueue nothing else.

A bump is a queued PR that changes lake-manifest.json or lean-toolchain — the property,
not the branch name, since a wedged bump gets re-rolled onto an ad-hoc branch (#1986 sat
on `bump-mathlib/fix-c003275`). LKG_BRANCH also matches by name, but only in this repo:
a fork could otherwise reserve the queue by naming a branch.

Two release conditions matter more than the mechanism. A queued bump never blocks itself.
And the hold expires after MAX_HOLD_HOURS, so a wedged bump cannot freeze every merge in
the repository; stuck_alerts.py escalates from there.

FAIL OPEN, unlike the watchdog: a lock stuck "held" on an API blip stops the repository,
while a lost race costs one day. Any error reports the queue free and says why.

    bump_lock.py [--pr N]      # writes `held=` / `reason=` for >> "$GITHUB_OUTPUT"

Environment: GH_REPO, GH_TOKEN / GITHUB_TOKEN.
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
PIN_FILES = {"lake-manifest.json", "lean-toolchain"}
# ~3x one rebuild: covers an attempt plus a re-queue, while a genuinely wedged bump costs
# the repository hours rather than a day. Past this it is stuck_alerts.py's problem.
MAX_HOLD_HOURS = 4.0

# A PR whose file list is truncated at 100 is not a bump, so the cap fails open.
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


def hours_since(ts, now=None):
    at = datetime.datetime.fromisoformat(ts.replace("Z", "+00:00"))
    return ((now or now_utc()) - at).total_seconds() / 3600.0


def queue_entries():
    """The merge queue's entries, or [] if the queue is empty or unconfigured. Raises on
    any transport or shape problem, so the caller can fail open with a stated reason."""
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
    return queue["entries"]["nodes"] if queue else []


def is_bump(pr):
    """Does this queued PR move a Lake pin, and so face the full 85-minute rebuild?"""
    if not pr:
        return False
    own = (pr.get("headRepository") or {}).get("nameWithOwner")
    if pr.get("headRefName") == LKG_BRANCH and own == REPO:
        return True
    return any(f.get("path") in PIN_FILES
               for f in ((pr.get("files") or {}).get("nodes") or []))


def decide(entries, subject=None, now=None):
    """(held, reason) for a caller asking on behalf of PR `subject` (None = anyone)."""
    now = now or now_utc()
    subject = int(subject) if subject not in (None, "") else None
    bumps = [e for e in entries if is_bump(e.get("pullRequest"))]
    # Checked across ALL bump entries before any hold, so no ordering of the queue can lock
    # a bump out of the reservation that exists for it.
    if subject is not None and any(e["pullRequest"]["number"] == subject for e in bumps):
        return False, f"PR #{subject} is the queued pin bump; the queue is reserved for it"
    expired = None
    for entry in bumps:
        number = entry["pullRequest"]["number"]
        at = entry.get("enqueuedAt")
        if not at:
            # No clock means no expiry, and an unexpirable hold is the one outcome to avoid.
            expired = f"queue entry for PR #{number} has no enqueue time; not reserving"
            continue
        if hours_since(at, now) >= MAX_HOLD_HOURS:
            expired = (f"pin-bump PR #{number} has held the queue over {MAX_HOLD_HOURS:g}h; "
                       f"releasing it (see the stuck-bump alert)")
            continue
        return True, (f"pin-bump PR #{number} is in the merge queue "
                      f"(state {entry.get('state') or 'unknown'}); holding ordinary merges")
    return False, expired or "no pin bump in the merge queue"


def emit(held, reason):
    """GITHUB_OUTPUT is line-oriented, so `reason` is flattened to one line."""
    print(f"held={'true' if held else 'false'}")
    print("reason=" + " ".join(reason.split()))


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--pr", default=None, help="the PR the caller wants to enqueue")
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
