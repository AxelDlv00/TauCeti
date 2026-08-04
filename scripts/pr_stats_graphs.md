# Pull-request statistics graphs

`pr_stats_graphs.py` regenerates the five pull-request statistics assets intended for
the Tau Ceti Statistics page:

```sh
python3 scripts/pr_stats_graphs.py \
  --repo TauCetiProject/TauCeti \
  --out-dir web/static_files
```

It requires an authenticated `gh` CLI. In GitHub Actions, set `GH_TOKEN` to
`${{ github.token }}` and grant `pull-requests: read` plus `issues: read`.

## Definitions

- **Total time open** is snapshot time minus PR creation time for every open PR.
- **Awaiting author** starts when the current `awaiting-author` label was applied.
- **In review** starts when the current review cycle entered `awaiting-review`; a
  subsequent `review-in-progress` label remains part of that same clock.
- **Review cycle N** means that `awaiting-review` has been applied to the PR at least N
  times. This must come from label events: scoreboard comments are edited in place and
  counting comments undercounts later rounds. The chart states the earliest date on
  which that label is observed, since PRs predating the review-state labels cannot be
  reconstructed from those transitions.
- **One review scoreboard** in the contributor history is one issue comment containing
  `<!--tauceti-scoreboard-->`, attributed to the GitHub login that posted it. This is a
  count of posted scoreboards, not reconstructed review rounds; scoreboards edited in
  place remain one comment.
- Seven-day metrics use complete UTC calendar days. Merge latency is PR creation to
  merge time among PRs merged in that trailing window.

## Reproducible and offline runs

Save the normalized source snapshot while fetching:

```sh
python3 scripts/pr_stats_graphs.py \
  --repo TauCetiProject/TauCeti \
  --out-dir /tmp/pr-stats \
  --dump-data /tmp/pr-stats-source.json
```

Replay it without GitHub access:

```sh
python3 scripts/pr_stats_graphs.py \
  --data /tmp/pr-stats-source.json \
  --out-dir /tmp/pr-stats-replay
```

`--as-of` overrides the snapshot clock for deterministic fixtures. The default chart
limits can be adjusted with `--history-days`, `--contributor-limit`, and
`--max-review-cycles`.

## Scaling

GitHub pagination is explicit at both levels. PR metadata is fetched separately from
label history because GitHub can silently truncate a timeline nested inside the outer
PR connection—even when it reports no next page. Timelines are therefore queried one
at a time through authoritative direct `pullRequest(number:)` connections; batching
those direct connections can also lose events. Any timeline with more than 100 label
events is paginated separately. The current repository uses about 1,900 of GitHub's
5,000-point hourly GraphQL budget per run. Excessive missing state transitions stop
generation rather than publishing a mislabelled clock. Issue comments are filtered by
`gh` before reaching Python, so full scoreboard bodies do not accumulate in memory.

All six outputs are rendered in a staging directory and promoted only after every
chart and the JSON payload succeeds. A failed scheduled fetch therefore keeps the
previous coherent asset set.

Contributor charts plot up to 24 contributors and one aggregate `Other` series.
Only those bounded series are expanded by day. `pr-stats.json` still records the exact
all-time total for every contributor, so increasing the project from tens to thousands
of contributors does not create a thousand-line SVG or a days-times-contributors
in-memory matrix.

## Tests

The tests are hermetic and use only the standard library:

```sh
python3 scripts/test_pr_stats_graphs.py
```

They cover direct timeline pagination, fail-closed state clocks,
all-or-nothing rendering, cycle reach beyond six, the requested queue panel order,
SVG/XML validity, and a synthetic 2,500-contributor history.
