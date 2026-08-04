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
  counting comments undercounts later rounds.
- **One review** in the contributor history is one issue comment containing
  `<!--tauceti-scoreboard-->`, attributed to the GitHub login that posted it.
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

GitHub pagination is explicit at both levels: all PR pages are fetched, and any PR
with more than 100 label events has its nested timeline paginated separately. Issue
comments are filtered by `gh` before reaching Python, so full scoreboard bodies do not
accumulate in memory.

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

They cover nested timeline pagination, cycle reach beyond six, the requested queue
panel order, SVG/XML validity, and a synthetic 2,500-contributor history.
