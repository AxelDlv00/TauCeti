#!/usr/bin/env python3
"""Generate the Tau Ceti pull-request statistics SVGs.

The live data path uses GitHub's GraphQL API for every pull request and its label
timeline, plus the repository issue-comments REST endpoint for posted Tau Ceti
scoreboards.  A normalized snapshot can be written with ``--dump-data`` and replayed
with ``--data``; tests and local chart work therefore need no network.

Generated files:

* ``pr-queue-age.svg`` — total open age, awaiting-author age, then in-review age;
* ``review-cycles-reached.svg`` — PRs reaching each ``awaiting-review`` cycle;
* ``rolling-seven-day-history.svg`` — merge throughput, authors, and latency;
* ``cumulative-merges-by-contributor.svg``;
* ``cumulative-reviews-by-contributor.svg``;
* ``pr-stats.json`` — definitions, exact contributor totals, and plotted series.

Contributor charts deliberately draw only the top N contributors plus one aggregate
``Other`` line.  The cap makes the SVG bounded even if the project eventually has
thousands of contributors; exact totals for every login remain in ``pr-stats.json``.
The implementation also stores daily series only for plotted lines, avoiding a
days-times-contributors memory blow-up.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import time
from collections import Counter
from datetime import date, datetime, time as day_time, timedelta, timezone
from pathlib import Path
from typing import Iterable


BG = "#fbfaf7"
TEXT = "#25313d"
MUTED = "#68737e"
GRID = "#d8dce0"
SCOREBOARD_MARKER = "<!--tauceti-scoreboard-->"
STATE_REVIEW = {"awaiting-review", "review-in-progress"}
PALETTE = [
    "#3979c6", "#d26735", "#2f9364", "#8059bd", "#c0446e", "#168b99",
    "#9b7124", "#5268c4", "#6f8b2d", "#b64d3f", "#1473a5", "#9d4f9e",
    "#567b53", "#a85f22", "#4e6d91", "#8a6950", "#4f9089", "#7f5c87",
    "#767d2c", "#b24f72", "#3f7d9a", "#7365a6",
]
HOUR_EDGES = [0, 1, 2, 4, 8, 12, 24, 48, 72, 120, math.inf]
HOUR_LABELS = [
    "<1h", "1–2h", "2–4h", "4–8h", "8–12h", "12–24h",
    "1–2d", "2–3d", "3–5d", "5d+",
]


def parse_dt(value: str | None) -> datetime | None:
    return datetime.fromisoformat(value.replace("Z", "+00:00")) if value else None


def iso_z(value: datetime) -> str:
    return value.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


def atomic_write(path: Path, content: str) -> None:
    """Replace path atomically so a failed daily run cannot leave a partial asset."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        os.fchmod(fd, 0o644)
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            stream.write(content)
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def run_gh(arguments: list[str], attempts: int = 3) -> str:
    """Run gh with short retries for transient GitHub/API failures."""
    last_error = None
    for attempt in range(attempts):
        result = subprocess.run(
            ["gh", *arguments], text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if result.returncode == 0:
            return result.stdout
        last_error = result.stderr.strip() or f"gh exited {result.returncode}"
        if attempt + 1 < attempts:
            time.sleep(2 ** attempt)
    raise RuntimeError(f"GitHub query failed after {attempts} attempts: {last_error}")


def split_repo(repo: str) -> tuple[str, str]:
    match = re.fullmatch(r"([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)", repo)
    if not match:
        raise ValueError(f"expected OWNER/REPO, got {repo!r}")
    return match.group(1), match.group(2)


PR_PAGE_QUERY = r"""
query($owner:String!, $name:String!, $cursor:String) {
  repository(owner:$owner, name:$name) {
    pullRequests(first:100, after:$cursor,
                 orderBy:{field:CREATED_AT, direction:ASC}) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number createdAt mergedAt closedAt state isDraft
        author { login }
        labels(first:30) { nodes { name } }
        timelineItems(first:100, itemTypes:[LABELED_EVENT]) {
          pageInfo { hasNextPage endCursor }
          nodes { ... on LabeledEvent { createdAt label { name } } }
        }
      }
    }
  }
}
"""

TIMELINE_PAGE_QUERY = r"""
query($owner:String!, $name:String!, $number:Int!, $cursor:String!) {
  repository(owner:$owner, name:$name) {
    pullRequest(number:$number) {
      timelineItems(first:100, after:$cursor, itemTypes:[LABELED_EVENT]) {
        pageInfo { hasNextPage endCursor }
        nodes { ... on LabeledEvent { createdAt label { name } } }
      }
    }
  }
}
"""


def graphql(query: str, **variables) -> dict:
    args = ["api", "graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        if value is None:
            continue
        flag = "-F" if isinstance(value, int) else "-f"
        args.extend([flag, f"{key}={value}"])
    payload = json.loads(run_gh(args))
    if payload.get("errors"):
        raise RuntimeError(f"GitHub GraphQL errors: {payload['errors']}")
    return payload["data"]


def fetch_prs(repo: str) -> list[dict]:
    """Fetch every PR and every labeled event, including nested pagination."""
    owner, name = split_repo(repo)
    cursor = None
    prs = []
    while True:
        data = graphql(PR_PAGE_QUERY, owner=owner, name=name, cursor=cursor)
        connection = data["repository"]["pullRequests"]
        for raw in connection["nodes"]:
            timeline = raw.pop("timelineItems")
            events = timeline["nodes"]
            event_page = timeline["pageInfo"]
            while event_page["hasNextPage"]:
                extra = graphql(
                    TIMELINE_PAGE_QUERY, owner=owner, name=name,
                    number=raw["number"], cursor=event_page["endCursor"],
                )["repository"]["pullRequest"]["timelineItems"]
                events.extend(extra["nodes"])
                event_page = extra["pageInfo"]
            prs.append({
                "number": raw["number"],
                "created_at": raw["createdAt"],
                "merged_at": raw["mergedAt"],
                "closed_at": raw["closedAt"],
                "state": raw["state"],
                "is_draft": raw["isDraft"],
                "author": (raw.get("author") or {}).get("login") or "unknown",
                "labels": [item["name"] for item in raw["labels"]["nodes"]],
                "labeled_events": [
                    {"created_at": event["createdAt"], "label": event["label"]["name"]}
                    for event in events if event.get("label")
                ],
            })
        if not connection["pageInfo"]["hasNextPage"]:
            break
        cursor = connection["pageInfo"]["endCursor"]
    return prs


def fetch_scoreboards(repo: str) -> list[dict]:
    # Filter at gh/jq before returning data to Python. Scoreboard bodies can be large;
    # retaining them all would make memory proportional to review prose, not metrics.
    raw = run_gh([
        "api", "--paginate",
        f"repos/{repo}/issues/comments?per_page=100",
        "--jq", f'.[] | select((.body // "") | contains("{SCOREBOARD_MARKER}"))'
                ' | {issue_url, created_at, updated_at, user: .user.login}',
    ])
    scoreboards = []
    for line in raw.splitlines():
        comment = json.loads(line)
        issue_url = comment.get("issue_url") or ""
        try:
            pr_number = int(issue_url.rsplit("/", 1)[1])
        except (IndexError, ValueError):
            continue
        scoreboards.append({
            "pr": pr_number,
            "created_at": comment["created_at"],
            "updated_at": comment["updated_at"],
            "user": comment.get("user") or "unknown",
        })
    return scoreboards


def fetch_snapshot(repo: str) -> dict:
    return {
        "schema_version": 1,
        "repo": repo,
        "fetched_at": iso_z(datetime.now(timezone.utc)),
        "prs": fetch_prs(repo),
        "scoreboards": fetch_scoreboards(repo),
    }


def last_labeled(pr: dict, label: str) -> datetime | None:
    for event in reversed(pr.get("labeled_events") or []):
        if event["label"] == label:
            return parse_dt(event["created_at"])
    return None


def queue_age_metrics(prs: list[dict], snapshot: datetime) -> dict:
    total, author, review = [], [], []
    missing_transition = 0
    other = 0
    for pr in prs:
        if pr["state"] != "OPEN":
            continue
        created = parse_dt(pr["created_at"])
        total.append(max(0.0, (snapshot - created).total_seconds() / 3600))
        labels = set(pr.get("labels") or [])
        if pr.get("is_draft"):
            other += 1
        elif "awaiting-author" in labels:
            start = last_labeled(pr, "awaiting-author")
            if start is None:
                start = created
                missing_transition += 1
            author.append(max(0.0, (snapshot - start).total_seconds() / 3600))
        elif labels & STATE_REVIEW:
            # review-in-progress is a claimed awaiting-review cycle, not a new wait.
            start = last_labeled(pr, "awaiting-review")
            if start is None:
                start = last_labeled(pr, "review-in-progress") or created
                missing_transition += 1
            review.append(max(0.0, (snapshot - start).total_seconds() / 3600))
        else:
            other += 1
    return {
        "total_open_hours": total,
        "awaiting_author_hours": author,
        "in_review_hours": review,
        "other_open_prs": other,
        "missing_transition_fallbacks": missing_transition,
    }


def review_cycle_metrics(prs: list[dict]) -> dict:
    counts = {
        str(pr["number"]): sum(
            event["label"] == "awaiting-review"
            for event in pr.get("labeled_events") or []
        )
        for pr in prs
    }
    observed = [count for count in counts.values() if count]
    maximum = max(observed, default=0)
    reach = [
        {"cycle": cycle, "prs": sum(count >= cycle for count in observed)}
        for cycle in range(1, maximum + 1)
    ]
    return {
        "definition": "number of times the awaiting-review label was applied",
        "reviewed_prs": len(observed),
        "awaiting_review_transitions": sum(observed),
        "max_cycle": maximum,
        "reach": reach,
        "cycles_by_pr": counts,
    }


def percentile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    position = (len(ordered) - 1) * q
    low, high = math.floor(position), math.ceil(position)
    if low == high:
        return ordered[low]
    return ordered[low] + (ordered[high] - ordered[low]) * (position - low)


def rolling_metrics(prs: list[dict], last_full_day: date, history_days: int) -> list[dict]:
    project_start = min(parse_dt(pr["created_at"]).date() for pr in prs)
    display_start = max(project_start, last_full_day - timedelta(days=history_days - 1))
    parsed = [{
        "created": parse_dt(pr["created_at"]),
        "merged": parse_dt(pr.get("merged_at")),
        "author": pr["author"],
    } for pr in prs]
    rows = []
    day = display_start
    while day <= last_full_day:
        end = datetime.combine(day + timedelta(days=1), day_time.min, tzinfo=timezone.utc)
        start = end - timedelta(days=7)
        merged = [pr for pr in parsed if pr["merged"] and start <= pr["merged"] < end]
        opened = [pr for pr in parsed if start <= pr["created"] < end]
        latencies = [
            (pr["merged"] - pr["created"]).total_seconds() / 3600
            for pr in merged
        ]
        rows.append({
            "date": day.isoformat(),
            "merges": len(merged),
            "active_authors": len({pr["author"] for pr in opened}),
            "median_merge_hours": percentile(latencies, .5),
            "p90_merge_hours": percentile(latencies, .9),
        })
        day += timedelta(days=1)
    return rows


def cumulative_chart_series(
    events: Iterable[tuple[datetime, str]], start: date, end: date, limit: int,
) -> tuple[list[str], list[str], dict[str, list[int]], Counter]:
    """Build bounded plotted series while retaining exact totals for every login."""
    events = [(timestamp, name) for timestamp, name in events if timestamp.date() <= end]
    totals = Counter(name for _, name in events)
    selected = sorted(totals, key=lambda name: (-totals[name], name.casefold()))[:limit]
    selected_set = set(selected)
    omitted = len(totals) - len(selected)
    other = f"Other ({omitted:,} contributors)" if omitted else None
    names = selected + ([other] if other else [])
    daily = Counter()
    for timestamp, name in events:
        group = name if name in selected_set else other
        daily[(timestamp.date(), group)] += 1
    running = Counter()
    series = {name: [] for name in names}
    dates = []
    day = start
    while day <= end:
        dates.append(day.isoformat())
        for name in names:
            running[name] += daily[(day, name)]
            series[name].append(running[name])
        day += timedelta(days=1)
    return dates, names, series, totals


def histogram(values: Iterable[float]) -> list[int]:
    counts = [0] * len(HOUR_LABELS)
    for value in values:
        for index, (low, high) in enumerate(zip(HOUR_EDGES, HOUR_EDGES[1:])):
            if low <= value < high:
                counts[index] += 1
                break
    return counts


def nice_axis_max(value: float) -> int:
    if value <= 0:
        return 5
    magnitude = 10 ** math.floor(math.log10(value))
    for multiple in (1, 2, 2.5, 5, 10):
        candidate = multiple * magnitude
        if candidate >= value:
            return max(5, int(candidate))
    return max(5, math.ceil(value))


def draw_histogram(
    parts: list[str], counts: list[int], x: int, y: int, width: int, height: int,
    color: str, heading: str, total: int,
) -> None:
    left, right, top, bottom = x + 42, x + width - 10, y + 55, y + height - 48
    axis_max = nice_axis_max(max(counts, default=0))
    parts.append(f'<text x="{x}" y="{y+20}" class="panel">{html.escape(heading)}</text>')
    parts.append(f'<text x="{x+width-10}" y="{y+20}" text-anchor="end" class="paneltotal">n={total:,}</text>')
    for index in range(6):
        fraction = index / 5
        gy = bottom - fraction * (bottom - top)
        value = round(fraction * axis_max)
        parts.append(f'<line x1="{left}" y1="{gy:.1f}" x2="{right}" y2="{gy:.1f}" class="grid"/>')
        parts.append(f'<text x="{left-8}" y="{gy+4:.1f}" text-anchor="end" class="tick">{value}</text>')
    slot = (right - left) / len(counts)
    bar_width = slot * .72
    for index, (label, count) in enumerate(zip(HOUR_LABELS, counts)):
        bar_height = count / axis_max * (bottom - top)
        bx = left + index * slot + (slot - bar_width) / 2
        by = bottom - bar_height
        parts.append(f'<rect x="{bx:.1f}" y="{by:.1f}" width="{bar_width:.1f}" height="{bar_height:.1f}" rx="4" fill="{color}"/>')
        if count:
            parts.append(f'<text x="{bx+bar_width/2:.1f}" y="{max(top-10, by-8):.1f}" text-anchor="middle" class="value">{count}</text>')
        parts.append(f'<text x="{bx+bar_width/2:.1f}" y="{bottom+20}" text-anchor="middle" class="tick">{html.escape(label)}</text>')


def render_queue_age(path: Path, metrics: dict, snapshot: datetime) -> None:
    width, height = 1710, 620
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="Open PR age and current review-state age">',
        f'<rect width="100%" height="100%" fill="{BG}"/>',
        f'<style>text{{font-family:Inter,ui-sans-serif,system-ui,sans-serif;fill:{TEXT}}}.title{{font-size:29px;font-weight:700}}.subtitle{{font-size:14px;fill:{MUTED}}}.panel{{font-size:18px;font-weight:680}}.paneltotal{{font-size:15px;font-weight:700;fill:{MUTED}}}.tick{{font-size:11px;fill:{MUTED}}}.value{{font-size:12px;font-weight:750}}.grid{{stroke:{GRID};stroke-width:1}}</style>',
        '<text x="55" y="44" class="title">Open PR age and current review state</text>',
        f'<text x="55" y="73" class="subtitle">Snapshot {snapshot:%Y-%m-%d %H:%M} UTC · current-state clocks begin at the label transition · {metrics["other_open_prs"]:,} PRs outside author/review states appear only in total time open</text>',
    ]
    panels = [
        (metrics["total_open_hours"], "#2f9364", "Total time open"),
        (metrics["awaiting_author_hours"], "#d27736", "Awaiting author"),
        (metrics["in_review_hours"], "#3979c6", "In review"),
    ]
    for index, (values, color, title) in enumerate(panels):
        draw_histogram(
            parts, histogram(values), 45 + index * 555, 115, 515, 455,
            color, title, len(values),
        )
    parts.append("</svg>")
    atomic_write(path, "".join(parts) + "\n")


def render_review_cycles(path: Path, metrics: dict, max_rows: int) -> None:
    reach = metrics["reach"]
    shown = reach[:max_rows]
    truncated = len(reach) > max_rows
    if truncated:
        shown[-1] = dict(shown[-1], label=f"Review cycle {max_rows}+")
    reviewed = metrics["reviewed_prs"]
    width = 1250
    height = 116 + max(1, len(shown)) * 52 + 35
    bar_x, bar_width = 235, 780
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="Pull requests reaching each automated review cycle">',
        f'<rect width="100%" height="100%" fill="{BG}"/>',
        f'<style>text{{font-family:Inter,ui-sans-serif,system-ui,sans-serif;fill:{TEXT}}}.title{{font-size:27px;font-weight:700}}.subtitle{{font-size:14px;fill:{MUTED}}}.label{{font-size:14px;font-weight:680}}.value{{font-size:13px;font-weight:750}}.track{{fill:#e3e6e8}}</style>',
        '<text x="45" y="42" class="title">PRs reaching each review cycle</text>',
        f'<text x="45" y="70" class="subtitle">One cycle = one application of the awaiting-review label · {metrics["awaiting_review_transitions"]:,} transitions across {reviewed:,} reviewed PRs</text>',
    ]
    if not shown:
        parts.append('<text x="45" y="125" class="label">No review cycles observed.</text>')
    for index, item in enumerate(shown):
        cycle, count = item["cycle"], item["prs"]
        y = 98 + index * 52
        fraction = count / reviewed if reviewed else 0
        label = item.get("label", f"Review cycle {cycle}")
        color = PALETTE[min(index, len(PALETTE) - 1)]
        parts.append(f'<text x="45" y="{y+25}" class="label">{html.escape(label)}</text>')
        parts.append(f'<rect x="{bar_x}" y="{y}" width="{bar_width}" height="36" rx="7" class="track"/>')
        parts.append(f'<rect x="{bar_x}" y="{y}" width="{max(2, bar_width*fraction):.1f}" height="36" rx="7" fill="{color}"/>')
        parts.append(f'<text x="{bar_x+bar_width+22}" y="{y+25}" class="value">{count:,} · {fraction:.1%}</text>')
    parts.append("</svg>")
    atomic_write(path, "".join(parts) + "\n")


def render_rolling(path: Path, rolling: list[dict]) -> None:
    width, height = 1500, 830
    panels = [
        ("Merges in trailing 7 days", "merges", "#3979c6", lambda x: f"{int(x)}"),
        ("Active PR authors in trailing 7 days", "active_authors", "#d27736", lambda x: f"{int(x)}"),
        ("Median time to merge", "median_merge_hours", "#2f9364", lambda x: f"{x:.1f}h"),
        ("90th percentile time to merge", "p90_merge_hours", "#8059bd", lambda x: f"{x:.1f}h"),
    ]
    panel_width, panel_height = 680, 285
    origins = [(65, 125), (785, 125), (65, 475), (785, 475)]
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="Trailing-seven-day pull request health">',
        f'<rect width="100%" height="100%" fill="{BG}"/>',
        f'<style>text{{font-family:Inter,ui-sans-serif,system-ui,sans-serif;fill:{TEXT}}}.title{{font-size:29px;font-weight:700}}.subtitle{{font-size:14px;fill:{MUTED}}}.panel{{font-size:17px;font-weight:650}}.latest{{font-size:28px;font-weight:750}}.tick{{font-size:11px;fill:{MUTED}}}.grid{{stroke:{GRID};stroke-width:1}}</style>',
        '<text x="55" y="44" class="title">Trailing-seven-day project health</text>',
        f'<text x="55" y="72" class="subtitle">Daily UTC windows ending {rolling[0]["date"]}–{rolling[-1]["date"]} · complete days only</text>',
    ]
    for (title, key, color, formatter), (ox, oy) in zip(panels, origins):
        values = [row[key] or 0 for row in rolling]
        axis_max = nice_axis_max(max(values, default=0))
        left, right = ox + 44, ox + panel_width - 15
        top, bottom = oy + 68, oy + panel_height - 26
        parts.append(f'<text x="{ox}" y="{oy+20}" class="panel">{html.escape(title)}</text>')
        parts.append(f'<text x="{ox+panel_width-20}" y="{oy+25}" text-anchor="end" class="latest" style="fill:{color}">{formatter(values[-1])}</text>')
        for index in range(5):
            fraction = index / 4
            y = bottom - fraction * (bottom - top)
            value = fraction * axis_max
            parts.append(f'<line x1="{left}" y1="{y:.1f}" x2="{right}" y2="{y:.1f}" class="grid"/>')
            parts.append(f'<text x="{left-8}" y="{y+4:.1f}" text-anchor="end" class="tick">{formatter(value)}</text>')
        points = []
        for index, value in enumerate(values):
            x = left + index * (right - left) / max(len(values) - 1, 1)
            y = bottom - value / axis_max * (bottom - top)
            points.append(f"{x:.1f},{y:.1f}")
        parts.append(f'<polyline points="{" ".join(points)}" fill="none" stroke="{color}" stroke-width="3.5" stroke-linejoin="round" stroke-linecap="round"/>')
        last_tick_x = -math.inf
        for index, row in enumerate(rolling):
            x = left + index * (right - left) / max(len(values) - 1, 1)
            if index not in (0, len(rolling) - 1) and x - last_tick_x < 100:
                continue
            if index == len(rolling) - 1 and x - last_tick_x < 70:
                continue
            day = date.fromisoformat(row["date"])
            parts.append(f'<text x="{x:.1f}" y="{bottom+18}" text-anchor="middle" class="tick">{day:%b} {day.day}</text>')
            last_tick_x = x
    parts.append("</svg>")
    atomic_write(path, "".join(parts) + "\n")


def color_for(name: str, other: bool = False) -> str:
    if other:
        return "#7b8490"
    digest = hashlib.sha256(name.encode("utf-8")).digest()
    return PALETTE[int.from_bytes(digest[:2], "big") % len(PALETTE)]


def spread_labels(items: list[tuple[str, float]], top: float, bottom: float, gap: int = 22) -> dict[str, float]:
    positioned = []
    for name, y in sorted(items, key=lambda item: item[1]):
        positioned.append([name, max(y, positioned[-1][1] + gap if positioned else top)])
    if positioned and positioned[-1][1] > bottom:
        positioned[-1][1] = bottom
        for index in range(len(positioned) - 2, -1, -1):
            positioned[index][1] = min(positioned[index][1], positioned[index + 1][1] - gap)
    return dict(positioned)


def log_ticks(maximum: int) -> list[int]:
    ticks = [0]
    power = 0
    while 10 ** power <= maximum:
        for multiplier in (1, 3):
            value = multiplier * 10 ** power
            if value <= maximum:
                ticks.append(value)
        power += 1
    if maximum not in ticks and maximum > ticks[-1] * 1.25:
        ticks.append(maximum)
    return sorted(set(ticks))


def render_cumulative_contributors(
    path: Path, title: str, noun: str, dates: list[str], names: list[str],
    series: dict[str, list[int]], totals: Counter, total_contributors: int,
) -> None:
    width, height = 1500, 760
    left, right, top, bottom = 90, 1030, 120, 680
    label_x = 1070
    plotted_totals = {name: values[-1] for name, values in series.items()}
    maximum = max(plotted_totals.values(), default=1)
    logmax = math.log10(maximum + 1)

    def y_for(value):
        return bottom - math.log10(value + 1) / logmax * (bottom - top)

    labels = spread_labels([(name, y_for(plotted_totals[name])) for name in names], top, bottom)
    omitted = total_contributors - min(total_contributors, len([name for name in names if not name.startswith("Other (")]))
    coverage = f"top {len(names) - bool(omitted)} + {omitted:,} others" if omitted else "every contributor"
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="{html.escape(title)}">',
        f'<rect width="100%" height="100%" fill="{BG}"/>',
        f'<style>text{{font-family:Inter,ui-sans-serif,system-ui,sans-serif;fill:{TEXT}}}.title{{font-size:29px;font-weight:700}}.subtitle{{font-size:14px;fill:{MUTED}}}.tick{{font-size:11px;fill:{MUTED}}}.label{{font-size:12px;font-weight:650}}.grid{{stroke:{GRID};stroke-width:1}}.leader{{stroke-width:1;opacity:.55}}</style>',
        f'<text x="55" y="44" class="title">{html.escape(title)}</text>',
        f'<text x="55" y="72" class="subtitle">Cumulative {html.escape(noun)} by UTC day, {dates[0]}–{dates[-1]} · logarithmic count axis · {coverage}; exact totals for all {total_contributors:,} in JSON</text>',
    ]
    for tick in log_ticks(maximum):
        y = y_for(tick)
        parts.append(f'<line x1="{left}" y1="{y:.1f}" x2="{right}" y2="{y:.1f}" class="grid"/>')
        parts.append(f'<text x="{left-10}" y="{y+4:.1f}" text-anchor="end" class="tick">{tick:,}</text>')
    for name in reversed(names):
        color = color_for(name, name.startswith("Other ("))
        values = series[name]
        points = []
        for index, value in enumerate(values):
            x = left + index * (right - left) / max(len(values) - 1, 1)
            points.append(f"{x:.1f},{y_for(value):.1f}")
        parts.append(f'<polyline points="{" ".join(points)}" fill="none" stroke="{color}" stroke-width="2.7" stroke-linejoin="round" stroke-linecap="round"/>')
    for name in names:
        color = color_for(name, name.startswith("Other ("))
        actual_y = y_for(plotted_totals[name])
        label_y = labels[name]
        parts.append(f'<line x1="{right+4}" y1="{actual_y:.1f}" x2="{label_x-8}" y2="{label_y:.1f}" stroke="{color}" class="leader"/>')
        parts.append(f'<circle cx="{right}" cy="{actual_y:.1f}" r="3.2" fill="{color}"/>')
        parts.append(f'<text x="{label_x}" y="{label_y+4:.1f}" class="label" style="fill:{color}">{html.escape(name)} · {plotted_totals[name]:,}</text>')
    last_tick_x = -math.inf
    for index, value in enumerate(dates):
        x = left + index * (right - left) / max(len(dates) - 1, 1)
        if index not in (0, len(dates) - 1) and x - last_tick_x < 95:
            continue
        if index == len(dates) - 1 and x - last_tick_x < 65:
            continue
        day = date.fromisoformat(value)
        parts.append(f'<text x="{x:.1f}" y="{bottom+24}" text-anchor="middle" class="tick">{day:%b} {day.day}</text>')
        last_tick_x = x
    parts.append("</svg>")
    atomic_write(path, "".join(parts) + "\n")


def generate(
    data: dict, out_dir: Path, contributor_limit: int = 24,
    history_days: int = 90, max_review_cycles: int = 12,
    as_of: datetime | None = None,
) -> dict:
    prs = data.get("prs") or []
    if not prs:
        raise ValueError("snapshot contains no pull requests")
    snapshot = as_of or parse_dt(data["fetched_at"])
    if snapshot.tzinfo is None:
        snapshot = snapshot.replace(tzinfo=timezone.utc)
    snapshot = snapshot.astimezone(timezone.utc)
    last_full_day = snapshot.date() - timedelta(days=1)
    project_start = min(parse_dt(pr["created_at"]).date() for pr in prs)
    if last_full_day < project_start:
        raise ValueError("snapshot predates the first pull request")

    queue = queue_age_metrics(prs, snapshot)
    cycles = review_cycle_metrics(prs)
    rolling = rolling_metrics(prs, last_full_day, history_days)
    merge_events = [
        (parse_dt(pr["merged_at"]), pr["author"])
        for pr in prs if pr.get("merged_at")
    ]
    review_events = [
        (parse_dt(item["created_at"]), item["user"])
        for item in data.get("scoreboards") or []
    ]
    merge_dates, merge_names, merge_series, merge_totals = cumulative_chart_series(
        merge_events, project_start, last_full_day, contributor_limit,
    )
    review_dates, review_names, review_series, review_totals = cumulative_chart_series(
        review_events, project_start, last_full_day, contributor_limit,
    )

    render_queue_age(out_dir / "pr-queue-age.svg", queue, snapshot)
    render_review_cycles(out_dir / "review-cycles-reached.svg", cycles, max_review_cycles)
    render_rolling(out_dir / "rolling-seven-day-history.svg", rolling)
    render_cumulative_contributors(
        out_dir / "cumulative-merges-by-contributor.svg",
        "Total merged PRs by contributor since project inception", "merged PRs",
        merge_dates, merge_names, merge_series, merge_totals, len(merge_totals),
    )
    render_cumulative_contributors(
        out_dir / "cumulative-reviews-by-contributor.svg",
        "Total reviews by contributor since project inception", "reviews",
        review_dates, review_names, review_series, review_totals, len(review_totals),
    )

    metrics = {
        "schema_version": 1,
        "repo": data.get("repo"),
        "snapshot": iso_z(snapshot),
        "last_full_day": last_full_day.isoformat(),
        "definitions": {
            "review_cycle": cycles["definition"],
            "review": "one GitHub issue comment containing <!--tauceti-scoreboard-->",
            "active_author": "distinct PR author opening a PR in the trailing seven-day window",
            "merge_latency": "PR creation timestamp to merge timestamp",
        },
        "queue": queue,
        "review_cycles": cycles,
        "rolling_seven_day": rolling,
        "contributor_limit": contributor_limit,
        "cumulative_dates": merge_dates,
        "cumulative_merges_plotted": merge_series,
        "cumulative_reviews_plotted": review_series,
        "merge_totals_by_contributor": dict(merge_totals.most_common()),
        "review_totals_by_contributor": dict(review_totals.most_common()),
    }
    atomic_write(
        out_dir / "pr-stats.json",
        json.dumps(metrics, separators=(",", ":")) + "\n",
    )
    return metrics


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default="TauCetiProject/TauCeti")
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--data", type=Path, help="normalized offline snapshot")
    parser.add_argument("--dump-data", type=Path, help="write fetched normalized snapshot")
    parser.add_argument("--as-of", help="override snapshot time (ISO 8601)")
    parser.add_argument("--contributor-limit", type=int, default=24)
    parser.add_argument("--history-days", type=int, default=90)
    parser.add_argument("--max-review-cycles", type=int, default=12)
    args = parser.parse_args()
    if args.contributor_limit < 1 or args.history_days < 1 or args.max_review_cycles < 1:
        parser.error("numeric limits must be positive")

    if args.data:
        data = json.loads(args.data.read_text(encoding="utf-8"))
    else:
        data = fetch_snapshot(args.repo)
        if args.dump_data:
            atomic_write(args.dump_data, json.dumps(data, indent=2) + "\n")
    as_of = parse_dt(args.as_of) if args.as_of else None
    metrics = generate(
        data, args.out_dir, args.contributor_limit, args.history_days,
        args.max_review_cycles, as_of,
    )
    print(
        f"wrote five charts to {args.out_dir}: "
        f"{len(metrics['queue']['total_open_hours'])} open PRs; "
        f"{metrics['review_cycles']['awaiting_review_transitions']} review transitions; "
        f"{len(metrics['merge_totals_by_contributor'])} merge contributors; "
        f"{len(metrics['review_totals_by_contributor'])} review contributors"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
