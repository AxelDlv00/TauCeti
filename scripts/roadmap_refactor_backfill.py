#!/usr/bin/env python3
"""Safely add explicit roadmap attribution to selected historical refactor PRs.

This is deliberately manifest-driven: semantic classification happens before
this script is invoked. A proposal JSONL contains one object per high-confidence
PR with these fields:

    {"pr": 1522, "roadmap": "ContourIntegration",
     "roadmap_file": "TauCetiRoadmap/ContourIntegration/README.md",
     "roadmap_heading": "Layer 4: ...",
     "roadmap_quote": "the multi-crossing PV engine",
     "provenance": ["#949", "#950"]}

The evidence fields must actually connect the PR to the roadmap, so none of them
is taken on trust. ``roadmap_heading`` must be a real ATX heading of
``roadmap_file`` (fenced code cannot supply one) and ``roadmap_quote`` must sit in
that heading's own section, not merely somewhere in the file. ``provenance`` must
be ``#N``/pull-request-URL references that resolve, against GitHub, to merged PRs
of this repository which the production classifier already attributes to the same
roadmap area, at least one of which touched a file the migrated PR also changes.

``prepare`` captures the verbatim body and roadmap labels, validates the PR and
evidence, computes the insertion, and writes a reversible execution manifest.
``dry-run`` revalidates a tranche without writing (``check`` is a short alias).
``apply`` edits at most twenty PRs, re-runs the production classifier on the
post-edit state, and applies exactly its result. ``revert`` restores the
captured body and label if the applied body has not subsequently changed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import time

import roadmap_label

REPO = "TauCetiProject/TauCeti"
REFACTOR_TITLE = re.compile(r"^refactor(?:[(!:/]| )", re.IGNORECASE)
MAX_TRANCHE = 20
PROVENANCE_REF = re.compile(
    r"(?:#|https://github\.com/(?P<repo>[\w.-]+/[\w.-]+)/pull/)(?P<number>[1-9][0-9]*)"
)
ATX_HEADING = re.compile(r" {0,3}(#{1,6})(?:[ \t]+(.*?))?[ \t]*")


def body_hash(body: str) -> str:
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def insert_roadmap_line(body: str, area: str) -> str:
    """Insert ``Roadmap: area`` without rewriting any existing body bytes."""
    present, declared = roadmap_label.parse_declared_area(body, {area})
    if present:
        if declared == area:
            return body
        raise ValueError("body already contains an invalid or different Roadmap: declaration")

    newline = "\r\n" if "\r\n" in body else "\n"
    line = f"Roadmap: {area}"
    footer = re.search(
        r"(?m)^(?::robot:|🤖)\s*Prepared with [^\r\n]+(?:\r?\n)?\Z",
        body,
    )
    if footer is not None:
        prefix = body[:footer.start()]
        separator = "" if prefix.endswith(newline * 2) else (
            newline if prefix.endswith(newline) else newline * 2
        )
        return prefix + separator + line + newline * 2 + body[footer.start():]

    separator = "" if not body or body.endswith(newline * 2) else (
        newline if body.endswith(newline) else newline * 2
    )
    return body + separator + line


def _run_gh(args: list[str], *, stdin: str | None = None, retries: int = 3) -> str:
    last = ""
    for attempt in range(retries):
        result = subprocess.run(
            ["gh", *args],
            input=stdin,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if result.returncode == 0:
            return result.stdout or ""
        last = result.stderr or ""
        if attempt < retries - 1:
            time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"gh {' '.join(args)} failed after {retries} tries: {last.strip()}")


def pr_state(repo: str, pr: int) -> dict:
    return json.loads(_run_gh([
        "pr", "view", str(pr), "--repo", repo,
        "--json", "number,title,body,files,labels,state",
    ]))


def roadmap_labels(state: dict) -> list[str]:
    return sorted(
        item["name"] for item in state.get("labels") or []
        if item["name"].startswith("roadmap/")
    )


def changed_files(state: dict) -> list[str]:
    return [item["path"] for item in state.get("files") or []]


def patch_body(repo: str, pr: int, body: str) -> None:
    _run_gh(
        ["api", "--method", "PATCH", f"repos/{repo}/pulls/{pr}", "--input", "-"],
        stdin=json.dumps({"body": body}, ensure_ascii=False),
    )


def read_jsonl(path: pathlib.Path) -> list[dict]:
    rows = []
    with path.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_number}: invalid JSON: {exc}") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected an object")
            rows.append(row)
    return rows


def write_jsonl(path: pathlib.Path, rows: list[dict]) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as target:
        for row in rows:
            target.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def heading_sections(contents: str) -> list[tuple[str, str]]:
    """Return ``(heading text, section text)`` for each ATX heading of a document.

    A section runs to the next heading of the same or a higher level, so a quote is
    credited only to the heading it actually sits under. Fenced code is skipped, so
    a shell comment cannot masquerade as a heading, and the hashes must be followed
    by a space, as CommonMark requires, so a bare ``#123`` PR reference cannot
    either.
    """
    lines = contents.splitlines()
    fence: str | None = None
    headings: list[tuple[int, str, int]] = []
    for index, line in enumerate(lines):
        marker = line.lstrip()[:3]
        if marker in {"```", "~~~"}:
            if fence is None:
                fence = marker
            elif fence == marker:
                fence = None
            continue
        if fence is not None:
            continue
        match = ATX_HEADING.fullmatch(line)
        if match is None:
            continue
        text = re.sub(r"[ \t]+#+\Z", "", match.group(2) or "").strip()
        headings.append((len(match.group(1)), text, index))

    sections = []
    for position, (level, text, start) in enumerate(headings):
        end = next(
            (other_start for other_level, _, other_start in headings[position + 1:]
             if other_level <= level),
            len(lines),
        )
        sections.append((text, "\n".join(lines[start + 1:end])))
    return sections


def parse_provenance(proposal: dict) -> list[tuple[str | None, int]]:
    """Parse ``provenance`` into ``(repo, number)`` pull-request references.

    Free text is rejected outright: provenance is the link between the PR being
    migrated and the roadmap it is being attributed to, so every entry has to name
    a pull request that ``verify_provenance`` can resolve and check.
    """
    pr = proposal["pr"]
    provenance = proposal["provenance"]
    if not isinstance(provenance, list) or not provenance:
        raise ValueError(f"#{pr}: provenance must be a nonempty list of PR references")
    refs: list[tuple[str | None, int]] = []
    for item in provenance:
        match = PROVENANCE_REF.fullmatch(item.strip()) if isinstance(item, str) else None
        if match is None:
            raise ValueError(
                f"#{pr}: provenance entry {item!r} is not a #N or pull-request URL"
            )
        number = int(match.group("number"))
        if number == pr:
            raise ValueError(f"#{pr}: provenance cannot cite the PR being migrated")
        if (match.group("repo"), number) not in refs:
            refs.append((match.group("repo"), number))
    return refs


def verify_provenance(
    repo: str,
    record: dict,
    areas: set[str],
    target_files: list[str],
) -> None:
    """Check that the cited PRs really tie the migrated PR to the roadmap area.

    Each one must be a merged PR of this repository that the production classifier,
    or the label that classifier already applied, attributes to the same area; and
    at least one must have touched a file the migrated PR also changes. Without the
    overlap the citation would say nothing about *this* PR.
    """
    pr = record["pr"]
    area = record["roadmap"]
    expected = roadmap_label.area_label(area)
    target = set(target_files)
    overlapping = []
    for ref_repo, number in parse_provenance(record):
        if ref_repo is not None and ref_repo != repo:
            raise ValueError(f"#{pr}: provenance #{number} is not a {repo} pull request")
        try:
            state = pr_state(repo, number)
        except RuntimeError as exc:
            raise ValueError(f"#{pr}: provenance #{number} does not resolve: {exc}") from exc
        if state.get("state") != "MERGED":
            raise ValueError(f"#{pr}: provenance #{number} is not merged")
        files = changed_files(state)
        label = roadmap_label.classify(
            state.get("title") or "", state.get("body") or "", files, areas)
        if label != expected and expected not in roadmap_labels(state):
            raise ValueError(
                f"#{pr}: provenance #{number} is not attributed to {area} "
                f"(classifier says {label})"
            )
        if target & set(files):
            overlapping.append(number)
    if not overlapping:
        raise ValueError(
            f"#{pr}: no provenance PR touches a file this PR changes, so the "
            f"citation does not connect it to {area}"
        )


def validate_evidence(
    proposal: dict,
    areas: set[str],
    roadmap_dir: pathlib.Path,
) -> tuple[int, str]:
    required = ("pr", "roadmap", "roadmap_file", "roadmap_heading", "roadmap_quote", "provenance")
    missing = [name for name in required if name not in proposal]
    if missing:
        raise ValueError(f"proposal missing {', '.join(missing)}")
    pr = proposal["pr"]
    area = proposal["roadmap"]
    if not isinstance(pr, int) or pr <= 0:
        raise ValueError("proposal pr must be a positive integer")
    if area not in areas:
        raise ValueError(f"#{pr}: {area!r} is not an active or completed roadmap")
    for name in ("roadmap_file", "roadmap_heading", "roadmap_quote"):
        if not isinstance(proposal[name], str) or not proposal[name].strip():
            raise ValueError(f"#{pr}: {name} must be nonempty")
    parse_provenance(proposal)

    relative = pathlib.PurePosixPath(proposal["roadmap_file"])
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError(f"#{pr}: roadmap_file must stay inside the roadmap checkout")
    expected_prefixes = {
        ("TauCetiRoadmap", area),
        ("Completed", area),
    }
    if tuple(relative.parts[:2]) not in expected_prefixes:
        raise ValueError(f"#{pr}: roadmap_file is not within the {area} roadmap")
    path = roadmap_dir / pathlib.Path(*relative.parts)
    if not path.is_file():
        raise ValueError(f"#{pr}: roadmap_file does not exist: {relative}")
    contents = path.read_text(encoding="utf-8")
    heading = proposal["roadmap_heading"].strip()
    sections = [text for name, text in heading_sections(contents) if name == heading]
    if not sections:
        raise ValueError(f"#{pr}: roadmap_heading is not an exact Markdown heading")
    quote = proposal["roadmap_quote"].strip()
    if not any(quote in section for section in sections):
        raise ValueError(f"#{pr}: roadmap_quote is not under the cited roadmap_heading")
    return pr, area


def prepare_record(
    repo: str,
    proposal: dict,
    areas: set[str],
    roadmap_dir: pathlib.Path,
) -> dict:
    pr, area = validate_evidence(proposal, areas, roadmap_dir)
    state = pr_state(repo, pr)
    if not REFACTOR_TITLE.match(state.get("title") or ""):
        raise ValueError(f"#{pr}: title is not a conventional refactor title")
    if state.get("state") not in {"MERGED", "OPEN"}:
        raise ValueError(f"#{pr}: closed-unmerged PRs are outside migration scope")
    files = changed_files(state)
    if roadmap_label.is_infra(files):
        raise ValueError(f"#{pr}: infrastructure/empty diff is outside migration scope")
    if roadmap_label.is_pin_only(files):
        raise ValueError(f"#{pr}: pin-only diff is outside migration scope")
    verify_provenance(repo, proposal, areas, files)
    old_labels = roadmap_labels(state)
    expected = roadmap_label.area_label(area)
    if old_labels not in ([roadmap_label.NONE_LABEL], [expected]):
        raise ValueError(
            f"#{pr}: expected roadmap/none or {expected}, found {old_labels}"
        )

    old_body = state.get("body") or ""
    new_body = insert_roadmap_line(old_body, area)
    if new_body == old_body:
        raise ValueError(f"#{pr}: body already has the requested declaration")

    return {
        **proposal,
        "title": state.get("title") or "",
        "old_body": old_body,
        "old_body_sha256": body_hash(old_body),
        "old_roadmap_labels": old_labels,
        "new_body": new_body,
        "new_body_sha256": body_hash(new_body),
    }


def validate_manifest_record(
    record: dict,
    areas: set[str],
    roadmap_dir: pathlib.Path,
) -> None:
    pr, area = validate_evidence(record, areas, roadmap_dir)
    for field in (
        "title", "old_body", "old_body_sha256", "old_roadmap_labels",
        "new_body", "new_body_sha256",
    ):
        if field not in record:
            raise ValueError(f"#{pr}: manifest missing {field}")
    if body_hash(record["old_body"]) != record["old_body_sha256"]:
        raise ValueError(f"#{pr}: old body hash is inconsistent")
    if body_hash(record["new_body"]) != record["new_body_sha256"]:
        raise ValueError(f"#{pr}: new body hash is inconsistent")
    if insert_roadmap_line(record["old_body"], area) != record["new_body"]:
        raise ValueError(f"#{pr}: new body is not the canonical insertion")
    expected = roadmap_label.area_label(area)
    if record["old_roadmap_labels"] not in ([roadmap_label.NONE_LABEL], [expected]):
        raise ValueError(
            f"#{pr}: rollback label must be roadmap/none or {expected}"
        )


def select_tranche(rows: list[dict], offset: int, limit: int) -> list[dict]:
    if offset < 0:
        raise ValueError("--offset must be nonnegative")
    if limit < 1 or limit > MAX_TRANCHE:
        raise ValueError(f"--limit must be between 1 and {MAX_TRANCHE}")
    return rows[offset:offset + limit]


def check_current(repo: str, record: dict, areas: set[str], *, applied: bool) -> dict:
    pr = record["pr"]
    expected_hash = record["new_body_sha256"] if applied else record["old_body_sha256"]
    for attempt in range(2):
        state = pr_state(repo, pr)
        actual_hash = body_hash(state.get("body") or "")
        if actual_hash == expected_hash:
            break
        if attempt == 1:
            phase = "applied" if applied else "pre-edit"
            raise ValueError(f"#{pr}: {phase} body drift ({actual_hash} != {expected_hash})")
    if not applied and roadmap_labels(state) != record["old_roadmap_labels"]:
        raise ValueError(f"#{pr}: roadmap labels drifted to {roadmap_labels(state)}")
    return state


def restore_record(repo: str, record: dict, areas: set[str]) -> None:
    patch_body(repo, record["pr"], record["old_body"])
    roadmap_label.apply_label(
        repo, record["pr"], record["old_roadmap_labels"][0], areas)


def apply_record(repo: str, record: dict, areas: set[str]) -> None:
    pr = record["pr"]
    before = check_current(repo, record, areas, applied=False)
    verify_provenance(repo, record, areas, changed_files(before))
    expected = roadmap_label.area_label(record["roadmap"])
    try:
        patch_body(repo, pr, record["new_body"])
        after_body = pr_state(repo, pr)
        actual_body = after_body.get("body") or ""
        actual = roadmap_label.classify(
            after_body.get("title") or "",
            actual_body,
            changed_files(after_body),
            areas,
        )
        if body_hash(actual_body) != record["new_body_sha256"]:
            raise ValueError(f"#{pr}: GitHub did not preserve the proposed body")
        if actual != expected:
            raise ValueError(f"#{pr}: production classifier returned {actual}, expected {expected}")
        roadmap_label.apply_label(repo, pr, actual, areas)
        final = check_current(repo, record, areas, applied=True)
        if roadmap_labels(final) != [expected]:
            raise ValueError(f"#{pr}: final roadmap labels are {roadmap_labels(final)}")
    except Exception:
        # Restore only when this invocation still owns the exact proposed body.
        current = pr_state(repo, pr)
        if body_hash(current.get("body") or "") == record["new_body_sha256"]:
            restore_record(repo, record, areas)
        raise


def revert_record(repo: str, record: dict, areas: set[str]) -> None:
    check_current(repo, record, areas, applied=True)
    restore_record(repo, record, areas)
    check_current(repo, record, areas, applied=False)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=REPO)
    parser.add_argument("--roadmap-dir", required=True, type=pathlib.Path)
    sub = parser.add_subparsers(dest="command", required=True)

    prepare = sub.add_parser("prepare", help="capture rollback state from proposal JSONL")
    prepare.add_argument("--proposals", required=True, type=pathlib.Path)
    prepare.add_argument("--manifest", required=True, type=pathlib.Path)

    for command in ("check", "dry-run", "apply", "revert"):
        action = sub.add_parser(command)
        action.add_argument("--manifest", required=True, type=pathlib.Path)
        action.add_argument("--offset", type=int, default=0)
        action.add_argument("--limit", type=int, default=MAX_TRANCHE)

    args = parser.parse_args(argv)
    areas = roadmap_label.canonical_areas(args.roadmap_dir)
    if not areas:
        parser.error(f"no roadmap areas found under {args.roadmap_dir}")

    if args.command == "prepare":
        proposals = read_jsonl(args.proposals)
        records = [
            prepare_record(args.repo, proposal, areas, args.roadmap_dir)
            for proposal in proposals
        ]
        write_jsonl(args.manifest, records)
        print(f"prepared {len(records)} reversible record(s) in {args.manifest}")
        return 0

    rows = read_jsonl(args.manifest)
    for record in rows:
        validate_manifest_record(record, areas, args.roadmap_dir)
    try:
        tranche = select_tranche(rows, args.offset, args.limit)
    except ValueError as exc:
        parser.error(str(exc))

    failures = []
    for record in tranche:
        pr = record["pr"]
        try:
            if args.command in {"check", "dry-run"}:
                state = check_current(args.repo, record, areas, applied=False)
                verify_provenance(args.repo, record, areas, changed_files(state))
            elif args.command == "apply":
                apply_record(args.repo, record, areas)
            else:
                revert_record(args.repo, record, areas)
            print(f"{args.command}: #{pr} {record['roadmap']}")
        except Exception as exc:  # noqa: BLE001 -- finish the tranche, then fail
            failures.append((pr, str(exc)))
            print(f"FAILED #{pr}: {exc}", file=sys.stderr)

    print(
        f"{args.command}: {len(tranche)} selected, "
        f"{len(tranche) - len(failures)} succeeded, {len(failures)} failed"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
