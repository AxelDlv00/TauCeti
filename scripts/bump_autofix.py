#!/usr/bin/env python3
"""bump_autofix.py — apply the mechanical renames a mathlib bump asks for.

Almost all bump breakage has one shape: code that landed on main uses a name the new
mathlib deprecates, and the compiler names both halves of the fix.

    error: TauCeti/.../DiamondOperators.lean:99:8:
        `ModularForm.IsGLPos.coe_smul` has been deprecated: Use `FunLike.coe_smul` instead

#1986 lost four merge-group rebuilds waiting for a human to type that. Only deprecations
naming a replacement are mechanical; an unknown identifier, or a proof a changed lemma
statement broke, is reported unfixed and left to the stuck-bump alert.

THE LOG IS UNTRUSTED: it is a build's stdout, not an authenticated compiler channel, and
the edits are committed with an App token. bump-autofix.yml reads only logs from a build
of the machine-owned bump branch, and this module independently refuses to let a log line
reach outside the library — the path grammar admits no `..`, and `_resolve_under` rechecks
containment on the resolved real path.

Being wrong is cheap: the push re-runs the full build, so a bad rename stays red exactly
as the unrenamed source did.

    bump_autofix.py --log build.log [--root .] [--applied-files F]

Exit 0 if it changed a file, 3 if there was nothing it could fix.
"""

import argparse
import collections
import os
import re
import sys

# Path components are restricted to what a Lean module name can hold, which is what keeps
# `..` and absolute paths out — the first of two independent containment gates.
_PATH = r"TauCeti(?:\.lean|(?:/[A-Za-z0-9_][A-Za-z0-9_'-]*)+\.lean)"
_AT = r"(?P<path>" + _PATH + r"):(?P<line>\d+):(?P<col>\d+): "

# Anchored on the `path:line:col:` prefix, not the line start: `gh run view --log-failed`
# puts a job/step/timestamp prefix on every line. IGNORECASE and the gap between the two
# backticked names absorb the wordings mathlib writes by hand.
RENAME_RE = re.compile(
    _AT + r"`(?P<old>[^`\s]+)` has been deprecated:[^`]*?\buse `(?P<new>[^`\s]+)` instead",
    re.IGNORECASE)
DEPRECATED_RE = re.compile(_AT + r"`(?P<old>[^`\s]+)` has been deprecated")
UNKNOWN_RE = re.compile(_AT + r"unknown (?:identifier|constant) '(?P<old>[^']+)'")
# Every dot component non-empty. Without this a forged `` `.` `` yields the empty suffix,
# and `startswith("")` is true at every position — an insertion matching no token at all.
NAME_RE = re.compile(r"[^\s`.]+(?:\.[^\s`.]+)*\Z")

Rename = collections.namedtuple("Rename", "path line col old new")


def renames_from_log(text):
    """Deduplicated `Rename`s, in file/line/column order. A log can repeat a diagnostic,
    and applying one twice at the same position would corrupt the line."""
    seen = {}
    for m in RENAME_RE.finditer(text):
        old, new = m.group("old"), m.group("new")
        if NAME_RE.match(old) and NAME_RE.match(new):
            seen[Rename(m.group("path"), int(m.group("line")), int(m.group("col")),
                        old, new)] = None
    return sorted(seen, key=lambda r: (r.path, r.line, r.col))


def unfixable_from_log(text):
    """`(path, line, col, name, why)` for breakage with no replacement to substitute, so a
    partial repair says so instead of looking complete."""
    fixable = {(r.path, r.line, r.col) for r in renames_from_log(text)}
    out = {}
    for m in DEPRECATED_RE.finditer(text):
        at = (m.group("path"), int(m.group("line")), int(m.group("col")))
        if at not in fixable:
            out[at + (m.group("old"), "deprecated, but no replacement is named")] = None
    for m in UNKNOWN_RE.finditer(text):
        at = (m.group("path"), int(m.group("line")), int(m.group("col")))
        out[at + (m.group("old"), "unknown identifier; nothing to substitute")] = None
    return sorted(out, key=lambda t: t[:3])


def _is_name_char(ch):
    """Could `ch` continue a Lean identifier? `isalnum` is Unicode-aware, so it covers the
    Greek letters and subscripts Lean names are full of (`ε`, `x₀`) and not `,`, `]`, `⟩`."""
    return bool(ch) and (ch.isalnum() or ch in "_'!?.")


def _dot_suffixes(name):
    """`A.B.c` -> `["A.B.c", "B.c", "c"]`: Lean reports the full name, but the source may
    have written any suffix (inside `namespace A`, or after `open A.B`). Longest first."""
    parts = name.split(".")
    return [c for c in (".".join(parts[i:]) for i in range(len(parts))) if c]


def _resolve_under(root, path):
    """The real path `path` names inside `root`, or None if it escapes. The second gate,
    independent of the path grammar, because a forged line reaching outside the library
    would be edited and then committed with an App token."""
    base = os.path.realpath(root)
    full = os.path.realpath(os.path.join(base, path))
    if full == os.path.join(base, "TauCeti.lean"):
        return full
    library = os.path.join(base, "TauCeti") + os.sep
    return full if full.startswith(library) and full.endswith(".lean") else None


def apply_renames(root, renames):
    """Rewrite files under `root`; returns `(applied, [(rename, why), ...])`.

    Each edit replaces the token AT THE REPORTED POSITION, never every occurrence: Lean
    emits one diagnostic per occurrence, so this still reaches them all, while a file-wide
    substitution would also rewrite the name in a comment or inside a longer identifier.
    It refuses unless the text there really is the name (or a suffix) and both starts and
    ends there, so a stale log skips rather than edits blind. The replacement is fully
    qualified even where the old name was not, since we cannot know what is open there.
    Edits run bottom-right upwards so one never shifts another's position.
    """
    applied, skipped = [], []
    by_file = collections.defaultdict(list)
    for r in renames:
        by_file[r.path].append(r)
    for path, group in sorted(by_file.items()):
        full = _resolve_under(root, path)
        if full is None:
            skipped += [(r, "path escapes TauCeti/ — refusing to edit it") for r in group]
            continue
        if os.path.islink(os.path.join(root, path)) or not os.path.isfile(full):
            skipped += [(r, "not a regular file in the working tree") for r in group]
            continue
        with open(full, encoding="utf-8") as fh:
            lines = fh.read().split("\n")
        changed = False
        for r in sorted(group, key=lambda r: (r.line, r.col), reverse=True):
            if not 1 <= r.line <= len(lines):
                skipped.append((r, f"line {r.line} is past the end of the file"))
                continue
            text = lines[r.line - 1]
            if r.col > 0 and _is_name_char(text[r.col - 1:r.col]):
                skipped.append((r, f"column {r.col} is mid-identifier; the source has moved"))
                continue
            for cand in _dot_suffixes(r.old):
                end = r.col + len(cand)
                if text.startswith(cand, r.col) and not _is_name_char(text[end:end + 1]):
                    lines[r.line - 1] = text[:r.col] + r.new + text[end:]
                    applied.append(r)
                    changed = True
                    break
            else:
                skipped.append((r, f"no `{r.old}` at column {r.col}; the source has moved"))
        if changed:
            with open(full, "w", encoding="utf-8") as fh:
                fh.write("\n".join(lines))
    return applied, skipped


def summary(applied, skipped, unfixable):
    """Printed on stdout, and reused verbatim as the commit-message body."""
    out = [f"Applied {len(applied)} mechanical rename(s) named by the build:"
           if applied else "Applied no renames."]
    out += [f"  {r.path}:{r.line}:{r.col}  {r.old} -> {r.new}" for r in applied]
    if skipped:
        out += ["", f"Skipped {len(skipped)} rename(s):"]
        out += [f"  {r.path}:{r.line}:{r.col}  {r.old} -> {r.new}: {why}"
                for r, why in skipped]
    if unfixable:
        out += ["", f"{len(unfixable)} failure(s) need a human (no replacement is named):"]
        out += [f"  {p}:{ln}:{col}  {name}: {why}" for p, ln, col, name, why in unfixable]
    return "\n".join(out)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--log", required=True)
    ap.add_argument("--root", default=".")
    ap.add_argument("--applied-files",
                    help="write each edited path here, so the caller stages only those")
    args = ap.parse_args(argv[1:])
    with open(args.log, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    applied, skipped = apply_renames(args.root, renames_from_log(text))
    print(summary(applied, skipped, unfixable_from_log(text)))
    if args.applied_files:
        with open(args.applied_files, "w", encoding="utf-8") as fh:
            fh.write("".join(p + "\n" for p in sorted({r.path for r in applied})))
    return 0 if applied else 3


if __name__ == "__main__":
    sys.exit(main(sys.argv))
