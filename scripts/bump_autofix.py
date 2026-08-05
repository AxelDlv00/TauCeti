#!/usr/bin/env python3
"""bump_autofix.py — apply the mechanical renames a mathlib bump asks for.

Almost all bump breakage has one shape. A PR lands on main using a name the *current*
mathlib is happy with; the bump moves to a mathlib that has deprecated it; the bump's
build fails with a diagnostic that names both the old name and its replacement:

    error: TauCeti/NumberTheory/ModularForms/DiamondOperators.lean:99:8:
        `ModularForm.IsGLPos.coe_smul` has been deprecated: Use `FunLike.coe_smul` instead

That is exactly what happened to #1986, which then lost its merge-group rebuild four
times in a row waiting for a human to type the substitution. Nothing about the edit
needs judgement: the compiler has already located the occurrence and named what to put
there. This module turns such a build log into the edits, so `bump-autofix.yml` can push
them to the bump branch instead of the bump waiting a day for a person.

WHAT IT WILL NOT DO. Only deprecations that name a replacement are mechanical. An
`unknown identifier` or `unknown constant` says a name is gone but not what replaced it,
and a proof that broke because a lemma's statement changed needs a mathematician. Those
are reported as unfixed and left for the `stuck-bump` alert; guessing at them would push
noise onto the bump branch and burn the 85-minute rebuild the alert is trying to save.

THE LOG IS UNTRUSTED INPUT. It is a build process's stdout, not an authenticated compiler
channel, so anything that elaborates in that build can print a line shaped like a
diagnostic. `bump-autofix.yml` therefore reads only logs from a build of the machine-owned
bump branch, and this module independently refuses to let a log line reach outside the
library: the path grammar (`_PATH`) admits no `..` and no absolute path, and
`_resolve_under` re-checks containment against the resolved real path. Two independent
gates, because the edits are committed with an App token.

WHY IT IS SAFE TO BE WRONG. Every edit is a proposal, not a verdict: the push it feeds
re-runs the full sandboxed build, so a mistaken rename simply stays red exactly as the
un-renamed source did. The failure mode is a wasted rebuild, never a bad merge. The
edits themselves are still made conservatively -- see `apply_renames` -- so a wasted
rebuild is rare rather than routine.

Usage:
    bump_autofix.py --log build.log [--root .]

Prints a human-readable summary (which the workflow puts in the commit message) and
exits 0 when it changed at least one file, 3 when there was nothing it could fix, and 1
on a usage error. Reads and writes only files under `--root`; runs nothing.
"""

import argparse
import collections
import os
import re
import sys

# The path a diagnostic may name. Every path component is restricted to characters a Lean
# module name can contain, which is what keeps `..` (and `/`, and a leading `/`) out: a log
# line reading `TauCeti/../scripts/lint-env.sh` must not be able to steer an edit outside
# the library, and this is the first of two independent places that is enforced (see
# `_resolve_under`). The whole log is untrusted input -- it is a build's stdout, not an
# authenticated compiler channel -- so the grammar here is an allowlist, never a filter.
_PATH = r"TauCeti(?:\.lean|(?:/[A-Za-z0-9_][A-Za-z0-9_'-]*)+\.lean)"

# A Lean diagnostic that names both the deprecated name and its replacement. Anchored on
# the `TauCeti/...lean:line:col:` prefix rather than on the start of the line, because the
# log this reads is `gh run view --log-failed` output, whose every line carries a
# job/step/timestamp prefix. Lean's own wording is "Use `X` instead"; the IGNORECASE and
# the `[^`]*?` between the two backticked names absorb the variants mathlib writes by
# hand (`use \`X\` instead`, "deprecated: use `X` instead (since ...)").
RENAME_RE = re.compile(
    r"(?P<path>" + _PATH + r"):(?P<line>\d+):(?P<col>\d+): "
    r"`(?P<old>[^`\s]+)` has been deprecated:[^`]*?\buse `(?P<new>[^`\s]+)` instead",
    re.IGNORECASE)

# Every deprecation diagnostic, including the ones with no replacement to substitute.
# Counted only so the summary can say how much of the breakage was mechanical.
DEPRECATED_RE = re.compile(
    r"(?P<path>" + _PATH + r"):(?P<line>\d+):(?P<col>\d+): "
    r"`(?P<old>[^`\s]+)` has been deprecated")

# A name Lean cannot resolve at all. Not fixable here (no replacement is named), but
# worth reporting: it is the other half of what a bump breaks.
UNKNOWN_RE = re.compile(
    r"(?P<path>" + _PATH + r"):(?P<line>\d+):(?P<col>\d+): "
    r"unknown (?:identifier|constant) '(?P<old>[^']+)'")

Rename = collections.namedtuple("Rename", "path line col old new")


def renames_from_log(text):
    """Deduplicated `Rename`s parsed from a build log, in file/line/column order.

    A log can repeat a diagnostic (a re-run step, a summary block), and applying the same
    substitution twice at the same position would corrupt the line, so identity is the
    whole tuple and duplicates collapse here rather than at the edit.
    """
    seen = {}
    for m in RENAME_RE.finditer(text):
        r = Rename(m.group("path"), int(m.group("line")), int(m.group("col")),
                   m.group("old"), m.group("new"))
        seen[r] = None
    return sorted(seen, key=lambda r: (r.path, r.line, r.col))


def unfixable_from_log(text):
    """`(path, line, col, name, why)` for breakage this module cannot mechanically fix.

    A deprecation whose message names no replacement, and any unresolvable name. Reported
    so a run that fixed only part of the breakage says so out loud instead of looking
    like a complete repair.
    """
    fixable = {(r.path, r.line, r.col) for r in renames_from_log(text)}
    out = {}
    for m in DEPRECATED_RE.finditer(text):
        at = (m.group("path"), int(m.group("line")), int(m.group("col")))
        if at not in fixable:
            out[at + (m.group("old"), "deprecated, but the message names no replacement")] = None
    for m in UNKNOWN_RE.finditer(text):
        at = (m.group("path"), int(m.group("line")), int(m.group("col")))
        out[at + (m.group("old"), "unknown identifier; no replacement to substitute")] = None
    return sorted(out, key=lambda t: (t[0], t[1], t[2]))


def _is_name_char(ch):
    """Could `ch` continue a Lean identifier? Used only to refuse a partial-token edit.

    `isalnum` is the right primitive here because Python evaluates it over Unicode: it is
    true for the Greek letters, subscript digits and modifier letters that Lean names are
    full of (`ε`, `x₀`, `Mₐ`) and false for the delimiters that end one (`,`, `]`, `⟩`).
    """
    return bool(ch) and (ch.isalnum() or ch in "_'!?.")


def _dot_suffixes(name):
    """`A.B.c` -> `["A.B.c", "B.c", "c"]`: the ways that name can appear in source.

    Lean reports the deprecation under the FULL name, but the source may have written any
    suffix of it -- inside `namespace A`, or after `open A.B`. Longest first, so the most
    specific match wins.
    """
    parts = name.split(".")
    return [".".join(parts[i:]) for i in range(len(parts))]


def _resolve_under(root, path):
    """The real path `path` names inside `root`, or None if it escapes.

    The SECOND, independent containment check (the first is the path grammar in `_PATH`),
    because the consequence of getting this wrong is that a forged log line edits a file
    the App token then commits. It resolves symlinks on both sides and compares the results,
    so neither `..` nor a symlink planted under `TauCeti/` can reach outside the library.
    Nothing but `TauCeti/**.lean` and the root `TauCeti.lean` is ever writable from here.
    """
    base = os.path.realpath(root)
    full = os.path.realpath(os.path.join(base, path))
    if full == os.path.join(base, "TauCeti.lean"):
        return full
    library = os.path.join(base, "TauCeti") + os.sep
    if full.startswith(library) and full.endswith(".lean"):
        return full
    return None


def apply_renames(root, renames):
    """Rewrite the files under `root`. Returns `(applied, skipped)`.

    `applied` is the `Rename`s written; `skipped` is `(rename, why)` for the rest.

    Two things make an edit conservative enough to push unattended:

      * It replaces the token AT THE REPORTED POSITION, never every occurrence of the
        name in the file. Lean reports one diagnostic per occurrence, so a
        position-anchored edit still reaches all of them, while a file-wide substitution
        would also rewrite the name inside a docstring, a comment, or a longer identifier
        that merely starts with it.
      * It refuses unless the text at that position really is the deprecated name (or a
        suffix of it) AND ends there. If the source has moved under the log -- a stale
        log, a line already edited by an earlier rename in this same run -- the edit is
        skipped rather than applied blind.

    The replacement is the FULLY QUALIFIED new name even where the old one was written
    unqualified, because this module cannot know which namespaces are open at that point;
    a fully qualified name resolves wherever an unqualified one did.

    Edits within a file are applied from the bottom right upwards, so an earlier edit
    never shifts the line/column of one still to come.
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
    """The report printed on stdout, and reused verbatim as the commit-message body."""
    out = []
    if applied:
        out.append(f"Applied {len(applied)} mechanical rename(s) named by the build:")
        out += [f"  {r.path}:{r.line}:{r.col}  {r.old} -> {r.new}" for r in applied]
    else:
        out.append("Applied no renames.")
    if skipped:
        out.append("")
        out.append(f"Skipped {len(skipped)} rename(s):")
        out += [f"  {r.path}:{r.line}:{r.col}  {r.old} -> {r.new}: {why}"
                for r, why in skipped]
    if unfixable:
        out.append("")
        out.append(f"{len(unfixable)} failure(s) need a human (no replacement is named):")
        out += [f"  {p}:{ln}:{col}  {name}: {why}" for p, ln, col, name, why in unfixable]
    return "\n".join(out)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--log", required=True, help="build log to read the diagnostics from")
    ap.add_argument("--root", default=".", help="repository root to rewrite (default: .)")
    ap.add_argument("--applied-files",
                    help="write the repo-relative path of each edited file here, one per "
                         "line, so the caller can stage exactly those and nothing else")
    args = ap.parse_args(argv[1:])
    with open(args.log, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    applied, skipped = apply_renames(args.root, renames_from_log(text))
    print(summary(applied, skipped, unfixable_from_log(text)))
    if args.applied_files:
        edited = sorted({r.path for r in applied})
        with open(args.applied_files, "w", encoding="utf-8") as fh:
            fh.write("".join(p + "\n" for p in edited))
    return 0 if applied else 3


if __name__ == "__main__":
    sys.exit(main(sys.argv))
