#!/usr/bin/env python3
"""Validate the review bot's exact-commit Mathlib pin in lakefile.toml.

The ordinary bump guard requires the Lake configuration to be byte-identical to
the trusted base.  The incompatibility tracker is the one exception: its PR
replaces Mathlib's nominated branch with the immutable first-known-bad SHA so the
PR builds against the commit it is meant to repair.  To leave an exact pin, the
same bot changes that line back to ``master`` while either advancing the manifest
pin or, when the reported last-known-good commit equals the existing pin, changing
only Mathlib's manifest ``inputRev``.  This helper proves that the sole lakefile
change is Mathlib's revision, that Mathlib's manifest ``rev``/``inputRev`` fields
agree with it, and that a same-revision de-pin leaves every other manifest field
unchanged.  ``check-bump.sh`` validates the remaining manifest derivation and the
direction of any resolved-pin transition.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
import tomllib


SHA_RE = re.compile(r"[0-9a-f]{40}")
REV_LINE_RE = re.compile(r'^(\s*rev\s*=\s*)"([^"]*)"(\s*(?:#.*)?(?:\n)?)$')


class ValidationError(ValueError):
    """Raised when a proposed review-bot lakefile pin has an invalid shape."""

    pass


def _load_toml(path: pathlib.Path) -> dict:
    try:
        return tomllib.loads(path.read_text())
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise ValidationError(f"cannot parse {path.name}: {exc}") from exc


def _mathlib_require(config: dict, source: str) -> dict:
    requires = config.get("require") or []
    matches = [item for item in requires if item.get("name") == "mathlib"]
    if len(matches) != 1:
        raise ValidationError(
            f"{source} must contain exactly one [[require]] named mathlib; found {len(matches)}")
    return matches[0]


def mathlib_rev(path: pathlib.Path) -> str:
    """Return the unique Mathlib requirement's nominated revision."""

    require = _mathlib_require(_load_toml(path), path.name)
    rev = require.get("rev") or ""
    if not isinstance(rev, str):
        raise ValidationError(f"{path.name} Mathlib rev must be a string")
    return rev


def _single_changed_line(base_text: str, pr_text: str) -> tuple[str, str]:
    base_lines = base_text.splitlines(keepends=True)
    pr_lines = pr_text.splitlines(keepends=True)
    changed = [(before, after) for before, after in zip(base_lines, pr_lines) if before != after]
    if len(base_lines) != len(pr_lines) or len(changed) != 1:
        raise ValidationError("lakefile.toml must change exactly one existing line")
    return changed[0]


def _load_manifest(path: pathlib.Path, source: str) -> tuple[dict, dict]:
    try:
        manifest = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise ValidationError(f"cannot parse {path.name}: {exc}") from exc
    packages = manifest.get("packages") or []
    mathlib = [item for item in packages if item.get("name") == "mathlib"]
    if len(mathlib) != 1:
        raise ValidationError(
            f"{source} must contain exactly one package named mathlib; found {len(mathlib)}")
    return manifest, mathlib[0]


def validate(base_lakefile: pathlib.Path, pr_lakefile: pathlib.Path,
             base_manifest: pathlib.Path, pr_manifest: pathlib.Path) -> str:
    """Validate the lakefile/Mathlib-manifest relationship for a bot pin or de-pin.

    The PR must change only Mathlib's ``rev`` line, to either a 40-hex commit or
    ``master``.  An exact pin must equal the manifest's Mathlib ``rev``, and the
    manifest's Mathlib ``inputRev`` must always equal the proposed lakefile value.
    Return that proposed value.  Raise ``ValidationError`` for invalid contents
    and ``OSError`` when an input cannot be read; ``check-bump.sh`` performs the
    remaining manifest and forward-transition validation.
    """

    base_text = base_lakefile.read_text()
    pr_text = pr_lakefile.read_text()
    before, after = _single_changed_line(base_text, pr_text)
    before_match = REV_LINE_RE.fullmatch(before)
    after_match = REV_LINE_RE.fullmatch(after)
    if not before_match or not after_match:
        raise ValidationError("the sole lakefile.toml change must be a rev = \"...\" line")

    base_config = _load_toml(base_lakefile)
    pr_config = _load_toml(pr_lakefile)
    base_mathlib = _mathlib_require(base_config, "base lakefile.toml")
    pr_mathlib = _mathlib_require(pr_config, "PR lakefile.toml")
    base_rev = mathlib_rev(base_lakefile)
    pr_rev = mathlib_rev(pr_lakefile)
    if before_match.group(2) != base_rev or after_match.group(2) != pr_rev:
        raise ValidationError("the changed rev line is not Mathlib's [[require]] revision")
    if pr_rev != "master" and not SHA_RE.fullmatch(pr_rev):
        raise ValidationError(f"PR Mathlib rev {pr_rev!r} is neither master nor a 40-hex SHA")

    # Semantic backstop: after restoring only Mathlib.rev, every parsed Lake setting must match.
    pr_mathlib["rev"] = base_rev
    if pr_config != base_config:
        raise ValidationError("lakefile.toml changes settings other than Mathlib's rev")

    base_manifest_data, base_manifest_mathlib = _load_manifest(
        base_manifest, "base manifest")
    manifest, manifest_mathlib = _load_manifest(pr_manifest, "PR manifest")
    manifest_rev = manifest_mathlib.get("rev") or ""
    manifest_input = manifest_mathlib.get("inputRev") or ""
    if not SHA_RE.fullmatch(manifest_rev):
        raise ValidationError(f"manifest Mathlib rev {manifest_rev!r} is not a 40-hex SHA")
    if pr_rev != "master" and manifest_rev != pr_rev:
        raise ValidationError(
            f"lakefile Mathlib rev {pr_rev} does not match manifest rev {manifest_rev}")
    if manifest_input != pr_rev:
        raise ValidationError(
            f"manifest inputRev {manifest_input!r} must equal the bot's lakefile rev {pr_rev!r}")

    # A consecutive incompatibility can have its LKG exactly at the old FKB.
    # In that case the safe transition changes only the nomination from the
    # exact SHA back to master while leaving every resolved pin unchanged.
    base_manifest_rev = base_manifest_mathlib.get("rev") or ""
    base_manifest_input = base_manifest_mathlib.get("inputRev") or ""
    if pr_rev == "master" and manifest_rev == base_manifest_rev:
        if base_rev != base_manifest_rev or base_manifest_input != base_manifest_rev:
            raise ValidationError(
                "same-revision de-pin requires a consistently exact-pinned base")
        manifest_mathlib["inputRev"] = base_manifest_input
        if manifest != base_manifest_data:
            raise ValidationError(
                "same-revision de-pin may change only Mathlib's manifest inputRev")
    return pr_rev


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("base_lakefile", type=pathlib.Path)
    parser.add_argument("pr_lakefile", type=pathlib.Path)
    parser.add_argument("base_manifest", type=pathlib.Path)
    parser.add_argument("pr_manifest", type=pathlib.Path)
    args = parser.parse_args()
    try:
        rev = validate(
            args.base_lakefile, args.pr_lakefile, args.base_manifest, args.pr_manifest)
    except (OSError, ValidationError) as exc:
        print(f"bot lakefile validation failed: {exc}", file=sys.stderr)
        return 1
    print(f"bot lakefile validation passed: Mathlib lakefile rev set to {rev}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
