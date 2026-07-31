#!/usr/bin/env python3
"""Synchronize TauCeti's locked dependencies into the docs project.

The docs project has additional direct dependencies, so it needs its own Lake
manifest.  Its inherited TauCeti dependencies must nevertheless use the exact
resolved revisions in the parent manifest, even when the parent's lakefile
nominates a moving branch such as Mathlib's ``master``.
"""

from __future__ import annotations

import json
from pathlib import Path


DOCBUILD_DIR = Path(__file__).resolve().parent
ROOT_MANIFEST = DOCBUILD_DIR.parent / "lake-manifest.json"
DOCS_MANIFEST = DOCBUILD_DIR / "lake-manifest.json"


def packages_by_name(manifest: dict, path: Path) -> dict[str, dict]:
    packages = manifest["packages"]
    by_name = {package["name"]: package for package in packages}
    if len(by_name) != len(packages):
        raise SystemExit(f"{path} contains duplicate package names")
    return by_name


root = json.loads(ROOT_MANIFEST.read_text())
docs = json.loads(DOCS_MANIFEST.read_text())
root_packages = packages_by_name(root, ROOT_MANIFEST)
packages_by_name(docs, DOCS_MANIFEST)

merged = []
copied = set()
for package in docs["packages"]:
    name = package["name"]
    if name not in root_packages:
        merged.append(package)
        continue
    inherited = dict(root_packages[name])
    inherited["inherited"] = True
    merged.append(inherited)
    copied.add(name)

# A Mathlib update can introduce a new transitive dependency that was not in the
# previously committed docs manifest.
for package in root["packages"]:
    name = package["name"]
    if name in copied:
        continue
    inherited = dict(package)
    inherited["inherited"] = True
    merged.append(inherited)
    copied.add(name)

missing = set(root_packages) - copied
if missing:
    raise SystemExit(f"failed to synchronize packages: {', '.join(sorted(missing))}")

docs["packages"] = merged
DOCS_MANIFEST.write_text(json.dumps(docs, ensure_ascii=False, indent=1) + "\n")

print(f"synchronized {len(copied)} TauCeti dependency pins into {DOCS_MANIFEST}")
