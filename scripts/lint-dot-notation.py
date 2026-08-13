#!/usr/bin/env python3
"""Flag Mathlib namespaces recreated inside `namespace TauCeti`.

Tau Ceti's convention: material lives in the `TauCeti` namespace, except when it is dot
notation on something already defined in Lean or Mathlib. A declaration whose first explicit
argument has an existing Mathlib type belongs in that type's namespace, so `x.foo` elaborates
for consumers and the declaration can be upstreamed without renaming.

The failure this catches is `namespace TauCeti` wrapping `namespace Foo` for a Mathlib type
`Foo`, which yields `TauCeti.Foo.bar` and silently blocks `x.bar`.

Deliberately conservative — three classes of false positive are excluded:

  * Mathlib *organisational* namespaces (`AlgebraicGeometry`, `MeasureTheory`, ...). Filing
    Tau Ceti's own material under those is normal and is not a dot-notation question.
  * Namespaces naming a type Tau Ceti defines itself, even where the name also exists in
    Mathlib (`Cycle` for contour cycles, `Hom` for comodule homs, `Relator`).
  * Declarations that take no argument of the type, where dot notation would not apply.

Run: python3 scripts/lint-dot-notation.py [--baseline scripts/lint-dot-notation-baseline.txt]

Reports only violations absent from the baseline, so the existing backlog does not fail CI
while new files are held to the convention. Exits 1 if any new violation is found.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

# Mathlib namespaces that organise files rather than name a type. Nesting Tau Ceti material
# under these is not a dot-notation defect.
ORGANISATIONAL = {
    "AlgebraicGeometry", "MeasureTheory", "Algebra", "Lie", "CategoryTheory", "Topology",
    "Analysis", "NumberTheory", "Combinatorics", "Order", "Set", "Function", "Filter",
    "Polynomial", "RingTheory", "LinearAlgebra", "ProbabilityTheory", "Geometry", "Complex",
    "Real", "Nat", "Int", "Finset", "List",
}

DECL = re.compile(
    r"^(?:public\s+|private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance)\s+([\w.']+)"
)
NAMESPACE = re.compile(r"^namespace\s+([\w.]+)\s*$")
END = re.compile(r"^end\s+([\w.]+)\s*$")
TYPE_DECL = re.compile(
    r"^(?:public\s+|private\s+|protected\s+|noncomputable\s+)*"
    r"(?:structure|inductive|abbrev|def)\s+([A-Z][\w']*)",
    re.M,
)


def mathlib_namespaces(root: pathlib.Path) -> set[str]:
    names: set[str] = set()
    for f in root.rglob("*.lean"):
        for m in re.finditer(r"^namespace ([A-Z][\w.]*)", f.read_text(errors="ignore"), re.M):
            names.update(m.group(1).split("."))
    return names


def own_types(sources: dict[pathlib.Path, str]) -> set[str]:
    names: set[str] = set()
    for text in sources.values():
        names.update(m.group(1) for m in TYPE_DECL.finditer(text))
    return names


def violations(sources, mathlib_ns, owned):
    for path, text in sorted(sources.items()):
        lines = text.splitlines()
        stack: list[str] = []
        for i, line in enumerate(lines, start=1):
            if m := NAMESPACE.match(line):
                stack.extend(m.group(1).split("."))
                continue
            if e := END.match(line):
                for _ in e.group(1).split("."):
                    if stack:
                        stack.pop()
                continue
            d = DECL.match(line)
            if not d or not stack or stack[0] != "TauCeti":
                continue
            inner = [s for s in stack[1:]
                     if s in mathlib_ns and s not in ORGANISATIONAL and s not in owned]
            if not inner:
                continue
            ns = inner[-1]
            signature = " ".join(lines[i - 1:i + 5])
            # dot notation only applies if some binder actually has this type
            if re.search(rf"[:(\[]\s*{re.escape(ns)}[\s.)\]]", signature) or \
               re.search(rf":\s*{re.escape(ns)}\b", signature):
                yield f"{path}:{i}: TauCeti.{ns}.{d.group(1)}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", default="scripts/lint-dot-notation-baseline.txt")
    ap.add_argument("--write-baseline", action="store_true")
    args = ap.parse_args()

    mathlib = pathlib.Path(".lake/packages/mathlib/Mathlib")
    if not mathlib.is_dir():
        print("lint-dot-notation: no Mathlib checkout; skipping", file=sys.stderr)
        return 0

    sources = {p: p.read_text(errors="ignore") for p in pathlib.Path("TauCeti").rglob("*.lean")}
    found = sorted(violations(sources, mathlib_namespaces(mathlib), own_types(sources)))

    baseline_path = pathlib.Path(args.baseline)
    if args.write_baseline:
        baseline_path.write_text("".join(f"{v}\n" for v in found))
        print(f"lint-dot-notation: wrote {len(found)} baseline entries")
        return 0

    baseline = set()
    if baseline_path.is_file():
        baseline = {l.strip() for l in baseline_path.read_text().splitlines() if l.strip()}

    # compare on declaration identity, not line number, so unrelated edits do not trip it
    def key(v: str) -> str:
        return v.split(": ", 1)[1]

    known = {key(b) for b in baseline}
    new = [v for v in found if key(v) not in known]

    print(f"lint-dot-notation: {len(found)} total, {len(baseline)} grandfathered, {len(new)} new")
    if new:
        print("\nA Mathlib type's namespace is opened inside `namespace TauCeti`, so dot")
        print("notation on that type does not elaborate. Close `namespace TauCeti` around the")
        print("block and reopen it after, or drop the wrapper if the file holds nothing else.")
        print("Watch for `open`/`variable` lines inside the wrapper: they must be hoisted to")
        print("file scope or the moved block loses them.\n")
        for v in new:
            print(f"  {v}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
