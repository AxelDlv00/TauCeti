import Mathlib.Tactic.Linter.Header
import Mathlib.Tactic.Linter.TextBased

/-!
# Copyright-header and style-baseline audit for Tau Ceti sources

Human-owned governance machinery. Mathlib's `linter.style.header` deliberately skips a module
unless the library root imports it. Tau Ceti's root is intentionally empty, so the ordinary
command linter never reaches these files. This audit calls the linter's public
`copyrightHeaderChecks` function on the validated source list supplied by `scripts/lint-style.sh`.

This intentionally enforces the copyright block and `Authors:` contract from issue #3546, not the
same command linter's separate broad-import, duplicate-import, directory-dependency, or module-doc
checks. The latter require elaborator state and are outside this text-based CI check.

It also uses Mathlib's public `lintModules` entry point with no exceptions to emit the actual
text-style violations on stdout. The wrapper captures that output, compares it with
`scripts/nolints-style.txt`, and rejects stale exceptions.

Run via `lake env lean --run scripts/HeaderStyle.lean ...`, as part of `scripts/lint-style.sh`.
-/

open Mathlib.Linter
open Mathlib.Linter.TextBased

/-- Mathlib's default required license line, also used by Tau Ceti. -/
def expectedLicense := Mathlib.Linter.linter.style.header.license.defValue

def pathToModule (path : String) : Lean.Name :=
  (path.dropEnd 5).toString.splitOn "/" |>.foldl
    (fun name component => name.mkStr component) .anonymous

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "header-style: received no validated TauCeti source files; the audit is miswired."
    return 1
  let mut failures : UInt32 := 0
  for path in args do
    -- `copyrightHeaderChecks` stops at the end of the first copyright block, so passing the whole
    -- source is equivalent to Mathlib's leading-trivia call while avoiding elaborator state.
    let errors := copyrightHeaderChecks (← IO.FS.readFile path) expectedLicense
    unless errors.isEmpty do
      failures := failures + 1
      for (_, message) in errors do
        IO.eprintln s!"{path}: {message}"
  if failures != 0 then
    IO.eprintln s!"header-style: {failures} source file(s) have malformed copyright headers."
  else
    IO.eprintln s!"header-style: all {args.length} TauCeti source file(s) have conforming headers."
  let opts : Lean.Linter.LinterOptions := { toOptions := {}, linterSets := {} }
  discard <| lintModules opts #[] (args.toArray.map pathToModule) .exceptionsFile false
  return min failures 125
