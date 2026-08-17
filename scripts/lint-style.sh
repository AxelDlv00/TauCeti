#!/usr/bin/env bash
# Run the source-based style checks over every TauCeti source file.
#
# lint-style treats its module arguments as import roots and lints only their imports. The
# library root TauCeti.lean is intentionally empty, so generate a temporary import-all module
# instead. It lives under .lake because that is the writable area in the PR build sandbox. The
# candidate TauCeti/ tree is untrusted there, so validate every discovered path before using it
# as Lean syntax; malformed or empty discovery must fail closed.
set -euo pipefail

lint_src="$(mktemp -d "$PWD/.lake/lint-style-src.XXXXXX")"
trap 'rm -rf "$lint_src"' EXIT
lint_module="$lint_src/TauCetiLint/All.lean"
mkdir -p "$(dirname "$lint_module")"

find TauCeti -type f -name '*.lean' -print0 | sort -z > "$lint_src/files"
find TauCeti -type l -print0 | sort -z > "$lint_src/symlinks"
mapfile -d '' files < "$lint_src/files"
mapfile -d '' symlinks < "$lint_src/symlinks"
if ((${#symlinks[@]} != 0)); then
  printf 'lint-style: refusing symlinked source path %q\n' "${symlinks[0]}" >&2
  exit 1
fi
if ((${#files[@]} == 0)); then
  echo 'lint-style: found no TauCeti source files; the audit is miswired.' >&2
  exit 1
fi

module_path_re="^TauCeti(/[A-Za-z_][A-Za-z0-9_']*)+\\.lean$"
printf 'import TauCeti\n' > "$lint_module"
for file in "${files[@]}"; do
  if [[ ! $file =~ $module_path_re ]]; then
    printf 'lint-style: refusing non-module source path %q\n' "$file" >&2
    exit 1
  fi
  module="${file%.lean}"
  printf 'import %s\n' "${module//\//.}" >> "$lint_module"
done
expected_imports=$((${#files[@]} + 1))
emitted_imports="$(grep -c '^import ' "$lint_module")"
if ((emitted_imports != expected_imports)); then
  echo 'lint-style: generated import root is incomplete; refusing to run.' >&2
  exit 1
fi

# Use the one validated discovery list for the copyright/Authors audit and raw style enumeration.
# Capture the latter for the baseline ratchet. Mathlib's expected raw-violation summary is filtered
# from stderr; all header or compiler diagnostics remain visible. Keep going after a header failure
# so contributors see both classes of diagnostics in one CI round.
status=0
actual_errors="$lint_src/style-errors.txt"
audit_stderr="$lint_src/audit.stderr"
if ! lake env lean --run scripts/HeaderStyle.lean "${files[@]}" \
    > "$actual_errors" 2> "$audit_stderr"; then
  status=1
fi
sed -E '/^error: found [0-9]+ new style error\(s\)! Try `lake exe lint-style --fix` to apply automatic fixes\.$/d' \
  "$audit_stderr" >&2

# Mathlib deliberately does not report exceptions whose underlying violation disappeared. Run its
# public linter entry point without exceptions and ratchet the trusted baseline by the exact key
# Mathlib uses: path and error kind (including the offending unicode character), but not the
# informational line number.
baseline_re="^TauCeti/[A-Za-z0-9_/'-]+\\.lean : line [0-9]+ : ERR_[A-Z_]+ : .+$"
while IFS= read -r line; do
  if [[ -n $line && $line != --* && ! $line =~ $baseline_re ]]; then
    printf 'lint-style: malformed baseline entry: %s\n' "$line" >&2
    status=1
  fi
done < scripts/nolints-style.txt
sed -E '/^--/d; /^[[:space:]]*$/d; s/ : line [0-9]+ : / : /' \
  scripts/nolints-style.txt | sort -u > "$lint_src/baseline.keys"
sed -E '/^--/d; /^[[:space:]]*$/d; s/ : line [0-9]+ : / : /' \
  "$actual_errors" | sort -u > "$lint_src/actual.keys"
stale_entries="$(comm -23 "$lint_src/baseline.keys" "$lint_src/actual.keys")"
if [[ -n $stale_entries ]]; then
  echo 'lint-style: stale entries in scripts/nolints-style.txt; remove or update:' >&2
  printf '%s\n' "$stale_entries" >&2
  status=1
fi
echo "lint-style: all $(wc -l < "$lint_src/baseline.keys") text-style baseline entry/entries are still needed."

# TauCetiLint.All supplies every TauCeti/ import plus TauCeti itself, so the intentionally empty
# root also receives text checks. The TauCeti argument makes lint-style's package-root filter retain
# those imports, while contributing none of its own. The copyright audit is separate because the
# pinned Mathlib header linter is a command linter that skips modules absent from the empty root.
if ! LEAN_SRC_PATH="$lint_src${LEAN_SRC_PATH:+:$LEAN_SRC_PATH}" \
    lake exe lint-style "$@" TauCetiLint.All TauCeti; then
  status=1
fi

exit "$status"
