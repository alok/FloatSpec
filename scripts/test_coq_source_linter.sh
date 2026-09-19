#!/usr/bin/env bash
set -euo pipefail

scratch="$(mktemp -d "${TMPDIR:-/tmp}/floatspec-coq-linter.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT

printf '%s\n' \
  'import FloatSpec.Linter.CoqSourceLinter' \
  'set_option warningAsError false' \
  'set_option linter.coqSource true' \
  'def missingCoqLinkProbe : Nat := 1' \
  >"$scratch/MissingCoqLink.lean"

if [[ -n "${LEAN_TOOLCHAIN_OVERRIDE:-}" ]]; then
  elan run "$LEAN_TOOLCHAIN_OVERRIDE" lake env lean "$scratch/MissingCoqLink.lean" \
    >"$scratch/diagnostics.txt" 2>&1
else
  lake env lean "$scratch/MissingCoqLink.lean" >"$scratch/diagnostics.txt" 2>&1
fi

rg -q 'missingCoqLinkProbe has no pinned Flocq link' "$scratch/diagnostics.txt"
printf '%s\n' 'Coq source-link linter regression passed'
