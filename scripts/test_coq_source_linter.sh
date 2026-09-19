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

rg -q 'missingCoqLinkProbe is unclassified' "$scratch/diagnostics.txt"

printf '%s\n' \
  'import FloatSpec.Linter.CoqSourceLinter' \
  'set_option linter.coqSource true' \
  'set_option warningAsError true' \
  'noncomputable def missingNoncomputableCoqLinkProbe : Nat := 1' \
  >"$scratch/MissingNoncomputableCoqLink.lean"

if [[ -n "${LEAN_TOOLCHAIN_OVERRIDE:-}" ]]; then
  if elan run "$LEAN_TOOLCHAIN_OVERRIDE" lake env lean "$scratch/MissingNoncomputableCoqLink.lean" \
      >"$scratch/error-diagnostics.txt" 2>&1; then
    echo 'An unclassified public definition unexpectedly passed the strict gate' >&2
    exit 1
  fi
else
  if lake env lean "$scratch/MissingNoncomputableCoqLink.lean" \
      >"$scratch/error-diagnostics.txt" 2>&1; then
    echo 'An unclassified public definition unexpectedly passed the strict gate' >&2
    exit 1
  fi
fi
rg -q 'missingNoncomputableCoqLinkProbe is unclassified' "$scratch/error-diagnostics.txt"

printf '%s\n' \
  'import FloatSpec.Linter.CoqSourceLinter' \
  'set_option linter.coqSource true' \
  '@[flocq_local "A Lean-only test helper"]' \
  'def localCoqLinkProbe : Nat := 1' \
  >"$scratch/LocalCoqLink.lean"

if [[ -n "${LEAN_TOOLCHAIN_OVERRIDE:-}" ]]; then
  elan run "$LEAN_TOOLCHAIN_OVERRIDE" lake env lean "$scratch/LocalCoqLink.lean" \
    >"$scratch/local-diagnostics.txt" 2>&1
else
  lake env lean "$scratch/LocalCoqLink.lean" >"$scratch/local-diagnostics.txt" 2>&1
fi

if rg -q 'localCoqLinkProbe is unclassified' "$scratch/local-diagnostics.txt"; then
  echo 'Explicit local-helper classification was not recognized' >&2
  exit 1
fi
printf '%s\n' 'Coq source-link linter regression passed'
