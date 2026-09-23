#!/usr/bin/env bash
set -euo pipefail

if ! command -v rg >/dev/null 2>&1; then
  echo 'source hygiene prerequisite missing: rg' >&2
  exit 2
fi

require_no_matches() {
  local status
  if rg "$@"; then
    echo 'unexpected legacy proof surface found' >&2
    exit 1
  else
    status=$?
    if [[ "$status" -ne 1 ]]; then
      echo "source hygiene ripgrep failed (status $status)" >&2
      exit "$status"
    fi
  fi
}

require_no_matches -n --glob '*.lean' \
  '^[[:space:]]*(@\[spec\]|mvcgen\b|mspec\b)|^import Std\.Tactic\.Do$' FloatSpec/src
# Ratchet: only these not-yet-migrated modules may still state `Id` Hoare
# triples or import/open `Std.Do`. Shrink this list as modules migrate; never
# grow it.
legacy_std_do=(
  Calc/Sqrt.lean
  Core/Zaux.lean
  Pff/Pff.lean
  SimprocWP.lean
)
legacy_globs=()
for path in "${legacy_std_do[@]}"; do
  legacy_globs+=(--glob "!FloatSpec/src/$path")
done
require_no_matches -n --glob '*.lean' "${legacy_globs[@]}" \
  '[⦃⦄]|^(import|open) Std\.Do\b' FloatSpec/src

test ! -e FloatSpec/Linter/HoareStyleLinter.lean
echo 'Unused mvcgen surface is absent; migrated modules stay free of Hoare triples and Std.Do.'
