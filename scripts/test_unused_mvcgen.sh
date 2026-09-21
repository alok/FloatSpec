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
require_no_matches -n '[⦃⦄]' FloatSpec/src/Core/FIX.lean

test ! -e FloatSpec/Linter/HoareStyleLinter.lean
echo 'Unused mvcgen surface is absent; FIX stays direct.'
