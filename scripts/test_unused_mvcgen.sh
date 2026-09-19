#!/usr/bin/env bash
set -euo pipefail

if rg -n --glob '*.lean' \
    '^[[:space:]]*(@\[spec\]|mvcgen\b|mspec\b)|^import Std\.Tactic\.Do$' FloatSpec/src; then
  echo 'unused mvcgen lookup or tactic surface reintroduced' >&2
  exit 1
fi

if rg -n '[⦃⦄]' FloatSpec/src/Core/FIX.lean; then
  echo 'FIX source-facing theorems must remain direct propositions' >&2
  exit 1
fi

test ! -e FloatSpec/Linter/HoareStyleLinter.lean
echo 'Unused mvcgen surface is absent; FIX stays direct.'
