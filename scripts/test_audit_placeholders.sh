#!/usr/bin/env bash
set -euo pipefail

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

printf '%s\n' \
  'namespace AuditProbe' \
  'protected axiom assumedFalse : False' \
  'theorem derivedFalse : False := AuditProbe.assumedFalse' \
  'end AuditProbe' \
  >"$tmp_dir/ProtectedAxiom.lean"

output="$tmp_dir/findings.json"
if scripts/audit_placeholders.sh --json --fail-on-findings "$tmp_dir" >"$output"; then
  echo "expected protected axiom fixture to fail the trust scan" >&2
  exit 1
fi

rg -q '"kind": "axiom"' "$output"
rg -q 'protected axiom assumedFalse' "$output"

printf '%s\n' 'example : (1 : Nat) = 1 := by native_decide' >"$tmp_dir/NativeDecide.lean"
if scripts/audit_placeholders.sh --json --fail-on-findings "$tmp_dir/NativeDecide.lean" >"$output"; then
  echo "expected native_decide fixture to fail the trust scan" >&2
  exit 1
fi

rg -q '"kind": "native_decide"' "$output"
printf '%s\n' 'protected-axiom and native_decide scanner regressions passed'

repo_root="$(git rev-parse --show-toplevel)"
for name in AttributedAxioms Extern; do
  fixture="$repo_root/scripts/fixtures/audit/$name.lean"
  # Compile the fixture: a regex hit in invalid Lean is not a useful regression.
  lake env lean "$fixture"
  if scripts/audit_placeholders.sh --json --fail-on-findings "$fixture" >"$output"; then
    echo "expected $name fixture to fail the trust scan" >&2
    exit 1
  fi
  if [[ "$name" == AttributedAxioms ]]; then
    rg -q '"axiom": 2' "$output"
  else
    rg -q '"extern": 1' "$output"
    rg -q '"opaque": 1' "$output"
  fi
done

# Exercise the platform awk parser even when the current diff has no Lean lines.
scripts/audit_placeholders.sh --diff --json FloatSpec >"$output"
printf '%s\n' 'public/attributed axiom, extern, and macOS diff-mode regressions passed'
