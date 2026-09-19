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
