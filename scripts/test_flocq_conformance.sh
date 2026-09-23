#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
flocq_git="$repo_root/Deps/flocq"
gitlink_commit="$(git -C "$repo_root" rev-parse HEAD:Deps/flocq)"
scratch="$(mktemp -d "${TMPDIR:-/tmp}/floatspec-flocq-conformance.XXXXXX")"
managed_worktree=""
managed_parent=""

cleanup() {
  if [[ -n "$managed_parent" && -n "$managed_worktree" ]]; then
    git -C "$managed_parent" worktree remove --force "$managed_worktree" >/dev/null 2>&1 || true
  fi
  rm -rf "$scratch"
}
trap cleanup EXIT

run_lake() {
  if [[ -n "${LEAN_TOOLCHAIN_OVERRIDE:-}" ]]; then
    elan run "$LEAN_TOOLCHAIN_OVERRIDE" lake "$@"
  else
    lake "$@"
  fi
}

if [[ -n "${FLOCQ_AUDIT_DIR:-}" ]]; then
  flocq_dir="$FLOCQ_AUDIT_DIR"
  actual_commit="$(git -C "$flocq_dir" rev-parse HEAD)"
  if [[ "$actual_commit" != "$gitlink_commit" ]]; then
    echo "FLOCQ_AUDIT_DIR is at $actual_commit, expected gitlink $gitlink_commit" >&2
    exit 1
  fi
else
  managed_worktree="$scratch/flocq"
  if git -C "$flocq_git" rev-parse --git-dir >/dev/null 2>&1; then
    if ! git -C "$flocq_git" cat-file -e "$gitlink_commit^{commit}"; then
      git -C "$flocq_git" fetch origin "$gitlink_commit"
    fi
    managed_parent="$flocq_git"
    git -C "$flocq_git" worktree add --detach "$managed_worktree" "$gitlink_commit" >/dev/null
  else
    git clone --filter=blob:none --no-checkout \
      "${FLOCQ_REPOSITORY:-https://gitlab.inria.fr/flocq/flocq.git}" \
      "$managed_worktree"
    git -C "$managed_worktree" fetch origin "$gitlink_commit"
    git -C "$managed_worktree" checkout --detach "$gitlink_commit"
  fi
  flocq_dir="$managed_worktree"
fi

# A matching HEAD alone does not make a modified reference pinned. CI and this
# loop share one policy, verify_reference in scripts/flocq_bridge.py, which
# validate_flocq_source_refs.py applies before anything else.
uv run "$repo_root/scripts/validate_flocq_source_refs.py" "$flocq_dir"
uv run "$repo_root/scripts/test_reference_policy.py" -v
uv run "$repo_root/scripts/test_flocq_source_refs.py" -v
uv run "$repo_root/scripts/test_flocq_port_queue.py" -v
uv run "$repo_root/scripts/test_scan_failures.py" -v
uv run "$repo_root/scripts/check_compiled_trust.py"
uv run "$repo_root/scripts/check_compiled_trust.py" --scope tests
uv run "$repo_root/scripts/flocq_port_queue.py" --check-lean-reviews --skip-build
uv run "$repo_root/scripts/test_compiled_trust.py" -v

if [[ "${FLOCQ_SKIP_BUILD:-0}" != "1" ]]; then
  (
    cd "$flocq_dir"
    autoreconf -i
    ./configure
    ./remake --jobs="${FLOCQ_JOBS:-4}"
  )
fi
# Verify again after building, as CI does, so no regression below runs against
# build products compiled from other sources.
uv run python -c 'import sys; from pathlib import Path; sys.path.insert(0, sys.argv[1]); import flocq_bridge; print("Built reference verified at", flocq_bridge.verify_reference(Path(sys.argv[2]).resolve()))' \
  "$repo_root/scripts" "$flocq_dir"

if [[ -n "${COQC:-}" ]]; then
  coqc_bin="$COQC"
else
  configured_coqc="$(sed -n 's/^S\["COQC"\]="\(.*\)"$/\1/p' "$flocq_dir/config.status" 2>/dev/null | head -n 1)"
  if [[ -n "$configured_coqc" && -x "$configured_coqc" ]]; then
    coqc_bin="$configured_coqc"
  else
    coqc_bin="$(command -v coqc)"
  fi
fi
# Compile every Rocq fixture, discovered by glob as in CI, against the reference.
for path in "$repo_root"/scripts/fixtures/*.v; do
  fixture="$(basename "$path" .v)"
  echo "== $fixture"
  "$coqc_bin" -q -R "$flocq_dir/src" Flocq -o "$scratch/$fixture.vo" "$path"
done
echo 'Pure Rocq loop passed: examples and 10,734 independent arithmetic invariant cases'
echo 'Pure Rocq bit loop passed: 20,000 binary32/binary64 roundtrip checks'
echo 'Pure Rocq order loop passed: 2,000 ordering-law checks and boundary examples'
echo 'Pure Rocq contract loop passed: typed premises, counterexamples, finite error laws, 35,845 rounding-oracle cases'

run_lake build FloatSpec.Test.FlocqConformance FloatSpec.Test.ArithmeticProperties \
  FloatSpec.Test.BitsExecution FloatSpec.Test.BitOrderExecution FloatSpec.Test.NativeSourceArithmetic \
  FloatSpec.Test.RoundingWalkthrough FloatSpec.Test.SourcePremiseContracts
# Re-execute the checks, even when Lake already has their compiled modules.
run_lake env lean "$repo_root/FloatSpec/Test/ArithmeticProperties.lean"
run_lake env lean "$repo_root/FloatSpec/Test/BitsExecution.lean"
run_lake env lean "$repo_root/FloatSpec/Test/BitOrderExecution.lean"
run_lake env lean "$repo_root/FloatSpec/Test/NativeSourceArithmetic.lean"
run_lake env lean "$repo_root/FloatSpec/Test/RoundingWalkthrough.lean"
run_lake env lean "$repo_root/FloatSpec/Test/SourcePremiseContracts.lean"
run_lake env lean "$repo_root/FloatSpec/Test/PffLogTotality.lean"
run_lake env lean "$repo_root/FloatSpec/Test/PffExecution.lean"
run_lake env lean "$repo_root/FloatSpec/Test/PffAuxExecution.lean"
run_lake env lean "$repo_root/FloatSpec/Test/PffRoundingSource.lean"
run_lake env lean "$repo_root/FloatSpec/Test/DoubleRoundingContracts.lean"
run_lake env lean "$repo_root/FloatSpec/Test/NativeModelAdapters.lean"
run_lake env lean "$repo_root/FloatSpec/Test/LpoSourceContracts.lean"
run_lake env lean "$repo_root/FloatSpec/Test/UlpSourceChoice.lean"
# Every Lean fixture, discovered by glob with warnings as errors, as in CI;
# fixtures defining `main` also execute, and every fixture's declarations are
# then replayed through the kernel.
executable_fixtures=' GuidedDemo PffWalkthrough '
fixture_oleans="$(mktemp -d "$scratch/oleans.XXXXXX")"
for path in "$repo_root"/scripts/fixtures/*.lean; do
  fixture="$(basename "$path" .lean)"
  echo "== $fixture"
  if [[ "$executable_fixtures" == *" $fixture "* ]]; then
    run_lake env lean -DwarningAsError=true -o "$fixture_oleans/$fixture.olean" --run "$path"
  else
    run_lake env lean -DwarningAsError=true -o "$fixture_oleans/$fixture.olean" "$path"
  fi
done
run_lake env lean --run "$repo_root/scripts/KernelReplay.lean" "$fixture_oleans"/*.olean
echo 'Pure Lean loop passed: examples and 10,734 kernel-checked arithmetic invariant cases'
run_lake exe floatspec_demo
echo 'Lean bit/order loops passed: 20,000 roundtrips, 2,000 pure laws, 200,000 native comparisons'
echo 'Boolean ordering passed: eight boundary assertions and 600,000 native Boolean comparisons'
echo 'Native source-arithmetic loop passed: 100,100 binary32/binary64 comparisons'
echo 'Native SingleNaN arithmetic loop passed: 200,200 direct/source-mode comparisons'
echo 'Native frExp loop passed: 200,556 Float.frExp/nativeFrExp runtime agreements'
echo 'Multiplication-error loop passed: 5,385 conditional cases and a required-underflow-premise counterexample'
echo 'Lean contract loop passed: 147 premise guards, typed consumers, finite error laws, 35,845 format-rounding and 5,125 integer-rounding oracle cases'
echo 'Independent Calc loop passed: 8,640 division brackets, 2,496 square-root brackets, and a required-exponent-premise counterexample'

uv run "$repo_root/scripts/flocq_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_BRIDGE_SAMPLES:-100}" \
  --batch-size "${FLOCQ_BRIDGE_BATCH_SIZE:-200}"
# Preserve all counterexamples independently of the new corpus's random seed.
for replay in RawIEEERoundingReplay RawOverflowReplay PrimitiveComparisonReplay PrimitiveConversionReplay; do
  uv run "$repo_root/scripts/flocq_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
    --replay "$repo_root/scripts/fixtures/$replay.json" --skip-build
done
uv run "$repo_root/scripts/pff_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --replay "$repo_root/scripts/fixtures/PffSignLawsReplay.json" --skip-build
uv run "$repo_root/scripts/pff_integer_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --replay "$repo_root/scripts/fixtures/PffIntegerReplay.json" --skip-build
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_flocq_bridge.py" -v

uv run "$repo_root/scripts/native_ieee_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_NATIVE_SAMPLES:-200}" \
  --batch-size "${FLOCQ_NATIVE_BATCH_SIZE:-25}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_native_ieee_bridge.py" -v

uv run "$repo_root/scripts/native_arithmetic_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_ARITHMETIC_SAMPLES:-100}" \
  --batch-size "${FLOCQ_ARITHMETIC_BATCH_SIZE:-20}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_native_arithmetic_bridge.py" -v

uv run "$repo_root/scripts/ieee_modes_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_MODES_SAMPLES:-10}" \
  --batch-size "${FLOCQ_MODES_BATCH_SIZE:-5}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_ieee_modes_bridge.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_ieee_exact_oracle.py" -v

uv run "$repo_root/scripts/ieee_scale_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_SCALE_SAMPLES:-20}" \
  --batch-size "${FLOCQ_SCALE_BATCH_SIZE:-40}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_ieee_scale_bridge.py" -v

uv run "$repo_root/scripts/ieee_integer_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_INTEGER_SAMPLES:-20}" \
  --batch-size "${FLOCQ_INTEGER_BATCH_SIZE:-40}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_ieee_integer_bridge.py" -v

uv run "$repo_root/scripts/pff_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_PFF_SAMPLES:-100}" \
  --batch-size "${FLOCQ_PFF_BATCH_SIZE:-50}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_pff_bridge.py" -v

uv run "$repo_root/scripts/pff_aux_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_PFF_AUX_SAMPLES:-100}" \
  --batch-size "${FLOCQ_PFF_AUX_BATCH_SIZE:-50}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_pff_aux_bridge.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_pff_rounding_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_double_rounding_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_lpo_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_ulp_choice_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_ulp_nearest_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_round_ne_point_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_remainder_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_pff_basic_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_flocq_exemplars.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_flocqsmith.py" -v

uv run "$repo_root/scripts/pff_integer_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_PFF_INTEGER_SAMPLES:-100}" \
  --batch-size "${FLOCQ_PFF_INTEGER_BATCH_SIZE:-100}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_pff_integer_bridge.py" -v
uv run "$repo_root/scripts/zaux_prelude_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-864211}" --samples "${FLOCQ_ZAUX_PRELUDE_SAMPLES:-120}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_zaux_prelude_bridge.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_zaux_power_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_zaux_division_contracts.py" -v
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_round_pred_contracts.py" -v

uv run "$repo_root/scripts/remainder_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples 0 \
  --batch-size "${FLOCQ_REMAINDER_BATCH_SIZE:-200}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_remainder_bridge.py" -v

uv run "$repo_root/scripts/model_adapter_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_MODEL_ADAPTER_SAMPLES:-100}" \
  --batch-size "${FLOCQ_MODEL_ADAPTER_BATCH_SIZE:-25}"
FLOCQ_AUDIT_DIR="$flocq_dir" uv run "$repo_root/scripts/test_model_adapter_bridge.py" -v

echo "Three finite-test loops passed against pinned Flocq $gitlink_commit"
