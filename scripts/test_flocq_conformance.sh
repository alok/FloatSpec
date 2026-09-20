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

# A matching HEAD alone does not make a modified reference pinned. Generated
# build files are fine; changed tracked sources and untracked .v files are not.
git -C "$flocq_dir" diff --exit-code HEAD -- src
if git -C "$flocq_dir" ls-files --others --exclude-standard src | rg -q '\.v$'; then
  echo 'Reference checkout contains untracked Rocq source files' >&2
  exit 1
fi

uv run "$repo_root/scripts/validate_flocq_source_refs.py" "$flocq_dir"
uv run "$repo_root/scripts/test_flocq_source_refs.py" -v
uv run "$repo_root/scripts/check_compiled_trust.py"
uv run "$repo_root/scripts/test_compiled_trust.py" -v

if [[ "${FLOCQ_SKIP_BUILD:-0}" != "1" ]]; then
  (
    cd "$flocq_dir"
    autoreconf -i
    ./configure
    ./remake --jobs="${FLOCQ_JOBS:-4}"
  )
fi

cat >"$scratch/FloatSpecConformance.v" <<'COQ'
From Stdlib Require Import ZArith.
From Flocq Require Import Core.Zaux Core.Defs Core.FIX Calc.Bracket Calc.Operations Calc.Plus Calc.Round Calc.Div Calc.Sqrt IEEE754.Binary Pff.Pff2FlocqAux.

Open Scope Z_scope.

Example even_middle_exact_location :
    Bracket.new_location_even 4 2 SpecFloat.loc_Exact =
    SpecFloat.loc_Inexact Eq.
Proof. vm_compute. reflexivity. Qed.

Example odd_middle_inexact_location :
    Bracket.new_location_odd 3 1 (SpecFloat.loc_Inexact Gt) =
    SpecFloat.loc_Inexact Gt.
Proof. vm_compute. reflexivity. Qed.

Example fplus_core_negative_scale :
    (let beta := Build_radix 2 eq_refl in
      Fplus_core beta 1 0 0 1 1) =
    (0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fplus_core_positive_control :
    (let beta := Build_radix 2 eq_refl in
      Fplus_core beta 1 0 0 1 0) =
    (1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example falign_reverse_exponent :
    (let beta := Build_radix 2 eq_refl in
      Operations.Falign (Float beta 1 0) (Float beta 1 (-1))) =
    (2, 1, -1).
Proof. vm_compute. reflexivity. Qed.

Example fplus_close_magnitudes :
    (let beta := Build_radix 2 eq_refl in
      Plus.Fplus beta (FIX_exp 0) (Float beta 1 0) (Float beta 1 1)) =
    (3, 0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fdiv_core_exact_quotient :
    (let beta := Build_radix 2 eq_refl in
      Div.Fdiv_core beta 4 0 2 0 0) =
    (2, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fdiv_core_halfway_location :
    (let beta := Build_radix 2 eq_refl in
      Div.Fdiv_core beta 1 0 2 0 0) =
    (0, SpecFloat.loc_Inexact Eq).
Proof. vm_compute. reflexivity. Qed.

Example fdiv_exact_quotient :
    (let beta := Build_radix 2 eq_refl in
      Div.Fdiv (FIX_exp 0) (Float beta 4 0) (Float beta 2 0)) =
    (2, 0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fsqrt_core_exact_square :
    (let beta := Build_radix 2 eq_refl in
      Sqrt.Fsqrt_core beta 4 0 0) =
    (2, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example fsqrt_core_inexact_location :
    (let beta := Build_radix 2 eq_refl in
      Sqrt.Fsqrt_core beta 2 0 0) =
    (1, SpecFloat.loc_Inexact Lt).
Proof. vm_compute. reflexivity. Qed.

Example fsqrt_exact_square :
    (let beta := Build_radix 2 eq_refl in
      Sqrt.Fsqrt (FIX_exp 0) (Float beta 4 0)) =
    (2, 0, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example truncate_aux_negative_scale :
    (let beta := Build_radix 2 eq_refl in
      truncate_aux beta (2, 0, SpecFloat.loc_Exact) (-1)) =
    (0, -1, SpecFloat.loc_Inexact Gt).
Proof. vm_compute. reflexivity. Qed.

Example truncate_aux_positive_control :
    (let beta := Build_radix 2 eq_refl in
      truncate_aux beta (2, 0, SpecFloat.loc_Exact) 1) =
    (1, 1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example truncate_source_exponent :
    (let beta := Build_radix 2 eq_refl in
      truncate beta (FIX_exp 1) (4, 0, SpecFloat.loc_Exact)) =
    (2, 1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example round_sign_up_negative :
    Round.round_sign_UP true (SpecFloat.loc_Inexact Gt) = false.
Proof. vm_compute. reflexivity. Qed.

Example round_nearest_tie_choice :
    Round.round_N true (SpecFloat.loc_Inexact Eq) = true.
Proof. vm_compute. reflexivity. Qed.

Example truncate_fix_positive_shift :
    (let beta := Build_radix 2 eq_refl in
      Round.truncate_FIX beta 1 (4, 0, SpecFloat.loc_Exact)) =
    (2, 1, SpecFloat.loc_Exact).
Proof. vm_compute. reflexivity. Qed.

Example nan_payload_bitlength_boundary :
    Zlt_bool (Zpos (SpecFloat.digits2_pos 4)) 3 = false.
Proof. vm_compute. reflexivity. Qed.

Example nan_payload_bitlength_valid :
    Zlt_bool (Zpos (SpecFloat.digits2_pos 3)) 3 = true.
Proof. vm_compute. reflexivity. Qed.

Example make_bound_Emin_zero_precision :
    (let beta := Build_radix 2 eq_refl in
      Z.of_N (Pff.dExp (make_bound beta 0 (-1)))) = 1.
Proof. vm_compute. reflexivity. Qed.
COQ

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
"$coqc_bin" -q -R "$flocq_dir/src" Flocq "$scratch/FloatSpecConformance.v"
"$coqc_bin" -q -R "$flocq_dir/src" Flocq -o "$scratch/ArithmeticProperties.vo" \
  "$repo_root/scripts/fixtures/ArithmeticProperties.v"
echo 'Pure Rocq loop passed: examples and 10,734 independent arithmetic invariant cases'
"$coqc_bin" -q -R "$flocq_dir/src" Flocq -o "$scratch/BitsProperties.vo" \
  "$repo_root/scripts/fixtures/BitsProperties.v"
echo 'Pure Rocq bit loop passed: 20,000 binary32/binary64 roundtrip checks'
"$coqc_bin" -q -R "$flocq_dir/src" Flocq -o "$scratch/BitOrderProperties.vo" \
  "$repo_root/scripts/fixtures/BitOrderProperties.v"
echo 'Pure Rocq order loop passed: 2,000 ordering-law checks and boundary examples'
"$coqc_bin" -q -R "$flocq_dir/src" Flocq -o "$scratch/RoundingWalkthrough.vo" \
  "$repo_root/scripts/fixtures/RoundingWalkthrough.v"
for fixture in BooleanComparison PrimitiveComparison PrimitiveConversion PrimitiveExecution RawIEEERounding RawOverflow SingleNaNArithmetic SingleNaNHelpers FrexpLaws Normalization MultiplicationErrorGrid DoubleRoundingWitness SingleNaNValidity RelativeErrorGrid \
    SourcePremiseContracts PffLogTotality PffExecution CalcBrackets ExactArithmeticLaws RoundingOracle IntegerRounding; do
  "$coqc_bin" -q -R "$flocq_dir/src" Flocq -o "$scratch/$fixture.vo" \
    "$repo_root/scripts/fixtures/$fixture.v"
done
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
for fixture in BooleanComparison PrimitiveComparison PrimitiveConversion PrimitiveExecution RawIEEERounding RawOverflow SingleNaNArithmetic SingleNaNHelpers FrexpLaws Normalization CalcBrackets NativeSingleNaNArithmetic MultiplicationErrorGrid DoubleRoundingWitness SingleNaNValidity RelativeErrorGrid ExactArithmeticLaws RoundingOracle IntegerRounding; do
  run_lake env lean "$repo_root/scripts/fixtures/$fixture.lean"
done
run_lake env lean --run "$repo_root/scripts/fixtures/GuidedDemo.lean"
run_lake env lean --run "$repo_root/scripts/fixtures/PffWalkthrough.lean"
echo 'Pure Lean loop passed: examples and 10,734 kernel-checked arithmetic invariant cases'
run_lake exe floatspec_demo
echo 'Lean bit/order loops passed: 20,000 roundtrips, 2,000 pure laws, 200,000 native comparisons'
echo 'Boolean ordering passed: eight boundary assertions and 600,000 native Boolean comparisons'
echo 'Native source-arithmetic loop passed: 100,100 binary32/binary64 comparisons'
echo 'Native SingleNaN arithmetic loop passed: 200,200 direct/source-mode comparisons'
echo 'Multiplication-error loop passed: 5,385 conditional cases and a required-underflow-premise counterexample'
echo 'Lean contract loop passed: 98 premise guards, typed consumers, finite error laws, 35,845 format-rounding and 5,125 integer-rounding oracle cases'
echo 'Independent Calc loop passed: 8,640 division brackets, 2,496 square-root brackets, and a required-exponent-premise counterexample'

uv run "$repo_root/scripts/flocq_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
  --seed "${FLOCQ_BRIDGE_SEED:-20260919}" --samples "${FLOCQ_BRIDGE_SAMPLES:-100}" \
  --batch-size "${FLOCQ_BRIDGE_BATCH_SIZE:-200}"
# Preserve all counterexamples independently of the new corpus's random seed.
for replay in RawIEEERoundingReplay RawOverflowReplay PrimitiveComparisonReplay PrimitiveConversionReplay; do
  uv run "$repo_root/scripts/flocq_bridge.py" --flocq-dir "$flocq_dir" --coqc "$coqc_bin" \
    --replay "$repo_root/scripts/fixtures/$replay.json" --skip-build
done
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

echo "Three finite-test loops passed against pinned Flocq $gitlink_commit"
