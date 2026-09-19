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

python3 "$repo_root/scripts/validate_flocq_source_refs.py" "$flocq_dir" \
  --lean-dir "$repo_root/FloatSpec/src"

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
From Flocq Require Import Core.Zaux Core.Defs Core.FIX Calc.Operations Calc.Plus Calc.Round Calc.Div IEEE754.Binary Pff.Pff2FlocqAux.

Open Scope Z_scope.

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

if [[ -n "${LEAN_TOOLCHAIN_OVERRIDE:-}" ]]; then
  elan run "$LEAN_TOOLCHAIN_OVERRIDE" lake build FloatSpec.Test.FlocqConformance
else
  lake build FloatSpec.Test.FlocqConformance
fi

echo "Flocq and Lean conformance regressions passed at $gitlink_commit"
