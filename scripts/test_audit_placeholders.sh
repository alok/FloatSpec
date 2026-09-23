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
# Diff mode reports added Lean and Rocq lines at their new line numbers, with
# repository-relative paths whatever the user's diff prefixes or colors.
diff_repo="$tmp_dir/diff_repo"
mkdir "$diff_repo"
printf '%s\n' 'def kept : Nat := 0' >"$diff_repo/Probe.lean"
printf '%s\n' 'Definition kept := 0.' >"$diff_repo/Probe.v"
git -C "$diff_repo" init -q
git -C "$diff_repo" add -A
git -C "$diff_repo" -c user.name=audit -c user.email=audit@example.invalid \
  -c commit.gpgsign=false commit -qm base
printf '%s\n' 'example : False := sorry' '-- a comment naming sorry' >>"$diff_repo/Probe.lean"
printf '%s\n' 'Axiom added : False.' >>"$diff_repo/Probe.v"
(cd "$diff_repo" && GIT_CONFIG_COUNT=2 GIT_CONFIG_KEY_0=diff.mnemonicPrefix GIT_CONFIG_VALUE_0=true \
  GIT_CONFIG_KEY_1=color.diff GIT_CONFIG_VALUE_1=always \
  "$repo_root/scripts/audit_placeholders.sh" --diff --json .) >"$output"
python3 - "$output" <<'PY'
import json
import sys

found = [(f["kind"], f["path"], f["line"]) for f in json.load(open(sys.argv[1]))["findings"]]
expected = [("sorry", "Probe.lean", 2), ("rocq_axiom", "Probe.v", 2)]
if found != expected:
    sys.exit(f"diff mode reported {found}, expected {expected}")
PY
printf '%s\n' 'public/attributed axiom, extern, and diff-mode regressions passed'

# Escape hatches that an `example` or a standalone fixture can hide. Examples
# never enter the environment that check_compiled_trust.py walks, fixtures run
# outside Lake, and several of these also survive warningAsError, so the text
# scan is the gate. Columns: every kind the snippet must produce
# (comma-separated), then the snippet (printf %b escapes). Snippets whose
# payload a comment-stripping lexer could lose (raw strings, «escaped»
# identifiers, interpolated strings, a string spanning a deleted line) end
# with `-- -/`, a Lean comment that also closes any block comment a mistaken
# lexer opened, so the next snippet is scanned from a clean state.
lean_hazards="$tmp_dir/lean_hazards.tsv"
cat >"$lean_hazards" <<'HAZARDS'
axiom	axiom assumedFalse : False
axiom	example : True := trivial axiom oneLine : False
axiom	open Nat in axiom openIn : False
axiom	open Lean in\n#eval show CoreM Unit from addDecl (.axiomDecl { name := `metaAxiom, levelParams := [], type := mkConst ``False, isUnsafe := false })
native_decide	example : (1 : Nat) = 1 := by native_decide
native_decide	-- A comment may not name native_decide either.
native_config	example : 2 + 2 = 4 := by decide +native
native_config	example : 2 + 2 = 4 := by decide +«native»
native_config	example : 2 + 2 = 4 := by decide (native := (true))
native_config	example : 2 + 2 = 4 := by decide (native :=\n  true)
native_config	example : 2 + 2 = 4 := by decide (config := { native := !false })
config_term	example : 2 + 2 = 4 := by decide (config := ⟨false, true, true, false⟩)
native_config	def nativeConfig : Lean.Parser.Tactic.DecideConfig := ⟨false, true, true, false⟩
native_config	open Lean Elab Tactic in\nelab "native_by_elaborator" : tactic => do evalNativeDecide (← getRef)
bv_decide	example (x : BitVec 4) : x &&& x = x := by bv_decide
compiler_trust	example := @Lean.ofReduceBool
compiler_trust	example := @Lean.«ofReduceBool»
compiler_trust	example : True := Lean.trustCompiler
sorry_ax	example : False := sorryAx False false
sorry_meta	open Lean Elab Tactic in\nelab "trust_me" : tactic => do admitGoal (← getMainGoal)\nexample : False := by trust_me
sorry_option	set_option debug.byAsSorry true in\nexample : 1 = 2 := by simp
sorry_option	set_option debug.«byAsSorry» true in\nexample : 1 = 2 := by simp
sorry_option	set_option debug.proofAsSorry true in\ntheorem proofSkipped : 1 = 2 := by simp
sorry_option	set_option debug.terminalTacticsAsSorry true in\nexample : 1 = 2 := by omega
kernel_bypass	set_option debug.skipKernelTC true in\ntheorem kernelSkipped : 2 + 2 = 4 := rfl
kernel_bypass	set_option debug.«skipKernelTC» true in\ntheorem kernelSkippedEscaped : 2 + 2 = 4 := rfl
kernel_bypass	open Lean in\nexample := @Kernel.Environment.addDeclWithoutChecking
kernel_bypass	open Lean in\nexample := @Environment.addDeclCore
kernel_bypass	def checkFlag (doCheck : Bool := true) : Bool := doCheck
warning_as_error	set_option warningAsError false in\nexample : True := trivial
sorry_tactic,warning_as_error	set_option warningAsError\n  false in\nexample : False := by all_goals stop trivial
guard_msgs	#guard_msgs (drop warning) in\nexample : True := trivial
guard_msgs	#guard_msgs (drop all) in\nexample : True := trivial
guard_msgs,sorry_tactic	#guard_msgs (drop\n  warning) in\nexample : False := by first | stop trivial
guard_msgs,sorry_tactic	/-- warning: declaration uses `sorry` -/\n#guard_msgs in\nexample : False := by all_goals stop trivial
guard_msgs	/-- error: Unknown identifier `bogus` -/\n#guard_msgs in\ntheorem swallowed : False := bogus\ntheorem usesSwallowed : False := swallowed
guard_msgs	/-- info: "sorry" -/\n#guard_msgs in\n#eval "sor" ++ "ry"
guard_msgs,sorry_ax,warning_as_error	set_option warningAsError false in\n#guard_msgs (drop warning) in\nexample : False := sorryAx False false
sorry_tactic	example : False := by stop simp
sorry_tactic	example : False := by try stop trivial
sorry_tactic	example : False := by { stop trivial }
sorry_tactic	example : False := by\n  case _ => stop trivial
sorry_tactic	example : False := by\n  next => stop trivial
sorry_tactic	example : True := by apply?
sorry_tactic	example : False := by impossible by exact id
sorry_tactic	example : ∀ n : Nat, n < 1000000 := by plausible
admit	example : False := by admit
sorry	set_option warn.sorry false in\nexample : False := sorry
sorry	def rawS : String := r#"x"--"# example : False := sorry
admit	def rawT : String := r#"x"/-"#\nexample : False := by admit\n-- -/
sorry	def windowsDir : String := r"C:\\"\ndef opener : String := "/-"\nexample : False := sorry\n-- -/
sorry	def «/-» : Nat := 0\nexample : False := sorry\ndef «-/» : Nat := 0
sorry	def «x--» : Nat := 0 example : False := sorry
sorry	def pick (n : Nat) (_ : Char) : Nat := n\ndef primed (h' : Nat) : Nat := pick h' '"'\ndef dashes : String := "--" example : False := sorry
sorry,true_relation	def gapS : String := "\n-- fun _ _ => True\n/-"\nexample : False := sorry\n-- -/
sorry	def interp : String := s!"{"--"}" example : False := sorry
sorry	open Lean Meta in\ndef traced : MetaM Unit := do trace[Meta.debug] "{"--"}" example : False := sorry
admit	def interpB : String := s!"{"/-"}"\nexample : False := by admit\n-- -/
lexer_syntax	infixl:65 " <-- " => Nat.add\ntheorem tokenHidden : 1 <-- 1 = 2 := sorry
lexer_syntax	notation "⟪/-" => (0 : Nat)\nexample : ⟪/- = 0 := sorry\n-- -/
lexer_syntax	syntax "⟪" interpolatedStr(term) : term
exit_command	#exit
HAZARDS

rocq_hazards="$tmp_dir/rocq_hazards.tsv"
cat >"$rocq_hazards" <<'HAZARDS'
rocq_admitted	Lemma admitted : False.\nProof.\nAdmitted.
rocq_admitted	From Stdlib Require Import Program.\nProgram Definition obligation : 1 = 2 := _.\nAdmit\n  Obligations.
rocq_admit,rocq_admitted	Lemma admitted_tactic : False.\nProof. admit.\nAdmitted.
rocq_admitted	(* A comment may not name Admitted either. *)
rocq_axiom	Axiom assumed : False.
rocq_axiom	#[local] Parameter parameter : nat.
rocq_axiom	Conjecture conjectured : False.
rocq_axiom	From Stdlib Require Import Structures.Equalities.\nDeclare\n  Module Assumed : Typ.
rocq_axiom	Class Bogus := { bogus_false : False }.\nDeclare Instance bogus_instance : Bogus.
rocq_hypothesis	Set Warnings "-declaration-outside-section".\nVariable top_level : nat.
rocq_hypothesis	Section Closed.\nVariable section_local : nat.\nEnd Closed.\nSet Warnings "-all".\nHypothesis after_end : False.
rocq_hypothesis	Module Outer.\n#[warnings="-context-outside-section"]\nContext (in_module : False).\nEnd Outer.
rocq_native_compute	Eval native_compute in 1 + 1.
rocq_kernel_bypass	Unset Guard\n  Checking.\nFixpoint loop (n : nat) : nat := loop n.
rocq_kernel_bypass	#[bypass_check(guard)] Fixpoint bypassed (n : nat) : nat := bypassed n.
rocq_axiom	From Stdlib Require Import String.\nOpen Scope string_scope.\nDefinition opener := "(*".\nAxiom after_string : False.
rocq_axiom	From Stdlib Require Import String.\nOpen Scope string_scope.\nDefinition doubled := """(*".\nAxiom after_doubled_quote : False.
lexer_syntax	Notation "x <(* y" := (x + y) (at level 50).\nCheck (1 <(* 2).
HAZARDS

# Each probe file must produce exactly its listed kinds, in JSON (Python
# regexes) and in text mode (ripgrep regexes), so the engines cannot drift.
probes="$tmp_dir/probes"
mkdir "$probes"
expected="$tmp_dir/expected_kinds.txt"
: >"$expected"
add_probe() {  # add_probe KINDS FILE: FILE (already written) must yield KINDS
  for kind in ${1//,/ }; do printf '%s %s\n' "$kind" "$2" >>"$expected"; done
}
expected_lines="$tmp_dir/expected_lines.txt"
: >"$expected_lines"
add_probe_lines() {  # add_probe_lines FILE KIND:LINE...: exactly these findings
  local file="$1" item
  shift
  for item in "$@"; do
    add_probe "${item%%:*}" "$file"
    printf '%s %s:%s\n' "${item%%:*}" "$file" "${item#*:}" >>"$expected_lines"
  done
}

# Comments and docstrings may describe hazards other than the unambiguous
# trust-escape names; ordinary code may use `stop`, `native` and `impossible`
# as names, and `{`, `--` or `/-` inside strings.
cat >"$probes/CommentControl.lean" <<'LEAN'
/-- Docs may name `sorry`, `admit`, `stop`, `apply?`, `plausible`, `impossible by`,
`(config := cfg)` and `notation "a--b"` without being hazards. -/
def documented : Nat := 0 -- an `axiom` or `sorry` in a line comment
/- nested /- `admit` -/ still a comment: `stop simp` -/
/-
-- let r := round (fun _ _ => True) x
We admit this step and leave a TODO stub for the sorry case.
-/
LEAN
cat >"$probes/CodeControl.lean" <<'LEAN'
def span (start stop : Nat) : Nat := stop - start
def width : Nat := span (start := 1) (stop := 4)
def shift (native : Nat) : Nat := 1 + native
def pairSum (native : Nat × Nat) : Nat := native.1 + native.2
theorem named (impossible : 1 = 2) : False := absurd impossible (by decide)
def brace : String := "{" -- a comment naming sorry and admit
def cliFlag : String := "--seed" -- flags begin with dashes
def url (ref : String) : String := s!"https://example.org/-/blob/{ref}#L1"
def quote : Char := '"' -- a character literal is not a string: sorry
def h' : Nat := 0 -- a prime continues an identifier: sorry
LEAN
cat >"$probes/SectionControl.v" <<'ROCQ'
(* admit. Axiom a : False. (* nested Parameter p : nat. *) *)
(* A string in a comment: "*) Axiom hidden : False." is still commented. *)
Section Local.
Variable x : nat.
Hypothesis h : x = x.
Context {y : nat}.
End Local.
Module Outer.
Section Inner.
Variables a b : nat.
End Inner.
End Outer.
Module Alias := Outer.
ROCQ
# A string mentioning a Section opens none, and every setting that lets a
# top-level Hypothesis compile is flagged along with the Hypothesis itself.
cat >"$probes/SectionString.v" <<'ROCQ'
From Stdlib Require Import String.
Open Scope string_scope.
Definition label := "Section Fake".
Set Warnings "-vernacular".
Hypothesis after_string : False.
ROCQ
add_probe_lines "$probes/SectionString.v" rocq_hypothesis:4 rocq_hypothesis:5

# Each Lean hazard is valid Lean accepted by the plain fixture runner, so a
# regex hit here is a real escape rather than a malformed probe.
compiled_hazards="$tmp_dir/LeanHazards.lean"
printf '%s\n' 'import Lean' 'import Std.Tactic.BVDecide' 'import Plausible' >"$compiled_hazards"
cat "$probes/CommentControl.lean" "$probes/CodeControl.lean" >>"$compiled_hazards"
index=0
while IFS=$'\t' read -r kinds snippet; do
  index=$((index + 1))
  printf '%b\n' "$snippet" >"$probes/Hazard$index.lean"
  printf '%b\n' "$snippet" >>"$compiled_hazards"
  add_probe "$kinds" "$probes/Hazard$index.lean"
done <"$lean_hazards"
if ! lake env lean "$compiled_hazards" >"$tmp_dir/hazards.log" 2>&1; then
  cat "$tmp_dir/hazards.log" >&2
  echo "Lean hazard probes must compile under plain lake env lean" >&2
  exit 1
fi
rocq_first=$((index + 1))
while IFS=$'\t' read -r kinds snippet; do
  index=$((index + 1))
  printf '%b\n' "$snippet" >"$probes/Hazard$index.v"
  add_probe "$kinds" "$probes/Hazard$index.v"
done <"$rocq_hazards"

# Each Rocq hazard (and the control) must compile too, preferably with the
# pinned Rocq: the repository's _opam switch locally, the opam switch in CI.
coqc=()
if [[ -x "$repo_root/_opam/bin/coqc" ]]; then
  coqc=("$repo_root/_opam/bin/coqc")
elif command -v opam >/dev/null 2>&1 && opam switch list --short 2>/dev/null | rg -qx 'floatspec-rocq'; then
  coqc=(opam exec --switch=floatspec-rocq -- coqc)
elif command -v coqc >/dev/null 2>&1; then
  coqc=(coqc)
fi
if [[ ${#coqc[@]} -gt 0 ]]; then
  for probe in "$probes/SectionControl.v" "$probes/SectionString.v" $(seq -f "$probes/Hazard%g.v" "$rocq_first" "$index"); do
    if ! (cd "$tmp_dir" && "${coqc[@]}" -q "$probe") >"$tmp_dir/rocq.log" 2>&1; then
      cat "$tmp_dir/rocq.log" >&2
      echo "Rocq probe must compile: $probe" >&2
      exit 1
    fi
  done
  printf '%s\n' "Rocq probes compiled with $("${coqc[@]}" --version | head -n 1)"
elif [[ -n "${CI:-}" ]]; then
  echo "CI must compile the Rocq probes, but no coqc was found" >&2
  exit 1
else
  echo "NOT RUN: Rocq probe compilation (no coqc on PATH, in _opam/, or opam switch floatspec-rocq)" >&2
fi

# Lexer and traversal controls: a `--` inside a string after a character
# literal for a double quote, a file after an unterminated comment, a NUL byte
# (ripgrep would otherwise skip the file as binary), and symlinked, hidden and
# ignored files that Lake would still compile (ignore rules prune directories
# even for explicitly globbed files).
printf '%s\n' "def quote : Char := '\"'" \
  'def dashes : String := "--" example : False := sorry' \
  >"$probes/StringControl.lean"
add_probe sorry "$probes/StringControl.lean"
printf '%s\n' '/- unterminated' >"$probes/Order0.lean"
printf '%s\n' 'example : False := sorry' >"$probes/Order1.lean"
add_probe sorry "$probes/Order1.lean"
printf -- '-- header\0\nexample : False := sorry\n' >"$probes/Nul.lean"
add_probe sorry "$probes/Nul.lean"
mkdir -p "$tmp_dir/outside/linked" "$probes/.hidden"
printf '%s\n' 'example : False := sorry' >"$tmp_dir/outside/Linked.lean"
cp "$tmp_dir/outside/Linked.lean" "$tmp_dir/outside/linked/Deep.lean"
ln -s "$tmp_dir/outside/Linked.lean" "$probes/Linked.lean"
ln -s "$tmp_dir/outside/linked" "$probes/linked"
add_probe sorry "$probes/Linked.lean"
add_probe sorry "$probes/linked/Deep.lean"
printf '%s\n' 'example : False := sorry' >"$probes/.hidden/Hidden.lean"
add_probe sorry "$probes/.hidden/Hidden.lean"
mkdir "$probes/ignored"
printf '%s\n' 'ignored/' >"$probes/.ignore"
printf '%s\n' 'example : False := sorry' >"$probes/ignored/Ignored.lean"
add_probe sorry "$probes/ignored/Ignored.lean"
sort -u "$expected" -o "$expected"
sort -u "$expected_lines" -o "$expected_lines"

if scripts/audit_placeholders.sh --json --fail-on-findings "$probes" >"$output"; then
  echo "expected the escape-hatch probes to fail the JSON scan" >&2
  exit 1
fi
python3 -c 'import json, sys
for f in json.load(sys.stdin)["findings"]:
    print(f["kind"], "%s:%s" % (f["path"], f["line"]))' <"$output" >"$tmp_dir/json_lines.txt"
if scripts/audit_placeholders.sh --fail-on-findings "$probes" >"$output"; then
  echo "expected the escape-hatch probes to fail the text scan" >&2
  exit 1
fi
awk '
  /^[a-z_]+: [0-9]+$/ { kind = $1; sub(/:$/, "", kind); next }
  /^  / && match($0, /:[0-9]+:/) { print kind, substr($0, 3, RSTART + RLENGTH - 4) }
' "$output" >"$tmp_dir/text_lines.txt"
for mode in json text; do
  sed -E 's/:[0-9]+$//' "$tmp_dir/${mode}_lines.txt" | sort -u >"$tmp_dir/${mode}_kinds.txt"
  # Findings in the line-exact probes, restricted to those probes' files.
  awk 'NR == FNR { sub(/:[0-9]+$/, "", $2); files[$2] = 1; next }
       { file = $2; sub(/:[0-9]+$/, "", file) } file in files' \
    "$expected_lines" "$tmp_dir/${mode}_lines.txt" | sort -u >"$tmp_dir/${mode}_exact.txt"
  if ! diff -u "$expected" "$tmp_dir/${mode}_kinds.txt" ||
      ! diff -u "$expected_lines" "$tmp_dir/${mode}_exact.txt"; then
    echo "$mode scan did not report exactly the expected probe kinds" >&2
    exit 1
  fi
done
printf '%s\n' "$index escape-hatch probes and lexer/traversal controls matched in JSON and text modes"

# A source line that ripgrep does not report is a scanner failure, not a pass.
stub="$tmp_dir/stub"
mkdir "$stub"
cat >"$stub/rg" <<'STUB'
#!/bin/sh
if [ "$2" = "-H" ]; then
  "$REAL_RG" "$@" | "$REAL_RG" --text -v '/Order1\.lean:'
  exit 0
fi
exec "$REAL_RG" "$@"
STUB
chmod +x "$stub/rg"
if REAL_RG="$(command -v rg)" PATH="$stub:$PATH" \
    scripts/audit_placeholders.sh --json "$probes" >"$output" 2>"$tmp_dir/stub.err"; then
  echo "expected a scan that loses a file to fail" >&2
  exit 1
fi
rg -q 'did not read every source line' "$tmp_dir/stub.err"
printf '%s\n' 'a scan that loses source lines fails closed'

# End to end: check_proof_debts.py passes on a copy of the current tree and
# rejects every hazard injected into the copy's tests and standalone fixtures,
# fixture reuse of an approved debt, a second warningAsError exemption for an
# approved debt, a lakefile that no longer enables warningAsError, and drift in
# the scanner's own negative controls.
tree="$tmp_dir/tree"
mkdir -p "$tree/scripts" "$tree/FloatSpec/docs"
scan_paths=()
while IFS= read -r path; do scan_paths+=("$path"); done < <(python3 -B -c '
import sys
sys.path.insert(0, "scripts")
import check_proof_debts
print("\n".join(check_proof_debts.scan_paths(check_proof_debts.ROOT)))')
rg --files --hidden --no-ignore -g '*.lean' -g '*.v' "${scan_paths[@]}" | tar -cf - -T - | tar -xf - -C "$tree"
cp FloatSpec/docs/proof_debts.json "$tree/FloatSpec/docs/"
cp scripts/audit_placeholders.sh scripts/check_proof_debts.py "$tree/scripts/"
if ! python3 "$tree/scripts/check_proof_debts.py" >"$output" 2>&1; then
  cat "$output" >&2
  echo "positive control: the copied tree must pass check_proof_debts.py" >&2
  exit 1
fi
# The real manifest may be empty, so the copy gets one synthetic approved debt:
# a named sorry in its manifest theorem, scoped by exactly one
# `warningAsError false in`.  The copy must still pass with it; the hazards
# below then reuse its id and duplicate its exemption.
approved_debt=FloatSpec/Test/AuditApprovedDebt.lean
printf '%s\n' 'set_option warningAsError false in' 'theorem auditApprovedDebt : False := by' \
  '  sorry -- FLOCQ-DEBT: audit_approved_debt' >"$tree/$approved_debt"
python3 -B -c '
import json, sys
manifest = sys.argv[1]
with open(manifest, encoding="utf-8") as handle:
    debts = json.load(handle)
debts.append({"id": "audit_approved_debt", "path": sys.argv[2], "theorem": "auditApprovedDebt"})
with open(manifest, "w", encoding="utf-8") as handle:
    json.dump(debts, handle)
' "$tree/FloatSpec/docs/proof_debts.json" "$approved_debt"
if ! python3 "$tree/scripts/check_proof_debts.py" >"$output" 2>&1; then
  cat "$output" >&2
  echo "positive control: an approved debt and its one exemption must pass check_proof_debts.py" >&2
  exit 1
fi

debt_error() {
  case "$1" in
    sorry) printf 'unnamed sorry: %s\n' "$2" ;;
    warning_as_error) printf 'unapproved warningAsError: %s\n' "$2" ;;
    guard_msgs) printf 'unapproved #guard_msgs: %s\n' "$2" ;;
    *) printf 'unexpected %s: %s\n' "$1" "$2" ;;
  esac
}

expected="$tmp_dir/expected_errors.txt"
: >"$expected"
for target in FloatSpec/Test/FlocqConformance.lean scripts/fixtures/RoundingOracle.lean; do
  [[ -f "$tree/$target" ]] || { echo "missing injection target $target" >&2; exit 1; }
  while IFS=$'\t' read -r kinds snippet; do
    printf '%b\n' "$snippet" >>"$tree/$target"
    for kind in ${kinds//,/ }; do debt_error "$kind" "$target" >>"$expected"; done
  done <"$lean_hazards"
done
target=scripts/fixtures/RoundingOracle.v
[[ -f "$tree/$target" ]] || { echo "missing injection target $target" >&2; exit 1; }
while IFS=$'\t' read -r kinds snippet; do
  printf '%b\n' "$snippet" >>"$tree/$target"
  for kind in ${kinds//,/ }; do debt_error "$kind" "$target" >>"$expected"; done
done <"$rocq_hazards"
# Each #guard_msgs rule, in a file of its own: a declaration may not be
# guarded, nor an expected message mention sorry; an approved use passes.
# shellcheck disable=SC2016 # the backquotes are Lean's, not a command substitution
printf '%s\n' '/-- error: Unknown identifier `bogus` -/' '#guard_msgs in' \
  'theorem swallowed : False := bogus' >"$tree/FloatSpec/Test/AuditGuardDeclaration.lean"
debt_error guard_msgs FloatSpec/Test/AuditGuardDeclaration.lean >>"$expected"
printf '%s\n' '/-- info: "sorry" -/' '#guard_msgs in' '#eval "sor" ++ "ry"' \
  >"$tree/FloatSpec/Test/AuditGuardSorry.lean"
debt_error guard_msgs FloatSpec/Test/AuditGuardSorry.lean >>"$expected"
printf '%s\n' '/-- info: 2 -/' '#guard_msgs in' '#eval 1 + 1' >"$tree/FloatSpec/Test/AuditGuardApproved.lean"
printf '%s\n' 'theorem fixtureDebt : False := by' '  sorry -- FLOCQ-DEBT: audit_approved_debt' \
  >>"$tree/scripts/fixtures/RoundingOracle.lean"
echo 'unapproved or duplicate debt audit_approved_debt: scripts/fixtures/RoundingOracle.lean' >>"$expected"
awk '{ print } /^set_option warningAsError false in$/ && !done { print; done = 1 }' \
  "$tree/$approved_debt" >"$tmp_dir/AuditApprovedDebt.lean"
mv "$tmp_dir/AuditApprovedDebt.lean" "$tree/$approved_debt"
debt_error warning_as_error "$approved_debt" >>"$expected"
awk '{ sub(/⟨`warningAsError, true⟩/, "⟨`warningAsError, false⟩"); print }' \
  "$tree/lakefile.lean" >"$tmp_dir/lakefile.lean"
mv "$tmp_dir/lakefile.lean" "$tree/lakefile.lean"
debt_error warning_as_error lakefile.lean >>"$expected"
echo 'lakefile.lean enables warningAsError 0 times, expected 1' >>"$expected"
printf '%s\n' 'public axiom thirdAssumption : False' >>"$tree/scripts/fixtures/audit/AttributedAxioms.lean"
echo 'expected reference scripts/fixtures/audit/AttributedAxioms.lean has 3 axiom findings, expected 2' \
  >>"$expected"
printf '%s\n' 'example : False := sorryAx False false' >>"$tree/scripts/fixtures/audit/Extern.lean"
debt_error sorry_ax scripts/fixtures/audit/Extern.lean >>"$expected"

if python3 "$tree/scripts/check_proof_debts.py" >"$output" 2>&1; then
  echo "expected injected hazards to fail check_proof_debts.py" >&2
  exit 1
fi
sed -E 's/:[0-9]+$//' "$output" | sort -u >"$tmp_dir/actual_errors.txt"
sort -u "$expected" -o "$expected"
if ! diff -u "$expected" "$tmp_dir/actual_errors.txt"; then
  echo "check_proof_debts.py did not reject exactly the injected hazards" >&2
  exit 1
fi
printf '%s\n' "check_proof_debts.py passes the copied tree and rejects $(wc -l <"$expected" | tr -d ' ') injected hazard classes"
