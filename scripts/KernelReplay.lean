import Lean.Replay

/-!
Replay compiled Lean modules through the kernel.

`lake env lean --run scripts/KernelReplay.lean TARGET...` loads each target (a
module name, or the path of an `.olean` file) on top of its imports and sends
every declaration it adds to the kernel again, as the toolchain's `leanchecker`
does.  Metaprograms and debug options can add a declaration to the environment
without the kernel checking it; neither `#print axioms` nor the compiled trust
audit can see that, but the replay does, whatever spelling was used.  Unlike
`leanchecker`, a module name never selects other modules it is a prefix of, so
a stale build output left behind by a deleted source file is never replayed.

The kernel skips unsafe and partial constants, as `leanchecker` does; a safe
declaration that uses one is rejected, and the compiled trust audit rejects
unsafe project declarations.  Prints `replayed TARGET N` (N declarations sent
to the kernel) for each target and exits 1 if the kernel rejects any.
-/

open Lean

/-- The data files of the module stored at `olean`: exported, server, private. -/
def moduleFiles (olean : System.FilePath) : IO (Array System.FilePath) := do
  unless ← olean.pathExists do
    throw <| IO.userError s!"object file {olean} does not exist"
  let server := OLeanLevel.server.adjustFileName olean
  let priv := OLeanLevel.private.adjustFileName olean
  if !(← server.pathExists) then return #[olean]
  if !(← priv.pathExists) then return #[olean, server]
  return #[olean, server, priv]

/-- Replay the module stored at `olean` into the environment of its imports.
Unsafe only to free the imported regions, which bounds memory and mappings. -/
unsafe def replayModule (olean : System.FilePath) : IO Nat := do
  let parts ← readModuleDataParts (← moduleFiles olean)
  let some (header, _) := parts[0]? | throw <| IO.userError s!"no module data in {olean}"
  -- The last (most private) part holds every constant of the earlier ones.
  let some (data, _) := parts.back? | throw <| IO.userError s!"no module data in {olean}"
  let (_, imported) ← importModulesCore header.imports |>.run
  let env ← finalizeImport imported header.imports {} 0 false false (isModule := true)
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for name in data.constNames, info in data.constants do
    constants := constants.insert name info
  discard <| env.toKernelEnv.replay constants
  env.freeRegions
  return (constants.toList.filter fun (_, info) => !info.isUnsafe && !info.isPartial).length

/-- Replay every target in parallel and report each result in argument order. -/
unsafe def main (targets : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if targets.isEmpty then
    throw <| IO.userError "usage: KernelReplay (MODULE | FILE.olean)..."
  let mut tasks := #[]
  for target in targets do
    let olean ← if target.endsWith ".olean" then pure (System.FilePath.mk target)
      else findOLean target.toName
    tasks := tasks.push (target, ← IO.asTask (replayModule olean))
  let mut failed := false
  for (target, task) in tasks do
    match task.get with
    | .ok count => IO.println s!"replayed {target} {count}"
    | .error error =>
      IO.eprintln s!"kernel replay rejected {target}: {error}"
      failed := true
  return if failed then 1 else 0
