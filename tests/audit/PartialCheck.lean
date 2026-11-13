import Lean
open Lean

/-!
# Fast-gate check: no unsafe or partial declaration in the library

The audit's rule 1 (`tests/audit/Audit.lean`), alone: every declaration of a `ZlibF` module that the
compiled environment marks unsafe or partial is rejected, except the reviewed compiler auxiliaries
of `tests/audit/compiler-helpers.txt`. A recursive `def` whose compiled code needs an
`_unsafe_rec` helper is caught here, on every push, instead of in the nightly audit; marking the
definition `noncomputable` removes the helper and leaves kernel reduction unchanged.

Run after the library build: `lake env lean --run tests/audit/PartialCheck.lean`.
-/

def readNames (path : System.FilePath) : IO NameSet := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return lines.foldl (init := {}) fun s line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then s else s.insert line.toName

def main : IO UInt32 := do
  let helpers ← readNames "tests/audit/compiler-helpers.txt"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ZlibF }] {} 0
  let mut problems : Array String := #[]
  for (n, ci) in env.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i]!).getRoot == `ZlibF
      | none => false
    unless ours do continue
    if helpers.contains n then continue
    if ci.isUnsafe then problems := problems.push s!"unsafe declaration {n}"
    if ci.isPartial then problems := problems.push s!"partial declaration {n}"
  for p in problems.qsort (· < ·) do IO.println s!"PROBLEM: {p}"
  if problems.isEmpty then
    IO.println "no unsafe or partial declaration outside the reviewed compiler auxiliaries"
    return 0
  IO.println "mark the recursive definition noncomputable (or review it into tests/audit/compiler-helpers.txt)"
  return 1
