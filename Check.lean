import Lean
import ZlibF

/-! Axiom gate. Every theorem listed at the end may depend only on `propext`,
`Classical.choice` and `Quot.sound`. A theorem that uses `sorry`, `axiom` or
`native_decide` (which adds `Lean.ofReduceBool`) fails here. List a theorem only
when its proof is complete. -/
open Lean Elab Command

elab "#assert_axioms " ids:ident* : command => do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    let bad := axs.toList.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "{n} depends on disallowed axioms {bad}"
    logInfo m!"{n}: ok ({axs.size} axioms, all allowed)"

-- Completed theorems are listed here, one per line:
#assert_axioms
