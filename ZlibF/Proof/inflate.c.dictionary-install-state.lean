import ZlibF.Proof.«inflate.c.default-public-memory-contract»
import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«inflate.c.prime-default-state»
import ZlibF.Proof.«inflate.c.default-public-memory-witness»
import ZlibF.Proof.«inflate.c.public-setdict-success»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual final dictionary flag store retains all initialized decoder
clauses. Installed table contents are transported on the actual heap. -/
theorem DefaultStateJ.set_havedict {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    DefaultStateJ (setI h zs { s with havedict := 1 }) r zs z { s with havedict := 1 } := by
  let state := { s with havedict := 1 }
  have good : Good (setI h zs state) r zs z state :=
    good_state invariant.good rfl invariant.good.live.mode
      (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
  have views : ∀ ref : CodeRef, (Space.get (setI h zs state) ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    cases ref with
    | istate_codes i =>
      by_cases same : i = zs
      · subst i
        simp only [Space.get, setI_istates_same, invariant.good.live.hs, Option.map_some, state]
      · simp only [Space.get, setI_istates_ne h zs i state same]
    | st_lenfix | st_distfix => rfl
  have tables : DataTableInvariant (setI h zs state) state := by
    intro active
    have old := invariant.tables active
    constructor
    · obtain ⟨ref, offset, codes, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, codes, pointer, (views ref).trans get, safe⟩
    · obtain ⟨ref, offset, codes, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, codes, pointer, (views ref).trans get, safe⟩
  have pending : DataPendingInvariant state :=
    ⟨invariant.pending.sane, invariant.pending.lenext, invariant.pending.dist,
      invariant.pending.distext, invariant.pending.matching⟩
  exact ⟨⟨good, tables, pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header,
    invariant.modes, invariant.trailer, invariant.globals, invariant.platform.with_istates _⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

#print axioms DefaultStateJ.set_havedict
end Zlib.Inflate.Proofs
