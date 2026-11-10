import ZlibF.Proof.«inflate.c.nonfinal-type-bad-v1»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.BlockSourceGate
set_option autoImplicit false

/-- Every real non-final TYPE/TYPEDO step either observes the documented
TYPE flush pause, waits for three tag bits, installs the source-selected
STORED/fixed/TABLE phase, or rejects the reserved BTYPE3. No kind,
minimum buffer, accepted future, or callee result is a caller premise. -/
theorem EpochCallCut4.nonfinal_tag_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (modes : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last = 0) :
    Nonempty (DispatchResult4 before) := by
  rcases block_dispatch_pause_or_typed before.facts.env modes with pause | typed
  · exact before.type_flush_pause pause.1 pause.2.1
  obtain ⟨outcome, pulled, used, pull, bound, inv, source, _count, shape,
    maximum, _identity, full, _short, kinds, cursor⟩ :=
    NEEDBITS_run_cursor before.facts.buffers.bits 3 (by decide)
  have small : pulled.bits.toNat ≤ 39 := by
    have initial := before.facts.bits
    change pulled.bits.toNat ≤ max l.bits.toNat 10 at maximum
    omega
  rcases kinds with normal | wait
  · have enough : 3 ≤ pulled.bits.toNat := full normal
    let kind := (pulled.hold.toNat / 2) % 4
    have range : kind < 4 := Nat.mod_lt _ (by decide)
    have cases : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases cases with zero | one | two | three
    · exact before.nonfinal_tag_stored modes last typed (by rwa [normal] at pull)
        bound inv source shape cursor small enough zero
    · by_cases trees : c.flush = Z_TREES
      · exact before.nonfinal_tag_fixed_trees modes last typed (by rwa [normal] at pull)
          bound inv source shape cursor small enough one trees
      · exact before.nonfinal_tag_fixed modes last typed (by rwa [normal] at pull)
          bound inv source shape cursor small enough one trees
    · exact before.nonfinal_tag_table modes last typed (by rwa [normal] at pull)
        bound inv source shape cursor small enough two
    · exact before.nonfinal_tag_bad modes last typed (by rwa [normal] at pull)
        bound inv source shape cursor small enough three
  · exact before.nonfinal_tag_wait modes last typed (by rwa [wait] at pull)
      bound inv source shape cursor small

#print axioms EpochCallCut4.nonfinal_tag_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
