import ZlibF.Proof.«inflate.c.fast-arbitrary-length-extra»
import ZlibF.Proof.«inflate.c.fast-distance-arbitrary-source-v1»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inffast.Proofs
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Real distance refill and root pointer arithmetic, preserving arbitrary
remaining source and all pending scalar fields. The capacity is derived
from six actual bytes minus the already consumed length code/extras. -/
theorem distance_refill_current_prefix
    {h : Heap} {slow : IL} {bs : List UInt8} {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {ref : CodeRef} {codes : Array Code} {offset root : Nat}
    (packet : FastInputPacket h slow bs l) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs) (bits : slow.bits.toNat ≤ 30)
    (capacity : 28 ≤ (stream slow bs).length)
    (pointer : c.dcode = .ref ref offset) (get : Space.get h ref = some codes)
    (safe : DistTableSafe codes offset root) (mask : c.dmask.toUInt64.toNat = 2 ^ root - 1) :
    ∃ used next selected,
      used ≤ 2 ∧ used ≤ bs.length ∧
      selected.in_ = inputAdvance l.in_ used ∧
      C.run (dolenRefill c l) h =
        C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) selected) h ∧
      FastInputPacket h next (bs.drop used) selected ∧ DispatchBuffers h r next (bs.drop used) ∧
      selected.here = .ref ref (offset + selected.hold.toNat % 2 ^ root) ∧
      stream next (bs.drop used) = stream slow bs ∧ 15 ≤ next.bits.toNat ∧ next.bits.toNat ≤ 30 ∧
      selected.len = l.len ∧ selected.out = l.out ∧ selected.againL = l.againL ∧ selected.broke = l.broke ∧
      next.put = slow.put ∧ next.left = slow.left := by
  have rootPrefix (next : IL) (localRegs : Zlib.Inffast.L) (unread : List UInt8)
      (view : FastInputPacket h next unread localRegs) :
      let selected := {localRegs with here := .ref ref (offset + localRegs.hold.toNat % 2 ^ root)}
      C.run (dolenDist c localRegs) h =
        C.run (cdoWhile (Zlib.Inffast.dodist c) (fun q => pure (q.againD, q)) selected) h ∧
      FastInputPacket h next unread selected := by
    dsimp only
    have rootBound : offset + localRegs.hold.toNat % 2 ^ root ≤ codes.size := by
      have size := safe.2.1
      have bound := Nat.mod_lt localRegs.hold.toNat (Nat.two_pow_pos root)
      omega
    have addRun : Ptr.add c.dcode (localRegs.hold &&& c.dmask.toUInt64).toNat h =
        .ok (.ref ref (offset + localRegs.hold.toNat % 2 ^ root), h) := by
      rw [pointer, u64_and_mask mask]
      exact Ptr.add_nat_ok get rootBound
    refine ⟨?_, ⟨view.source, view.cursor, view.hold, view.bits⟩⟩
    change (dolenDist c localRegs) h = _
    unfold dolenDist
    rw [bind_ok addRun]
    rfl
  by_cases short : l.bits < 15
  · have less : slow.bits.toNat < 15 := by rw [← packet.bits]; exact UInt32.lt_iff_toNat_lt.mp short
    cases bs with
    | nil => simp only [stream, bytesBits, List.flatMap_nil, List.append_nil, natBits_length] at capacity; omega
    | cons first rest =>
      cases rest with
      | nil => simp only [stream, List.length_append, natBits_length, bytesBits_length, List.length_cons, List.length_nil] at capacity; omega
      | cons second tail =>
        obtain ⟨ptr1, fast1, slow1, run1, _ptr1Eq, slow1Eq, fast1Eq, view1, _current1, buffers1, source1⟩ :=
          packet.pull_default_state invariant buffers (by omega)
        have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by rw [slow1Eq]; exact u32_add8 _ (by omega)
        obtain ⟨ptr2, fast2, slow2, run2, _ptr2Eq, slow2Eq, fast2Eq, view2, _current2, buffers2, source2⟩ :=
          view1.pull_default_state invariant buffers1 (by omega)
        have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by rw [slow2Eq]; exact u32_add8 _ (by omega)
        obtain ⟨rootRun, selectedPacket⟩ := rootPrefix slow2 fast2 tail view2
        refine ⟨2, slow2, _, by omega, by simp, ?_, ?_, selectedPacket, buffers2, rfl,
          source2.trans source1, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · change fast2.in_ = inputAdvance l.in_ 2
          rw [fast2Eq]
          change ptr2 = inputAdvance l.in_ 2
          rw [packet.cursor, _ptr2Eq, slow1Eq]
          change inputAdvance ptr1 1 = inputAdvance slow.next 2
          rw [_ptr1Eq, inputAdvance_add]
        · change (dolenRefill c l) h = _
          unfold dolenRefill
          simp only [short, ite_true]
          rw [bind_ok (show Zlib.Inffast.pull l h = .ok (fast1, h) from run1),
            bind_ok (show Zlib.Inffast.pull fast1 h = .ok (fast2, h) from run2)]
          exact rootRun
        · simp only [fast2Eq, fast1Eq, pullL]
        · simp only [fast2Eq, fast1Eq, pullL]
        · simp only [fast2Eq, fast1Eq, pullL]
        · simp only [fast2Eq, fast1Eq, pullL]
        · rw [slow2Eq, slow1Eq]; rfl
        · rw [slow2Eq, slow1Eq]; rfl
  · have held : 15 ≤ slow.bits.toNat := by
      have noLess : ¬ l.bits.toNat < 15 := fun bad => short (UInt32.lt_iff_toNat_lt.mpr bad)
      rw [packet.bits] at noLess
      omega
    obtain ⟨rootRun, selectedPacket⟩ := rootPrefix slow l bs packet
    exact ⟨0, slow, _, by omega, by omega, (by change l.in_ = inputAdvance l.in_ 0; cases l.in_ <;> simp [inputAdvance]), by simpa only [dolenRefill, short, ite_false] using rootRun,
      selectedPacket, buffers, rfl, rfl, held, bits, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms distance_refill_current_prefix
end Zlib.Inflate.Proofs.FastArbitraryBody
