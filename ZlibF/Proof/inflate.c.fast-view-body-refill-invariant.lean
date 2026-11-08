import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-four-byte-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The fast body's initial two pulls turn six caller bytes into four unread
bytes while establishing the sixteen held bits needed by `dolen`. -/
theorem FastInputPacket.fast_body_refill_default_state
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15) :
    ∃ fastNext slowNext,
      C.run (do
        let one ← Zlib.Inffast.pull l
        Zlib.Inffast.pull one) h = .ok (fastNext, h) ∧
      FastInputPacket h slowNext
        (third :: fourth :: fifth :: sixth :: rest) fastNext ∧
      DefaultStateJ h r zs z s ∧
      DispatchBuffers h r slowNext
        (third :: fourth :: fifth :: sixth :: rest) ∧
      16 ≤ slowNext.bits.toNat ∧
      slowNext.bits.toNat ≤ 30 ∧
      stream slowNext (third :: fourth :: fifth :: sixth :: rest) =
        stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: rest) := by
  obtain ⟨next1, fast1, slow1, run1, _, slow1Eq,
    _, packet1, _, buffers1, stream1⟩ :=
    packet.pull_default_state invariant buffers (by omega)
  have small1 : slow1.bits.toNat ≤ 22 := by
    rw [slow1Eq]
    change (slow.bits + 8).toNat ≤ 22
    rw [u32_add8 slow.bits (by omega)]
    omega
  obtain ⟨next2, fast2, slow2, run2, _, slow2Eq,
    _, packet2, state2, buffers2, stream2⟩ :=
    packet1.pull_default_state invariant buffers1 small1
  have firstBits : slow1.bits.toNat = slow.bits.toNat + 8 := by
    rw [slow1Eq]
    exact u32_add8 slow.bits (by omega)
  have secondBits : slow2.bits.toNat = slow1.bits.toNat + 8 := by
    rw [slow2Eq]
    exact u32_add8 slow1.bits (by omega)
  have run : C.run (do
      let one ← Zlib.Inffast.pull l
      Zlib.Inffast.pull one) h = .ok (fast2, h) := by
    change (Zlib.Inffast.pull l >>= Zlib.Inffast.pull) h =
      .ok (fast2, h)
    change Zlib.Inffast.pull l h = .ok (fast1, h) at run1
    change Zlib.Inffast.pull fast1 h = .ok (fast2, h) at run2
    rw [bind_app, run1]
    exact run2
  exact ⟨fast2, slow2, run, packet2, state2, buffers2,
    by omega, by omega, stream2.trans stream1⟩

/-- The fast body's translated root lookup selects a bounded entry without
changing the synchronized caller byte view. -/
theorem FastInputPacket.fast_body_root_lookup
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1) :
    let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
    let selected : Zlib.Inffast.L :=
      { l with here := .ref codeRef (baseOff + rootSlice) }
    rootSlice < 2 ^ rootWidth ∧
      C.run (Ptr.add c.lcode rootSlice) h =
        .ok (.ref codeRef (baseOff + rootSlice), h) ∧
      FastInputPacket h slow bs selected := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  have sliceEq : rootSlice = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have sliceBound : rootSlice < 2 ^ rootWidth := by
    rw [sliceEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.lcode rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) := by
    rw [lcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  exact ⟨sliceBound, addRun,
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩⟩

end Zlib.Inflate.Proofs
