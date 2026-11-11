import ZlibF.Proof.«inflate.c.fast-view-dolen-invalid-invariant»
import ZlibF.Proof.«inflate.c.construction-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The translated fast block-end write changes only the inflate mode.
The caller's bit and buffer views stay valid at the TYPE boundary. -/
theorem FastInputPacket.fast_end_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode) :
    let state := { s with mode := TYPE }
    let after := setI h zs state
    C.run (do
      let current ← ldInflateState c.state
      stInflateState c.state { current with mode := TYPE }) h =
        .ok ((), after) ∧
      FastInputPacket after slow bs l ∧
      DefaultStateJ after r zs z state ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after := by
  let state := { s with mode := TYPE }
  let after := setI h zs state
  have stateLoad : ldInflateState c.state h = .ok (s, h) := by
    rw [statePtr]
    exact ldInflateState_ok invariant.good.live.hs
  have stateStore : stInflateState c.state state h =
      .ok ((), after) := by
    rw [statePtr]
    have store := stInflateState_ok
      (r := InflateStateRef.tab zs) invariant.good.live.hs rfl
      (v' := state)
    rw [InflateStateRef.put_tab invariant.good.live.hs state] at store
    exact store
  have run : C.run (do
      let current ← ldInflateState c.state
      stInflateState c.state { current with mode := TYPE }) h =
        .ok ((), after) := by
    change (do
      let current ← ldInflateState c.state
      stInflateState c.state { current with mode := TYPE }) h =
        .ok ((), after)
    rw [bind_ok stateLoad]
    exact stateStore
  have good : Good after r zs z state :=
    invariant.good.decode_update (by rfl)
      (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
  have tables : DataTableInvariant after state := by
    intro active
    have impossible : DataTableMode TYPE := by
      simpa only [state] using active
    exact False.elim ((by unfold DataTableMode; decide :
      ¬ DataTableMode TYPE) impossible)
  have pending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (s := state) invariant.pending.sane
    change TYPE ≠ LENEXT ∧ TYPE ≠ DIST ∧
      TYPE ≠ DISTEXT ∧ TYPE ≠ MATCH
    decide
  have sizes : ByteViewSizes h after := byte_view_sizes_setI h zs state
  have decode : DefaultDecodeJ after r zs z state :=
    invariant.toDefaultDecodeJ.decode_update good tables pending
      (by rfl) (Or.inr (Or.inl rfl)) sizes rfl
  have final : DefaultStateJ after r zs z state :=
    invariant.config_update decode (by exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
      (invariant.data_format mode)
  have views : ∀ ref : BRef,
      (Space.get after ref : Option (Array UInt8)) =
        Space.get h ref := by
    intro ref
    exact byte_view_get_setI h zs state ref
  have readonly : ∀ ref : BRef,
      Space.ro after ref = Space.ro h ref := by
    intro ref
    exact byte_view_ro_setI h zs state ref
  have nextPacket : FastInputPacket after slow bs l :=
    ⟨packet.source.byte_views views, packet.cursor,
      packet.hold, packet.bits⟩
  have nextBuffers : DispatchBuffers after r slow bs :=
    buffers.byte_views invariant.good good rfl views readonly
  exact ⟨run, nextPacket, final, nextBuffers, sizes⟩

/-- The actual `dolen` block-end branch consumes the code and enters TYPE
while retaining the default state and caller byte views. -/
theorem FastInputPacket.dolen_end_leaf_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true) :
    ∃ result slowNext,
      C.run (Zlib.Inffast.dolen c l) h =
        .ok (result, setI h zs { s with mode := TYPE }) ∧
      result.broke = true ∧ result.againL = false ∧
      result.in_ = l.in_ ∧ result.out = l.out ∧
      FastInputPacket (setI h zs { s with mode := TYPE })
        slowNext bs result ∧
      DefaultStateJ (setI h zs { s with mode := TYPE })
        r zs z { s with mode := TYPE } ∧
      DispatchBuffers (setI h zs { s with mode := TYPE })
        r slowNext bs ∧
      ByteViewSizes h (setI h zs { s with mode := TYPE }) ∧
      stream slowNext bs = (stream slow bs).drop
        codes[index].bits.toNat := by
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow bs firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
      using codeBits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
        using codeWidth
    omega
  have dropped := firstPacket.drop_bits_default_state
    buffers count countFits countSmall
  let slowNext : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowNext bs afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  let selected : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 }
  have selectedPacket : FastInputPacket h slowNext bs selected :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  obtain ⟨endRun, endPacket, endInvariant, endBuffers,
    sizes⟩ := selectedPacket.fast_end_default_state
      invariant codeBuffers statePtr mode
  let result : Zlib.Inffast.L := { selected with broke := true }
  have resultPacket : FastInputPacket
      (setI h zs { s with mode := TYPE }) slowNext bs result :=
    ⟨endPacket.source, endPacket.cursor,
      endPacket.hold, endPacket.bits⟩
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzeroEntry : entry.op.toUInt32 ≠ 0 := by
      intro zero
      have zero8 : entry.op = 0 := by
        apply UInt8.toNat_inj.mp
        simpa only [UInt8.toNat_toUInt32, UInt32.toNat_zero,
          UInt8.toNat_zero]
          using congrArg UInt32.toNat zero
      exact nonzero (by simpa only [entry] using zero8)
    simp [nonzeroEntry]
  have notBaseEntry : (entry.op.toUInt32 &&& 16 != 0) = false := by
    simpa only [entry] using notBase
  have notLinkEntry : (entry.op.toUInt32 &&& 64 == 0) = false := by
    simpa only [entry] using notLink
  have endEntry : (entry.op.toUInt32 &&& 32 != 0) = true := by
    simpa only [entry] using endCode
  have stateLoad : ldInflateState c.state h = .ok (s, h) := by
    rw [statePtr]
    exact ldInflateState_ok invariant.good.live.hs
  have stateStore : stInflateState c.state { s with mode := TYPE } h =
      .ok ((), setI h zs { s with mode := TYPE }) := by
    rw [statePtr]
    have store := stInflateState_ok
      (r := InflateStateRef.tab zs) invariant.good.live.hs rfl
      (v' := { s with mode := TYPE })
    rw [InflateStateRef.put_tab invariant.good.live.hs
      { s with mode := TYPE }] at store
    exact store
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, setI h zs { s with mode := TYPE }) := by
    change (Zlib.Inffast.dolen c l) h = _
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, notBaseEntry, notLinkEntry,
      endEntry, Bool.false_eq_true, ite_false, ite_true]
    rw [bind_ok stateLoad]
    rw [bind_ok stateStore]
    rfl
  refine ⟨result, slowNext, run, rfl, rfl, rfl, rfl,
    resultPacket, endInvariant, endBuffers, sizes, ?_⟩
  simpa only [count, Zlib.Inffast.Proofs.toNat32]
    using dropped.2.2.1

end Zlib.Inflate.Proofs
