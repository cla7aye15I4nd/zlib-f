import ZlibF.Proof.«inflate.c.header-actual-tables-classifier»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem missing_eob_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (E : Env c h r zs z s) (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (zero : (s.lens.getD 256 0).toNat = 0) :
    ∃ i, runX (clTail c) l h = .ok ((.ok (), l), tcBadHeap h r zs z s i) := by
  have cellZero : s.lens.getD 256 0 = (0 : UInt16) := UInt16.toNat_inj.mp zero
  have inside : 0 + 256 < s.lens.size := by omega
  have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens E.hs) inside
  have read' : Ptr.index (lensP c.st) 256 h = .ok ((0 : UInt16), h) := by
    rw [E.st]
    change OkOn h ((Ptr.ref (WRef.istate_lens zs) 0).index 256) (0 : UInt16)
    have value : s.lens[0 + 256] = 0 := by simpa [Array.getD, inside] using cellZero
    simpa [value] using read
  have modeRead : rdS c.st (·.mode) h = .ok (CODELENS, h) := by rw [E.st, rdI_eq, E.hs]; simp only [mode]
  obtain ⟨i, _literal, bad⟩ := tcBadMode_run (c := c) "invalid code -- missing end-of-block" lit_missing_eob E.strm E.st E.hz E.hs
  refine ⟨i, ?_⟩
  have distinct : CODELENS ≠ BAD := by decide
  simp [clTail, runX_bind, runX_lift_ok modeRead, distinct, runX_lift_ok read', runX_lift_ok bad, runX_pure]

structure TailRejected (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (l : IL) where
  state : InflateState
  message : Nat
  ret : Int32
  frame : state = {s with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode}
  reason : (state = s ∧ (s.lens.getD 256 0).toNat = 0) ∨ RejectedConstructorTrace h zs s state
  actual : runX (clTail c) l h = .ok ((.ok (), {l with ret := ret}), tcBadHeap h r zs z state message)

structure TailReady (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (l : IL) (bs : List UInt8) where
  tables : TablesReady c h zs s l
  origin : DefaultOriginState (setI h zs tables.state) r zs z tables.state
  buffers : DispatchBuffers (setI h zs tables.state) r {l with ret := 0} bs
  eob : HasEndOfBlock ((actualLengthPrefix s).take s.nlen.toNat)
  actual : runX (clTail c) l h = if c.flush = Z_TREES then .ok ((.error Ex.leave, {l with ret := 0}), setI h zs tables.state)
    else runX (inflate_LEN_ c) {l with ret := 0} (setI h zs tables.state)

/-- Actual EOB testing and both actual default constructors reject or
establish a fully represented stable LEN_ packet. No Header, CodeLens,
acceptable alphabet, return value or desired post-state is assumed. -/
theorem clTail_branch_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = CODELENS) (literalCount : 256 < s.nlen.toNat)
    (complete : s.«have».toNat = s.nlen.toNat + s.ndist.toNat) :
    Nonempty (TailRejected c h r zs z s l) ∨ Nonempty (TailReady c h r zs z s l bs) := by
  by_cases zero : (s.lens.getD 256 0).toNat = 0
  · obtain ⟨i, actual⟩ := missing_eob_source E origin.good.inv.wf.1 mode zero
    have self : {l with ret := l.ret} = l := by cases l; rfl
    exact Or.inl ⟨⟨s, i, l.ret, rfl, Or.inl ⟨rfl, zero⟩, by simpa only [self] using actual⟩⟩
  have cut := PayloadTables.clTail_eob_source_cut (l := l) E.st E.hs origin.good.inv.wf.1 mode zero
  obtain ⟨_pointer, _safe, nlen, ndist, _have, initialized⟩ := origin.lengths mode
  have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by rw [← complete]; exact initialized
  rcases clTables_branch_classifier E origin.good.inv.wf nlen ndist lengths with rejected | ready
  · obtain ⟨bad⟩ := rejected
    exact Or.inl ⟨⟨bad.state, bad.message, -1, bad.frame, Or.inr bad.calls, cut.trans bad.actual⟩⟩
  · obtain ⟨tables⟩ := ready
    have pointers : PtrInv zs tables.state := ⟨⟨tables.offset + tables.used, tables.nextPtr, by have := tables.roomL; have := tables.roomD; omega⟩,
      Or.inl ⟨0, tables.offset, tables.lenPtr, tables.distPtr, by decide, by have := tables.roomL; omega⟩⟩
    have safe : DataTablesSafe (setI h zs tables.state) tables.state := by
      have get : Space.get (setI h zs tables.state) (CodeRef.istate_codes zs) = some tables.state.codes := CodeRef.get_istate_codes (setI_istates_same ..)
      exact ⟨⟨.istate_codes zs, 0, tables.state.codes, tables.lenPtr, get, tables.safeL⟩,
        ⟨.istate_codes zs, tables.offset, tables.state.codes, tables.distPtr, get, tables.safeD⟩⟩
    obtain ⟨nextOrigin, packet, _sizes⟩ := PayloadPhaseView.constructor_metadata_packet origin buffers tables.frame tables.wf.2.1 tables.wf.2.2 pointers tables.mode safe tables.lenPtr
      (origin.construction_format (Or.inr (Or.inr mode)))
    have eob : HasEndOfBlock ((actualLengthPrefix s).take s.nlen.toNat) := by
      rw [(PayloadTables.actualLengthPrefix_payload_slices s complete).1]
      unfold HasEndOfBlock
      rw [Zlib.Inftrees.Proofs.lensOf_getD _ literalCount]
      exact zero
    exact Or.inr ⟨⟨tables, nextOrigin, packet, eob, cut.trans tables.actual⟩⟩

#print axioms missing_eob_source
#print axioms clTail_branch_classifier
end Zlib.Inflate.Proofs.ActualHeader
