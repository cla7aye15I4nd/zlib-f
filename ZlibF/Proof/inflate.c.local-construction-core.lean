import ZlibF.Proof.«inflate.c.local-default-state»
import ZlibF.Proof.«inflate.c.local-head»
import ZlibF.Proof.«inflate.c.construction-default-state»

/-! Actual dynamic construction on locally unique private records.
The execution and Huffman-table results come from the existing lower-level
execution theorems, which do not require global heap uniqueness. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual reading loop preserves the local representation and the
CODELENS boundary relation, including BAD and input-exhaustion exits. The
stream's control fields and all storage outside its two records retain
the exact update relation from clRead_run_full. -/
theorem clRead_run_good {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : LocalGood h cutoff r zs z s) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs) :
    ∃ outcome regs after state stream,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ CodeLengthInvariant zs state ∧
      DataTableInvariant after state ∧ ClReadResult zs s l bs outcome regs after := by
  obtain ⟨outcome, regs, after, run, result, stream, streamGet, streamFrame, heapState, heapEq⟩ :=
    clRead_run_full hr hc good.live.hz good.live.hs good.inv.wf.1 mode stateInv B
  have retained := result
  obtain ⟨state, used, stateGet, _, _, _, _, stateFrame, size, count, prefixValues, modes, _⟩ := result
  have same : heapState = state := by
    rw [heapEq] at stateGet
    simp only [setI_istates_same] at stateGet
    exact Option.some.inj stateGet
  subst heapState
  have inv : StInv h zs state := by
    constructor
    · refine ⟨size, ?_, ?_⟩
      · rw [stateFrame]; exact good.inv.wf.2.1
      · rw [stateFrame]; exact good.inv.wf.2.2
    · rw [stateFrame]
      exact ⟨good.inv.win.wbits, good.inv.win.block, good.inv.win.nullws,
        good.inv.win.ws, good.inv.win.hv, good.inv.win.wn, good.inv.win.eq⟩
    · rw [stateFrame]; exact good.inv.reqbits
    · rw [stateFrame]; exact good.inv.bits
    · rw [stateFrame]; exact good.inv.ptr
  have bounded : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with codes | bad
    · rw [codes]; decide
    · rw [bad]; decide
  have sameState : stream.state = z.state := by rw [streamFrame]
  have alloc : stream.zalloc ≠ .null := by rw [streamFrame]; exact good.live.zalloc
  have free : stream.zfree ≠ .null := by rw [streamFrame]; exact good.live.zfree
  have back : state.strm = s.strm := by rw [stateFrame]
  have finalGood := good.setZI sameState alloc free back bounded inv
  rw [← heapEq] at finalGood
  refine ⟨outcome, regs, after, state, stream, run, finalGood, ?_, ?_, retained⟩
  · intro _
    obtain ⟨pointer, table, nlen, ndist, _, _⟩ := stateInv mode
    refine ⟨?_, ?_, ?_, ?_, ?_, prefixValues⟩
    · rw [stateFrame]; exact pointer
    · rw [stateFrame]; exact table
    · rw [stateFrame]; exact nlen
    · rw [stateFrame]; exact ndist
    · rw [stateFrame]; exact count
  · intro active
    rcases modes with codes | bad
    · rw [codes] at active
      simp only [DataTableMode] at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> cases eq
    · rw [bad] at active
      simp only [DataTableMode] at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> cases eq

private theorem good_table_fields {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {before after : InflateState} (good : LocalGood h cutoff r zs z before)
    (frame : after = { before with next := after.next, lencode := after.lencode, distcode := after.distcode, lenbits := after.lenbits, distbits := after.distbits, work := after.work, codes := after.codes, mode := after.mode })
    (workSize : after.work.size = 288) (codeSize : after.codes.size = 1444)
    (pointers : PtrInv zs after) (mode : HEAD ≤ after.mode ∧ after.mode ≤ SYNC) :
    LocalGood (setI h zs after) cutoff r zs z after := by
  have inv : StInv h zs after := by
    constructor
    · refine ⟨?_, workSize, codeSize⟩
      rw [frame]; exact good.inv.wf.1
    · rw [frame]
      exact ⟨good.inv.win.wbits, good.inv.win.block, good.inv.win.nullws,
        good.inv.win.ws, good.inv.win.hv, good.inv.win.wn, good.inv.win.eq⟩
    · rw [frame]; exact good.inv.reqbits
    · rw [frame]; exact good.inv.bits
    · exact pointers
  have result := good.setZI (stream := z) rfl good.live.zalloc good.live.zfree
    (by rw [frame]) mode inv
  rwa [ZStreamRef.put_self good.live.hz] at result

private theorem good_bad_mode {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (good : LocalGood h cutoff r zs z s) (i : Nat) :
    LocalGood (tcBadHeap h r zs z s i) cutoff r zs { z with msg := .ref (.str i) 0 } { s with mode := BAD } := by
  have inv : StInv h zs { s with mode := BAD } := by
    exact ⟨good.inv.wf,
      ⟨good.inv.win.wbits, good.inv.win.block, good.inv.win.nullws,
        good.inv.win.ws, good.inv.win.hv, good.inv.win.wn, good.inv.win.eq⟩,
      good.inv.reqbits, good.inv.bits, good.inv.ptr⟩
  exact good.setZI rfl good.live.zalloc good.live.zfree rfl (by change HEAD ≤ BAD ∧ BAD ≤ SYNC; decide) inv

private theorem bad_dataTableInvariant (h : Heap) (s : InflateState) :
    DataTableInvariant h { s with mode := BAD } := by
  intro active
  simp only [DataTableMode] at active
  rcases active with eq | eq | eq | eq | eq | eq | eq <;> cases eq

theorem clTables_run_good_full {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : LocalGood h cutoff r zs z s)
    (pointer : s.lencode = .ref (.istate_codes zs) 0)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) :
    (∃ ret after stream state,
      runX (clTables c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      LocalGood after cutoff r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      BitInv after { l with ret := ret } bs ∧
      ClTablesUpdate h r zs z s after stream state) ∨
    (∃ after state,
      LocalGood after cutoff r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      BitInv after { l with ret := 0 } bs ∧
      (runX (clTables c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after) ∧
      ClTablesUpdate h r zs z s after z state) := by
  have oldDist : ∃ offset, s.distcode = .ref (.istate_codes zs) offset ∧ offset ≤ 1443 := by
    rcases good.inv.ptr.2 with ⟨_, offset, _, dist, _, bound⟩ | ⟨fixed, _⟩
    · exact ⟨offset, dist, bound⟩
    · rw [pointer] at fixed
      cases fixed
  obtain ⟨lensRet, lensNext, lensBits, work1, codes1, workSize1, codeSize1,
    lensPointer, _, lensRun, lensSafe⟩ :=
    clTables_lens_run_complete hc good.live.hs good.inv.wf nlen (fun k bound => lengths k (by omega))
  let lensState := clLensResult zs s lensNext lensBits work1 codes1
  let lensAfter := setI h zs lensState
  obtain ⟨lensEnd, lensNextEq, lensEndBound⟩ := lensPointer
  have lensPtrs : PtrInv zs lensState := by
    obtain ⟨oldOffset, oldPointer, oldBound⟩ := oldDist
    refine ⟨⟨lensEnd, lensNextEq, by omega⟩,
      Or.inl ⟨0, oldOffset, rfl, oldPointer, by decide, oldBound⟩⟩
  have lensGood : LocalGood lensAfter cutoff r zs z lensState :=
    good_table_fields good rfl workSize1 codeSize1 lensPtrs good.live.mode
  have lensB : BitInv lensAfter { l with ret := lensRet } bs := by
    have inv : BitInv h { l with ret := lensRet } bs := ⟨B.have_eq, B.next, B.hold_lt⟩
    exact inv.setI zs _
  by_cases lensOk : lensRet = 0
  · obtain ⟨offset, next, room, safeLens, extentLens⟩ := lensSafe lensOk
    have lensWf : lensState.WellFormed := ⟨good.inv.wf.1, workSize1, codeSize1⟩
    have distLengths : ∀ k, k < lensState.ndist.toNat →
        (lensState.lens.getD (lensState.nlen.toNat + k) 0).toNat ≤ 15 := by
      intro k bound
      exact lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at bound; omega)
    obtain ⟨distRet, distNext, distBits, work2, codes2, workSize2, codeSize2,
      distPointer, _, distRun, preservedLens, _, safeDist⟩ :=
      clAfterLens_distance_run_complete (l := { l with ret := 0 }) hc lensGood.live.hs lensWf
        nlen ndist distLengths offset next room safeLens extentLens
    let state := clDistResult lensState distNext distBits work2 codes2
    let after := setI lensAfter zs state
    obtain ⟨distUsed, distNextEq, distUsedBound⟩ := distPointer
    have distPtrs : PtrInv zs state := by
      refine ⟨⟨offset + distUsed, distNextEq, by omega⟩,
        Or.inl ⟨0, offset, rfl, next, by decide, by omega⟩⟩
    have distGood : LocalGood after cutoff r zs z state :=
      good_table_fields lensGood rfl workSize2 codeSize2 distPtrs lensGood.live.mode
    have distB : BitInv after { l with ret := distRet } bs := by
      have inv : BitInv lensAfter { l with ret := distRet } bs := by
        have original : BitInv h { l with ret := distRet } bs := ⟨B.have_eq, B.next, B.hold_lt⟩
        exact original.setI zs _
      exact inv.setI zs _
    rw [lensOk] at lensRun
    have run : runX (clTables c) l h = runX (clAfterDist c distRet) { l with ret := distRet } after :=
      lensRun.trans distRun
    by_cases distOk : distRet = 0
    · right
      let final := { state with mode := LEN_ }
      let finalHeap := setI after zs final
      have finalGood : LocalGood finalHeap cutoff r zs z final :=
        good_table_fields distGood rfl workSize2 codeSize2 distPtrs (by change HEAD ≤ LEN_ ∧ LEN_ ≤ SYNC; decide)
      have data : DataTableInvariant finalHeap final := by
        intro _
        have get : Space.get finalHeap (CodeRef.istate_codes zs) = some codes2 := by
          simp [Space.get, finalHeap, final, after, state, setI, clDistResult]
        constructor
        · exact ⟨.istate_codes zs, 0, codes2, rfl, get, preservedLens⟩
        · exact ⟨.istate_codes zs, offset, codes2, next, get, safeDist distOk⟩
      have finalB : BitInv finalHeap { l with ret := 0 } bs := by
        rw [distOk] at distB
        exact distB.setI zs _
      refine ⟨finalHeap, final, finalGood, rfl, data, finalB, ?_, ?_⟩
      · rw [distOk] at run
        exact run.trans (clAfterDist_success hc distGood.live.hs)
      · refine ⟨?_, ?_, rfl⟩
        · simp only [finalHeap, after, lensAfter, setI_setI, ZStreamRef.put_self good.live.hz]
        · cases z; rfl
    · left
      obtain ⟨i, _, errorRun⟩ := clAfterDist_error (l := { l with ret := distRet }) hr hc
        distGood.live.hz distGood.live.hs distOk
      refine ⟨distRet, tcBadHeap after r zs z state i, _, _, run.trans errorRun,
        good_bad_mode distGood i, rfl, bad_dataTableInvariant _ _,
        (distB.put_stream r _).setI zs _, ?_⟩
      refine ⟨?_, rfl, rfl⟩
      simp only [tcBadHeap, after, lensAfter, ZStreamRef.put_setI, setI_setI]
  · left
    obtain ⟨i, _, errorRun⟩ := clAfterLens_error (l := { l with ret := lensRet }) hr hc
      lensGood.live.hz lensGood.live.hs lensOk
    refine ⟨lensRet, tcBadHeap lensAfter r zs z lensState i, _, _, lensRun.trans errorRun,
      good_bad_mode lensGood i, rfl, bad_dataTableInvariant _ _,
      (lensB.put_stream r _).setI zs _, ?_⟩
    refine ⟨?_, rfl, rfl⟩
    simp only [tcBadHeap, lensAfter, ZStreamRef.put_setI, setI_setI]

/-- The complete actual code-length reading loop retains the same public
buffer packet, exact input cursor and held-bit budget. Its only heap
writes are the state prefix and an optional error message. -/
theorem clRead_buffers {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (codes : CodeLengthInvariant zs s) (buffers : DispatchBuffers h r l bs) (mode : s.mode = CODELENS) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      CodeLengthInvariant zs state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧ regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧ after.static = h.static ∧
      state = { s with lens := state.lens, «have» := state.«have», mode := state.mode } ∧
      (state.mode = CODELENS ∨ state.mode = BAD) ∧
      (outcome = .ok () → state.mode = BAD ∨ state.«have».toNat = s.nlen.toNat + s.ndist.toNat) := by
  obtain ⟨outcome, regs, after, state, stream, run, current, nextCodes, tables, result⟩ :=
    clRead_run_good E.strm E.st good mode codes buffers.bits
  obtain ⟨outcome2, regs2, after2, run2, full, used, bound, inv, cursor, budget⟩ :=
    clRead_run_full_cursor E.strm E.st E.hz E.hs good.inv.wf.1 mode codes buffers.bits
  rw [run] at run2
  cases run2
  obtain ⟨readState, _, stateGet, _, _, regFrame, bitBound, stateFrame, _, _, _, modes, complete⟩ := result
  have same : readState = state := Option.some.inj (stateGet.symm.trans current.live.hs)
  subst readState
  obtain ⟨stream2, streamGet, streamFrame, heapState, heapEq⟩ := full.2
  have streamEq : stream2 = stream := Option.some.inj (streamGet.symm.trans current.live.hz)
  subst stream2
  have heapStateEq : heapState = state := by
    have get : after.istates zs = some heapState := by rw [heapEq]; simp
    exact Option.some.inj (get.symm.trans current.live.hs)
  subst heapState
  have views : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    rw [heapEq, byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h after := by intro ref; rw [views]
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have nextPending : DataPendingInvariant state := by
    apply dataPendingInvariant_idle (by rw [stateFrame]; exact pending.sane)
    rcases modes with normal | normal <;> rw [normal] <;> decide
  have packet : DispatchBuffers after r regs (bs.drop used) :=
    dispatch_advance_both_local buffers good current (by rw [stateFrame]) sizes readonly cursor count
      (made := 0) (by rw [regFrame, inputAdvance_zero]) (by rw [regFrame]; rfl)
      (by rw [regFrame]) inv
  exact ⟨outcome, regs, after, stream, state, used, bound, run, current, tables, nextPending,
    nextCodes, packet, sizes, cursor, count, by rw [regFrame], by rw [regFrame],
    by rw [regFrame], bitBound, budget, by rw [heapEq]; simp only [setI, ZStreamRef.put_static],
    stateFrame, modes, complete⟩


/-- Constructor metadata writes preserve public byte views and buffers.
The exact heap relation is produced by the actual two table constructors. -/
theorem clTablesUpdate_buffers {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l : IL} {bs : List UInt8}
    (before : LocalGood h cutoff r zs z s) (current : LocalGood after cutoff r zs stream state)
    (buffers : DispatchBuffers h r l bs)
    (update : ClTablesUpdate h r zs z s after stream state) (ret : Int32) :
    DispatchBuffers after r { l with ret := ret } bs ∧ ByteViewSizes h after ∧ after.static = h.static := by
  obtain ⟨heapEq, _, frame⟩ := update
  have views : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    rw [heapEq, byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [heapEq, byte_view_ro_setI, byte_view_ro_stream_put]
  have sizes : ByteViewSizes h after := by intro ref; rw [views]
  have inv : BitInv after { l with ret := ret } bs :=
    ⟨buffers.bits.have_eq, (buffers.bits.byte_views views).next, buffers.bits.hold_lt⟩
  refine ⟨?_, sizes, by rw [heapEq]; simp only [setI, ZStreamRef.put_static]⟩
  simpa only [List.drop_zero] using dispatch_advance_both_local buffers before current (by rw [frame]) sizes readonly
    (regs := { l with ret := ret }) (used := 0) (made := 0)
    (inputAdvance_zero l.next).symm (by rfl) (inputAdvance_zero l.put).symm (by rfl) rfl
    (by simpa only [List.drop_zero] using inv)

/-- Both actual dynamic table calls retain the complete packet. Refusals
stop at BAD; successful installation reaches the actual LEN_ continuation
or the documented Z_TREES exit, with no callee contract assumed. -/
theorem clTables_buffers {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs)
    (pointer : s.lencode = .ref (.istate_codes zs) 0)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15) :
    (∃ ret after stream state,
      runX (clTables c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      LocalGood after cutoff r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := ret } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧ ClTablesUpdate h r zs z s after stream state) ∨
    (∃ after state,
      LocalGood after cutoff r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := 0 } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧
      (runX (clTables c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after) ∧ ClTablesUpdate h r zs z s after z state) := by
  rcases clTables_run_good_full E.strm E.st good pointer nlen ndist lengths buffers.bits with bad | ready
  · obtain ⟨ret, after, stream, state, run, current, mode, tables, _, update⟩ := bad
    obtain ⟨packet, sizes, static⟩ := clTablesUpdate_buffers good current buffers update ret
    have nextPending : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (by rw [update.2.2]; exact pending.sane)
      rw [mode]
      decide
    exact Or.inl ⟨ret, after, stream, state, run, current, mode, tables, nextPending, packet, sizes, static, update⟩
  · obtain ⟨after, state, current, mode, tables, _, run, update⟩ := ready
    obtain ⟨packet, sizes, static⟩ := clTablesUpdate_buffers good current buffers update 0
    have nextPending : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (by rw [update.2.2]; exact pending.sane)
      rw [mode]
      decide
    exact Or.inr ⟨after, state, current, mode, tables, nextPending, packet, sizes, static, run, update⟩


/-- The real end-of-block check and both table constructors retain the
same buffer packet before the actual LEN_ continuation. -/
theorem clTail_buffers {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (codes : CodeLengthInvariant zs s)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat) :
    (∃ ret after stream state,
      runX (clTail c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      LocalGood after cutoff r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := ret } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧ ClTablesUpdate h r zs z s after stream state) ∨
    (∃ after state,
      LocalGood after cutoff r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      DataPendingInvariant state ∧ DispatchBuffers after r { l with ret := 0 } bs ∧
      ByteViewSizes h after ∧ after.static = h.static ∧
      (runX (clTail c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after) ∧ ClTablesUpdate h r zs z s after z state) := by
  have self : { l with ret := l.ret } = l := by cases l; rfl
  have modeRead : rdS c.st (·.mode) h = .ok (s.mode, h) := by rw [E.st, rdI_eq, E.hs]
  by_cases bad : s.mode = BAD
  · have update : ClTablesUpdate h r zs z s h z s := by
      refine ⟨?_, rfl, ?_⟩
      · rw [ZStreamRef.put_self E.hz, tcSetI_same E.hs]
      · rfl
    refine Or.inl ⟨l.ret, h, z, s, ?_, good, bad, ?_, pending,
      by simpa only [self] using buffers, ByteViewSizes.refl h, rfl, update⟩
    · simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_pure, self]
    · intro active
      rw [bad] at active
      exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode BAD) active)
  · have mode : s.mode = CODELENS := modes.resolve_left bad
    obtain ⟨pointer, _, nlen, ndist, _, initialized⟩ := codes mode
    have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
      rw [← done mode]
      exact initialized
    have inside : 0 + 256 < s.lens.size := by rw [good.inv.wf.1]; decide
    have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens E.hs) inside
    let value : UInt16 := s.lens[0 + 256]
    have read' : Ptr.index (lensP c.st) 256 h = .ok (value, h) := by rw [E.st]; exact read
    have tailRun : runX (clTail c) l h =
        if value = 0 then runX (do badMode c "invalid code -- missing end-of-block"; pure ()) l h
        else runX (clTables c) l h := by
      by_cases zero : value = 0 <;>
        simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_lift_ok read', zero]
    by_cases zero : value = 0
    · obtain ⟨i, _, run⟩ := tcBadMode_run (c := c) "invalid code -- missing end-of-block"
        lit_missing_eob E.strm E.st E.hz E.hs
      obtain ⟨current, tables, nextPending, packet, sizes, static⟩ :=
        Zlib.Inflate.Local.head_bad_packet good pending buffers buffers.bits (by rfl) i
      refine Or.inl ⟨l.ret, tcBadHeap h r zs z s i, { z with msg := .ref (.str i) 0 },
        { s with mode := BAD }, ?_, current, rfl, tables, nextPending,
        by rw [self]; exact packet, sizes, static, ?_⟩
      · rw [tailRun, if_pos zero]
        simpa [runX_bind, runX_lift_ok run, runX_pure, self]
      · exact ⟨rfl, rfl, by rfl⟩
    · have tables := clTables_buffers E good pending buffers pointer nlen ndist lengths
      rw [tailRun, if_neg zero]
      exact tables


end Zlib.Inflate.Local
