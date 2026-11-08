import ZlibF.Proof.«inflate.c.codelens-loop»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual reading loop preserves the public representation and the
CODELENS boundary relation, including BAD and input-exhaustion exits. The
stream's control fields and all storage outside its two records retain
the exact update relation from clRead_run_full. -/
theorem clRead_run_good {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs) :
    ∃ outcome regs after state stream,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ CodeLengthInvariant zs state ∧
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

theorem clAfterLens_error {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {ret : Int32}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s) (error : ret ≠ 0) :
    ∃ i, strTable[i]? = some "invalid literal/lengths set" ∧
      runX (clAfterLens c ret) l h = .ok ((.ok (), l), tcBadHeap h r zs z s i) := by
  obtain ⟨i, literal, bad⟩ := tcBadMode_run (c := c) "invalid literal/lengths set"
    lit_literal_lengths hr hc hz hs
  refine ⟨i, literal, ?_⟩
  unfold clAfterLens
  simp [error, runX_bind, runX_lift_ok bad, runX_pure]

theorem clAfterDist_error {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {ret : Int32}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s) (error : ret ≠ 0) :
    ∃ i, strTable[i]? = some "invalid distances set" ∧
      runX (clAfterDist c ret) l h = .ok ((.ok (), l), tcBadHeap h r zs z s i) := by
  obtain ⟨i, literal, bad⟩ := tcBadMode_run (c := c) "invalid distances set"
    lit_distances hr hc hz hs
  refine ⟨i, literal, ?_⟩
  unfold clAfterDist
  simp [error, runX_bind, runX_lift_ok bad, runX_pure]

private theorem good_table_fields {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {before after : InflateState} (good : Good h r zs z before)
    (frame : after = { before with next := after.next, lencode := after.lencode, distcode := after.distcode, lenbits := after.lenbits, distbits := after.distbits, work := after.work, codes := after.codes, mode := after.mode })
    (workSize : after.work.size = 288) (codeSize : after.codes.size = 1444)
    (pointers : PtrInv zs after) (mode : HEAD ≤ after.mode ∧ after.mode ≤ SYNC) :
    Good (setI h zs after) r zs z after := by
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
  have result := good.setZI (z' := z) rfl good.live.zalloc good.live.zfree
    (by rw [frame]) mode inv
  rwa [ZStreamRef.put_self good.live.hz] at result

private theorem good_bad_mode {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (good : Good h r zs z s) (i : Nat) :
    Good (tcBadHeap h r zs z s i) r zs { z with msg := .ref (.str i) 0 } { s with mode := BAD } := by
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

/-- The constructor suffix changes only table fields and the error message.
This exact record update retains the caller frame for later composition. -/
def ClTablesUpdate (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (before : InflateState) (after : Heap) (stream : ZStream) (state : InflateState) : Prop :=
  after = setI (r.put h stream) zs state ∧ stream = { z with msg := stream.msg } ∧
    state = { before with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode }

/-- The actual dynamic-table suffix covers both constructor refusals and
successful installation. Every branch restores Good. Successful branches
activate decoder table safety before the actual LEN_ continuation. -/
theorem clTables_run_good_full {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (pointer : s.lencode = .ref (.istate_codes zs) 0)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) :
    (∃ ret after stream state,
      runX (clTables c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      Good after r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      BitInv after { l with ret := ret } bs ∧
      ClTablesUpdate h r zs z s after stream state) ∨
    (∃ after state,
      Good after r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
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
  have lensGood : Good lensAfter r zs z lensState :=
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
    have distGood : Good after r zs z state :=
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
      have finalGood : Good finalHeap r zs z final :=
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

/-- The actual dynamic-table suffix covers both constructor refusals and
successful installation. Every branch restores Good. Successful branches
activate decoder table safety before the actual LEN_ continuation. -/
theorem clTables_run_good {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (pointer : s.lencode = .ref (.istate_codes zs) 0)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) :
    (∃ ret after stream state,
      runX (clTables c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      Good after r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      BitInv after { l with ret := ret } bs) ∨
    (∃ after state,
      Good after r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      BitInv after { l with ret := 0 } bs ∧
      runX (clTables c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after) := by
  rcases clTables_run_good_full hr hc good pointer nlen ndist lengths B with bad | success
  · obtain ⟨ret, after, stream, state, run, finalGood, mode, data, inv, _⟩ := bad
    exact Or.inl ⟨ret, after, stream, state, run, finalGood, mode, data, inv⟩
  · obtain ⟨after, state, finalGood, mode, data, inv, run, _⟩ := success
    exact Or.inr ⟨after, state, finalGood, mode, data, inv, run⟩

/-- A safe mode exit, or the actual continuation after installing decoder tables.
The second case makes no assumption about the continuation's contract. -/
def ClTailBoundary (c : Ctx) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (bs : List UInt8) (l : IL) (h : Heap) : Prop :=
    (∃ ret after stream state,
      runX (clTail c) l h = .ok ((.ok (), { l with ret := ret }), after) ∧
      Good after r zs stream state ∧ state.mode = BAD ∧ DataTableInvariant after state ∧
      BitInv after { l with ret := ret } bs) ∨
    (∃ after state,
      Good after r zs z state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      BitInv after { l with ret := 0 } bs ∧
      runX (clTail c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), after)
        else runX (inflate_LEN_ c) { l with ret := 0 } after)

/-- The actual mode and end-of-block checks precede both constructors.
A rejected end-of-block code returns safely in BAD mode. -/
theorem clTail_run_good {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (B : BitInv h l bs) : ClTailBoundary c r zs z bs l h := by
  unfold ClTailBoundary
  have self : { l with ret := l.ret } = l := by cases l; rfl
  have modeRead : rdS c.st (·.mode) h = .ok (s.mode, h) := by
    rw [hc, rdI_eq, good.live.hs]
  by_cases bad : s.mode = BAD
  · left
    refine ⟨l.ret, h, z, s, ?_, good, bad, ?_, ?_⟩
    · simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_pure]
    · intro active
      rw [bad] at active
      simp only [DataTableMode] at active
      rcases active with eq | eq | eq | eq | eq | eq | eq <;> cases eq
    · simpa only [self] using B
  · have mode : s.mode = CODELENS := modes.resolve_left bad
    obtain ⟨pointer, _, nlen, ndist, _, initialized⟩ := stateInv mode
    have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
      rw [← done mode]
      exact initialized
    have inside : 0 + 256 < s.lens.size := by rw [good.inv.wf.1]; decide
    have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens good.live.hs) inside
    let value : UInt16 := s.lens[0 + 256]
    have read' : Ptr.index (lensP c.st) 256 h = .ok (value, h) := by
      rw [hc]
      exact read
    have tailRun : runX (clTail c) l h =
        if value = 0 then runX (do badMode c "invalid code -- missing end-of-block"; pure ()) l h
        else runX (clTables c) l h := by
      by_cases zero : value = 0 <;>
        simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_lift_ok read', zero]
    by_cases zero : value = 0
    · left
      obtain ⟨i, _, badRun⟩ := tcBadMode_run (c := c) "invalid code -- missing end-of-block"
        lit_missing_eob hr hc good.live.hz good.live.hs
      refine ⟨l.ret, tcBadHeap h r zs z s i, _, _, ?_, good_bad_mode good i,
        rfl, bad_dataTableInvariant _ _, ?_⟩
      · rw [tailRun, if_pos zero]
        simpa [runX_bind, runX_lift_ok badRun, runX_pure]
      · rw [self]
        exact (B.put_stream r { z with msg := .ref (.str i) 0 }).setI zs { s with mode := BAD }
    · rw [tailRun, if_neg zero]
      exact clTables_run_good hr hc good pointer nlen ndist lengths B

/-- The complete actual CODELENS mode reaches a checked exit or the actual
LEN_ continuation. No contract for that continuation is assumed. The loop,
both constructors, error paths and Z_TREES exit are all executed here. -/
theorem inflate_CODELENS_boundary {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs) :
    ∃ used regs, used ≤ bs.length ∧ regs.bits.toNat ≤ max l.bits.toNat 21 ∧
    ((∃ outcome after stream state,
      runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      BitInv after regs (bs.drop used) ∧ (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
    (∃ after stream state,
      Good after r zs stream state ∧ state.mode = LEN_ ∧ DataTableInvariant after state ∧
      BitInv after regs (bs.drop used) ∧
      runX (inflate_CODELENS c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
        else runX (inflate_LEN_ c) regs after)) := by
  obtain ⟨outcome, regs, after, state, stream, run, nextGood, nextCodes, nextData, result⟩ :=
    clRead_run_good hr hc good mode stateInv B
  obtain ⟨readState, used, stateGet, usedBound, nextB, _, bits, stateFrame,
    _, _, _, modes, complete⟩ := result
  have same : readState = state := Option.some.inj (stateGet.symm.trans nextGood.live.hs)
  subst readState
  cases outcome with
  | error e =>
    have source : runX (inflate_CODELENS c) l h = .ok ((.error e, regs), after) := by
      rw [inflate_CODELENS_eq, runX_bind, run]
    refine ⟨used, regs, usedBound, bits, Or.inl ?_⟩
    exact ⟨.error e, after, stream, state, source, nextGood, nextData, nextB, Or.inl (by intro eq; cases eq)⟩
  | ok unit =>
    cases unit
    have source : runX (inflate_CODELENS c) l h = runX (clTail c) regs after := by
      rw [inflate_CODELENS_eq, runX_bind, run]
    have done : state.mode = CODELENS → state.«have».toNat = state.nlen.toNat + state.ndist.toNat := by
      intro codes
      have total := complete rfl
      rcases total with bad | total
      · rw [codes] at bad
        cases bad
      · calc
          state.«have».toNat = s.nlen.toNat + s.ndist.toNat := total
          _ = state.nlen.toNat + state.ndist.toNat := by rw [stateFrame]
    have tail := clTail_run_good hr hc nextGood modes.symm nextCodes done nextB
    rcases tail with bad | success
    · obtain ⟨ret, finalHeap, finalStream, finalState, tailRun, finalGood, badMode, finalData, finalB⟩ := bad
      refine ⟨used, { regs with ret := ret }, usedBound, bits, Or.inl ?_⟩
      exact ⟨.ok (), finalHeap, finalStream, finalState, source.trans tailRun,
        finalGood, finalData, finalB, Or.inr badMode⟩
    · obtain ⟨finalHeap, finalState, finalGood, finalMode, finalData, finalB, tailRun⟩ := success
      refine ⟨used, { regs with ret := 0 }, usedBound, bits, Or.inr ?_⟩
      exact ⟨finalHeap, stream, finalState, finalGood, finalMode, finalData, finalB, source.trans tailRun⟩

/-- With the public Z_TREES flush, CODELENS itself has no unresolved
continuation: every admitted entry returns without a runtime fault. This
is a mode theorem, not the public inflate theorem. -/
theorem inflate_CODELENS_trees_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (good : Good h r zs z s) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s) (B : BitInv h l bs)
    (flush : c.flush = Z_TREES) :
    ∃ used regs outcome after stream state,
      used ≤ bs.length ∧ regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      runX (inflate_CODELENS c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧
      BitInv after regs (bs.drop used) ∧
      (outcome = .ok () → state.mode = BAD) := by
  obtain ⟨used, regs, usedBound, bits, stopped | continued⟩ :=
    inflate_CODELENS_boundary hr hc good mode stateInv B
  · obtain ⟨outcome, after, stream, state, run, nextGood, data, nextB, why⟩ := stopped
    refine ⟨used, regs, outcome, after, stream, state, usedBound, bits, run, nextGood, data, nextB, ?_⟩
    intro ok
    exact why.resolve_left (fun unequal => unequal ok)
  · obtain ⟨after, stream, state, nextGood, _, data, nextB, run⟩ := continued
    rw [if_pos flush] at run
    exact ⟨used, regs, .error Ex.leave, after, stream, state, usedBound, bits,
      run, nextGood, data, nextB, fun impossible => by cases impossible⟩

end Zlib.Inflate.Proofs
