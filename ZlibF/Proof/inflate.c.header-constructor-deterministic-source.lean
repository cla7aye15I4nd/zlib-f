import ZlibF.Proof.«inflate.c.header-table-lens-public»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeBoundary Zlib.Inflate.Proofs.CumulativeTableBoundary
set_option autoImplicit false

theorem lenlens_alphabet_prefix_fields_source
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    {bs : List UInt8} {received : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (bound : s.ncode.toNat ≤ 19)
    (haveBound : s.«have».toNat ≤ s.ncode.toNat)
    (good : Good3 s.lens s.«have».toNat) (B : BitInv h l bs)
    (progress : LenlensProgress s l.hold l.bits received)
    (enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream l bs).length) :
    ∃ regs used state, used ≤ bs.length ∧
      BitInv h regs (bs.drop used) ∧ state.WellFormed ∧ Good3 state.lens 19 ∧
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.last = s.last ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ state.wsize = s.wsize ∧
      runX (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c)) l h =
        .ok ((.ok (), regs), setI h zs state) ∧
      runX (inflate_LENLENS c) l h = runX (llTail c) regs (setI h zs state) ∧
      ∀ future, readCodeLenLens s.ncode.toNat
        ((received ++ bytesBits (bs.take used)) ++ future) = some
        (Zlib.Inftrees.Proofs.lensOf (fun k => (state.lens.getD k 0).toNat) 19,
         natBits regs.bits.toNat regs.hold.toNat ++ future) := by
  obtain ⟨outcome, regs, used, count, countEq, readRun, usedBound, inv, trace⟩ :=
    ll1_header_progress hc hs wf.1 bound haveBound B progress
  have full : count = s.ncode.toNat - s.«have».toNat := by
    rw [countEq]
    apply Nat.min_eq_left
    omega
  rw [full] at readRun inv trace
  obtain ⟨outcome0, regs0, used0, readRun0, usedBound0, inv0, _remaining, regShape, _wait, complete⟩ :=
    ll1_run hc hs wf.1 bound haveBound B
  have maxReads : min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) =
      s.ncode.toNat - s.«have».toNat := by apply Nat.min_eq_left; omega
  rw [maxReads, readRun] at readRun0
  cases readRun0
  have normal := complete maxReads
  subst outcome
  let readState := llSt s (stream l bs) (s.ncode.toNat - s.«have».toNat)
  have readCount : readState.«have».toNat = s.ncode.toNat := by
    rw [llSt_have s _ _ (by omega)]
    omega
  have readGood : Good3 readState.lens readState.«have».toNat := by
    change Good3 (lensRead s.lens s.«have».toNat (stream l bs)
      (s.ncode.toNat - s.«have».toNat)) readState.«have».toNat
    rw [← show s.«have».toNat + (s.ncode.toNat - s.«have».toNat) =
      readState.«have».toNat by rw [readCount]; omega]
    exact lensRead_good _ good _ (by omega)
  have size : readState.lens.size = 320 := by
    change (lensRead s.lens s.«have».toNat _ _).size = 320
    rw [lensRead_size]
    exact wf.1
  let state := lzSt readState (19 - readState.«have».toNat)
  have zeroRun := lz_run (c := c) (l := regs) hc
    (show (setI h zs readState).istates zs = some readState by simp) size (by omega)
  have filled : Good3 state.lens 19 := by
    change Good3 (lensZero readState.lens readState.«have».toNat
      (19 - readState.«have».toNat)) 19
    have key := lensZero_good readGood (19 - readState.«have».toNat) (by omega)
    simpa only [show readState.«have».toNat + (19 - readState.«have».toNat) = 19 by omega] using key
  refine ⟨regs, used, state, usedBound, ?_, ?_, filled, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · have same : used0 = used := by
      have first := inv.have_eq
      have second := inv0.have_eq
      rw [List.length_drop] at first second
      omega
    subst used0
    exact inv0
  · refine ⟨?_, wf.2.1, wf.2.2⟩
    change (lensZero readState.lens _ _).size = 320
    rw [lensZero_size]
    exact size
  · rw [regShape]
  · rw [regShape]
  · rw [regShape]
  · rw [runX_bind, readRun]
    simp only []
    rw [zeroRun]
    simp only [setI_setI]
    rfl
  · rw [inflate_LENLENS_eq, runX_bind, readRun]
    simp only []
    rw [runX_bind, zeroRun]
    simp only [setI_setI]
    rfl
  · intro future
    exact trace.alphabet (by change 19 ≤ readState.lens.size; rw [size]; decide) bound readCount readGood future



theorem lenlens_constructor_boundary_ready_source
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    {bs : List UInt8} {received : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (bound : s.ncode.toNat ≤ 19)
    (haveBound : s.«have».toNat ≤ s.ncode.toNat)
    (good : Good3 s.lens s.«have».toNat) (B : BitInv h l bs)
    (progress : LenlensProgress s l.hold l.bits received)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream l bs).length) :
    ∃ (regs : IL) (used : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      runX (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c)) l h =
        .ok ((.ok (), regs), setI h zs filled) ∧
      runX (llInstall c) regs (setI h zs filled) =
        .ok ((.ok ret, { regs with ret := ret }),
          setI h zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 ∨ ret = -1) ∧
      (ret = 0 ↔ Acceptable .codeLength
        (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) ∧
      (∀ future, readCodeLenLens s.ncode.toNat
        ((received ++ bytesBits (bs.take used)) ++ future) = some
        (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19,
          natBits regs.bits.toNat regs.hold.toNat ++ future)) ∧
      (ret = 0 →
        let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
        state.WellFormed ∧ CodeLengthInvariant zs state ∧
        Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat
          (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19) ∧
        actualLengthPrefix state = [] ∧
        state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.last = s.last ∧
        regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ state.wsize = s.wsize ∧
        BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
        runX (inflate_LENLENS c) l h =
          runX (inflate_CODELENS c) { regs with ret := 0 } (setI h zs state)) := by
  obtain ⟨regs, used, filled, usedBound, inv, filledWf, filledGood,
    codeCount, litCount, distCount, last, put, left, out, window, headerRun, cut, alphabet⟩ :=
    lenlens_alphabet_prefix_fields_source hc hs wf bound haveBound good B progress enough
  obtain ⟨ret, next, root, work, codes, workSize, codeSize, _workFrame, _codeFrame,
    install, kinds, precise, semantic⟩ :=
    llInstall_code_length_contents_result (l := regs) hc (show (setI h zs filled).istates zs = some filled by simp) filledWf filledGood
  change (ret = 0 ↔ Acceptable .codeLength
    (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) at precise
  refine ⟨regs, used, filled, ret, next, root, work, codes, usedBound, inv, headerRun, ?_, kinds, precise, alphabet, ?_⟩
  · simpa only [setI_setI] using install
  · intro success
    have contents := semantic success
    refine ⟨⟨filledWf.1, workSize, codeSize⟩, ?_, contents, ?_, codeCount, litCount, distCount, last, put, left, out, window, ?_, ?_⟩
    · intro _
      refine ⟨rfl, contents.safe, ?_, ?_, ?_, ?_⟩
      · change filled.nlen.toNat ≤ 286
        rw [litCount]
        exact nlen
      · change filled.ndist.toNat ≤ 30
        rw [distCount]
        exact ndist
      · simp
      · intro k inside
        change k < (0 : UInt32).toNat at inside
        have zero : (0 : UInt32).toNat = 0 := by decide
        omega
    · simp [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf]
    · exact (show BitInv h { regs with ret := 0 } (bs.drop used) from ⟨inv.have_eq, inv.next, inv.hold_lt⟩).setI zs _
    · have tail : runX (llTail c) regs (setI h zs filled) =
          runX (inflate_CODELENS c) { regs with ret := 0 }
            (setI (setI h zs filled) zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }) := by
        rw [llTail_install_eq, runX_bind, install, success]
        simp [hc, runX_bind, runX_lift, wrI_eq, setI_setI]
      exact cut.trans (by simpa only [setI_setI] using tail)




theorem Meaning.lens_constructor_prefix_wait
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {stream0 : ZStream} {observedState : InflateState}
    (before : Meaning .lens h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (nonnull : stream0.next_out ≠ .null) (inputValid : stream0.next_in = .null → stream0.avail_in = 0)
    (actual : DataStep .inflate h after r flush rc input output used)
    (enough : 3 * (observedState.ncode.toNat - observedState.«have».toNat) ≤
      (stream (dispatchRegs stream0 observedState) input).length) :
    ∃ (headerRegs : IL) (headerUsed : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      headerUsed ≤ input.length ∧
      runX (do
        (do xwhile (llCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (llBody ⟨some r, some (.tab zs), syncBuf h, flush⟩)
            xwhile (lzCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (lzBody ⟨some r, some (.tab zs), syncBuf h, flush⟩))
        llInstall ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs stream0 observedState) (syncAlloc h) =
        .ok ((.ok ret, { headerRegs with ret := ret }),
          setI (syncAlloc h) zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 →
        ¬ (∀ value ∈ Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19, value = 0) →
        let codeState := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
        ∀ (regs : IL) (readHeap : Heap) (readState : InflateState),
          runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) { headerRegs with ret := 0 }
            (setI (syncAlloc h) zs codeState) = .ok ((.error Ex.leave, regs), readHeap) →
          readHeap.istates zs = some readState → readState.mode = CODELENS →
          Meaning .code after r zs (credit log input output used rc)) := by
  obtain ⟨z, state, current, allocator, window, empty, mode, record, received, lastBound, last, countsView,
    litCount, distCount, codeCount, progress⟩ := before
  have sameZ : stream0 = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
  have sameS : observedState = state := Option.some.inj (getS.symm.trans current.good.live.hs)
  subst stream0 observedState
  have actual0 := actual
  obtain ⟨z0, returned, get0, get1, _buffers, _header, bytes, usedEq, _outputBytes, _run⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := state) bytes current.held
  have allocated := default_origin_syncAlloc current
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z state := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have view0 : BitInv (syncAlloc h) (dispatchRegs z state) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with null | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc current.good.fresh get).1, bound, values⟩
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := current.headerLengths mode
  obtain ⟨headerRegs, headerUsed, filled, ret, next, root, work, codes, headerBound, _inputB,
    headerRun, install, _kinds, _successIff, alphabetRead, ready⟩ :=
    lenlens_constructor_boundary_ready_source env.st env.hs current.good.inv.wf ncode haveBound good view0 progress nlen ndist enough
  refine ⟨headerRegs, headerUsed, filled, ret, next, root, work, codes, headerBound, ?_, ?_⟩
  · rw [runX_bind, headerRun]
    exact install
  intro success nonempty
  dsimp only
  intro regs readHeap readState readRun readGet readMode
  obtain ⟨wf, inv, contents, emptyPrefix, code, lit, dist, savedLast, put, left, out, codeWindow, codeB, cut⟩ := ready success
  let codeState := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  let alphabet := Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19
  have ordinary : ∀ index, index < 2 ^ codeState.lenbits.toNat → ∃ entry, codeState.codes[index]? = some entry ∧ entry.op = 0 := by
    rcases contents.layout with emptyRoot | ordinaryRoot
    · exact False.elim (nonempty emptyRoot.2.1)
    · simpa only [Nat.zero_add] using ordinaryRoot
  have prefixCut : runX (inflate_dispatch c) (dispatchRegs z state) (syncAlloc h) =
      runX (inflate_CODELENS c) { headerRegs with ret := 0 } (setI (syncAlloc h) zs codeState) := by
    rw [inflate_dispatch_LENLENS env _ mode]
    exact cut
  obtain ⟨nextZ, nextS, readUsed, nextJ, nextAllocator, noOutput, availIn, stateMode, stateWindow,
    finalCode, finalLit, finalDist, finalLast, finalContents, finalOrdinary, readBound, readB, nextProgress⟩ :=
    phase_to_codelens_observed_seed_with_last current allocator actual0 nonnull inputValid (by rw [mode]; decide) prefixCut
      (by simpa using env.hz) (by rw [setI_istates_same]) wf rfl inv contents ordinary codeB emptyPrefix (codeWindow.trans window)
      (by change headerRegs.out_ = headerRegs.left; rw [out, left]; rfl) put left readRun readGet readMode
  have returnedEq : returned = nextZ := Option.some.inj (get1.symm.trans nextJ.good.live.hz)
  subst returned
  have actualUse : headerUsed + readUsed = used := by
    have before := view.have_eq
    have finalHave := readB.have_eq
    rw [usedEq, availIn]
    change z.avail_in.toNat = input.length at before
    simp only [List.length_drop] at finalHave readBound
    omega
  have alphabetView : View readAlphabet ⟨record, alphabet⟩
      (bytesBits log.input ++ bytesBits (input.take headerUsed))
      (natBits headerRegs.bits.toNat headerRegs.hold.toNat) := by
    apply countsView.alphabet_of_counts
    rw [← codeCount]
    exact alphabetRead
  have wholeView := alphabetView.advance (bytesBits ((input.drop headerUsed).take readUsed))
  refine ⟨nextZ, nextS, nextJ, nextAllocator, stateWindow, ?_, stateMode, ⟨record, alphabet⟩,
    natBits headerRegs.bits.toNat headerRegs.hold.toNat ++ bytesBits ((input.drop headerUsed).take readUsed),
    lastBound, ?_, ?_, ?_, ?_, ?_, finalContents, finalOrdinary, ?_⟩
  · simp only [credit, empty, noOutput, List.nil_append]
  · rw [finalLast, savedLast]; exact last
  · simpa only [credit, bytesBits_append, ← actualUse, List.take_add, List.append_assoc] using wholeView
  · rw [finalLit, lit]; exact litCount
  · rw [finalDist, dist]; exact distCount
  · rw [finalCode, code]; exact codeCount
  · simpa only [finalLit, finalDist] using nextProgress



/-- A deterministic source selector contains only the actual combined
header/constructor run, actual state getters, the nonzero source alphabet
and actual exhausted clRead run. Its desired Meaning is derived. -/
theorem Meaning.lens_constructor_observed
    {h after prefixHeap readHeap : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {stream0 : ZStream} {observedState installed readState : InflateState} {prefixRegs regs : IL}
    (before : Meaning .lens h r zs log) (getZ : r.get h = some stream0) (getS : h.istates zs = some observedState)
    (nonnull : stream0.next_out ≠ .null) (inputValid : stream0.next_in = .null → stream0.avail_in = 0)
    (actual : DataStep .inflate h after r flush rc input output used)
    (enough : 3 * (observedState.ncode.toNat - observedState.«have».toNat) ≤
      (stream (dispatchRegs stream0 observedState) input).length)
    (prefixRun : runX (do
      (do xwhile (llCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (llBody ⟨some r, some (.tab zs), syncBuf h, flush⟩)
          xwhile (lzCond ⟨some r, some (.tab zs), syncBuf h, flush⟩) (lzBody ⟨some r, some (.tab zs), syncBuf h, flush⟩))
      llInstall ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs stream0 observedState) (syncAlloc h) =
        .ok ((.ok 0, prefixRegs), prefixHeap))
    (prefixGet : prefixHeap.istates zs = some installed)
    (nonempty : ¬ (∀ value ∈ Zlib.Inftrees.Proofs.lensOf (fun k => (installed.lens.getD k 0).toNat) 19, value = 0))
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) prefixRegs
      (setI prefixHeap zs { installed with «have» := 0, mode := CODELENS }) = .ok ((.error Ex.leave, regs), readHeap))
    (readGet : readHeap.istates zs = some readState) (readMode : readState.mode = CODELENS) :
    Meaning .code after r zs (credit log input output used rc) := by
  obtain ⟨headerRegs, headerUsed, filled, ret, next, root, work, codes, _bound, computed, branch⟩ :=
    before.lens_constructor_prefix_wait getZ getS nonnull inputValid actual enough
  have same := Except.ok.inj (computed.symm.trans prefixRun)
  cases same
  simp only [setI_istates_same] at prefixGet
  have sameInstalled := Option.some.inj prefixGet
  subst installed
  apply branch rfl nonempty regs readHeap readState
  · simpa only [setI_setI] using readRun
  · exact readGet
  · exact readMode

#print axioms lenlens_alphabet_prefix_fields_source
#print axioms lenlens_constructor_boundary_ready_source
#print axioms Meaning.lens_constructor_prefix_wait
#print axioms Meaning.lens_constructor_observed
end Zlib.Inflate.Proofs.HeaderPhaseView
