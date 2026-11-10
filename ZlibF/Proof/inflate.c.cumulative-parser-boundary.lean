import ZlibF.Proof.«inflate.c.cumulative-parser-history»

namespace Zlib.Inflate.Proofs.CumulativeBoundary
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CumulativeParser
set_option autoImplicit false

/-- Any actual header dispatch which exhausts its input takes one main
loop trip and the real no-window leave suffix. All supplied equations are
source observations, independently of the header parser's meaning. -/
theorem header_dispatch_wait_body
    {c : Ctx} {h readHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s readState : InflateState} {regs : IL}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (noType : s.mode ≠ TYPE)
    (step : runX (inflate_dispatch c) (dispatchRegs z s) h = .ok ((.error Ex.leave, regs), readHeap))
    (readGet : readHeap.istates zs = some readState) (window : readState.wsize = 0)
    (noOutput : regs.out_ = regs.left) (put : regs.put = z.next_out) (left : regs.left = z.avail_out) :
    ∃ rc after stream0 state,
      (do let (result, localRegs) ← runX (inflate_run c) IL.init
          match result with | .error (.ret value) => pure value | _ => inflate_leave c localRegs) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧
      LeaveMetadataFrame (leaveState readState regs) state ∧
      stream0.next_in = regs.next ∧ stream0.avail_in = regs.have_ ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => dispatchRegs z s) (fun _ => h)
    0 (by unfold fuel; decide) Ex.leave regs readHeap (by intro j impossible; omega) step
  have entry : runX (inflate_run c) IL.init h =
      runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z s) h := by
    unfold inflate_run
    rw [runX_bind, runX_rdS E]
    simp only [noType, beq_iff_eq, ite_false, runX_bind]
    rw [LOAD_run E]
    simp only []
    rw [runX_modify]
    rfl
  have mainRun : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), readHeap) := entry.trans loop
  obtain ⟨_bs0, exit, regs0, heap0, stream0, state0, _used0, _made0, _bound0, run0, current,
    packet, bitBound, _sizes, _next, _count, _put, _left, _fixed, currentAllocator⟩ :=
    inflate_run_default_origin_framed E initial allocator buffers nonnull inputValid
  rw [mainRun] at run0
  cases run0
  have sameState : state0 = readState := Option.some.inj (current.good.live.hs.symm.trans readGet)
  subst state0
  have env : Env c readHeap r zs stream0 readState := ⟨E.strm, E.st, current.good.live.hz, readGet⟩
  obtain ⟨rc, after, finalStream, state, leave, final, finalAllocator, frame,
    nextIn, availIn, nextOut, availOut⟩ :=
    EntryPath.HeadHistory.leave_wait_no_window env current currentAllocator packet bitBound window noOutput
  refine ⟨rc, after, finalStream, state, ?_, final, finalAllocator, frame, nextIn, availIn, nextOut.trans put, availOut.trans left⟩
  rw [bind_app, mainRun]
  exact leave

/-- The actual phase-changing dispatch also crosses allocation and free
of the public local object, retaining its exact decoder metadata frame. -/
theorem header_dispatch_wait_public
    {h readHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s readState : InflateState} {regs : IL} {flush : Int32}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (noType : s.mode ≠ TYPE)
    (step : runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), readHeap)) (readGet : readHeap.istates zs = some readState)
    (window : readState.wsize = 0) (noOutput : regs.out_ = regs.left)
    (put : regs.put = z.next_out) (left : regs.left = z.avail_out) :
    ∃ rc after stream0 state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ after.bytes h.nextBlk = none ∧
      LeaveMetadataFrame (leaveState readState regs) state ∧
      stream0.next_in = regs.next ∧ stream0.avail_in = regs.have_ ∧
      stream0.next_out = z.next_out ∧ stream0.avail_out = z.avail_out := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_origin_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
    by_cases null : z.next_in = .null
    · simp [nonnull, null, inputValid null]
    · simp [nonnull, null]
  obtain ⟨rc, heap1, stream0, state, bytes, bodyRun, current, finalAllocator, localGet, localSize, localRo⟩ :=
    inflate_default_origin_local_state_return env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  obtain ⟨traceRc, traceHeap, traceStream, traceState, traceRun, traceFinal, _traceAllocator,
    frame, nextIn, availIn, nextOut, availOut⟩ :=
    header_dispatch_wait_body env allocated allocator (streamBuffers_syncAlloc initial.good.fresh buffers)
      nonnull inputValid noType step readGet window noOutput put left
  have same : (rc, heap1) = (traceRc, traceHeap) := Except.ok.inj (bodyRun.symm.trans traceRun)
  cases same
  have sameState : state = traceState := Option.some.inj (current.good.live.hs.symm.trans traceFinal.good.live.hs)
  have sameStream : stream0 = traceStream := Option.some.inj (current.good.live.hz.symm.trans traceFinal.good.live.hz)
  subst traceState traceStream
  have final := current.free_local localGet localSize
  refine ⟨rc, freeWin heap1 (syncBuf h), stream0, state, ?_, final, finalAllocator, ?_, frame, nextIn, availIn, nextOut, availOut⟩
  · unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live, bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  · simp only [syncBuf, freeWin, upd_same]

#print axioms header_dispatch_wait_body
#print axioms header_dispatch_wait_public

/-- A real header dispatch prefix and exhausted CODELENS reader establish
the stored ledger after their same public call. Its constructor facts come
from the actual alphabet producer; no desired parser postcondition occurs
among the source observations. -/
theorem phase_to_codelens_observed_seed
    {h after codeHeap readHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s codeState readState : InflateState} {codeRegs regs : IL} {codeInput input output : List UInt8}
    {alphabet : List Nat} {flush rc : Int32} {used : Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0) (noType : s.mode ≠ TYPE)
    (prefixCut : runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      runX (inflate_CODELENS ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs codeHeap)
    (codeZ : r.get codeHeap = some z) (codeGet : codeHeap.istates zs = some codeState)
    (wf : codeState.WellFormed) (codeMode : codeState.mode = CODELENS) (codeInv : CodeLengthInvariant zs codeState)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents codeState.codes 0 codeState.lenbits.toNat alphabet)
    (ordinary : ∀ index, index < 2 ^ codeState.lenbits.toNat → ∃ entry, codeState.codes[index]? = some entry ∧ entry.op = 0)
    (codeB : BitInv codeHeap codeRegs codeInput) (emptyPrefix : actualLengthPrefix codeState = [])
    (codeWindow : codeState.wsize = 0) (codeNoOutput : codeRegs.out_ = codeRegs.left)
    (codePut : codeRegs.put = z.next_out) (codeLeft : codeRegs.left = z.avail_out)
    (readRun : runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs codeHeap =
      .ok ((.error Ex.leave, regs), readHeap)) (readGet : readHeap.istates zs = some readState)
    (readMode : readState.mode = CODELENS) :
    ∃ stream0 state readUsed,
      DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧ stream0.avail_in = regs.have_ ∧
      state.mode = CODELENS ∧ state.wsize = 0 ∧
      state.ncode = codeState.ncode ∧ state.nlen = codeState.nlen ∧ state.ndist = codeState.ndist ∧
      Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
      (∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
      readUsed ≤ codeInput.length ∧ BitInv readHeap regs (codeInput.drop readUsed) ∧
      Progress alphabet (codeState.nlen.toNat + codeState.ndist.toNat) []
        (natBits codeRegs.bits.toNat codeRegs.hold.toNat ++ bytesBits (codeInput.take readUsed)) state := by
  obtain ⟨z0, returned, get0, get1, buffers, _header, _inputBytes, _usedEq, outputBytes, actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  obtain ⟨outcome, regs0, heap0, state0, readUsed, run0, full, getState, bound, readB, causal⟩ :=
    clRead_exact_consumed_input (c := ⟨some r, some (.tab zs), syncBuf h, flush⟩) rfl rfl codeZ codeGet wf.1 codeMode codeInv contents ordinary codeB
  rw [readRun] at run0
  cases run0
  have sameState : state0 = readState := Option.some.inj (getState.symm.trans readGet)
  subst state0
  have notBad : readState.mode ≠ BAD := by rw [readMode]; decide
  obtain ⟨consumed, source, trace⟩ := causal notBad
  rw [emptyPrefix] at trace
  obtain ⟨state0, _used0, get0, _bound0, _inv0, shape, _bits, readFrame, _remaining⟩ := full.1
  have sameState : state0 = readState := Option.some.inj (get0.symm.trans readGet)
  subst state0
  have step : runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
      .ok ((.error Ex.leave, regs), readHeap) := by rw [prefixCut, inflate_CODELENS_eq, runX_bind, readRun]
  have window : readState.wsize = 0 := by rw [readFrame]; exact codeWindow
  have noOutput : regs.out_ = regs.left := by rw [shape]; exact codeNoOutput
  have put : regs.put = z.next_out := by rw [shape]; exact codePut
  have left : regs.left = z.avail_out := by rw [shape]; exact codeLeft
  obtain ⟨rc0, after0, stream0, state, publicRun, final, finalAllocator, _freed, frame, _nextIn, availIn, _nextOut, availOut⟩ :=
    header_dispatch_wait_public initial allocator buffers nonnull inputValid noType step readGet window noOutput put left
  have same : (rc0, after0) = (rc, after) := Except.ok.inj (publicRun.symm.trans actual)
  cases same
  have returnedEq : returned = stream0 := Option.some.inj (get1.symm.trans final.good.live.hz)
  subst returned
  have empty : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [availOut, Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  have codes : state.codes = codeState.codes := by rw [frame, readFrame]; rfl
  have root : state.lenbits = codeState.lenbits := by rw [frame, readFrame]; rfl
  refine ⟨stream0, state, readUsed, final, finalAllocator, empty, availIn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, bound, readB, consumed, ?_, ?_⟩
  · rw [frame]; exact readMode
  · rw [frame]; exact window
  · rw [frame, readFrame]; rfl
  · rw [frame, readFrame]; rfl
  · rw [frame, readFrame]; rfl
  · rw [codes, root]; exact contents
  · rw [codes, root]; exact ordinary
  · rw [frame]; exact source
  · rw [frame]; exact trace

#print axioms phase_to_codelens_observed_seed

theorem lenlens_alphabet_prefix_fields
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
      state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ state.wsize = s.wsize ∧
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
  refine ⟨regs, used, state, usedBound, ?_, ?_, filled, rfl, rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
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
  · rw [inflate_LENLENS_eq, runX_bind, readRun]
    simp only []
    rw [runX_bind, zeroRun]
    simp only [setI_setI]
    rfl
  · intro future
    exact trace.alphabet (by change 19 ≤ readState.lens.size; rw [size]; decide) bound readCount readGood future



#print axioms lenlens_alphabet_prefix_fields
theorem lenlens_constructor_boundary_ready
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
        state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
        regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ state.wsize = s.wsize ∧
        BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
        runX (inflate_LENLENS c) l h =
          runX (inflate_CODELENS c) { regs with ret := 0 } (setI h zs state)) := by
  obtain ⟨regs, used, filled, usedBound, inv, filledWf, filledGood,
    codeCount, litCount, distCount, put, left, out, window, cut, alphabet⟩ :=
    lenlens_alphabet_prefix_fields hc hs wf bound haveBound good B progress enough
  obtain ⟨ret, next, root, work, codes, workSize, codeSize, _workFrame, _codeFrame,
    install, kinds, precise, semantic⟩ :=
    llInstall_code_length_contents_result (l := regs) hc (show (setI h zs filled).istates zs = some filled by simp) filledWf filledGood
  change (ret = 0 ↔ Acceptable .codeLength
    (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) at precise
  refine ⟨regs, used, filled, ret, next, root, work, codes, usedBound, inv, ?_, kinds, precise, alphabet, ?_⟩
  · simpa only [setI_setI] using install
  · intro success
    have contents := semantic success
    refine ⟨⟨filledWf.1, workSize, codeSize⟩, ?_, contents, ?_, codeCount, litCount, distCount, put, left, out, window, ?_, ?_⟩
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


#print axioms lenlens_constructor_boundary_ready

/-- Cumulative LENLENS provenance and independent format validity produce
all source facts consumed by the public phase-transition seed. An actual
CODELENS exhausted exit credits exactly its bytes and stored held suffix. -/
theorem lenlens_public_codelens_seed
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {received future alphabetRest rest : List Bool}
    {alphabet decoded : List Nat}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (observed : DataStep .inflate h after r flush rc input output used)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (mode : s.mode = LENLENS) (window : s.wsize = 0)
    (progress : LenlensProgress s s.hold s.bits received)
    (enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream (dispatchRegs z s) input).length)
    (formatRead : readCodeLenLens s.ncode.toNat ((received ++ bytesBits input) ++ future) = some (alphabet, alphabetRest))
    (acceptable : Acceptable .codeLength alphabet)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) [] alphabetRest rest decoded)
    (positive : 0 < s.nlen.toNat + s.ndist.toNat) :
    ∃ (codeRegs : IL) (codeState : InflateState) (headerUsed : Nat),
      headerUsed ≤ input.length ∧
      runX (inflate_dispatch ⟨some r, some (.tab zs), syncBuf h, flush⟩) (dispatchRegs z s) (syncAlloc h) =
        runX (inflate_CODELENS ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs (setI (syncAlloc h) zs codeState) ∧
      CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) [] (stream codeRegs (input.drop headerUsed) ++ future) rest decoded ∧
      ∀ (regs : IL) (readHeap : Heap) (readState : InflateState),
        runX (clRead ⟨some r, some (.tab zs), syncBuf h, flush⟩) codeRegs (setI (syncAlloc h) zs codeState) =
          .ok ((.error Ex.leave, regs), readHeap) →
        readHeap.istates zs = some readState → readState.mode = CODELENS →
        ∃ stream0 state readUsed,
          DefaultOriginState after r zs stream0 state ∧ DefAlloc stream0 ∧ output = [] ∧
          headerUsed + readUsed = used ∧ state.mode = CODELENS ∧ state.wsize = 0 ∧
          state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
          Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
          (∀ index, index < 2 ^ state.lenbits.toNat → ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
          Progress alphabet (s.nlen.toNat + s.ndist.toNat) []
            (natBits codeRegs.bits.toNat codeRegs.hold.toNat ++ bytesBits ((input.drop headerUsed).take readUsed)) state := by
  have observed0 := observed
  obtain ⟨z0, returned, get0, get1, _buffers, _header, bytes, usedEq, _outputBytes, _actual⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans initial.good.live.hz)
  subst z0
  have view := header_input_view_of_bytes (s := s) bytes initial.held
  have allocated := default_origin_syncAlloc initial
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have view0 : BitInv (syncAlloc h) (dispatchRegs z s) input := by
    refine ⟨view.have_eq, ?_, view.hold_lt⟩
    rcases view.next with empty | ⟨ref, array, off, pointer, get, bound, values⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref, array, off, pointer, (byte_view_syncAlloc initial.good.fresh get).1, bound, values⟩
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := initial.headerLengths mode
  obtain ⟨regs0, headerUsed, filled, ret, next, root, work, codes, headerBound, _inputB, _install, _kinds,
    successIff, readActual, ready⟩ :=
    lenlens_constructor_boundary_ready env.st env.hs initial.good.inv.wf ncode haveBound good view0 progress nlen ndist enough
  have actualRead := readActual (bytesBits (input.drop headerUsed) ++ future)
  have inputEq : ((received ++ bytesBits (input.take headerUsed)) ++ (bytesBits (input.drop headerUsed) ++ future)) =
      ((received ++ bytesBits input) ++ future) := by
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesBits (input.take headerUsed)) (bytesBits (input.drop headerUsed)) future,
      ← bytesBits_append, List.take_append_drop]
  rw [inputEq] at actualRead
  have same := Option.some.inj (actualRead.symm.trans formatRead)
  have alphabetEq := congrArg Prod.fst same
  have sourceEq := congrArg Prod.snd same
  dsimp only at alphabetEq sourceEq
  have success : ret = 0 := successIff.mpr (by rw [alphabetEq]; exact acceptable)
  obtain ⟨wf, inv, contents, empty, code, lit, dist, put, left, out, codeWindow, codeB, cut⟩ := ready success
  let codeState := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  let codeRegs := { regs0 with ret := 0 }
  have actualContents : Zlib.Inftrees.Proofs.CodeLengthContents codeState.codes 0 codeState.lenbits.toNat alphabet := by
    rw [alphabetEq] at contents
    exact contents
  have ordinary : ∀ index, index < 2 ^ codeState.lenbits.toNat → ∃ entry, codeState.codes[index]? = some entry ∧ entry.op = 0 := by
    obtain ⟨symbol, inside, nonzero⟩ := codeLens_positive_alphabet_nonzero parsed (by simpa using positive)
    have notEmpty : ¬ (∀ value ∈ alphabet, value = 0) := by
      intro zero
      apply nonzero
      apply zero
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
      exact List.getElem_mem inside
    rcases actualContents.layout with emptyRoot | ordinaryRoot
    · exact False.elim (notEmpty emptyRoot.2.1)
    · simpa only [Nat.zero_add] using ordinaryRoot
  have prefixCut : runX (inflate_dispatch c) (dispatchRegs z s) (syncAlloc h) =
      runX (inflate_CODELENS c) codeRegs (setI (syncAlloc h) zs codeState) := by
    rw [inflate_dispatch_LENLENS env _ mode]
    exact cut
  refine ⟨codeRegs, codeState, headerUsed, headerBound, prefixCut, ?_, ?_⟩
  · change CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) []
      ((natBits regs0.bits.toNat regs0.hold.toNat ++ bytesBits (input.drop headerUsed)) ++ future) rest decoded
    rw [List.append_assoc, sourceEq]
    exact parsed
  · intro regs readHeap readState readRun readGet readMode
    obtain ⟨stream0, state, readUsed, current, currentAllocator, noOutput, availIn, stateMode, stateWindow,
      finalCode, finalLit, finalDist, finalContents, finalOrdinary, readBound, readB, trace⟩ :=
      phase_to_codelens_observed_seed initial allocator observed0 nonnull inputValid (by rw [mode]; decide) prefixCut
        (by simpa using env.hz) (by rw [setI_istates_same]) wf rfl inv actualContents ordinary codeB empty (codeWindow.trans window)
        (by change regs0.out_ = regs0.left; rw [out, left]; rfl) put left readRun readGet readMode
    have returnedEq : returned = stream0 := Option.some.inj (get1.symm.trans current.good.live.hz)
    subst returned
    have actualUse : headerUsed + readUsed = used := by
      have before := view.have_eq
      have finalHave := readB.have_eq
      rw [usedEq, availIn]
      change z.avail_in.toNat = input.length at before
      simp only [List.length_drop] at finalHave readBound
      omega
    rw [lit, dist] at trace
    exact ⟨stream0, state, readUsed, current, currentAllocator, noOutput, actualUse, stateMode, stateWindow,
      finalCode.trans code, finalLit.trans lit, finalDist.trans dist, finalContents, finalOrdinary, trace⟩

#print axioms lenlens_public_codelens_seed

end Zlib.Inflate.Proofs.CumulativeBoundary
