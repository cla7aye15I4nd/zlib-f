import ZlibF.Proof.«inflate.c.header-constructor-deterministic-source»
import ZlibF.Proof.«inflate.c.lenlens-code-length-entry»
namespace Zlib.Inflate.Proofs.LenlensOriginSource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.HeaderPhaseView
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

theorem lenlens_alphabet_prefix_packet_source
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
      LengthTableFrame s state ∧ regs.next = inputAdvance l.next used ∧ TcRegShape l regs ∧
      regs.bits.toNat ≤ max l.bits.toNat 10 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
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
  obtain ⟨outcome0, regs0, used0, readRun0, usedBound0, inv0, _remaining, regShape, _wait, complete, cursor, bits⟩ :=
    ll1_run_cursor hc hs wf.1 bound haveBound B
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
  have same : used0 = used := by
    have first := inv.have_eq
    have second := inv0.have_eq
    rw [List.length_drop] at first second
    omega
  subst used0
  have budget : regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
    have shorter : (stream regs (bs.drop used)).length ≤ (stream l bs).length := by
      rw [_remaining, List.length_drop]
      omega
    rw [tcStream_length inv0, tcStream_length B, List.length_drop] at shorter
    omega
  refine ⟨regs, used, state, usedBound, inv0, ?_, filled, rfl, rfl, rfl, rfl,
    ?_, cursor, regShape, bits, budget, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, wf.2.1, wf.2.2⟩
    change (lensZero readState.lens _ _).size = 320
    rw [lensZero_size]
    exact size
  · simp only [LengthTableFrame, state, lzSt, readState, llSt]
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




theorem llInstall_pointer_contents_result {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (lengths : Good3 s.lens 19) :
    ∃ (ret : Int32) (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 128) ∧
      (∀ index, 19 ≤ index → work[index]? = s.work[index]?) ∧
      (∀ index, 128 ≤ index → codes[index]? = s.codes[index]?) ∧
      runX (llInstall c) l h = .ok ((.ok ret, { l with ret := ret }),
        setI h zs { llPre zs s with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 ∨ ret = -1) ∧
      (ret = 0 ↔ Acceptable .codeLength (Zlib.Inftrees.Spec.lensList s.lens 0 19)) ∧
      (ret = 0 → Zlib.Inftrees.Proofs.CodeLengthContents codes 0 root.toNat
        (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) 19)) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (llPre zs s)).istates zs = some (llPre zs s) := by simp
  have lens : Space.get (setI h zs (llPre zs s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [llPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (llPre zs s)) (WRef.istate_work zs) = some s.work := by
    simpa [llPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (llPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [llPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (llPre zs s)) CODES
      (.istate_lens zs) 0 19 (.istate_codes zs) 0 7 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inl rfl, lens, work, codes, by simp, by simp,
      by simp; omega, by simp; omega,
      by simp [Zlib.Inftrees.Spec.capOf, CODES]; omega,
      (by intro k inside; have := lengths.all k (by simpa using inside); simpa using (by omega : (s.lens.getD k 0).toNat ≤ 15)),
      (by intro _; exact ⟨by decide, fun k inside => by simpa using lengths.all k (by simpa using inside), by decide⟩),
      (by intro impossible; cases impossible), (by intro impossible; cases impossible)⟩
  obtain ⟨result, after, run, frame, contents⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_establishes_code_length_contents pre
  obtain ⟨extentResult, extentHeap, extentRun, _extentFrame, tables⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  rw [run] at extentRun
  cases extentRun
  have pointerBounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by intro success; obtain ⟨_, _, _, _, _, extent, _⟩ := tables success; exact extent.2.1)
  obtain ⟨result0, after0, run0, rejected, accepted, noSpace⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_correct_ret (setI h zs (llPre zs s)) CODES
      (.istate_lens zs) 0 19 (.istate_codes zs) 0 7 (.istate_work zs) 0
      pre.la pre.wa pre.ca pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne
      pre.hla pre.hwa pre.hca pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [run] at run0
  cases run0
  obtain ⟨ret, next, root⟩ := result
  obtain ⟨work, codes, heap, workSize', codeSize', workFrame, codeFrame, casesResult⟩ := frame
  change work.size = s.work.size at workSize'
  change codes.size = s.codes.size at codeSize'
  have heapEq : after = setI h zs (llBadSt zs s work codes) := by
    rw [heap, put_work_codes stored]
    simp [setI_setI, llBadSt, llPre]
  change (ret = -1 ↔ ¬ Acceptable .codeLength (Zlib.Inftrees.Spec.lensList s.lens 0 19)) at rejected
  change (ret = 0 → Acceptable .codeLength (Zlib.Inftrees.Spec.lensList s.lens 0 19)) at accepted
  have kinds : ret = 0 ∨ ret = -1 := by
    rcases casesResult with ⟨zero, _⟩ | ⟨one | neg, _⟩
    · exact Or.inl zero
    · exact False.elim ((noSpace one).2 rfl)
    · exact Or.inr neg
  have precise : ret = 0 ↔ Acceptable .codeLength (Zlib.Inftrees.Spec.lensList s.lens 0 19) := by
    refine ⟨accepted, ?_⟩
    intro format
    rcases kinds with zero | neg
    · exact zero
    · exact False.elim ((rejected.mp neg) format)
  have actualPointer : ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 128 := by
    obtain ⟨used, bound, pointer⟩ := pointerBounds.1
    exact ⟨used, by simpa only [Nat.zero_add] using pointer,
      by simpa only [Zlib.Inftrees.Spec.capOf, CODES, ite_true] using bound⟩
  refine ⟨ret, next, root, work, codes, by omega, by omega, actualPointer,
    fun index lower => workFrame index (Or.inr (by simpa using lower)),
    fun index lower => codeFrame index (Or.inr (by simpa [Zlib.Inftrees.Spec.capOf, CODES] using lower)), ?_, kinds, precise, ?_⟩
  · unfold llInstall
    rw [hc]
    have call : inflate_table CODES (.ref (WRef.istate_lens zs) 0) 19
        (.ref (CodeRef.istate_codes zs) 0) 7 (.ref (WRef.istate_work zs) 0)
        (setI h zs (llPre zs s)) = .ok ((ret, next, root), after) := run
    simp [llPre] at call
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, lensP, workP, codesP,
      call, heapEq, runX_modify, runX_pure, llBadSt, llPre, setI_setI]
  · intro success
    obtain ⟨array, get, semantic⟩ := contents success
    have actual : Space.get after (CodeRef.istate_codes zs) = some codes := by
      rw [heapEq]
      simp [Space.get, setI, llBadSt, llPre]
    rw [actual] at get
    cases Option.some.inj get
    exact semantic




/-- The actual LENLENS header and CODES installation preserve initialized
Origin, buffers and live-register accounting at their real CODELENS cut.
Success is exposed as its actual constructor branch, never as a returned
invariant premise. The independent alphabet is supplied as a causal read. -/
theorem lenlens_constructor_origin_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (progress : LenlensProgress s l.hold l.bits received)
    (enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream l bs).length) :
    ∃ (regs : IL) (used : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      used ≤ bs.length ∧
      runX (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c)) l h = .ok ((.ok (), regs), setI h zs filled) ∧
      runX (llInstall c) regs (setI h zs filled) = .ok ((.ok ret, { regs with ret := ret }),
        setI h zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 ↔ Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) ∧
      (∀ future, readCodeLenLens s.ncode.toNat ((received ++ bytesBits (bs.take used)) ++ future) =
        some (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19, natBits regs.bits.toNat regs.hold.toNat ++ future)) ∧
      (ret = 0 →
        let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
        DefaultOriginState (setI h zs state) r zs z state ∧
        DispatchBuffers (setI h zs state) r { regs with ret := 0 } (bs.drop used) ∧
        ByteViewSizes h (setI h zs state) ∧ state.WellFormed ∧
        LengthTableFrame s state ∧ state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧ state.last = s.last ∧
        (∃ tableUsed, state.next = .ref (.istate_codes zs) tableUsed ∧ tableUsed ≤ 128) ∧
        Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat
          (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19) ∧ actualLengthPrefix state = [] ∧
        regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
        regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
        regs.bits.toNat ≤ max l.bits.toNat 10 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
        runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) { regs with ret := 0 } (setI h zs state)) := by
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := initial.headerLengths mode
  obtain ⟨regs, used, filled, bound, B, wf, filledGood, codeCount, litCount, distCount, last,
    filledFrame, cursor, shape, bits, budget, put, left, out, _window, headerRun, sourceCut, alphabetRead⟩ :=
    lenlens_alphabet_prefix_packet_source E.st E.hs initial.good.inv.wf ncode haveBound good buffers.bits progress enough
  obtain ⟨ret, next, root, work, codes, workSize, codeSize, pointer, _workFrame, _codeFrame,
    install, _kinds, precise, semantic⟩ :=
    llInstall_pointer_contents_result (l := regs) E.st (show (setI h zs filled).istates zs = some filled by simp) wf filledGood
  change (ret = 0 ↔ Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) at precise
  have actualInstall : runX (llInstall c) regs (setI h zs filled) =
      .ok ((.ok ret, { regs with ret := ret }), setI h zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) := by
    simpa only [setI_setI] using install
  refine ⟨regs, used, filled, ret, next, root, work, codes, bound, headerRun, actualInstall, precise, alphabetRead, ?_⟩
  intro success
  let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  have contents := semantic success
  have stateWf : state.WellFormed := ⟨wf.1, workSize, codeSize⟩
  have frame : LengthTableFrame s state := by
    unfold LengthTableFrame at filledFrame ⊢
    dsimp only [state, llPre]
    rw [filledFrame]
  obtain ⟨tableUsed, nextEq, tableBound⟩ := pointer
  have pointers : PtrInv zs state :=
    ⟨⟨tableUsed, nextEq, by omega⟩, Or.inl ⟨0, 0, rfl, rfl, by decide, by decide⟩⟩
  have codeInv : CodeLengthInvariant zs state := by
    intro _
    refine ⟨rfl, contents.safe, ?_, ?_, ?_, ?_⟩
    · change filled.nlen.toNat ≤ 286
      rw [litCount]; exact nlen
    · change filled.ndist.toNat ≤ 30
      rw [distCount]; exact ndist
    · simp only [state, UInt32.toNat_zero]; omega
    · intro k inside
      change k < (0 : UInt32).toNat at inside
      have zero : (0 : UInt32).toNat = 0 := rfl
      omega
  have count : regs.have_.toNat + used = l.have_.toNat := by
    rw [B.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have retB : BitInv h { regs with ret := 0 } (bs.drop used) := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨nextJ, packet, sizes⟩ := initial.toDefaultStateJ.toDefaultDecodeJ.length_table_packet buffers frame
    (stream := z) rfl stateWf pointers (Or.inr rfl) codeInv retB cursor count put left out
  rw [ZStreamRef.put_self E.hz] at nextJ packet sizes
  have config : DefaultConfigFrame s state := by rw [frame]; exact ⟨rfl, rfl, rfl, rfl⟩
  have nextState := initial.toDefaultStateJ.config_update nextJ config (initial.construction_format (Or.inr (Or.inl mode)))
  have origin : DefaultOriginState (setI h zs state) r zs z state :=
    ⟨nextState, by rw [frame]; exact initial.flagsOrigin, Or.inl rfl⟩
  have continuation : runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) { regs with ret := 0 } (setI h zs state) := by
    rw [sourceCut, llTail_install_eq, runX_bind, actualInstall, success]
    simp [E.st, runX_bind, runX_lift, wrI_eq, setI_setI, state]
  exact ⟨origin, packet, sizes, stateWf, frame, codeCount, litCount, distCount, last,
    ⟨tableUsed, nextEq, tableBound⟩, contents, by simp [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf],
    cursor, count, put, left, out, bits, budget, continuation⟩



#print axioms lenlens_alphabet_prefix_packet_source
#print axioms llInstall_pointer_contents_result
#print axioms lenlens_constructor_origin_source
end Zlib.Inflate.Proofs.LenlensOriginSource
