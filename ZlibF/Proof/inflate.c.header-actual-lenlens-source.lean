import ZlibF.Proof.«inflate.c.header-actual-code-classifier»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.LenlensOriginSource
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The actual LENLENS header and CODES installation preserve initialized
Origin, buffers and live-register accounting at their real CODELENS cut.
Success is exposed as its actual constructor branch, never as a returned
invariant premise. The independent alphabet is supplied as a causal read. -/
theorem lenlens_constructor_cases_source
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
      runX (inflate_LENLENS c) l h = runX (llTail c) regs (setI h zs filled) ∧
      (ret = 0 ∨ ret = -1) ∧
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
    install, kinds, precise, semantic⟩ :=
    llInstall_pointer_contents_result (l := regs) E.st (show (setI h zs filled).istates zs = some filled by simp) wf filledGood
  change (ret = 0 ↔ Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) at precise
  have actualInstall : runX (llInstall c) regs (setI h zs filled) =
      .ok ((.ok ret, { regs with ret := ret }), setI h zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) := by
    simpa only [setI_setI] using install
  refine ⟨regs, used, filled, ret, next, root, work, codes, bound, headerRun, actualInstall, sourceCut, kinds, precise, alphabetRead, ?_⟩
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



#print axioms lenlens_constructor_cases_source
end Zlib.Inflate.Proofs.ActualHeader
