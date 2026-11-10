import ZlibF.Proof.«inflate.c.header-phase-table-history»
import ZlibF.Proof.«inflate.c.origin-fields-dispatch»
import ZlibF.Proof.«inflate.c.header-progress-table-start»
import ZlibF.Proof.«inflate.c.header-progress-complete»
import ZlibF.Proof.«inflate.c.code-length-classified»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

/-- A complete resumed LENLENS phase supplies the independent alphabet at
its actual constructor cut, for every future suffix. The prefix word is
advanced only by bytes consumed by this call. -/
theorem inflate_LENLENS_resumed_alphabet_prefix_counts
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
  obtain ⟨outcome0, regs0, used0, readRun0, usedBound0, inv0, _remaining, _shape, _wait, complete⟩ :=
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
  refine ⟨regs, used, state, usedBound, ?_, ?_, filled, rfl, rfl, rfl, ?_, ?_⟩
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
  · rw [inflate_LENLENS_eq, runX_bind, readRun]
    simp only []
    rw [runX_bind, zeroRun]
    simp only [setI_setI]
    rfl
  · intro future
    exact trace.alphabet (by change 19 ≤ readState.lens.size; rw [size]; decide) bound readCount readGood future


#print axioms inflate_LENLENS_resumed_alphabet_prefix_counts

/-- The actual completing LENLENS prefix feeds its independently parsed
alphabet to the real CODES constructor. Constructor success is an output
branch, not a caller-supplied table contract. -/
theorem inflate_LENLENS_resumed_contents_prefix
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    {bs : List UInt8} {received : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (bound : s.ncode.toNat ≤ 19)
    (haveBound : s.«have».toNat ≤ s.ncode.toNat)
    (good : Good3 s.lens s.«have».toNat) (B : BitInv h l bs)
    (progress : LenlensProgress s l.hold l.bits received)
    (enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream l bs).length) :
    ∃ (regs : IL) (used : Nat) (filled : InflateState) (ret : Int32)
      (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      filled.WellFormed ∧ Good3 filled.lens 19 ∧
      runX (llInstall c) regs (setI h zs filled) =
        .ok ((.ok ret, { regs with ret := ret }),
          setI h zs { llPre zs filled with next := next, lenbits := root, work := work, codes := codes }) ∧
      (∀ future, readCodeLenLens s.ncode.toNat
        ((received ++ bytesBits (bs.take used)) ++ future) = some
        (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19,
          natBits regs.bits.toNat regs.hold.toNat ++ future)) ∧
      (ret = 0 →
        let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
        Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat
          (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19) ∧
        BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
        actualLengthPrefix state = [] ∧
        runX (inflate_LENLENS c) l h =
          runX (inflate_CODELENS c) { regs with ret := 0 } (setI h zs state)) := by
  obtain ⟨regs, used, filled, usedBound, inv, filledWf, filledGood, cut, alphabet⟩ :=
    inflate_LENLENS_resumed_alphabet_prefix hc hs wf bound haveBound good B progress enough
  obtain ⟨ret, next, root, work, codes, install, continuation⟩ :=
    llTail_code_length_contents_continuation hc
      (show (setI h zs filled).istates zs = some filled by simp) filledWf filledGood
  refine ⟨regs, used, filled, ret, next, root, work, codes,
    usedBound, inv, filledWf, filledGood, ?_, alphabet, ?_⟩
  · simpa only [setI_setI] using install
  · intro success
    obtain ⟨contents, tail⟩ := continuation success
    refine ⟨contents, ?_, ?_, ?_⟩
    · have inv0 : BitInv h { regs with ret := 0 } (bs.drop used) :=
        ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      exact inv0.tc_setI zs _
    · simp [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf]
    · exact cut.trans (by simpa only [setI_setI] using tail)

#print axioms inflate_LENLENS_resumed_contents_prefix
/-- The actual constructor prefix installs the full empty/nonempty content
classification, not just the meaning of ordinary accepted queries. Every
constructor result is retained; success is a conclusion branch. -/
theorem llInstall_code_length_contents_result {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (lengths : Good3 s.lens 19) :
    ∃ (ret : Int32) (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
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
  refine ⟨ret, next, root, work, codes, by omega, by omega,
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


#print axioms llInstall_code_length_contents_result

/-- Completing the actual resumed reader establishes all local CODELENS
reader premises on the constructor's actual array, while retaining the
original count fields and independent header alphabet. -/
theorem inflate_LENLENS_resumed_constructor_ready
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
        state.lens.size = 320 ∧ CodeLengthInvariant zs state ∧
        Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat
          (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19) ∧
        actualLengthPrefix state = [] ∧
        state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
        BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
        runX (inflate_LENLENS c) l h =
          runX (inflate_CODELENS c) { regs with ret := 0 } (setI h zs state)) := by
  obtain ⟨regs, used, filled, usedBound, inv, filledWf, filledGood,
    codeCount, litCount, distCount, cut, alphabet⟩ :=
    inflate_LENLENS_resumed_alphabet_prefix_counts hc hs wf bound haveBound good B progress enough
  obtain ⟨ret, next, root, work, codes, install, ready⟩ :=
    llTail_code_length_read_ready (l := regs) hc
      (show (setI h zs filled).istates zs = some filled by simp) filledWf filledGood
      (by rw [litCount]; exact nlen) (by rw [distCount]; exact ndist)
  obtain ⟨ret0, next0, root0, work0, codes0, _workSize, _codeSize, _workFrame, _codeFrame,
    install0, kinds, precise, _contents0⟩ :=
    llInstall_code_length_contents_result (l := regs) hc
      (show (setI h zs filled).istates zs = some filled by simp) filledWf filledGood
  have sameRet : ret = ret0 := by
    have same := Except.ok.inj (install.symm.trans install0)
    exact Except.ok.inj (congrArg (fun pair => pair.1.1) same)
  rw [← sameRet] at kinds precise
  change (ret = 0 ↔ Acceptable .codeLength
    (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)) at precise
  refine ⟨regs, used, filled, ret, next, root, work, codes, usedBound, inv, ?_, kinds, precise, alphabet, ?_⟩
  · simpa only [setI_setI] using install
  · intro success
    obtain ⟨size, stateInv, contents, empty, tail⟩ := ready success
    refine ⟨size, stateInv, contents, empty, codeCount, litCount, distCount, ?_, ?_⟩
    · have inv0 : BitInv h { regs with ret := 0 } (bs.drop used) :=
        ⟨inv.have_eq, inv.next, inv.hold_lt⟩
      exact inv0.tc_setI zs _
    · exact cut.trans (by simpa only [setI_setI] using tail)

#print axioms inflate_LENLENS_resumed_constructor_ready
/-- The independent dynamic-body relation supplies constructor validity.
The four parser equalities identify the actual observed alphabet; no new
Acceptable premise is imposed on a public caller. -/
theorem dynamic_body_observed_alphabet_acceptable
    {dict history output : List UInt8} {input rest firstRest secondRest thirdRest alphabetRest : List Bool}
    {hlit hdist hclen : Nat} {alphabet : List Nat}
    (meaning : Body dict 2 history input rest output)
    (first : readBits 5 input = some (hlit, firstRest))
    (second : readBits 5 firstRest = some (hdist, secondRest))
    (third : readBits 4 secondRest = some (hclen, thirdRest))
    (actual : readCodeLenLens (hclen + 4) thirdRest = some (alphabet, alphabetRest)) :
    Acceptable .codeLength alphabet := by
  cases meaning with
  | dynamic first0 second0 third0 _counts actual0 acceptable _parsed _eob _lit _dist _symbols =>
    have e1 := Option.some.inj (first.symm.trans first0)
    cases e1
    have e2 := Option.some.inj (second.symm.trans second0)
    cases e2
    have e3 := Option.some.inj (third.symm.trans third0)
    cases e3
    have ea := Option.some.inj (actual.symm.trans actual0)
    cases ea
    exact acceptable

#print axioms dynamic_body_observed_alphabet_acceptable
/-- Any positive independent length parse reads a nonzero canonical
symbol. This rules out an empty code-length alphabet for a dynamic body. -/
theorem codeLens_positive_alphabet_nonzero
    {alphabet before lengths : List Nat} {total : Nat} {input rest : List Bool}
    (parsed : CodeLens alphabet total before input rest lengths) (more : before.length < total) :
    ∃ symbol, symbol < alphabet.length ∧ alphabet.getD symbol 0 ≠ 0 := by
  cases parsed with
  | done full => omega
  | @len _ _ _ _ symbol _ _ decoded _ _ =>
    exact ⟨symbol, (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).1,
      (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1⟩
  | rep16 _ decoded _ _ _ _ =>
    exact ⟨16, (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).1,
      (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1⟩
  | rep17 _ decoded _ _ _ =>
    exact ⟨17, (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).1,
      (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1⟩
  | rep18 _ decoded _ _ _ =>
    exact ⟨18, (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).1,
      (Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded).2.1⟩

/-- A genuine dynamic body requires a complete, nonempty code-length
alphabet. The single-symbol incomplete-tree exception is unavailable to
CODES; an empty constructor table cannot finish the positive CodeLens. -/
theorem dynamic_body_observed_alphabet_complete
    {dict history output : List UInt8} {input rest firstRest secondRest thirdRest alphabetRest : List Bool}
    {hlit hdist hclen : Nat} {alphabet : List Nat}
    (meaning : Body dict 2 history input rest output)
    (first : readBits 5 input = some (hlit, firstRest))
    (second : readBits 5 firstRest = some (hdist, secondRest))
    (third : readBits 4 secondRest = some (hclen, thirdRest))
    (actual : readCodeLenLens (hclen + 4) thirdRest = some (alphabet, alphabetRest)) :
    Acceptable .codeLength alphabet ∧ Complete alphabet ∧ ¬ (∀ value ∈ alphabet, value = 0) := by
  cases meaning with
  | dynamic first0 second0 third0 _counts actual0 acceptable parsed _eob _lit _dist _symbols =>
    have e1 := Option.some.inj (first.symm.trans first0)
    cases e1
    have e2 := Option.some.inj (second.symm.trans second0)
    cases e2
    have e3 := Option.some.inj (third.symm.trans third0)
    cases e3
    have ea := Option.some.inj (actual.symm.trans actual0)
    cases ea
    obtain ⟨symbol, inside, nonzero⟩ := codeLens_positive_alphabet_nonzero parsed (by simp; omega)
    have notEmpty : ¬ (∀ value ∈ alphabet, value = 0) := by
      intro zero
      apply nonzero
      apply zero
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
      exact List.getElem_mem inside
    refine ⟨acceptable, ?_, notEmpty⟩
    rcases acceptable.2.2 with full | empty | single
    · exact full
    · exact False.elim (notEmpty empty)
    · exact False.elim (single.1 rfl)

#print axioms codeLens_positive_alphabet_nonzero
#print axioms dynamic_body_observed_alphabet_complete
end Zlib.Inflate.Proofs


namespace Zlib.Inflate.Proofs.EntryPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The real non-final block-header path selects TABLE from the actual
three held header bits. Both independent reads and the exact remaining
packet are conclusions about the actual pull. No desired callee run is
supplied by the caller. -/
theorem dynamic_block_source_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (input : BitInv h l bs) (last : s.last = 0) :
    ∃ outcome pulled used,
      runX (NEEDBITS 3) l h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧
      (outcome = .ok () →
        let first := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
        let regs := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
        let state := { s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
        first.hold.toNat % 4 = 2 →
        runX (inflate_TYPEDO c) l h = .ok ((.ok (), regs), setI h zs state) ∧
        BitInv h regs (bs.drop used) ∧
        readBits 1 (stream l bs) = some (pulled.hold.toNat % 2, stream first (bs.drop used)) ∧
        readBits 2 (stream first (bs.drop used)) = some (2, stream regs (bs.drop used)) ∧
        stream regs (bs.drop used) = (stream l bs).drop 3 ∧
        regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat) := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, source, _count, shape,
    _bitBound, _noPull, full, _wait, _kinds, cursor⟩ := NEEDBITS_run_cursor input 3 (by decide)
  refine ⟨outcome, pulled, used, pull, bound, inv, ?_⟩
  intro normal
  dsimp only
  intro dynamic
  let first : IL := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
  let regs : IL := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
  let middle := { s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) }
  have full3 : 3 ≤ pulled.bits.toNat := full normal
  obtain ⟨firstInv, firstStream, firstBits⟩ := DROPBITS_inv inv 1 (by change 1 ≤ pulled.bits.toNat; omega) (by decide)
  change BitInv h first (bs.drop used) at firstInv
  change stream first (bs.drop used) = (stream pulled (bs.drop used)).drop 1 at firstStream
  change first.bits.toNat = pulled.bits.toNat - 1 at firstBits
  obtain ⟨regsInv, regsStream, _regsBits⟩ := DROPBITS_inv firstInv 2 (by change 2 ≤ first.bits.toNat; omega) (by decide)
  change BitInv h regs (bs.drop used) at regsInv
  change stream regs (bs.drop used) = (stream first (bs.drop used)).drop 2 at regsStream
  have middleEnv : Env c (setI h zs middle) r zs z middle :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using E.hz, setI_istates_same ..⟩
  have run := (inflate_TYPEDO_head E l pulled last (by rwa [normal] at pull)).trans
    (typedoTail_table middleEnv first dynamic)
  have count : pulled.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, input.have_eq, List.length_drop]
    omega
  have firstRead := readBits_held_stream pulled (bs.drop used) 1 (by omega)
  rw [← firstStream, source] at firstRead
  have secondRead := readBits_held_stream first (bs.drop used) 2 (by omega)
  rw [← regsStream, dynamic] at secondRead
  refine ⟨?_, regsInv, firstRead, secondRead, ?_, ?_, ?_⟩
  · simpa only [middle, first, regs, setI_setI] using run
  · rw [regsStream, firstStream, List.drop_drop, source]
  · exact cursor
  · exact count

#print axioms dynamic_block_source_cut

/-- The actual HEAD prefix reaches its literal zlib checks on a given
successful NEEDBITS run. The run is an operational source-cut observation. -/
theorem head_zlib_parsed_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l regs : IL)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (header : s.head = none)
    (pull : runX (NEEDBITS 16) l h = .ok ((.ok (), regs), h)) :
    runX (inflate_HEAD c) l h = runX (headDefaultCheck c s regs) regs h := by
  have nowrap : (s.wrap == 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  have nogzip : ((s.wrap &&& 2) != 0) = false := by rcases wrap with wrap | wrap <;> rw [wrap] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [nowrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, pull]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_ldS E]
  simp only [nogzip, bne_self_eq_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, header, beq_self_eq_true, Bool.not_true]
  unfold headDefaultCheck
  simp only [Bool.false_eq_true, ↓reduceIte]

#print axioms head_zlib_parsed_cut

/-- The real public dispatch selects TYPEDO once TYPE's stop flushes are excluded. -/
theorem dispatch_type_proceeds
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (flushing : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h := by
  rw [inflate_dispatch_block_type E l mode]
  by_cases selected : s.mode = TYPE
  · rw [if_pos selected, inflate_TYPE_go c l h flushing]
  · rw [if_neg selected]

/-- The selected dynamic source branch produces TABLE's strong origin
state and live packet on the same actually returned execution. -/
theorem dynamic_block_origin_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (flushing : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES)
    (last : s.last = 0) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome pulled used,
      runX (NEEDBITS 3) l h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧
      (outcome = .ok () →
        let first := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
        let regs := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
        let state := { s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
        let after := setI h zs state
        first.hold.toNat % 4 = 2 →
        runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
        DefaultOriginState after r zs z state ∧ DispatchBuffers after r regs (bs.drop used) ∧
        readBits 1 (stream l bs) = some (pulled.hold.toNat % 2, stream first (bs.drop used)) ∧
        readBits 2 (stream first (bs.drop used)) = some (2, stream regs (bs.drop used)) ∧
        stream regs (bs.drop used) = (stream l bs).drop 3 ∧ regs.bits.toNat ≤ 39) := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, accepted⟩ :=
    dynamic_block_source_cut E buffers.bits last
  refine ⟨outcome, pulled, used, pull, bound, inv, ?_⟩
  intro normal
  dsimp only
  intro dynamic
  obtain ⟨run, _bits, firstRead, secondRead, rest, _cursor, count⟩ := accepted normal dynamic
  have actual := (dispatch_type_proceeds E l mode flushing).trans run
  obtain ⟨exit, regs0, after0, stream0, state0, used0, made, bound0,
    run0, current, packet, _sizes, _next, count0, _put, _left, bits0, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank E initial buffers incoming
  rw [actual] at run0
  cases run0
  have sameUsed : used0 = used := by omega
  subst used0
  have expectedGet : r.get (setI h zs { s with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }) = some z := by
    simpa only [ZStreamRef.get_setI] using E.hz
  have sameStream : stream0 = z := Option.some.inj (current.good.live.hz.symm.trans expectedGet)
  subst stream0
  have sameState := current.good.live.hs
  rw [setI_istates_same] at sameState
  cases Option.some.inj sameState
  exact ⟨actual, current, packet, firstRead, secondRead, rest, bits0⟩

#print axioms dispatch_type_proceeds
#print axioms dynamic_block_origin_entry

/-- Starting with an empty held word, a complete default zlib header reads
exactly sixteen source bits. Accepted non-dictionary headers produce the
actual TYPE state, not an assumed post-initialization invariant. -/
theorem fresh_head_type_origin_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (freshBits : l.bits = 0) :
    ∃ outcome pulled used,
      runX (NEEDBITS 16) l h = .ok ((outcome, pulled), h) ∧ used ≤ bs.length ∧
      BitInv h pulled (bs.drop used) ∧
      (outcome = .ok () →
        headHeaderRejected s pulled = false → headMethodRejected pulled = false →
        (headWindowRegs pulled).len.toNat ≤ 15 → headDefaultMode pulled = TYPE →
        let regs := { headWindowRegs pulled with hold := 0, bits := 0 }
        let state := headDefaultState s pulled
        let after := setI (r.put h { z with adler := 1 }) zs state
        runX (inflate_dispatch c) l h = .ok ((.ok (), regs), after) ∧
        DefaultOriginState after r zs { z with adler := 1 } state ∧
        DispatchBuffers after r regs (bs.drop used) ∧
        state.mode = TYPE ∧ state.last = s.last ∧ regs.bits = 0 ∧ used = 2 ∧
        readBits 16 (stream l bs) = some (pulled.hold.toNat % 2 ^ 16, stream regs (bs.drop used))) := by
  obtain ⟨outcome, pulled, used, pull, bound, inv, source, count, shape,
    bitBound, _noPull, full, _wait, _kinds, _cursor⟩ := NEEDBITS_run_cursor buffers.bits 16 (by decide)
  refine ⟨outcome, pulled, used, pull, bound, inv, ?_⟩
  intro normal header method window noDictionary
  dsimp only
  have incoming : l.bits.toNat = 0 := by rw [freshBits]; rfl
  have enough : 16 ≤ pulled.bits.toNat := full normal
  have usedTwo : used = 2 := by
    rw [incoming] at count bitBound
    change pulled.bits.toNat ≤ max 0 23 at bitBound
    omega
  have bits16 : pulled.bits.toNat = 16 := by rw [incoming, usedTwo] at count; exact count
  have actual := (inflate_dispatch_HEAD E l mode).trans
    ((head_zlib_parsed_cut E l pulled wrap initial.header (by rwa [normal] at pull)).trans
      (headDefaultCheck_accept E pulled header method window initial.window))
  obtain ⟨exit, regs0, after0, stream0, state0, used0, made, bound0,
    run0, current, packet, _sizes, _next, count0, _put, _left, _bits0, _rank⟩ :=
    inflate_dispatch_default_origin_state_rank E initial buffers (by omega)
  rw [actual] at run0
  cases run0
  have inputCount : pulled.have_.toNat + used = l.have_.toNat := by
    rw [inv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  change pulled.have_.toNat + used0 = l.have_.toNat at count0
  have sameUsed : used0 = used := by omega
  subst used0
  have expectedGet : r.get (setI (r.put h { z with adler := 1 }) zs (headDefaultState s pulled)) =
      some { z with adler := 1 } := by
    rw [ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz _
  have sameStream : stream0 = { z with adler := 1 } :=
    Option.some.inj (current.good.live.hz.symm.trans expectedGet)
  subst stream0
  have sameState := current.good.live.hs
  rw [setI_istates_same] at sameState
  cases Option.some.inj sameState
  have rest : (stream pulled (bs.drop used)).drop 16 = bytesBits (bs.drop used) := by
    unfold stream
    rw [bits16, List.drop_append_of_le_length (by rw [natBits_length]; omega)]
    rw [List.drop_eq_nil_of_le (by rw [natBits_length]; omega)]
    rfl
  have read := readBits_held_stream pulled (bs.drop used) 16 enough
  rw [source] at rest read
  rw [rest] at read
  refine ⟨actual, current, packet, noDictionary, rfl, rfl, usedTwo, ?_⟩
  simpa only [stream, UInt32.toNat_zero, natBits, List.nil_append] using read

#print axioms fresh_head_type_origin_entry

/-- An accepted fresh zlib header and a dynamic block header form two
actual consecutive dispatch steps. The second state's input packet is
the original source after the independently read 16/1/2-bit fields. -/
theorem fresh_head_dynamic_table_entry
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (freshBits : l.bits = 0) (last : s.last = 0)
    (flushing : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    ∃ headOutcome headPulled headUsed,
      runX (NEEDBITS 16) l h = .ok ((headOutcome, headPulled), h) ∧ headUsed ≤ bs.length ∧
      BitInv h headPulled (bs.drop headUsed) ∧
      (headOutcome = .ok () →
        headHeaderRejected s headPulled = false → headMethodRejected headPulled = false →
        (headWindowRegs headPulled).len.toNat ≤ 15 → headDefaultMode headPulled = TYPE →
        let headRegs := { headWindowRegs headPulled with hold := 0, bits := 0 }
        let headState := headDefaultState s headPulled
        let headHeap := setI (r.put h { z with adler := 1 }) zs headState
        ∃ outcome pulled used,
          runX (inflate_dispatch c) l h = .ok ((.ok (), headRegs), headHeap) ∧
          DefaultOriginState headHeap r zs { z with adler := 1 } headState ∧
          runX (NEEDBITS 3) headRegs headHeap = .ok ((outcome, pulled), headHeap) ∧
          used ≤ (bs.drop headUsed).length ∧ BitInv headHeap pulled ((bs.drop headUsed).drop used) ∧
          (outcome = .ok () →
            let first := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
            let regs := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
            let state := { headState with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
            let after := setI headHeap zs state
            first.hold.toNat % 4 = 2 →
            runX (inflate_dispatch c) headRegs headHeap = .ok ((.ok (), regs), after) ∧
            DefaultOriginState after r zs { z with adler := 1 } state ∧
            DispatchBuffers after r regs (bs.drop (headUsed + used)) ∧
            readBits 16 (stream l bs) = some (headPulled.hold.toNat % 2 ^ 16, stream headRegs (bs.drop headUsed)) ∧
            readBits 1 (stream headRegs (bs.drop headUsed)) =
              some (pulled.hold.toNat % 2, stream first ((bs.drop headUsed).drop used)) ∧
            readBits 2 (stream first ((bs.drop headUsed).drop used)) =
              some (2, stream regs ((bs.drop headUsed).drop used)) ∧
            regs.bits.toNat ≤ 39)) := by
  obtain ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, accepted⟩ :=
    fresh_head_type_origin_entry E initial buffers mode wrap freshBits
  refine ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, ?_⟩
  intro normal header method window noDictionary
  dsimp only
  obtain ⟨headRun, current, packet, currentMode, currentLast, currentBits, _headUsed, headerRead⟩ :=
    accepted normal header method window noDictionary
  have env : Env c (setI (r.put h { z with adler := 1 }) zs (headDefaultState s headPulled))
      r zs { z with adler := 1 } (headDefaultState s headPulled) :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨outcome, pulled, used, pull, bound, inv, block⟩ :=
    dynamic_block_origin_entry env current packet (Or.inl currentMode) flushing
      (currentLast.trans last) (by rw [currentBits]; decide)
  refine ⟨outcome, pulled, used, headRun, current, pull, bound, inv, ?_⟩
  intro normalBlock dynamic
  obtain ⟨blockRun, final, finalPacket, firstRead, secondRead, _rest, bits⟩ := block normalBlock dynamic
  refine ⟨blockRun, final, ?_, headerRead, firstRead, secondRead, bits⟩
  simpa only [List.drop_drop] using finalPacket

#print axioms fresh_head_dynamic_table_entry

/-- Actual successful default initialization writes the source entry
fields, including last zero, which the public initial postcondition does
not separately project. -/
theorem default_init_entry_fields {h after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (allocation : h.allocOk h.nalloc = true)
    (run : C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after))
    {z : ZStream} {s : InflateState} (good : Good after r h.nextBlk z s) :
    s.mode = HEAD ∧ s.last = 0 ∧ s.hold = 0 ∧ s.bits = 0 ∧ s.wrap = 5 := by
  obtain ⟨fresh, _, _, validVersion, before, get, allocators, _⟩ := domain
  obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have expected : C.run (inflateInit_ (some r) version 112) h =
      .ok (Z_OK, initOkHeap h r before 5 15) := by
    change inflateInit2_ (some r) 15 version 112 h = _
    exact inflateInit2_success get fresh allocation allocators.1 allocators.2 nonnull first (by decide +kernel)
  have heapEq : after = initOkHeap h r before 5 15 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans expected))
  have stateEq : s = resetKeepState h.nextBlk (resetPre (reset2Pre 5 15 (initState r))) := by
    apply Option.some.inj
    rw [← good.live.hs, heapEq]
    simp [initOkHeap]
  rw [stateEq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Actual init and caller buffer replacement establish the fresh HEAD
source premises. Neither the initialized invariant nor the input view is
assumed as a callee contract. -/
theorem default_initialized_rebuffer_entry
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ initialized z s,
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, initialized) ∧
      DefaultOriginState initialized r h.nextBlk z s ∧ DefAlloc z ∧
      StreamReachable .inflate initialized r ∧
      s.mode = HEAD ∧ s.last = 0 ∧ s.hold = 0 ∧ s.bits = 0 ∧ s.wrap = 5 ∧
      ∀ incoming, Rebuffer initialized incoming r → ZlibF.PlatformMemory.ByteObjectsFit incoming →
        ∃ stream0, DefaultOriginState incoming r h.nextBlk stream0 s ∧ DefAlloc stream0 ∧
          (dispatchRegs stream0 s).bits = 0 ∧
          ∀ bs, Bytes incoming stream0.next_in stream0.avail_in.toNat bs →
            BitInv incoming (dispatchRegs stream0 s) bs := by
  obtain ⟨initialized, z, s, run, initial, allocator, reachable⟩ :=
    inflate_default_origin_initial h r version domain platform allocation
  obtain ⟨head, last, held, bits, wrap⟩ := default_init_entry_fields domain allocation run initial.good
  refine ⟨initialized, z, s, run, initial, allocator, reachable, head, last, held, bits, wrap, ?_⟩
  intro incoming edit nextPlatform
  obtain ⟨stream0, current⟩ := rebuffer_default_origin initial edit nextPlatform
  obtain ⟨otherStream, fields, good⟩ := rebuffer_inflate_good initial.good edit
  have same : otherStream = stream0 := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
  subst otherStream
  refine ⟨stream0, current, ?_, bits, ?_⟩
  · rw [fields]
    exact allocator
  · intro bs input
    exact header_input_view_of_bytes (s := s) input current.held

#print axioms default_init_entry_fields
#print axioms default_initialized_rebuffer_entry


end Zlib.Inflate.Proofs.EntryPath

namespace Zlib.Inflate.Proofs.ConstructorEntry
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs
set_option autoImplicit false

theorem readBits_source_size {n value : Nat} {input rest : List Bool}
    (read : readBits n input = some (value, rest)) : input.length = n + rest.length := by
  have word := (ZlibF.Math.CodeLengthPrefix.read_word read).2
  rw [word, List.length_append, bitsOfNat_length]

theorem readNats_source_size {width count : Nat} {input rest : List Bool} {values : List Nat}
    (read : readNats width count input = some (values, rest)) :
    input.length = width * count + rest.length := by
  induction count generalizing input values rest with
  | zero =>
    simp only [readNats] at read
    cases read
    simp
  | succ count ih =>
    cases first : readBits width input with
    | none => simp [readNats, first] at read
    | some pair =>
      obtain ⟨value, middle⟩ := pair
      cases tail : readNats width count middle with
      | none => simp [readNats, first, tail] at read
      | some pair =>
        obtain ⟨suffix, final⟩ := pair
        simp only [readNats, first, tail] at read
        cases read
        have one := readBits_source_size first
        have more := ih tail
        simp only [Nat.mul_succ]
        omega

theorem readCodeLenLens_source_size {count : Nat} {input rest : List Bool} {alphabet : List Nat}
    (read : readCodeLenLens count input = some (alphabet, rest)) :
    input.length = 3 * count + rest.length := by
  cases parsed : readNats 3 count input with
  | none => simp [readCodeLenLens, parsed] at read
  | some pair =>
    obtain ⟨values, remaining⟩ := pair
    simp only [readCodeLenLens, parsed] at read
    cases read
    exact readNats_source_size parsed

/-- Independent dynamic validity exposes each source read and its code
alphabet condition; none of these is a translated-callee hypothesis. -/
theorem dynamic_body_header_fields
    {dict history output : List UInt8} {input rest : List Bool}
    (meaning : Body dict 2 history input rest output) :
    ∃ hlit hdist hclen firstRest secondRest thirdRest alphabet alphabetRest,
      readBits 5 input = some (hlit, firstRest) ∧
      readBits 5 firstRest = some (hdist, secondRest) ∧
      readBits 4 secondRest = some (hclen, thirdRest) ∧ DynamicCountsOK hlit hdist ∧
      readCodeLenLens (hclen + 4) thirdRest = some (alphabet, alphabetRest) ∧
      Acceptable .codeLength alphabet := by
  cases meaning with
  | dynamic first second third counts read acceptable _ _ _ _ _ =>
    exact ⟨_, _, _, _, _, _, _, _, first, second, third, counts, read, acceptable⟩

#print axioms readBits_source_size
#print axioms readNats_source_size
#print axioms readCodeLenLens_source_size
#print axioms dynamic_body_header_fields
/-- Full independent dynamic input makes the real TABLE/complete LENLENS
and CODES path reach CODELENS with classified contents. The caller gives
no constructor-success or extra Acceptable assumption. Local registers
are passed through unchanged source continuations, without reloading. -/
theorem table_valid_body_codelens_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {dict history output : List UInt8} {rest : List Bool}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE)
    (meaning : Body dict 2 history (stream l bs) rest output) :
    ∃ (regs : IL) (state : InflateState) (used : Nat) (alphabet : List Nat)
      (hlit hdist hclen : Nat) (firstRest secondRest thirdRest : List Bool),
      used ≤ bs.length ∧
      runX (inflate_TABLE c) l h = runX (inflate_CODELENS c) regs (setI h zs state) ∧
      BitInv (setI h zs state) regs (bs.drop used) ∧
      state.mode = CODELENS ∧ state.lens.size = 320 ∧ CodeLengthInvariant zs state ∧
      Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
      actualLengthPrefix state = [] ∧
      (∀ index, index < 2 ^ state.lenbits.toNat →
        ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
      readBits 5 (stream l bs) = some (hlit, firstRest) ∧
      readBits 5 firstRest = some (hdist, secondRest) ∧
      readBits 4 secondRest = some (hclen, thirdRest) ∧
      readCodeLenLens (hclen + 4) thirdRest = some (alphabet, stream regs (bs.drop used)) ∧
      state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4 := by
  obtain ⟨hlit, hdist, hclen, firstRest, secondRest, thirdRest, formatAlphabet, alphabetRest,
    first, second, third, countBounds, formatRead, _formatAcceptable⟩ := dynamic_body_header_fields meaning
  have len1 := readBits_source_size first
  have len2 := readBits_source_size second
  have len3 := readBits_source_size third
  have inputEnough : 14 ≤ (stream l bs).length := by omega
  obtain ⟨outcome, pulled, tableUsed, pull, tableBound, tableInv, accepted⟩ :=
    inflate_TABLE_header_phase_start E initial buffers mode
  obtain ⟨outcome0, pulled0, used0, pull0, bound0, inv0, source,
    _bitCount, _shape, _bitBound, _noPull, full, waiting, kinds, _cursor⟩ :=
    NEEDBITS_run_cursor buffers.bits 14 (by decide)
  rw [pull] at pull0
  cases pull0
  have sameUse : used0 = tableUsed := by
    have one := inv0.have_eq
    have two := tableInv.have_eq
    rw [List.length_drop] at one two
    omega
  subst used0
  have normal : outcome = .ok () := by
    rcases kinds with normal | leaves
    · exact normal
    · obtain ⟨usedAll, _empty, small⟩ := waiting leaves
      have length := congrArg List.length source
      rw [tcStream_length inv0, usedAll, List.drop_length, List.length_nil,
        Nat.mul_zero, Nat.add_zero] at length
      change pulled.bits.toNat < 14 at small
      omega
  obtain ⟨actualLit, actualDist, actualCode, actualFirst, actualSecond,
    actualRead1, actualRead2, actualRead3, litCount, distCount, codeCount⟩ :=
    tableCounts_read_fields s tableInv (full normal)
  rw [source] at actualRead1
  have eq1 := Option.some.inj (actualRead1.symm.trans first)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq1
  have eq2 := Option.some.inj (actualRead2.symm.trans second)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq2
  have eq3 := Option.some.inj (actualRead3.symm.trans third)
  obtain ⟨rfl, restEq⟩ := Prod.mk.inj eq3
  have valid : ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) := by
    intro invalid
    rcases invalid with lit | dist
    · have over := UInt32.lt_iff_toNat_lt.mp lit
      change 286 < (tableCounts s pulled.hold).nlen.toNat at over
      rw [litCount] at over
      have allowed := countBounds.1
      omega
    · have over := UInt32.lt_iff_toNat_lt.mp dist
      change 30 < (tableCounts s pulled.hold).ndist.toNat at over
      rw [distCount] at over
      have allowed := countBounds.2
      omega
  obtain ⟨phase, packet, seed, _fields, tableCut⟩ := accepted normal valid
  let startState := { tableCounts s pulled.hold with «have» := 0, mode := LENLENS }
  have sourceRead : readCodeLenLens (actualCode + 4)
      (stream (tableRegs pulled) (bs.drop tableUsed)) = some (formatAlphabet, alphabetRest) := by
    rw [restEq]
    exact formatRead
  have size := readCodeLenLens_source_size sourceRead
  have enough : 3 * (startState.ncode.toNat - startState.«have».toNat) ≤
      (stream (tableRegs pulled) (bs.drop tableUsed)).length := by
    change 3 * ((tableCounts s pulled.hold).ncode.toNat - (0 : UInt32).toNat) ≤ _
    rw [codeCount]
    omega
  obtain ⟨ncode, haveBound, nlen, ndist, good⟩ := phase.headerLengths rfl
  obtain ⟨regs, lensUsed, filled, ret, next, root, work, codes, lensBound, inputInv,
    _install, _kinds, resultValid, alphabetRead, ready⟩ :=
    inflate_LENLENS_resumed_constructor_ready E.st phase.good.live.hs
      phase.good.inv.wf ncode haveBound good packet.bits seed nlen ndist enough
  have parsed := alphabetRead (bytesBits ((bs.drop tableUsed).drop lensUsed))
  have consumedWord :
      (natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++
        bytesBits ((bs.drop tableUsed).take lensUsed)) ++ bytesBits ((bs.drop tableUsed).drop lensUsed) =
      stream (tableRegs pulled) (bs.drop tableUsed) := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    rfl
  rw [consumedWord] at parsed
  change readCodeLenLens (tableCounts s pulled.hold).ncode.toNat _ = _ at parsed
  rw [codeCount] at parsed
  have actualAcceptable := dynamic_body_observed_alphabet_acceptable meaning first second third
    (by rw [← restEq]; exact parsed)
  have success : ret = 0 := resultValid.mpr actualAcceptable
  obtain ⟨lensSize, codeInv, contents, emptyPrefix, finalCode, finalLit, finalDist,
    finalInv, continuation⟩ := ready success
  let state := { llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
  have noEmpty := (dynamic_body_observed_alphabet_complete meaning first second third
    (by rw [← restEq]; exact parsed)).2.2
  have ordinary : ∀ index, index < 2 ^ state.lenbits.toNat →
      ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0 := by
    rcases contents.layout with empty | ordinary
    · exact False.elim (noEmpty empty.2.1)
    · simpa only [Nat.zero_add] using ordinary
  refine ⟨{ regs with ret := 0 }, state, tableUsed + lensUsed, _, actualLit, actualDist, actualCode,
    actualFirst, actualSecond, thirdRest, ?_, ?_, ?_, rfl, lensSize, codeInv, contents,
    emptyPrefix, ordinary, first, second, third, ?_, ?_, ?_, ?_⟩
  · rw [List.length_drop] at lensBound
    omega
  · rw [tableCut, continuation]
    simp only [setI_setI, state]
  · simpa only [setI_setI, List.drop_drop] using finalInv
  · rw [← restEq]
    simpa only [stream, List.drop_drop] using parsed
  · rw [finalLit]
    exact litCount
  · rw [finalDist]
    exact distCount
  · rw [finalCode]
    exact codeCount

#print axioms table_valid_body_codelens_cut
/-- Fresh HEAD, TYPE and the complete TABLE constructor use consecutive
live source states in the same context. The complete independent Body
supplies all alphabet/count acceptance; no TABLE reload or constructor
success premise is introduced. This is a switch-prefix source cut. -/
theorem fresh_head_dynamic_constructor_chain
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD)
    (wrap : s.wrap = 1 ∨ s.wrap = 5) (freshBits : l.bits = 0) (last : s.last = 0)
    (flushing : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES) :
    ∃ headOutcome headPulled headUsed,
      runX (NEEDBITS 16) l h = .ok ((headOutcome, headPulled), h) ∧ headUsed ≤ bs.length ∧
      BitInv h headPulled (bs.drop headUsed) ∧
      (headOutcome = .ok () →
        headHeaderRejected s headPulled = false → headMethodRejected headPulled = false →
        (headWindowRegs headPulled).len.toNat ≤ 15 → headDefaultMode headPulled = TYPE →
        let headRegs := { headWindowRegs headPulled with hold := 0, bits := 0 }
        let headState := headDefaultState s headPulled
        let headHeap := setI (r.put h { z with adler := 1 }) zs headState
        ∃ outcome pulled used,
          runX (inflate_dispatch c) l h = .ok ((.ok (), headRegs), headHeap) ∧
          DefaultOriginState headHeap r zs { z with adler := 1 } headState ∧
          runX (NEEDBITS 3) headRegs headHeap = .ok ((outcome, pulled), headHeap) ∧
          used ≤ (bs.drop headUsed).length ∧ BitInv headHeap pulled ((bs.drop headUsed).drop used) ∧
          (outcome = .ok () →
            let first := { pulled with hold := pulled.hold >>> 1, bits := pulled.bits - 1 }
            let dynamicRegs := { first with hold := first.hold >>> 2, bits := first.bits - 2 }
            let dynamicState := { headState with last := u2i (pulled.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)), mode := TABLE }
            let dynamicHeap := setI headHeap zs dynamicState
            let remaining := bs.drop (headUsed + used)
            first.hold.toNat % 4 = 2 →
            ∀ dict history output rest,
              Body dict 2 history (stream dynamicRegs remaining) rest output →
              ∃ (regs : IL) (state : InflateState) (consumed : Nat) (alphabet : List Nat)
                (hlit hdist hclen : Nat) (firstRest secondRest thirdRest : List Bool),
                consumed ≤ remaining.length ∧
                runX (inflate_dispatch c) headRegs headHeap = .ok ((.ok (), dynamicRegs), dynamicHeap) ∧
                runX (inflate_dispatch c) dynamicRegs dynamicHeap =
                  runX (inflate_CODELENS c) regs (setI dynamicHeap zs state) ∧
                BitInv (setI dynamicHeap zs state) regs (remaining.drop consumed) ∧
                state.mode = CODELENS ∧ state.lens.size = 320 ∧ CodeLengthInvariant zs state ∧
                Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat alphabet ∧
                actualLengthPrefix state = [] ∧
                (∀ index, index < 2 ^ state.lenbits.toNat →
                  ∃ entry, state.codes[index]? = some entry ∧ entry.op = 0) ∧
                readBits 16 (stream l bs) =
                  some (headPulled.hold.toNat % 2 ^ 16, stream headRegs (bs.drop headUsed)) ∧
                readBits 1 (stream headRegs (bs.drop headUsed)) =
                  some (pulled.hold.toNat % 2, stream first ((bs.drop headUsed).drop used)) ∧
                readBits 2 (stream first ((bs.drop headUsed).drop used)) =
                  some (2, stream dynamicRegs ((bs.drop headUsed).drop used)) ∧
                readBits 5 (stream dynamicRegs remaining) = some (hlit, firstRest) ∧
                readBits 5 firstRest = some (hdist, secondRest) ∧
                readBits 4 secondRest = some (hclen, thirdRest) ∧
                readCodeLenLens (hclen + 4) thirdRest = some (alphabet, stream regs (remaining.drop consumed)) ∧
                state.nlen.toNat = hlit + 257 ∧ state.ndist.toNat = hdist + 1 ∧ state.ncode.toNat = hclen + 4)) := by
  obtain ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, headAccepted⟩ :=
    EntryPath.fresh_head_dynamic_table_entry E initial buffers mode wrap freshBits last flushing
  refine ⟨headOutcome, headPulled, headUsed, headPull, headBound, headInv, ?_⟩
  intro headNormal header method window noDictionary
  dsimp only
  obtain ⟨outcome, pulled, used, headRun, headJ, blockPull, blockBound, blockInv, blockAccepted⟩ :=
    headAccepted headNormal header method window noDictionary
  refine ⟨outcome, pulled, used, headRun, headJ, blockPull, blockBound, blockInv, ?_⟩
  intro blockNormal dynamic dict history output rest meaning
  obtain ⟨blockRun, tableJ, tablePacket, headRead, lastRead, typeRead, _bits⟩ :=
    blockAccepted blockNormal dynamic
  have tableEnv : Env c _ r zs { z with adler := 1 } _ :=
    ⟨E.strm, E.st, tableJ.good.live.hz, tableJ.good.live.hs⟩
  obtain ⟨regs, state, consumed, alphabet, hlit, hdist, hclen, firstRest, secondRest, thirdRest,
    consumedBound, tableCut, inv, readyMode, size, codeInv, contents, empty,
    ordinary, read1, read2, read3, readAlphabet, nlen, ndist, ncode⟩ :=
    table_valid_body_codelens_cut tableEnv tableJ tablePacket rfl meaning
  refine ⟨regs, state, consumed, alphabet, hlit, hdist, hclen, firstRest, secondRest, thirdRest,
    consumedBound, blockRun, ?_, inv, readyMode, size, codeInv, contents, empty, ordinary,
    headRead, lastRead, typeRead, read1, read2, read3, readAlphabet, nlen, ndist, ncode⟩
  rw [inflate_dispatch_TABLE tableEnv _ rfl]
  exact tableCut

#print axioms fresh_head_dynamic_constructor_chain
end Zlib.Inflate.Proofs.ConstructorEntry
