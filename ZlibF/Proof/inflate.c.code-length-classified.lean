import ZlibF.Proof.«inflate.c.code-length-empty»
import ZlibF.Proof.«inflate.c.code-length-install»
import ZlibF.Proof.«inflate.c.code-length-loop-prefix»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- The actual constructor's content classification covers both root cases.
The empty-prefix premise is an internal representation fact: have = 0
establishes it, and the actual empty reader retains it. It is not a callee
contract. Normal ordinary completion has independent CodeLens meaning;
normal empty completion supplies only zero lengths for the later EOB check. -/
theorem clRead_contents_format {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (emptyPrefix : (∀ length ∈ alphabet, length = 0) →
      actualLengthPrefix s = List.replicate s.«have».toNat 0)
    (B : BitInv h l bs) :
    ∃ outcome regs after state used,
      runX (clRead c) l h = .ok ((outcome, regs), after) ∧ ClReadResultFull h r z zs s l bs outcome regs after ∧
      after.istates zs = some state ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      ((state.mode = CODELENS ∧ (∀ length ∈ alphabet, length = 0) ∧
        actualLengthPrefix state = List.replicate state.«have».toNat 0 ∧
        (outcome = .ok () → state.«have».toNat = s.nlen.toNat + s.ndist.toNat)) ∨
       ((state.mode ≠ BAD → ∃ consumed, stream l bs = consumed ++ stream regs (bs.drop used) ∧
          ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat)
            (actualLengthPrefix s) consumed (actualLengthPrefix state)) ∧
        (outcome = .ok () → state.mode ≠ BAD →
          CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
            (stream regs (bs.drop used)) (actualLengthPrefix state)))) := by
  rcases contents.layout with ⟨root, allZero, first, second⟩ | ordinary
  · have first' : s.codes[0]? = some (⟨64, 1, 0⟩ : Code) := first
    have second' : s.codes[1]? = some (⟨64, 1, 0⟩ : Code) := second
    obtain ⟨outcome, regs, after, state, used, run, getState, usedBound, inv, stateMode, zeros, count⟩ :=
      clRead_empty_root hc hs size mode stateInv root first' second' (emptyPrefix allZero) B
    obtain ⟨outcome2, regs2, after2, run2, full, _cursor⟩ :=
      clRead_run_full_cursor hr hc hz hs size mode stateInv B
    rw [run] at run2
    cases run2
    exact ⟨outcome, regs, after, state, used, run, full, getState, usedBound, inv,
      Or.inl ⟨stateMode, allZero, zeros, count⟩⟩
  · have ordinary' : ∀ index, index < 2 ^ s.lenbits.toNat →
        ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0 := by
      simpa only [Nat.zero_add] using ordinary
    obtain ⟨outcome, regs, after, state, used, run, full, getState, bound, inv, causal, parsed⟩ :=
      clRead_ordinary_trace_format hr hc hz hs size mode stateInv contents ordinary' B
    exact ⟨outcome, regs, after, state, used, run, full, getState, bound, inv, Or.inr ⟨causal, parsed⟩⟩

/-- The actual constructor resets have before entering CODELENS, so no
length-array initialization is needed to establish the empty-prefix fact. -/
theorem actualLengthPrefix_empty_for_alphabet {s : InflateState} (start : s.«have» = 0)
    (alphabet : List Nat) : (∀ length ∈ alphabet, length = 0) →
      actualLengthPrefix s = List.replicate s.«have».toNat 0 := by
  intro _
  simp [actualLengthPrefix, start, Zlib.Inftrees.Proofs.lensOf]


/-- The real LENLENS constructor and its stores establish the entire local
reading invariant, exact table contents and empty prefix at the source
continuation. No called-program contract is an incoming hypothesis. -/
theorem llTail_code_length_read_ready {c : Ctx} {l : IL} {h : Heap}
    {zs : Nat} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (wf : s.WellFormed) (lengths : Good3 s.lens 19)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30) :
    ∃ (ret : Int32) (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      runX (llInstall c) l h = .ok ((.ok ret, { l with ret := ret }),
        setI h zs { llPre zs s with next := next, lenbits := root, work := work, codes := codes }) ∧
      (ret = 0 →
        let state := { llPre zs s with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
        state.lens.size = 320 ∧ CodeLengthInvariant zs state ∧
        Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) 19) ∧
        actualLengthPrefix state = [] ∧
        runX (llTail c) l h = runX (inflate_CODELENS c) { l with ret := 0 } (setI h zs state)) := by
  obtain ⟨ret, next, root, work, codes, actual, continuation⟩ :=
    llTail_code_length_contents_continuation hc hs wf lengths
  refine ⟨ret, next, root, work, codes, actual, ?_⟩
  intro success
  obtain ⟨contents, run⟩ := continuation success
  dsimp only
  refine ⟨wf.1, ?_, contents, ?_, run⟩
  · intro _
    refine ⟨rfl, contents.safe, nlen, ndist, ?_, ?_⟩
    · simp
    · intro k inside
      change k < (0 : UInt32).toNat at inside
      simp at inside
  · simp [actualLengthPrefix, Zlib.Inftrees.Proofs.lensOf]

#print axioms llTail_code_length_read_ready

#print axioms clRead_contents_format
#print axioms actualLengthPrefix_empty_for_alphabet
end Zlib.Inflate.Proofs
