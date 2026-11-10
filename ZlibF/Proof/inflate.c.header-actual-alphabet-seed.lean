import ZlibF.Proof.«inflate.c.header-count-read-source»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- An actual successful CODES installation, with its exact translated
prefix programs and causal alphabet-read observation. This contains no
completed CodeLens, Header, future validity or desired parser invariant. -/
structure AlphabetSeed (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (received : List Bool) where
  regs : IL
  used : Nat
  filled : InflateState
  next : CodePtr
  root : UInt32
  work : Array UInt16
  codes : Array Code
  state : InflateState
  written : state = {llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS}
  bound : used ≤ bs.length
  headerRun : runX (do xwhile (llCond c) (llBody c); xwhile (lzCond c) (lzBody c)) l h = .ok ((.ok (), regs), setI h zs filled)
  install : runX (llInstall c) regs (setI h zs filled) = .ok ((.ok 0, {regs with ret := 0}),
    setI h zs {llPre zs filled with next := next, lenbits := root, work := work, codes := codes})
  origin : DefaultOriginState (setI h zs state) r zs z state
  buffers : DispatchBuffers (setI h zs state) r {regs with ret := 0} (bs.drop used)
  literalCount : state.nlen = s.nlen
  distanceCount : state.ndist = s.ndist
  last : state.last = s.last
  read : ∀ tail, readCodeLenLens s.ncode.toNat ((received ++ bytesBits (bs.take used)) ++ tail) =
    some (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19, natBits regs.bits.toNat regs.hold.toNat ++ tail)
  valid : Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)
  empty : actualLengthPrefix state = []
  contents : Zlib.Inftrees.Proofs.CodeLengthContents state.codes 0 state.lenbits.toNat
    (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19)
  actual : runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) {regs with ret := 0} (setI h zs state)

/-- Construct the source parser seed from the actual count and alphabet
programs. A desired HeaderSourcePrefix is an output, never an event premise. -/
theorem AlphabetSeed.prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (event : AlphabetSeed c h r zs z s l bs received) (data : CountReadSource s received bs) :
    ∃ prefixData : HeaderSourcePrefix event.state {event.regs with ret := 0} (bs.drop event.used)
      (Zlib.Inftrees.Proofs.lensOf (fun k => (event.filled.lens.getD k 0).toNat) 19), prefixData.bodyInput = data.body :=
  data.alphabet_seed event.literalCount event.distanceCount event.read event.valid event.empty

/-- Unconditional actual alphabet completion: the constructor rejects or
supplies its real seed event. In particular no successful return or
acceptable alphabet is requested from the caller. -/
theorem actual_alphabet_seed
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (progress : LenlensProgress s l.hold l.bits received)
    (enough : 3 * (s.ncode.toNat - s.«have».toNat) ≤ (stream l bs).length) :
    (∃ (regs : IL) (after : Heap), runX (inflate_LENLENS c) l h = .ok ((.ok (), {regs with ret := -1}), after)) ∨
    Nonempty (AlphabetSeed c h r zs z s l bs received) := by
  obtain ⟨regs, used, filled, ret, next, root, work, codes, bound, headerRun, install, cut, kinds, precise, read, good⟩ :=
    lenlens_constructor_cases_source E origin buffers mode progress enough
  rcases kinds with success | rejected
  · obtain ⟨current, packet, _sizes, _wf, _frame, _ncode, lit, dist, last, _ptr, contents, empty,
      _cursor, _count, _put, _left, _out, _bits, _budget, actual⟩ := good success
    refine Or.inr ⟨⟨regs, used, filled, next, root, work, codes,
      {llPre zs filled with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS},
      rfl, bound, headerRun, ?_, current, packet, lit, dist, last, read, precise.mp success, empty, contents, actual⟩⟩
    simpa only [success] using install
  · obtain ⟨i, actual⟩ := rejected_codes_source E cut (by simpa only [rejected] using install)
    exact Or.inl ⟨regs, _, actual⟩

/-- An actual short alphabet read transports both the physical parser
progress and the cumulative count-read record. -/
theorem actual_alphabet_wait
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (progress : LenlensProgress s l.hold l.bits received) (data : CountReadSource s received bs)
    (short : (stream l bs).length < 3 * (s.ncode.toNat - s.«have».toNat)) :
    ∃ regs state used, used ≤ bs.length ∧
      runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
      DefaultOriginState (setI h zs state) r zs z state ∧ DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      LenlensProgress state regs.hold regs.bits (received ++ bytesBits (bs.take used)) ∧
      ∃ next : CountReadSource state (received ++ bytesBits (bs.take used)) (bs.drop used), next.body = data.body := by
  obtain ⟨regs, state, used, bound, actual, current, packet, _frame, _last, lit, dist, code, _mode, nextProgress, _rest⟩ :=
    LaterHeader.lenlens_short_source E origin buffers mode progress short
  exact ⟨regs, state, used, bound, actual, current, packet, nextProgress, data.wait_transport lit dist code⟩

#print axioms AlphabetSeed.prefix
#print axioms actual_alphabet_seed
#print axioms actual_alphabet_wait
end Zlib.Inflate.Proofs.ActualHeader
