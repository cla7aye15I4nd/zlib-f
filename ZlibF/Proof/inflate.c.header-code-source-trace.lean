import ZlibF.Proof.«inflate.c.header-actual-alphabet-seed»
import ZlibF.Proof.«inflate.c.header-actual-accepted-packet»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Parser-relevant field observations, e.g. from the actual public leave
and caller edit. The held word remains governed by the separate credited
physical source ledger. -/
theorem HeaderSourcePrefix.resume
    {s state : InflateState} {l regs : IL} {bs input : List UInt8} {alphabet : List Nat}
    (data : HeaderSourcePrefix s l bs alphabet)
    (lit : state.nlen = s.nlen) (dist : state.ndist = s.ndist)
    (values : actualLengthPrefix state = actualLengthPrefix s) :
    ∃ word, data.bodyInput = word ++ stream l bs ∧
      ∃ next : HeaderSourcePrefix state regs input alphabet,
        next.bodyInput = word ++ stream regs input ∧ next.consumed = data.consumed := by
  obtain ⟨word, source, replay⟩ := data.replay
  obtain ⟨next, nextSource, consumed⟩ := replay regs input
  refine ⟨word, source, ⟨next.bodyInput, next.r1, next.r2, next.r3, next.codeInput, next.consumed,
    next.hlit, next.hdist, next.hclen, next.first, next.second, next.third, next.counts,
    ?_, ?_, next.alphabetRead, next.acceptable, next.source, ?_⟩, nextSource, consumed⟩
  · rw [lit]; exact next.literalCount
  · rw [dist]; exact next.distanceCount
  · rw [lit, dist, values]; exact next.trace

/-- A finite actual source-event trace. Its constructors record real
translated alphabet/read/leave/load executions and caller Rebuffer; none
accepts HeaderSourcePrefix, Header or future validity as an input. -/
inductive CodeSourceTrace (r : ZStreamRef) (zs : Nat) :
    Heap → ZStream → InflateState → IL → List UInt8 → List Nat → Prop where
  | seed {c h z s l bs received}
      (counts : CountReadSource s received bs)
      (event : AlphabetSeed c h r zs z s l bs received) :
      CodeSourceTrace r zs (setI h zs event.state) z event.state {event.regs with ret := 0}
        (bs.drop event.used) (Zlib.Inftrees.Proofs.lensOf (fun k => (event.filled.lens.getD k 0).toNat) 19)
  | read {c h z s l bs alphabet}
      (previous : CodeSourceTrace r zs h z s l bs alphabet)
      (event : CodeReadObservation c h r zs z s l bs alphabet)
      (mode : event.state.mode = CODELENS)
      (ordinary : ¬ ∀ length ∈ alphabet, length = 0) :
      CodeSourceTrace r zs event.heap event.streamZ event.state event.regs (bs.drop event.used) alphabet
  | resume {c h z s l bs alphabet publicHeap callerHeap publicState publicZ callerZ regs input rc}
      (previous : CodeSourceTrace r zs h z s l bs alphabet)
      (leave : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
      (publicGet : publicHeap.istates zs = some publicState)
      (publicStream : r.get publicHeap = some publicZ)
      (caller : Rebuffer publicHeap callerHeap r)
      (callerGet : callerHeap.istates zs = some publicState)
      (callerStream : r.get callerHeap = some callerZ)
      (loaded : runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap))
      (inputBytes : Bytes callerHeap callerZ.next_in callerZ.avail_in.toNat input)
      (lit : publicState.nlen = s.nlen) (dist : publicState.ndist = s.ndist)
      (values : actualLengthPrefix publicState = actualLengthPrefix s)
      (codes : publicState.codes = s.codes) (rootBits : publicState.lenbits = s.lenbits)
      (haveEq : publicState.«have» = s.«have») :
      CodeSourceTrace r zs callerHeap callerZ publicState regs input alphabet

/-- Induction on the source events produces the parser relation. It is
not passed to any trace constructor as a desired after-condition. -/
theorem CodeSourceTrace.prefix
    {r : ZStreamRef} {zs : Nat} {h : Heap} {z : ZStream} {s : InflateState} {l : IL}
    {bs : List UInt8} {alphabet : List Nat} (trace : CodeSourceTrace r zs h z s l bs alphabet) :
    Nonempty (HeaderSourcePrefix s l bs alphabet) := by
  induction trace with
  | seed counts event =>
    obtain ⟨data, _⟩ := event.prefix counts
    exact ⟨data⟩
  | read previous event mode ordinary ih =>
    obtain ⟨data⟩ := ih
    rcases data.advance event mode with empty | next
    · exact False.elim (ordinary empty.1)
    · obtain ⟨next, _⟩ := next
      exact ⟨next⟩
  | resume previous leave publicGet publicStream caller callerGet callerStream loaded inputBytes lit dist values codes rootBits haveEq ih =>
    obtain ⟨data⟩ := ih
    obtain ⟨_word, _source, next, _⟩ := data.resume lit dist values
    exact ⟨next⟩

/-- The accepted packet now consumes an actual finite source trace,
rather than a caller-supplied desired parser prefix. -/
theorem CodeSourceTrace.accepted_packet
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {alphabet : List Nat}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (mode : s.mode = CODELENS)
    (allocator : DefAlloc z) (credit : WrapperGlue.AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (incoming : l.bits.toNat ≤ 39)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (observation : CodeReadObservation c h r zs z s l bs alphabet)
    (normal : observation.outcome = .ok ()) (code : observation.state.mode = CODELENS)
    (ready : TailReady c observation.heap r zs observation.streamZ observation.state observation.regs (bs.drop observation.used)) :
    Nonempty (AcceptedPacket c h callHeap r zs z s l bs alphabet credited history) := by
  obtain ⟨data⟩ := trace.prefix
  exact accepted_packet_from_observations E origin mode allocator credit dictionary incoming main data observation normal code ready

#print axioms HeaderSourcePrefix.resume
#print axioms CodeSourceTrace.prefix
#print axioms CodeSourceTrace.accepted_packet
end Zlib.Inflate.Proofs.ActualHeader
