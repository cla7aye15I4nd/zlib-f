import ZlibF.Proof.«inflate.c.header-actual-source-progress»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The three already-read count words are fixed independently of a new
caller buffer. This replays only those real words before the retained
alphabet word and the newly bound input. -/
theorem CountReadSource.replay
    {s : InflateState} {received : List Bool} {bs : List UInt8}
    (data : CountReadSource s received bs) :
    ∃ word, data.body = word ++ received ++ bytesBits bs ∧
      ∀ (state : InflateState) (input : List UInt8), state.nlen = s.nlen → state.ndist = s.ndist → state.ncode = s.ncode →
        ∃ next : CountReadSource state received input, next.body = word ++ received ++ bytesBits input := by
  obtain ⟨w1, firstSource, firstReplay⟩ := ZlibF.Math.HeaderConsumedReplay.readBits_consumed_word data.first
  obtain ⟨w2, secondSource, secondReplay⟩ := ZlibF.Math.HeaderConsumedReplay.readBits_consumed_word data.second
  obtain ⟨w3, thirdSource, thirdReplay⟩ := ZlibF.Math.HeaderConsumedReplay.readBits_consumed_word data.third
  let word := w1 ++ w2 ++ w3
  refine ⟨word, ?_, ?_⟩
  · rw [firstSource, secondSource, thirdSource]
    simp only [word, List.append_assoc]
  · intro state input lit dist code
    let rest := received ++ bytesBits input
    refine ⟨⟨word ++ rest, w2 ++ w3 ++ rest, w3 ++ rest, data.hlit, data.hdist, data.hclen,
      ?_, ?_, ?_, data.counts, ?_, ?_, ?_⟩, ?_⟩
    · simpa only [word, List.append_assoc] using firstReplay (w2 ++ w3 ++ rest)
    · simpa only [List.append_assoc] using secondReplay (w3 ++ rest)
    · exact thirdReplay rest
    · rw [lit]; exact data.literalCount
    · rw [dist]; exact data.distanceCount
    · rw [code]; exact data.codeCount
    · simp only [rest, List.append_assoc]

/-- Resume a real LENLENS wait through public leave and actual caller
rebuffer. Scalar equalities are observations of the real public saved
state; LOAD and private-state/source preservation are derived here. -/
theorem CountReadSource.resume_credited
    {c : Ctx} {h publicHeap callerHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {s : InflateState} {l : IL} {bs input : List UInt8} {received : List Bool}
    {callerZ : ZStream} {rc : Int32} {log : DataLog} {committed : List Bool}
    (data : CountReadSource s received bs) (progress : LenlensProgress s l.hold l.bits received)
    (root : c.strm = some r) (stateRoot : c.st = some (.tab zs))
    (leave : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
    (source : CausalInput.AtPublic publicHeap r log committed) (owner : source.zs = zs)
    (lit : source.state.nlen = s.nlen) (dist : source.state.ndist = s.ndist) (code : source.state.ncode = s.ncode)
    (lens : source.state.lens = s.lens) (haveEq : source.state.«have» = s.«have»)
    (hold : source.state.hold = l.hold) (bits : source.state.bits = l.bits)
    (edit : Rebuffer publicHeap callerHeap r) (streamGet : r.get callerHeap = some callerZ)
    (inputBytes : Bytes callerHeap callerZ.next_in callerZ.avail_in.toNat input) :
    ∃ next : CausalInput.AtPublic callerHeap r log committed,
      next.zs = zs ∧ next.state = source.state ∧ next.z = callerZ ∧
      ∃ regs, runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) ∧
        LenlensProgress source.state regs.hold regs.bits received ∧
        ∃ word, data.body = word ++ received ++ bytesBits bs ∧
          ∃ nextCount : CountReadSource source.state received input,
            nextCount.body = word ++ received ++ bytesBits input := by
  obtain ⟨next, sameOwner, sameState, _streamFields⟩ := source.rebuffer_same edit
  have nextOwner : next.zs = zs := sameOwner.trans owner
  have nextZ : next.z = callerZ := Option.some.inj (next.good.live.hz.symm.trans streamGet)
  have callerGood : Good callerHeap r zs callerZ source.state := by
    have good := next.good
    rw [nextOwner, sameState, nextZ] at good
    exact good
  have env : Env c callerHeap r zs callerZ source.state := ⟨root, stateRoot, streamGet, callerGood.live.hs⟩
  let regs := {IL.init with put := callerZ.next_out, left := callerZ.avail_out, next := callerZ.next_in, have_ := callerZ.avail_in, hold := source.state.hold, bits := source.state.bits}
  have loaded : runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) := LOAD_run env IL.init
  obtain ⟨word, oldBody, replay⟩ := data.replay
  obtain ⟨nextCount, nextBody⟩ := replay source.state input lit dist code
  refine ⟨next, nextOwner, sameState, nextZ, regs, loaded, ?_, word, oldBody, nextCount, nextBody⟩
  change LenlensProgress source.state source.state.hold source.state.bits received
  rw [hold, bits]
  exact progress.of_fields lens haveEq

#print axioms CountReadSource.replay
#print axioms CountReadSource.resume_credited
end Zlib.Inflate.Proofs.ActualHeader
