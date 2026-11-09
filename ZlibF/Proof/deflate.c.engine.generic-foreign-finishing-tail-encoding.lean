import ZlibF.Proof.«deflate.c.engine.generic-foreign-trailer-fixed-header-valid»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-tail-phase»
import ZlibF.Proof.«deflate.c.engine.finishing-tail-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- After the completed raw output has drained, actual finishing-tail
execution either appends and publishes its one-time trailer or returns
STREAM_END for a wrapper already written. The encoding is retained on
the same returned heap, including short or zero trailer output. -/
theorem public_foreign_finishing_tail_encoding {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {accepted published : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (empty : z.avail_in = 0) (pending : d.pending = 0)
    (checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64)
    (encoding : FinishedEncoding h d accepted published) :
    ∃ rc after z' result written,
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 written.length ∧
      Bytes after z.next_out written.length written ∧ FinishingPhase result config ∧
      FinishedEncoding after result accepted (published ++ written) ∧ result.wrap = -1 ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧
      (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ published ++ written)) := by
  have originalEncoding := encoding
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  have length := caller_bytes_length data
  have tailNil : tailBytes = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa only [pending, UInt64.toNat_zero] using length)
  rcases meaning with ⟨wrap, rawMeaning⟩ | ⟨wrap, wrappedMeaning⟩
  · have rawValid : ZlibF.Spec.Deflate.Valid accepted published := by simpa only [tailNil, List.append_nil] using rawMeaning
    obtain ⟨otherD, pb, buf, trees⟩ := good.trees
    have stateEq : otherD = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst otherD
    obtain ⟨produced, after, z', result, written, remaining, trailerRun, goodA, buffersA,
        accountA, wrapA, bitsA, bytesA, pendingA, _trailerEq, checksumA, _allocA, _nextA, _frameA, validA, drainedA⟩ :=
      foreign_zlib_trailer_publish_fixed_header_valid good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits checksum rawValid
    have header := public_finishing_header_source good phase empty
    have actual := header.trans trailerRun
    obtain ⟨_otherProduced, _otherRc, other, otherZ, otherResult, otherRun, otherGood, _otherBuffers,
        _otherAccount, _allowed, otherPhase, _last, _emptyA, _ended⟩ :=
      public_foreign_finishing_tail_phase good buffers phase pointer empty pending
    have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans actual))).2
    rw [heaps] at otherGood
    have sameState : otherResult = result := Option.some.inj (otherGood.live.hs.symm.trans goodA.live.hs)
    rw [sameState] at otherPhase
    have writtenLength := caller_bytes_length bytesA
    refine ⟨if result.pending != 0 then Z_OK else Z_STREAM_END, after, z', result, written,
      actual, goodA, buffersA, ?_, ?_, otherPhase,
      ⟨bitsA, remaining, pendingA, Or.inr ⟨wrapA, by simpa only [List.append_assoc] using validA⟩⟩,
      wrapA, checksumA, ?_⟩
    · rw [writtenLength]; exact accountA
    · rw [writtenLength]; exact bytesA
    · intro ended
      have drained : result.pending = 0 := by
        by_cases drained : result.pending = 0
        · exact drained
        · simp [drained, show Z_OK ≠ Z_STREAM_END from by decide] at ended
      exact drainedA drained
  · have valid : ZlibF.Spec.Zlib.Valid accepted ([120,156] ++ published) := by
      simpa only [tailNil, List.append_nil] using wrappedMeaning
    have noBytes : Bytes h z.next_out 0 [] := by
      obtain ⟨foreign,get,bound,_⟩ := caller_foreign_output good buffers pointer
      exact Or.inr ⟨.dstate_depth owner, oo, foreign.depth, pointer, BRef.get_dstate_depth get, by omega, by simp⟩
    exact ⟨Z_STREAM_END, h, z, d, [], public_finished_headers good phase.status empty phase.lookahead wrap,
      good, buffers, stream_accounting_zero z, noBytes, phase,
      by simpa only [List.append_nil] using originalEncoding, wrap, checksum,
      fun _ => by simpa only [List.append_nil] using valid⟩


end Zlib.Deflate.Engine.Proofs
