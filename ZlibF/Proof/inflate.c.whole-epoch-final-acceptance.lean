import ZlibF.Proof.«inflate.c.whole-epoch-source-spine»
import ZlibF.Proof.«inflate.c.protocol-end-mode-observer»
import ZlibF.Spec.Api.InflateAccepted

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A finished source certificate gives the independent configured-window
meaning. The original RFC relation is not substituted for acceptance. -/
theorem Finished.decodes_with_default_window {log : DataLog} (finished : Finished log) :
    Zlib.DecodesWithWindow 15 log.dictionary log.input log.output := by
  let wrapper := finished.wrapper
  by_cases present : wrapper.flg.toNat / 32 % 2 = 1
  · refine ⟨wrapper.cmf, wrapper.flg, be32 (adler32 log.dictionary).toNat,
      finished.bodyAndTrailer, ?_, wrapper.valid, ?_, ?_⟩
    · simpa [Wrapper.bytes, wrapper, present, List.cons_append] using finished.source
    · intro absent
      omega
    · intro _
      refine ⟨rfl, ?_⟩
      simpa [Wrapper.dictionary, wrapper, present] using finished.deflate
  · have absent : wrapper.flg.toNat / 32 % 2 = 0 := by
      have bound := Nat.mod_lt (wrapper.flg.toNat / 32) (by decide : 0 < 2)
      omega
    refine ⟨wrapper.cmf, wrapper.flg, [], finished.bodyAndTrailer, ?_, wrapper.valid, ?_, ?_⟩
    · simpa [Wrapper.bytes, wrapper, present, List.cons_append] using finished.source
    · intro _
      refine ⟨rfl, ?_⟩
      simpa [Wrapper.dictionary, wrapper, present] using finished.deflate
    · intro impossible
      exact False.elim (present impossible)

/-- Header validity bounds CINFO by the default configured window. -/
theorem Finished.default_window_fits {log : DataLog} (finished : Finished log) :
    Api.ZlibFits 15 log.input := by
  refine Or.inr ⟨finished.wrapper.cmf, ?_, ?_⟩
  · rw [finished.source]
    rfl
  · have bound := finished.wrapper.valid.2.1
    omega

/-- Exact wrapper, preset dictionary, body and checksum certificates imply
the public default successful-output relation, with no extra input premise. -/
theorem Finished.default_accepted {log : DataLog} (finished : Finished log) :
    Api.Layer.InflateAccepted .zlib 15 log.dictionary log.input log.output :=
  ⟨finished.decodes_with_default_window, finished.default_window_fits⟩

/-- A real DONE observation selects the finished source case. This is a
projection from the candidate invariant, not its unproved preservation. -/
theorem SourcePhase.finished_of_done {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase log s wire) (done : s.mode = DONE) : Nonempty (Finished log) := by
  cases phase <;>
    simp_all [HEAD, DICTID, DICT, TYPE, TYPEDO, TABLE, LENLENS, CODELENS,
      STORED, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, LIT, MATCH,
      CHECK, LENGTH, BAD, MEM, DONE]
  exact ⟨by assumption⟩

/-- Only the semantic projection is asserted: arbitrary accepted-call
preservation of AtPublic remains a separate proof obligation. -/
theorem AtPublic.default_accepted_of_done
    {h : Heap} {r : ZStreamRef} {log : DataLog} (before : AtPublic h r log)
    (done : before.point.state.mode = DONE) :
    Api.Layer.InflateAccepted .zlib 15 log.dictionary log.input log.output := by
  obtain ⟨finished⟩ := before.phase.finished_of_done done
  exact finished.default_accepted

/-- Combine actual protocol END/DONE correspondence with an established
source spine. No candidate invariant is assumed to hold for every trace. -/
theorem AtPublic.default_accepted_of_protocol_end
    {h : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    (before : AtPublic h r log)
    (trace : InflateProtocolTrace 15 r h log pending)
    (scope : ProtocolWindow.PlatformScope trace) (ended : log.result = Z_STREAM_END) :
    Api.Layer.InflateAccepted .zlib 15 log.dictionary log.input log.output := by
  apply before.default_accepted_of_done
  exact ProtocolWindow.protocol_result_end_mode trace scope
    before.point.zs before.point.z before.point.state before.point.good ended

#print axioms Finished.decodes_with_default_window
#print axioms Finished.default_window_fits
#print axioms Finished.default_accepted
#print axioms SourcePhase.finished_of_done
#print axioms AtPublic.default_accepted_of_done
#print axioms AtPublic.default_accepted_of_protocol_end
end Zlib.Inflate.Proofs.WholeEpoch
