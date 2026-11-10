import ZlibF.Proof.«inflate.c.whole-slow-facts-entry»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken
set_option autoImplicit false

 theorem reading_complete_event
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history : List UInt8} {L D : List Nat} {input residual : List Bool}
    (E : Env c h r zs z s) (view : PayloadView h r zs z s l bs dict history L D)
    (phase : ReadPrefix L D input s residual) (source : residual = stream l bs)
    (modes : s.mode = LENEXT ∨ s.mode = DIST ∨ s.mode = DISTEXT ∨ s.mode = LIT) :
    SlowReverseTokenComplete.DispatchEvent c h r zs l bs dict history L D input := by
  cases phase with
  | code mode =>
    rcases modes with selected | selected | selected | selected <;> rw [mode] at selected <;> cases selected
  | literal decoded small mode length back =>
    exact SlowReverseTokenComplete.LIT_dispatch_event E view (by rwa [source] at decoded) small mode length back
  | lenext decoded lower upper mode length extra back =>
    exact SlowReverseTokenComplete.LENEXT_dispatch_event E view (by rwa [source] at decoded) lower upper mode length extra back
  | dist decoded lower upper read mode length was back =>
    exact SlowReverseTokenComplete.DIST_dispatch_event E view decoded lower upper (by rwa [source] at read) mode length was back
  | distext decoded lower upper read distanceDecode distanceUpper mode length was offset extra back =>
    exact SlowReverseTokenComplete.DISTEXT_dispatch_event E view decoded lower upper read (by rwa [source] at distanceDecode)
      distanceUpper mode length was offset extra back
  | matching _p _inputEq mode _length _was _distance =>
    rcases modes with selected | selected | selected | selected <;> rw [mode] at selected <;> cases selected

/-- Appending currently supplied raw bytes to a held-only pending read
keeps its parser prefix independent of any valid future completion. -/
 theorem Reading.available_phase
    {log : DataLog} {s : InflateState} {wire : List Bool} (reading : Reading log s wire)
    (l : IL) (bs : List UInt8) (bits : held s = natBits l.bits.toNat l.hold.toNat) :
    ReadPrefix reading.boundary.L reading.boundary.D (reading.pendingWord ++ stream l bs) s (stream l bs) := by
  have extended := reading.parsed.append_suffix reading.boundary.validL reading.boundary.validD (bytesBits bs)
  simpa only [bits, stream, List.append_assoc] using extended

#print axioms reading_complete_event
#print axioms Reading.available_phase
end Zlib.Inflate.Proofs.WholeEpoch

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Proofs
open Zlib.Inflate.Proofs SlowInputFragment
set_option autoImplicit false

/-- Caller bytes extend an already parsed syntax witness only as an unread
suffix. All scalar decoded values remain the actual previous values. -/
def append_copy_syntax {L D : List Nat} (p : CopySyntax L D)
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D) (suffix : List Bool) : CopySyntax L D :=
  ⟨p.input ++ suffix, p.r1 ++ suffix, p.r2 ++ suffix, p.r3 ++ suffix, p.rest ++ suffix,
    p.symbol, p.distanceSymbol, p.lengthValue, p.distanceValue,
    ext_acceptable lengths _ _ _ _ p.lengthDecode, p.lengthLower, p.lengthUpper,
    readBits_append _ _ _ _ _ p.lengthRead, ext_acceptable distances _ _ _ _ p.distanceDecode,
    p.distanceUpper, readBits_append _ _ _ _ _ p.distanceRead⟩

#print axioms append_copy_syntax
end Zlib.Inflate.Proofs.WholeEpoch
