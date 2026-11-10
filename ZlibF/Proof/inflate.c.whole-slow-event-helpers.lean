import ZlibF.Proof.«inflate.c.whole-slow-observed-source»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment SlowReverseToken FunctionalTrailer
open ZlibF.Math.LZ77Copy
set_option autoImplicit false

def SlowExitMode (mode : UInt32) : Prop :=
  mode = TYPE ∨ mode = LEN ∨ mode = LENEXT ∨ mode = DIST ∨ mode = DISTEXT ∨ mode = LIT ∨ mode = MATCH ∨ mode = BAD

 theorem read_prefix_modes {L D : List Nat} {input rest : List Bool} {s : InflateState}
    (phase : ReadPrefix L D input s rest) : SlowExitMode s.mode := by
  cases phase with
  | code mode => exact Or.inr (Or.inl mode)
  | literal _ _ mode _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode)))))
  | lenext _ _ _ mode _ _ _ => exact Or.inr (Or.inr (Or.inl mode))
  | dist _ _ _ _ mode _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl mode)))
  | distext _ _ _ _ _ _ mode _ _ _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode))))
  | matching _ _ mode _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode))))))

 theorem complete_event_modes
    {L D : List Nat} {dict history : List UInt8} {input : List Bool} {r : ZStreamRef} {zs : Nat}
    {outcome : Except Ex Unit} {regs : IL} {after : Heap} {z : ZStream} {state : InflateState} {bs : List UInt8}
    (event : SlowReverseTokenComplete.TokenEvent L D dict history input r zs outcome regs after z state bs) : SlowExitMode state.mode := by
  cases event with
  | wait _view phase _empty _pending => exact read_prefix_modes phase
  | bad _good _B mode => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr mode))))))
  | literalPending _view _phase mode _step _length _small => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode)))))
  | eob _view mode _back _step => exact Or.inl mode
  | literalDone _good _buffers mode _get _put _physical _step => exact Or.inr (Or.inl mode)
  | copy _p _made _dest _off _array _input _rest _good _buffers _dictionary _positive _bound
      _length modes _get _put _physical _count _remaining _step _was _offset _back _completed =>
    rcases modes with len | matching
    · exact Or.inr (Or.inl len)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl matching))))))

 theorem SlowExitMode.lower {mode : UInt32} (actual : SlowExitMode mode) : TYPE ≤ mode := by
  rcases actual with m | m | m | m | m | m | m | m <;> rw [m] <;> decide

 theorem SlowExitMode.not_stored {mode : UInt32} (actual : SlowExitMode mode) : mode ≠ STORED := by
  rcases actual with m | m | m | m | m | m | m | m <;> rw [m] <;> decide

 theorem SlowExitMode.not_codes {mode : UInt32} (actual : SlowExitMode mode) : mode ≠ CODELENS := by
  rcases actual with m | m | m | m | m | m | m | m <;> rw [m] <;> decide

 theorem OutputCredit.nat_count
    {h : Heap} {r : ZStreamRef} {z : ZStream} {s : InflateState} {l : IL} {bs prior emitted : List UInt8}
    (output : OutputCredit h z s l prior emitted 0) (buffers : DispatchBuffers h r l bs) :
    l.out_.toNat - l.left.toNat = emitted.length := by
  have pending := output.pending
  rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr buffers.output.count)] at pending
  simpa only [Nat.sub_zero] using pending

 theorem OutputCredit.observed_unique
    {h : Heap} {r : ZStreamRef} {z : ZStream} {s : InflateState} {l : IL} {bs prior emitted observed : List UInt8}
    {dest : BRef} {off : Nat} {array : Array UInt8}
    (output : OutputCredit h z s l prior emitted 0) (buffers : DispatchBuffers h r l bs)
    (put : l.put = .ref dest off) (get : Space.get h dest = some array)
    (bytes : writtenBytes array off (l.out_.toNat - l.left.toNat) = observed) : emitted = observed := by
  obtain ⟨ref, base, actual, pointer, actualGet, _start, _bound, physical⟩ := output.physical
  cases pointer.symm.trans put
  have same : actual = array := Option.some.inj (actualGet.symm.trans get)
  subst actual
  rw [OutputCredit.nat_count output buffers] at bytes
  exact physical.symm.trans bytes

 theorem no_output_more_empty
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    {bs dict history more : List UInt8} {L D : List Nat} {prior : List UInt8}
    (view : PayloadView h r zs z s l bs dict history L D)
    (output : OutputCredit h z s l prior (history ++ more) 0) : more = [] := by
  have count := OutputCredit.nat_count output view.buffers
  have old := view.count
  have length : more.length = 0 := by simp only [List.length_append] at count; omega
  exact List.length_eq_zero_iff.mp length

#print axioms read_prefix_modes
#print axioms complete_event_modes
#print axioms SlowExitMode.lower
#print axioms SlowExitMode.not_stored
#print axioms SlowExitMode.not_codes
#print axioms OutputCredit.nat_count
#print axioms OutputCredit.observed_unique
#print axioms no_output_more_empty
end Zlib.Inflate.Proofs.WholeEpoch
