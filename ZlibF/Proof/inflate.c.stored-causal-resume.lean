import ZlibF.Proof.«inflate.c.stored-causal-copy»

namespace Zlib.Inflate.Proofs.StoredCausal
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.CausalInput
set_option autoImplicit false

/-- A split stored header keeps its original consumed alignment padding
and only its actual unfinished held word. Unread caller bytes are absent. -/
def HeaderCausal (input : List UInt8) (priorBits padding : List Bool) (l : IL) : Prop :=
  padding.length < 8 ∧ l.bits.toNat % 8 = 0 ∧ Credited input (priorBits ++ padding) l.bits l.hold

/-- Actual first alignment establishes the split-header causal phase. -/
theorem header_causal_begin
    {input bs : List UInt8} {priorBits : List Bool} {l current : IL} {used : Nat}
    (before : Credited input priorBits l.bits l.hold)
    (actualSource : stream current (bs.drop used) = (stream l bs).drop ((stream l bs).length % 8)) :
    let raw := natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)
    HeaderCausal (input ++ bs.take used) priorBits (raw.take (raw.length % 8)) current := by
  obtain ⟨aligned, slice, small⟩ := header_held_source_slice actualSource
  have bits : current.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length aligned
    simp only [List.length_drop, natBits_length] at lengths
    omega
  exact ⟨small, bits, before.append slice⟩

/-- Resuming an aligned partial LEN/NLEN consumes no new padding. The
original first-call padding is retained through any number of input splits. -/
theorem HeaderCausal.resume_source
    {input bs : List UInt8} {priorBits padding : List Bool} {l current : IL} {used : Nat}
    (before : HeaderCausal input priorBits padding l)
    (actualSource : stream current (bs.drop used) = (stream l bs).drop ((stream l bs).length % 8)) :
    HeaderCausal (input ++ bs.take used) priorBits padding current := by
  obtain ⟨small, alignedBefore, source⟩ := before
  obtain ⟨aligned, slice, _newSmall⟩ := header_held_source_slice actualSource
  have modulo : (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)).length % 8 = 0 := by
    simp only [List.length_append, natBits_length, bytesBits_length]
    omega
  have bits : current.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length aligned
    simp only [List.length_drop, natBits_length] at lengths
    omega
  rw [modulo, List.take_zero, List.nil_append] at slice
  have next := source.append (word := []) (by simpa only [List.nil_append] using slice)
  exact ⟨small, bits, by simpa only [List.append_nil] using next⟩

/-- Closed actual header resumption derives the live packet, exact source
credit and unchanged output registers. Wait is its literal source leave;
the arbitrary accepted/BAD classifier handles the completed macro on the
same unique execution. No valid future or successful callee is assumed. -/
theorem arbitrary_header_resume_source
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs input : List UInt8} {priorBits padding : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = STORED) (bits : l.bits.toNat ≤ 39)
    (causal : HeaderCausal input priorBits padding l) :
    ∃ outcome current used,
      runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h) ∧ used ≤ bs.length ∧
      DispatchBuffers h r current (bs.drop used) ∧ HeaderCausal (input ++ bs.take used) priorBits padding current ∧
      current.next = inputAdvance l.next used ∧ current.have_.toNat + used = l.have_.toNat ∧
      current.put = l.put ∧ current.left = l.left ∧ current.in_ = l.in_ ∧ current.out_ = l.out_ ∧
      (outcome = .error Ex.leave → runX (inflate_STORED c) l h = .ok ((.error Ex.leave, current), h)) ∧
      (outcome = .ok () → current.bits.toNat = 32) := by
  obtain ⟨outcome, current, used, macroRun, bound, inv, source, waiting, normal⟩ :=
    stored_STORED_header_prefix E origin packet mode bits
  obtain ⟨next, haveCount, put, left, in_, out_, _bits⟩ :=
    stored_header_actual_metadata packet.bits bound inv macroRun
  have currentPacket := packet.advance_both origin.good origin.good rfl (ByteViewSizes.refl h)
    (fun _ => rfl) next haveCount (made := 0) (by simpa only [inputAdvance_zero] using put)
    (by rw [left]; rfl) out_ inv
  exact ⟨outcome, current, used, macroRun, bound, currentPacket, causal.resume_source source,
    next, haveCount, put, left, in_, out_, waiting, fun accepted => (normal accepted).1⟩

/-- Once the real complement check accepted, commit the held header word
and initialize COPY progress with the retained original padding. -/
theorem HeaderCausal.accepted_copy
    {input : List UInt8} {priorBits padding : List Bool} {l : IL} {len : Nat} {s : InflateState}
    (causal : HeaderCausal input priorBits padding l)
    (header : HeaderWord (natBits l.bits.toNat l.hold.toNat) len)
    (length : s.length.toNat = len) :
    CopyCausal input priorBits padding (natBits l.bits.toNat l.hold.toNat) len [] s {l with bits := 0, hold := 0} := by
  obtain ⟨small, _aligned, source⟩ := causal
  apply CopyCausal.initial small header length rfl
  unfold Credited at source ⊢
  simpa only [UInt32.toNat_zero, natBits, List.append_nil, List.append_assoc] using source

/-- Actual RESTORE/leave field observations retain a partial stored
header when constructing the next public dispatch registers. -/
theorem HeaderCausal.saved_registers
    {input : List UInt8} {priorBits padding : List Bool} {l : IL} {z : ZStream} {s : InflateState}
    (causal : HeaderCausal input priorBits padding l) (bits : s.bits = l.bits) (hold : s.hold = l.hold) :
    HeaderCausal input priorBits padding (dispatchRegs z s) := by
  obtain ⟨small, aligned, source⟩ := causal
  exact ⟨small, by simpa only [dispatchRegs, bits] using aligned,
    by simpa only [dispatchRegs, bits, hold] using source⟩

/-- COPY's original word and observed bytes survive real leave's restored
hold/bits and unchanged remaining length. Window/accounting writes and
caller buffer replacement do not enter the causal payload record. -/
theorem CopyCausal.saved_registers
    {input copied : List UInt8} {priorBits padding word : List Bool} {len : Nat}
    {l : IL} {z : ZStream} {s state : InflateState}
    (causal : CopyCausal input priorBits padding word len copied s l)
    (bits : state.bits = l.bits) (hold : state.hold = l.hold) (length : state.length = s.length) :
    CopyCausal input priorBits padding word len copied state (dispatchRegs z state) := by
  obtain ⟨small, pending, zero, source⟩ := causal
  refine ⟨small, ⟨pending.1, by rw [length]; exact pending.2⟩, ?_, ?_⟩
  · change state.bits = 0
    rw [bits, zero]
  · simpa only [dispatchRegs, bits, hold] using source

#print axioms header_causal_begin
#print axioms HeaderCausal.resume_source
#print axioms arbitrary_header_resume_source
#print axioms HeaderCausal.accepted_copy
#print axioms HeaderCausal.saved_registers
#print axioms CopyCausal.saved_registers
end Zlib.Inflate.Proofs.StoredCausal
