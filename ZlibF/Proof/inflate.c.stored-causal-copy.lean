import ZlibF.Proof.«inflate.c.stored-causal-header»
import ZlibF.Proof.«inflate.c.input-base-modes»

namespace Zlib.Inflate.Proofs.StoredCausal
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.CausalInput
set_option autoImplicit false

/-- A fully observed payload closes the independent stored grammar from
the actual accepted header word. Padding is arbitrary and retained;
there is no premise that the original input was valid. -/
theorem HeaderWord.completed_body
    {word padding : List Bool} {len : Nat} {copied future dictionary prior : List UInt8}
    (header : HeaderWord word len) (padBound : padding.length < 8) (count : copied.length = len) :
    Body dictionary 0 prior ((padding ++ word) ++ bytesBits copied ++ bytesBits future)
      (bytesBits future) (prior ++ copied) := by
  obtain ⟨wordLength, _small, nlen, middle, first, second, complement⟩ := header
  have alignment : (((padding ++ word) ++ bytesBits copied) ++ bytesBits future).length % 8 = padding.length := by
    simp only [List.length_append, bytesBits_length]
    omega
  have aligned : (((padding ++ word) ++ bytesBits copied) ++ bytesBits future).drop padding.length =
      word ++ (bytesBits copied ++ bytesBits future) := by
    rw [List.append_assoc, List.append_assoc, List.drop_left]
  have firstExtended := stored_readBits_append first (bytesBits copied ++ bytesBits future)
  have secondExtended := stored_readBits_append second (bytesBits copied ++ bytesBits future)
  simp only [List.nil_append] at secondExtended
  have readPayload : readBytes len (bytesBits copied ++ bytesBits future) = some (copied, bytesBits future) := by
    rw [← count]
    simpa only [bytesBits_eq_bytesToBits] using
      Zlib.Trees.Proofs.Out.readBytes_encoded copied (bytesBits future)
  apply Body.stored (len := len) (nlen := nlen) (r1 := middle ++ (bytesBits copied ++ bytesBits future))
    (r2 := bytesBits copied ++ bytesBits future)
  · rw [alignment, aligned]
    exact firstExtended
  · exact secondExtended
  · exact complement
  · exact readPayload

/-- Pending arbitrary stored bytes are actual copied bytes, not a guessed
future payload. The debt is the real original LEN minus bytes observed so far. -/
def CopyPending (word : List Bool) (len : Nat) (copied : List UInt8) (s : InflateState) : Prop :=
  HeaderWord word len ∧ s.length.toNat + copied.length = len

/-- The complete actual COPY or COPY_ dispatch exposes one bounded source
segment and its literal mode alternatives, before any semantic assumption. -/
theorem copy_dispatch_actual_boundary
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = COPY ∨ s.mode = COPY_) :
    ∃ outcome regs after state made,
      made ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop made) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state.mode = COPY) ∨
       (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
       (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY)) ∧ after.static = h.static := by
  rcases mode with copying | starting
  · obtain ⟨outcome, regs, after, state, made, bound, actual, good, tables, pending,
      currentPacket, sizes, frame, next, haveCount, put, leftCount, bits, hold, kinds, static, _shape⟩ :=
      inflate_COPY_boundary_frame E origin.good origin.pending packet copying
    refine ⟨outcome, regs, after, state, made, bound, (inflate_dispatch_COPY E l copying).trans actual,
      good, tables, pending, currentPacket, sizes, frame, next, haveCount, put, leftCount,
      bits, hold, ?_, static⟩
    rcases kinds with ⟨exit, zero, same⟩ | ⟨exit, zero, type⟩ | ⟨exit, positive, copy, _debt⟩
    · exact Or.inl ⟨exit, zero, by rw [same]; exact copying⟩
    · exact Or.inr (Or.inl ⟨exit, zero, type⟩)
    · exact Or.inr (Or.inr ⟨exit, positive, copy⟩)
  · obtain ⟨outcome, regs, after, state, made, bound, actual, good, tables, pending,
      currentPacket, sizes, frame, next, haveCount, put, leftCount, bits, hold, kinds, static, _shape⟩ :=
      inflate_COPY_start_boundary_frame E origin.good origin.pending packet starting
    refine ⟨outcome, regs, after, state, made, bound, (inflate_dispatch_COPY_start E l starting).trans actual,
      good, tables, pending, currentPacket, sizes, frame, next, haveCount, put, leftCount,
      bits, hold, ?_, static⟩
    rcases kinds with ⟨exit, zero, same⟩ | ⟨exit, zero, type⟩ | ⟨exit, positive, copy, _debt⟩
    · exact Or.inl ⟨exit, zero, by rw [same]⟩
    · exact Or.inr (Or.inl ⟨exit, zero, type⟩)
    · exact Or.inr (Or.inr ⟨exit, positive, copy⟩)

/-- One actual COPY dispatch advances only observed source bytes and the
pending LEN debt, with no full future payload or valid-input premise.
The causal input ledger and exact physical output segment are produced
from the real run. Waiting and TYPE completion remain explicit. -/
theorem arbitrary_copy_fragment
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs input copied : List UInt8} {committed word : List Bool} {len : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = COPY ∨ s.mode = COPY_)
    (bits : l.bits = 0) (source : Credited input committed l.bits l.hold)
    (pending : CopyPending word len copied s) :
    ∃ outcome regs after state made,
      made ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultOriginState after r zs z state ∧ DecodeStateFrame s state ∧ DispatchBuffers after r regs (bs.drop made) ∧
      Bytes after l.put made (bs.take made) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits = 0 ∧ regs.hold = l.hold ∧ regs.out_ = l.out_ ∧ regs.in_ = l.in_ ∧
      (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + made ∧
      Credited (input ++ bs.take made) (committed ++ bytesBits (bs.take made)) regs.bits regs.hold ∧
      CopyPending word len (copied ++ bs.take made) state ∧
      (∃ ref off array, l.put = .ref ref off ∧ regs.put = .ref ref (off + made) ∧
        Space.get after ref = some array ∧ off + made ≤ array.size ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made = bs.take made) ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state.mode = COPY) ∨
       (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
       (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY)) := by
  obtain ⟨outcome, regs, after, state, made, bound, actual, good, tables, nextPending,
    currentPacket, sizes, frame, next, haveCount, put, leftCount, bitsEq, holdEq, kinds, static⟩ :=
    copy_dispatch_actual_boundary E origin packet mode
  have observed : Bytes after l.put made (bs.take made) ∧ state.length.toNat + made = s.length.toNat := by
    rcases mode with copying | starting
    · have payload := stored_COPY_payload_of_run E origin.good packet
        ((inflate_dispatch_COPY E l copying).symm.trans actual) leftCount
      exact ⟨payload.1, payload.2.2.2 state good.live.hs⟩
    · have payload := stored_COPY_start_payload_of_run E origin.good packet
        ((inflate_dispatch_COPY_start E l starting).symm.trans actual) leftCount
      exact ⟨payload.1, payload.2.2 state good.live.hs⟩
  have storedMode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY :=
    mode.elim (fun copy => Or.inr (Or.inr copy)) (fun start => Or.inr (Or.inl start))
  have modes : StoredExitMode state.mode := by
    rcases kinds with ⟨_, _, copy⟩ | ⟨_, _, type⟩ | ⟨_, _, copy⟩
    · exact Or.inr (Or.inr (Or.inl copy))
    · exact Or.inr (Or.inr (Or.inr (Or.inl type)))
    · exact Or.inr (Or.inr (Or.inl copy))
  have currentJ := origin.toDefaultStateJ.stored_update storedMode good tables nextPending frame modes sizes static
  have current := inflate_dispatch_default_origin_state E origin packet actual currentJ
  have memory : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
    rcases mode with copying | starting
    · exact inflate_COPY_frame_of_run E origin.good packet ((inflate_dispatch_COPY E l copying).symm.trans actual) leftCount
    · exact inflate_COPY_start_frame_of_run E origin.good packet ((inflate_dispatch_COPY_start E l starting).symm.trans actual) leftCount
  have nextBits : regs.bits = 0 := bitsEq.trans bits
  have outBase := inflate_dispatch_output_base_noncheck E (by rcases mode with m | m <;> rw [m] <;> decide) actual
  have inBase := inputBaseX_inflate_dispatch l.in_ c l h outcome regs after rfl actual
  have count : (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + made := by
    have oldBound := packet.output.count
    have nextBound : regs.left.toNat ≤ regs.out_.toNat := by rw [outBase]; omega
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr nextBound),
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr oldBound), outBase]
    omega
  have nextSource : Credited (input ++ bs.take made) (committed ++ bytesBits (bs.take made)) regs.bits regs.hold := by
    apply source.append
    rw [bits, nextBits]
    simp only [UInt32.toNat_zero, natBits, List.nil_append, List.append_nil]
  have nextDebt : CopyPending word len (copied ++ bs.take made) state := by
    refine ⟨pending.1, ?_⟩
    have debt := observed.2
    have oldDebt := pending.2
    simp only [List.length_append, List.length_take, Nat.min_eq_left bound]
    omega
  have physical : ∃ ref off array, l.put = .ref ref off ∧ regs.put = .ref ref (off + made) ∧
      Space.get after ref = some array ∧ off + made ≤ array.size ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made = bs.take made := by
    rcases observed.1 with ⟨null, _zero, _empty⟩ | ⟨ref, off, array, pointer, get, room, values⟩
    · exact False.elim (packet.output.nonnull null)
    · refine ⟨ref, off, array, pointer, ?_, get, room, ?_⟩
      · rw [put, pointer]; rfl
      · have bytes : Bytes after (.ref ref ((off + made) - made)) made (bs.take made) := by
          rw [Nat.add_sub_cancel]
          exact Or.inr ⟨ref, off, array, rfl, get, room, values⟩
        exact (writtenBytes_matches_output get (by omega) room bytes).symm
  exact ⟨outcome, regs, after, state, made, bound, actual, current, frame, currentPacket,
    observed.1, memory, next, haveCount, put, leftCount, nextBits, holdEq, outBase, inBase,
    count, nextSource, nextDebt, physical, kinds⟩

#print axioms HeaderWord.completed_body
#print axioms copy_dispatch_actual_boundary
#print axioms arbitrary_copy_fragment
end Zlib.Inflate.Proofs.StoredCausal

namespace Zlib.Inflate.Proofs.StoredCausal
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.CausalInput
set_option autoImplicit false

/-- A real accepted header initializes empty observed-copy progress. -/
theorem CopyPending.initial {word : List Bool} {len : Nat} {s : InflateState}
    (header : HeaderWord word len) (length : s.length.toNat = len) : CopyPending word len [] s := by
  exact ⟨header, by simpa only [List.length_nil, Nat.add_zero] using length⟩

/-- At actual zero remaining debt, the observed bytes reconstruct the
independent Body.stored grammar. Future bytes are arbitrary continuation,
not an assumed full future payload. -/
theorem CopyPending.completed
    {word padding : List Bool} {len : Nat} {copied : List UInt8} {s : InflateState}
    (pending : CopyPending word len copied s) (zero : s.length = 0) (padBound : padding.length < 8) :
    ∀ future dictionary prior,
      Body dictionary 0 prior ((padding ++ word) ++ bytesBits copied ++ bytesBits future)
        (bytesBits future) (prior ++ copied) := by
  have length : copied.length = len := by
    have debt := pending.2
    rw [zero] at debt
    simpa only [UInt32.toNat_zero, Nat.zero_add] using debt
  intro future dictionary prior
  exact HeaderWord.completed_body pending.1 padBound length

/-- Existing original public DataSteps and caller rebuffering accumulate
only actual copied bytes. The closed trace theorem identifies input and
output, preserves the LEN debt and reconstructs Body.stored whenever the
actual remaining length reaches zero. No valid-source/Body premise or
expected future output is supplied. Public MEM outcomes remain in the
underlying actual trace rather than being recast as completion. -/
theorem partial_trace_arbitrary_progress
    {start after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {input output copied : List UInt8} {word : List Bool} {len : Nat}
    (origin : DefaultOriginState start r zs z s) (allocator : DefAlloc z)
    (pending : CopyPending word len copied s)
    (history : StoredCopyPartialTrace start r zs after input output) :
    ∃ stream state, DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      output = input ∧ CopyPending word len (copied ++ output) state ∧
      (state.length = 0 → ∀ padding : List Bool, padding.length < 8 → ∀ future dictionary prior,
        Body dictionary 0 prior ((padding ++ word) ++ bytesBits (copied ++ output) ++ bytesBits future)
          (bytesBits future) (prior ++ (copied ++ output))) := by
  obtain ⟨stream, state, current, currentAllocator, same, debt⟩ := history.sound origin allocator
  have nextPending : CopyPending word len (copied ++ output) state := by
    refine ⟨pending.1, ?_⟩
    have oldDebt := pending.2
    rw [same, List.length_append]
    omega
  refine ⟨stream, state, current, currentAllocator, same, nextPending, ?_⟩
  intro zero padding padBound
  exact CopyPending.completed nextPending zero padBound

#print axioms CopyPending.initial
#print axioms CopyPending.completed
#print axioms partial_trace_arbitrary_progress
end Zlib.Inflate.Proofs.StoredCausal

namespace Zlib.Inflate.Proofs.StoredCausal
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.CausalInput
set_option autoImplicit false

/-- Causal stored phase over actually credited bytes. It retains the
original alignment, checked header word and copied bytes; it mentions no
future payload and assumes no independent Body interpretation. -/
def CopyCausal (input : List UInt8) (priorBits padding word : List Bool) (len : Nat)
    (copied : List UInt8) (s : InflateState) (l : IL) : Prop :=
  padding.length < 8 ∧ CopyPending word len copied s ∧ l.bits = 0 ∧
    Credited input (priorBits ++ ((padding ++ word) ++ bytesBits copied)) l.bits l.hold

/-- Actual accepted-header fields initialize the causal phase with no
copied bytes. The source equation is exactly the accepted branch of the
header classifier after substituting its real padding/held-word split. -/
theorem CopyCausal.initial
    {input : List UInt8} {priorBits padding word : List Bool} {len : Nat} {s : InflateState} {l : IL}
    (padBound : padding.length < 8) (header : HeaderWord word len)
    (length : s.length.toNat = len) (bits : l.bits = 0)
    (source : Credited input (priorBits ++ (padding ++ word)) l.bits l.hold) :
    CopyCausal input priorBits padding word len [] s l := by
  exact ⟨padBound, CopyPending.initial header length, bits,
    by simpa only [bytesBits_nil, List.append_nil] using source⟩

/-- Execute one real arbitrary COPY/COPY_ step and advance the causal
source, observed payload and pending scalar debt together. Original
padding and header provenance are retained. The physical slice and exact
BufferFrame feed the common OutputCredit append rule. -/
theorem arbitrary_causal_copy_step
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs input copied : List UInt8} {priorBits padding word : List Bool} {len : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = COPY ∨ s.mode = COPY_)
    (causal : CopyCausal input priorBits padding word len copied s l) :
    ∃ outcome regs after state made,
      made ≤ bs.length ∧ runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultOriginState after r zs z state ∧ DecodeStateFrame s state ∧
      DispatchBuffers after r regs (bs.drop made) ∧ Bytes after l.put made (bs.take made) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∧
      regs.next = inputAdvance l.next made ∧ regs.have_.toNat + made = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.out_ = l.out_ ∧ regs.in_ = l.in_ ∧
      (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + made ∧
      CopyCausal (input ++ bs.take made) priorBits padding word len (copied ++ bs.take made) state regs ∧
      (∃ ref off array, l.put = .ref ref off ∧ regs.put = .ref ref (off + made) ∧
        Space.get after ref = some array ∧ off + made ≤ array.size ∧
        ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made = bs.take made) ∧
      ((outcome = .error Ex.leave ∧ made = 0 ∧ state.mode = COPY) ∨
       (outcome = .ok () ∧ made = 0 ∧ state.mode = TYPE) ∨
       (outcome = .ok () ∧ 0 < made ∧ state.mode = COPY)) := by
  obtain ⟨padBound, pending, bits, source⟩ := causal
  obtain ⟨outcome, regs, after, state, made, bound, actual, current, frame, currentPacket,
    bytes, memory, next, haveCount, put, leftCount, nextBits, _hold, outBase, inBase,
    count, nextSource, nextPending, physical, kinds⟩ :=
    arbitrary_copy_fragment E origin packet mode bits source pending
  have nextCausal : CopyCausal (input ++ bs.take made) priorBits padding word len
      (copied ++ bs.take made) state regs := by
    refine ⟨padBound, nextPending, nextBits, ?_⟩
    simpa only [bytesBits_append, List.append_assoc] using nextSource
  exact ⟨outcome, regs, after, state, made, bound, actual, current, frame, currentPacket,
    bytes, memory, next, haveCount, put, leftCount, outBase, inBase, count, nextCausal, physical, kinds⟩

/-- At actual zero debt the grammar comes from the actually credited
input prefix, not a preselected valid source. The copied bytes are the
actual output accumulator advanced by the execution producer above. -/
theorem CopyCausal.completed_source
    {input copied : List UInt8} {priorBits padding word : List Bool} {len : Nat}
    {s : InflateState} {l : IL}
    (causal : CopyCausal input priorBits padding word len copied s l) (zero : s.length = 0) :
    ∃ bodySource, bytesBits input = priorBits ++ bodySource ∧
      ∀ future dictionary prior,
        Body dictionary 0 prior (bodySource ++ bytesBits future) (bytesBits future) (prior ++ copied) := by
  obtain ⟨padBound, pending, bits, source⟩ := causal
  refine ⟨(padding ++ word) ++ bytesBits copied, ?_, ?_⟩
  · unfold Credited at source
    simpa only [bits, UInt32.toNat_zero, natBits, List.append_nil] using source
  · exact CopyPending.completed pending zero padBound

#print axioms CopyCausal.initial
#print axioms arbitrary_causal_copy_step
#print axioms CopyCausal.completed_source
end Zlib.Inflate.Proofs.StoredCausal
