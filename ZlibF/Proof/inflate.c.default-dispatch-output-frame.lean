import ZlibF.Proof.«inflate.c.construction-output-frame»
import ZlibF.Proof.«inflate.c.stored-mode-output-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual default mode has the exact frame of its produced caller
slice, including all source continuations and defined refusal outcomes. -/
theorem inflate_dispatch_default_exact_frame
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state made,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · by_cases gzip : GzipAllowed s.wrap
    · sorry
    exact inflate_dispatch_HEAD_exact_frame E invariant buffers head gzip incoming
  · apply inflate_dispatch_metadata_exact_frame E invariant buffers ?_ incoming
    rcases dictionary with selected | selected <;> simp only [MetadataMode, selected] <;> simp
  · apply inflate_dispatch_metadata_exact_frame E invariant buffers ?_ incoming
    rcases type with selected | selected <;> simp only [MetadataMode, selected] <;> simp
  · exact inflate_dispatch_stored_exact_frame E invariant buffers stored incoming
  · exact inflate_dispatch_construction_exact_frame E invariant buffers construction
  · exact inflate_dispatch_data_exact_frame E invariant buffers data
  · apply inflate_dispatch_metadata_exact_frame E invariant buffers ?_ incoming
    rcases trailer with selected | selected <;> simp only [MetadataMode, selected] <;> simp
  · exact inflate_dispatch_terminal_exact_frame E invariant.good terminal
  · sorry

/-- Identify the exact frame with any already proved actual dispatch run
and its actual output count, rather than assuming a dispatcher contract. -/
theorem inflate_dispatch_default_frame_of_run
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨outcome2, regs2, after2, _stream, _state, made2, run2, _good, count2, _put, frame⟩ :=
    inflate_dispatch_default_exact_frame E invariant buffers incoming
  rw [run] at run2
  cases run2
  have same : made2 = made := by omega
  simpa only [same] using frame

/-- The exact memory frame, full initialized state, caller packet and rank
are established on the same actual default dispatch execution. -/
theorem inflate_dispatch_default_view_state_frame_rank
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = inputAdvance l.put made ∧
      regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat ≤ 39 ∧
      HeaderLocal c after r state regs ∧
      (outcome = .ok () → dispatchRank regs state.mode < dispatchRank l s.mode) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, current, packet,
    sizes, next, count, put, left, bits, finalLocal, rank⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers local_ incoming
  exact ⟨outcome, regs, after, stream, state, used, made, bound, run, current, packet,
    sizes, next, count, put, left, bits, finalLocal, rank,
    inflate_dispatch_default_frame_of_run E invariant buffers incoming run left⟩

#print axioms inflate_dispatch_default_view_state_frame_rank
end Zlib.Inflate.Proofs
