import ZlibF.Proof.«inflate.c.default-dispatch-output-frame»
import ZlibF.Proof.«inflate.c.region-frame-compose»
import ZlibF.Proof.«inflate.c.gzip-dispatch-state»
import ZlibF.Proof.«inflate.c.head-gzip-frame»

/-!
# inflate.c: the memory frame of one dispatch in a public call

One dispatch writes the stream and state records, the local `hbuf`, the
attached gzip header record, the produced output and the header record's
caller buffers. Its frame names a sublist of the call's regions: the output
slice and the header record's regions at entry.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An output-only frame is a call frame. -/
theorem call_frame_of_output {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {head : GzHeaderPtr} {put : BPtr} {made : Nat} {rest : List Region}
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨put, made⟩]) :
    ∃ S, RegionsWithin S (⟨put, made⟩ :: rest) ∧ BufferFrame h after (CallChanged c r zs head) S :=
  ⟨[⟨put, made⟩], (RegionsWithin.nil rest).cons, frame.mono_changed fun _ view => CallChanged.of_view view⟩

/-- Every dispatch of a public call is framed by the call's changed blocks
and a sublist of its regions. -/
theorem inflate_dispatch_call_frame
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    ∃ S, RegionsWithin S (⟨l.put, made⟩ :: HeaderRegions h s.head) ∧
      BufferFrame h after (CallChanged c r zs s.head) S := by
  have output {outcome2 : Except Ex Unit} {regs2 : IL} {after2 : Heap} {made2 : Nat}
      (run2 : runX (inflate_dispatch c) l h = .ok ((outcome2, regs2), after2))
      (count2 : regs2.left.toNat + made2 = l.left.toNat)
      (frame : BufferFrame h after2 (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made2⟩]) :
      ∃ S, RegionsWithin S (⟨l.put, made⟩ :: HeaderRegions h s.head) ∧
        BufferFrame h after (CallChanged c r zs s.head) S := by
    rw [run] at run2
    cases run2
    have same : made2 = made := by omega
    subst same
    exact call_frame_of_output frame
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · by_cases gzip : GzipAllowed s.wrap
    · sorry
    obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_HEAD_exact_frame E invariant buffers head gzip incoming
    exact output run2 count2 frame
  · obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_metadata_exact_frame E invariant buffers (by
        rcases dictionary with selected | selected <;> simp only [MetadataMode, selected] <;> simp) incoming
    exact output run2 count2 frame
  · obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_metadata_exact_frame E invariant buffers (by
        rcases type with selected | selected <;> simp only [MetadataMode, selected] <;> simp) incoming
    exact output run2 count2 frame
  · obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_stored_exact_frame E invariant buffers stored incoming
    exact output run2 count2 frame
  · obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_construction_exact_frame E invariant buffers construction
    exact output run2 count2 frame
  · obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_data_exact_frame E invariant buffers data
    exact output run2 count2 frame
  · obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_metadata_exact_frame E invariant buffers (by
        rcases trailer with selected | selected <;> simp only [MetadataMode, selected] <;> simp) incoming
    exact output run2 count2 frame
  · obtain ⟨_, _, _, _, _, made2, run2, _, count2, _, frame⟩ :=
      inflate_dispatch_terminal_exact_frame E invariant.good terminal
    exact output run2 count2 frame
  · have inRange : HEAD ≤ s.mode ∧ s.mode ≤ HCRC := by
      obtain ⟨low, high, _⟩ := gzipHeader
      exact ⟨UInt32.le_trans (by decide : HEAD ≤ FLAGS) low, high⟩
    obtain ⟨_, _, _, _, _, _, _, run2, _, _, _, _, _, _, _, _, _, _, _, _, footprint, _⟩ :=
      inflate_dispatch_gzip_header_state_rank E invariant buffers gzipHeader (local_ inRange.1 inRange.2)
        incoming
    rw [run] at run2
    cases run2
    exact ⟨HeaderRegions h s.head, RegionsWithin.tail _ _, footprint.1⟩

#print axioms inflate_dispatch_call_frame
end Zlib.Inflate.Proofs
