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

/-- Regions kept or set to `Z_NULL` name no new view and cover no new byte. -/
theorem RegionsKept.within : ∀ {after before : List Region}, RegionsKept after before →
    RegionsWithin after before
  | [], [], _ => RegionsWithin.refl []
  | a :: after, b :: before, kept => by
    obtain ⟨here, rest⟩ := kept
    have tail := RegionsKept.within rest
    rcases here with rfl | ⟨null, _⟩
    · exact tail.cons
    · refine ⟨?_, ?_⟩
      · rintro ref ⟨region, member, off, pointer⟩
        rcases List.mem_cons.mp member with rfl | inner
        · rw [null] at pointer; cases pointer
        · exact (RegionsWithin.tail b before).1 ref (tail.1 ref ⟨region, inner, off, pointer⟩)
      · rintro ref j ⟨region, member, covers⟩
        rcases List.mem_cons.mp member with rfl | inner
        · obtain ⟨off, pointer, _⟩ := covers
          rw [null] at pointer; cases pointer
        · exact (RegionsWithin.tail b before).2 ref j (tail.2 ref j ⟨region, inner, covers⟩)
  | [], _ :: _, kept => by cases kept
  | _ :: _, [], kept => by cases kept

/-- One dispatch of a public call either writes only the stream, the state
and the produced output, or runs in a header mode: it then writes the call's
blocks and the header record's caller buffers, keeps the attached record and
only drops its regions. -/
def DispatchCallFrame (c : Ctx) (r : ZStreamRef) (zs : Nat) (s : InflateState) (l : IL) (made : Nat)
    (h after : Heap) : Prop :=
  BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] ∨
    (HEAD ≤ s.mode ∧ s.mode ≤ HCRC ∧
      BufferFrame h after (CallChanged c r zs s.head) (HeaderRegions h s.head) ∧
      ∀ state, after.istates zs = some state →
        state.head = s.head ∧ RegionsWithin (HeaderRegions after state.head) (HeaderRegions h s.head))

/-- Every dispatch of a public call has its call frame. -/
theorem inflate_dispatch_call_frame
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    DispatchCallFrame c r zs s l made h after := by
  have output {outcome2 : Except Ex Unit} {regs2 : IL} {after2 : Heap} {made2 : Nat}
      (run2 : runX (inflate_dispatch c) l h = .ok ((outcome2, regs2), after2))
      (count2 : regs2.left.toNat + made2 = l.left.toNat)
      (frame : BufferFrame h after2 (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made2⟩]) :
      DispatchCallFrame c r zs s l made h after := by
    rw [run] at run2
    cases run2
    have same : made2 = made := by omega
    subst same
    exact Or.inl frame
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal | gzipHeader
  · by_cases gzip : GzipAllowed s.wrap
    · have inRange : HEAD ≤ s.mode ∧ s.mode ≤ HCRC := by rw [head]; decide
      have headerLocal := local_ inRange.1 inRange.2
      obtain ⟨foot, regionsEq⟩ := inflate_dispatch_HEAD_gzip_frame E invariant buffers head gzip headerLocal run
      obtain ⟨_, _, _, _, state2, _, _, run2, final, _, _, _, _, _, _, _, _, _, _, headEq, _⟩ :=
        inflate_dispatch_HEAD_gzip_state_rank E invariant buffers head gzip headerLocal incoming
      rw [run] at run2
      cases run2
      refine Or.inr ⟨inRange.1, inRange.2, foot.bufferFrame, ?_⟩
      intro state get
      have same : state = state2 := Option.some.inj (get.symm.trans final.good.live.hs)
      subst same
      rw [headEq, regionsEq]
      exact ⟨rfl, RegionsWithin.refl _⟩
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
    obtain ⟨_, _, _, _, state2, _, _, run2, final, _, _, _, _, _, _, _, _, _, stateFrame, _, footprint, kept, _⟩ :=
      inflate_dispatch_gzip_header_state_rank E invariant buffers gzipHeader (local_ inRange.1 inRange.2)
        incoming
    rw [run] at run2
    cases run2
    refine Or.inr ⟨inRange.1, inRange.2, footprint.1, ?_⟩
    intro state get
    have same : state = state2 := Option.some.inj (get.symm.trans final.good.live.hs)
    subst same
    have headEq : state.head = s.head := by rw [stateFrame]
    refine ⟨headEq, ?_⟩
    have within := kept.within
    rw [headEq] at within ⊢
    exact within

#print axioms inflate_dispatch_call_frame
end Zlib.Inflate.Proofs
