import ZlibF.Proof.«inflate.c.default-dispatch-output-frame»
import ZlibF.Proof.«inflate.c.region-frame-compose»
import ZlibF.Proof.«inflate.c.gzip-dispatch-state»
import ZlibF.Proof.«inflate.c.head-gzip-frame»
import ZlibF.Proof.«inflate.c.head-source-observer»

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

/-- A block holding a stream, a decoder state or a gzip file state holds no gzip header record. -/
theorem Uniq.gzheaders_none {h : Heap} (uniq : Uniq h) {i : Nat}
    (other : h.streams i ≠ none ∨ h.istates i ≠ none ∨ h.gzstates i ≠ none) : h.gzheaders i = none := by
  have count := uniq i
  cases g : h.gzheaders i with
  | none => rfl
  | some _ =>
    exfalso
    rw [g] at count
    rcases other with e | e | e
    · cases x : h.streams i with
      | none => exact e x
      | some _ => simp only [x, cnt_some] at count; omega
    · cases x : h.istates i with
      | none => exact e x
      | some _ => simp only [x, cnt_some] at count; omega
    · cases x : h.gzstates i with
      | none => exact e x
      | some _ => simp only [x, cnt_some] at count; omega

/-- The stream root and the state block hold no gzip header record. -/
theorem view_block_no_header {h : Heap} {r : ZStreamRef} {zs i : Nat} {z : ZStream} {s : InflateState}
    (uniq : Uniq h) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (view : StreamRoot r i ∨ i = zs) : h.gzheaders i = none := by
  apply Uniq.gzheaders_none uniq
  rcases view with root | rfl
  · cases r with
    | tab j =>
      change i = j at root
      subst root
      exact Or.inl (by change h.streams i = some z at hz; rw [hz]; simp)
    | in_gzstate_strm j =>
      change i = j at root
      subst root
      refine Or.inr (Or.inr ?_)
      change (h.gzstates i).map (·.strm) = some z at hz
      intro none
      rw [none] at hz
      cases hz
  · exact Or.inr (Or.inl (by rw [hs]; simp))

/-- A frame that changes only the stream and the state keeps every gzip
header record, so the attached record names the same regions. -/
theorem output_frame_header_regions {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z z' : ZStream} {s s' : InflateState} {R : List Region}
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) R)
    (before : Good h r zs z s) (current : Good after r zs z' s') (live : after.live = h.live)
    (head : GzHeaderPtr) : HeaderRegions after head = HeaderRegions h head := by
  have key : ∀ i, after.gzheaders i = h.gzheaders i := by
    intro i
    by_cases view : StreamRoot r i ∨ i = zs
    · rw [view_block_no_header current.uniq current.live.hz current.live.hs view,
        view_block_no_header before.uniq before.live.hz before.live.hs view]
    · by_cases liveH : h.live i
      · obtain ⟨_, _, _, headers, _⟩ := frame.1.2.2.2.2.2 i liveH view
        have other := (restoreRegions_other h after R).2.2.2.2.2.2.2.1
        rw [other] at headers
        exact headers
      · have liveA : ¬ after.live i := by rw [live]; exact liveH
        have noneH : h.gzheaders i = none := by
          cases e : h.gzheaders i with
          | none => rfl
          | some _ => exact absurd (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp))))) liveH
        have noneA : after.gzheaders i = none := by
          cases e : after.gzheaders i with
          | none => rfl
          | some _ => exact absurd (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp))))) liveA
        rw [noneH, noneA]
  unfold HeaderRegions
  rcases head with _ | ⟨i⟩
  · rfl
  · cases i with
    | tab i => simp only [key i]

/-- Every dispatch keeps the attached gzip header record pointer. -/
theorem dispatch_head_kept {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {s state : InflateState}
    {l regs : IL} {outcome : Except Ex Unit} (root : c.strm = some r)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (before : h.istates zs = some s) (get : after.istates zs = some state) : state.head = s.head := by
  have fixed := HeadObserver.windowFrameX_inflate_dispatch r c root l h outcome regs after run
  have selected := congrFun fixed zs
  change (after.istates zs).map HeadObserver.counts = (h.istates zs).map HeadObserver.counts at selected
  rw [get, before] at selected
  exact Option.some.inj selected

/-- What the call frame needs from the caller at the start of the body: the
output buffer and the header record's buffers are writable views of blocks
the call does not change, and the saved window is none of them. -/
structure CallFrameFacts (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) :
    Prop where
  views : RegionViews (CallChanged c r zs s.head) (⟨z.next_out, 0⟩ :: HeaderRegions h s.head)
  window : ∀ w, s.window = .ref (.blk w) 0 →
    ¬ CallChanged c r zs s.head w ∧ ¬ RegionRoot (⟨z.next_out, 0⟩ :: HeaderRegions h s.head) (.blk w)

theorem RegionRoot.head_length {pointer : BPtr} {n m : Nat} {rest : List Region} {ref : BRef}
    (root : RegionRoot (⟨pointer, n⟩ :: rest) ref) : RegionRoot (⟨pointer, m⟩ :: rest) ref := by
  obtain ⟨region, member, off, at_⟩ := root
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨_, List.mem_cons_self, off, at_⟩
  · exact ⟨region, List.mem_cons_of_mem _ tail, off, at_⟩

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
