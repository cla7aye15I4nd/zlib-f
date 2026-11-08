import ZlibF.Proof.«inflate.c.byte-views»
import ZlibF.Spec.Public.History

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem byte_view_put_existing {h : Heap} {ref : BRef} {a : Array UInt8}
    (get : Space.get h ref = some a) : Space.put h ref a = h := by
  cases ref with
  | blk i => simp only [Space.get] at get; simp [Space.put, upd_self _ _ _ get]
  | dstate_depth i =>
    cases state : h.dstates i with
    | none => simp [Space.get, state] at get
    | some s =>
      have same : s.depth = a := by simpa [Space.get, state] using get
      rw [← same]
      simp [Space.put, state, upd_self _ _ _ state]
  | str _ | st_dist_code | st_length_code => rfl

/-- Restoring byte views that did not change leaves the heap unchanged. -/
theorem restoreRegions_unchanged {before after : Heap}
    (views : ∀ ref : BRef, Space.get after ref = Space.get before ref)
    (regions : List Region) : restoreRegions before after regions = after := by
  induction regions with
  | nil => rfl
  | cons region rest ih =>
    have first : (match region.pointer with
      | .null => after
      | .ref ref _ => match Space.get before ref with
        | none => after
        | some a => Space.put after ref a) = after := by
      cases pointer : region.pointer with
      | null => rfl
      | ref ref off =>
        cases get : Space.get before ref with
        | none => simp only [get]
        | some a => simpa only [get] using byte_view_put_existing ((views ref).trans get)
    exact (congrArg (fun next => restoreRegions before next rest) first).trans ih

/-- Fast writeback changes only the stream and inflate state records.
It preserves every caller byte view and the exact allocation ledger. -/
theorem fastWriteback_heap_frame {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (hz : r.get h = some z)
    (hs : h.istates zs = some s) (z' : ZStream) (s' : InflateState)
    (regions : List Region) :
    let after := setI (r.put h z') zs s'
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) regions ∧
    LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc := by
  dsimp only
  have views : ∀ ref : BRef, Space.get (setI (r.put h z') zs s') ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have frame : Frame h (setI (r.put h z') zs s') (fun b => StreamRoot r b ∨ b = zs) := by
    cases r with
    | tab i =>
      simp only [ZStreamRef.get] at hz
      simp only [Frame, setI, ZStreamRef.put, hz, true_and, Nat.le_refl]
      intro b live unchanged
      have ni : b ≠ i := fun same => unchanged (Or.inl same)
      have ns : b ≠ zs := fun same => unchanged (Or.inr same)
      simp [upd_ne _ _ _ _ ni, upd_ne _ _ _ _ ns]
    | in_gzstate_strm i =>
      obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.mp hz
      simp only [Frame, setI, ZStreamRef.put, hg, true_and, Nat.le_refl]
      intro b live unchanged
      have ni : b ≠ i := fun same => unchanged (Or.inl same)
      have ns : b ≠ zs := fun same => unchanged (Or.inr same)
      simp [upd_ne _ _ _ _ ni, upd_ne _ _ _ _ ns]
  refine ⟨⟨?_, ?_⟩, ?_, by simp [setI]⟩
  · rw [restoreRegions_unchanged views]
    exact frame
  · intro region member ref off a pointer get
    exact ⟨a, (views ref).trans get, rfl, fun _ _ _ => rfl⟩
  · have shape := (shape_put hz z').trans (shape_setI (by simpa using hs) s')
    intro b
    simpa only [or_false, not_false_eq_true, and_true] using shape.live b

#print axioms fastWriteback_heap_frame
end Zlib.Inflate.Proofs
