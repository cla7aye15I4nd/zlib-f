import ZlibF.Proof.«inflate.c.whole-epoch-source-spine»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

private theorem bytes_put_other (h : Heap) (ref : BRef) (array : Array UInt8) (w : Nat)
    (different : ref ≠ .blk w) : (Space.put h ref array).bytes w = h.bytes w := by
  cases ref with
  | blk b =>
    have notSame : w ≠ b := by intro same; subst b; exact different rfl
    exact upd_ne _ _ _ _ notSame
  | str _ => rfl
  | dstate_depth index =>
    change (match h.dstates index with
      | some s => {h with dstates := upd h.dstates index (some {s with depth := array})}
      | none => h).bytes w = h.bytes w
    cases h.dstates index <;> rfl
  | st_dist_code => rfl
  | st_length_code => rfl

private theorem restore_output_other_bytes (before after : Heap) (pointer : BPtr) (made w : Nat)
    (separate : ∀ off, pointer ≠ .ref (.blk w) off) :
    (restoreRegions before after [⟨pointer, made⟩]).bytes w = after.bytes w := by
  unfold restoreRegions
  simp only [List.foldl_cons, List.foldl_nil]
  cases pointer with
  | null => rfl
  | ref ref off =>
    have different : ref ≠ .blk w := by intro same; subst ref; exact separate off rfl
    change (match (Space.get before ref : Option (Array UInt8)) with
      | none => after
      | some array => Space.put after ref array).bytes w = after.bytes w
    cases get : (Space.get before ref : Option (Array UInt8)) with
    | none => simp only [get]
    | some array => simpa only [get] using bytes_put_other after ref array w different

/-- Exact caller-output frames preserve the private saved window. The
caller range excludes that owned byte block even for general BRef output. -/
theorem dictionary_caller_output_frame
    {before after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {dictionary : List UInt8} {pointer : BPtr} {capacity made : Nat}
    (good : Good before r zs z s)
    (range : CallerRange before r pointer capacity true)
    (frame : BufferFrame before after (fun b => StreamRoot r b ∨ b = zs) [⟨pointer, made⟩])
    (window : state.window = s.window) (size : state.wsize = s.wsize)
    (haveCount : state.whave = s.whave) (next : state.wnext = s.wnext)
    (stored : InflateDictionary before s dictionary) : InflateDictionary after state dictionary := by
  rcases stored with ⟨zero, empty⟩ | ⟨ref, off, array, pointerWindow, get, bound, values⟩
  · exact Or.inl ⟨by rw [haveCount]; exact zero, empty⟩
  · rcases good.inv.win.block with null | ⟨w, original, windowPointer, bytes, _readonly, _size⟩
    · rw [null] at pointerWindow
      cases pointerWindow
    · rw [windowPointer] at pointerWindow
      cases pointerWindow
      have unique := Uniq.bytes_only good.uniq bytes
      have outside : ¬ (StreamRoot r w ∨ w = zs) := by
        intro selected
        rcases selected with root | stateId
        · cases r with
          | tab id =>
            change w = id at root
            subst id
            have absent := unique.2.1
            have streamGet := good.live.hz
            change before.streams w = some z at streamGet
            rw [streamGet] at absent
            cases absent
          | in_gzstate_strm id =>
            change w = id at root
            subst id
            have absent := unique.2.2.2.2.2
            have streamGet := good.live.hz
            change (before.gzstates w).map (·.strm) = some z at streamGet
            rw [absent] at streamGet
            cases streamGet
        · subst zs
          have absent := unique.2.2.2.2.1
          rw [good.live.hs] at absent
          cases absent
      have live : before.live w := by simp [Heap.live, bytes]
      have kept := frame.1.2.2.2.2.2 w live outside
      have separate : ∀ offset, pointer ≠ .ref (.blk w) offset := by
        intro offset equal
        exact (callerRange_private_window good range equal w windowPointer) rfl
      have finalGet : Space.get after (BRef.blk w) = some array := by
        change after.bytes w = some array
        rw [← restore_output_other_bytes before after pointer made w separate, kept.1]
        exact get
      refine Or.inr ⟨.blk w, 0, array, ?_, finalGet, ?_, ?_⟩
      · rw [window]; exact windowPointer
      · rw [size]; exact bound
      · simpa only [haveCount, next] using values

#print axioms dictionary_caller_output_frame
end Zlib.Inflate.Proofs.WholeEpoch
