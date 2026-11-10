import ZlibF.Proof.«inflate.c.whole-payload-facts-trip-counters»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

private theorem byte_put_static (h : Heap) (dest : BRef) (array : Array UInt8) :
    (Space.put h dest array).static = h.static := by
  cases dest with
  | blk _ => rfl
  | str _ => rfl
  | dstate_depth i =>
    change (match h.dstates i with | some state => _ | none => h).static = h.static
    cases h.dstates i <;> rfl
  | st_dist_code => rfl
  | st_length_code => rfl

private theorem restore_static (h after : Heap) (pointer : BPtr) (made : Nat) :
    (restoreRegions h after [⟨pointer, made⟩]).static = after.static := by
  unfold restoreRegions
  simp only [List.foldl_cons, List.foldl_nil]
  cases pointer with
  | null => rfl
  | ref dest off =>
    change (match (Space.get h dest : Option (Array UInt8)) with
      | none => after | some array => Space.put after dest array).static = after.static
    cases Space.get h dest with
    | none => rfl
    | some array => exact byte_put_static after dest array

/-- The output-prefix frame retains both fixed static tables on every
actual payload branch. -/
theorem PayloadTrip4.statics
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) : after.static = h.static := by
  have statics := trip.outputFrame.1.1
  rw [restore_static] at statics
  exact statics.symm

/-- Selected tables are the owner's codes or the actual fixed tables.
Their cells survive the exact state frame; no arbitrary heap-wide code
view oracle is assumed. -/
theorem PayloadTrip4.selected_views_of_decode_frame
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    (trip : PayloadTrip4 before after regs outcome) (frame : DecodeStateFrame s trip.state) :
    ∀ (ref : CodeRef) (off : Nat), (s.lencode = .ref ref off ∨ s.distcode = .ref ref off) →
      (Space.get after ref : Option (Array Code)) = Space.get h ref := by
  intro ref off pointer
  rcases before.origin.good.inv.ptr.2 with ⟨i, j, lens, dists, _⟩ | ⟨lens, dists⟩
  · have codeEq : trip.state.codes = s.codes := by rw [frame]
    have same : (Space.get after (CodeRef.istate_codes zs) : Option (Array Code)) = Space.get h (CodeRef.istate_codes zs) := by
      change (after.istates zs).map (·.codes) = (h.istates zs).map (·.codes)
      rw [trip.origin.good.live.hs, before.origin.good.live.hs, Option.map_some, Option.map_some, codeEq]
    rcases pointer with pointer | pointer
    · rw [lens] at pointer
      cases pointer
      exact same
    · rw [dists] at pointer
      cases pointer
      exact same
  · rcases pointer with pointer | pointer
    · rw [lens] at pointer
      cases pointer
      change some after.static.lenfix = some h.static.lenfix
      rw [trip.statics]
    · rw [dists] at pointer
      cases pointer
      change some after.static.distfix = some h.static.distfix
      rw [trip.statics]

/-- Existing installed semantic tables and their actual branch/query-take
properties transport through one real slow payload trip. -/
theorem PayloadTrip4.slow_tables
    {c : Ctx} {entryHeap h after : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l regs : IL} {base : DataLog} {raw : List UInt8}
    {outcome : Except Ex Unit} {before : CallFacts c entryHeap h r zs entryZ z s l base raw}
    {L D : List Nat}
    (trip : PayloadTrip4 before after regs outcome) (mode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (tables : TableBinding h s L D) : TableBinding after trip.state L D := by
  have frame := trip.slow_frame mode slow
  have views := trip.selected_views_of_decode_frame frame
  obtain ⟨⟨lengths, distances⟩, ⟨lflags, dflags⟩, ⟨ltake, dtake⟩⟩ := tables
  have kept : TableBinding after s L D := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · obtain ⟨ref, off, array, used, ptr, get, inv, stable⟩ := lengths
      exact ⟨ref, off, array, used, ptr, (views ref off (Or.inl ptr)).trans get, inv, stable⟩
    · obtain ⟨ref, off, array, used, ptr, get, inv, stable⟩ := distances
      exact ⟨ref, off, array, used, ptr, (views ref off (Or.inr ptr)).trans get, inv, stable⟩
    · obtain ⟨ref, off, array, ptr, get, flags⟩ := lflags
      exact ⟨ref, off, array, ptr, (views ref off (Or.inl ptr)).trans get, flags⟩
    · obtain ⟨ref, off, array, ptr, get, flags⟩ := dflags
      exact ⟨ref, off, array, ptr, (views ref off (Or.inr ptr)).trans get, flags⟩
    · obtain ⟨ref, off, array, ptr, get, take⟩ := ltake
      exact ⟨ref, off, array, ptr, (views ref off (Or.inl ptr)).trans get, take⟩
    · obtain ⟨ref, off, array, ptr, get, take⟩ := dtake
      exact ⟨ref, off, array, ptr, (views ref off (Or.inr ptr)).trans get, take⟩
  rw [frame]
  exact kept

#print axioms PayloadTrip4.statics
#print axioms PayloadTrip4.selected_views_of_decode_frame
#print axioms PayloadTrip4.slow_tables
end Zlib.Inflate.Proofs.WholeEpoch
