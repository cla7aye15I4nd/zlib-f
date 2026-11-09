import ZlibF.Proof.«uncompr.c.finish»
import ZlibF.Proof.«uncompr.c.local-writeback-support»
import ZlibF.Proof.«inflate.c.local-end»

/-! Original ordered utility tail with local decoder storage.
The scalar stores, actual End and both automatic frees stay in C source order. -/
namespace Zlib.Uncompr.Proof.LocalFinish
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Writeback
open Zlib.Uncompr.Proof.Finish
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem slot_none {α : Type} {o : Option α} (zero : cnt o = 0) : o = none := by
  cases o <;> simp_all

private theorem caller_byte_root_not_stream_local
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs off b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {a : Array UInt8}
    (good : LocalGood h cutoff r zs z s) (roots : LocalRoots cutoff r zs s)
    (get : Space.get h ref = some a) (root : ByteRoot (.ref ref off) b) : ¬ StreamRoot r b := by
  intro streamRoot
  have lower := roots.stream b streamRoot
  have absent : h.streams b = none ∧ h.gzstates b = none := by
    cases ref with
    | blk i =>
      change b = i at root
      subst b
      have slots := good.unique.bytes_only lower get
      exact ⟨slots.2.1, slots.2.2.2.2.2⟩
    | dstate_depth i =>
      change b = i at root
      subst b
      cases state : h.dstates i with
      | none => simp [Space.get, state] at get
      | some value =>
        have bound := good.unique i lower
        simp only [state, cnt_some] at bound
        exact ⟨slot_none (by omega), slot_none (by omega)⟩
    | str i => cases root
    | st_dist_code => cases root
    | st_length_code => cases root
  cases r with
  | tab i =>
    change b = i at streamRoot
    have live := good.live.hz
    simp only [ZStreamRef.get, ← streamRoot, absent.1] at live
    contradiction
  | in_gzstate_strm i =>
    change b = i at streamRoot
    have live := good.live.hz
    simp only [ZStreamRef.get, ← streamRoot, absent.2, Option.map_none] at live
    contradiction

private theorem caller_byte_root_outside_local
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs off count b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {a : Array UInt8}
    (good : LocalGood h cutoff r zs z s) (roots : LocalRoots cutoff r zs s)
    (get : Space.get h ref = some a) (range : CallerRange h r (.ref ref off) count false)
    (root : ByteRoot (.ref ref off) b) : ¬ (StreamRoot r b ∨ InflateOwned zs s b) := by
  rcases range with null | ⟨_, _, outside⟩
  · cases null
  · rintro (stream | owned)
    · exact caller_byte_root_not_stream_local good roots get root stream
    · exact outside b root ((good.streamOwned_iff b).mpr owned)

private theorem read_range {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write) : CallerRange h r p n false := by
  rcases range with null | ⟨readable, _, unowned⟩
  · exact Or.inl null
  · exact Or.inr ⟨readable, by simp, unowned⟩

/-- A whole-object frame preserves the exact view of a caller allocation. -/
theorem frame_caller_view {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {off n : Nat} {a : Array UInt8}
    (good : LocalGood h cutoff r zs z s) (roots : LocalRoots cutoff r zs s) (get : Space.get h ref = some a)
    (range : CallerRange h r (.ref ref off) n false)
    (frame : Frame h after (fun x => StreamRoot r x ∨ InflateOwned zs s x)) :
    Space.get after ref = some a ∧ Space.ro after ref = Space.ro h ref := by
  have outside := fun x root => caller_byte_root_outside_local good roots get range (b := x) root
  cases ref with
  | blk b =>
    have live : h.live b := Or.inl (by simp [show h.bytes b = some a from get])
    have slot := frame.2.2.2.2.2 b live (outside b rfl)
    exact ⟨slot.1.trans get, slot.2.2.2.2.2.2.2⟩
  | dstate_depth b =>
    have live : h.live b := by
      cases state : h.dstates b with
      | none => simp [Space.get, state] at get
      | some state => simp [Heap.live, state]
    have slot := frame.2.2.2.2.2 b live (outside b rfl)
    constructor
    · simpa only [Space.get, slot.2.2.2.2.1] using get
    · rfl
  | str i => exact ⟨get, rfl⟩
  | st_dist_code => exact ⟨by simpa only [Space.get, ← frame.1] using get, rfl⟩
  | st_length_code => exact ⟨by simpa only [Space.get, ← frame.1] using get, rfl⟩

theorem frame_caller_object {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {p : BPtr} {n : Nat} {xs : List UInt8} {write : Bool}
    (good : LocalGood h cutoff r zs z s) (roots : LocalRoots cutoff r zs s) (bytes : Bytes h p n xs) (range : CallerRange h r p n write)
    (frame : Frame h after (fun x => StreamRoot r x ∨ InflateOwned zs s x)) :
    Bytes after p n xs ∧ (write = true → Writable after p n) := by
  rcases bytes with null | ⟨ref, off, a, ptr, get, room, values⟩
  · refine ⟨Or.inl null, ?_⟩
    intro _
    exact Or.inl ⟨null.1, null.2.1⟩
  · subst p
    obtain ⟨newGet, ro⟩ := frame_caller_view good roots get (read_range range) frame
    refine ⟨Or.inr ⟨ref, off, a, rfl, newGet, room, values⟩, ?_⟩
    intro writing
    rcases range with null | ⟨_, writable, _⟩
    · cases null
    · rcases writable writing with null | ⟨ref', off', a', ptr, get', write', room'⟩
      · cases null.1
      · cases ptr
        have same := Option.some.inj (get'.symm.trans get)
        subst a'
        exact Or.inr ⟨ref, off, a, rfl, newGet, ro.trans write', room'⟩

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl

theorem finish_safe (h : Heap) (cutoff b zs reserved : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (junk : List UInt8)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (inputRange : CallerRange h (.tab b) sourceLen 8 true)
    (outputRange : CallerRange h (.tab b) destLen 8 true)
    (separate : Separate sourceLen 8 destLen 8)
    (reservedBytes : Bytes h (.ref (.blk reserved) 0) 8 junk)
    (reservedRange : CallerRange h (.tab b) (.ref (.blk reserved) 0) 8 true)
    (reservedSource : Separate (.ref (.blk reserved) 0) 8 sourceLen 8)
    (reservedDest : Separate (.ref (.blk reserved) 0) 8 destLen 8) :
    ∃ mid written clean,
      C.run (finish (some (.tab b)) (.ref (.blk reserved) 0) destLen sourceLen l) h =
        .ok (resultCode l.err (l.len + z.avail_in.toUInt64), releasedHeap clean b reserved) ∧
      Store h sourceLen (lengthBytes (n - (l.len + z.avail_in.toUInt64))) mid ∧
      Store mid destLen (lengthBytes (capacity - (l.left + z.avail_out.toUInt64))) written ∧
      LocalStateJ written cutoff (.tab b) zs z s ∧
      LengthCell clean sourceLen (n - (l.len + z.avail_in.toUInt64)) ∧
      LengthCell clean destLen (capacity - (l.left + z.avail_out.toUInt64)) ∧
      LiveChange h written (fun _ => False) (fun _ => False) ∧
      LiveChange written clean (fun _ => False) (InflateOwned zs s) ∧
      UniqueFrom clean cutoff ∧ Fresh clean ∧
      clean.streams b = some { z with state := none } ∧
      (∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false) := by
  obtain ⟨mid, written, stores, current, finalAllocator, storeIn, storeOut, cellIn, cellOut, live, ownership⟩ :=
    LocalWriteback.ordered_length_writeback invariant allocator inputCell outputCell inputRange outputRange separate
      (l.len + z.avail_in.toUInt64) (l.left + z.avail_out.toUInt64)
  have rangeIn := cell_range_of_same_ownership cellIn inputRange ownership
  have rangeOut := cell_range_of_same_ownership cellOut outputRange ownership
  obtain ⟨reservedBytes1, reservedRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    reservedBytes reservedRange reservedSource reservedDest
  obtain ⟨clean, endRun, same, fresh, unique, streamGet, endLive, frame, _, _⟩ :=
    inflateEnd_local current.good current.roots finalAllocator.2
  obtain ⟨inputBytes2, inputWrite2⟩ := frame_caller_object current.good current.roots cellIn.1 rangeIn frame
  obtain ⟨outputBytes2, outputWrite2⟩ := frame_caller_object current.good current.roots cellOut.1 rangeOut frame
  obtain ⟨reservedBytes2, reservedWrite2⟩ := frame_caller_object current.good current.roots reservedBytes1 reservedRange1 frame
  obtain ⟨a, reservedGet, reservedRo⟩ : ∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false := by
    rcases reservedWrite2 rfl with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  have cleanup := freeLocals_run clean b reserved _ a streamGet reservedGet reservedRo
  refine ⟨mid, written, clean, ?_, storeIn, storeOut, current,
    ⟨inputBytes2, inputWrite2 rfl⟩, ⟨outputBytes2, outputWrite2 rfl⟩, live, ?_,
    unique, fresh, streamGet, ⟨a, reservedGet, reservedRo⟩⟩
  · have ld : Zlib.Gzguts.ldZ (some (.tab b)) h = .ok (z, h) := by
      simp [Zlib.Gzguts.ldZ, ldZ_eq, show ZStreamRef.get h (.tab b) = some z from invariant.good.live.hz]
    change finish (some (.tab b)) (.ref (.blk reserved) 0) destLen sourceLen l h = _
    unfold finish
    rw [bind_app, ld]
    dsimp only
    have seq : ((do
      (do store64 sourceLen ((← load64 sourceLen) - (l.len + z.avail_in.toUInt64))
          store64 destLen ((← load64 destLen) - (l.left + z.avail_out.toUInt64)))
      let _ ← Zlib.Inflate.inflateEnd (some (.tab b))
      freeLocals (some (.tab b)) (.ref (.blk reserved) 0)
      pure (resultCode l.err (l.len + z.avail_in.toUInt64))) h) =
        .ok (resultCode l.err (l.len + z.avail_in.toUInt64), releasedHeap clean b reserved) := by
      simp only [C.run] at endRun
      rw [bind_app, stores]
      dsimp only
      rw [bind_app, endRun]
      dsimp only
      rw [bind_app, cleanup]
      rfl
    simpa only [m_bind_assoc, resultCode] using seq
  · intro x
    simpa [LiveChange, InflateOwned, OwnedBy, WinBlk, and_comm] using endLive x


#print axioms finish_safe
end Zlib.Uncompr.Proof.LocalFinish
