import ZlibF.Proof.«uncompr.c.loop-objects»
import ZlibF.Proof.«uncompr.c.writeback-support»

/-!
# Actual ordered uncompress writeback and cleanup

The actual two scalar writes retain the decoder relation. Real inflateEnd then
releases its graph before both actual automatic objects are freed. The returned
cells are exact before the automatic frees, whose heap and live ledger are also
exact. Full initialized wrapper composition and its public format goal remain
separate obligations.
-/

namespace Zlib.Uncompr.Proof.Finish
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Writeback

private theorem read_range {h : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write) : CallerRange h r p n false := by
  rcases range with null | ⟨readable, _, unowned⟩
  · exact Or.inl null
  · exact Or.inr ⟨readable, by simp, unowned⟩

/-- A whole-object frame preserves the exact view of a caller allocation. -/
theorem frame_caller_view {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {off n : Nat} {a : Array UInt8}
    (good : Good h r zs z s) (get : Space.get h ref = some a)
    (range : CallerRange h r (.ref ref off) n false)
    (frame : Frame h after (fun x => StreamRoot r x ∨ InflateOwned zs s x)) :
    Space.get after ref = some a ∧ Space.ro after ref = Space.ro h ref := by
  have outside := fun x root => caller_byte_root_outside good get range (b := x) root
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

theorem frame_caller_object {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {p : BPtr} {n : Nat} {xs : List UInt8} {write : Bool}
    (good : Good h r zs z s) (bytes : Bytes h p n xs) (range : CallerRange h r p n write)
    (frame : Frame h after (fun x => StreamRoot r x ∨ InflateOwned zs s x)) :
    Bytes after p n xs ∧ (write = true → Writable after p n) := by
  rcases bytes with null | ⟨ref, off, a, ptr, get, room, values⟩
  · refine ⟨Or.inl null, ?_⟩
    intro _
    exact Or.inl ⟨null.1, null.2.1⟩
  · subst p
    obtain ⟨newGet, ro⟩ := frame_caller_view good get (read_range range) frame
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

def releasedHeap (h : Heap) (stream reserved : Nat) : Heap :=
  { h with bytes := upd h.bytes reserved none, streams := upd h.streams stream none }

theorem freeLocals_run (h : Heap) (stream reserved : Nat) (z : ZStream) (a : Array UInt8)
    (streamGet : h.streams stream = some z) (reservedGet : h.bytes reserved = some a)
    (writable : h.ro reserved = false) :
    freeLocals (some (.tab stream)) (.ref (.blk reserved) 0) h = .ok ((), releasedHeap h stream reserved) := by
  simp [freeLocals, freeB, freeZStream, reservedGet, writable, streamGet, releasedHeap]

private theorem none_of_cnt {α : Type} {o : Option α} (zero : cnt o = 0) : o = none := by
  cases o <;> simp_all

/-- The two actual automatic frees remove exactly their two allocation roots. -/
theorem released_live (h : Heap) (stream reserved : Nat) (z : ZStream) (a : Array UInt8)
    (uniq : Uniq h) (streamGet : h.streams stream = some z) (reservedGet : h.bytes reserved = some a) :
    LiveChange h (releasedHeap h stream reserved) (fun _ => False)
      (fun x => x = stream ∨ x = reserved) := by
  have byteOnly := Uniq.bytes_only uniq reservedGet
  have distinct : stream ≠ reserved := by
    intro same
    subst stream
    rw [byteOnly.2.1] at streamGet
    cases streamGet
  have count := uniq stream
  simp only [streamGet, cnt_some] at count
  have b : h.bytes stream = none := none_of_cnt (by omega)
  have w : h.words stream = none := none_of_cnt (by omega)
  have gh : h.gzheaders stream = none := none_of_cnt (by omega)
  have ds : h.dstates stream = none := none_of_cnt (by omega)
  have ist : h.istates stream = none := none_of_cnt (by omega)
  have gz : h.gzstates stream = none := none_of_cnt (by omega)
  intro x
  by_cases atStream : x = stream
  · subst x
    simp [releasedHeap, Heap.live, distinct, b, w, gh, ds, ist, gz]
  · by_cases atReserved : x = reserved
    · subst x
      simp [releasedHeap, Heap.live, Ne.symm distinct, byteOnly.1, byteOnly.2.1,
        byteOnly.2.2.1, byteOnly.2.2.2.1, byteOnly.2.2.2.2.1, byteOnly.2.2.2.2.2]
    · simp [releasedHeap, Heap.live, atStream, atReserved]

/-- Releasing the automatic objects retains any scalar cell whose byte root is
outside the reserved allocation. Both cells may still share a caller allocation. -/
theorem released_cell (h : Heap) (stream reserved : Nat) (p : BPtr) (value : UInt64)
    (cell : LengthCell h p value) (outside : ∀ off, p ≠ .ref (.blk reserved) off) :
    LengthCell (releasedHeap h stream reserved) p value := by
  have view {ref : BRef} {off : Nat} {a : Array UInt8}
      (ptr : p = .ref ref off) (get : Space.get h ref = some a) :
      Space.get (releasedHeap h stream reserved) ref = some a := by
    cases ref with
    | blk b =>
      have different : b ≠ reserved := by intro same; subst b; exact outside off ptr
      simpa [Space.get, releasedHeap, different] using get
    | dstate_depth b => exact get
    | str i => exact get
    | st_dist_code => exact get
    | st_length_code => exact get
  constructor
  · rcases cell.1 with null | ⟨ref, off, a, ptr, get, room, values⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, view ptr get, room, values⟩
  · rcases cell.2 with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, view ptr get, ro, room⟩

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl

def resultCode (err : Int32) (remaining : UInt64) : Int32 :=
  if err == Z_STREAM_END then Z_OK
  else if err == Z_NEED_DICT then Z_DATA_ERROR
  else if err == Z_BUF_ERROR && remaining == 0 then Z_DATA_ERROR else err

/-- Both real scalar stores precede the real End and both automatic frees.
The returned scalar evidence is retained on the pre-local-free heap; the final
heap is the exact local release. This is an internal tail theorem, not the public
format contract. -/
theorem finish_safe (h : Heap) (b zs reserved : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (junk : List UInt8)
    (invariant : DefaultStateJ h (.tab b) zs z s) (allocator : DefAlloc z)
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
      DefaultStateJ written (.tab b) zs z s ∧
      LengthCell clean sourceLen (n - (l.len + z.avail_in.toUInt64)) ∧
      LengthCell clean destLen (capacity - (l.left + z.avail_out.toUInt64)) ∧
      LiveChange h written (fun _ => False) (fun _ => False) ∧
      LiveChange written clean (fun _ => False) (InflateOwned zs s) ∧
      Uniq clean ∧ Fresh clean ∧
      clean.streams b = some { z with state := none } ∧
      (∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false) := by
  obtain ⟨mid, written, stores, current, finalAllocator, storeIn, storeOut, cellIn, cellOut, live, ownership⟩ :=
    ordered_length_writeback invariant allocator inputCell outputCell inputRange outputRange separate
      (l.len + z.avail_in.toUInt64) (l.left + z.avail_out.toUInt64)
  have rangeIn := cell_range_of_same_ownership cellIn inputRange ownership
  have rangeOut := cell_range_of_same_ownership cellOut outputRange ownership
  obtain ⟨reservedBytes1, reservedRange1⟩ := ordered_stores_keep_object storeIn storeOut ownership
    reservedBytes reservedRange reservedSource reservedDest
  obtain ⟨clean, endRun, same, unique, fresh, streamGet, allocations, _check⟩ :=
    inflateEnd_safe current.good finalAllocator.2
  have frame : Frame written clean (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) := by
    rw [same]
    exact ZlibF.Spec.Public.InflateEndProof.end_frame current.good.live.hz (windowBlock current.good.inv.win)
  obtain ⟨inputBytes2, inputWrite2⟩ := frame_caller_object current.good cellIn.1 rangeIn frame
  obtain ⟨outputBytes2, outputWrite2⟩ := frame_caller_object current.good cellOut.1 rangeOut frame
  obtain ⟨reservedBytes2, reservedWrite2⟩ := frame_caller_object current.good reservedBytes1 reservedRange1 frame
  obtain ⟨a, reservedGet, reservedRo⟩ : ∃ a, clean.bytes reserved = some a ∧ clean.ro reserved = false := by
    rcases reservedWrite2 rfl with null | ⟨ref, off, a, ptr, get, ro, room⟩
    · cases null.1
    · cases ptr
      exact ⟨a, get, ro⟩
  have cleanup := freeLocals_run clean b reserved _ a streamGet reservedGet reservedRo
  have endLive := allocations (fun x => written.live x) (fun _ => Iff.rfl)
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

#print axioms released_live
#print axioms released_cell
#print axioms finish_safe
#print axioms frame_caller_view
#print axioms frame_caller_object
#print axioms freeLocals_run
end Zlib.Uncompr.Proof.Finish
