import ZlibF.Proof.«deflate.c.universal-ops-prime»
import ZlibF.Proof.«deflate.c.universal-stored-io»
import ZlibF.Proof.«deflate.c.public-getdict»
import ZlibF.Spec.Public.Streams

/-!
# deflate.c: a caller buffer that the model views inside library storage

A writable caller range outside this stream's blocks (`CallerRange`) is one of two views
(`OutputKind`): a byte block, or the `depth` array of another deflate state record (the
`dstate_depth` view; `zlib.h` does not forbid a caller buffer there). `DInv` constrains only this
stream's state record and its own blocks, so a same-size write into either view keeps it: this is
a frame argument (`caller_view_write`). The other stream's `depth` is scratch storage that
`build_tree` writes before it reads (`trees.c`); no statement of this stream depends on it.

`caller_view_write` is the shape for every operation that writes a caller buffer which may lie in
library storage. `deflateGetDictionary` (`getDictionary_view`, `step_getDictionary`) is its first
user: the history needs no clause that keeps its destination out of deflate state records.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

theorem caller_view_put_put (h : Heap) (ref : BRef) (a a' : Array UInt8) :
    Space.put (Space.put h ref a) ref a' = Space.put h ref a' := by
  cases ref with
  | blk b => simp [Space.put, upd_upd]
  | str i => simp [Space.put]
  | dstate_depth b =>
    cases e : h.dstates b with
    | none => simp [Space.put, e]
    | some st => simp [Space.put, e, upd_upd]
  | st_dist_code => simp [Space.put]
  | st_length_code => simp [Space.put]

theorem caller_view_put_self {h : Heap} {ref : BRef} {a : Array UInt8} (g : Space.get h ref = some a) :
    Space.put h ref a = h := by
  cases ref with
  | blk b => simp only [Space.get] at g; simp [Space.put, upd_self _ _ _ g]
  | str i => simp [Space.put]
  | dstate_depth b =>
    cases e : h.dstates b with
    | none => simp [Space.get, e] at g
    | some st =>
      have same : st.depth = a := by simpa [Space.get, e] using g
      rw [← same]
      simp [Space.put, e, upd_self _ _ _ e]
  | st_dist_code => simp [Space.put]
  | st_length_code => simp [Space.put]

/-- A byte block that holds bytes is not the stream's record. -/
theorem byte_block_not_root {h : Heap} {r : ZStreamRef} {ds ob : Nat} {z : ZStream} {d : DeflateState}
    {a : Array UInt8} (good : DGood h r ds z d) (get : h.bytes ob = some a) : ¬ StreamRoot r ob := by
  have absent := good.uniq.bytes_only get
  cases r with
  | tab i =>
    intro eq
    change ob = i at eq
    have live := good.live.hz
    simp only [ZStreamRef.get, ← eq, absent.2.1] at live
    contradiction
  | in_gzstate_strm i =>
    intro eq
    change ob = i at eq
    have live := good.live.hz
    simp only [ZStreamRef.get, ← eq, absent.2.2.2.2.2, Option.map_none] at live
    contradiction

/-- A writable caller range outside the stream is a byte block outside the stream or the `depth`
array of another deflate state record, with room for the range. -/
theorem caller_view_of_range {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {p : BPtr} {n : Nat} {ref : BRef} {off : Nat} (good : DGood h r ds z d)
    (range : CallerRange h r p n true) (pointer : p = .ref ref off) :
    ∃ old, Space.get h ref = some old ∧ Space.ro h ref = false ∧ off + n ≤ old.size ∧
      OutputKind h r ds d ref := by
  subst pointer
  have range0 := range
  rcases range with null | ⟨⟨xs, bytes⟩, writable, notOwned⟩
  · cases null
  rcases bytes with ⟨null, _, _⟩ | ⟨q', i, a, eq, get, fit, _⟩
  · cases null
  cases eq
  have write := writable rfl
  rcases writable rfl with ⟨null, _⟩ | ⟨q2, i2, a2, eq2, get2, ro2, _⟩
  · cases null
  cases eq2
  refine ⟨a, get, ro2, by omega, ?_⟩
  rcases writable_reference_cases write with ⟨b, rfl⟩ | ⟨owner, rfl⟩
  · refine Or.inl ⟨b, rfl, ?_⟩
    rintro (root | owned)
    · exact byte_block_not_root good get root
    · exact notOwned b rfl ((stream_owned_deflate good b).2 owned)
  · cases e : h.dstates owner with
    | none =>
      change (h.dstates owner).map (·.depth) = some a at get
      rw [e] at get; cases get
    | some foreign =>
      exact Or.inr ⟨owner, foreign, rfl, e, foreign_depth_owner_not_private good range0⟩

/-- **A write into a caller view.** A same-size array written into a caller view (`OutputKind`),
equal to the old one outside `[off, off + n)`, keeps `DInv`, the stream record and this stream's
state record, the frame of a caller region `[off, off + len)` with `n ≤ len`, and the live blocks. -/
theorem caller_view_write {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {ref : BRef} {off n len : Nat} {old new : Array UInt8}
    (inv : DInv h r ds z d) (get : Space.get h ref = some old) (kind : OutputKind h r ds d ref)
    (size : new.size = old.size) (keep : ∀ j, ¬ (off ≤ j ∧ j < off + n) → new[j]? = old[j]?)
    (cover : n ≤ len) (changed : Nat → Prop) :
    DInv (Space.put h ref new) r ds z d ∧ r.get (Space.put h ref new) = r.get h ∧
      (Space.put h ref new).dstates ds = h.dstates ds ∧
      BufferFrame h (Space.put h ref new) changed [⟨.ref ref off, len⟩] ∧
      LiveChange h (Space.put h ref new) (fun b => StreamOwned (Space.put h ref new) r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned (Space.put h ref new) r b) := by
  obtain ⟨put, getNew⟩ := output_put inv.good get kind size
  have inv' : DInv (Space.put h ref new) r ds z d :=
    inv.transfer put.good put.static (fun b o => put.private_ b (Or.inr o)) (fun b _ => by rw [put.words])
  have restored : restoreRegions h (Space.put h ref new) [⟨.ref ref off, len⟩] = h := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil, get]
    rw [caller_view_put_put, caller_view_put_self get]
  have liveSame : ∀ b, (Space.put h ref new).live b ↔ h.live b := by
    intro b
    rcases kind with ⟨ob, rfl, -⟩ | ⟨owner, foreign, rfl, getF, -⟩
    · have g : h.bytes ob = some old := get
      by_cases e : b = ob
      · subst e; simp [Heap.live, Space.put, upd_same, g]
      · simp [Heap.live, Space.put, upd_ne _ _ _ _ e]
    · rw [BRef.put_dstate_depth getF]
      by_cases e : b = owner
      · subst e; simp [Heap.live, setD, upd_same, getF]
      · simp [Heap.live, setD, upd_ne _ _ _ _ e]
  refine ⟨inv', put.stream, put.state, ⟨?_, ?_⟩, ?_⟩
  · rw [restored]; exact frame_refl h changed
  · intro region mem q o a pointer old'
    simp only [List.mem_singleton] at mem
    subst region
    have eqs := Ptr.ref.inj pointer
    cases eqs.1
    cases eqs.2
    rw [get] at old'
    cases old'
    refine ⟨new, getNew, size, fun j _ notCovered => keep j fun inside => notCovered ?_⟩
    exact ⟨⟨.ref ref off, len⟩, List.mem_singleton.mpr rfl, off, rfl, inside.1, by change j < off + len; omega⟩
  · intro y
    rw [liveSame y]
    constructor
    · intro live
      exact Or.inl ⟨live, fun ⟨owned, not⟩ => not ((inv'.owned y).2 ((inv.owned y).1 owned))⟩
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact owned_live inv.good ((inv'.owned y).1 owned)

/-- **`deflateGetDictionary` into any writable caller range** outside the stream, a byte block or
the `depth` array of another deflate state record. The call returns `Z_OK`, keeps `DInv`, leaves
the stream and its state record unchanged, writes only the destination range, and allocates and
frees nothing. -/
theorem getDictionary_view {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (dictionary : BPtr) (hasDictLength : Bool)
    (range : CallerRange h r dictionary (min d.w_size.toNat (d.strstart.toNat + d.lookahead.toNat)) true)
    (changed : Nat → Prop) :
    ∃ after, C.run (deflateGetDictionary (some r) dictionary hasDictLength) h =
        .ok ((Z_OK, if hasDictLength then some (dictLen d) else none), after) ∧
      DInv after r ds z d ∧ r.get after = r.get h ∧ after.dstates ds = h.dstates ds ∧
      BufferFrame h after changed [⟨dictionary, 32768⟩] ∧
      LiveChange h after (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  have hI := inv.good.inv
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  obtain ⟨wa, hwa, hwsz⟩ := hB.wa
  have hws : d.w_size.toNat ≤ 32768 := by
    have := hI.wsize; have := hI.wbits_hi
    have : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hI.wbits_hi
    omega
  have hfill := inv.shape.room
  have hlen := dictLen_toNat hI.wsz hws hfill
  have hwsz' : wa.size = d.window_size.toNat := by have := hI.wsz; omega
  by_cases hn : dictionary = .null ∨ dictLen d = 0
  · have restored : restoreRegions h h [⟨dictionary, 32768⟩] = h := by
      rcases dictionary with _ | ⟨q', o⟩
      · rfl
      · simp only [restoreRegions, List.foldl_cons, List.foldl_nil]
        cases g : Space.get h q' with
        | none => rfl
        | some a => exact caller_view_put_self g
    refine ⟨h, by rw [C.run]; exact deflateGetDictionary_run_nocopy inv.good.live dictionary hasDictLength hn,
      inv, rfl, rfl, ⟨by rw [restored]; exact frame_refl h changed, ?_⟩, ?_⟩
    · intro region _ q' o a _ g
      exact ⟨a, g, rfl, fun _ _ _ => rfl⟩
    · intro y
      constructor
      · intro live
        exact Or.inl ⟨live, fun ⟨owned, not⟩ => not owned⟩
      · rintro (⟨live, _⟩ | ⟨owned, _⟩)
        · exact live
        · exact owned_live inv.good ((inv.owned y).1 owned)
  · have hnn : dictionary ≠ .null := fun e => hn (Or.inl e)
    have hne : dictLen d ≠ 0 := fun e => hn (Or.inr e)
    obtain ⟨ref, off, pointer⟩ : ∃ ref off, dictionary = .ref ref off := by
      rcases dictionary with _ | ⟨ref, off⟩
      · exact absurd rfl hnn
      · exact ⟨ref, off, rfl⟩
    obtain ⟨da, getD, ro, room, kind⟩ := caller_view_of_range inv.good range pointer
    have hdis : ref ≠ .blk w ∨
        off + (dictLen d).toNat ≤ d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat ∨
        d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat + (dictLen d).toNat ≤ off := by
      refine Or.inl ?_
      rcases kind with ⟨ob, rfl, outside⟩ | ⟨owner, _, rfl, _, _⟩
      · intro e
        cases e
        exact outside (Or.inr (Or.inr (Or.inl hB.win)))
      · intro e; cases e
    have run := deflateGetDictionary_run_copy_general inv.good.live hB hfill dictionary hasDictLength
      pointer getD ro (by omega) hwa hlen hne hdis hwsz'
    have room' : off + (dictLen d).toNat ≤ da.size := by omega
    obtain ⟨invA, str, dst, frame, live⟩ := caller_view_write (len := 32768) (n := (dictLen d).toNat)
      (new := copyRange da wa off (d.strstart.toNat + d.lookahead.toNat - (dictLen d).toNat) (dictLen d).toNat)
      inv getD kind
      (size_copyRange _ _ _ _ _)
      (fun j nin => by rw [getElem?_copyRange _ _ _ _ _ _ room', if_neg nin]) (by omega) changed
    refine ⟨_, by rw [C.run]; exact run, invA, str, dst, ?_, live⟩
    rw [pointer]; exact frame

/-- `deflateGetDictionary` keeps the invariant, in the form of `operation_step`, for every
destination the history admits (`CallerRange`). -/
theorem step_getDictionary {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (dictionary : BPtr) (hasDictLength : Bool)
    (range : CallerRange h r dictionary (min d.w_size.toNat (d.strstart.toNat + d.lookahead.toNat)) true) :
    StepOk h r (.deflateGetDictionary (some r) dictionary hasDictLength) := by
  obtain ⟨after, run, invA, -, -, frame, live⟩ := getDictionary_view inv dictionary hasDictLength range _
  exact ⟨_, after, heapCall_run run, ⟨ds, z, d, invA⟩, frame, live⟩

end Zlib.Deflate.Universal
