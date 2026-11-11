import ZlibF.Proof.«inflate.c.call-default»
import ZlibF.Proof.«inflate.c.check-dispatch»
import ZlibF.Proof.«crc32.c.views»

/-!
# inflate.c: the heap footprint of the gzip header modes

The gzip header modes `FLAGS` .. `HCRC` write the stream and state records,
the local `hbuf` array, the attached `gz_header` record, and bytes inside the
caller regions that record names (`extra`, `name`, `comment`). This module
gives the interface definitions of the gzip header dispatch, a pointwise
footprint relation `HeaderFoot` between the heap at the start of the dispatch
and the current heap, one lemma per kind of write that keeps it, and the
conversion of `HeaderFoot` into the public `BufferFrame` and `LiveChange`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Interface definitions of the gzip header dispatch -/

/-- The local `unsigned char hbuf[4]` of `inflate()`: a writable four-byte array. -/
def LocalHbuf (c : Ctx) (h : Heap) : Prop :=
  ∃ b a, c.hbuf = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ a.size = 4 ∧ h.ro b = false

/-- The state fields the gzip header modes may write. -/
def GzipHeaderStateFrame (before after : InflateState) : Prop :=
  after = { before with
    mode := after.mode
    flags := after.flags
    check := after.check
    length := after.length }

/-- The heap footprint of one gzip header dispatch: the stream and state
records, the local array, the attached header record, and the caller
regions that record names; no allocation or release. -/
def GzipHeaderFootprint (c : Ctx) (r : ZStreamRef) (zs : Nat) (s : InflateState)
    (h after : Heap) : Prop :=
  BufferFrame h after
      (fun b => StreamRoot r b ∨ b = zs ∨ c.hbuf = .ref (.blk b) 0 ∨ s.head = some (.tab b))
      (HeaderRegions h s.head) ∧
    LiveChange h after (fun _ => False) (fun _ => False)

/-- The library constants include the CRC-32 tables. -/
theorem LibraryGlobals.statics {h : Heap} (globals : LibraryGlobals h) :
    Zlib.Crc32.Proofs.StaticsOK h := by
  unfold LibraryGlobals at globals
  rw [Zlib.Crc32.Proofs.StaticsOK, globals]
  exact ⟨rfl, rfl⟩

/-! ## `restoreRegions`, field by field -/

/-- A region list starts a region on this byte view. -/
def RegionRoot (regions : List Region) (ref : BRef) : Prop :=
  ∃ region, region ∈ regions ∧ ∃ off, region.pointer = .ref ref off

/-- A region list covers this byte of this view. -/
def RegionCovers (regions : List Region) (ref : BRef) (j : Nat) : Prop :=
  ∃ region, region ∈ regions ∧ region.covers ref j

theorem restoreRegions_cons (before after : Heap) (region : Region) (rest : List Region) :
    restoreRegions before after (region :: rest) =
      restoreRegions before (match region.pointer with
        | .null => after
        | .ref ref _ => match (Space.get before ref : Option (Array UInt8)) with
          | none => after
          | some a => Space.put after ref a) rest := rfl

/-- The tables that `restoreRegions` never touches. -/
theorem restoreRegions_other (before after : Heap) (regions : List Region) :
    let r := restoreRegions before after regions
    r.static = after.static ∧ r.allocOk = after.allocOk ∧ r.garbage = after.garbage ∧
      r.nextBlk = after.nextBlk ∧ r.nalloc = after.nalloc ∧ r.words = after.words ∧
      r.streams = after.streams ∧ r.gzheaders = after.gzheaders ∧ r.istates = after.istates ∧
      r.gzstates = after.gzstates ∧ r.ro = after.ro := by
  induction regions generalizing after with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons region rest ih =>
    rw [restoreRegions_cons]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := ih (match region.pointer with
        | .null => after
        | .ref ref _ => match (Space.get before ref : Option (Array UInt8)) with
          | none => after
          | some a => Space.put after ref a)
    refine ⟨a1.trans ?_, a2.trans ?_, a3.trans ?_, a4.trans ?_, a5.trans ?_, a6.trans ?_,
      a7.trans ?_, a8.trans ?_, a9.trans ?_, a10.trans ?_, a11.trans ?_⟩ <;>
    · rcases region with ⟨pointer, length⟩
      cases pointer with
      | null => rfl
      | ref ref off =>
        simp only []
        cases (Space.get before ref : Option (Array UInt8)) with
        | none => rfl
        | some a =>
          cases ref <;> simp only [Space.put] <;> (try split) <;> rfl

open Classical in
/-- The byte table after `restoreRegions`. -/
theorem restoreRegions_bytes (before after : Heap) (regions : List Region) (b : Nat) :
    (restoreRegions before after regions).bytes b =
      if RegionRoot regions (.blk b) ∧ before.bytes b ≠ none then before.bytes b else after.bytes b := by
  induction regions generalizing after with
  | nil => simp [restoreRegions, RegionRoot]
  | cons region rest ih =>
    rw [restoreRegions_cons, ih]
    rcases region with ⟨pointer, length⟩
    by_cases inRest : RegionRoot rest (.blk b) ∧ before.bytes b ≠ none
    · have all : RegionRoot (⟨pointer, length⟩ :: rest) (.blk b) ∧ before.bytes b ≠ none := by
        obtain ⟨⟨region, member, off, ptr⟩, present⟩ := inRest
        exact ⟨⟨region, List.mem_cons_of_mem _ member, off, ptr⟩, present⟩
      rw [if_pos inRest, if_pos all]
    · rw [if_neg inRest]
      cases pointer with
      | null =>
        have absent : ¬ (RegionRoot (⟨.null, length⟩ :: rest) (.blk b) ∧ before.bytes b ≠ none) := by
          rintro ⟨⟨region, member, off, ptr⟩, present⟩
          rcases List.mem_cons.mp member with head | tail
          · subst head; cases ptr
          · exact inRest ⟨⟨region, tail, off, ptr⟩, present⟩
        rw [if_neg absent]
      | ref ref off =>
        simp only []
        by_cases here : ref = .blk b
        · subst here
          cases get : before.bytes b with
          | none =>
            rw [if_neg (fun ⟨_, present⟩ => present rfl)]
            change (match (before.bytes b : Option (Array UInt8)) with
              | none => after | some a => Space.put after (BRef.blk b) a).bytes b = after.bytes b
            rw [get]
          | some a =>
            rw [if_pos ⟨⟨_, List.mem_cons_self, off, rfl⟩, by simp⟩]
            change (match (before.bytes b : Option (Array UInt8)) with
              | none => after | some a => Space.put after (BRef.blk b) a).bytes b = some a
            rw [get]
            simp [Space.put]
        · have absent : ¬ (RegionRoot (⟨.ref ref off, length⟩ :: rest) (.blk b) ∧ before.bytes b ≠ none) := by
            rintro ⟨⟨region, member, off', ptr⟩, present⟩
            rcases List.mem_cons.mp member with head | tail
            · subst head
              cases ptr
              exact here rfl
            · exact inRest ⟨⟨region, tail, off', ptr⟩, present⟩
          rw [if_neg absent]
          cases (Space.get before ref : Option (Array UInt8)) with
          | none => rfl
          | some a =>
            cases ref with
            | blk id =>
              have ne : b ≠ id := fun e => here (by rw [e])
              simp [Space.put, upd_ne _ _ _ _ ne]
            | _ => simp only [Space.put] <;> (try split) <;> rfl

open Classical in
/-- The deflate-state table after `restoreRegions`: only the `depth` arrays of
region roots come back. -/
theorem restoreRegions_dstates (before after : Heap) (regions : List Region) (b : Nat) :
    (restoreRegions before after regions).dstates b =
      if RegionRoot regions (.dstate_depth b) then
        (match before.dstates b, after.dstates b with
          | some d0, some d => some { d with depth := d0.depth }
          | _, current => current)
      else after.dstates b := by
  induction regions generalizing after with
  | nil => simp [restoreRegions, RegionRoot]
  | cons region rest ih =>
    rw [restoreRegions_cons, ih]
    rcases region with ⟨pointer, length⟩
    -- the dstate entry after the first restoring step
    have step : (match (⟨pointer, length⟩ : Region).pointer with
        | .null => after
        | .ref ref _ => match (Space.get before ref : Option (Array UInt8)) with
          | none => after
          | some a => Space.put after ref a).dstates b =
        if (∃ off, pointer = .ref (.dstate_depth b) off) then
          (match before.dstates b, after.dstates b with
            | some d0, some d => some { d with depth := d0.depth }
            | _, current => current)
        else after.dstates b := by
      cases pointer with
      | null => simp
      | ref ref off =>
        simp only []
        by_cases here : ref = .dstate_depth b
        · subst here
          rw [if_pos ⟨off, rfl⟩]
          cases d0 : before.dstates b with
          | none => simp [Space.get, d0]
          | some d0v =>
            cases d : after.dstates b with
            | none => simp [Space.get, Space.put, d0, d]
            | some dv => simp [Space.get, Space.put, d0, d]
        · have absent : ¬ ∃ off', Ptr.ref ref off = .ref (.dstate_depth b) off' := by
            rintro ⟨off', e⟩
            cases e
            exact here rfl
          rw [if_neg absent]
          cases (Space.get before ref : Option (Array UInt8)) with
          | none => rfl
          | some a =>
            cases ref with
            | dstate_depth id =>
              have ne : b ≠ id := fun e => here (by rw [e])
              simp only [Space.put]
              split <;> simp [upd_ne _ _ _ _ ne]
            | _ => simp only [Space.put]
    by_cases inRest : RegionRoot rest (.dstate_depth b)
    · have all : RegionRoot (⟨pointer, length⟩ :: rest) (.dstate_depth b) := by
        obtain ⟨region, member, off, ptr⟩ := inRest
        exact ⟨region, List.mem_cons_of_mem _ member, off, ptr⟩
      rw [if_pos inRest, if_pos all, step]
      by_cases here : ∃ off, pointer = .ref (.dstate_depth b) off
      · rw [if_pos here]
        cases before.dstates b <;> cases after.dstates b <;> simp
      · rw [if_neg here]
    · rw [if_neg inRest, step]
      by_cases here : ∃ off, pointer = .ref (.dstate_depth b) off
      · obtain ⟨off, ptr⟩ := here
        have all : RegionRoot (⟨pointer, length⟩ :: rest) (.dstate_depth b) :=
          ⟨_, List.mem_cons_self, off, ptr⟩
        rw [if_pos ⟨off, ptr⟩, if_pos all]
      · have absent : ¬ RegionRoot (⟨pointer, length⟩ :: rest) (.dstate_depth b) := by
          rintro ⟨region, member, off, ptr⟩
          rcases List.mem_cons.mp member with head | tail
          · subst head; exact here ⟨off, ptr⟩
          · exact inRest ⟨region, tail, off, ptr⟩
        rw [if_neg here, if_neg absent]

/-! ## The pointwise footprint relation -/

/-- The current heap `h` differs from the entry heap `h0` only in the records
of `changed` blocks and in caller bytes covered by `regions`; sizes, the
allocation state and all other objects are those of `h0`. -/
structure HeaderFoot (changed : Nat → Prop) (regions : List Region) (h0 h : Heap) : Prop where
  static : h.static = h0.static
  allocOk : h.allocOk = h0.allocOk
  garbage : h.garbage = h0.garbage
  nextBlk : h.nextBlk = h0.nextBlk
  nalloc : h.nalloc = h0.nalloc
  shape : Shape h0 h
  words : ∀ b, ¬ changed b → h.words b = h0.words b
  streams : ∀ b, ¬ changed b → h.streams b = h0.streams b
  gzheaders : ∀ b, ¬ changed b → h.gzheaders b = h0.gzheaders b
  istates : ∀ b, ¬ changed b → h.istates b = h0.istates b
  gzstates : ∀ b, ¬ changed b → h.gzstates b = h0.gzstates b
  ro : h.ro = h0.ro
  bytes : ∀ b, ¬ changed b → ¬ RegionRoot regions (.blk b) → h.bytes b = h0.bytes b
  dstates : ∀ b, ¬ RegionRoot regions (.dstate_depth b) → h.dstates b = h0.dstates b
  dmeta : ∀ b d, h.dstates b = some d → ∃ d0, h0.dstates b = some d0 ∧ d = { d0 with depth := d.depth }
  cells : ∀ ref, RegionRoot regions ref → ∀ a0, Space.get h0 ref = some a0 →
    ∃ a, Space.get h ref = some a ∧ a.size = a0.size ∧
      ∀ j, j < a0.size → ¬ RegionCovers regions ref j → a[j]? = a0[j]?

theorem HeaderFoot.refl (changed : Nat → Prop) (regions : List Region) (h : Heap) :
    HeaderFoot changed regions h h := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, Shape.refl h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro b d get
    exact ⟨d, get, by cases d; rfl⟩
  · intro ref _ a0 get
    exact ⟨a0, get, rfl, fun _ _ _ => rfl⟩

/-- A state record write. -/
theorem HeaderFoot.setI {changed : Nat → Prop} {regions : List Region} {h0 h : Heap}
    (foot : HeaderFoot changed regions h0 h) {zs : Nat} {s0 : InflateState}
    (allowed : changed zs) (current : h.istates zs = some s0) (s : InflateState) :
    HeaderFoot changed regions h0 (setI h zs s) := by
  refine ⟨foot.static, foot.allocOk, foot.garbage, foot.nextBlk, foot.nalloc,
    foot.shape.trans (shape_setI current s), foot.words, foot.streams, foot.gzheaders, ?_,
    foot.gzstates, foot.ro, foot.bytes, foot.dstates, foot.dmeta, ?_⟩
  · intro b unchanged
    have ne : b ≠ zs := fun e => unchanged (e ▸ allowed)
    simp only [Zlib.Inflate.Spec.setI, upd_ne _ _ _ _ ne]
    exact foot.istates b unchanged
  · intro ref root a0 get
    obtain ⟨a, now, size, same⟩ := foot.cells ref root a0 get
    exact ⟨a, by rw [byte_view_get_setI]; exact now, size, same⟩

/-- A stream record write. -/
theorem HeaderFoot.streamPut {changed : Nat → Prop} {regions : List Region} {h0 h : Heap}
    (foot : HeaderFoot changed regions h0 h) {r : ZStreamRef} {z0 : ZStream}
    (allowed : ∀ b, StreamRoot r b → changed b) (current : r.get h = some z0) (z : ZStream) :
    HeaderFoot changed regions h0 (r.put h z) := by
  have shape := shape_put current z
  cases r with
  | tab i =>
    have get : h.streams i = some z0 := current
    have eq : (ZStreamRef.tab i).put h z = { h with streams := upd h.streams i (some z) } := by
      simp [ZStreamRef.put, get]
    rw [eq] at shape ⊢
    refine ⟨foot.static, foot.allocOk, foot.garbage, foot.nextBlk, foot.nalloc,
      foot.shape.trans shape, foot.words, ?_, foot.gzheaders, foot.istates,
      foot.gzstates, foot.ro, foot.bytes, foot.dstates, foot.dmeta, ?_⟩
    · intro b unchanged
      have ne : b ≠ i := fun e => unchanged (allowed b e)
      simp only [upd_ne _ _ _ _ ne]
      exact foot.streams b unchanged
    · intro ref root a0 get0
      obtain ⟨a, now, size, same⟩ := foot.cells ref root a0 get0
      refine ⟨a, ?_, size, same⟩
      cases ref <;> exact now
  | in_gzstate_strm i =>
    obtain ⟨g, get, -⟩ : ∃ g, h.gzstates i = some g ∧ g.strm = z0 := by
      simp only [ZStreamRef.get] at current
      cases e : h.gzstates i with
      | none => simp [e] at current
      | some g => simp [e] at current; exact ⟨g, rfl, current⟩
    have eq : (ZStreamRef.in_gzstate_strm i).put h z =
        { h with gzstates := upd h.gzstates i (some { g with strm := z }) } := by
      simp [ZStreamRef.put, get]
    rw [eq] at shape ⊢
    refine ⟨foot.static, foot.allocOk, foot.garbage, foot.nextBlk, foot.nalloc,
      foot.shape.trans shape, foot.words, foot.streams, foot.gzheaders, foot.istates,
      ?_, foot.ro, foot.bytes, foot.dstates, foot.dmeta, ?_⟩
    · intro b unchanged
      have ne : b ≠ i := fun e => unchanged (allowed b e)
      simp only [upd_ne _ _ _ _ ne]
      exact foot.gzstates b unchanged
    · intro ref root a0 get0
      obtain ⟨a, now, size, same⟩ := foot.cells ref root a0 get0
      refine ⟨a, ?_, size, same⟩
      cases ref <;> exact now

/-- A `gz_header` record write. -/
theorem HeaderFoot.headerPut {changed : Nat → Prop} {regions : List Region} {h0 h : Heap}
    (foot : HeaderFoot changed regions h0 h) {i : Nat} {g0 : GzHeader}
    (allowed : changed i) (current : h.gzheaders i = some g0) (g : GzHeader) :
    HeaderFoot changed regions h0 ((GzHeaderRef.tab i).put h g) := by
  have shape := shape_putG (g := .tab i) current g
  have eq : (GzHeaderRef.tab i).put h g = { h with gzheaders := upd h.gzheaders i (some g) } :=
    GzHeaderRef.put_tab current g
  rw [eq] at shape ⊢
  refine ⟨foot.static, foot.allocOk, foot.garbage, foot.nextBlk, foot.nalloc,
    foot.shape.trans shape, foot.words, foot.streams, ?_, foot.istates,
    foot.gzstates, foot.ro, foot.bytes, foot.dstates, foot.dmeta, ?_⟩
  · intro b unchanged
    have ne : b ≠ i := fun e => unchanged (e ▸ allowed)
    simp only [upd_ne _ _ _ _ ne]
    exact foot.gzheaders b unchanged
  · intro ref root a0 get0
    obtain ⟨a, now, size, same⟩ := foot.cells ref root a0 get0
    refine ⟨a, ?_, size, same⟩
    cases ref <;> exact now

/-- A write of a whole private byte block that no region starts on (the local `hbuf`). -/
theorem HeaderFoot.privatePut {changed : Nat → Prop} {regions : List Region} {h0 h : Heap}
    (foot : HeaderFoot changed regions h0 h) {b : Nat} {a : Array UInt8}
    (allowed : changed b) (outside : ¬ RegionRoot regions (.blk b))
    (current : h.bytes b = some a) (a' : Array UInt8) :
    HeaderFoot changed regions h0 (Space.put h (BRef.blk b) a') := by
  have shape := shape_setB current a'
  change HeaderFoot changed regions h0 { h with bytes := upd h.bytes b (some a') }
  refine ⟨foot.static, foot.allocOk, foot.garbage, foot.nextBlk, foot.nalloc,
    foot.shape.trans shape, foot.words, foot.streams, foot.gzheaders, foot.istates,
    foot.gzstates, foot.ro, ?_, foot.dstates, foot.dmeta, ?_⟩
  · intro b' unchanged notRoot
    have ne : b' ≠ b := fun e => unchanged (e ▸ allowed)
    simp only [upd_ne _ _ _ _ ne]
    exact foot.bytes b' unchanged notRoot
  · intro ref root a0 get0
    obtain ⟨a1, now, size, same⟩ := foot.cells ref root a0 get0
    have ne : ref ≠ BRef.blk b := fun e => outside (e ▸ root)
    refine ⟨a1, ?_, size, same⟩
    change (Space.get (Space.put h (BRef.blk b) a') ref : Option (Array UInt8)) = some a1
    rw [byte_view_get_put_ne h ne]
    exact now

/-- A write of a region's view that changes only covered bytes. -/
theorem HeaderFoot.regionPut {changed : Nat → Prop} {regions : List Region} {h0 h : Heap}
    (foot : HeaderFoot changed regions h0 h) {ref : BRef} {a : Array UInt8}
    (root : RegionRoot regions ref) (current : Space.get h ref = some a) (write : Space.ro h ref = false)
    (a' : Array UInt8) (size : a'.size = a.size)
    (covered : ∀ j, j < a.size → ¬ RegionCovers regions ref j → a'[j]? = a[j]?) :
    HeaderFoot changed regions h0 (Space.put h ref a') := by
  have shape := byte_view_put_shape current write a'
  refine ⟨?_, ?_, ?_, byte_view_put_nextBlk h ref a' ▸ foot.nextBlk, ?_,
    foot.shape.trans shape, ?_, ?_, ?_, ?_, ?_, byte_view_put_ro h ref a' ▸ foot.ro, ?_, ?_, ?_, ?_⟩
  · cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.static
  · cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.allocOk
  · cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.garbage
  · cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.nalloc
  · intro b u; cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.words b u
  · intro b u; cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.streams b u
  · intro b u; cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.gzheaders b u
  · intro b u; rw [byte_view_put_istates]; exact foot.istates b u
  · intro b u; cases ref <;> simp only [Space.put] <;> (try split) <;> exact foot.gzstates b u
  · intro b u notRoot
    cases ref with
    | blk id =>
      have ne : b ≠ id := fun e => notRoot (e ▸ root)
      simp only [Space.put, upd_ne _ _ _ _ ne]
      exact foot.bytes b u notRoot
    | _ => simp only [Space.put] <;> (try split) <;> exact foot.bytes b u notRoot
  · intro b notRoot
    cases ref with
    | dstate_depth id =>
      have ne : b ≠ id := fun e => notRoot (e ▸ root)
      simp only [Space.put]
      split <;> (try simp only [upd_ne _ _ _ _ ne]) <;> exact foot.dstates b notRoot
    | _ => simp only [Space.put] <;> (try split) <;> exact foot.dstates b notRoot
  · intro b d get
    cases ref with
    | dstate_depth id =>
      simp only [Space.put] at get
      split at get
      · next old e =>
        by_cases same : b = id
        · subst same
          simp only [upd_same, Option.some.injEq] at get
          subst get
          obtain ⟨d0, get0, eq⟩ := foot.dmeta b old e
          refine ⟨d0, get0, ?_⟩
          rw [eq]
        · simp only [upd_ne _ _ _ _ same] at get
          exact foot.dmeta b d get
      · exact foot.dmeta b d get
    | _ => simp only [Space.put] at get <;> (try split at get) <;> exact foot.dmeta b d get
  · intro ref' root' a0 get0
    obtain ⟨a1, now, size1, same1⟩ := foot.cells ref' root' a0 get0
    by_cases here : ref' = ref
    · subst here
      have eq : a1 = a := Option.some.inj (now.symm.trans current)
      subst eq
      refine ⟨a', byte_view_get_put current write a', size.trans size1, ?_⟩
      intro j bound outside
      exact (covered j (by omega) outside).trans (same1 j bound outside)
    · exact ⟨a1, by rw [byte_view_get_put_ne h here]; exact now, size1, same1⟩

/-- Byte views keep their sizes under a footprint. -/
theorem HeaderFoot.live {changed : Nat → Prop} {regions : List Region} {h0 h : Heap}
    (foot : HeaderFoot changed regions h0 h) : LiveChange h0 h (fun _ => False) (fun _ => False) := by
  intro b
  rw [Shape.live foot.shape b]
  simp

/-- The footprint relation gives the public buffer frame. -/
theorem HeaderFoot.bufferFrame {changed : Nat → Prop} {regions : List Region} {h0 h : Heap}
    (foot : HeaderFoot changed regions h0 h) : BufferFrame h0 h changed regions := by
  classical
  obtain ⟨statics, allocs, garbage, nextBlk, nalloc, words, streams, gzheaders, istates,
    gzstates, ro⟩ := restoreRegions_other h0 h regions
  refine ⟨⟨by rw [statics, foot.static], by rw [allocs, foot.allocOk], by rw [garbage, foot.garbage],
    Nat.le_of_eq (by rw [nextBlk, foot.nextBlk]), Nat.le_of_eq (by rw [nalloc, foot.nalloc]), ?_⟩, ?_⟩
  · intro b _ unchanged
    refine ⟨?_, by rw [words, foot.words b unchanged], by rw [streams, foot.streams b unchanged],
      by rw [gzheaders, foot.gzheaders b unchanged], ?_, by rw [istates, foot.istates b unchanged],
      by rw [gzstates, foot.gzstates b unchanged], by rw [ro, foot.ro]⟩
    · rw [restoreRegions_bytes]
      split
      · rfl
      · next notBoth =>
        by_cases root : RegionRoot regions (.blk b)
        · have absent : h0.bytes b = none := by
            cases e : h0.bytes b with
            | none => rfl
            | some _ => exact absurd ⟨root, by rw [e]; simp⟩ notBoth
          have shape := (foot.shape b).1
          rw [absent] at shape ⊢
          cases e : h.bytes b with
          | none => rfl
          | some _ => simp [e] at shape
        · exact foot.bytes b unchanged root
    · rw [restoreRegions_dstates]
      split
      · cases get0 : h0.dstates b with
        | none =>
          have shape := (foot.shape b).2.2.2.2.1
          rw [get0] at shape
          cases e : h.dstates b with
          | none => simp
          | some _ => simp [e] at shape
        | some d0 =>
          cases e : h.dstates b with
          | none =>
            have shape := (foot.shape b).2.2.2.2.1
            rw [get0, e] at shape
            simp at shape
          | some d =>
            obtain ⟨d0', get0', eq⟩ := foot.dmeta b d e
            rw [get0] at get0'
            cases get0'
            simp only [Option.some.injEq]
            rw [eq]
      · next notRoot => exact foot.dstates b notRoot
  · intro region member ref off a0 ptr get0
    obtain ⟨a, now, size, same⟩ := foot.cells ref ⟨region, member, off, ptr⟩ a0 get0
    exact ⟨a, now, size, fun j bound outside => same j bound outside⟩

end Zlib.Inflate.Proofs
