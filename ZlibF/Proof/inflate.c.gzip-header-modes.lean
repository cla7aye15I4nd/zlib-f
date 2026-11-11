import ZlibF.Proof.«inflate.c.gzip-header-state»
import ZlibF.Proof.«inflate.c.head-gzip»

/-!
# inflate.c: the gzip header modes run

One lemma per gzip header mode, from `HCRC` back to `FLAGS`: from any point
where `GzInv` holds and the state is in that mode, the translated mode runs
without a fault and ends in `GzDone`: it leaves in a header mode, or it returns
normally in `TYPE` (header complete) or `BAD`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Crc32 (crc32)
set_option autoImplicit false

/-- In `EXTRA`, the remaining length of the extra field is at most the record's `extra_len`. -/
def ExtraLenOk (h : Heap) (s : InflateState) : Prop :=
  s.mode = EXTRA → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g → s.length ≤ g.extra_len

theorem ExtraLenOk.of_ne {h : Heap} {s : InflateState} (ne : s.mode ≠ EXTRA) : ExtraLenOk h s :=
  fun m => absurd m ne

/-- How a gzip header dispatch ends. -/
def GzDone (e : GzEntry) (outcome : Except Ex Unit) (regs : IL) (after : Heap) : Prop :=
  ∃ stream state used, GzInv e regs after stream state used ∧
    ((outcome = .error Ex.leave ∧ FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨
      (outcome = .ok () ∧ (state.mode = TYPE ∨ state.mode = BAD))) ∧
    (state.mode ≠ BAD → state.mode ≠ FLAGS → state.flags ≠ -1 ∧ state.flags ≠ 0) ∧
    ExtraLenOk after state

/-- The program runs and ends in `GzDone`. -/
def GzRuns (e : GzEntry) (x : X Unit) (l : IL) (h : Heap) : Prop :=
  ∃ outcome regs after, runX x l h = .ok ((outcome, regs), after) ∧ GzDone e outcome regs after

/-- A leave from a header mode. -/
theorem GzDone.leave {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}
    (inv : GzInv e l h z s used) (mode : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC)
    (flags : s.mode ≠ FLAGS → s.flags ≠ -1 ∧ s.flags ≠ 0) (lenOk : ExtraLenOk h s) :
    GzDone e (.error Ex.leave) l h :=
  ⟨z, s, used, inv, Or.inl ⟨rfl, mode⟩, fun _ notFlags => flags notFlags, lenOk⟩

/-- A `BAD` result. -/
theorem GzDone.bad {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}
    (inv : GzInv e l h z s used) (i : Nat) :
    GzDone e (.ok ()) l (tcBadHeap h e.r e.zs z s i) :=
  ⟨_, _, used, inv.bad i, Or.inr ⟨rfl, Or.inr rfl⟩, fun notBad => absurd rfl notBad,
    ExtraLenOk.of_ne (by change BAD ≠ EXTRA; decide)⟩

/-! ## Primitive runs -/

section primitives
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

theorem GzInv.runX_wrZ (inv : GzInv e l h z s used) (valid : e.Valid) (f : ZStream → ZStream) :
    runX (monadLift (wrZ e.c.strm f) : X Unit) l h = .ok ((.ok (), l), e.r.put h (f z)) := by
  apply runX_lift_ok
  rw [valid.env.strm, wrZ_eq, inv.good.live.hz]

theorem crc32_null_run (h : Heap) : crc32 0 .null 0 h = .ok (0, h) :=
  Zlib.Crc32.Proofs.crc32_null h 0 0

theorem GzInv.hcrcOn_run (inv : GzInv e l h z s used) (valid : e.Valid) :
    hcrcOn e.c.st h = .ok ((s.flags &&& 0x0200) != 0 && (s.wrap &&& 4) != 0, h) := by
  unfold hcrcOn
  rw [valid.env.st]
  simp [bind_app, ldInflateState_tab inv.good.live.hs]

/-- The entry header record, when one is attached. -/
theorem GzEntry.Valid.entryRecord {e : GzEntry} (valid : e.Valid) {i : Nat} (head : e.s.head = some (.tab i)) :
    ∃ g0, e.h.gzheaders i = some g0 ∧
      (g0.extra ≠ .null → CallerRange e.h e.r g0.extra g0.extra_max.toNat true) ∧
      (g0.name ≠ .null → CallerRange e.h e.r g0.name g0.name_max.toNat true) ∧
      (g0.comment ≠ .null → CallerRange e.h e.r g0.comment g0.comm_max.toNat true) := by
  rcases valid.record with none | ⟨j, g0, ptr, get, _, extra, name, comment⟩
  · rw [head] at none; cases none
  · rw [head] at ptr
    cases ptr
    exact ⟨g0, get, extra, by simpa using name, by simpa using comment⟩

/-- The current header record, when one is attached. -/
theorem GzInv.record (inv : GzInv e l h z s used) (valid : e.Valid) {i : Nat} (head : s.head = some (.tab i)) :
    ∃ g g0, h.gzheaders i = some g ∧ e.h.gzheaders i = some g0 ∧
      g.extra_max = g0.extra_max ∧ g.name_max = g0.name_max ∧ g.comm_max = g0.comm_max ∧
      (g.extra = g0.extra ∨ g.extra = .null) ∧ (g.name = g0.name ∨ g.name = .null) ∧
      (g.comment = g0.comment ∨ g.comment = .null) ∧ ldGzHeader s.head h = .ok (g, h) := by
  have head0 : e.s.head = some (.tab i) := inv.head ▸ head
  obtain ⟨g0, get0, _⟩ := valid.entryRecord head0
  obtain ⟨g, get, rest⟩ := inv.links i head0 g0 get0
  exact ⟨g, g0, get, get0, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1, rest.2.2.2.2.2,
    by rw [head]; exact ldGzHeader_tab get⟩

theorem stGzHeader_run {h : Heap} {i : Nat} {g : GzHeader} (get : h.gzheaders i = some g) (g' : GzHeader) :
    stGzHeader (some (.tab i)) g' h = .ok ((), (GzHeaderRef.tab i).put h g') :=
  stGzHeader_ok (r := .tab i) get rfl

end primitives

/-! ## HCRC -/

/-- The end of `case HCRC`: reset the check value and go to `TYPE`. -/
def hcrcFinish (c : Ctx) : X Unit := do
  let v ← crc32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  setMode c.st TYPE

theorem gz_hcrcFinish {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}
    (valid : e.Valid) (inv : GzInv e l h z s used) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (hcrcFinish e.c) l h := by
  have E := inv.env valid
  have inv1 := inv.setState (s' := { s with check := 0 }) rfl inv.good.live.mode
  have E1 := inv1.env valid
  have inv2 := inv1.setStream (z' := { z with adler := 0 }) rfl
  have E2 := inv2.env valid
  have inv3 := inv2.setState (s' := { s with check := 0, mode := TYPE }) rfl
    (by change HEAD ≤ TYPE ∧ TYPE ≤ SYNC; decide)
  refine ⟨_, _, _, ?_, ⟨_, _, used, inv3, Or.inr ⟨rfl, Or.inl rfl⟩, fun _ _ => flags,
    ExtraLenOk.of_ne (by change TYPE ≠ EXTRA; decide)⟩⟩
  unfold hcrcFinish
  rw [runX_bind, runX_lift_ok (crc32_null_run h)]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  rw [runX_bind, inv1.runX_wrZ valid]
  simp only []
  rw [runX_setMode E2]

/-- The part of `case HCRC` after the header CRC check. -/
def hcrcTail (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with hcrc := (s.flags >>> 9) &&& 1, done := 1 }
  hcrcFinish c

theorem gz_hcrcTail {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}
    (valid : e.Valid) (inv : GzInv e l h z s used) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (hcrcTail e.c) l h := by
  have E := inv.env valid
  unfold GzRuns hcrcTail
  rw [runX_bind, runX_ldS E]
  simp only []
  cases head : s.head with
  | none =>
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact gz_hcrcFinish valid inv flags
  | some ref =>
    cases ref with
    | tab i =>
      obtain ⟨g, g0, get, _, _, _, _, _, _, _, load⟩ := inv.record valid head
      rw [head] at load
      have inv1 := inv.setHeader (g' := { g with hcrc := (s.flags >>> 9) &&& 1, done := 1 }) head get
        ⟨rfl, rfl, rfl⟩ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
      rw [runX_bind, runX_lift_ok load]
      simp only []
      rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
      simp only []
      exact gz_hcrcFinish valid inv1 flags

set_option maxRecDepth 100000 in
theorem lit_header_crc_mismatch : "header crc mismatch" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_unknown_header_flags : "unknown header flags set" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

theorem gz_HCRC {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}
    (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = HCRC)
    (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (inflate_HCRC e.c) l h := by
  have E := inv.env valid
  unfold GzRuns inflate_HCRC
  rw [runX_bind, runX_rdS E]
  simp only []
  split
  · obtain ⟨r, l', j, run, inv', kinds, _, _⟩ := inv.needbits 16 (by decide)
    rw [runX_bind, run]
    rcases kinds with rfl | rfl
    · simp only []
      rw [runX_bind, runX_ldS E]
      simp only []
      rw [runX_bind, runX_get]
      simp only []
      split
      · obtain ⟨i, _, bad⟩ := tcBadMode_run (c := e.c) "header crc mismatch" lit_header_crc_mismatch
          valid.env.strm valid.env.st E.hz E.hs
        rw [runX_bind, runX_lift_ok bad]
        exact ⟨_, _, _, rfl, GzDone.bad inv' i⟩
      · rw [runX_bind, runX_INITBITS]
        simp only []
        exact gz_hcrcTail valid inv'.initbits flags
    · exact ⟨_, _, _, rfl, GzDone.leave inv' (by rw [mode]; decide) (fun _ => flags)
      (ExtraLenOk.of_ne (by rw [mode]; decide))⟩
  · exact gz_hcrcTail valid inv flags

/-! ## Caller regions of the header record -/

theorem array_set!_getElem?_ne {α : Type} (a : Array α) {i j : Nat} (ne : i ≠ j) (v : α) :
    (a.set! i v)[j]? = a[j]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne ne]

theorem array_set!_size {α : Type} (a : Array α) (i : Nat) (v : α) : (a.set! i v).size = a.size := by
  simp

/-- The regions of the entry record. -/
theorem GzEntry.regions_eq {e : GzEntry} {i : Nat} {g0 : GzHeader} (head : e.s.head = some (.tab i))
    (get : e.h.gzheaders i = some g0) :
    e.regions = [⟨g0.extra, g0.extra_max.toNat⟩, ⟨g0.name, g0.name_max.toNat⟩, ⟨g0.comment, g0.comm_max.toNat⟩] := by
  simp [GzEntry.regions, HeaderRegions, head, get]

/-- A header field the copy loops may write: its current pointer, when not
NULL, is the entry region of the field. -/
def FieldRoom (e : GzEntry) (h : Heap) (sel : GzHeader → BPtr) (cap : GzHeader → UInt32) : Prop :=
  ∀ i g, e.s.head = some (.tab i) → h.gzheaders i = some g → sel g ≠ .null →
    (⟨sel g, (cap g).toNat⟩ : Region) ∈ e.regions ∧ CallerRange e.h e.r (sel g) (cap g).toNat true

theorem FieldRoom.headers {e : GzEntry} {h h' : Heap} {sel : GzHeader → BPtr} {cap : GzHeader → UInt32}
    (room : FieldRoom e h sel cap) (same : h'.gzheaders = h.gzheaders) : FieldRoom e h' sel cap := by
  intro i g head get
  rw [same] at get
  exact room i g head get

section fields
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

theorem GzInv.nameRoom (inv : GzInv e l h z s used) (valid : e.Valid) :
    FieldRoom e h (·.name) (·.name_max) := by
  intro i g head get nonnull
  obtain ⟨g0, get0, _, name, _⟩ := valid.entryRecord head
  obtain ⟨g1, get1, _, nm, _, _, ptr, _⟩ := inv.links i head g0 get0
  rw [get] at get1
  cases get1
  have same : g.name = g0.name := ptr.resolve_right nonnull
  rw [GzEntry.regions_eq head get0]
  simp only [same, nm]
  exact ⟨by simp, name (by rw [← same]; exact nonnull)⟩

theorem GzInv.commentRoom (inv : GzInv e l h z s used) (valid : e.Valid) :
    FieldRoom e h (·.comment) (·.comm_max) := by
  intro i g head get nonnull
  obtain ⟨g0, get0, _, _, comment⟩ := valid.entryRecord head
  obtain ⟨g1, get1, _, _, cm, _, _, ptr⟩ := inv.links i head g0 get0
  rw [get] at get1
  cases get1
  have same : g.comment = g0.comment := ptr.resolve_right nonnull
  rw [GzEntry.regions_eq head get0]
  simp only [same, cm]
  exact ⟨by simp, comment (by rw [← same]; exact nonnull)⟩

/-- A store of one byte into a caller region of the entry record. -/
theorem GzInv.regionByte (inv : GzInv e l h z s used) {p : BPtr} {cap : Nat}
    (member : (⟨p, cap⟩ : Region) ∈ e.regions) (range : CallerRange e.h e.r p cap true)
    (nonnull : p ≠ .null) {k : Nat} (small : k < cap) :
    ∃ ref off a, p = .ref ref off ∧ Space.get h ref = some a ∧ Space.ro h ref = false ∧
      off + cap ≤ a.size ∧ ∀ v, GzInv e l (Space.put h ref (a.set! (off + k) v)) z s used := by
  rcases range with null | ⟨_, writable, _⟩
  · exact absurd null nonnull
  · rcases writable rfl with ⟨null, _⟩ | ⟨ref, off, a0, ptr, get0, ro0, fit⟩
    · exact absurd null nonnull
    · obtain ⟨a, get, size⟩ := inv.sizes.view get0
      have ro : Space.ro h ref = false := by rw [inv.readonly]; exact ro0
      refine ⟨ref, off, a, ptr, get, ro, by rw [size]; exact fit, fun v => ?_⟩
      refine inv.storeRegion ⟨_, member, off, ptr⟩ get ro _ (array_set!_size a _ v) ?_
      intro j _ outside
      apply array_set!_getElem?_ne
      intro same
      apply outside
      exact ⟨_, member, off, ptr, by omega, show j < off + cap by omega⟩

end fields

/-! ## The byte loop of NAME and COMMENT -/

/-- The loop body of `case NAME` (`sel = name`) and `case COMMENT` (`sel = comment`). -/
def strBody (c : Ctx) (sel : GzHeader → BPtr) (cap : GzHeader → UInt32) : X Unit := do
  let l ← get
  let b ← index8 l.next l.copy.toNat
  set { l with len := b.toUInt32, copy := l.copy + 1 }
  let s ← ldInflateState c.st
  if s.head != none then
    let g ← ldGzHeader s.head
    if sel g != .null && s.length < cap g then
      store8 (← (sel g).add (s.length.toNat : Int)) b
      wrS c.st fun s => { s with length := s.length + 1 }

/-- The loop condition of `case NAME` and `case COMMENT`. -/
def strCond : X Bool := do
  let l ← get
  return l.len != 0 && l.copy < l.have_

section loop
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

/-- The unread input is a readable view when it is not empty. -/
theorem GzInv.input (inv : GzInv e l h z s used) (pos : 0 < l.have_.toNat) :
    ∃ ref off a, l.next = .ref ref off ∧ Space.get h ref = some a ∧ off + l.have_.toNat ≤ a.size := by
  obtain ⟨rest, _, bits⟩ := inv.bits
  rcases bits.next with empty | ⟨ref, a, off, ptr, get, fit, _⟩
  · have := bits.have_eq; rw [empty] at this; simp at this; omega
  · exact ⟨ref, off, a, ptr, get, by rw [bits.have_eq]; exact fit⟩

/-- Registers of one pass of the byte loop. -/
def StrRegs (l l' : IL) : Prop :=
  l'.next = l.next ∧ l'.have_ = l.have_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧
    l'.put = l.put ∧ l'.left = l.left ∧ l'.out_ = l.out_

theorem StrRegs.refl (l : IL) : StrRegs l l := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem StrRegs.trans {a b c : IL} (x : StrRegs a b) (y : StrRegs b c) : StrRegs a c :=
  ⟨y.1.trans x.1, y.2.1.trans x.2.1, y.2.2.1.trans x.2.2.1, y.2.2.2.1.trans x.2.2.2.1,
    y.2.2.2.2.1.trans x.2.2.2.2.1, y.2.2.2.2.2.1.trans x.2.2.2.2.2.1, y.2.2.2.2.2.2.trans x.2.2.2.2.2.2⟩

theorem gz_strBody {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} (valid : e.Valid)
    (inv : GzInv e l h z s used) (room : FieldRoom e h sel cap) (inRange : l.copy.toNat < l.have_.toNat) :
    ∃ l' h' s', runX (strBody e.c sel cap) l h = .ok ((.ok (), l'), h') ∧ GzInv e l' h' z s' used ∧
      StrRegs l l' ∧ l'.copy = l.copy + 1 ∧ s'.mode = s.mode ∧ s'.flags = s.flags ∧
      h'.gzheaders = h.gzheaders := by
  have E := inv.env valid
  obtain ⟨ref, off, a, nxt, get, fit⟩ := inv.input (by omega)
  have lt : off + l.copy.toNat < a.size := by omega
  have idx : index8 l.next l.copy.toNat h = .ok (a[off + l.copy.toNat], h) := by
    rw [nxt]; exact Ptr.index_ok get lt
  let l1 : IL := { l with len := (a[off + l.copy.toNat]).toUInt32, copy := l.copy + 1 }
  have regs1 : StrRegs l l1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have inv1 : GzInv e l1 h z s used := inv.scratch regs1
  unfold strBody
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok idx]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  rw [runX_bind, runX_ldS E]
  simp only []
  cases head : s.head with
  | none =>
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨l1, h, s, by rw [runX_pure], inv1, regs1, rfl, rfl, rfl, rfl⟩
  | some ref =>
    cases ref with
    | tab i =>
      obtain ⟨g, _, gget, _, _, _, _, _, _, _, load⟩ := inv.record valid head
      rw [head] at load
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
      rw [runX_bind, runX_lift_ok load]
      simp only []
      split
      · next cond =>
        have nonnull : sel g ≠ .null := by
          intro null; simp [null] at cond
        have lenSmall : s.length.toNat < (cap g).toNat := by
          have := cond; simp at this; exact UInt32.lt_iff_toNat_lt.mp this.2
        obtain ⟨member, range⟩ := room i g (inv.head ▸ head) gget nonnull
        obtain ⟨ref2, off2, a2, ptr2, get2, ro2, fit2, store⟩ :=
          inv1.regionByte member range nonnull lenSmall
        have add : (sel g).add (s.length.toNat : Int) h = .ok (.ref ref2 (off2 + s.length.toNat), h) := by
          rw [ptr2]; exact Ptr.add_nat_ok get2 (by omega)
        have st : store8 (.ref ref2 (off2 + s.length.toNat)) (a[off + l.copy.toNat]) h =
            .ok ((), Space.put h ref2 (a2.set! (off2 + s.length.toNat) (a[off + l.copy.toNat]))) :=
          Ptr.store_ok get2 ro2 (by omega)
        have inv2 := store (a[off + l.copy.toNat])
        have E2 := inv2.env valid
        have inv3 := inv2.setState (s' := { s with length := s.length + 1 }) rfl inv.good.live.mode
        rw [runX_bind, runX_lift_ok add]
        simp only []
        rw [runX_bind, runX_lift_ok st]
        simp only []
        rw [runX_wrS E2]
        refine ⟨l1, _, _, rfl, inv3, regs1, rfl, rfl, rfl, ?_⟩
        simp only [Zlib.Inflate.Spec.setI]
        cases ref2 <;> simp only [Space.put] <;> (try split) <;> rfl
      · exact ⟨l1, h, s, by rw [runX_pure], inv1, regs1, rfl, rfl, rfl, rfl⟩

theorem uint32_succ_toNat {a b : UInt32} (lt : a.toNat < b.toNat) : (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add]
  have := b.toNat_lt
  simp only [UInt32.toNat_one, UInt32.size] at *
  omega

theorem gz_strLoop {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} (valid : e.Valid)
    (inv : GzInv e l h z s used)
    (roomOf : ∀ {l' : IL} {h' : Heap} {z' : ZStream} {s' : InflateState} {used' : Nat},
      GzInv e l' h' z' s' used' → FieldRoom e h' sel cap)
    (copy0 : l.copy = 0) (pos : 0 < l.have_.toNat) :
    ∃ l' h' s', runX (xdoWhile (strBody e.c sel cap) strCond) l h = .ok ((.ok (), l'), h') ∧
      GzInv e l' h' z s' used ∧ StrRegs l l' ∧ 1 ≤ l'.copy.toNat ∧ l'.copy.toNat ≤ l'.have_.toNat ∧
      s'.mode = s.mode ∧ s'.flags = s.flags := by
  have start : l.copy.toNat < l.have_.toNat := by rw [copy0]; simpa using pos
  obtain ⟨l1, h1, s1, run1, inv1, regs1, copy1, m1, f1, _⟩ := gz_strBody valid inv (roomOf inv) start
  have c1 : l1.copy.toNat = 1 := by rw [copy1, copy0]; rfl
  let P : IL → Heap → Prop := fun l' h' => ∃ s', GzInv e l' h' z s' used ∧ StrRegs l l' ∧
    1 ≤ l'.copy.toNat ∧ l'.copy.toNat ≤ l'.have_.toNat ∧ s'.mode = s.mode ∧ s'.flags = s.flags
  have P1 : P l1 h1 := ⟨s1, inv1, regs1, by omega, by rw [c1, regs1.2.1]; omega, m1, f1⟩
  let Q : Except Ex Unit → IL → Heap → Prop := fun r l' h' => r = .ok () ∧ P l' h'
  have step : ∀ l' h', P l' h' → ∃ test : Except Ex Bool, ∃ l1 h1, runX strCond l' h' = .ok ((test, l1), h1) ∧
      (match test with
       | .error fault => Q (.error fault) l1 h1
       | .ok false => Q (.ok ()) l1 h1
       | .ok true => ∃ result : Except Ex Bool, ∃ l2 h2,
           runX (do strBody e.c sel cap; pure false) l1 h1 = .ok ((result, l2), h2) ∧
           (match result with
            | .error fault => Q (.error fault) l2 h2
            | .ok true => Q (.ok ()) l2 h2
            | .ok false => P l2 h2 ∧ l2.have_.toNat - l2.copy.toNat < l'.have_.toNat - l'.copy.toNat)) := by
    intro l' h' ⟨s', inv', regs', c1', c2', m', f'⟩
    refine ⟨.ok (l'.len != 0 && decide (l'.copy < l'.have_)), l', h', rfl, ?_⟩
    cases test : (l'.len != 0 && decide (l'.copy < l'.have_))
    · exact ⟨rfl, s', inv', regs', c1', c2', m', f'⟩
    · have lt : l'.copy.toNat < l'.have_.toNat := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at test
        exact UInt32.lt_iff_toNat_lt.mp test.2
      obtain ⟨l2, h2, s2, run2, inv2, regs2, copy2, m2, f2, _⟩ := gz_strBody valid inv' (roomOf inv') lt
      have succ := uint32_succ_toNat lt
      refine ⟨.ok false, l2, h2, ?_, ⟨s2, inv2, regs'.trans regs2, ?_, ?_, m2.trans m', f2.trans f'⟩, ?_⟩
      · rw [runX_bind, run2]; rfl
      · rw [copy2, succ]; omega
      · rw [copy2, succ, regs2.2.1]; omega
      · rw [copy2, succ, regs2.2.1]; omega
  obtain ⟨result, regs, after, run, done, final⟩ := xwhileBrk_rank (cond := strCond)
    (body := (do strBody e.c sel cap; pure false)) P (fun l' _ => l'.have_.toNat - l'.copy.toNat)
    Q step P1 (by
      have := l1.have_.toNat_lt
      show _ < C.fuel
      unfold C.fuel
      omega)
  refine ⟨regs, after, ?_⟩
  obtain ⟨s', inv', regs', c1', c2', m', f'⟩ := final
  subst done
  refine ⟨s', ?_, inv', regs', c1', c2', m', f'⟩
  unfold xdoWhile xwhile
  rw [runX_bind, run1]
  exact run

end loop

/-! ## The rest of NAME and COMMENT -/

/-- After the byte loop: consume the copied bytes, leave if the terminating
zero was not seen, else continue with `k`. -/
def strAdvanceK (k : X Unit) : X Unit := do
  let l ← get
  let nx ← l.next.add (l.copy.toNat : Int)
  set { l with have_ := l.have_ - l.copy, next := nx }
  if l.len != 0 then throw Ex.leave
  k

/-- `case NAME` / `case COMMENT` when the flag is set, continuing with `k`. -/
def strCopyK (c : Ctx) (sel : GzHeader → BPtr) (cap : GzHeader → UInt32) (k : X Unit) : X Unit := do
  if (← get).have_ == 0 then throw Ex.leave
  modify fun l => { l with copy := 0 }
  xdoWhile (strBody c sel cap) strCond
  if ← hcrcOn c.st then
    let l ← get
    let v ← crc32 (← rdS c.st (·.check)) l.next l.copy
    wrS c.st fun s => { s with check := v }
  strAdvanceK k

section copy
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

theorem uint32_sub_toNat {a b : UInt32} (le : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr le)

theorem gz_strAdvanceK {k : X Unit} (valid : e.Valid) (inv : GzInv e l h z s used)
    (bound : l.copy.toNat ≤ l.have_.toNat) (pos : 0 < l.have_.toNat)
    (mode : FLAGS < s.mode ∧ s.mode ≤ HCRC) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) (notExtra : s.mode ≠ EXTRA)
    (cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e k l' h') :
    GzRuns e (strAdvanceK k) l h := by
  obtain ⟨ref, off, a, nxt, get, fit⟩ := inv.input pos
  have add : l.next.add (l.copy.toNat : Int) h = .ok (.ref ref (off + l.copy.toNat), h) := by
    rw [nxt]; exact Ptr.add_nat_ok get (by omega)
  let l1 : IL := { l with have_ := l.have_ - l.copy, next := .ref ref (off + l.copy.toNat) }
  have inv1 : GzInv e l1 h z s (used + l.copy.toNat) :=
    inv.consume bound (by simp only [l1, nxt, inputAdvance])
      (by simp only [l1]; rw [uint32_sub_toNat bound]; omega) ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold GzRuns strAdvanceK
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok add]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  split
  · rw [runX_bind, runX_throw]
    exact ⟨_, _, _, rfl, GzDone.leave inv1 ⟨Nat.le_of_lt mode.1, mode.2⟩ (fun _ => flags)
      (ExtraLenOk.of_ne notExtra)⟩
  · exact cont _ _ _ _ inv1 rfl rfl

theorem gz_strCopyK {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} {k : X Unit} (valid : e.Valid)
    (inv : GzInv e l h z s used)
    (roomOf : ∀ {l' : IL} {h' : Heap} {z' : ZStream} {s' : InflateState} {used' : Nat},
      GzInv e l' h' z' s' used' → FieldRoom e h' sel cap)
    (mode : FLAGS < s.mode ∧ s.mode ≤ HCRC) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) (notExtra : s.mode ≠ EXTRA)
    (cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e k l' h') :
    GzRuns e (strCopyK e.c sel cap k) l h := by
  unfold GzRuns strCopyK
  rw [runX_bind, runX_get]
  simp only []
  split
  · next empty =>
    rw [runX_bind, runX_throw]
    exact ⟨_, _, _, rfl, GzDone.leave inv ⟨Nat.le_of_lt mode.1, mode.2⟩ (fun _ => flags)
      (ExtraLenOk.of_ne notExtra)⟩
  · next nonempty =>
    have pos : 0 < l.have_.toNat := by
      have : l.have_ ≠ 0 := by simpa using nonempty
      exact Nat.pos_of_ne_zero (fun z0 => this (UInt32.toNat_inj.mp (by simpa using z0)))
    let l0 : IL := { l with copy := 0 }
    have inv0 : GzInv e l0 h z s used := inv.scratch ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨l1, h1, s1, run1, inv1, regs1, c1, c2, m1, f1⟩ := gz_strLoop valid inv0 roomOf rfl pos
    have pos1 : 0 < l1.have_.toNat := by rw [regs1.2.1]; exact pos
    have mode1 : FLAGS < s1.mode ∧ s1.mode ≤ HCRC := by rw [m1]; exact mode
    have flags1 : s1.flags ≠ -1 ∧ s1.flags ≠ 0 := by rw [f1]; exact flags
    have notExtra1 : s1.mode ≠ EXTRA := by rw [m1]; exact notExtra
    have cont1 : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s1.mode → s'.flags = s1.flags →
        GzRuns e k l' h' := fun l' h' s' used' inv' m' f' => cont l' h' s' used' inv' (m'.trans m1) (f'.trans f1)
    rw [runX_bind, runX_modify]
    simp only []
    rw [runX_bind, run1]
    simp only []
    have E1 := inv1.env valid
    rw [runX_bind, runX_lift_ok (inv1.hcrcOn_run valid)]
    simp only []
    split
    · obtain ⟨ref, off, a, nxt, get, fit⟩ := inv1.input pos1
      have crc := Zlib.Crc32.Proofs.ViewsProof.crc32_correct h1 (inv1.statics valid) s1.check ref off a get
        l1.copy (by omega)
      let v : UInt64 := (ZlibF.Spec.crc32Update s1.check.toUInt32 ((a.toList.drop off).take l1.copy.toNat)).toUInt64
      have crc' : crc32 s1.check l1.next l1.copy h1 = .ok (v, h1) := by rw [nxt]; exact crc
      have inv2 := inv1.setState (s' := { s1 with check := v }) rfl inv1.good.live.mode
      rw [runX_bind, runX_get]
      simp only []
      rw [runX_bind, runX_rdS E1]
      simp only []
      rw [runX_bind, runX_lift_ok crc']
      simp only []
      rw [runX_bind, runX_wrS E1]
      simp only []
      exact gz_strAdvanceK valid inv2 c2 pos1 mode1 flags1 notExtra1 cont1
    · exact gz_strAdvanceK valid inv1 c2 pos1 mode1 flags1 notExtra1 cont1

end copy

/-! ## COMMENT and NAME -/

section modes
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

theorem gz_toHCRC (valid : e.Valid) (inv : GzInv e l h z s used) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (do setMode e.c.st HCRC; inflate_HCRC e.c) l h := by
  have E := inv.env valid
  have inv1 := inv.setState (s' := { s with mode := HCRC }) rfl (by change HEAD ≤ HCRC ∧ HCRC ≤ SYNC; decide)
  unfold GzRuns
  rw [runX_bind, runX_setMode E]
  exact gz_HCRC valid inv1 rfl flags

/-- Clearing a buffer pointer of the header record, if one is attached. -/
theorem GzInv.clearField (inv : GzInv e l h z s used) (valid : e.Valid) {i : Nat} (head : s.head = some (.tab i))
    (which : Fin 3) :
    ∃ g, h.gzheaders i = some g ∧ ldGzHeader s.head h = .ok (g, h) ∧
      GzInv e l ((GzHeaderRef.tab i).put h
        (if which = 0 then { g with extra := .null } else if which = 1 then { g with name := .null }
          else { g with comment := .null })) z s used := by
  obtain ⟨g, _, get, _, _, _, _, _, _, _, load⟩ := inv.record valid head
  refine ⟨g, get, load, ?_⟩
  by_cases w0 : which = 0
  · simp only [w0, ↓reduceIte]
    exact inv.setHeader head get ⟨rfl, rfl, rfl⟩ (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  · by_cases w1 : which = 1
    · simp only [w0, w1, ↓reduceIte]
      exact inv.setHeader head get ⟨rfl, rfl, rfl⟩ (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
    · simp only [w0, w1, ↓reduceIte]
      exact inv.setHeader head get ⟨rfl, rfl, rfl⟩ (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)

theorem gz_COMMENT (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = COMMENT)
    (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (inflate_COMMENT e.c) l h := by
  have E := inv.env valid
  have range : FLAGS < s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e (do setMode e.c.st HCRC; inflate_HCRC e.c) l' h' :=
    fun l' h' s' used' inv' _ f' => gz_toHCRC valid inv' (by rw [f']; exact flags)
  unfold inflate_COMMENT
  unfold GzRuns
  rw [runX_bind, runX_rdS E]
  simp only []
  split
  · exact gz_strCopyK (sel := (·.comment)) (cap := (·.comm_max)) valid inv
      (fun inv' => inv'.commentRoom valid) range flags (by rw [mode]; decide) cont
  · rw [runX_bind, runX_ldS E]
    simp only []
    cases head : s.head with
    | none =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact gz_toHCRC valid inv flags
    | some ref =>
      cases ref with
      | tab i =>
        obtain ⟨g, get, load, inv1⟩ := inv.clearField valid head 2
        rw [head] at load
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_lift_ok load]
        simp only []
        rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
        simp only []
        exact gz_toHCRC valid inv1 flags

theorem gz_toCOMMENT (valid : e.Valid) (inv : GzInv e l h z s used) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (do wrS e.c.st (fun s => { s with length := 0, mode := COMMENT }); inflate_COMMENT e.c) l h := by
  have E := inv.env valid
  have inv1 := inv.setState (s' := { s with length := 0, mode := COMMENT }) rfl
    (by change HEAD ≤ COMMENT ∧ COMMENT ≤ SYNC; decide)
  unfold GzRuns
  rw [runX_bind, runX_wrS E]
  exact gz_COMMENT valid inv1 rfl flags

theorem gz_NAME (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = NAME)
    (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (inflate_NAME e.c) l h := by
  have E := inv.env valid
  have range : FLAGS < s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e (do wrS e.c.st (fun s => { s with length := 0, mode := COMMENT }); inflate_COMMENT e.c) l' h' :=
    fun l' h' s' used' inv' _ f' => gz_toCOMMENT valid inv' (by rw [f']; exact flags)
  unfold inflate_NAME
  unfold GzRuns
  rw [runX_bind, runX_rdS E]
  simp only []
  split
  · exact gz_strCopyK (sel := (·.name)) (cap := (·.name_max)) valid inv
      (fun inv' => inv'.nameRoom valid) range flags (by rw [mode]; decide) cont
  · rw [runX_bind, runX_ldS E]
    simp only []
    cases head : s.head with
    | none =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact gz_toCOMMENT valid inv flags
    | some ref =>
      cases ref with
      | tab i =>
        obtain ⟨g, get, load, inv1⟩ := inv.clearField valid head 1
        rw [head] at load
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_lift_ok load]
        simp only []
        rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
        simp only []
        exact gz_toCOMMENT valid inv1 flags

end modes

/-! ## EXTRA -/

theorem copyRange_getElem?_outside {T : Type} [Inhabited T] (d src : Array T) (doff soff n j : Nat)
    (out : j < doff ∨ doff + n ≤ j) : (copyRange d src doff soff n)[j]? = d[j]? := by
  unfold copyRange
  suffices key : ∀ (list : List Nat) (a : Array T), (∀ i ∈ list, i < n) →
      (list.foldl (fun a i => a.set! (doff + i) src[soff + i]!) a)[j]? = a[j]? by
    exact key _ _ (fun i member => List.mem_range.mp member)
  intro list
  induction list with
  | nil => intro a _; rfl
  | cons i rest ih =>
    intro a bound
    simp only [List.foldl_cons]
    rw [ih _ (fun k member => bound k (List.mem_cons_of_mem _ member))]
    apply array_set!_getElem?_ne
    have := bound i List.mem_cons_self
    omega

/-- After the extra field copy: leave unless the field is complete. -/
def extraEndK (c : Ctx) (k : X Unit) : X Unit := do
  if (← rdS c.st (·.length)) != 0 then throw Ex.leave
  k

/-- Consume the copied bytes of the extra field. -/
def extraAdvanceK (c : Ctx) (copy : UInt32) (k : X Unit) : X Unit := do
  let l ← get
  let nx ← l.next.add (copy.toNat : Int)
  set { l with have_ := l.have_ - copy, next := nx }
  wrS c.st fun s => { s with length := s.length - copy }
  extraEndK c k

/-- The header CRC over the copied bytes of the extra field. -/
def extraCrcK (c : Ctx) (copy : UInt32) (k : X Unit) : X Unit := do
  if ← hcrcOn c.st then
    let v ← crc32 (← rdS c.st (·.check)) (← get).next copy
    wrS c.st fun s => { s with check := v }
  extraAdvanceK c copy k

section extra
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

theorem gz_extraEndK {k : X Unit} (valid : e.Valid) (inv : GzInv e l h z s used)
    (mode : FLAGS < s.mode ∧ s.mode ≤ HCRC) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) (lenOk : ExtraLenOk h s)
    (cont : GzInv e l h z s used → GzRuns e k l h) :
    GzRuns e (extraEndK e.c k) l h := by
  have E := inv.env valid
  unfold GzRuns extraEndK
  rw [runX_bind, runX_rdS E]
  simp only []
  split
  · rw [runX_bind, runX_throw]
    exact ⟨_, _, _, rfl, GzDone.leave inv ⟨Nat.le_of_lt mode.1, mode.2⟩ (fun _ => flags) lenOk⟩
  · exact cont inv

theorem gz_extraAdvanceK {k : X Unit} {copy : UInt32} (valid : e.Valid) (inv : GzInv e l h z s used)
    (bound : copy.toNat ≤ l.have_.toNat) (pos : 0 < l.have_.toNat)
    (mode : FLAGS < s.mode ∧ s.mode ≤ HCRC) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0)
    (lenOk : ExtraLenOk h s) (copyLe : copy.toNat ≤ s.length.toNat)
    (cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e k l' h') :
    GzRuns e (extraAdvanceK e.c copy k) l h := by
  obtain ⟨ref, off, a, nxt, get, fit⟩ := inv.input pos
  have add : l.next.add (copy.toNat : Int) h = .ok (.ref ref (off + copy.toNat), h) := by
    rw [nxt]; exact Ptr.add_nat_ok get (by omega)
  let l1 : IL := { l with have_ := l.have_ - copy, next := .ref ref (off + copy.toNat) }
  have inv1 : GzInv e l1 h z s (used + copy.toNat) :=
    inv.consume bound (by simp only [l1, nxt, inputAdvance])
      (by simp only [l1]; rw [uint32_sub_toNat bound]; omega) ⟨rfl, rfl, rfl, rfl, rfl⟩
  have E1 := inv1.env valid
  have inv2 := inv1.setState (s' := { s with length := s.length - copy }) rfl inv.good.live.mode
  unfold GzRuns extraAdvanceK
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok add]
  simp only []
  rw [runX_bind, runX_set]
  simp only []
  rw [runX_bind, runX_wrS E1]
  simp only []
  have lenOk2 : ExtraLenOk (setI h e.zs { s with length := s.length - copy }) { s with length := s.length - copy } := by
    intro m i g head get
    have le := UInt32.le_iff_toNat_le.mp (lenOk m i g head get)
    change s.length - copy ≤ g.extra_len
    rw [UInt32.le_iff_toNat_le, uint32_sub_toNat copyLe]
    omega
  exact gz_extraEndK valid inv2 mode flags lenOk2 (fun inv' => cont _ _ _ _ inv' rfl rfl)

theorem gz_extraCrcK {k : X Unit} {copy : UInt32} (valid : e.Valid) (inv : GzInv e l h z s used)
    (bound : copy.toNat ≤ l.have_.toNat) (pos : 0 < l.have_.toNat)
    (mode : FLAGS < s.mode ∧ s.mode ≤ HCRC) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0)
    (lenOk : ExtraLenOk h s) (copyLe : copy.toNat ≤ s.length.toNat)
    (cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e k l' h') :
    GzRuns e (extraCrcK e.c copy k) l h := by
  have E := inv.env valid
  unfold GzRuns extraCrcK
  rw [runX_bind, runX_lift_ok (inv.hcrcOn_run valid)]
  simp only []
  split
  · obtain ⟨ref, off, a, nxt, get, fit⟩ := inv.input pos
    let v : UInt64 := (ZlibF.Spec.crc32Update s.check.toUInt32 ((a.toList.drop off).take copy.toNat)).toUInt64
    have crc : crc32 s.check l.next copy h = .ok (v, h) := by
      rw [nxt]
      exact Zlib.Crc32.Proofs.ViewsProof.crc32_correct h (inv.statics valid) s.check ref off a get copy (by omega)
    have inv1 := inv.setState (s' := { s with check := v }) rfl inv.good.live.mode
    rw [runX_bind, runX_rdS E]
    simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_lift_ok crc]
    simp only []
    rw [runX_bind, runX_wrS E]
    simp only []
    exact gz_extraAdvanceK valid inv1 bound pos mode flags (fun m i g head get => lenOk m i g head get) copyLe cont
  · exact gz_extraAdvanceK valid inv bound pos mode flags lenOk copyLe cont

/-- The entry `extra` region is separate from the current unread input. -/
theorem GzInv.extraSeparate (inv : GzInv e l h z s used) (valid : e.Valid) {i : Nat} {g0 : GzHeader}
    (head0 : e.s.head = some (.tab i)) (get0 : e.h.gzheaders i = some g0) :
    Separate g0.extra g0.extra_max.toNat l.next l.have_.toNat := by
  have sep := valid.extra i g0 head0 get0
  have swapped := separate_swap _ _ _ _ sep
  have count := inv.count
  have adv := inputAdvance_separate e.l.next g0.extra e.l.have_.toNat g0.extra_max.toNat used
    (by omega) swapped
  rw [← inv.next] at adv
  have eq : e.l.have_.toNat - used = l.have_.toNat := by omega
  rw [eq] at adv
  exact separate_swap _ _ _ _ adv

theorem gz_toNAME (valid : e.Valid) (inv : GzInv e l h z s used) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (do wrS e.c.st (fun s => { s with length := 0, mode := NAME }); inflate_NAME e.c) l h := by
  have E := inv.env valid
  have inv1 := inv.setState (s' := { s with length := 0, mode := NAME }) rfl
    (by change HEAD ≤ NAME ∧ NAME ≤ SYNC; decide)
  unfold GzRuns
  rw [runX_bind, runX_wrS E]
  exact gz_NAME valid inv1 rfl flags

/-- `case EXTRA` with its join points written out as calls. -/
def extraTop (c : Ctx) : X Unit := do
  if ((← rdS c.st (·.flags)) &&& 0x0400) != 0 then
    let s ← ldInflateState c.st
    let l ← get
    let copy := if s.length > l.have_ then l.have_ else s.length
    set { l with copy := copy }
    if copy != 0 then
      if s.head != none then
        let g ← ldGzHeader s.head
        if g.extra != .null then
          let len := g.extra_len - s.length
          modify fun l => { l with len := len }
          if len < g.extra_max then
            let n := if len + copy > g.extra_max then g.extra_max - len else copy
            memcpyB (← g.extra.add (len.toNat : Int)) (← get).next n.toNat
            extraCrcK c copy (do wrS c.st (fun s => { s with length := 0, mode := NAME }); inflate_NAME c)
          else extraCrcK c copy (do wrS c.st (fun s => { s with length := 0, mode := NAME }); inflate_NAME c)
        else extraCrcK c copy (do wrS c.st (fun s => { s with length := 0, mode := NAME }); inflate_NAME c)
      else extraCrcK c copy (do wrS c.st (fun s => { s with length := 0, mode := NAME }); inflate_NAME c)
    else extraEndK c (do wrS c.st (fun s => { s with length := 0, mode := NAME }); inflate_NAME c)
  else
    wrS c.st fun s => { s with length := 0, mode := NAME }
    inflate_NAME c

theorem inflate_EXTRA_eq (c : Ctx) : inflate_EXTRA c = extraTop c := rfl

theorem gz_EXTRA (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = EXTRA)
    (flags : s.flags ≠ -1 ∧ s.flags ≠ 0)
    (lenOk : (s.flags &&& 0x0400 != 0) = true → ExtraLenOk h s) :
    GzRuns e (inflate_EXTRA e.c) l h := by
  have E := inv.env valid
  have range : FLAGS < s.mode ∧ s.mode ≤ HCRC := by rw [mode]; decide
  have cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e (do wrS e.c.st (fun s => { s with length := 0, mode := NAME }); inflate_NAME e.c) l' h' :=
    fun l' h' s' used' inv' _ f' => gz_toNAME valid inv' (by rw [f']; exact flags)
  rw [inflate_EXTRA_eq]
  unfold extraTop
  unfold GzRuns
  rw [runX_bind, runX_rdS E]
  simp only []
  split
  · next flagSet =>
    have lenOk := lenOk flagSet
    have extraLen := lenOk mode
    rw [runX_bind, runX_ldS E]
    simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_set]
    simp only []
    -- the copy count
    have cpHave0 : (if s.length > l.have_ then l.have_ else s.length).toNat ≤ l.have_.toNat := by
      split
      · exact Nat.le_refl _
      · next notGt => exact UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp notGt)
    have cpLength0 : (if s.length > l.have_ then l.have_ else s.length).toNat ≤ s.length.toNat := by
      split
      · next gt => exact Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp gt)
      · exact Nat.le_refl _
    generalize hcp : (if s.length > l.have_ then l.have_ else s.length) = cp
    have cpHave : cp.toNat ≤ l.have_.toNat := hcp ▸ cpHave0
    have cpLength : cp.toNat ≤ s.length.toNat := hcp ▸ cpLength0
    let l1 : IL := { l with copy := cp }
    have inv1 : GzInv e l1 h z s used := inv.scratch ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    split
    · next nonzero =>
      have cpPos : 0 < cp.toNat := by
        have : cp ≠ 0 := by simpa using nonzero
        exact Nat.pos_of_ne_zero (fun z0 => this (UInt32.toNat_inj.mp (by simpa using z0)))
      have pos : 0 < l1.have_.toNat := by change 0 < l.have_.toNat; omega
      cases head : s.head with
      | none =>
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact gz_extraCrcK valid inv1 cpHave pos range flags lenOk cpLength cont
      | some ref =>
        cases ref with
        | tab i =>
          obtain ⟨g, g0, get, get0, xm, _, _, xp, _, _, load⟩ := inv1.record valid head
          rw [head] at load
          simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
          rw [runX_bind, runX_lift_ok load]
          simp only []
          split
          · next extraSet =>
            have nonnull : g.extra ≠ .null := by simpa using extraSet
            have same : g.extra = g0.extra := xp.resolve_right nonnull
            have head0 : e.s.head = some (.tab i) := inv.head ▸ head
            have lenFit := extraLen i g head get
            have lenFitNat : s.length.toNat ≤ g.extra_len.toNat := UInt32.le_iff_toNat_le.mp lenFit
            have lenNat0 : (g.extra_len - s.length).toNat = g.extra_len.toNat - s.length.toNat :=
              uint32_sub_toNat lenFitNat
            generalize hlen : g.extra_len - s.length = len at lenNat0
            let l2 : IL := { l1 with len := len }
            have inv2 : GzInv e l2 h z s used := inv1.scratch ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            rw [runX_bind, runX_modify]
            simp only []
            split
            · next lenSmall =>
              -- the copy destination: inside the entry extra region
              obtain ⟨g0', get0', extraRange, _, _⟩ := valid.entryRecord head0
              have g0eq : g0' = g0 := Option.some.inj (get0'.symm.trans get0)
              rw [g0eq] at extraRange
              have range0 := extraRange (by rw [← same]; exact nonnull)
              have member : (⟨g0.extra, g0.extra_max.toNat⟩ : Region) ∈ e.regions := by
                rw [GzEntry.regions_eq head0 get0]; simp
              have sep := inv2.extraSeparate valid head0 get0
              have lenLt : len.toNat < g.extra_max.toNat := UInt32.lt_iff_toNat_lt.mp lenSmall
              have xmNat : g.extra_max.toNat = g0.extra_max.toNat := by rw [xm]
              have extraLenLt := g.extra_len.toNat_lt
              have noWrap : len.toNat + cp.toNat < 2 ^ 32 := by omega
              have nFit0 : len.toNat + (if len + cp > g.extra_max then g.extra_max - len else cp).toNat ≤
                  g0.extra_max.toNat ∧ (if len + cp > g.extra_max then g.extra_max - len else cp).toNat ≤ cp.toNat := by
                split
                · next over =>
                  have over' : g.extra_max.toNat < (len + cp).toNat := UInt32.lt_iff_toNat_lt.mp over
                  rw [UInt32.toNat_add, Nat.mod_eq_of_lt noWrap] at over'
                  rw [uint32_sub_toNat (by omega)]
                  omega
                · next notOver =>
                  have notOver' : (len + cp).toNat ≤ g.extra_max.toNat :=
                    UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp notOver)
                  rw [UInt32.toNat_add, Nat.mod_eq_of_lt noWrap] at notOver'
                  omega
              generalize hn : (if len + cp > g.extra_max then g.extra_max - len else cp) = n at nFit0
              have nFit := nFit0
              rcases range0 with null | ⟨_, writable, _⟩
              · exact absurd null (by rw [← same]; exact nonnull)
              rcases writable rfl with ⟨null, _⟩ | ⟨dref, doff, da0, dptr, dget0, dro0, dfit0⟩
              · exact absurd null (by rw [← same]; exact nonnull)
              obtain ⟨da, dget, dsize⟩ := inv2.sizes.view dget0
              have dro : Space.ro h dref = false := by rw [inv2.readonly]; exact dro0
              obtain ⟨sref, soff, sa, snxt, sget, sfit⟩ := inv2.input pos
              have add : g.extra.add (len.toNat : Int) h = .ok (.ref dref (doff + len.toNat), h) := by
                rw [same, dptr]; exact Ptr.add_nat_ok dget (by omega)
              have disjoint : dref ≠ sref ∨ doff + len.toNat + n.toNat ≤ soff ∨
                  soff + n.toNat ≤ doff + len.toNat := by
                rw [dptr, snxt] at sep
                rcases sep with empty | empty | apart
                · omega
                · change l.have_.toNat = 0 at empty; omega
                · rcases apart with ne | before | after
                  · exact Or.inl ne
                  · exact Or.inr (Or.inl (by omega))
                  · exact Or.inr (Or.inr (by change soff + l.have_.toNat ≤ doff at after; omega))
              have copyRun : memcpyB (.ref dref (doff + len.toNat)) l2.next n.toNat h =
                  .ok ((), Space.put h dref (copyRange da sa (doff + len.toNat) soff n.toNat)) := by
                change memcpyB (.ref dref (doff + len.toNat)) l.next n.toNat h = _
                rw [snxt]
                exact Ptr.memcpy_ok dget sget dro (by omega) (by change soff + l.have_.toNat ≤ sa.size at sfit; omega)
                  disjoint
              have inv3 : GzInv e l2 (Space.put h dref (copyRange da sa (doff + len.toNat) soff n.toNat)) z s used := by
                refine inv2.storeRegion ⟨_, member, doff, dptr⟩ dget dro _ (size_copyRange _ _ _ _ _) ?_
                intro j _ outside
                apply copyRange_getElem?_outside
                rcases Nat.lt_or_ge j (doff + len.toNat) with lo | hi
                · exact Or.inl lo
                · exact Or.inr (Nat.le_of_not_lt fun inside =>
                    outside ⟨_, member, doff, dptr, by omega, show j < doff + g0.extra_max.toNat by omega⟩)
              rw [runX_bind, runX_lift_ok add]
              simp only []
              rw [runX_bind, runX_get]
              simp only []
              rw [runX_bind, runX_lift_ok copyRun]
              simp only []
              have lenOk3 : ExtraLenOk (Space.put h dref (copyRange da sa (doff + len.toNat) soff n.toNat)) s := by
                intro m i' g' head' get'
                apply lenOk m i' g' head'
                have same : (Space.put h dref (copyRange da sa (doff + len.toNat) soff n.toNat)).gzheaders = h.gzheaders := by
                  cases dref <;> simp only [Space.put] <;> (try split) <;> rfl
                rw [← same]; exact get'
              exact gz_extraCrcK valid inv3 cpHave pos range flags lenOk3 cpLength cont
            · exact gz_extraCrcK valid inv2 cpHave pos range flags lenOk cpLength cont
          · exact gz_extraCrcK valid inv1 cpHave pos range flags lenOk cpLength cont
    · exact gz_extraEndK valid inv1 range flags lenOk (fun inv' => cont _ _ _ _ inv' rfl rfl)
  · exact cont _ _ _ _ inv rfl rfl

end extra

/-! ## The header CRC macros -/

section crc
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

/-- One byte store into `hbuf` at offset `k < 4`. -/
theorem GzInv.hbufStep (inv : GzInv e l h z s used) (valid : e.Valid) {b : Nat}
    (ptr : e.c.hbuf = .ref (.blk b) 0) {k : Nat} (small : k < 4) (v : UInt8) :
    ∃ h', (Ptr.ref (BRef.blk b) 0 : BPtr).add (k : Int) h = .ok (.ref (.blk b) k, h) ∧
      store8 (.ref (.blk b) k) v h = .ok ((), h') ∧ GzInv e l h' z s used ∧ h'.gzheaders = h.gzheaders := by
  obtain ⟨b', a, ptr', get, size, ro, _, _⟩ := inv.hbuf valid
  rw [ptr] at ptr'
  have bb : b' = b := by cases ptr'; rfl
  subst bb
  have viewGet : Space.get h (BRef.blk b') = some a := get
  have write : Space.ro h (BRef.blk b') = false := ro
  refine ⟨Space.put h (BRef.blk b') (a.set! k v), ?_, Ptr.store_ok viewGet write (by omega),
    inv.storeHbuf valid ptr get _ (array_set!_size a k v), rfl⟩
  have := Ptr.add_nat_ok (n := k) (off := 0) viewGet (by omega)
  unfold OkOn at this
  rw [Nat.zero_add] at this
  exact this

theorem GzInv.crc2 (inv : GzInv e l h z s used) (valid : e.Valid) :
    ∃ h' v, runX (CRC2 e.c) l h = .ok ((.ok (), l), h') ∧ GzInv e l h' z { s with check := v } used ∧
      h'.gzheaders = h.gzheaders := by
  obtain ⟨b, _, ptr, _⟩ := inv.hbuf valid
  obtain ⟨h1, _, st1, inv1, g1⟩ := inv.hbufStep valid ptr (k := 0) (by decide) l.hold.toUInt8
  obtain ⟨h2, add2, st2, inv2, g2⟩ := inv1.hbufStep valid ptr (k := 1) (by decide) (l.hold >>> 8).toUInt8
  have add2 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 1 h1 = .ok (.ref (.blk b) 1, h1) := by simpa using add2
  obtain ⟨b', a, ptr', get, size, _, _, _⟩ := inv2.hbuf valid
  rw [ptr] at ptr'
  have bb : b' = b := by cases ptr'; rfl
  subst bb
  have E2 := inv2.env valid
  let v : UInt64 := (ZlibF.Spec.crc32Update s.check.toUInt32 ((a.toList.drop 0).take (2 : UInt32).toNat)).toUInt64
  have crc : crc32 s.check e.c.hbuf 2 h2 = .ok (v, h2) := by
    rw [ptr]
    exact Zlib.Crc32.Proofs.ViewsProof.crc32_correct h2 (inv2.statics valid) s.check (BRef.blk b') 0 a get 2
      (by rw [size]; decide)
  refine ⟨_, v, ?_, inv2.setState (s' := { s with check := v }) rfl inv.good.live.mode, ?_⟩
  · unfold CRC2
    rw [runX_bind, runX_get]
    simp only []
    rw [ptr]
    rw [runX_bind, runX_lift_ok st1]
    simp only []
    rw [runX_bind, runX_lift_ok add2]
    simp only []
    rw [runX_bind, runX_lift_ok st2]
    simp only []
    rw [ptr] at crc
    rw [runX_bind, runX_rdS E2]
    simp only []
    rw [runX_bind, runX_lift_ok crc]
    simp only []
    rw [runX_wrS E2]
  · simp only [Zlib.Inflate.Spec.setI]; rw [g2, g1]

theorem GzInv.crc4 (inv : GzInv e l h z s used) (valid : e.Valid) :
    ∃ h' v, runX (CRC4 e.c) l h = .ok ((.ok (), l), h') ∧ GzInv e l h' z { s with check := v } used ∧
      h'.gzheaders = h.gzheaders := by
  obtain ⟨b, _, ptr, _⟩ := inv.hbuf valid
  obtain ⟨h1, _, st1, inv1, g1⟩ := inv.hbufStep valid ptr (k := 0) (by decide) l.hold.toUInt8
  obtain ⟨h2, add2, st2, inv2, g2⟩ := inv1.hbufStep valid ptr (k := 1) (by decide) (l.hold >>> 8).toUInt8
  obtain ⟨h3, add3, st3, inv3, g3⟩ := inv2.hbufStep valid ptr (k := 2) (by decide) (l.hold >>> 16).toUInt8
  obtain ⟨h4, add4, st4, inv4, g4⟩ := inv3.hbufStep valid ptr (k := 3) (by decide) (l.hold >>> 24).toUInt8
  have add2 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 1 h1 = .ok (.ref (.blk b) 1, h1) := by simpa using add2
  have add3 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 2 h2 = .ok (.ref (.blk b) 2, h2) := by simpa using add3
  have add4 : (Ptr.ref (BRef.blk b) 0 : BPtr).add 3 h3 = .ok (.ref (.blk b) 3, h3) := by simpa using add4
  obtain ⟨b', a, ptr', get, size, _, _, _⟩ := inv4.hbuf valid
  rw [ptr] at ptr'
  have bb : b' = b := by cases ptr'; rfl
  subst bb
  have E4 := inv4.env valid
  let v : UInt64 := (ZlibF.Spec.crc32Update s.check.toUInt32 ((a.toList.drop 0).take (4 : UInt32).toNat)).toUInt64
  have crc : crc32 s.check (.ref (.blk b') 0) 4 h4 = .ok (v, h4) :=
    Zlib.Crc32.Proofs.ViewsProof.crc32_correct h4 (inv4.statics valid) s.check (BRef.blk b') 0 a get 4
      (by rw [size]; decide)
  refine ⟨_, v, ?_, inv4.setState (s' := { s with check := v }) rfl inv.good.live.mode, ?_⟩
  · unfold CRC4
    rw [runX_bind, runX_get]
    simp only []
    rw [ptr]
    rw [runX_bind, runX_lift_ok st1]
    simp only []
    rw [runX_bind, runX_lift_ok add2]
    simp only []
    rw [runX_bind, runX_lift_ok st2]
    simp only []
    rw [runX_bind, runX_lift_ok add3]
    simp only []
    rw [runX_bind, runX_lift_ok st3]
    simp only []
    rw [runX_bind, runX_lift_ok add4]
    simp only []
    rw [runX_bind, runX_lift_ok st4]
    simp only []
    rw [runX_bind, runX_rdS E4]
    simp only []
    rw [runX_bind, runX_lift_ok crc]
    simp only []
    rw [runX_wrS E4]
  · simp only [Zlib.Inflate.Spec.setI]; rw [g4, g3, g2, g1]

/-- `if ((state->flags & 0x0200) && (state->wrap & 4)) CRC2(state->check, hold);` then `k`. -/
def crc2K (c : Ctx) (k : X Unit) : X Unit := do
  if ← hcrcOn c.st then CRC2 c
  k

/-- `if ((state->flags & 0x0200) && (state->wrap & 4)) CRC4(state->check, hold);` then `k`. -/
def crc4K (c : Ctx) (k : X Unit) : X Unit := do
  if ← hcrcOn c.st then CRC4 c
  k

/-- What a continuation after a header CRC macro may rely on. -/
def CrcCont (e : GzEntry) (l : IL) (h : Heap) (z : ZStream) (s : InflateState) (used : Nat) (k : X Unit) : Prop :=
  ∀ h' s', GzInv e l h' z s' used → s'.mode = s.mode → s'.flags = s.flags → s'.length = s.length →
    h'.gzheaders = h.gzheaders → GzRuns e k l h'

theorem gz_crc2K {k : X Unit} (valid : e.Valid) (inv : GzInv e l h z s used) (cont : CrcCont e l h z s used k) :
    GzRuns e (crc2K e.c k) l h := by
  unfold GzRuns crc2K
  rw [runX_bind, runX_lift_ok (inv.hcrcOn_run valid)]
  simp only []
  split
  · obtain ⟨h', v, run, inv', g'⟩ := inv.crc2 valid
    rw [runX_bind, run]
    simp only []
    exact cont h' _ inv' rfl rfl rfl g'
  · exact cont h s inv rfl rfl rfl rfl

theorem gz_crc4K {k : X Unit} (valid : e.Valid) (inv : GzInv e l h z s used) (cont : CrcCont e l h z s used k) :
    GzRuns e (crc4K e.c k) l h := by
  unfold GzRuns crc4K
  rw [runX_bind, runX_lift_ok (inv.hcrcOn_run valid)]
  simp only []
  split
  · obtain ⟨h', v, run, inv', g'⟩ := inv.crc4 valid
    rw [runX_bind, run]
    simp only []
    exact cont h' _ inv' rfl rfl rfl g'
  · exact cont h s inv rfl rfl rfl rfl

end crc

/-! ## EXLEN, OS, TIME, FLAGS -/

/-- `case EXLEN` with its join points written out. -/
def exlenTop (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  if (s.flags &&& 0x0400) != 0 then
    NEEDBITS 16
    let l ← get
    wrS c.st fun s => { s with length := l.hold.toUInt32 }
    let s ← ldInflateState c.st
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with extra_len := l.hold.toUInt32 }
      crc2K c (do INITBITS; setMode c.st EXTRA; inflate_EXTRA c)
    else crc2K c (do INITBITS; setMode c.st EXTRA; inflate_EXTRA c)
  else
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with extra := .null }
      setMode c.st EXTRA
      inflate_EXTRA c
    else
      setMode c.st EXTRA
      inflate_EXTRA c

theorem inflate_EXLEN_eq (c : Ctx) : inflate_EXLEN c = exlenTop c := rfl

/-- `case OS` with its join points written out. -/
def osTop (c : Ctx) : X Unit := do
  NEEDBITS 16
  let l ← get
  let s ← ldInflateState c.st
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with xflags := (l.hold &&& 0xff).toUInt32.toInt32, os := (l.hold >>> 8).toUInt32.toInt32 }
    crc2K c (do INITBITS; setMode c.st EXLEN; inflate_EXLEN c)
  else crc2K c (do INITBITS; setMode c.st EXLEN; inflate_EXLEN c)

theorem inflate_OS_eq (c : Ctx) : inflate_OS c = osTop c := rfl

/-- `case TIME` with its join points written out. -/
def timeTop (c : Ctx) : X Unit := do
  NEEDBITS 32
  let l ← get
  let s ← ldInflateState c.st
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with time := l.hold }
    crc4K c (do INITBITS; setMode c.st OS; inflate_OS c)
  else crc4K c (do INITBITS; setMode c.st OS; inflate_OS c)

theorem inflate_TIME_eq (c : Ctx) : inflate_TIME c = timeTop c := rfl

/-- `case FLAGS` with its join points written out. -/
def flagsTop (c : Ctx) : X Unit := do
  NEEDBITS 16
  let l ← get
  wrS c.st fun s => { s with flags := l.hold.toUInt32.toInt32 }
  let s ← ldInflateState c.st
  if (s.flags &&& 0xff) != Z_DEFLATED then
    badMode c "unknown compression method"
    return
  else if (s.flags &&& 0xe000) != 0 then
    badMode c "unknown header flags set"
    return
  else if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with text := ((l.hold >>> 8) &&& 1).toUInt32.toInt32 }
    crc2K c (do INITBITS; setMode c.st TIME; inflate_TIME c)
  else crc2K c (do INITBITS; setMode c.st TIME; inflate_TIME c)

theorem inflate_FLAGS_eq (c : Ctx) : inflate_FLAGS c = flagsTop c := rfl

section chain
variable {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}

theorem gz_EXLEN (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = EXLEN)
    (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (inflate_EXLEN e.c) l h := by
  have E := inv.env valid
  rw [inflate_EXLEN_eq]
  unfold exlenTop GzRuns
  rw [runX_bind, runX_ldS E]
  simp only []
  split
  · obtain ⟨r, l1, j, run, inv1, kinds, _, _⟩ := inv.needbits 16 (by decide)
    rw [runX_bind, run]
    rcases kinds with rfl | rfl
    · simp only []
      rw [runX_bind, runX_get]
      simp only []
      let s2 : InflateState := { s with length := l1.hold.toUInt32 }
      have inv2 : GzInv e l1 (setI h e.zs s2) z s2 (used + j) := inv1.setState rfl inv.good.live.mode
      rw [runX_bind, runX_wrS E]
      simp only []
      have E2 := inv2.env valid
      rw [runX_bind, runX_ldS E2]
      simp only []
      have contK : ∀ h3, (∀ i g, s.head = some (.tab i) → h3.gzheaders i = some g →
          l1.hold.toUInt32 ≤ g.extra_len) →
          CrcCont e l1 h3 z s2 (used + j) (do INITBITS; setMode e.c.st EXTRA; inflate_EXTRA e.c) := by
        intro h3 lenOk h' s' inv' m' f' len' g'
        have E' := inv'.env valid
        have inv'' := inv'.initbits.setState (s' := { s' with mode := EXTRA }) rfl
          (by change HEAD ≤ EXTRA ∧ EXTRA ≤ SYNC; decide)
        unfold GzRuns
        rw [runX_bind, runX_INITBITS]
        simp only []
        rw [runX_bind, runX_setMode E']
        simp only []
        refine gz_EXTRA valid inv'' rfl (by change s'.flags ≠ -1 ∧ s'.flags ≠ 0; rw [f']; exact flags) ?_
        intro _ _ i g head get
        have head' : s.head = some (.tab i) := by
          rw [inv.head, ← inv'.head]; exact head
        have get' : h3.gzheaders i = some g := by rw [← g']; exact get
        change s'.length ≤ g.extra_len
        rw [len']
        exact lenOk i g head' get'
      cases head : s.head with
      | none =>
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact gz_crc2K valid inv2 (contK _ (fun i g h0 _ => by rw [head] at h0; cases h0))
      | some ref =>
        cases ref with
        | tab i =>
          obtain ⟨g, _, get, _, _, _, _, _, _, _, load⟩ := inv2.record valid head
          rw [head] at load
          simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
          rw [runX_bind, runX_lift_ok load]
          simp only []
          rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
          simp only []
          have inv3 := inv2.setHeader (g' := { g with extra_len := l1.hold.toUInt32 }) head get
            ⟨rfl, rfl, rfl⟩ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
          refine gz_crc2K valid inv3 (contK _ ?_)
          intro i' g' h0 get'
          have ii : i' = i := by rw [head] at h0; cases h0; rfl
          subst ii
          have : g' = { g with extra_len := l1.hold.toUInt32 } := by
            simp [GzHeaderRef.put, get] at get'
            exact get'.symm
          rw [this]
          exact UInt32.le_refl _
    · exact ⟨_, _, _, rfl, GzDone.leave inv1 (by rw [mode]; decide) (fun _ => flags)
      (ExtraLenOk.of_ne (by rw [mode]; decide))⟩
  · next flagUnset =>
    have noFlag : ∀ s' : InflateState, s'.flags = s.flags → ¬ (s'.flags &&& 0x0400 != 0) = true := by
      intro s' f'; rw [f']; exact flagUnset
    cases head : s.head with
    | none =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have inv1 := inv.setState (s' := { s with mode := EXTRA }) rfl (by change HEAD ≤ EXTRA ∧ EXTRA ≤ SYNC; decide)
      rw [runX_bind, runX_setMode E]
      simp only []
      exact gz_EXTRA valid inv1 rfl flags (fun set => absurd set (noFlag _ rfl))
    | some ref =>
      cases ref with
      | tab i =>
        obtain ⟨g, get, load, inv1⟩ := inv.clearField valid head 0
        replace inv1 : GzInv e l ((GzHeaderRef.tab i).put h { g with extra := .null }) z s used := inv1
        rw [head] at load
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_lift_ok load]
        simp only []
        rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
        simp only []
        have E1 := inv1.env valid
        have inv2 := inv1.setState (s' := { s with mode := EXTRA }) rfl (by change HEAD ≤ EXTRA ∧ EXTRA ≤ SYNC; decide)
        rw [runX_bind, runX_setMode E1]
        simp only []
        exact gz_EXTRA valid inv2 rfl flags (fun set => absurd set (noFlag _ rfl))

/-- The continuation `INITBITS; state->mode = M;` then case `M`. -/
theorem gz_initThen {k : X Unit} {m : UInt32} (valid : e.Valid) (inv : GzInv e l h z s used)
    (range : HEAD ≤ m ∧ m ≤ SYNC)
    (next : ∀ h' s', GzInv e { l with hold := 0, bits := 0 } h' z s' used → s'.mode = m →
      s'.flags = s.flags → GzRuns e k { l with hold := 0, bits := 0 } h') :
    GzRuns e (do INITBITS; setMode e.c.st m; k) l h := by
  have E := inv.env valid
  have inv1 := inv.initbits.setState (s' := { s with mode := m }) rfl range
  unfold GzRuns
  rw [runX_bind, runX_INITBITS]
  simp only []
  rw [runX_bind, runX_setMode E]
  simp only []
  exact next _ _ inv1 rfl rfl

theorem gz_OS (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = OS)
    (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (inflate_OS e.c) l h := by
  have E := inv.env valid
  rw [inflate_OS_eq]
  unfold osTop GzRuns
  obtain ⟨r, l1, j, run, inv1, kinds, _, _⟩ := inv.needbits 16 (by decide)
  rw [runX_bind, run]
  rcases kinds with rfl | rfl
  · simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_ldS E]
    simp only []
    have contK : ∀ h3, CrcCont e l1 h3 z s (used + j) (do INITBITS; setMode e.c.st EXLEN; inflate_EXLEN e.c) := by
      intro h3 h' s' inv' _ f' _ _
      exact gz_initThen valid inv' (by change HEAD ≤ EXLEN ∧ EXLEN ≤ SYNC; decide)
        (fun h'' s'' inv'' m'' f'' => gz_EXLEN valid inv'' m'' (by rw [f'', f']; exact flags))
    cases head : s.head with
    | none =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact gz_crc2K valid inv1 (contK _)
    | some ref =>
      cases ref with
      | tab i =>
        obtain ⟨g, _, get, _, _, _, _, _, _, _, load⟩ := inv1.record valid head
        rw [head] at load
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_lift_ok load]
        simp only []
        rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
        simp only []
        exact gz_crc2K valid (inv1.setHeader head get ⟨rfl, rfl, rfl⟩ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)) (contK _)
  · exact ⟨_, _, _, rfl, GzDone.leave inv1 (by rw [mode]; decide) (fun _ => flags)
      (ExtraLenOk.of_ne (by rw [mode]; decide))⟩

theorem gz_TIME (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = TIME)
    (flags : s.flags ≠ -1 ∧ s.flags ≠ 0) :
    GzRuns e (inflate_TIME e.c) l h := by
  have E := inv.env valid
  rw [inflate_TIME_eq]
  unfold timeTop GzRuns
  obtain ⟨r, l1, j, run, inv1, kinds, _, _⟩ := inv.needbits 32 (by decide)
  rw [runX_bind, run]
  rcases kinds with rfl | rfl
  · simp only []
    rw [runX_bind, runX_get]
    simp only []
    rw [runX_bind, runX_ldS E]
    simp only []
    have contK : ∀ h3, CrcCont e l1 h3 z s (used + j) (do INITBITS; setMode e.c.st OS; inflate_OS e.c) := by
      intro h3 h' s' inv' _ f' _ _
      exact gz_initThen valid inv' (by change HEAD ≤ OS ∧ OS ≤ SYNC; decide)
        (fun h'' s'' inv'' m'' f'' => gz_OS valid inv'' m'' (by rw [f'', f']; exact flags))
    cases head : s.head with
    | none =>
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact gz_crc4K valid inv1 (contK _)
    | some ref =>
      cases ref with
      | tab i =>
        obtain ⟨g, _, get, _, _, _, _, _, _, _, load⟩ := inv1.record valid head
        rw [head] at load
        simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
        rw [runX_bind, runX_lift_ok load]
        simp only []
        rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
        simp only []
        exact gz_crc4K valid (inv1.setHeader head get ⟨rfl, rfl, rfl⟩ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)) (contK _)
  · exact ⟨_, _, _, rfl, GzDone.leave inv1 (by rw [mode]; decide) (fun _ => flags)
      (ExtraLenOk.of_ne (by rw [mode]; decide))⟩

/-- A flags word whose method byte is 8 is neither 0 nor -1. -/
theorem flags_of_method {v : Int32} (method : ¬ (v &&& 0xff != Z_DEFLATED) = true) : v ≠ -1 ∧ v ≠ 0 := by
  have eq : v &&& 0xff = Z_DEFLATED := by simpa using method
  constructor
  · intro m; rw [m] at eq; revert eq; decide
  · intro m; rw [m] at eq; revert eq; decide

theorem gz_FLAGS (valid : e.Valid) (inv : GzInv e l h z s used) (mode : s.mode = FLAGS) :
    GzRuns e (inflate_FLAGS e.c) l h := by
  have E := inv.env valid
  rw [inflate_FLAGS_eq]
  unfold flagsTop GzRuns
  obtain ⟨r, l1, j, run, inv1, kinds, _, _⟩ := inv.needbits 16 (by decide)
  rw [runX_bind, run]
  rcases kinds with rfl | rfl
  · simp only []
    rw [runX_bind, runX_get]
    simp only []
    let s2 : InflateState := { s with flags := l1.hold.toUInt32.toInt32 }
    have inv2 : GzInv e l1 (setI h e.zs s2) z s2 (used + j) := inv1.setState rfl inv.good.live.mode
    have E2 := inv2.env valid
    rw [runX_bind, runX_wrS E]
    simp only []
    rw [runX_bind, runX_ldS E2]
    simp only []
    split
    · obtain ⟨i, _, bad⟩ := tcBadMode_run (c := e.c) "unknown compression method" lit_unknown_compression_method
        valid.env.strm valid.env.st E2.hz E2.hs
      rw [runX_bind, runX_lift_ok bad]
      exact ⟨_, _, _, rfl, GzDone.bad inv2 i⟩
    · next method =>
      have flags2 : s2.flags ≠ -1 ∧ s2.flags ≠ 0 := flags_of_method method
      split
      · obtain ⟨i, _, bad⟩ := tcBadMode_run (c := e.c) "unknown header flags set" lit_unknown_header_flags
          valid.env.strm valid.env.st E2.hz E2.hs
        rw [runX_bind, runX_lift_ok bad]
        exact ⟨_, _, _, rfl, GzDone.bad inv2 i⟩
      · have contK : ∀ h3, CrcCont e l1 h3 z s2 (used + j) (do INITBITS; setMode e.c.st TIME; inflate_TIME e.c) := by
          intro h3 h' s' inv' _ f' _ _
          exact gz_initThen valid inv' (by change HEAD ≤ TIME ∧ TIME ≤ SYNC; decide)
            (fun h'' s'' inv'' m'' f'' => gz_TIME valid inv'' m'' (by rw [f'', f']; exact flags2))
        cases head : s.head with
        | none =>
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          exact gz_crc2K valid inv2 (contK _)
        | some ref =>
          cases ref with
          | tab i =>
            obtain ⟨g, _, get, _, _, _, _, _, _, _, load⟩ := inv2.record valid head
            rw [head] at load
            simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
            rw [runX_bind, runX_lift_ok load]
            simp only []
            rw [runX_bind, runX_lift_ok (stGzHeader_run get _)]
            simp only []
            exact gz_crc2K valid (inv2.setHeader head get ⟨rfl, rfl, rfl⟩ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl))
              (contK _)
  · exact ⟨_, _, _, rfl, GzDone.leave inv1 (by rw [mode]; decide) (fun notFlags => absurd mode notFlags)
      (ExtraLenOk.of_ne (by rw [mode]; decide))⟩

end chain

end Zlib.Inflate.Proofs
