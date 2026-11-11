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

/-- How a gzip header dispatch ends. -/
def GzDone (e : GzEntry) (outcome : Except Ex Unit) (regs : IL) (after : Heap) : Prop :=
  ∃ stream state used, GzInv e regs after stream state used ∧
    ((outcome = .error Ex.leave ∧ FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨
      (outcome = .ok () ∧ (state.mode = TYPE ∨ state.mode = BAD))) ∧
    (state.mode ≠ BAD → state.mode ≠ FLAGS → state.flags ≠ -1 ∧ state.flags ≠ 0)

/-- The program runs and ends in `GzDone`. -/
def GzRuns (e : GzEntry) (x : X Unit) (l : IL) (h : Heap) : Prop :=
  ∃ outcome regs after, runX x l h = .ok ((outcome, regs), after) ∧ GzDone e outcome regs after

/-- A leave from a header mode. -/
theorem GzDone.leave {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}
    (inv : GzInv e l h z s used) (mode : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC)
    (flags : s.mode ≠ FLAGS → s.flags ≠ -1 ∧ s.flags ≠ 0) : GzDone e (.error Ex.leave) l h :=
  ⟨z, s, used, inv, Or.inl ⟨rfl, mode⟩, fun _ notFlags => flags notFlags⟩

/-- A `BAD` result. -/
theorem GzDone.bad {e : GzEntry} {l : IL} {h : Heap} {z : ZStream} {s : InflateState} {used : Nat}
    (inv : GzInv e l h z s used) (i : Nat) :
    GzDone e (.ok ()) l (tcBadHeap h e.r e.zs z s i) :=
  ⟨_, _, used, inv.bad i, Or.inr ⟨rfl, Or.inr rfl⟩, fun notBad => absurd rfl notBad⟩

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
  refine ⟨_, _, _, ?_, ⟨_, _, used, inv3, Or.inr ⟨rfl, Or.inl rfl⟩, fun _ _ => flags⟩⟩
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
    · exact ⟨_, _, _, rfl, GzDone.leave inv' (by rw [mode]; decide) (fun _ => flags)⟩
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
    (mode : FLAGS < s.mode ∧ s.mode ≤ HCRC) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0)
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
    exact ⟨_, _, _, rfl, GzDone.leave inv1 ⟨Nat.le_of_lt mode.1, mode.2⟩ (fun _ => flags)⟩
  · exact cont _ _ _ _ inv1 rfl rfl

theorem gz_strCopyK {sel : GzHeader → BPtr} {cap : GzHeader → UInt32} {k : X Unit} (valid : e.Valid)
    (inv : GzInv e l h z s used)
    (roomOf : ∀ {l' : IL} {h' : Heap} {z' : ZStream} {s' : InflateState} {used' : Nat},
      GzInv e l' h' z' s' used' → FieldRoom e h' sel cap)
    (mode : FLAGS < s.mode ∧ s.mode ≤ HCRC) (flags : s.flags ≠ -1 ∧ s.flags ≠ 0)
    (cont : ∀ l' h' s' used', GzInv e l' h' z s' used' → s'.mode = s.mode → s'.flags = s.flags →
      GzRuns e k l' h') :
    GzRuns e (strCopyK e.c sel cap k) l h := by
  unfold GzRuns strCopyK
  rw [runX_bind, runX_get]
  simp only []
  split
  · next empty =>
    rw [runX_bind, runX_throw]
    exact ⟨_, _, _, rfl, GzDone.leave inv ⟨Nat.le_of_lt mode.1, mode.2⟩ (fun _ => flags)⟩
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
      exact gz_strAdvanceK valid inv2 c2 pos1 mode1 flags1 cont1
    · exact gz_strAdvanceK valid inv1 c2 pos1 mode1 flags1 cont1

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
      (fun inv' => inv'.commentRoom valid) range flags cont
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
      (fun inv' => inv'.nameRoom valid) range flags cont
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

end Zlib.Inflate.Proofs
