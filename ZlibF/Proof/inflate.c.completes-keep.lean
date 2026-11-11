import ZlibF.Proof.«inflate.c.borrow-stable-run»

/-!
# inflate.c: what one `inflate` run keeps (relation and primitives)

`Keeps h h'` relates the heap before and after a successful run of a piece of
the translated `inflate`. It is proved from each actual operation, with no
`Good` or frame premise, in the style of `inflate.c.borrow-stable-*`.

* Allocation metadata: the static tables and the failure oracle are unchanged,
  the call and block counters only grow.
* Byte objects (other than borrowed string views): every array present after
  either has the size of the array present before, or is new and smaller
  than `2^32` bytes.
* Decoder records: every decoder record present after was present before, with
  the same gzip header pointer; it does not newly enter `SYNC`; it is in `MEM`
  only if it was; a set window pointer is kept; a new window pointer names a
  block numbered at least the old `nextBlk`.

The one place that sets `MEM` (`inflate_leave` after a refused window
allocation) is treated separately, in `inflate.c.completes-keep-run`.
-/

namespace Zlib.Inflate.KeepProofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The size bound of a byte object created by one `inflate` run. -/
def small : Nat := 2 ^ 32

/-- The control fields of one decoder record from `s` (in heap `h`) to `s'`. -/
structure Ctl (h : Heap) (s s' : InflateState) : Prop where
  head : s'.head = s.head
  sync : s.mode ≠ SYNC → s'.mode ≠ SYNC
  mem : s'.mode = MEM → s.mode = MEM
  win : s.window ≠ .null → s'.window = s.window
  fresh : s'.window = s.window ∨ ∃ w, s'.window = .ref (.blk w) 0 ∧ h.nextBlk ≤ w

theorem Ctl.refl (h : Heap) (s : InflateState) : Ctl h s s :=
  ⟨rfl, id, id, fun _ => rfl, Or.inl rfl⟩

theorem Ctl.of_fields {h : Heap} {s s' : InflateState} (hd : s'.head = s.head) (hm : s'.mode = s.mode)
    (hw : s'.window = s.window) : Ctl h s s' :=
  ⟨hd, fun n => hm ▸ n, fun m => hm ▸ m, fun _ => hw, Or.inl hw⟩

theorem Ctl.trans {h h1 : Heap} {s s1 s2 : InflateState} (le : h.nextBlk ≤ h1.nextBlk)
    (a : Ctl h s s1) (b : Ctl h1 s1 s2) : Ctl h s s2 := by
  refine ⟨b.head.trans a.head, fun n => b.sync (a.sync n), fun m => a.mem (b.mem m), ?_, ?_⟩
  · intro n
    have e1 := a.win n
    rw [b.win (by rw [e1]; exact n), e1]
  · rcases b.fresh with e | ⟨w, e, lw⟩
    · rw [e]; exact a.fresh
    · exact Or.inr ⟨w, e, Nat.le_trans le lw⟩

/-- A field update of a decoder record that keeps its control fields: the
header pointer and the window are unchanged, and the mode is unchanged or set
to a mode other than `SYNC` and `MEM`. -/
def WrOk (f : InflateState → InflateState) : Prop :=
  ∀ s, (f s).head = s.head ∧ (f s).window = s.window ∧
    ((f s).mode = s.mode ∨ ((f s).mode ≠ SYNC ∧ (f s).mode ≠ MEM))

theorem WrOk.ctl {f : InflateState → InflateState} (hf : WrOk f) (h : Heap) (s : InflateState) :
    Ctl h s (f s) := by
  obtain ⟨hd, w, m⟩ := hf s
  refine ⟨hd, ?_, ?_, fun _ => w, Or.inl w⟩
  · intro n; rcases m with e | ⟨e, _⟩
    · rw [e]; exact n
    · exact e
  · intro e; rcases m with e' | ⟨_, e'⟩
    · rw [← e']; exact e
    · exact absurd e e'

/-- A byte reference that is not a borrowed string view. -/
def NotStr (ref : BRef) : Prop := ∀ i, ref ≠ .str i

/-- An array present after has an old size, or is new and small. -/
def SizeKept (h h' : Heap) (ref : BRef) : Prop :=
  ∀ a', Space.get h' ref = some a' → (∃ a, Space.get h ref = some a ∧ a'.size = a.size) ∨ a'.size < small

structure Keeps (h h' : Heap) : Prop where
  static : h'.static = h.static
  allocOk : h'.allocOk = h.allocOk
  nalloc : h.nalloc ≤ h'.nalloc
  next : h.nextBlk ≤ h'.nextBlk
  sizes : ∀ ref, NotStr ref → SizeKept h h' ref
  states : ∀ j s', h'.istates j = some s' → ∃ s, h.istates j = some s ∧ Ctl h s s'

theorem Keeps.refl (h : Heap) : Keeps h h :=
  ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ a' g => Or.inl ⟨a', g, rfl⟩,
    fun _ s' g => ⟨s', g, Ctl.refl h s'⟩⟩

theorem Keeps.trans {h h1 h2 : Heap} (a : Keeps h h1) (b : Keeps h1 h2) : Keeps h h2 := by
  refine ⟨b.static.trans a.static, b.allocOk.trans a.allocOk, Nat.le_trans a.nalloc b.nalloc,
    Nat.le_trans a.next b.next, ?_, ?_⟩
  · intro ref n a2 g2
    rcases b.sizes ref n a2 g2 with ⟨a1, g1, e1⟩ | s
    · rcases a.sizes ref n a1 g1 with ⟨a0, g0, e0⟩ | s
      · exact Or.inl ⟨a0, g0, e1.trans e0⟩
      · exact Or.inr (e1 ▸ s)
    · exact Or.inr s
  · intro j s2 g2
    obtain ⟨s1, g1, c1⟩ := b.states j s2 g2
    obtain ⟨s0, g0, c0⟩ := a.states j s1 g1
    exact ⟨s0, g0, Ctl.trans a.next c0 c1⟩

/-- The byte views as a function of the heap. -/
theorem getB (h : Heap) (ref : BRef) : Space.get h ref = (match ref with
    | .blk b => h.bytes b
    | .str i => staticStringBytes h i
    | .dstate_depth id => (h.dstates id).map (·.depth)
    | .st_dist_code => some h.static.dist_code
    | .st_length_code => some h.static.length_code) := by
  cases ref <;> rfl

/-- A heap change that touches none of the tables `Keeps` observes. -/
theorem Keeps.of_tables {h h' : Heap} (bytes : h'.bytes = h.bytes) (dstates : h'.dstates = h.dstates)
    (istates : h'.istates = h.istates) (static : h'.static = h.static) (allocOk : h'.allocOk = h.allocOk)
    (nalloc : h'.nalloc = h.nalloc) (next : h'.nextBlk = h.nextBlk) : Keeps h h' := by
  refine ⟨static, allocOk, nalloc ▸ Nat.le_refl _, next ▸ Nat.le_refl _, ?_, ?_⟩
  · intro ref n a' g
    left
    refine ⟨a', ?_, rfl⟩
    rw [← g]
    cases ref with
    | str i => exact absurd rfl (n i)
    | _ => simp only [getB, bytes, dstates, static]
  · intro j s' g
    exact ⟨s', istates ▸ g, Ctl.refl h s'⟩

/-! ## The monadic rules -/

def KeepM {α : Type} (m : M α) : Prop :=
  ∀ h a after, m h = .ok (a, after) → Keeps h after

theorem KeepM.pure {α : Type} (a : α) : KeepM (pure a : M α) := by
  intro h v after hr
  cases hr
  exact Keeps.refl h

theorem KeepM.ub {α : Type} (what : String) : KeepM (C.ub what : M α) := by
  intro h value after hr
  cases hr

theorem KeepM.of_same {α : Type} {m : M α} (same : ∀ h a after, m h = .ok (a, after) → after = h) :
    KeepM m := by
  intro h a after hr
  rw [same h a after hr]
  exact Keeps.refl h

theorem KeepM.bind {α β : Type} {m : M α} {f : α → M β}
    (hm : KeepM m) (hf : ∀ a, KeepM (f a)) : KeepM (m >>= f) := by
  intro h value after hr
  rw [bind_app] at hr
  cases he : m h with
  | error e => simp [he] at hr
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [he] at hr
    exact (hm h a h1 he).trans (hf a h1 value after hr)

theorem KeepM.ite {α : Type} (p : Prop) [Decidable p] {a b : M α}
    (ha : KeepM a) (hb : KeepM b) : KeepM (if p then a else b) := by
  split <;> assumption

theorem KeepM.cwhile_go {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, KeepM (cond s)) (hb : ∀ s, KeepM (body s)) (n : Nat) (s : σ) :
    KeepM (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => intro h v after hr; cases hr
  | succ n ih =>
    rw [cwhile.go]
    apply KeepM.bind (hc s)
    rintro ⟨c, s'⟩
    apply KeepM.ite
    · exact KeepM.bind (hb s') (fun t => ih t)
    · exact KeepM.pure _

theorem KeepM.cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, KeepM (cond s)) (hb : ∀ s, KeepM (body s)) (s : σ) :
    KeepM (C.cwhile cond body s) := KeepM.cwhile_go cond body hc hb fuel s

theorem KeepM.cdoWhile_go {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, KeepM (body s)) (hc : ∀ s, KeepM (cond s)) (n : Nat) (s : σ) :
    KeepM (cdoWhile.go body cond n s) := by
  induction n generalizing s with
  | zero => intro h v after hr; cases hr
  | succ n ih =>
    rw [cdoWhile.go]
    apply KeepM.bind (hb s)
    intro s'
    apply KeepM.bind (hc s')
    rintro ⟨c, t⟩
    exact KeepM.ite _ (ih t) (KeepM.pure _)

theorem KeepM.cdoWhile {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, KeepM (body s)) (hc : ∀ s, KeepM (cond s)) (s : σ) :
    KeepM (C.cdoWhile body cond s) := KeepM.cdoWhile_go body cond hb hc fuel s

theorem KeepM.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (keep : ∀ value member state, KeepM (body value member state))
    (initial : β) : KeepM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact KeepM.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply KeepM.bind (keep head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact KeepM.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => keep value (by simp [member]) state) next

/-! ## Reads -/

theorem keep_ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : KeepM (p.add k) := by
  apply KeepM.of_same
  intro h value after hr
  unfold Ptr.add at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : KeepM (Ptr.load p : M T) := by
  apply KeepM.of_same
  intro h value after hr
  unfold Ptr.load at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_ptr_index {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) :
    KeepM (Ptr.index p k : M T) := by
  unfold Ptr.index
  exact KeepM.bind (keep_ptr_add _ _) (fun _ => keep_ptr_load _)

theorem keep_load8 (p : BPtr) : KeepM (load8 p) := keep_ptr_load p

theorem keep_index8 (p : BPtr) (i : Int) : KeepM (index8 p i) := keep_ptr_index p i

theorem keep_ptr_diff {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    KeepM (Ptr.diff p q) := by
  apply KeepM.of_same
  intro h value after hr
  unfold Ptr.diff at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_ptr_lt {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    KeepM (Ptr.lt p q) := by
  apply KeepM.of_same
  intro h value after hr
  unfold Ptr.lt at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_ldZStream (p : ZStreamPtr) : KeepM (ldZStream p) := by
  apply KeepM.of_same
  intro h value after hr
  unfold ldZStream at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_ldInflateState (p : InflateStatePtr) : KeepM (ldInflateState p) := by
  apply KeepM.of_same
  intro h value after hr
  unfold ldInflateState at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_ldGzHeader (p : GzHeaderPtr) : KeepM (ldGzHeader p) := by
  apply KeepM.of_same
  intro h value after hr
  unfold ldGzHeader at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_castInflateState (p : Option StateRef) : KeepM (castInflateState p) := by
  apply KeepM.of_same
  intro h value after hr
  unfold castInflateState at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_strLitRef (s : String) : KeepM (strLitRef s) := by
  apply KeepM.of_same
  intro h value after hr
  unfold strLitRef at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem keep_strlenB (p : BPtr) : KeepM (strlenB p) := by
  apply KeepM.of_same
  intro h value after hr
  unfold strlenB at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

/-! ## Writes to records other than decoder records -/

theorem keep_stZStream (p : ZStreamPtr) (z : ZStream) : KeepM (stZStream p z) := by
  intro h v after hr
  cases p with
  | none => simp [stZStream] at hr
  | some r =>
    simp only [stZStream] at hr
    split at hr
    · split at hr
      · cases hr
      · cases hr
        cases r with
        | tab i =>
          simp only [ZStreamRef.put]
          split
          · exact Keeps.of_tables rfl rfl rfl rfl rfl rfl rfl
          · exact Keeps.refl h
        | in_gzstate_strm i =>
          simp only [ZStreamRef.put]
          split
          · exact Keeps.of_tables rfl rfl rfl rfl rfl rfl rfl
          · exact Keeps.refl h
    · cases hr

theorem keep_stGzHeader (p : GzHeaderPtr) (g : GzHeader) : KeepM (stGzHeader p g) := by
  intro h v after hr
  cases p with
  | none => simp [stGzHeader] at hr
  | some r =>
    simp only [stGzHeader] at hr
    split at hr
    · split at hr
      · cases hr
      · cases hr
        cases r with
        | tab i =>
          simp only [GzHeaderRef.put]
          split
          · exact Keeps.of_tables rfl rfl rfl rfl rfl rfl rfl
          · exact Keeps.refl h
    · cases hr

/-! ## Writes to byte, word and code arrays -/

/-- Replacing a byte array by one of the same size. -/
theorem keeps_put_bytes {h : Heap} {r : BRef} {a a' : Array UInt8} (g : Space.get h r = some a)
    (size : a'.size = a.size) : Keeps h (Space.put h r a') := by
  cases r with
  | blk b =>
    refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, fun j s' g' => ⟨s', g', Ctl.refl h s'⟩⟩
    intro ref n x gx
    left
    cases ref with
    | blk c =>
      simp only [getB, Space.put] at gx g ⊢
      rw [upd_apply] at gx
      by_cases e : c = b
      · subst e
        rw [if_pos rfl] at gx
        cases gx
        exact ⟨a, g, size⟩
      · rw [if_neg e] at gx
        exact ⟨x, gx, rfl⟩
    | str i => exact absurd rfl (n i)
    | _ => exact ⟨x, gx, rfl⟩
  | str i => exact Keeps.refl h
  | dstate_depth id =>
    simp only [getB] at g
    cases hd : h.dstates id with
    | none => rw [hd] at g; cases g
    | some d =>
      rw [hd] at g
      cases g
      have put : Space.put h (BRef.dstate_depth id) a' =
          { h with dstates := upd h.dstates id (some { d with depth := a' }) } := by
        show (match h.dstates id with
          | some s => { h with dstates := upd h.dstates id (some { s with depth := a' }) }
          | none => h) = _
        rw [hd]
      rw [put]
      refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, fun j s' g' => ⟨s', g', Ctl.refl h s'⟩⟩
      intro ref n x gx
      left
      cases ref with
      | dstate_depth c =>
        simp only [getB] at gx ⊢
        rw [upd_apply] at gx
        by_cases e : c = id
        · subst e
          rw [if_pos rfl] at gx
          cases gx
          exact ⟨d.depth, by rw [hd]; rfl, size⟩
        · rw [if_neg e] at gx
          exact ⟨x, gx, rfl⟩
      | str i => exact absurd rfl (n i)
      | _ => exact ⟨x, gx, rfl⟩
  | st_dist_code => exact Keeps.refl h
  | st_length_code => exact Keeps.refl h

/-- Replacing a word array keeps every byte array and every decoder's control fields. -/
theorem keeps_put_words {h : Heap} {r : WRef} (a' : Array UInt16) : Keeps h (Space.put h r a') := by
  cases r with
  | blk b => exact Keeps.of_tables rfl rfl rfl rfl rfl rfl rfl
  | dstate_bl_count id =>
    show Keeps h (match h.dstates id with
      | some s => { h with dstates := upd h.dstates id (some { s with bl_count := a' }) } | none => h)
    cases hd : h.dstates id with
    | none => exact Keeps.refl h
    | some d =>
      refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, fun j s' g' => ⟨s', g', Ctl.refl h s'⟩⟩
      intro ref n x gx
      left
      refine ⟨x, ?_, rfl⟩
      rw [← gx]
      cases ref with
      | dstate_depth c =>
        simp only [getB]
        rw [upd_apply]
        by_cases e : c = id
        · subst e; rw [if_pos rfl, hd]; rfl
        · rw [if_neg e]
      | str i => exact absurd rfl (n i)
      | _ => rfl
  | istate_lens id =>
    show Keeps h (match h.istates id with
      | some s => { h with istates := upd h.istates id (some { s with lens := a' }) } | none => h)
    cases hs : h.istates id with
    | none => exact Keeps.refl h
    | some d =>
      refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
      · intro ref n x gx
        left
        refine ⟨x, ?_, rfl⟩
        rw [← gx]
        cases ref with
        | str i => exact absurd rfl (n i)
        | _ => rfl
      · intro j s' g'
        simp only [] at g'
        rw [upd_apply] at g'
        by_cases e : j = id
        · subst e
          rw [if_pos rfl] at g'
          cases g'
          exact ⟨d, hs, Ctl.of_fields rfl rfl rfl⟩
        · rw [if_neg e] at g'
          exact ⟨s', g', Ctl.refl h s'⟩
  | istate_work id =>
    show Keeps h (match h.istates id with
      | some s => { h with istates := upd h.istates id (some { s with work := a' }) } | none => h)
    cases hs : h.istates id with
    | none => exact Keeps.refl h
    | some d =>
      refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
      · intro ref n x gx
        left
        refine ⟨x, ?_, rfl⟩
        rw [← gx]
        cases ref with
        | str i => exact absurd rfl (n i)
        | _ => rfl
      · intro j s' g'
        simp only [] at g'
        rw [upd_apply] at g'
        by_cases e : j = id
        · subst e
          rw [if_pos rfl] at g'
          cases g'
          exact ⟨d, hs, Ctl.of_fields rfl rfl rfl⟩
        · rw [if_neg e] at g'
          exact ⟨s', g', Ctl.refl h s'⟩

theorem keeps_put_codes {h : Heap} {r : CodeRef} (a' : Array Code) : Keeps h (Space.put h r a') := by
  cases r with
  | istate_codes id =>
    show Keeps h (match h.istates id with
      | some s => { h with istates := upd h.istates id (some { s with codes := a' }) } | none => h)
    cases hs : h.istates id with
    | none => exact Keeps.refl h
    | some d =>
      refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
      · intro ref n x gx
        left
        refine ⟨x, ?_, rfl⟩
        rw [← gx]
        cases ref with
        | str i => exact absurd rfl (n i)
        | _ => rfl
      · intro j s' g'
        simp only [] at g'
        rw [upd_apply] at g'
        by_cases e : j = id
        · subst e
          rw [if_pos rfl] at g'
          cases g'
          exact ⟨d, hs, Ctl.of_fields rfl rfl rfl⟩
        · rw [if_neg e] at g'
          exact ⟨s', g', Ctl.refl h s'⟩
  | st_lenfix => exact Keeps.refl h
  | st_distfix => exact Keeps.refl h

/-- A successful store replaces one array by an array of the same size. -/
theorem store_put {R T : Type} [Space Heap R T] {p : Ptr R} {v : T} {h after : Heap} {u : Unit}
    (hr : Ptr.store p v h = .ok (u, after)) :
    ∃ (r : R) (a a' : Array T), Space.get h r = some a ∧ a'.size = a.size ∧ after = Space.put h r a' := by
  cases p with
  | null => cases hr
  | ref r off =>
    simp only [Ptr.store] at hr
    split at hr
    · cases hr
    · rename_i a g
      split at hr
      · cases hr
      · split at hr
        · cases hr
          exact ⟨r, a, _, g, by simp, Space.modify_eq h r a _ g⟩
        · cases hr

theorem keep_store8 (p : BPtr) (v : UInt8) : KeepM (store8 p v) := by
  intro h value after hr
  obtain ⟨r, a, a', g, size, e⟩ := store_put hr
  rw [e]
  exact keeps_put_bytes g size

theorem keep_store_word (p : WPtr) (v : UInt16) : KeepM (Ptr.store p v) := by
  intro h value after hr
  obtain ⟨r, a, a', g, size, e⟩ := store_put hr
  rw [e]
  exact keeps_put_words _

theorem keep_store_code (p : CodePtr) (v : Code) : KeepM (Ptr.store p v) := by
  intro h value after hr
  obtain ⟨r, a, a', g, size, e⟩ := store_put hr
  rw [e]
  exact keeps_put_codes _

theorem keep_memcpyB (dst src : BPtr) (n : Nat) : KeepM (memcpyB dst src n) := by
  intro h value after hr
  unfold memcpyB Ptr.memcpy at hr
  split at hr
  · rename_i rd od rs os
    split at hr
    · rename_i da sa gd gs
      split at hr
      · contradiction
      · split at hr
        · split at hr
          · cases hr
            rw [Space.modify_eq h rd da _ gd]
            exact keeps_put_bytes gd (size_copyRange _ _ _ _ _)
          · contradiction
        · contradiction
    · contradiction
  · contradiction

/-! ## Allocation -/

theorem keep_allocBytes (a : Array UInt8) (small_a : a.size < small) : KeepM (allocBytes a) := by
  intro h value after hr
  unfold allocBytes at hr
  split at hr
  · contradiction
  · rename_i unused
    cases hr
    refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_succ _, ?_, ?_⟩
    · intro ref n x gx
      cases ref with
      | blk c =>
        simp only [getB] at gx ⊢
        rw [upd_apply] at gx
        by_cases e : c = h.nextBlk
        · rw [if_pos e] at gx
          cases gx
          exact Or.inr small_a
        · rw [if_neg e] at gx
          exact Or.inl ⟨x, gx, rfl⟩
      | str i => exact absurd rfl (n i)
      | _ => exact Or.inl ⟨x, gx, rfl⟩
    · intro j s' g'
      exact ⟨s', g', Ctl.refl h s'⟩

theorem keep_allocB (n : Nat) (small_n : n < small) : KeepM (allocB n) := by
  intro h value after hr
  unfold allocB at hr
  split at hr
  · split at hr
    · contradiction
    · cases hr
      refine ⟨rfl, rfl, Nat.le_succ _, Nat.le_succ _, ?_, ?_⟩
      · intro ref k x gx
        cases ref with
        | blk c =>
          simp only [getB] at gx ⊢
          rw [upd_apply] at gx
          by_cases e : c = h.nextBlk
          · rw [if_pos e] at gx
            cases gx
            exact Or.inr (by simpa using small_n)
          · rw [if_neg e] at gx
            exact Or.inl ⟨x, gx, rfl⟩
        | str i => exact absurd rfl (k i)
        | _ => exact Or.inl ⟨x, gx, rfl⟩
      · intro j s' g'
        exact ⟨s', g', Ctl.refl h s'⟩
  · cases hr
    exact ⟨rfl, rfl, Nat.le_succ _, Nat.le_refl _, fun _ _ a' g => Or.inl ⟨a', g, rfl⟩,
      fun _ s' g => ⟨s', g, Ctl.refl h s'⟩⟩

theorem keep_freeB (p : BPtr) : KeepM (freeB p) := by
  intro h value after hr
  unfold freeB at hr
  split at hr
  · cases hr; exact Keeps.refl h
  · split at hr
    · split at hr
      · contradiction
      · cases hr
        refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, fun _ s' g => ⟨s', g, Ctl.refl h s'⟩⟩
        intro ref n x gx
        left
        cases ref with
        | blk c =>
          simp only [getB] at gx ⊢
          rw [upd_apply] at gx
          split at gx
          · cases gx
          · exact ⟨x, gx, rfl⟩
        | str i => exact absurd rfl (n i)
        | _ => exact ⟨x, gx, rfl⟩
    · contradiction
  · contradiction

theorem keep_allocLocalB (n : Nat) (small_n : n < small) : KeepM (allocLocalB n) := by
  intro h value after hr
  exact keep_allocBytes _ (by simpa using small_n) h value after hr

/-! ## Decoder records -/

/-- A load followed by a store of a field update with `WrOk`. -/
theorem keep_wrS (p : InflateStatePtr) (f : InflateState → InflateState) (hf : WrOk f) :
    KeepM (wrS p f) := by
  intro h v after hr
  unfold wrS at hr
  rw [bind_app] at hr
  cases p with
  | none => simp [ldInflateState] at hr
  | some r =>
    cases r with
    | tab i =>
      cases g : h.istates i with
      | none =>
        have e : ldInflateState (some (.tab i)) h =
            .error (.ub "access through a dangling pointer (inflate_state)") := by
          simp [ldInflateState, InflateStateRef.get, g]
        rw [e] at hr
        cases hr
      | some s =>
        have g' : (InflateStateRef.tab i).get h = some s := g
        rw [ldInflateState_ok g'] at hr
        simp only [stInflateState, g'] at hr
        split at hr
        · cases hr
        · cases hr
          rw [InflateStateRef.put_tab g]
          refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
          · intro ref n x gx
            left
            refine ⟨x, ?_, rfl⟩
            rw [← gx]
            cases ref with
            | str k => exact absurd rfl (n k)
            | _ => rfl
          · intro j s' gj
            simp only [] at gj
            rw [upd_apply] at gj
            by_cases e : j = i
            · subst e
              rw [if_pos rfl] at gj
              cases gj
              exact ⟨s, g, hf.ctl h s⟩
            · rw [if_neg e] at gj
              exact ⟨s', gj, Ctl.refl h s'⟩

/-- The same pattern written out, followed by more code. -/
theorem keep_ld_st_bind {β : Type} (p : InflateStatePtr) (f : InflateState → InflateState) (hf : WrOk f)
    (k : Unit → M β) (hk : ∀ u, KeepM (k u)) :
    KeepM (ldInflateState p >>= fun s => stInflateState p (f s) >>= k) := by
  have e : (ldInflateState p >>= fun s => stInflateState p (f s) >>= k) = (wrS p f >>= k) := by
    unfold wrS
    funext h
    simp only [bind_app]
    cases ldInflateState p h with
    | error e => rfl
    | ok q => rfl
  rw [e]
  exact KeepM.bind (keep_wrS p f hf) hk

theorem keep_ld_st (p : InflateStatePtr) (f : InflateState → InflateState) (hf : WrOk f) :
    KeepM (ldInflateState p >>= fun s => stInflateState p (f s)) := keep_wrS p f hf

theorem keep_rdS {α : Type} (p : InflateStatePtr) (f : InflateState → α) : KeepM (rdS p f) :=
  KeepM.bind (keep_ldInflateState p) (fun _ => KeepM.pure _)

theorem keep_wrZ (p : ZStreamPtr) (f : ZStream → ZStream) : KeepM (wrZ p f) :=
  KeepM.bind (keep_ldZStream p) (fun _ => keep_stZStream _ _)

theorem keep_setMode (p : InflateStatePtr) (m : UInt32) (hm : m ≠ SYNC ∧ m ≠ MEM) :
    KeepM (setMode p m) :=
  keep_wrS p _ (fun _ => ⟨rfl, rfl, Or.inr hm⟩)

theorem keep_setMsg (strm : ZStreamPtr) (msg : String) : KeepM (setMsg strm msg) :=
  KeepM.bind (keep_strLitRef _) (fun _ =>
    KeepM.bind (keep_ldZStream _) (fun _ => keep_stZStream _ _))

/-- Proves `WrOk` of a literal field update. -/
macro "wr_ok" : tactic => `(tactic|
  (intro s
   refine ⟨rfl, rfl, ?_⟩
   dsimp only
   first
     | exact Or.inl rfl
     | exact Or.inr ⟨by decide, by decide⟩
     | (split <;> exact Or.inr ⟨by decide, by decide⟩)))

/-- Proves that a mode constant is neither `SYNC` nor `MEM`. -/
macro "mode_ok" : tactic => `(tactic|
  first
    | exact ⟨by decide, by decide⟩
    | (split <;> exact ⟨by decide, by decide⟩))

#print axioms Keeps.trans
#print axioms keeps_put_bytes
#print axioms keep_memcpyB
#print axioms keep_allocB
#print axioms keep_wrS
#print axioms keep_ld_st_bind
end Zlib.Inflate.KeepProofs
