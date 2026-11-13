import ZlibF.Proof.«inflate.c.completes-keep-modes»

/-!
# inflate.c: `Keeps` over the mode selector, the loop, `updatewindow` and `inflate`
-/

namespace Zlib.Inflate.KeepProofs
open C Zlib.Inflate
set_option autoImplicit false

theorem rdS_ok {α : Type} {p : InflateStatePtr} {f : InflateState → α} {h h' : Heap} {a : α}
    (hr : rdS p f h = .ok (a, h')) :
    h' = h ∧ ∃ i s, p = some (.tab i) ∧ h.istates i = some s ∧ a = f s := by
  unfold rdS at hr
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
        rw [ldInflateState_ok (show (InflateStateRef.tab i).get h = some s from g)] at hr
        cases hr
        exact ⟨rfl, i, s, rfl, g, rfl⟩

theorem keep_x_inflate_dispatch (c : Ctx) : KeepX c.st (inflate_dispatch c) := by
  unfold inflate_dispatch
  apply KeepX.lift_bind_dep (keep_rdS _ _)
  intro h m h' run
  obtain ⟨rfl, i, s, hst, hs, hm⟩ := rdS_ok run
  by_cases mem : m = MEM
  · subst mem
    simp (config := { decide := true }) only [↓reduceIte]
    intro l r after hr
    cases hr
    exact ⟨Keeps.refl _, fun _ => ⟨i, s, hst, hs, hm.symm⟩⟩
  · have ne : (m == MEM) = false := by simpa using mem
    simp only [ne, Bool.false_eq_true, ite_false]
    apply KeepX.at
    repeat' first
      | with_reducible exact keep_x_inflate_DONE _
      | with_reducible exact keep_x_inflate_LENGTH _
      | with_reducible exact keep_x_inflate_CHECK _
      | with_reducible exact keep_x_inflate_LIT _
      | with_reducible exact keep_x_inflate_MATCH _
      | with_reducible exact keep_x_inflate_DISTEXT _
      | with_reducible exact keep_x_inflate_DIST _
      | with_reducible exact keep_x_inflate_LENEXT _
      | with_reducible exact keep_x_inflate_LEN _
      | with_reducible exact keep_x_inflate_LEN_ _
      | with_reducible exact keep_x_inflate_CODELENS _
      | with_reducible exact keep_x_inflate_LENLENS _
      | with_reducible exact keep_x_inflate_TABLE _
      | with_reducible exact keep_x_inflate_COPY _
      | with_reducible exact keep_x_inflate_COPY_ _
      | with_reducible exact keep_x_inflate_STORED _
      | with_reducible exact keep_x_inflate_TYPEDO _
      | with_reducible exact keep_x_inflate_TYPE _
      | with_reducible exact keep_x_inflate_DICT _
      | with_reducible exact keep_x_inflate_DICTID _
      | with_reducible exact keep_x_inflate_HCRC _
      | with_reducible exact keep_x_inflate_COMMENT _
      | with_reducible exact keep_x_inflate_NAME _
      | with_reducible exact keep_x_inflate_EXTRA _
      | with_reducible exact keep_x_inflate_EXLEN _
      | with_reducible exact keep_x_inflate_OS _
      | with_reducible exact keep_x_inflate_TIME _
      | with_reducible exact keep_x_inflate_FLAGS _
      | with_reducible exact keep_x_inflate_HEAD _
      | keep_x_step

def KeepMAt {α : Type} (m : M α) (h : Heap) : Prop := ∀ a after, m h = .ok (a, after) → Keeps h after

theorem KeepM.bind_dep {α β : Type} {m : M α} {f : α → M β} (hm : KeepM m)
    (hf : ∀ h a h', m h = .ok (a, h') → KeepMAt (f a) h') : KeepM (m >>= f) := by
  intro h b after hr
  rw [bind_app] at hr
  cases e : m h with
  | error x => rw [e] at hr; cases hr
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [e] at hr
    exact (hm h a h1 e).trans (hf h a h1 e b after hr)

theorem KeepMAt.of {α : Type} {m : M α} (hm : KeepM m) (h : Heap) : KeepMAt m h := hm h

theorem KeepMAt.bind_dep {α β : Type} {m : M α} {f : α → M β} {h : Heap} (hm : KeepMAt m h)
    (hf : ∀ a h', m h = .ok (a, h') → KeepMAt (f a) h') : KeepMAt (m >>= f) h := by
  intro b after hr
  rw [bind_app] at hr
  cases e : m h with
  | error x => rw [e] at hr; cases hr
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [e] at hr
    exact (hm a h1 e).trans (hf a h1 e b after hr)

theorem KeepMAt.letFun {α β γ : Type} {X : β → M γ} {F : (β → M γ) → M α} {h : Heap}
    (hX : ∀ u, KeepM (X u)) (hF : ∀ jp : β → M γ, (∀ u, KeepM (jp u)) → KeepMAt (F jp) h) :
    KeepMAt (have jp := X; F jp) h := hF X hX

theorem KeepMAt.ite_dep {α : Type} (p : Prop) [Decidable p] {a b : M α} {h : Heap}
    (ha : p → KeepMAt a h) (hb : ¬ p → KeepMAt b h) : KeepMAt (if p then a else b) h := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem ldInflateState_ok' {p : InflateStatePtr} {h h' : Heap} {s : InflateState}
    (hr : ldInflateState p h = .ok (s, h')) :
    h' = h ∧ ∃ i, p = some (.tab i) ∧ h.istates i = some s := by
  cases p with
  | none => simp [ldInflateState] at hr
  | some r =>
    cases r with
    | tab i =>
      cases g : h.istates i with
      | none => simp [ldInflateState, InflateStateRef.get, g] at hr
      | some s' =>
        rw [ldInflateState_ok (show (InflateStateRef.tab i).get h = some s' from g)] at hr
        cases hr
        exact ⟨rfl, i, rfl, g⟩

theorem bind_ok {α β : Type} {m : M α} {f : α → M β} {h after : Heap} {b : β}
    (hr : (m >>= f) h = .ok (b, after)) : ∃ a h1, m h = .ok (a, h1) ∧ f a h1 = .ok (b, after) := by
  rw [bind_app] at hr
  cases e : m h with
  | error x => rw [e] at hr; cases hr
  | ok p =>
    obtain ⟨a, h1⟩ := p
    rw [e] at hr
    exact ⟨a, h1, rfl, hr⟩

theorem ldZStream_same {p : ZStreamPtr} {h h' : Heap} {z : ZStream} (hr : ldZStream p h = .ok (z, h')) :
    h' = h := by
  unfold ldZStream at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem shl32_same {x n v : UInt32} {h h' : Heap} (hr : shl32 x n h = .ok (v, h')) : h' = h := by
  unfold shl32 at hr
  split at hr
  · cases hr; rfl
  · cases hr

/-- The outcomes of the window allocation. -/
theorem zallocb_info {strm : ZStreamPtr} {n : UInt32} {h h2 : Heap} {w : BPtr}
    (hr : ZALLOCB strm n 1 h = .ok (w, h2)) :
    Keeps h h2 ∧ h2.istates = h.istates ∧
      ((w = .null ∧ h2.nalloc = h.nalloc + 1 ∧ h.allocOk h.nalloc = false) ∨
        w = .ref (.blk h.nextBlk) 0) := by
  unfold ZALLOCB at hr
  obtain ⟨z, h1, e1, hr1⟩ := bind_ok hr
  have s1 := ldZStream_same e1
  subst s1
  clear hr
  revert hr1
  generalize z.zalloc = fz
  intro hr1
  cases fz with
  | null => simp [ub] at hr1
  | fn name =>
    by_cases hn : name = "zcalloc"
    · subst hn
      simp only [] at hr1
      unfold Zlib.Zutil.zcalloc at hr1
      have keep := keep_allocB (n * 1).toNat (UInt32.toNat_lt _) _ w h2 hr1
      refine ⟨keep, ?_, ?_⟩
      · unfold allocB at hr1
        split at hr1
        · split at hr1
          · cases hr1
          · cases hr1; rfl
        · cases hr1; rfl
      · unfold allocB at hr1
        split at hr1
        · split at hr1
          · cases hr1
          · cases hr1; exact Or.inr rfl
        · rename_i bad
          cases hr1
          refine Or.inl ⟨rfl, rfl, ?_⟩
          simp only [not_and] at bad
          exact Bool.eq_false_iff.mpr fun hk => bad hk (C.lt_mallocLimit_of_lt_pow32 (UInt32.toNat_lt _))
    · simp [hn, ub] at hr1

theorem wrS_eq {i : Nat} {f : InflateState → InflateState} {h h' : Heap} {s : InflateState} {u : Unit}
    (hs : h.istates i = some s) (hr : wrS (some (.tab i)) f h = .ok (u, h')) :
    h' = { h with istates := upd h.istates i (some (f s)) } := by
  unfold wrS at hr
  have g' : (InflateStateRef.tab i).get h = some s := hs
  rw [bind_app, ldInflateState_ok g'] at hr
  simp only [stInflateState, g'] at hr
  split at hr
  · cases hr
  · cases hr
    exact InflateStateRef.put_tab hs _

theorem Keeps.put_state {h h2 : Heap} (k : Keeps h h2) (hi : h2.istates = h.istates) {i : Nat}
    {s s' : InflateState} (hs : h.istates i = some s) (c : Ctl h s s') :
    Keeps h { h2 with istates := upd h2.istates i (some s') } := by
  refine ⟨k.static, k.allocOk, k.nalloc, k.next, ?_, ?_, k.gz.trans (Zlib.Deflate.Universal.Params.GzRecordsKept.of_eq rfl),
    k.msgs.trans (StreamMsgs.of_eq rfl rfl)⟩
  · intro ref n x gx
    apply k.sizes ref n x
    rw [← gx]
    cases ref <;> rfl
  · intro j s2 g2
    simp only [] at g2
    rw [upd_apply] at g2
    by_cases e : j = i
    · subst e
      rw [if_pos rfl] at g2
      cases g2
      exact ⟨s, hs, c⟩
    · rw [if_neg e, hi] at g2
      exact ⟨s2, g2, Ctl.refl h s2⟩

/-- Allocating the window into a decoder record whose window is null. -/
theorem keepAt_alloc_window {β : Type} (strm : ZStreamPtr) (i : Nat) (n : UInt32)
    (K : BPtr → Unit → M β) (hK : ∀ w u, KeepM (K w u)) {h : Heap} {s : InflateState}
    (hs : h.istates i = some s) (hnull : s.window = .null) :
    KeepMAt (ZALLOCB strm n 1 >>= fun w =>
      wrS (some (.tab i)) (fun s => { s with window := w }) >>= K w) h := by
  intro a after hr
  obtain ⟨w, h2, e2, hr2⟩ := bind_ok hr
  obtain ⟨k2, ist2, wcase⟩ := zallocb_info e2
  obtain ⟨u, h3, e3, hr3⟩ := bind_ok hr2
  have hs2 : h2.istates i = some s := by rw [ist2]; exact hs
  have h3eq := wrS_eq hs2 e3
  subst h3eq
  have k3 : Keeps h { h2 with istates := upd h2.istates i (some { s with window := w }) } := by
    apply Keeps.put_state k2 ist2 hs
    refine ⟨rfl, id, id, fun n => absurd hnull n, ?_, rfl⟩
    rcases wcase with ⟨wn, _, _⟩ | wb
    · left; rw [wn, hnull]
    · right; exact ⟨h.nextBlk, wb, Nat.le_refl _⟩
  exact k3.trans (hK w u _ a after hr3)

theorem keep_updatewindow (p : ZStreamPtr) (end_ : BPtr) (copy : UInt32) :
    KeepM (updatewindow p end_ copy) := by
  unfold updatewindow
  apply KeepM.bind (keep_ldZStream _); intro z
  apply KeepM.bind (keep_castInflateState _); intro state
  apply KeepM.bind_dep (keep_ldInflateState _)
  intro h s h' hl
  obtain ⟨rfl, i, hst, hs⟩ := ldInflateState_ok' hl
  apply KeepMAt.ite_dep
  · intro hnull
    have wnull : s.window = .null := by simpa using hnull
    subst hst
    apply KeepMAt.bind_dep (KeepMAt.of (keep_shl32 _ _) _)
    intro n h2 e2
    have := shl32_same e2
    subst this
    apply keepAt_alloc_window _ _ _ _ ?_ hs wnull
    intro w u
    keep_m
  · intro _
    apply KeepMAt.of
    keep_m

theorem keep_x_inflate_run (c : Ctx) : KeepX c.st (inflate_run c) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact keep_x_inflate_dispatch _
    | keep_x_step

/-! ## The result of `updatewindow` -/

/-- An allocation call made between the two heaps was refused. -/
def Failed (h h' : Heap) : Prop := ∃ j, h.nalloc ≤ j ∧ j < h'.nalloc ∧ h.allocOk j = false

/-- Every successful run returns 0. -/
def RetZero (m : M Int32) : Prop := ∀ h v after, m h = .ok (v, after) → v = 0

theorem RetZero.pure0 : RetZero (pure 0) := by
  intro h v after hr; cases hr; rfl

theorem RetZero.bind {α : Type} {m : M α} {f : α → M Int32} (hf : ∀ a, RetZero (f a)) :
    RetZero (m >>= f) := by
  intro h v after hr
  obtain ⟨a, h1, _, hr1⟩ := bind_ok hr
  exact hf a h1 v after hr1

theorem RetZero.ite (p : Prop) [Decidable p] {a b : M Int32} (ha : RetZero a) (hb : RetZero b) :
    RetZero (if p then a else b) := by
  split <;> assumption

/-- A nonzero result comes with a refused allocation. -/
def RetFail (m : M Int32) (h : Heap) : Prop := ∀ v after, m h = .ok (v, after) → v ≠ 0 → Failed h after

theorem RetFail.of_zero {m : M Int32} (hm : RetZero m) (h : Heap) : RetFail m h :=
  fun v after hr nz => absurd (hm h v after hr) nz

theorem RetFail.ite_dep (p : Prop) [Decidable p] {a b : M Int32} {h : Heap}
    (ha : p → RetFail a h) (hb : ¬ p → RetFail b h) : RetFail (if p then a else b) h := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem castInflateState_same {p : Option StateRef} {h h' : Heap} {q : InflateStatePtr}
    (hr : castInflateState p h = .ok (q, h')) : h' = h := by
  unfold castInflateState at hr
  repeat' first | split at hr | contradiction | (cases hr; rfl)

theorem retFail_alloc_window (strm : ZStreamPtr) (i : Nat) (n : UInt32)
    (K : BPtr → Unit → M Int32) (hKk : ∀ w u, KeepM (K w u))
    (hK : ∀ w u, w ≠ .null → RetZero (K w u)) (h : Heap) :
    RetFail (ZALLOCB strm n 1 >>= fun w =>
      wrS (some (.tab i)) (fun s => { s with window := w }) >>= K w) h := by
  intro v after hr nz
  obtain ⟨w, h2, e2, hr2⟩ := bind_ok hr
  obtain ⟨_, _, wcase⟩ := zallocb_info e2
  obtain ⟨u, h3, e3, hr3⟩ := bind_ok hr2
  by_cases wn : w = .null
  · rcases wcase with ⟨_, na, bad⟩ | wb
    · have n3 : h3.nalloc = h2.nalloc := by
        cases hs : h2.istates i with
        | none =>
          unfold wrS at e3
          have e : ldInflateState (some (.tab i)) h2 =
              .error (.ub "access through a dangling pointer (inflate_state)") := by
            simp [ldInflateState, InflateStateRef.get, hs]
          rw [bind_app, e] at e3
          cases e3
        | some s => rw [wrS_eq hs e3]
      have k := hKk w u h3 v after hr3
      exact ⟨h.nalloc, Nat.le_refl _, by have := k.nalloc; omega, bad⟩
    · rw [wb] at wn; cases wn
  · exact absurd (hK w u wn h3 v after hr3) nz

theorem RetFail.bind_same {α : Type} {m : M α} {f : α → M Int32} {h : Heap}
    (same : ∀ a h', m h = .ok (a, h') → h' = h) (hf : ∀ a, m h = .ok (a, h) → RetFail (f a) h) :
    RetFail (m >>= f) h := by
  intro v after hr nz
  obtain ⟨a, h1, e1, hr1⟩ := bind_ok hr
  have := same a h1 e1
  subst this
  exact hf a e1 v after hr1 nz

theorem updatewindow_ret (p : ZStreamPtr) (end_ : BPtr) (copy : UInt32) (h : Heap) :
    RetFail (updatewindow p end_ copy) h := by
  unfold updatewindow
  apply RetFail.bind_same (fun _ _ e => ldZStream_same e)
  intro z _
  apply RetFail.bind_same (fun _ _ e => castInflateState_same e)
  intro state _
  apply RetFail.bind_same (fun _ _ e => (ldInflateState_ok' e).1)
  intro s e3
  obtain ⟨_, i, hst, hs⟩ := ldInflateState_ok' e3
  apply RetFail.ite_dep
  · intro _
    subst hst
    apply RetFail.bind_same (fun _ _ e => shl32_same e)
    intro n _
    apply retFail_alloc_window
    · intro w u
      keep_m
    · intro w u wn
      have bw : (w == Ptr.null) = false := by simpa using wn
      simp only [bw, Bool.false_eq_true, ite_false]
      repeat' first
        | exact RetZero.pure0
        | apply RetZero.bind
        | apply RetZero.ite
        | intro x
        | dsimp only
  · intro _
    apply RetFail.of_zero
    repeat' first
      | exact RetZero.pure0
      | apply RetZero.bind
      | apply RetZero.ite
      | intro x
      | dsimp only

/-! ## One public call -/

/-- The control fields of one decoder record over a whole call returning `rc`:
as `Ctl`, except that the record may newly be in `MEM` when the call returns
`Z_MEM_ERROR` after a refused allocation. -/
structure CtlCall (h h' : Heap) (rc : Int32) (s s' : InflateState) : Prop where
  head : s'.head = s.head
  sync : s.mode ≠ SYNC → s'.mode ≠ SYNC
  mem : s'.mode = MEM → s.mode = MEM ∨ (rc = Z_MEM_ERROR ∧ Failed h h')
  win : s.window ≠ .null → s'.window = s.window
  fresh : s'.window = s.window ∨ ∃ w, s'.window = .ref (.blk w) 0 ∧ h.nextBlk ≤ w
  dict : s'.havedict = s.havedict

structure KeepsCall (h h' : Heap) (rc : Int32) : Prop where
  static : h'.static = h.static
  allocOk : h'.allocOk = h.allocOk
  nalloc : h.nalloc ≤ h'.nalloc
  next : h.nextBlk ≤ h'.nextBlk
  sizes : ∀ ref, NotStr ref → SizeKept h h' ref
  states : ∀ j s', h'.istates j = some s' → ∃ s, h.istates j = some s ∧ CtlCall h h' rc s s'
  /-- every gz record keeps every field but its embedded stream -/
  gz : Zlib.Deflate.Universal.Params.GzRecordsKept h h'
  /-- every stream keeps existing; its message is the old one, `NULL` or a literal -/
  msgs : StreamMsgs h h'

theorem Keeps.call {h h' : Heap} (k : Keeps h h') (rc : Int32) : KeepsCall h h' rc := by
  refine ⟨k.static, k.allocOk, k.nalloc, k.next, k.sizes, ?_, k.gz, k.msgs⟩
  intro j s' g
  obtain ⟨s, g0, c⟩ := k.states j s' g
  exact ⟨s, g0, c.head, c.sync, fun m => Or.inl (c.mem m), c.win, c.fresh, c.dict⟩

theorem Failed.widen {h h1 h2 h3 : Heap} (a : Keeps h h1) (f : Failed h1 h2) (b : Keeps h2 h3) :
    Failed h h3 := by
  obtain ⟨j, lo, hi, bad⟩ := f
  refine ⟨j, Nat.le_trans a.nalloc lo, Nat.lt_of_lt_of_le hi b.nalloc, ?_⟩
  rw [← a.allocOk]; exact bad

theorem KeepsCall.left {h h1 h2 : Heap} {rc : Int32} (a : Keeps h h1) (b : KeepsCall h1 h2 rc) :
    KeepsCall h h2 rc := by
  refine ⟨b.static.trans a.static, b.allocOk.trans a.allocOk, Nat.le_trans a.nalloc b.nalloc,
    Nat.le_trans a.next b.next, ?_, ?_, a.gz.trans b.gz, a.msgs.trans b.msgs⟩
  · intro ref n a2 g2
    rcases b.sizes ref n a2 g2 with ⟨a1, g1, e1⟩ | sm
    · rcases a.sizes ref n a1 g1 with ⟨a0, g0, e0⟩ | sm
      · exact Or.inl ⟨a0, g0, e1.trans e0⟩
      · exact Or.inr (e1 ▸ sm)
    · exact Or.inr sm
  · intro j s2 g2
    obtain ⟨s1, g1, c1⟩ := b.states j s2 g2
    obtain ⟨s0, g0, c0⟩ := a.states j s1 g1
    refine ⟨s0, g0, c1.head.trans c0.head, fun n => c1.sync (c0.sync n), ?_, ?_, ?_, c1.dict.trans c0.dict⟩
    · intro m
      rcases c1.mem m with m1 | ⟨r, f⟩
      · exact Or.inl (c0.mem m1)
      · exact Or.inr ⟨r, Failed.widen a f (Keeps.refl _)⟩
    · intro n
      have e1 := c0.win n
      rw [c1.win (by rw [e1]; exact n), e1]
    · rcases c1.fresh with e | ⟨w, e, lw⟩
      · rw [e]; exact c0.fresh
      · exact Or.inr ⟨w, e, Nat.le_trans a.next lw⟩

theorem KeepsCall.right {h h1 h2 : Heap} {rc : Int32} (a : KeepsCall h h1 rc) (b : Keeps h1 h2) :
    KeepsCall h h2 rc := by
  refine ⟨b.static.trans a.static, b.allocOk.trans a.allocOk, Nat.le_trans a.nalloc b.nalloc,
    Nat.le_trans a.next b.next, ?_, ?_, a.gz.trans b.gz, a.msgs.trans b.msgs⟩
  · intro ref n a2 g2
    rcases b.sizes ref n a2 g2 with ⟨a1, g1, e1⟩ | sm
    · rcases a.sizes ref n a1 g1 with ⟨a0, g0, e0⟩ | sm
      · exact Or.inl ⟨a0, g0, e1.trans e0⟩
      · exact Or.inr (e1 ▸ sm)
    · exact Or.inr sm
  · intro j s2 g2
    obtain ⟨s1, g1, c1⟩ := b.states j s2 g2
    obtain ⟨s0, g0, c0⟩ := a.states j s1 g1
    refine ⟨s0, g0, c1.head.trans c0.head, fun n => c1.sync (c0.sync n), ?_, ?_, ?_, c1.dict.trans c0.dict⟩
    · intro m
      rcases c0.mem (c1.mem m) with m0 | ⟨r, f⟩
      · exact Or.inl m0
      · exact Or.inr ⟨r, Failed.widen (Keeps.refl _) f b⟩
    · intro n
      have e1 := c0.win n
      rw [c1.win (by rw [e1]; exact n), e1]
    · rcases c1.fresh with e | ⟨w, e, lw⟩
      · rw [e]; exact c0.fresh
      · exact Or.inr ⟨w, e, Nat.le_trans a.next lw⟩

/-- Every successful run returning `rc` keeps `KeepsCall` for `rc`. -/
def CallM (m : M Int32) : Prop := ∀ h rc after, m h = .ok (rc, after) → KeepsCall h after rc

theorem CallM.of_keep {m : M Int32} (hm : KeepM m) : CallM m :=
  fun h rc after hr => (hm h rc after hr).call rc

theorem CallM.pure (v : Int32) : CallM (pure v) := CallM.of_keep (KeepM.pure v)

theorem CallM.bind {α : Type} {m : M α} {f : α → M Int32} (hm : KeepM m) (hf : ∀ a, CallM (f a)) :
    CallM (m >>= f) := by
  intro h rc after hr
  obtain ⟨a, h1, e1, hr1⟩ := bind_ok hr
  exact KeepsCall.left (hm h a h1 e1) (hf a h1 rc after hr1)

/-- A computation whose result is passed through a heap-keeping epilogue. -/
theorem CallM.bind_ret {m : M Int32} {k : M Unit} (hm : CallM m) (hk : KeepM k) :
    CallM (m >>= fun r => k >>= fun _ => Pure.pure r) := by
  intro h rc after hr
  obtain ⟨r, h1, e1, hr1⟩ := bind_ok hr
  obtain ⟨u, h2, e2, hr2⟩ := bind_ok hr1
  cases hr2
  exact KeepsCall.right (hm h _ h1 e1) (hk h1 u _ e2)

theorem CallM.ite (p : Prop) [Decidable p] {a b : M Int32} (ha : CallM a) (hb : CallM b) :
    CallM (if p then a else b) := by
  split <;> assumption

/-- The window refusal exit of `inf_leave`. -/
theorem CallM.window_exit (strm : ZStreamPtr) (e : BPtr) (copy : UInt32) (st : InflateStatePtr)
    (J : M Int32) (hJ : CallM J) :
    CallM (updatewindow strm e copy >>= fun v =>
      if (v != 0) = true then (setMode st MEM >>= fun _ => Pure.pure Z_MEM_ERROR) else J) := by
  intro h rc after hr
  obtain ⟨v, h2, e2, hr2⟩ := bind_ok hr
  have k2 := keep_updatewindow strm e copy h v h2 e2
  by_cases nz : v = 0
  · have b : (v != 0) = false := by simp [nz]
    rw [b] at hr2
    exact KeepsCall.left k2 (hJ h2 rc after hr2)
  · have b : (v != 0) = true := by simp [nz]
    rw [b] at hr2
    have fail := updatewindow_ret strm e copy h v h2 e2 nz
    obtain ⟨u, h3, e3, hr3⟩ := bind_ok hr2
    cases hr3
    unfold setMode at e3
    cases st with
    | none => simp [wrS, ldInflateState] at e3
    | some r =>
      cases r with
      | tab i =>
        cases hs : h2.istates i with
        | none =>
          unfold wrS at e3
          have e : ldInflateState (some (.tab i)) h2 =
              .error (.ub "access through a dangling pointer (inflate_state)") := by
            simp [ldInflateState, InflateStateRef.get, hs]
          rw [bind_app, e] at e3
          cases e3
        | some s2 =>
          have h3eq := wrS_eq hs e3
          subst h3eq
          refine ⟨k2.static, k2.allocOk, k2.nalloc, k2.next, ?_, ?_, k2.gz.trans (Zlib.Deflate.Universal.Params.GzRecordsKept.of_eq rfl),
            k2.msgs.trans (StreamMsgs.of_eq rfl rfl)⟩
          · intro ref n x gx
            apply k2.sizes ref n x
            rw [← gx]
            cases ref <;> rfl
          · intro j s' g'
            simp only [] at g'
            rw [upd_apply] at g'
            by_cases ej : j = i
            · subst ej
              rw [if_pos rfl] at g'
              cases g'
              obtain ⟨s0, g0, c0⟩ := k2.states j s2 hs
              refine ⟨s0, g0, c0.head, fun _ => (by decide : MEM ≠ SYNC), fun _ => Or.inr ⟨rfl, fail⟩, c0.win, c0.fresh, c0.dict⟩
            · rw [if_neg ej] at g'
              obtain ⟨s0, g0, c0⟩ := k2.states j s' g'
              exact ⟨s0, g0, c0.head, c0.sync, fun m => Or.inl (c0.mem m), c0.win, c0.fresh, c0.dict⟩

theorem call_inflate_leave (c : Ctx) (l : IL) : CallM (inflate_leave c l) := by
  unfold inflate_leave
  repeat' first
    | with_reducible exact CallM.pure _
    | with_reducible apply CallM.window_exit
    | with_reducible apply CallM.ite
    | with_reducible apply CallM.bind
    | keep_m_step

theorem keep_inflateStateCheck (p : ZStreamPtr) : KeepM (inflateStateCheck p) := by
  unfold inflateStateCheck
  keep_m

theorem keep_run_inflate (c : Ctx) (l : IL) : KeepM (StateT.run (ExceptT.run (inflate_run c)) l) :=
  fun h r after hr => (keep_x_inflate_run c h l r after hr).1

/-- The complete public call. -/
theorem call_inflate (p : ZStreamPtr) (flush : Int32) : CallM (inflate p flush) := by
  unfold inflate
  repeat' first
    | with_reducible exact CallM.pure _
    | with_reducible exact call_inflate_leave _ _
    | with_reducible exact keep_allocLocalB _ (by decide)
    | with_reducible exact keep_inflateStateCheck _
    | with_reducible exact keep_run_inflate _ _
    | with_reducible exact keep_freeB _
    | with_reducible apply CallM.bind_ret
    | with_reducible apply CallM.ite
    | with_reducible apply CallM.bind
    | (show CallM _; split)
    | keep_m_step

#print axioms keep_updatewindow
#print axioms updatewindow_ret
#print axioms keep_x_inflate_run
end Zlib.Inflate.KeepProofs
