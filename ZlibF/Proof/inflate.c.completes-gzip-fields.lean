import ZlibF.Proof.«inflate.c.completes-room-modes»
import ZlibF.Proof.«inflate.c.completes-observe-mode»

/-!
# inflate.c: the gzip field modes leave only with no input (`GzipFieldLeaves`)

`NAME` and `COMMENT` copy a zero-terminated field with
`do { len = next[copy++]; ... } while (len && copy < have)`, then
`have -= copy; if (len) goto inf_leave;`. Before every pass `copy < have`, so the
loop ends with `len == 0` or `copy == have` (`str_loop_exit`), and a leave after
`have -= copy` is taken with no input left. `EXTRA` copies
`copy = min(length, have)` bytes and leaves if `length - copy != 0`, which needs
`copy == have`: the field length is read from the decoder record, and the steps in
between keep it (`ModeLen` observer).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public Zlib.Inflate.KeepProofs
set_option autoImplicit false

/-! ## A loop invariant that knows the test -/

theorem cwhile_test_inv {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (P Pb Pf : σ → Prop)
    (hc : ∀ s h s' h' t, P s → cond s h = .ok ((t, s'), h') → (t = true → Pb s') ∧ (t = false → Pf s'))
    (hb : ∀ s h s' h', Pb s → body s h = .ok (s', h') → P s') :
    ∀ n s h res h', P s → cwhile.go cond body n s h = .ok (res, h') → Pf res := by
  intro n
  induction n with
  | zero => intro s h res h' _ run; cases run
  | succ n ih =>
    intro s h res h' current run
    simp only [cwhile.go, bind_app] at run
    cases condition : cond s h with
    | error fault => rw [condition] at run; cases run
    | ok pair =>
      obtain ⟨⟨test, next⟩, heap1⟩ := pair
      rw [condition] at run
      have step := hc s h next heap1 test current condition
      cases test with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
        cases run
        exact step.2 rfl
      | true =>
        simp only [ite_true, bind_app] at run
        cases executed : body next heap1 with
        | error fault => rw [executed] at run; cases run
        | ok pair =>
          obtain ⟨next2, heap2⟩ := pair
          rw [executed] at run
          exact ih next2 heap2 res h' (hb next heap1 next2 heap2 (step.1 rfl) executed) run

theorem uint32_succ_toNat' {a b : UInt32} (lt : a.toNat < b.toNat) : (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add]
  have := b.toNat_lt
  simp only [UInt32.toNat_one, UInt32.size] at *
  omega

/-- The condition of the string loops. -/
def strTest : X Bool := do let l ← get; return l.len != 0 && l.copy < l.have_

/-- A string loop whose body advances `copy` by one and keeps `have` ends with
`len == 0` or `copy == have`. -/
theorem str_loop_exit {body : X Unit}
    (hb : ∀ l h l' h', l.copy.toNat < l.have_.toNat → runX body l h = .ok ((.ok (), l'), h') →
      l'.copy.toNat ≤ l'.have_.toNat)
    {l l' : IL} {h h' : Heap} (start : l.copy.toNat < l.have_.toNat)
    (run : runX (xdoWhile body strTest) l h = .ok ((.ok (), l'), h')) :
    l'.len = 0 ∨ l'.copy = l'.have_ := by
  unfold xdoWhile at run
  rw [runX_bind] at run
  split at run
  · rename_i u l1 h1 first
    have j1 := hb l h l1 h1 start first
    unfold xwhile xwhileBrk runX at run
    simp only [ExceptT.run, ExceptT.mk, StateT.run, bind_app] at run
    generalize hcw : cwhile _ _ (l1, Stop.go) h1 = cw at run
    cases cw with
    | error fault => cases run
    | ok pair =>
      obtain ⟨⟨regs, stop⟩, heap⟩ := pair
      have fin := cwhile_test_inv (body := _)
        (fun st : IL × Stop => st.2 ≠ Stop.brk ∧ (st.2 = Stop.go → st.1.copy.toNat ≤ st.1.have_.toNat))
        (fun st : IL × Stop => st.2 = Stop.go ∧ st.1.copy.toNat < st.1.have_.toNat)
        (fun st : IL × Stop => st.2 ≠ Stop.brk ∧ (st.2 = Stop.go → st.1.len = 0 ∨ st.1.copy = st.1.have_))
        ?_ ?_ _ _ _ _ _ ⟨by simp, fun _ => j1⟩ hcw
      · cases stop with
        | go =>
          simp only [pure_app] at run
          cases run
          exact fin.2 rfl
        | brk => exact absurd rfl fin.1
        | ex x => simp only [pure_app] at run; cases run
      · intro ⟨cur, st⟩ h0 s' h1 t current e
        cases st with
        | go =>
          simp only [bind_app] at e
          rw [show strTest cur h0 = (Except.ok ((Except.ok (cur.len != 0 && cur.copy < cur.have_), cur), h0) :
            Except Fault ((Except Ex Bool × IL) × Heap)) from rfl] at e
          simp only [pure_app] at e
          cases e
          constructor
          · intro tt
            simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at tt
            exact ⟨rfl, by have := tt.2; rw [UInt32.lt_iff_toNat_lt] at this; exact this⟩
          · intro ff
            refine ⟨by simp, fun _ => ?_⟩
            simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not] at ff
            rcases ff with z | nlt
            · exact Or.inl z
            · right
              have le : cur.copy.toNat ≤ cur.have_.toNat := current.2 rfl
              rw [UInt32.lt_iff_toNat_lt] at nlt
              show cur.copy = cur.have_
              exact UInt32.toNat_inj.mp (by omega)
        | brk => exact absurd rfl current.1
        | ex x =>
          simp only [pure_app] at e
          cases e
          exact ⟨fun t => (by cases t), fun _ => ⟨by simp, fun g => (by cases g)⟩⟩
      · intro ⟨cur, st⟩ h0 s' h1 pb e
        obtain ⟨isGo, lt⟩ := pb
        simp only at isGo lt
        subst isGo
        simp only [bind_app] at e
        generalize hb2 : (body >>= fun __r => (pure false : X Bool)) cur h0 = R at e
        have hR : runX (body >>= fun __r => (pure false : X Bool)) cur h0 = R := hb2
        rw [runX_bind] at hR
        cases b : runX body cur h0 with
        | error fault => rw [b] at hR; subst hR; simp at e
        | ok triple =>
          obtain ⟨⟨res, l2⟩, h2⟩ := triple
          rw [b] at hR
          cases res with
          | ok u =>
            dsimp only at hR
            rw [runX_pure] at hR
            subst hR
            simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, _⟩ := e
            exact ⟨by simp, fun _ => hb cur h0 l2 h2 lt b⟩
          | error x =>
            subst hR
            simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, _⟩ := e
            exact ⟨by simp, fun g => by cases g⟩
  · cases run
  · cases run

/-! ## Register effects -/

/-- Every run of `p` from the registers `l` that ends normally ends with registers in `Q`. -/
def RegsP {α : Type} (Q : IL → Prop) (l : IL) (p : X α) : Prop :=
  ∀ h v l' h', runX p l h = .ok ((.ok v, l'), h') → Q l'

theorem regsP_pure {α : Type} {Q : IL → Prop} {l : IL} (v : α) (hq : Q l) : RegsP Q l (pure v : X α) := by
  intro h v' l' h' run; cases run; exact hq

theorem regsP_lift {α : Type} {Q : IL → Prop} {l : IL} (m : M α) (hq : Q l) :
    RegsP Q l (monadLift m : X α) := by
  intro h v l' h' run
  rw [runX_lift] at run
  cases s : m h with
  | error x => simp only [s] at run; cases run
  | ok pair => simp only [s] at run; cases run; exact hq

theorem regsP_bind {α β : Type} {Q : IL → Prop} {l : IL} {p : X α} {k : α → X β}
    (hk : ∀ h a l1 h1, runX p l h = .ok ((.ok a, l1), h1) → RegsP Q l1 (k a)) :
    RegsP Q l (p >>= k) := by
  intro h v l' h' run
  rw [runX_bind] at run
  split at run
  · rename_i a l1 h1 first
    exact hk h a l1 h1 first h1 v l' h' run
  · cases run
  · cases run

theorem regsP_get_bind {β : Type} {Q : IL → Prop} {l : IL} {k : IL → X β} (hk : RegsP Q l (k l)) :
    RegsP Q l (get >>= k) :=
  regsP_bind (fun _ _ _ _ run => by rw [runX_get] at run; cases run; exact hk)

theorem regsP_set_bind {β : Type} {Q : IL → Prop} {l t : IL} {k : PUnit → X β} (hk : RegsP Q t (k ())) :
    RegsP Q l (set t >>= k) :=
  regsP_bind (fun _ _ _ _ run => by rw [runX_set] at run; cases run; exact hk)

theorem regsP_lift_bind {α β : Type} {Q : IL → Prop} {l : IL} {m : M α} {k : α → X β}
    (hk : ∀ a, RegsP Q l (k a)) : RegsP Q l ((monadLift m : X α) >>= k) :=
  regsP_bind (fun h a l1 h1 run => by
    rw [runX_lift] at run
    cases s : m h with
    | error x => simp only [s] at run; cases run
    | ok pair => simp only [s] at run; cases run; exact hk _)

theorem regsP_ite {α : Type} {Q : IL → Prop} {l : IL} {test : Prop} [Decidable test] {yes no : X α}
    (hy : test → RegsP Q l yes) (hn : ¬ test → RegsP Q l no) : RegsP Q l (if test then yes else no) := by
  split
  · exact hy ‹_›
  · exact hn ‹_›

macro "regs_step" : tactic =>
  `(tactic| first
    | with_reducible refine regsP_get_bind ?_
    | with_reducible refine regsP_set_bind ?_
    | with_reducible refine regsP_lift_bind (fun _ => ?_)
    | with_reducible refine regsP_ite (fun _ => ?_) (fun _ => ?_)
    | with_reducible refine regsP_pure _ ?_
    | with_reducible refine regsP_lift _ ?_
    | split)

/-- The body of a string loop advances `copy` by one and keeps `have`. -/
theorem copy_step {l : IL} {b : UInt8} (lt : l.copy.toNat < l.have_.toNat) :
    ({ l with len := b.toUInt32, copy := l.copy + 1 } : IL).copy.toNat ≤
      ({ l with len := b.toUInt32, copy := l.copy + 1 } : IL).have_.toNat := by
  show (l.copy + 1).toNat ≤ l.have_.toNat
  rw [uint32_succ_toNat' lt]
  omega

/-! ## The leave at the end of a field -/

/-- `have -= copy; if (len) goto inf_leave;` after a loop that ended with
`len == 0 || copy == have`. -/
theorem roomCause_strEnd {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {m : IL} {nx : BPtr}
    (done : m.len = 0 ∨ m.copy = m.have_) (test : (m.len != 0) = true) :
    ∀ h, pre h → RoomCause flush q { m with have_ := m.have_ - m.copy, next := nx } h := by
  intro _ _
  left
  rcases done with z | e
  · simp only [bne_iff_ne, ne_eq] at test; exact absurd z test
  · show m.have_ - m.copy = 0
    rw [e]; simp

/-- A string loop: its exits are the body's, and it ends with `len == 0 || copy == have`. -/
theorem roomP_strloop {β : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    {body : X Unit} {next : Unit → X β}
    (room : RoomX flush q body)
    (hb : ∀ l h l' h', l.copy.toNat < l.have_.toNat → runX body l h = .ok ((.ok (), l'), h') →
      l'.copy.toNat ≤ l'.have_.toNat)
    (start : l.copy.toNat < l.have_.toNat)
    (hn : ∀ v m, (m.len = 0 ∨ m.copy = m.have_) → RoomP flush q (fun _ => True) m (next v)) :
    RoomP flush q pre l (xdoWhile body strTest >>= next) := by
  apply roomP_bind (roomP_weaken (roomX_xdoWhile room (by
    intro l0
    unfold strTest
    room_source) l))
  intro h v middle heap _ run result regs after run2 e leave
  cases v
  exact hn () middle (str_loop_exit hb start run) heap result regs after trivial run2 e leave

/-! ## The modes -/

theorem copy_start {l : IL} (nonempty : ¬ (l.have_ == 0) = true) :
    ({ l with copy := 0 } : IL).copy.toNat < ({ l with copy := 0 } : IL).have_.toNat := by
  show (0 : UInt32).toNat < l.have_.toNat
  simp only [beq_iff_eq] at nonempty
  have : l.have_.toNat ≠ 0 := fun e => nonempty (UInt32.toNat_inj.mp (by simpa using e))
  simp only [UInt32.toNat_zero]
  omega

macro "strloop_side" : tactic =>
  `(tactic| first
    | (intro l0 h0 l1 h1 lt run
       refine (?_ : RegsP (fun l' => l'.copy.toNat ≤ l'.have_.toNat) l0 _) h0 () l1 h1 run
       repeat' first | exact copy_step lt | regs_step)
    | exact copy_start ‹_›)

theorem roomX_inflate_COMMENT (c : Ctx) : RoomX c.flush c.st (inflate_COMMENT c) := by
  intro l
  unfold inflate_COMMENT
  repeat' first
    | with_reducible exact roomX_inflate_HCRC _ _
    | exact room_imp (roomCause_strEnd ‹_› ‹_›)
    | refine roomP_strloop ?_ ?_ ?_ (fun _ m _ => ?_)
    | strloop_side
    | room_step

theorem roomX_inflate_NAME (c : Ctx) : RoomX c.flush c.st (inflate_NAME c) := by
  intro l
  unfold inflate_NAME
  repeat' first
    | with_reducible exact roomX_inflate_COMMENT _ _
    | exact room_imp (roomCause_strEnd ‹_› ‹_›)
    | refine roomP_strloop ?_ ?_ ?_ (fun _ m _ => ?_)
    | strloop_side
    | room_step

#print axioms roomX_inflate_NAME

/-! ## EXTRA: the field length through the copy -/

/-- The decoder record has field length `n`. -/
def LenIs (q : InflateStatePtr) (n : UInt32) (h : Heap) : Prop :=
  ∃ i s, q = some (.tab i) ∧ h.istates i = some s ∧ s.length = n

theorem lenIs_frame {q : InflateStatePtr} {n : UInt32} {h h' : Heap} {r : ZStreamRef} {o : InflateStatePtr}
    (frame : ModeLen.WindowFrame r o h h') (len : LenIs q n h) : LenIs q n h' := by
  obtain ⟨i, s, st, get, eq⟩ := len
  unfold ModeLen.WindowFrame ModeLen.decoderWindows at frame
  have at_i := congrFun frame i
  rw [get] at at_i
  cases g : h'.istates i with
  | none => rw [g] at at_i; cases at_i
  | some s' =>
    rw [g] at at_i
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at at_i
    exact ⟨i, s', st, g, at_i.2.trans eq⟩

theorem roomP_ld_len {β : Type} {flush : Int32} {q p : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    {next : InflateState → X β} (hn : ∀ s, RoomP flush q (LenIs p s.length) l (next s)) :
    RoomP flush q pre l ((monadLift (ldInflateState p) : X InflateState) >>= next) := by
  refine roomP_ld_bind (fun s => ?_)
  intro h result regs after hp run e leave
  obtain ⟨_, load⟩ := hp
  obtain ⟨_, i, st, get⟩ := ldInflateState_ok' load
  exact hn s h result regs after ⟨i, s, st, get, rfl⟩ run e leave

theorem roomP_lift_frame {α β : Type} {flush : Int32} {q p : InflateStatePtr} {n : UInt32} {l : IL}
    {m : M α} {next : α → X β} (hm : ModeLen.WindowFrameM (.tab 0) none m)
    (hn : ∀ v, RoomP flush q (LenIs p n) l (next v)) :
    RoomP flush q (LenIs p n) l ((monadLift m : X α) >>= next) := by
  apply roomP_bind (roomP_lift m)
  intro h v middle heap hp run
  rw [runX_lift] at run
  cases s : m h with
  | error x => simp only [s] at run; cases run
  | ok pair =>
    obtain ⟨v1, h1⟩ := pair
    simp only [s] at run
    cases run
    exact fun result regs after run e leave =>
      hn v _ result regs after (lenIs_frame (hm h v _ s) hp) run e leave

theorem roomP_rdS_len {β : Type} {flush : Int32} {q p : InflateStatePtr} {n : UInt32} {l : IL}
    {next : UInt32 → X β} (hn : ∀ v, v = n → RoomP flush q (LenIs p n) l (next v)) :
    RoomP flush q (LenIs p n) l ((monadLift (rdS p (·.length)) : X UInt32) >>= next) := by
  apply roomP_bind (roomP_lift _)
  intro h v middle heap hp run
  rw [runX_lift] at run
  cases s : rdS p (·.length) h with
  | error x => simp only [s] at run; cases run
  | ok pair =>
    obtain ⟨v1, h1⟩ := pair
    simp only [s] at run
    cases run
    obtain ⟨rfl, i, st0, pst, get, rfl⟩ := rdS_ok s
    obtain ⟨i', s', pst', get', len⟩ := hp
    rw [pst] at pst'
    cases pst'
    rw [get] at get'
    cases get'
    exact fun result regs after run e leave =>
      hn _ len _ result regs after ⟨i, st0, pst, get, len⟩ run e leave

theorem roomP_wrS_len {β : Type} {flush : Int32} {q p : InflateStatePtr} {n C : UInt32} {l : IL}
    {next : Unit → X β} (hn : RoomP flush q (LenIs p (n - C)) l (next ())) :
    RoomP flush q (LenIs p n) l
      ((monadLift (wrS p fun s => { s with length := s.length - C }) : X Unit) >>= next) := by
  apply roomP_bind (roomP_lift _)
  intro h v middle heap hp run
  rw [runX_lift] at run
  cases s : wrS p (fun s => { s with length := s.length - C }) h with
  | error x => simp only [s] at run; cases run
  | ok pair =>
    obtain ⟨v1, h1⟩ := pair
    simp only [s] at run
    cases run
    obtain ⟨i, st0, pst, get, len⟩ := hp
    subst pst
    have eq := wrS_eq get s
    subst eq
    exact fun result regs after run e leave =>
      hn _ result regs after ⟨i, { st0 with length := st0.length - C }, rfl, by simp [upd_apply], by simp [len]⟩
        run e leave

/-- After `have -= copy`: the field goes on only if the input ran out. -/
theorem roomCause_extra {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {R : IL}
    {len H v : UInt32} (hv : v = len - (if len > H then H else len)) (test : (v != 0) = true)
    (have_ : R.have_ = H - (if len > H then H else len)) : ∀ h, pre h → RoomCause flush q R h := by
  intro _ _
  left
  rw [have_]
  subst hv
  by_cases big : len > H
  · simp [big]
  · simp only [big, ite_false, UInt32.sub_self, bne_self_eq_false, Bool.false_eq_true] at test

/-- Nothing copied: the field goes on only if the input ran out. -/
theorem roomCause_extra0 {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {R : IL}
    {len H v : UInt32} (hv : v = len) (test : (v != 0) = true)
    (none_ : ¬ ((if len > H then H else len) != 0) = true)
    (have_ : R.have_ = H) : ∀ h, pre h → RoomCause flush q R h := by
  intro _ _
  left
  rw [have_]
  subst hv
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at none_ test
  by_cases big : v > H
  · simpa [big] using none_
  · simp only [big, ite_false] at none_
    exact absurd none_ test

macro "modelen_frame" : tactic =>
  `(tactic| first
    | exact ModeLen.windowFrameM_ldHeader _ _ _
    | exact ModeLen.windowFrameM_memcpyB _ _ _ _ _
    | exact ModeLen.windowFrameM_ptr_add _ _ _ _
    | exact ModeLen.windowFrameM_hcrcOn _ _ _
    | exact ModeLen.windowFrameM_crc32 _ _ _ _ _
    | exact ModeLen.windowFrameM_rdS _ _ _ _
    | exact ModeLen.windowFrameM_wrS_gen _ _ _ _ (fun _ => rfl))

set_option maxHeartbeats 2000000 in
theorem roomX_inflate_EXTRA (c : Ctx) : RoomX c.flush c.st (inflate_EXTRA c) := by
  intro l
  unfold inflate_EXTRA
  repeat' first
    | with_reducible exact roomX_inflate_NAME _ _
    | (show ∀ _, _ → ExitCause _ _ Ex.leave _ _
       first
         | exact room_imp (roomCause_extra ‹_› ‹_› rfl)
         | exact room_imp (roomCause_extra0 ‹_› ‹_› ‹_› rfl))
    | refine roomP_ld_len (fun _ => ?_)
    | refine roomP_rdS_len (fun _ _ => ?_)
    | exact roomP_weaken (roomP_lift_bind (fun _ => roomX_inflate_NAME c _))
    | refine roomP_lift_frame (by modelen_frame) (fun _ => ?_)
    | refine roomP_wrS_len ?_
    | room_step

/-- `GzipFieldLeaves`. -/
theorem gzip_field_leaves : GzipFieldLeaves :=
  fun c => ⟨roomX_inflate_EXTRA c, roomX_inflate_NAME c, roomX_inflate_COMMENT c⟩

#print axioms gzip_field_leaves

end Zlib.Inflate.Proofs
