import ZlibF.Proof.«inflate.c.leave-cause-frame»
import ZlibF.Proof.«inflate.c.main.common»
import ZlibF.Proof.«inflate.c.completes-keep-run»

/-!
# inflate.c: a leave for want of output room holds output (frame)

`goto inf_leave` is taken for no input (`have == 0`), a `Z_BLOCK`/`Z_TREES` stop,
a return code already in `ret`, or no output room (`left == 0`). The last
happens at exactly three places: `case LIT` and `case MATCH` before they write,
and `case COPY` when a stored block still has bytes. `RoomCause` records that in
the last case the decoder record is in `LIT`, `MATCH`, or `COPY` with bytes left
(`Holding`), at the heap of the leave.

`RoomP flush q pre l p`: a run of `p` from the registers `l` and any heap with
`pre` that leaves through `inf_leave` ends with a `RoomCause`. It is the
register-exact walk of `inflate.c.leave-cause-frame`, with a precondition on the
heap that register steps keep, a load of the decoder record extends, and every
other heap step drops.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.KeepProofs
set_option autoImplicit false

/-- The decoder record holds output it has to write. -/
def Holding (q : InflateStatePtr) (h : Heap) : Prop :=
  ∃ i s, q = some (.tab i) ∧ h.istates i = some s ∧
    (s.mode = LIT ∨ s.mode = MATCH ∨ (s.mode = COPY ∧ s.length ≠ 0))

/-- The reasons for `goto inf_leave`, with the decoder record at a room stop. -/
def RoomCause (flush : Int32) (q : InflateStatePtr) (l : IL) (h : Heap) : Prop :=
  l.have_ = 0 ∨ flush = Z_BLOCK ∨ flush = Z_TREES ∨ l.ret ≠ Z_OK ∨ (l.left = 0 ∧ Holding q h)

def RoomP {α : Type} (flush : Int32) (q : InflateStatePtr) (pre : Heap → Prop) (l : IL)
    (program : X α) : Prop :=
  ∀ h result regs after, pre h → runX program l h = .ok ((result, regs), after) →
    result = .error .leave → RoomCause flush q regs after

/-- `RoomP` from every start, with no precondition. -/
abbrev RoomX {α : Type} (flush : Int32) (q : InflateStatePtr) (program : X α) : Prop :=
  ∀ l, RoomP flush q (fun _ => True) l program

theorem roomP_weaken {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {program : X α} (all : RoomP flush q (fun _ => True) l program) :
    RoomP flush q pre l program :=
  fun h result regs after _ run leave => all h result regs after trivial run leave

theorem roomP_pure {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (value : α) : RoomP flush q pre l (pure value : X α) := by
  intro h result regs after _ run leave
  cases run
  cases leave

theorem roomP_get {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL} :
    RoomP flush q pre l (get : X IL) := by
  intro h result regs after _ run leave
  cases run
  cases leave

theorem roomP_set {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL} (next : IL) :
    RoomP flush q pre l (set next : X PUnit) := by
  intro h result regs after _ run leave
  cases run
  cases leave

theorem roomP_modify {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (update : IL → IL) : RoomP flush q pre l (modify update : X PUnit) := by
  intro h result regs after _ run leave
  cases run
  cases leave

theorem roomP_lift {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (program : M α) : RoomP flush q pre l (monadLift program : X α) := by
  intro h result regs after _ run leave
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    cases leave

theorem roomP_throw {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (exit : Ex) (cause : exit = .leave → ∀ h, pre h → RoomCause flush q l h) :
    RoomP flush q pre l (throw exit : X α) := by
  intro h result regs after hp run leave
  cases run
  exact cause (Except.error.inj leave) h hp

theorem roomP_ite {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    {test : Prop} [Decidable test] {yes no : X α}
    (hy : test → RoomP flush q pre l yes) (hn : ¬test → RoomP flush q pre l no) :
    RoomP flush q pre l (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

theorem roomP_bind {α β : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    {first : X α} {next : α → X β} (hf : RoomP flush q pre l first)
    (hn : ∀ h value middle heap, pre h → runX first l h = .ok ((.ok value, middle), heap) →
      ∀ result regs after, runX (next value) middle heap = .ok ((result, regs), after) →
        result = .error .leave → RoomCause flush q regs after) :
    RoomP flush q pre l (first >>= next) := by
  intro h result regs after hp run leave
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middle⟩, heap⟩ := pair
    rw [firstRun] at run
    cases decision with
    | error exit =>
      cases run
      exact hf _ _ _ _ hp firstRun (congrArg Except.error (Except.error.inj leave))
    | ok value => exact hn _ _ _ _ hp firstRun _ _ _ run leave

theorem roomP_bind_X {α β : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {first : X α} {next : α → X β} (hf : RoomX flush q first)
    (hn : ∀ value middle, RoomP flush q (fun _ => True) middle (next value)) :
    RoomP flush q pre l (first >>= next) :=
  roomP_bind (roomP_weaken (hf l))
    (fun _ value middle _ _ _ result regs after run leave =>
      hn value middle _ result regs after trivial run leave)

theorem roomP_get_bind {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {next : IL → X α} (hn : RoomP flush q pre l (next l)) :
    RoomP flush q pre l (get >>= next) := by
  apply roomP_bind roomP_get
  intro h value middle heap hp run
  rw [runX_get] at run
  cases run
  exact fun result regs after run leave => hn h result regs after hp run leave

theorem roomP_set_bind {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {target : IL} {next : PUnit → X α} (hn : RoomP flush q pre target (next ())) :
    RoomP flush q pre l (set target >>= next) := by
  apply roomP_bind (roomP_set target)
  intro h value middle heap hp run
  rw [runX_set] at run
  cases run
  exact fun result regs after run leave => hn h result regs after hp run leave

theorem roomP_modify_bind {α : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {update : IL → IL} {next : PUnit → X α}
    (hn : RoomP flush q pre (update l) (next ())) :
    RoomP flush q pre l (modify update >>= next) := by
  apply roomP_bind (roomP_modify update)
  intro h value middle heap hp run
  rw [runX_modify] at run
  cases run
  exact fun result regs after run leave => hn h result regs after hp run leave

theorem roomP_lift_bind {α β : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {program : M α} {next : α → X β}
    (hn : ∀ value, RoomP flush q (fun _ => True) l (next value)) :
    RoomP flush q pre l ((monadLift program : X α) >>= next) := by
  apply roomP_bind (roomP_lift program)
  intro h value middle heap _ run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value1, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact fun result regs after run leave => hn value _ result regs after trivial run leave

/-- A load of a decoder record keeps the heap and records what it read. -/
theorem roomP_ld_bind {β : Type} {flush : Int32} {q p : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {next : InflateState → X β}
    (hn : ∀ s, RoomP flush q (fun h => pre h ∧ ldInflateState p h = .ok (s, h)) l (next s)) :
    RoomP flush q pre l ((monadLift (ldInflateState p) : X InflateState) >>= next) := by
  apply roomP_bind (roomP_lift _)
  intro h value middle heap hp run
  rw [runX_lift] at run
  cases source : ldInflateState p h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value1, heap1⟩ := pair
    simp only [source] at run
    cases run
    have same := (ldInflateState_ok' source).1
    subst same
    exact fun result regs after run leave => hn value _ result regs after ⟨hp, source⟩ run leave

theorem roomP_pure_bind {α β : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {value : α} {next : α → X β} (hn : RoomP flush q pre l (next value)) :
    RoomP flush q pre l ((pure value : X α) >>= next) := by
  apply roomP_bind (roomP_pure value)
  intro h result middle heap hp run
  rw [runX_pure] at run
  cases run
  exact fun result regs after run leave => hn h result regs after hp run leave

theorem roomP_throw_bind {α β : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {exit : Ex} {next : α → X β}
    (cause : exit = .leave → ∀ h, pre h → RoomCause flush q l h) :
    RoomP flush q pre l ((throw exit : X α) >>= next) := by
  apply roomP_bind (roomP_throw exit cause)
  intro h value middle heap _ run
  rw [runX_throw] at run
  cases run

theorem roomP_ite_bind {α β : Type} {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop}
    {l : IL} {test : Prop} [Decidable test] {yes no : X α} {next : α → X β}
    (hy : test → RoomP flush q pre l (yes >>= next)) (hn : ¬test → RoomP flush q pre l (no >>= next)) :
    RoomP flush q pre l ((if test then yes else no) >>= next) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy selected
  · simpa only [selected, ↓reduceIte] using hn selected

theorem roomX_xwhileBrk {flush : Int32} {q : InflateStatePtr} {cond body : X Bool}
    (hc : RoomX flush q cond) (hb : RoomX flush q body) : RoomX flush q (xwhileBrk cond body) := by
  intro l h outcome regs after _ run leave
  let P := fun (state : IL × Stop) (heap : Heap) => match state.2 with
    | .ex .leave => RoomCause flush q state.1 heap
    | _ => True
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (result, next) ← runX cond current.1
      pure (match result with
        | .ok value => (value, (next, Stop.go))
        | .error raised => (false, (next, Stop.ex raised)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (result, next) ← runX body current.1
    pure (match result with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error raised => (next, Stop.ex raised))
  have condInv : ∀ state h test next after, P state h →
      loopCond state h = .ok ((test, next), after) → P next after := by
    intro ⟨current, stop⟩ h test next after currentP executed
    cases stop with
    | go =>
      change (do let (result, next) ← runX cond current; pure _) h = _ at executed
      rw [bind_app] at executed
      cases source : runX cond current h with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨result, regs1⟩, heap1⟩ := pair
        rw [source] at executed
        cases result with
        | ok value => cases executed; trivial
        | error raised =>
          cases executed
          cases raised with
          | leave => exact hc _ _ _ _ _ trivial source rfl
          | ret code => trivial
    | brk => cases executed; exact currentP
    | ex raised => cases executed; exact currentP
  have bodyInv : ∀ state h next after, P state h →
      loopBody state h = .ok (next, after) → P next after := by
    intro ⟨current, stop⟩ h next after currentP executed
    change (do let (result, next) ← runX body current; pure _) h = _ at executed
    rw [bind_app] at executed
    cases source : runX body current h with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨result, regs1⟩, heap1⟩ := pair
      rw [source] at executed
      cases result with
      | ok value => cases executed; cases value <;> trivial
      | error raised =>
        cases executed
        cases raised with
        | leave => exact hb _ _ _ _ _ trivial source rfl
        | ret code => trivial
  unfold xwhileBrk runX at run
  change (do let (next, stop) ← cwhile loopCond loopBody (l, Stop.go); pure _) h = _ at run
  rw [bind_app] at run
  cases source : cwhile loopCond loopBody (l, Stop.go) h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨⟨nextRegs, stop⟩, heap1⟩ := pair
    rw [source] at run
    have fixed := cwhile_success_invariant P condInv bodyInv (by trivial) source
    cases stop with
    | go => cases run; cases leave
    | brk => cases run; cases leave
    | ex raised =>
      cases run
      cases Except.error.inj leave
      exact fixed

theorem roomX_xwhile {flush : Int32} {q : InflateStatePtr} {cond : X Bool} {body : X Unit}
    (hc : RoomX flush q cond) (hb : RoomX flush q body) : RoomX flush q (xwhile cond body) :=
  roomX_xwhileBrk hc (fun _ => roomP_bind_X hb (fun _ _ => roomP_pure false))

theorem roomX_xdoWhile {flush : Int32} {q : InflateStatePtr} {body : X Unit} {cond : X Bool}
    (hb : RoomX flush q body) (hc : RoomX flush q cond) : RoomX flush q (xdoWhile body cond) := by
  unfold xdoWhile
  exact fun _ => roomP_bind_X hb (fun _ _ => roomX_xwhile hc hb _)

theorem roomX_xloopBrk {flush : Int32} {q : InflateStatePtr} {body : X Bool}
    (hb : RoomX flush q body) : RoomX flush q (xloopBrk body) :=
  roomX_xwhileBrk (fun _ => roomP_pure true) hb

/-! ## Leave reasons -/

theorem roomCause_have {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (test : (l.have_ == 0) = true) : ∀ h, pre h → RoomCause flush q l h :=
  fun _ _ => Or.inl (by simpa only [beq_iff_eq] using test)

theorem roomCause_trees {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (test : (flush == Z_TREES) = true) : ∀ h, pre h → RoomCause flush q l h :=
  fun _ _ => Or.inr (Or.inr (Or.inl (by simpa only [beq_iff_eq] using test)))

theorem roomCause_block {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (test : (flush == Z_BLOCK || flush == Z_TREES) = true) : ∀ h, pre h → RoomCause flush q l h := by
  intro _ _
  simp only [Bool.or_eq_true, beq_iff_eq] at test
  rcases test with block | trees
  · exact Or.inr (Or.inl block)
  · exact Or.inr (Or.inr (Or.inl trees))

theorem roomCause_end {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (code : l.ret = Z_STREAM_END) : ∀ h, pre h → RoomCause flush q l h :=
  fun _ _ => Or.inr (Or.inr (Or.inr (Or.inl (by rw [code]; decide))))

theorem roomCause_data {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL}
    (code : l.ret = Z_DATA_ERROR) : ∀ h, pre h → RoomCause flush q l h :=
  fun _ _ => Or.inr (Or.inr (Or.inr (Or.inl (by rw [code]; decide))))

/-- `case LIT`, `case MATCH`: no room, entered with the decoder record holding output. -/
theorem roomCause_left {flush : Int32} {q : InflateStatePtr} {l : IL}
    (test : (l.left == 0) = true) : ∀ h, Holding q h → RoomCause flush q l h :=
  fun _ hold => Or.inr (Or.inr (Or.inr (Or.inr ⟨by simpa only [beq_iff_eq] using test, hold⟩)))

theorem room_imp {flush : Int32} {q : InflateStatePtr} {pre : Heap → Prop} {l : IL} {exit : Ex}
    (cause : ∀ h, pre h → RoomCause flush q l h) :
    exit = .leave → ∀ h, pre h → RoomCause flush q l h := fun _ => cause

theorem roomX_intro {α : Type} {flush : Int32} {q : InflateStatePtr} {program : X α}
    (all : ∀ l, RoomP flush q (fun _ => True) l program) : RoomX flush q program := all

/-- Walk a source body as `leave_cause_source` does; a leave for want of room is
not taken here (it needs the decoder record, `roomCause_left`). -/
macro "room_step" : tactic =>
  `(tactic| first
    | with_reducible exact roomP_pure _
    | with_reducible exact roomP_get
    | with_reducible exact roomP_set _
    | with_reducible exact roomP_modify _
    | with_reducible exact roomP_lift _
    | with_reducible exact ret_not_leave
    | with_reducible exact room_imp (roomCause_have ‹_›)
    | with_reducible exact room_imp (roomCause_left ‹_›)
    | with_reducible exact room_imp (roomCause_trees ‹_›)
    | with_reducible exact room_imp (roomCause_block ‹_›)
    | with_reducible exact room_imp (roomCause_end rfl)
    | exact bne_beq_absurd ‹(_ != 0) = true› ‹(_ == 0) = true›
    | with_reducible exact room_imp (roomCause_data rfl)
    | with_reducible refine roomX_intro (fun _ => ?_)
    | with_reducible refine roomP_get_bind ?_
    | with_reducible refine roomP_set_bind ?_
    | with_reducible refine roomP_modify_bind ?_
    | with_reducible refine roomP_lift_bind (fun _ => ?_)
    | with_reducible refine roomP_pure_bind ?_
    | with_reducible refine roomP_throw_bind ?_
    | with_reducible refine roomP_ite_bind (fun _ => ?_) (fun _ => ?_)
    | with_reducible refine roomP_throw _ ?_
    | with_reducible refine roomP_ite (fun _ => ?_) (fun _ => ?_)
    | with_reducible apply roomX_xdoWhile
    | with_reducible apply roomX_xwhile
    | with_reducible apply roomX_xwhileBrk
    | with_reducible apply roomX_xloopBrk
    | with_reducible refine roomP_bind_X ?_ (fun _ _ => ?_)
    | split)

macro "room_source" : tactic => `(tactic| repeat' room_step)

/-! ## The macros -/

theorem roomX_LOAD (flush : Int32) (q : InflateStatePtr) (strm : ZStreamPtr) (st : InflateStatePtr) :
    RoomX flush q (LOAD strm st) := by
  intro l
  unfold LOAD
  room_source

theorem roomX_RESTORE (flush : Int32) (q : InflateStatePtr) (strm : ZStreamPtr) (st : InflateStatePtr) :
    RoomX flush q (RESTORE strm st) := by
  intro l
  unfold RESTORE
  room_source

theorem roomX_INITBITS (flush : Int32) (q : InflateStatePtr) : RoomX flush q INITBITS := by
  intro l
  unfold INITBITS
  room_source

theorem roomX_PULLBYTE (flush : Int32) (q : InflateStatePtr) : RoomX flush q PULLBYTE := by
  intro l
  unfold PULLBYTE
  room_source

theorem roomX_NEEDBITS (flush : Int32) (q : InflateStatePtr) (n : UInt32) : RoomX flush q (NEEDBITS n) := by
  intro l
  unfold NEEDBITS
  repeat' first
    | with_reducible exact roomX_PULLBYTE _ _ _
    | room_source

theorem roomX_BITS (flush : Int32) (q : InflateStatePtr) (n : UInt32) : RoomX flush q (BITS n) := by
  intro l
  unfold BITS
  room_source

theorem roomX_DROPBITS (flush : Int32) (q : InflateStatePtr) (n : UInt32) : RoomX flush q (DROPBITS n) := by
  intro l
  unfold DROPBITS
  room_source

theorem roomX_BYTEBITS (flush : Int32) (q : InflateStatePtr) : RoomX flush q BYTEBITS := by
  intro l
  unfold BYTEBITS
  room_source

theorem roomX_CRC2 (flush : Int32) (q : InflateStatePtr) (c : Ctx) : RoomX flush q (CRC2 c) := by
  intro l
  unfold CRC2
  room_source

theorem roomX_CRC4 (flush : Int32) (q : InflateStatePtr) (c : Ctx) : RoomX flush q (CRC4 c) := by
  intro l
  unfold CRC4
  room_source

theorem roomX_lookup1 (flush : Int32) (q : InflateStatePtr) (c : Ctx) (distance : Bool) :
    RoomX flush q (lookup1 c distance) := by
  intro l
  unfold lookup1
  repeat' first
    | with_reducible exact roomX_PULLBYTE _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | room_source

theorem roomX_lookup2 (flush : Int32) (q : InflateStatePtr) (c : Ctx) (distance : Bool) :
    RoomX flush q (lookup2 c distance) := by
  intro l
  unfold lookup2
  repeat' first
    | with_reducible exact roomX_PULLBYTE _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | room_source

end Zlib.Inflate.Proofs
