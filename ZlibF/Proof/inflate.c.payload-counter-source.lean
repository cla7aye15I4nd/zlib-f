import ZlibF.Proof.«inflate.c.exit-code-run»

namespace Zlib.Inflate.Proofs.PayloadCounters
open C Zlib.Inflate
set_option autoImplicit false
abbrev counterFields (l : IL) : UInt32 × UInt32 × Int32 := (l.in_, l.out_, l.ret)


/-- Source fragments without input-start/output-start/return assignments
retain all three values. Table construction and trailer paths are separate. -/
def CounterBaseX {α : Type} (base : UInt32 × UInt32 × Int32) (program : X α) : Prop :=
  ∀ l h result regs after, counterFields l = base →
    runX program l h = .ok ((result, regs), after) → counterFields regs = base

theorem counterBaseX_pure {α : Type} (base : UInt32 × UInt32 × Int32) (value : α) : CounterBaseX base (pure value) := by
  intro l h result regs after current run
  cases run
  exact current

theorem counterBaseX_get (base : UInt32 × UInt32 × Int32) : CounterBaseX base (get : X IL) := by
  intro l h result regs after current run
  cases run
  exact current

theorem counterBaseX_set (base : UInt32 × UInt32 × Int32) (l : IL) (current : counterFields l = base) :
    CounterBaseX base (set l : X Unit) := by
  intro before h result regs after _ run
  cases run
  exact current

theorem counterBaseX_modify (base : UInt32 × UInt32 × Int32) (update : IL → IL)
    (fixed : ∀ l, counterFields l = base → counterFields (update l) = base) :
    CounterBaseX base (modify update : X Unit) := by
  intro l h result regs after current run
  cases run
  exact fixed l current

theorem counterBaseX_lift {α : Type} (base : UInt32 × UInt32 × Int32) (program : M α) :
    CounterBaseX base (monadLift program : X α) := by
  intro l h result regs after current run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact current

theorem counterBaseX_throw {α : Type} (base : UInt32 × UInt32 × Int32) (exit : Ex) :
    CounterBaseX base (throw exit : X α) := by
  intro l h result regs after current run
  cases run
  exact current

theorem counterBaseX_bind {α β : Type} {base : UInt32 × UInt32 × Int32} {first : X α} {next : α → X β}
    (hf : CounterBaseX base first) (hn : ∀ value, CounterBaseX base (next value)) :
    CounterBaseX base (first >>= next) := by
  intro l h result regs after current run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    have middle := hf _ _ _ _ _ current firstRun
    cases decision with
    | error exit => cases run; exact middle
    | ok value => exact hn value _ _ _ _ _ middle run


theorem counterBaseX_get_bind {α : Type} {base : UInt32 × UInt32 × Int32} {next : IL → X α}
    (body : ∀ l, counterFields l = base → CounterBaseX base (next l)) :
    CounterBaseX base (get >>= next) := by
  intro l h result regs after current run
  rw [runX_bind, runX_get] at run
  exact body l current _ _ _ _ _ current run

theorem counterBaseX_ite {α : Type} {base : UInt32 × UInt32 × Int32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : CounterBaseX base yes) (hn : CounterBaseX base no) : CounterBaseX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem counterBaseX_xwhileBrk {base : UInt32 × UInt32 × Int32} {cond body : X Bool}
    (hc : CounterBaseX base cond) (hb : CounterBaseX base body) : CounterBaseX base (xwhileBrk cond body) := by
  intro l h result regs after current run
  let P := fun (state : IL × Stop) (_heap : Heap) => counterFields state.1 = base
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (outcome, next) ← runX cond current.1
      pure (match outcome with
        | .ok value => (value, (next, Stop.go))
        | .error exit => (false, (next, Stop.ex exit)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (outcome, next) ← runX body current.1
    pure (match outcome with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error exit => (next, Stop.ex exit))
  have condInv : ∀ state h test next after, P state h →
      loopCond state h = .ok ((test, next), after) → P next after := by
    intro ⟨state, stop⟩ h test next after stateP executed
    cases stop with
    | go =>
      change (do let (outcome, next) ← runX cond state; pure _) h = _ at executed
      rw [bind_app] at executed
      cases source : runX cond state h with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨outcome, nextRegs⟩, heap1⟩ := pair
        rw [source] at executed
        have fixed := hc _ _ _ _ _ stateP source
        cases outcome <;> cases executed <;> exact fixed
    | brk => cases executed; exact stateP
    | ex exit => cases executed; exact stateP
  have bodyInv : ∀ state h next after, P state h →
      loopBody state h = .ok (next, after) → P next after := by
    intro ⟨state, stop⟩ h next after stateP executed
    change (do let (outcome, next) ← runX body state; pure _) h = _ at executed
    rw [bind_app] at executed
    cases source : runX body state h with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨outcome, nextRegs⟩, heap1⟩ := pair
      rw [source] at executed
      have fixed := hb _ _ _ _ _ stateP source
      cases outcome <;> cases executed <;> exact fixed
  unfold xwhileBrk runX at run
  change (do let (next, stop) ← cwhile loopCond loopBody (l, Stop.go); pure _) h = _ at run
  rw [bind_app] at run
  cases source : cwhile loopCond loopBody (l, Stop.go) h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨⟨nextRegs, stop⟩, heap1⟩ := pair
    rw [source] at run
    have fixed := cwhile_success_invariant P condInv bodyInv current source
    cases stop <;> cases run <;> exact fixed

theorem counterBaseX_xwhile {base : UInt32 × UInt32 × Int32} {cond : X Bool} {body : X Unit}
    (hc : CounterBaseX base cond) (hb : CounterBaseX base body) : CounterBaseX base (xwhile cond body) :=
  counterBaseX_xwhileBrk hc (counterBaseX_bind hb (fun _ => counterBaseX_pure base false))

theorem counterBaseX_xdoWhile {base : UInt32 × UInt32 × Int32} {body : X Unit} {cond : X Bool}
    (hb : CounterBaseX base body) (hc : CounterBaseX base cond) : CounterBaseX base (xdoWhile body cond) := by
  unfold xdoWhile
  exact counterBaseX_bind hb (fun _ => counterBaseX_xwhile hc hb)

theorem counterBaseX_xloopBrk {base : UInt32 × UInt32 × Int32} {body : X Bool} (hb : CounterBaseX base body) :
    CounterBaseX base (xloopBrk body) := counterBaseX_xwhileBrk (counterBaseX_pure base true) hb

macro "counter_base_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact counterBaseX_pure _ _
    | with_reducible exact counterBaseX_get _
    | with_reducible exact counterBaseX_lift _ _
    | with_reducible exact counterBaseX_throw _ _
    | with_reducible refine counterBaseX_set _ _ ?_
    | with_reducible refine counterBaseX_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine counterBaseX_get_bind (fun _ fixed => ?_)
    | with_reducible apply counterBaseX_xdoWhile
    | with_reducible apply counterBaseX_xwhile
    | with_reducible apply counterBaseX_xwhileBrk
    | with_reducible apply counterBaseX_xloopBrk
    | with_reducible apply counterBaseX_ite
    | with_reducible refine counterBaseX_bind ?_ (fun _ => ?_)
    | rfl
    | split)


theorem counterBaseX_LOAD (base : UInt32 × UInt32 × Int32) (strm : ZStreamPtr) (st : InflateStatePtr) : CounterBaseX base (LOAD strm st) := by
  unfold LOAD
  repeat' first
    | counter_base_source

theorem counterBaseX_RESTORE (base : UInt32 × UInt32 × Int32) (strm : ZStreamPtr) (st : InflateStatePtr) : CounterBaseX base (RESTORE strm st) := by
  unfold RESTORE
  repeat' first
    | counter_base_source

theorem counterBaseX_INITBITS (base : UInt32 × UInt32 × Int32)  : CounterBaseX base (INITBITS) := by
  unfold INITBITS
  repeat' first
    | counter_base_source

theorem counterBaseX_PULLBYTE (base : UInt32 × UInt32 × Int32)  : CounterBaseX base (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | counter_base_source

theorem counterBaseX_NEEDBITS (base : UInt32 × UInt32 × Int32) (n : UInt32) : CounterBaseX base (NEEDBITS n) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact counterBaseX_PULLBYTE base
    | counter_base_source

theorem counterBaseX_BITS (base : UInt32 × UInt32 × Int32) (n : UInt32) : CounterBaseX base (BITS n) := by
  unfold BITS
  repeat' first
    | counter_base_source

theorem counterBaseX_DROPBITS (base : UInt32 × UInt32 × Int32) (n : UInt32) : CounterBaseX base (DROPBITS n) := by
  unfold DROPBITS
  repeat' first
    | counter_base_source

theorem counterBaseX_BYTEBITS (base : UInt32 × UInt32 × Int32)  : CounterBaseX base (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | counter_base_source

theorem counterBaseX_CRC2 (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (CRC2 c) := by
  unfold CRC2
  repeat' first
    | counter_base_source

theorem counterBaseX_CRC4 (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (CRC4 c) := by
  unfold CRC4
  repeat' first
    | counter_base_source

theorem counterBaseX_lookup1 (base : UInt32 × UInt32 × Int32) (c : Ctx) (distance : Bool) : CounterBaseX base (lookup1 c distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact counterBaseX_PULLBYTE base
    | with_reducible exact counterBaseX_BITS base _
    | counter_base_source

theorem counterBaseX_lookup2 (base : UInt32 × UInt32 × Int32) (c : Ctx) (distance : Bool) : CounterBaseX base (lookup2 c distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact counterBaseX_PULLBYTE base
    | with_reducible exact counterBaseX_BITS base _
    | counter_base_source



theorem counterBaseX_inflate_LIT (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (inflate_LIT c) := by
  unfold inflate_LIT
  repeat' first
    | counter_base_source

theorem counterBaseX_inflate_MATCH (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (inflate_MATCH c) := by
  unfold inflate_MATCH
  repeat' first
    | with_reducible exact counterBaseX_NEEDBITS base _
    | counter_base_source

theorem counterBaseX_inflate_DISTEXT (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact counterBaseX_PULLBYTE base
    | with_reducible exact counterBaseX_NEEDBITS base _
    | with_reducible exact counterBaseX_BITS base _
    | with_reducible exact counterBaseX_DROPBITS base _
    | with_reducible exact counterBaseX_inflate_MATCH base _
    | counter_base_source

theorem counterBaseX_inflate_DIST (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (inflate_DIST c) := by
  unfold inflate_DIST
  repeat' first
    | with_reducible exact counterBaseX_DROPBITS base _
    | with_reducible exact counterBaseX_lookup1 base _ _
    | with_reducible exact counterBaseX_lookup2 base _ _
    | with_reducible exact counterBaseX_inflate_DISTEXT base _
    | counter_base_source

theorem counterBaseX_inflate_LENEXT (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (inflate_LENEXT c) := by
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact counterBaseX_NEEDBITS base _
    | with_reducible exact counterBaseX_BITS base _
    | with_reducible exact counterBaseX_DROPBITS base _
    | with_reducible exact counterBaseX_inflate_DIST base _
    | counter_base_source

theorem counterBaseX_inflate_LEN (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (inflate_LEN c) := by
  unfold inflate_LEN
  repeat' first
    | with_reducible exact counterBaseX_LOAD base _ _
    | with_reducible exact counterBaseX_RESTORE base _ _
    | with_reducible exact counterBaseX_DROPBITS base _
    | with_reducible exact counterBaseX_lookup1 base _ _
    | with_reducible exact counterBaseX_lookup2 base _ _
    | with_reducible exact counterBaseX_inflate_LENEXT base _
    | counter_base_source

theorem counterBaseX_inflate_LEN_ (base : UInt32 × UInt32 × Int32) (c : Ctx) : CounterBaseX base (inflate_LEN_ c) := by
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact counterBaseX_inflate_LEN base _
    | counter_base_source





#print axioms counterBaseX_pure
#print axioms counterBaseX_get
#print axioms counterBaseX_set
#print axioms counterBaseX_modify
#print axioms counterBaseX_lift
#print axioms counterBaseX_throw
#print axioms counterBaseX_bind
#print axioms counterBaseX_get_bind
#print axioms counterBaseX_ite
#print axioms counterBaseX_xwhileBrk
#print axioms counterBaseX_xwhile
#print axioms counterBaseX_xdoWhile
#print axioms counterBaseX_xloopBrk
#print axioms counterBaseX_LOAD
#print axioms counterBaseX_RESTORE
#print axioms counterBaseX_INITBITS
#print axioms counterBaseX_PULLBYTE
#print axioms counterBaseX_NEEDBITS
#print axioms counterBaseX_BITS
#print axioms counterBaseX_DROPBITS
#print axioms counterBaseX_BYTEBITS
#print axioms counterBaseX_CRC2
#print axioms counterBaseX_CRC4
#print axioms counterBaseX_lookup1
#print axioms counterBaseX_lookup2
#print axioms counterBaseX_inflate_LIT
#print axioms counterBaseX_inflate_MATCH
#print axioms counterBaseX_inflate_DISTEXT
#print axioms counterBaseX_inflate_DIST
#print axioms counterBaseX_inflate_LENEXT
#print axioms counterBaseX_inflate_LEN
#print axioms counterBaseX_inflate_LEN_
end Zlib.Inflate.Proofs.PayloadCounters
