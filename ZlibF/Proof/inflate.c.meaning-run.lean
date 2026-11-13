import ZlibF.Proof.«inflate.c.meaning-dictid»
import ZlibF.Proof.«inflate.c.loop-control-post»
import ZlibF.Proof.«inflate.c.completes-blocked»

/-!
# inflate.c: the mode loop of one call keeps the format meaning (`loop_meaning`)

The mode loop `for (;;) switch (state->mode)` of one call, from a trip with
`LoopMatches`, ends in one of:

* `goto inf_leave` with `LoopMatches` (input or output exhausted, a `Z_BLOCK`
  or `Z_TREES` stop), from `DONE` with `Z_STREAM_END` and `LoopMatches`, or from
  `BAD` with `Z_DATA_ERROR` and `LoopBad` (`LoopExit`);
* `return Z_NEED_DICT` from `DICT` at a dictionary request (`NeedDictExit`).

The per-mode steps are one premise, `TripMeaning`: from `LoopMatches`, one
dispatch runs without a fault and ends in a `TripOutcome` or a
`NeedDictExit`. The per-mode lemmas of batch 1 (body modes) and batch 2
(header, dictionary, trailer modes) prove it mode by mode. Their side
premises (the stream record, the CRC tables, the window bounds) are facts of
the safety proof, carried as `Side`: a predicate on the registers and the
heap that every normal end of a dispatch keeps (`SideKept`). `Side` is a
parameter, so the loop rule does not fix the safety invariant.

A trip from `LoopBad` is `case BAD:` (`bad_trip`): it sets `Z_DATA_ERROR`
and leaves.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningDictid (NeedDictExit)
set_option autoImplicit false

/-- One trip of the mode loop from `LoopMatches`, under the side facts
`Side`, runs without a fault and ends in a `TripOutcome` or at the
dictionary request. -/
def TripMeaning (c : Ctx) (f : LoopFrame) (Side : IL → Heap → Prop) : Prop :=
  ∀ h l, Side l h → LoopMatches c f h l →
    ∃ result l' h', runX (inflate_dispatch c) l h = .ok ((result, l'), h') ∧
      (TripOutcome c f result h' l' ∨ NeedDictExit c f result h' l')

/-- Every normal end of a dispatch keeps the side facts. -/
def SideKept (c : Ctx) (Side : IL → Heap → Prop) : Prop :=
  ∀ l h l' h', Side l h → runX (inflate_dispatch c) l h = .ok ((.ok (), l'), h') → Side l' h'

/-- How the mode loop of a call ends, with the registers at the exit. -/
def LoopExit (c : Ctx) (f : LoopFrame) (exit : Ex) (h : Heap) (l : IL) : Prop :=
  (exit = .leave ∧
    (LoopMatches c f h l ∨
     (l.ret = Z_STREAM_END ∧ LoopMatches c f h { l with ret := Z_OK }) ∨
     (l.ret = Z_DATA_ERROR ∧ LoopBad c f h { l with ret := Z_OK }))) ∨
  NeedDictExit c f (.error exit) h l

/-- The loop never ends normally. -/
theorem xwhile_true_not_ok {body : X Unit} {l l' : IL} {h h' : Heap} {u : Unit}
    (run : runX (xwhile (pure true) body) l h = .ok ((.ok u, l'), h')) : False := by
  unfold xwhile at run
  exact xwhileBrk_true_not_ok (fun l0 h0 l1 h1 e => by
    rw [runX_bind] at e
    split at e
    · rw [runX_pure] at e; cases e
    · cases e
    · cases e) run

/-- `loop_meaning`: the mode loop of a call, entered with `LoopMatches` and the
side facts, ends in a `LoopExit`. -/
theorem loop_meaning {c : Ctx} {f : LoopFrame} {Side : IL → Heap → Prop} {r : ZStreamRef}
    (trip : TripMeaning c f Side) (kept : SideKept c Side) (strm : c.strm = some r)
    (record : ∀ l h, Side l h → ∃ z, r.get h = some z)
    {l regs : IL} {h after : Heap} {outcome : Except Ex Unit}
    (side : Side l h) (start : LoopMatches c f h l)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((outcome, regs), after)) :
    ∃ exit, outcome = .error exit ∧ LoopExit c f exit after regs := by
  cases outcome with
  | ok u => exact absurd run (fun run => xwhile_true_not_ok run)
  | error exit =>
    refine ⟨exit, rfl, ?_⟩
    let P : IL → Heap → Prop := fun l h => Side l h ∧ (LoopMatches c f h l ∨ LoopBad c f h l)
    let Q : Ex → IL → Heap → Prop := fun e l h => LoopExit c f e h l
    have step : ∀ l h outcome regs after, P l h →
        runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) →
        match outcome with
        | .ok () => P regs after
        | .error exit => Q exit regs after := by
      intro l h outcome regs after ⟨side, current⟩ source
      rcases current with loop | bad
      · obtain ⟨result, l', h', run', outcome'⟩ := trip h l side loop
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases outcome' with tripOut | needDict
        · rcases tripOut with ⟨rfl, cont⟩ | ⟨rfl, leave⟩
          · exact ⟨kept l h regs after side source, cont⟩
          · exact Or.inl ⟨rfl, leave⟩
        · have exitEq := needDict.1
          cases exitEq
          exact Or.inr needDict
      · obtain ⟨z, hz⟩ := record l h side
        obtain ⟨run', tripOut⟩ := bad_trip bad strm hz
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases tripOut with ⟨eq, _⟩ | ⟨_, leave⟩
        · cases eq
        · exact Or.inl ⟨rfl, leave⟩
    exact xwhile_success_control_post P Q step ⟨side, Or.inl start⟩ run

#print axioms loop_meaning

end Zlib.Inflate.Proofs
