import ZlibF.Proof.«inflate.c.match-emit»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false
set_option maxRecDepth 2048

/-- Actual MATCH source selection with its exact emission suffix. -/
def matchSelect (c : Ctx) : X Unit := do
  let l ← get
  -- if (left == 0) goto inf_leave;
  if l.left == 0 then throw Ex.leave
  -- copy = out - left;
  let mut copy := l.out_ - l.left
  let mut from_ : BPtr := l.from_
  let s ← ldInflateState c.st
  -- if (state->offset > copy) { /* copy from window */
  if s.offset > copy then
    -- copy = state->offset - copy;
    copy := s.offset - copy
    -- if (copy > state->whave) { if (state->sane) { ...BAD; break; } }
    if copy > s.whave then
      if s.sane != 0 then
        badMode c "invalid distance too far back"
        return
    -- if (copy > state->wnext) { copy -= state->wnext; from = state->window + (state->wsize - copy); }
    if copy > s.wnext then
      copy := copy - s.wnext
      from_ ← s.window.add ((s.wsize - copy).toNat : Int)
    else
      -- else from = state->window + (state->wnext - copy);
      from_ ← s.window.add ((s.wnext - copy).toNat : Int)
    -- if (copy > state->length) copy = state->length;
    if copy > s.length then copy := s.length
  else
    -- from = put - state->offset; copy = state->length;
    from_ ← l.put.add (-(s.offset.toNat : Int))
    copy := s.length
  -- if (copy > left) copy = left;
  if copy > l.left then copy := l.left
  matchEmitFrom c l copy from_

theorem inflate_MATCH_select_cut (c : Ctx) : inflate_MATCH c = matchSelect c := rfl

/-- Source selection for a back-reference in the current output. -/
theorem matchSelect_output_cut {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (left : l.left ≠ 0)
    (inOutput : ¬ s.offset > l.out_ - l.left) {from_ : BPtr}
    (address : l.put.add (-(s.offset.toNat : Int)) h = .ok (from_, h)) :
    runX (matchSelect c) l h = runX (matchEmit c (if s.length > l.left then l.left else s.length) from_) l h := by
  unfold matchSelect matchEmit
  rw [runX_bind, runX_get]
  simp only [left, beq_iff_eq, ↓reduceIte]
  rw [runX_bind, runX_ldS E]
  simp only [inOutput, ↓reduceIte]
  rw [runX_bind, runX_lift_ok address]
  simp only []
  split <;> simp only [runX_bind, runX_get, ↓reduceIte]

/-- Source selection for the window segment before the ring's write cursor. -/
theorem matchSelect_window_cut {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (left : l.left ≠ 0)
    (inWindow : s.offset > l.out_ - l.left)
    (history : ¬ s.offset - (l.out_ - l.left) > s.whave)
    (linear : ¬ s.offset - (l.out_ - l.left) > s.wnext) {from_ : BPtr}
    (address : s.window.add ((s.wnext - (s.offset - (l.out_ - l.left))).toNat : Int) h = .ok (from_, h)) :
    let span := s.offset - (l.out_ - l.left)
    let capped := if span > s.length then s.length else span
    runX (matchSelect c) l h = runX (matchEmit c (if capped > l.left then l.left else capped) from_) l h := by
  dsimp only
  unfold matchSelect matchEmit
  rw [runX_bind, runX_get]
  simp only [left, beq_iff_eq, ↓reduceIte]
  rw [runX_bind, runX_ldS E]
  simp only [inWindow, history, linear, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_lift_ok address]
  simp only []
  split <;> split <;> simp only [runX_bind, runX_get, ↓reduceIte]

/-- Source selection for the window segment that reaches the ring's end. -/
theorem matchSelect_wrap_cut {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (left : l.left ≠ 0)
    (inWindow : s.offset > l.out_ - l.left)
    (history : ¬ s.offset - (l.out_ - l.left) > s.whave)
    (wrap : s.offset - (l.out_ - l.left) > s.wnext) {from_ : BPtr}
    (address : s.window.add ((s.wsize - (s.offset - (l.out_ - l.left) - s.wnext)).toNat : Int) h = .ok (from_, h)) :
    let span := s.offset - (l.out_ - l.left) - s.wnext
    let capped := if span > s.length then s.length else span
    runX (matchSelect c) l h = runX (matchEmit c (if capped > l.left then l.left else capped) from_) l h := by
  dsimp only
  unfold matchSelect matchEmit
  rw [runX_bind, runX_get]
  simp only [left, beq_iff_eq, ↓reduceIte]
  rw [runX_bind, runX_ldS E]
  simp only [inWindow, history, wrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, runX_lift_ok address]
  simp only []
  split <;> split <;> simp only [runX_bind, runX_get, ↓reduceIte]

/-- With the normal sanity check enabled, insufficient history returns BAD
before any window pointer is formed. -/
theorem matchSelect_bad_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (left : l.left ≠ 0)
    (inWindow : s.offset > l.out_ - l.left)
    (history : s.offset - (l.out_ - l.left) > s.whave) (sane : s.sane ≠ 0) :
    ∃ i, strTable[i]? = some "invalid distance too far back" ∧
      runX (matchSelect c) l h = .ok ((.ok (), l), badHeap h r zs z s i) := by
  obtain ⟨i, msg, run⟩ := runX_badMode E (msg := "invalid distance too far back") (by simp [strTable]) l
  refine ⟨i, msg, ?_⟩
  unfold matchSelect
  rw [runX_bind, runX_get]
  simp only [left, beq_iff_eq, ↓reduceIte]
  rw [runX_bind, runX_ldS E]
  simp only [inWindow, history, sane, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
  rw [runX_bind, run]
  simp only [runX_pure]

/-- No output room leaves MATCH before inspecting its state or source. -/
theorem matchSelect_wait (c : Ctx) (h : Heap) (l : IL) (left : l.left = 0) :
    runX (matchSelect c) l h = .ok ((.error Ex.leave, l), h) := by
  unfold matchSelect
  rw [runX_bind, runX_get]
  simp only [left, beq_self_eq_true, ↓reduceIte, runX_throw]
  rw [runX_bind, runX_throw]

end Zlib.Inflate.Proofs
