import ZlibF.Zlib.«deflate_strategies.c»
import ZlibF.Proof.«deflate.c.engine.macros»
import ZlibF.Proof.«deflate.c.engine.match»

/-!
# deflate.c, engine: the comparison step of `longest_match`

`lm_cond` is the condition of the inner `do ... while`: `*++scan == *++match && ... (8 times) && scan < strend`.
`lmCondR n` is the same computation written as a recursion on the number of comparisons left. `lm_cond_eq` shows that
the translation is `lmCondR 8`; `lmCondR_ok` says what `n` comparisons do inside a window block: they stop at the
first position where the two strings differ, or run out and test `scan < strend`.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

/-- The recursion on the number of comparisons left. -/
def lmCondR (strend : BPtr) : Nat → BPtr → BPtr → M (Bool × BPtr × BPtr)
  | 0, scan, m => do return (← Ptr.lt scan strend, scan, m)
  | n + 1, scan, m => do
    let scan ← padd scan 1
    let m ← padd m 1
    if (← load8 scan) != (← load8 m) then return (false, scan, m)
    lmCondR strend n scan m

/-- The offset at which `n` comparisons from offset `t` stop: the first `i` in `1 .. n` with
`w (S + t + i) != w (C + t + i)` gives `some (t + i)`; `none` when all `n` agree. -/
def cmpSteps (w : Nat → UInt8) (S C : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, t => if w (S + t + 1) ≠ w (C + t + 1) then some (t + 1) else cmpSteps w S C n (t + 1)

theorem cmpSteps_some {w : Nat → UInt8} {S C : Nat} :
    ∀ n t k, cmpSteps w S C n t = some k → t + 1 ≤ k ∧ k ≤ t + n ∧ w (S + k) ≠ w (C + k) ∧
      ∀ j, t + 1 ≤ j → j < k → w (S + j) = w (C + j) := by
  intro n
  induction n with
  | zero => intro t k h; simp [cmpSteps] at h
  | succ n ih =>
    intro t k h
    unfold cmpSteps at h
    split at h
    · rename_i hne
      cases h
      refine ⟨by omega, by omega, by rwa [show S + (t + 1) = S + t + 1 by omega, show C + (t + 1) = C + t + 1 by omega],
        fun j h1 h2 => by omega⟩
    · rename_i heq
      obtain ⟨a, b, c, d⟩ := ih (t + 1) k h
      refine ⟨by omega, by omega, c, fun j h1 h2 => ?_⟩
      by_cases hj : j = t + 1
      · subst hj
        have e : w (S + t + 1) = w (C + t + 1) := by simpa using heq
        rwa [show S + (t + 1) = S + t + 1 by omega, show C + (t + 1) = C + t + 1 by omega]
      · exact d j (by omega) h2

theorem cmpSteps_none {w : Nat → UInt8} {S C : Nat} :
    ∀ n t, cmpSteps w S C n t = none → ∀ j, t + 1 ≤ j → j ≤ t + n → w (S + j) = w (C + j) := by
  intro n
  induction n with
  | zero => intro t _ j h1 h2; omega
  | succ n ih =>
    intro t h j h1 h2
    unfold cmpSteps at h
    split at h
    · simp at h
    · rename_i heq
      by_cases hj : j = t + 1
      · subst hj
        have e : w (S + t + 1) = w (C + t + 1) := by simpa using heq
        rwa [show S + (t + 1) = S + t + 1 by omega, show C + (t + 1) = C + t + 1 by omega]
      · exact ih (t + 1) h j (by omega) (by omega)

/-- **n comparisons of `lm_cond` inside the window.** The scan and match pointers are at offsets `S + t` and `C + t`
of one byte block, `C <= S`, and the end pointer is `S + 258`; the reads stay below `S + 258 < size`. The result
stops at the first differing position, or tests `scan < strend` after `n` equal comparisons. -/
theorem lmCondR_ok {h : Heap} {wb : Nat} {wa : Array UInt8} (hw : h.bytes wb = some wa) (S C : Nat)
    (hS : S + 258 < wa.size) (hCS : C ≤ S) :
    ∀ n t, t + n ≤ 258 →
      lmCondR (.ref (.blk wb) (S + 258)) n (.ref (.blk wb) (S + t)) (.ref (.blk wb) (C + t)) h =
        .ok ((match cmpSteps (bfn wa) S C n t with
          | some k => (false, Ptr.ref (BRef.blk wb) (S + k), Ptr.ref (BRef.blk wb) (C + k))
          | none => (decide (S + (t + n) < S + 258), Ptr.ref (BRef.blk wb) (S + (t + n)),
              Ptr.ref (BRef.blk wb) (C + (t + n)))), h) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have : OkOn h (Ptr.lt (Ptr.ref (BRef.blk wb) (S + t)) (Ptr.ref (BRef.blk wb) (S + 258))) (decide (S + t < S + 258)) :=
      Ptr.lt_ok (r := BRef.blk wb) (by simpa using hw) (by omega) (by omega)
    simp only [lmCondR, cmpSteps, bind_app, Nat.add_zero]
    unfold OkOn at this
    rw [this]; rfl
  | succ n ih =>
    intro t ht
    have g : Space.get h (BRef.blk wb) = some wa := by simpa using hw
    have hs1 : S + t + 1 < wa.size := by omega
    have hc1 : C + t + 1 < wa.size := by omega
    have p1 : padd (Ptr.ref (BRef.blk wb) (S + t)) 1 h = .ok (Ptr.ref (BRef.blk wb) (S + t + 1), h) :=
      padd_ok' g (by omega)
    have p2 : padd (Ptr.ref (BRef.blk wb) (C + t)) 1 h = .ok (Ptr.ref (BRef.blk wb) (C + t + 1), h) :=
      padd_ok' g (by omega)
    have l1 : load8 (Ptr.ref (BRef.blk wb) (S + t + 1)) h = .ok (wa[S + t + 1], h) := Ptr.load_ok g hs1
    have l2 : load8 (Ptr.ref (BRef.blk wb) (C + t + 1)) h = .ok (wa[C + t + 1], h) := Ptr.load_ok g hc1
    have b1 : bfn wa (S + t + 1) = wa[S + t + 1] := by simp [bfn, Array.getD_eq_getD_getElem?, hs1]
    have b2 : bfn wa (C + t + 1) = wa[C + t + 1] := by simp [bfn, Array.getD_eq_getD_getElem?, hc1]
    simp only [lmCondR, bind_app, p1, p2, l1, l2]
    by_cases hne : wa[S + t + 1] = wa[C + t + 1]
    · have hne' : ¬ (bfn wa (S + t + 1) ≠ bfn wa (C + t + 1)) := by rw [b1, b2]; simpa using hne
      have hih := ih (t + 1) (by omega)
      rw [show S + (t + 1) = S + t + 1 by omega, show C + (t + 1) = C + t + 1 by omega,
        show t + 1 + n = t + (n + 1) by omega] at hih
      simp only [cmpSteps, hne', ite_false, hne, bne_self_eq_false, Bool.false_eq_true, hih]
    · have hne' : bfn wa (S + t + 1) ≠ bfn wa (C + t + 1) := by rw [b1, b2]; exact hne
      have hb : (wa[S + t + 1] != wa[C + t + 1]) = true := by simpa using hne
      simp only [cmpSteps, ite_eq_left hne', hb]
      rfl

end Zlib.Deflate.Engine.Proofs
