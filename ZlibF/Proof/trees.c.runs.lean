import ZlibF.Proof.«trees.c.arrays»

/-!
# trees.c: the run-length model of `scan_tree` and `send_tree`

The model (`RunSt`, `runStep`, `runAt`, `runBits`, `runFreq`, ...) and its invariant lemmas are those of the earlier proof
(`Spec/trees/Emit`, `Proofs/trees/EmitSendTree`), with the bit strings written with `natBits`.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- Bits of `send_code(s, c, tree)`: `Len` bits of `Code`, least significant first. -/
def codeBits (t : Nat → UInt16 × UInt16) (n : Nat) : List Bool :=
  natBits (t n).1.toNat (t n).2.toNat

/-- Run-length state of `scan_tree` / `send_tree`: `prevlen`, `nextlen`, `count`, `max_count`, `min_count`. -/
structure RunSt where
  prev : Int
  next : Nat
  cnt : Nat
  mx : Nat
  mn : Nat

/-- Initial state for the lengths `L n = tree[n].Len`. -/
def runInit (L : Nat → Nat) : RunSt :=
  if L 0 = 0 then ⟨-1, L 0, 0, 138, 3⟩ else ⟨-1, L 0, 0, 7, 4⟩

/-- One iteration at index `n`: the new state, and the finished run `(curlen, prevlen, count, min_count)` if the run
ends here. -/
def runStep (L : Nat → Nat) (n : Nat) (s : RunSt) : RunSt × Option (Nat × Int × Nat × Nat) :=
  let cur := s.next
  let nx := L (n + 1)
  let cnt := s.cnt + 1
  if cnt < s.mx ∧ cur = nx then (⟨s.prev, nx, cnt, s.mx, s.mn⟩, none)
  else
    ((if nx = 0 then ⟨cur, nx, 0, 138, 3⟩ else if cur = nx then ⟨cur, nx, 0, 6, 3⟩
      else ⟨cur, nx, 0, 7, 4⟩), some (cur, s.prev, cnt, s.mn))

/-- State before iteration `n`. -/
def runAt (L : Nat → Nat) : Nat → RunSt
  | 0 => runInit L
  | n + 1 => (runStep L n (runAt L n)).1

/-- The bits `send_tree` emits for one finished run, with the bit-length code `blt`
(`REP_3_6 = 16`, `REPZ_3_10 = 17`, `REPZ_11_138 = 18`). -/
def runBits (blt : Nat → UInt16 × UInt16) : Option (Nat × Int × Nat × Nat) → List Bool
  | none => []
  | some (cur, prev, cnt, mn) =>
    if cnt < mn then (List.replicate cnt (codeBits blt cur)).flatten
    else if cur ≠ 0 then
      (if (cur : Int) ≠ prev then codeBits blt cur ++ codeBits blt 16 ++ natBits (cnt - 1 - 3) 2
       else codeBits blt 16 ++ natBits (cnt - 3) 2)
    else if cnt ≤ 10 then codeBits blt 17 ++ natBits (cnt - 3) 3
    else codeBits blt 18 ++ natBits (cnt - 11) 7

/-- Bits emitted by the first `n` iterations of `send_tree`. -/
def treeBitsUpTo (blt : Nat → UInt16 × UInt16) (L : Nat → Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => treeBitsUpTo blt L n ++ runBits blt (runStep L n (runAt L n)).2

/-- Everything `send_tree(s, tree, max_code)` emits. -/
def sendTreeBits (blt : Nat → UInt16 × UInt16) (L : Nat → Nat) (maxc : Nat) : List Bool :=
  treeBitsUpTo blt L (maxc + 1)

/-- How much one finished run adds to the frequency of bit-length symbol `k` (`scan_tree`). -/
def runFreq : Option (Nat × Int × Nat × Nat) → Nat → Nat
  | none, _ => 0
  | some (cur, prev, cnt, mn), k =>
    if cnt < mn then (if k = cur then cnt else 0)
    else if cur ≠ 0 then (if (cur : Int) ≠ prev ∧ k = cur then 1 else 0) + (if k = 16 then 1 else 0)
    else if cnt ≤ 10 then (if k = 17 then 1 else 0)
    else (if k = 18 then 1 else 0)

/-- Frequency added to bit-length symbol `k` by the first `n` iterations of `scan_tree`. -/
def scanFreqUpTo (L : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k => scanFreqUpTo L n k + runFreq (runStep L n (runAt L n)).2 k

/-- The lengths `scan_tree` sees: `L` with the guard `0xffff` at `max_code + 1`. -/
def guarded (L : Nat → Nat) (maxc : Nat) (i : Nat) : Nat := if i = maxc + 1 then 0xffff else L i


/-- Invariant of the run-length state (what makes every `send_bits` value fit). -/
def RunInv (s : RunSt) : Prop :=
  s.cnt < s.mx ∧ (s.next = 0 → s.mx = 138 ∧ s.mn = 3) ∧
  (s.next ≠ 0 → (s.mx = 6 ∧ s.mn = 3 ∧ (s.next : Int) = s.prev) ∨
    (s.mx = 7 ∧ s.mn = 4 ∧ (s.next : Int) ≠ s.prev)) ∧
  -1 ≤ s.prev ∧ s.prev < 2 ^ 16

theorem runAt_next (L : Nat → Nat) (n : Nat) : (runAt L n).next = L n := by
  cases n with
  | zero => simp only [runAt, runInit]; split <;> rfl
  | succ n =>
    simp only [runAt, runStep]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl

theorem runInv_runAt (L : Nat → Nat) (hL : ∀ n, L n < 2 ^ 16) (n : Nat) : RunInv (runAt L n) := by
  induction n with
  | zero =>
    simp only [runAt, runInit]
    split
    · rename_i h0; refine ⟨by simp, fun _ => ⟨rfl, rfl⟩, fun h => absurd h0 h, by simp, by simp⟩
    · rename_i h0
      refine ⟨by simp, fun h => absurd h h0, fun _ => Or.inr ⟨rfl, rfl, by simp <;> omega⟩, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    have hnext := runAt_next L n
    simp only [runAt, runStep]
    split
    · rename_i hc
      obtain ⟨hc1, hc2⟩ := hc
      refine ⟨hc1, ?_, ?_, i4, i5⟩
      · intro h0; apply i2; rw [← hc2] at h0; exact h0
      · intro h0; have := i3 (by rw [hc2]; exact h0); simp only at this ⊢; rw [← hc2]; exact this
    · rename_i hc
      have hcur : (runAt L n).next < 2 ^ 16 := by rw [hnext]; exact hL n
      split
      · rename_i hnx
        exact ⟨by simp, fun _ => ⟨rfl, rfl⟩, fun h => absurd hnx h, by simp, by simp <;> omega⟩
      · split
        · rename_i hnx he
          exact ⟨by simp, fun h => absurd h hnx, fun _ => Or.inl ⟨rfl, rfl, by simp [he]⟩, by simp, by simp <;> omega⟩
        · rename_i hnx he
          exact ⟨by simp, fun h => absurd h hnx, fun _ => Or.inr ⟨rfl, rfl, by simp <;> omega⟩, by simp, by simp <;> omega⟩

theorem treeBitsUpTo_mono (blt : Nat → UInt16 × UInt16) (L : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    (treeBitsUpTo blt L i).length ≤ (treeBitsUpTo blt L j).length := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    by_cases e : i = j + 1
    · subst e; exact Nat.le_refl _
    · have := ih (by omega); simp only [treeBitsUpTo, List.length_append]; omega

/-- `tree[i].Freq += v` (modulo 2^16). -/
def addFc (a : Array CtData) (i : Nat) (v : UInt16) : Array CtData := a.set! i { (a[i]!) with fc := (a[i]!).fc + v }

@[simp] theorem addFc_size (a : Array CtData) (i : Nat) (v : UInt16) : (addFc a i v).size = a.size := by
  simp [addFc]

theorem addFc_dl (a : Array CtData) (i : Nat) (v : UInt16) (k : Nat) : ((addFc a i v)[k]!).dl = (a[k]!).dl := by
  unfold addFc; rw [getElem!_set!]; split <;> simp_all

theorem addFc_fc (a : Array CtData) (i : Nat) (v : UInt16) (hi : i < a.size) (k : Nat) :
    ((addFc a i v)[k]!).fc = if k = i then (a[k]!).fc + v else (a[k]!).fc := by
  unfold addFc; rw [getElem!_set!]
  by_cases h : i = k
  · subst h; simp [hi]
  · simp [h, Ne.symm h]


end Zlib.Trees.Proofs.Out
