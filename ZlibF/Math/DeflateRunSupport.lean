import ZlibF.Proof.«trees.c.runs»

/-! # Positive-length symbols in the existing run-length model

These heap-free lemmas use the unchanged run model shared by the checked
scan and the forthcoming output proof. They introduce no execution contract.
-/

namespace Zlib.Trees.Proofs.Out

theorem runStep_done_prev (L : Nat → Nat) (n : Nat) (s : RunSt)
    (ha : ¬ (s.cnt + 1 < s.mx ∧ s.next = L (n + 1))) :
    (runStep L n s).1.prev = s.next := by
  simp only [runStep, ite_eq_right ha]
  split
  · rfl
  · split <;> rfl

theorem runStep_done_cnt (L : Nat → Nat) (n : Nat) (s : RunSt)
    (ha : ¬ (s.cnt + 1 < s.mx ∧ s.next = L (n + 1))) :
    (runStep L n s).1.cnt = 0 := by
  simp only [runStep, ite_eq_right ha]
  split
  · rfl
  · split <;> rfl

theorem scanFreq_le_next (L : Nat → Nat) (n k : Nat) :
    scanFreqUpTo L n k ≤ scanFreqUpTo L (n + 1) k := by
  simp only [scanFreqUpTo]
  omega

/-- A previously completed positive run already emitted its ordinary
length symbol. Repetitions can omit that symbol only after it was emitted. -/
theorem scanFreq_prev_positive (L : Nat → Nat) (n k : Nat) (hk : 0 < k)
    (hp : (runAt L n).prev = (k : Int)) : 0 < scanFreqUpTo L n k := by
  induction n with
  | zero =>
    simp only [runAt, runInit] at hp
    split at hp <;> (dsimp only at hp; omega)
  | succ n ih =>
    by_cases ha : (runAt L n).cnt + 1 < (runAt L n).mx ∧ (runAt L n).next = L (n + 1)
    · have hp' : (runAt L n).prev = (k : Int) := by
        simpa only [runAt, runStep, ite_eq_left ha] using hp
      have hb := ih hp'
      have hm := scanFreq_le_next L n k
      omega
    · have hcur : (runAt L n).next = k := by
        have ht := runStep_done_prev L n (runAt L n) ha
        change (runStep L n (runAt L n)).1.prev = (k : Int) at hp
        rw [ht] at hp
        omega
      by_cases hsame : ((runAt L n).next : Int) = (runAt L n).prev
      · have hb := ih (by rw [← hsame, hcur])
        have hm := scanFreq_le_next L n k
        omega
      · have hf : 0 < runFreq (some ((runAt L n).next, (runAt L n).prev, (runAt L n).cnt + 1, (runAt L n).mn)) k := by
          simp only [runFreq]
          by_cases hs : (runAt L n).cnt + 1 < (runAt L n).mn
          · simp only [ite_eq_left hs, ite_eq_left (show k = (runAt L n).next by omega)]
            omega
          · simp only [ite_eq_right hs, ite_eq_left (show (runAt L n).next ≠ 0 by omega),
              ite_eq_left (show ((runAt L n).next : Int) ≠ (runAt L n).prev ∧ k = (runAt L n).next from ⟨hsame, by omega⟩)]
            omega
        simp only [scanFreqUpTo, runStep, ite_eq_right ha]
        change 0 < scanFreqUpTo L n k + runFreq (some ((runAt L n).next, (runAt L n).prev, (runAt L n).cnt + 1, (runAt L n).mn)) k
        omega

/-- Finishing a positive run gives positive accumulated frequency even if
the current run itself uses only a repetition code. -/
theorem scanFreq_finished_positive (L : Nat → Nat) (n k : Nat) (hk : 0 < k)
    (hc : (runAt L n).next = k)
    (ha : ¬ ((runAt L n).cnt + 1 < (runAt L n).mx ∧ (runAt L n).next = L (n + 1))) :
    0 < scanFreqUpTo L (n + 1) k := by
  by_cases hp : ((runAt L n).next : Int) = (runAt L n).prev
  · have hprev : (runAt L n).prev = (k : Int) := by rw [← hp, hc]
    have hb := scanFreq_prev_positive L n k hk hprev
    have hm := scanFreq_le_next L n k
    omega
  · have hf : 0 < runFreq (some ((runAt L n).next, (runAt L n).prev, (runAt L n).cnt + 1, (runAt L n).mn)) k := by
      simp only [runFreq]
      by_cases hs : (runAt L n).cnt + 1 < (runAt L n).mn
      · simp only [ite_eq_left hs, ite_eq_left (show k = (runAt L n).next by omega)]
        omega
      · simp only [ite_eq_right hs, ite_eq_left (show (runAt L n).next ≠ 0 by omega),
          ite_eq_left (show ((runAt L n).next : Int) ≠ (runAt L n).prev ∧ k = (runAt L n).next from ⟨hp, by omega⟩)]
        omega
    simp only [scanFreqUpTo, runStep, ite_eq_right ha]
    omega

/-- A positive length that was read is either already represented by an
ordinary length code, or is still in the unfinished current run. -/
theorem scanFreq_seen_positive (L : Nat → Nat) (n v k : Nat) (hv : v < n)
    (hk : 0 < k) (hvk : L v = k) :
    0 < scanFreqUpTo L n k ∨ ((runAt L n).next = k ∧ 0 < (runAt L n).cnt) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hcur : (runAt L n).next = L n := runAt_next L n
    by_cases ha : (runAt L n).cnt + 1 < (runAt L n).mx ∧ (runAt L n).next = L (n + 1)
    · have hnext : (runAt L (n + 1)).next = (runAt L n).next := by
        simp only [runAt, runStep, ite_eq_left ha]
        exact ha.2.symm
      have hcnt : 0 < (runAt L (n + 1)).cnt := by
        simp only [runAt, runStep, ite_eq_left ha]
        omega
      by_cases hvn : v = n
      · right
        rw [hvn] at hvk
        exact ⟨hnext.trans (hcur.trans hvk), hcnt⟩
      · rcases ih (by omega) with hp | ⟨hn, hc⟩
        · left
          have hm := scanFreq_le_next L n k
          omega
        · exact Or.inr ⟨hnext.trans hn, hcnt⟩
    · by_cases hvn : v = n
      · left
        rw [hvn] at hvk
        exact scanFreq_finished_positive L n k hk (hcur.trans hvk) ha
      · rcases ih (by omega) with hp | ⟨hn, hc⟩
        · left
          have hm := scanFreq_le_next L n k
          omega
        · exact Or.inl (scanFreq_finished_positive L n k hk hn ha)

/-- Once the last pending run is finished, every positive source length
already has positive ordinary-symbol frequency. -/
theorem scanFreq_seen_done (L : Nat → Nat) (n v k : Nat) (hv : v < n)
    (hk : 0 < k) (hvk : L v = k) (hdone : (runAt L n).cnt = 0) :
    0 < scanFreqUpTo L n k := by
  rcases scanFreq_seen_positive L n v k hv hk hvk with hf | ⟨hnext, hc⟩
  · exact hf
  · omega

end Zlib.Trees.Proofs.Out
