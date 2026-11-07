import ZlibF.Math.DeflateTreeScan

/-! # Fresh dummy leaves for the two-leaf repair in `build_tree` -/

namespace Zlib.Trees.Math

def forceNode (m : Int) : Nat := if m < 2 then (m + 1).toNat else 0

def forceMax (m : Int) : Int := if m < 2 then m + 1 else m

def forceFreq (fr : Nat → UInt16) (m : Int) (v : Nat) : UInt16 :=
  if v = forceNode m then 1 else fr v

theorem scanCount_pos (fr : Nat → UInt16) (N a : Nat) (ha : a < N) (hf : fr a ≠ 0) :
    1 ≤ scanCount fr N := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [scanCount]
    by_cases heq : a = N
    · subst a; rw [ite_eq_left hf]; omega
    · have h := ih (by omega); split <;> omega

theorem scanCount_two (fr : Nat → UInt16) (N a b : Nat)
    (ha : a < N) (hb : b < N) (hab : a ≠ b) (hfa : fr a ≠ 0) (hfb : fr b ≠ 0) :
    2 ≤ scanCount fr N := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [scanCount]
    by_cases hea : a = N
    · subst a
      have h := scanCount_pos fr N b (by omega) hfb
      rw [ite_eq_left hfa]; omega
    · by_cases heb : b = N
      · subst b
        have h := scanCount_pos fr N a (by omega) hfa
        rw [ite_eq_left hfb]; omega
      · have h := ih (by omega) (by omega)
        split <;> omega

theorem scanCount_congr (fr gr : Nat → UInt16) (N : Nat) (h : ∀ v < N, fr v = gr v) :
    scanCount fr N = scanCount gr N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [scanCount, ih (by intro v hv; exact h v (by omega)), h N (by omega)]

theorem scanMax_congr (fr gr : Nat → UInt16) (N : Nat) (h : ∀ v < N, fr v = gr v) :
    scanMax fr N = scanMax gr N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [scanMax, ih (by intro v hv; exact h v (by omega)), h N (by omega)]

theorem scanMax_eq (fr : Nat → UInt16) (N a : Nat) (ha : a < N) (hf : fr a ≠ 0)
    (hz : ∀ v, a < v → v < N → fr v = 0) : scanMax fr N = a := by
  rcases scanMax_spec fr N with ⟨hm, hzero⟩ | ⟨u, hm, hu, hfu, hzero⟩
  · exact False.elim (hf (hzero a ha))
  · have heq : u = a := by
      by_cases hlt : u < a
      · exact False.elim (hf (hzero a hlt ha))
      · by_cases hgt : a < u
        · exact False.elim (hfu (hz u hgt hu))
        · omega
    simpa only [heq] using hm

/-- With at most one used leaf, zlib chooses a fresh leaf inside the actual
alphabet. An alphabet of at least three symbols includes the `max_code = 1`
case, where the chosen leaf is symbol 2. -/
theorem forceNode_fresh (fr : Nat → UInt16) (N : Nat) (hN : 3 ≤ N)
    (hc : scanCount fr N ≤ 1) :
    forceNode (scanMax fr N) < N ∧ fr (forceNode (scanMax fr N)) = 0 := by
  rcases scanMax_spec fr N with ⟨hm, hz⟩ | ⟨u, hm, hu, hf, hz⟩
  · rw [hm]
    have heq : forceNode (-1) = 0 := rfl
    rw [heq]
    exact ⟨by omega, hz 0 (by omega)⟩
  · rw [hm]
    by_cases hsmall : (u : Int) < 2
    · have hnode : forceNode (u : Int) = u + 1 := by simp only [forceNode, ite_eq_left hsmall]; omega
      rw [hnode]
      exact ⟨by omega, hz (u + 1) (by omega) (by omega)⟩
    · have hnode : forceNode (u : Int) = 0 := by simp only [forceNode, ite_eq_right hsmall]
      rw [hnode]
      refine ⟨by omega, ?_⟩
      apply Classical.byContradiction
      intro hzero
      have htwo := scanCount_two fr N 0 u (by omega) hu (by omega) hzero hf
      omega

theorem scanCount_set_one (fr : Nat → UInt16) (N node : Nat) (hn : node < N) (hz : fr node = 0) :
    scanCount (fun v => if v = node then 1 else fr v) N = scanCount fr N + 1 := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases heq : node = N
    · subst node
      have hpre : scanCount (fun v => if v = N then 1 else fr v) N = scanCount fr N :=
        scanCount_congr (fun v => if v = N then 1 else fr v) fr N (by intro v hv; rw [ite_eq_right (by omega)])
      simp [scanCount, hpre, hz]
    · have hpre := ih (by omega)
      simp only [scanCount, hpre, ite_eq_right (Ne.symm heq)]
      split <;> omega

theorem scanCount_force (fr : Nat → UInt16) (N : Nat) (hN : 3 ≤ N) (hc : scanCount fr N ≤ 1) :
    scanCount (forceFreq fr (scanMax fr N)) N = scanCount fr N + 1 := by
  obtain ⟨hn, hz⟩ := forceNode_fresh fr N hN hc
  exact scanCount_set_one fr N _ hn hz

/-- The control variable updated by zlib remains the exact maximum after
adding the fresh leaf. -/
theorem scanMax_force (fr : Nat → UInt16) (N : Nat) (hN : 3 ≤ N) (hc : scanCount fr N ≤ 1) :
    scanMax (forceFreq fr (scanMax fr N)) N = forceMax (scanMax fr N) := by
  obtain ⟨hn, hz⟩ := forceNode_fresh fr N hN hc
  rcases scanMax_spec fr N with ⟨hm, hzero⟩ | ⟨u, hm, hu, hfu, hzero⟩
  · rw [hm]
    change scanMax (fun v => if v = 0 then 1 else fr v) N = 0
    exact scanMax_eq _ N 0 (by omega) (by simp) (by
      intro v hv hvN; rw [ite_eq_right (by omega)]; exact hzero v hvN)
  · rw [hm]
    by_cases hsmall : (u : Int) < 2
    · have hnode : forceNode (u : Int) = u + 1 := by simp only [forceNode, ite_eq_left hsmall]; omega
      simp only [forceMax, ite_eq_left hsmall]
      have heq := scanMax_eq (forceFreq fr u) N (u + 1) (by omega)
        (by simp [forceFreq, hnode]) (by
          intro v hv hvN
          rw [show forceFreq fr u v = fr v by simp [forceFreq, hnode, show v ≠ u + 1 by omega]]
          exact hzero v (by omega) hvN)
      simpa using heq
    · have hnode : forceNode (u : Int) = 0 := by simp only [forceNode, ite_eq_right hsmall]
      simp only [forceMax, ite_eq_right hsmall]
      exact scanMax_eq (forceFreq fr u) N u hu
        (by simpa only [forceFreq, hnode, ite_eq_right (show u ≠ 0 by omega)] using hfu) (by
          intro v hv hvN
          rw [show forceFreq fr u v = fr v by simp [forceFreq, hnode, show v ≠ 0 by omega]]
          exact hzero v hv hvN)

end Zlib.Trees.Math
