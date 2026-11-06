import ZlibF.Math.DeflateRunSupport
import ZlibF.Proof.«inffast.c.sig»

/-! # Run-length output and the independent code-length grammar

The pending-run invariant follows the construction in zlib-formal's
`EmitDecodeDyn`. The decoding argument here targets the independent
inductive `CodeLens` relation, including its bounds and previous-length rule.
-/

namespace Zlib.Trees.Proofs.Out
open ZlibF.Spec

/-- The first `m` lengths. -/
def lens (L : Nat → Nat) (m : Nat) : List Nat := (List.range m).map L

theorem lens_length (L : Nat → Nat) (m : Nat) : (lens L m).length = m := by simp [lens]

theorem lens_succ (L : Nat → Nat) (m : Nat) : lens L (m + 1) = lens L m ++ [L m] := by
  simp [lens, List.range_succ]

theorem lens_add_rep (L : Nat → Nat) (m k v : Nat) (h : ∀ j, m ≤ j → j < m + k → L j = v) :
    lens L (m + k) = lens L m ++ List.replicate k v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, lens_succ, ih (fun j h1 h2 => h j h1 (by omega)), h (m + k) (by omega) (by omega),
      List.replicate_succ', List.append_assoc]

theorem lens_congr (L L' : Nat → Nat) (m : Nat) (h : ∀ j, j < m → L j = L' j) : lens L m = lens L' m := by
  unfold lens; apply List.map_congr_left; intro j hj; exact h j (List.mem_range.mp hj)

theorem getLastD_append_lens (A : List Nat) (L : Nat → Nat) (m : Nat) (hm : 0 < m) :
    (A ++ lens L m).getLastD 0 = L (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [lens_succ, ← List.append_assoc]
  simp

/-- Invariant of the `scan_tree`/`send_tree` state before iteration `n`: `nextlen`
is `L n`; the pending run is the `count` copies of `L n` just before `n`;
`prevlen` is the length before the pending run (or `-1` at the start); and
`max_count`/`min_count` are the ones zlib chose for a run of `L n` after `prevlen`. -/
def RunDInv (L : Nat → Nat) (n : Nat) (s : RunSt) : Prop :=
  s.next = L n ∧ s.cnt ≤ n ∧ (∀ j, n - s.cnt ≤ j → j < n → L j = L n) ∧
  (n - s.cnt = 0 → s.prev = -1) ∧ (0 < n - s.cnt → s.prev = ((L (n - s.cnt - 1) : Nat) : Int)) ∧
  (L n = 0 → s.mx = 138 ∧ s.mn = 3) ∧
  (L n ≠ 0 → s.prev = ((L n : Nat) : Int) → s.mx = 6 ∧ s.mn = 3) ∧
  (L n ≠ 0 → s.prev ≠ ((L n : Nat) : Int) → s.mx = 7 ∧ s.mn = 4) ∧
  s.cnt < s.mx

theorem runDInv_init (L : Nat → Nat) : RunDInv L 0 (runInit L) := by
  unfold runInit
  by_cases h : L 0 = 0
  · rw [ite_eq_left h]; unfold RunDInv; dsimp only
    refine ⟨rfl, Nat.le_refl _, fun j _ h2 => absurd h2 (by omega), fun _ => rfl,
      fun e => absurd e (by omega), fun _ => ⟨rfl, rfl⟩, fun e => absurd h e, fun e => absurd h e, by decide +kernel⟩
  · rw [ite_eq_right h]; unfold RunDInv; dsimp only
    refine ⟨rfl, Nat.le_refl _, fun j _ h2 => absurd h2 (by omega), fun _ => rfl,
      fun e => absurd e (by omega), fun e => absurd e h, fun _ e => absurd e (by omega),
      fun _ _ => ⟨rfl, rfl⟩, by decide +kernel⟩

theorem runDInv_step (L : Nat → Nat) (n : Nat) (s : RunSt) (hI : RunDInv L n s) :
    RunDInv L (n + 1) (runStep L n s).1 := by
  obtain ⟨hn, hc, hp, hp0, hp1, h0, h6, h7, hmx⟩ := hI
  unfold runStep
  dsimp only
  by_cases hcond : s.cnt + 1 < s.mx ∧ s.next = L (n + 1)
  · rw [ite_eq_left hcond]
    obtain ⟨hlt, heq⟩ := hcond
    rw [hn] at heq
    unfold RunDInv; dsimp only
    refine ⟨rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, hlt⟩
    · intro j h1 h2
      by_cases e : j = n
      · subst e; exact heq
      · rw [hp j (by omega) (by omega), heq]
    · intro e; exact hp0 (by omega)
    · intro e; rw [hp1 (by omega)]; congr 2; omega
    · intro e; rw [← heq] at e; exact h0 e
    · intro e1 e2; rw [← heq] at e1 e2; exact h6 e1 e2
    · intro e1 e2; rw [← heq] at e1 e2; exact h7 e1 e2
  · rw [ite_eq_right hcond, hn]
    have hpr : 0 < n + 1 - 0 → ((L n : Nat) : Int) = ((L (n + 1 - 0 - 1) : Nat) : Int) := by
      intro _; rw [show n + 1 - 0 - 1 = n by omega]
    by_cases hz : L (n + 1) = 0
    · rw [ite_eq_left hz]; unfold RunDInv; dsimp only
      refine ⟨rfl, by omega, fun j h1 h2 => absurd h2 (by omega), fun e => absurd e (by omega), hpr,
        fun _ => ⟨rfl, rfl⟩, fun e => absurd hz e, fun e => absurd hz e, by decide +kernel⟩
    · rw [ite_eq_right hz]
      by_cases he : L n = L (n + 1)
      · rw [ite_eq_left he]; unfold RunDInv; dsimp only
        refine ⟨rfl, by omega, fun j h1 h2 => absurd h2 (by omega), fun e => absurd e (by omega), hpr,
          fun e => absurd e hz, fun _ _ => ⟨rfl, rfl⟩, fun _ e => absurd (by rw [he]) e, by decide +kernel⟩
      · rw [ite_eq_right he]; unfold RunDInv; dsimp only
        refine ⟨rfl, by omega, fun j h1 h2 => absurd h2 (by omega), fun e => absurd e (by omega), hpr,
          fun e => absurd e hz, fun _ e => absurd (by omega) he, fun _ _ => ⟨rfl, rfl⟩, by decide +kernel⟩

theorem runDInv_at (L : Nat → Nat) : ∀ n, RunDInv L n (runAt L n) := by
  intro n
  induction n with
  | zero => exact runDInv_init L
  | succ n ih => exact runDInv_step L n _ ih

theorem runAt_succ (L : Nat → Nat) (n : Nat) : runAt L (n + 1) = (runStep L n (runAt L n)).1 := rfl


/-- Reuse the independent bit-reader theorem for the writer's low-bit list. -/
theorem readBits_natBits (n v : Nat) (r : List Bool) (h : v < 2 ^ n) :
    readBits n (natBits v n ++ r) = some (v, r) := by
  have ht := Zlib.Inffast.Proofs.readBits_bitsOfNat n n v r (Nat.le_refl _)
  simpa [Nat.mod_eq_of_lt h, Zlib.Inffast.Proofs.bitsOfNat, natBits] using ht

/-- Repeating an ordinary length code constructs the independent grammar,
with any valid continuation and exact suffix. -/
theorem codeLens_repeat {cl : List Nat} {total : Nat} {cw : List Bool} {sym : Nat}
    (hd : ∀ r, decodeSym cl (cw ++ r) = some (sym, r)) (hs : sym < 16) :
    ∀ (k : Nat) (A : List Nat) (Z rest : List Bool) (out : List Nat), A.length + k ≤ total →
      CodeLens cl total (A ++ List.replicate k sym) Z rest out →
      CodeLens cl total A ((List.replicate k cw).flatten ++ Z) rest out := by
  intro k
  induction k with
  | zero => intro A Z rest out _ hc; simpa using hc
  | succ k ih =>
    intro A Z rest out hk hc
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
    refine CodeLens.len (by omega) (hd _) hs ?_
    apply ih (A ++ [sym]) Z rest out (by simp; omega)
    simpa only [List.append_assoc, List.singleton_append, ← List.replicate_succ] using hc

set_option maxHeartbeats 1000000 in
/-- One actual run-model step constructs the independent grammar before
any valid continuation. Only symbols used by this step need decode data. -/
theorem run_step_codeLens {L : Nat → Nat} {blt : Nat → UInt16 × UInt16}
    {cl : List Nat} {total : Nat} {A : List Nat} {n : Nat}
    (Z rest : List Bool) (out : List Nat)
    (hLn : L n ≤ 15) (hlen : A.length + n + 1 ≤ total)
    (hT : ∀ k r, k < 19 → 0 < runFreq (runStep L n (runAt L n)).2 k →
      decodeSym cl (codeBits blt k ++ r) = some (k, r))
    (hcont : CodeLens cl total (A ++ lens L (n + 1 - (runAt L (n + 1)).cnt)) Z rest out) :
    CodeLens cl total (A ++ lens L (n - (runAt L n).cnt))
      (runBits blt (runStep L n (runAt L n)).2 ++ Z) rest out := by
  have hI := runDInv_at L n
  rw [runAt_succ] at hcont
  generalize runAt L n = s at hI hT hcont ⊢
  obtain ⟨hn, hc, hp, hp0, hp1, h0, h6, h7, hmx⟩ := hI
  unfold runStep at hT hcont ⊢
  dsimp only at hT hcont ⊢
  by_cases hcond : s.cnt + 1 < s.mx ∧ s.next = L (n + 1)
  · rw [ite_eq_left hcond] at hcont ⊢
    simpa only [runBits, List.nil_append,
      show n + 1 - (s.cnt + 1) = n - s.cnt by omega] using hcont
  · rw [ite_eq_right hcond] at hT hcont ⊢
    dsimp only at hT hcont ⊢
    have hlens : lens L (n + 1) = lens L (n - s.cnt) ++ List.replicate (s.cnt + 1) (L n) := by
      rw [← lens_add_rep L (n - s.cnt) (s.cnt + 1) (L n) (fun j h1 h2 => by
        by_cases e : j = n
        · rw [e]
        · exact hp j h1 (by omega))]
      congr 1; omega
    rw [show (n + 1 - (if L (n + 1) = 0 then (⟨s.next, L (n + 1), 0, 138, 3⟩ : RunSt)
        else if s.next = L (n + 1) then ⟨s.next, L (n + 1), 0, 6, 3⟩ else ⟨s.next, L (n + 1), 0, 7, 4⟩).cnt)
        = n + 1 by split <;> (try split) <;> rfl] at hcont
    rw [hlens, ← List.append_assoc] at hcont
    rw [hn] at hT ⊢
    have hfreq : ∀ k, 0 < runFreq (some (L n, s.prev, s.cnt + 1, s.mn)) k → k < 19 →
        ∀ r, decodeSym cl (codeBits blt k ++ r) = some (k, r) :=
      fun k hk h19 r => hT k r h19 hk
    generalize hB : A ++ lens L (n - s.cnt) = B at hcont ⊢
    have hBl : B.length = A.length + (n - s.cnt) := by rw [← hB]; simp [lens_length]
    simp only [runBits]
    by_cases hmn : s.cnt + 1 < s.mn
    · simp only [ite_eq_left hmn]
      have hd := hfreq (L n) (by simp [runFreq, hmn]) (by omega)
      exact codeLens_repeat hd (by omega) _ _ _ _ _ (by omega) hcont
    · simp only [ite_eq_right hmn]
      by_cases hz : L n = 0
      · obtain ⟨hm1, hm2⟩ := h0 hz
        simp only [hz, ne_eq, not_true_eq_false, ite_false]
        rw [hz] at hcont
        by_cases h10 : s.cnt + 1 ≤ 10
        · simp only [ite_eq_left h10, List.append_assoc]
          have hd := hfreq 17 (by simp [runFreq, hmn, hz, h10]) (by omega)
          refine CodeLens.rep17 (by omega) (hd _) (readBits_natBits 3 _ _ (by omega)) (by omega) ?_
          simpa only [show 3 + (s.cnt + 1 - 3) = s.cnt + 1 by omega] using hcont
        · simp only [ite_eq_right h10, List.append_assoc]
          have hd := hfreq 18 (by simp [runFreq, hmn, hz, h10]) (by omega)
          refine CodeLens.rep18 (by omega) (hd _) (readBits_natBits 7 _ _ (by omega)) (by omega) ?_
          simpa only [show 11 + (s.cnt + 1 - 11) = s.cnt + 1 by omega] using hcont
      · simp only [hz, ne_eq, not_false_eq_true, ite_true]
        by_cases hpv : ((L n : Nat) : Int) ≠ s.prev
        · obtain ⟨hm1, hm2⟩ := h7 hz (fun e => hpv e.symm)
          rw [ite_eq_left hpv]
          have hd1 := hfreq (L n) (by simp [runFreq, hmn, hz, hpv]; omega) (by omega)
          have hd2 := hfreq 16 (by simp [runFreq, hmn, hz, hpv]) (by omega)
          rw [List.append_assoc, List.append_assoc]
          refine CodeLens.len (by omega) (hd1 _) (by omega) ?_
          refine CodeLens.rep16 (by simp; omega) (hd2 _) (by simp)
            (readBits_natBits 2 _ _ (by omega)) (by simp; omega) ?_
          have hgl : (B ++ [L n]).getLastD 0 = L n := by simp
          simpa only [hgl, List.append_assoc,
            List.singleton_append, ← List.replicate_succ,
            show 3 + (s.cnt + 1 - 1 - 3) + 1 = s.cnt + 1 by omega] using hcont
        · have hpe : s.prev = ((L n : Nat) : Int) := by omega
          obtain ⟨hm1, hm2⟩ := h6 hz hpe
          rw [ite_eq_right hpv]
          have hd2 := hfreq 16 (by simp [runFreq, hmn, hz, hpv]) (by omega)
          have hpos : 0 < n - s.cnt := by
            rcases Nat.eq_zero_or_pos (n - s.cnt) with e | e
            · have := hp0 e; rw [this] at hpe; omega
            · exact e
          have hlast : B.getLastD 0 = L n := by
            rw [← hB, getLastD_append_lens _ _ _ hpos]
            have := hp1 hpos
            omega
          have hBne : B ≠ [] := by intro e; rw [e] at hBl; simp at hBl; omega
          rw [List.append_assoc]
          refine CodeLens.rep16 (by omega) (hd2 _) hBne (readBits_natBits 2 _ _ (by omega)) (by omega) ?_
          simpa only [hlast, show 3 + (s.cnt + 1 - 3) = s.cnt + 1 by omega] using hcont

/-- A later scan includes every earlier finished run. -/
theorem scanFreqUpTo_mono (L : Nat → Nat) (k : Nat) {i j : Nat} (hij : i ≤ j) :
    scanFreqUpTo L i k ≤ scanFreqUpTo L j k := by
  induction j with
  | zero => have hi : i = 0 := by omega
            subst i
            exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i
      exact Nat.le_refl _
    · have hp := ih (by omega)
      have hn := scanFreq_le_next L j k
      omega

/-- Every prefix of the writer constructs the grammar for its completed
runs. The pending run remains outside the already decoded prefix. -/
theorem treeBitsUpTo_codeLens {L : Nat → Nat} {blt : Nat → UInt16 × UInt16}
    {cl : List Nat} {total maxc : Nat} {A : List Nat}
    (hL : ∀ i, i ≤ maxc → L i ≤ 15) (hlen : A.length + maxc + 1 ≤ total)
    (hT : ∀ k r, k < 19 → 0 < scanFreqUpTo L (maxc + 1) k →
      decodeSym cl (codeBits blt k ++ r) = some (k, r)) :
    ∀ n, n ≤ maxc + 1 → ∀ (Z rest : List Bool) (out : List Nat),
      CodeLens cl total (A ++ lens L (n - (runAt L n).cnt)) Z rest out →
      CodeLens cl total A (treeBitsUpTo blt L n ++ Z) rest out := by
  intro n
  induction n with
  | zero => intro _ Z rest out hc; simpa [treeBitsUpTo, lens] using hc
  | succ n ih =>
    intro hn Z rest out hc
    simp only [treeBitsUpTo, List.append_assoc]
    apply ih (by omega)
    refine run_step_codeLens Z rest out (hL n (by omega)) (by omega) ?_ hc
    intro k r h19 hk
    apply hT k r h19
    have hm := scanFreqUpTo_mono L k (i := n + 1) (j := maxc + 1) hn
    change scanFreqUpTo L n k + runFreq (runStep L n (runAt L n)).2 k ≤ _ at hm
    omega

/-- A distinct terminal guard finishes the pending run. The complete
writer's bits satisfy the independent format grammar on any continuation. -/
theorem sendTree_codeLens {L : Nat → Nat} {blt : Nat → UInt16 × UInt16}
    {cl : List Nat} {total maxc : Nat} {A : List Nat} (Z rest : List Bool) (out : List Nat)
    (hL : ∀ i, i ≤ maxc → L i ≤ 15) (hg : 15 < L (maxc + 1))
    (hlen : A.length + maxc + 1 ≤ total)
    (hT : ∀ k r, k < 19 → 0 < scanFreqUpTo L (maxc + 1) k →
      decodeSym cl (codeBits blt k ++ r) = some (k, r))
    (hc : CodeLens cl total (A ++ lens L (maxc + 1)) Z rest out) :
    CodeLens cl total A (sendTreeBits blt L maxc ++ Z) rest out := by
  have h0 : (runAt L (maxc + 1)).cnt = 0 := by
    rw [runAt_succ]
    have hI := runDInv_at L maxc
    generalize runAt L maxc = s at hI ⊢
    unfold runStep
    dsimp only
    rw [ite_eq_right]
    · split <;> (try split) <;> rfl
    · intro ⟨_, e⟩
      rw [hI.1] at e
      have := hL maxc (Nat.le_refl _)
      omega
  apply treeBitsUpTo_codeLens hL hlen hT (maxc + 1) (Nat.le_refl _) Z rest out
  simpa only [h0, Nat.sub_zero] using hc

/-- The two independently started source-tree writers compose into one
code-length sequence. A leading repeat can never borrow a previous tree's
last length: each writer's own initial state establishes its first length. -/
theorem twoTrees_codeLens {L D : Nat → Nat} {blt : Nat → UInt16 × UInt16}
    {cl : List Nat} (lc dc : Nat) (suffix : List Bool)
    (hlc : 0 < lc) (hdc : 0 < dc)
    (hL : ∀ i < lc, L i ≤ 15) (hD : ∀ i < dc, D i ≤ 15)
    (hgL : 15 < L lc) (hgD : 15 < D dc)
    (hT : ∀ k r, k < 19 → 0 < scanFreqUpTo L lc k + scanFreqUpTo D dc k →
      decodeSym cl (codeBits blt k ++ r) = some (k, r)) :
    CodeLens cl (lc + dc) []
      (sendTreeBits blt L (lc - 1) ++ sendTreeBits blt D (dc - 1) ++ suffix)
      suffix (lens L lc ++ lens D dc) := by
  have hl : lc - 1 + 1 = lc := by omega
  have hd : dc - 1 + 1 = dc := by omega
  rw [List.append_assoc]
  apply sendTree_codeLens (A := []) (maxc := lc - 1) (sendTreeBits blt D (dc - 1) ++ suffix) suffix
    (lens L lc ++ lens D dc) (fun i hi => hL i (by omega)) (by simpa only [hl] using hgL)
    (by simp; omega) (fun k r hk hp => hT k r hk (by rw [hl] at hp; omega))
  simp only [hl, List.nil_append]
  apply sendTree_codeLens (maxc := dc - 1) suffix suffix (lens L lc ++ lens D dc)
    (fun i hi => hD i (by omega)) (by simpa only [hd] using hgD)
    (by rw [lens_length]; omega) (fun k r hk hp => hT k r hk (by rw [hd] at hp; omega))
  rw [hd]
  exact CodeLens.done (by simp only [List.length_append, lens_length])

end Zlib.Trees.Proofs.Out
