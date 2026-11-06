import ZlibF.Proof.«deflate.c.engine.lmcond»
import ZlibF.Proof.«deflate.c.engine.loops»

/-!
# deflate.c, engine: the inner comparison loop of `longest_match`

`do { } while (*++scan == *++match && ... && scan < strend);` starting at offset 2 (the first two bytes and, by the
hash, the third are known equal). The loop does not fault inside the window, leaves the heap alone, and stops with
`scan` at offset `r = firstMis w S C 3` from `S`, and `match` at offset `r` from `C`.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

theorem M_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  funext h
  simp only [bind_app]
  cases m h with
  | error e => rfl
  | ok p => rfl

theorem M_pure_bind {α β : Type} (a : α) (f : α → M β) : (pure a >>= f) = f a := rfl

theorem M_ite_bind {α β : Type} (c : Prop) [Decidable c] (a b : M α) (f : α → M β) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem lm_cond_eq (strend scan m : BPtr) : lm_cond strend scan m = lmCondR strend 8 scan m := by
  unfold lm_cond
  simp [List.range', List.forIn'_cons, List.forIn'_nil, lmCondR, M_bind_assoc, M_pure_bind, M_ite_bind]

/-- **The inner loop.** In a byte block `wa` with `S + 258 < wa.size` and `C <= S`, where the strings at `S` and `C`
agree on the first three bytes, the loop started at offsets 2 does not fault, leaves the heap as it is, and ends with
`scan = S + r`, `match = C + r`, `r = matchLen` (the first position from 3 on where they differ, or 258). -/
theorem lm_inner_loop {h : Heap} {wb : Nat} {wa : Array UInt8} (hw : h.bytes wb = some wa) (S C : Nat)
    (hS : S + 258 < wa.size) (hCS : C ≤ S)
    (h0 : bfn wa S = bfn wa C) (h1 : bfn wa (S + 1) = bfn wa (C + 1)) (h2 : bfn wa (S + 2) = bfn wa (C + 2)) :
    cdoWhile (fun x => (pure x : M (BPtr × BPtr)))
      (fun (scan, m) => do
        let (c, scan, m) ← lm_cond (Ptr.ref (BRef.blk wb) (S + 258)) scan m
        pure (c, (scan, m)))
      (Ptr.ref (BRef.blk wb) (S + 2), Ptr.ref (BRef.blk wb) (C + 2)) h =
    .ok ((Ptr.ref (BRef.blk wb) (S + matchLen (bfn wa) S C), Ptr.ref (BRef.blk wb) (C + matchLen (bfn wa) S C)), h) := by
  let Inv : BPtr × BPtr → Heap → Prop := fun s h' =>
    h' = h ∧ ∃ j, j % 8 = 2 ∧ 2 ≤ j ∧ j ≤ 250 ∧ s = (Ptr.ref (BRef.blk wb) (S + j), Ptr.ref (BRef.blk wb) (C + j)) ∧
      ∀ k, 3 ≤ k → k ≤ j → bfn wa (S + k) = bfn wa (C + k)
  let Q : BPtr × BPtr → Heap → Prop := fun s h' =>
    h' = h ∧ s = (Ptr.ref (BRef.blk wb) (S + matchLen (bfn wa) S C), Ptr.ref (BRef.blk wb) (C + matchLen (bfn wa) S C))
  let μ : BPtr × BPtr → Nat := fun s => match s.1 with | .null => 0 | .ref _ o => 258 - (o - S)
  have key := cdoWhile_measure (σ := BPtr × BPtr)
    (body := fun x => (pure x : M (BPtr × BPtr)))
    (cond := fun (scan, m) => do
        let (c, scan, m) ← lm_cond (Ptr.ref (BRef.blk wb) (S + 258)) scan m
        pure (c, (scan, m)))
    Inv μ Q ?_ (s := (Ptr.ref (BRef.blk wb) (S + 2), Ptr.ref (BRef.blk wb) (C + 2))) (h := h)
    ⟨rfl, 2, by omega, by omega, by omega, rfl, fun k hk1 hk2 => by omega⟩ (by unfold fuel; simp only [μ]; omega)
  · obtain ⟨s', h', hrun, hq, hs⟩ := key
    rw [hrun, hq, hs]
  · intro s h' hI
    obtain ⟨hh', j, hj8, hj2, hj250, hs, hag⟩ := hI
    have hh2 := hh'.symm
    subst hh2
    subst hs
    have hrun := lmCondR_ok hw S C hS hCS 8 j (by omega)
    cases hcs : cmpSteps (bfn wa) S C 8 j with
    | some k =>
      obtain ⟨hk1, hk2, hk3, hk4⟩ := cmpSteps_some 8 j k hcs
      refine ⟨_, h, false, (Ptr.ref (BRef.blk wb) (S + k), Ptr.ref (BRef.blk wb) (C + k)), h, rfl, ?_, ?_, ?_⟩
      · simp only [bind_app, lm_cond_eq, hrun, hcs]
        try rfl
      · intro _
        have : matchLen (bfn wa) S C = k := by
          unfold matchLen
          apply firstMis_unique (bfn wa) S C (by omega) (by omega)
          · intro q hq1 hq2
            by_cases hqj : q ≤ j
            · exact hag q hq1 hqj
            · exact hk4 q (by omega) hq2
          · intro _; exact hk3
        refine ⟨rfl, ?_⟩
        rw [this]
      · intro hc; simp at hc
    | none =>
      have hn := cmpSteps_none 8 j hcs
      by_cases hlt : S + (j + 8) < S + 258
      · refine ⟨_, h, true, (Ptr.ref (BRef.blk wb) (S + (j + 8)), Ptr.ref (BRef.blk wb) (C + (j + 8))), h, rfl, ?_, ?_, ?_⟩
        · simp [bind_app, lm_cond_eq, hrun, hcs, hlt]
        · intro hc; simp at hc
        · intro _
          refine ⟨⟨rfl, j + 8, by omega, by omega, by omega, rfl, ?_⟩, ?_⟩
          · intro k hk1 hk2
            by_cases hkj : k ≤ j
            · exact hag k hk1 hkj
            · exact hn k (by omega) (by omega)
          · simp only [μ]; omega
      · refine ⟨_, h, false, (Ptr.ref (BRef.blk wb) (S + (j + 8)), Ptr.ref (BRef.blk wb) (C + (j + 8))), h, rfl, ?_, ?_, ?_⟩
        · simp [bind_app, lm_cond_eq, hrun, hcs, hlt]
        · intro _
          have : matchLen (bfn wa) S C = 258 := by
            unfold matchLen
            apply firstMis_unique (bfn wa) S C (by omega) (by omega)
            · intro q hq1 hq2
              by_cases hqj : q ≤ j
              · exact hag q hq1 hqj
              · exact hn q (by omega) (by omega)
            · intro h258; omega
          refine ⟨rfl, ?_⟩
          rw [this]
          have e : j + 8 = 258 := by omega
          rw [e]
        · intro hc; simp at hc

end Zlib.Deflate.Engine.Proofs
