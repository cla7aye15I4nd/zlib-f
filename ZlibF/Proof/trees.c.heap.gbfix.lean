import ZlibF.Proof.«trees.c.heap.gbp1»

/-!
# trees.c: `gen_bitlen`, the repair of over-long codes

`do { bits = max_length-1; while (bl_count[bits] == 0) bits--; bl_count[bits]--; bl_count[bits+1] += 2;
bl_count[max_length]--; overflow -= 2; } while (overflow > 0);` on the counts `c b = bl_count[b]`.
`fixStep` is one round; the pure part is copied from the earlier attempt (`GenBitlenFixX.lean`).
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB

/-- Point update of a count function. -/
def updN (f : Nat → Nat) (a v : Nat) : Nat → Nat := fun x => if x = a then v else f x

/-- The deepest `b' ≤ b` with `c b' ≠ 0` (`0` if there is none). -/
def deepestX (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => if c (b + 1) ≠ 0 then b + 1 else deepestX c b

theorem deepestX_eq (c : Nat → Nat) : ∀ b b', 1 ≤ b' → b' ≤ b → c b' ≠ 0 → (∀ y, b' < y → y ≤ b → c y = 0) →
    deepestX c b = b'
  | 0, b', h1, h2, _, _ => by omega
  | b + 1, b', h1, h2, h3, h4 => by
    unfold deepestX
    by_cases e : b' = b + 1
    · subst e; rw [ite_eq_left h3]
    · rw [ite_eq_right (by rw [h4 (b + 1) (by omega) (Nat.le_refl _)]; simp)]
      exact deepestX_eq c b b' h1 (by omega) h3 (fun y a b'' => h4 y a (by omega))

/-- One round of the fix-up on the counts. -/
def fixStep (L : Nat) (c : Nat → Nat) : Nat → Nat :=
  let b := deepestX c (L - 1)
  let c1 := updN c b (c b - 1)
  let c2 := updN c1 (b + 1) (c1 (b + 1) + 2)
  updN c2 L (c2 L - 1)

/-- `M` rounds. -/
def fixIter (L : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, c => c
  | M + 1, c => fixIter L M (fixStep L c)

theorem fixIter_succ' (L : Nat) : ∀ M c, fixIter L (M + 1) c = fixStep L (fixIter L M c)
  | 0, _ => rfl
  | M + 1, c => by
    show fixIter L (M + 1) (fixStep L c) = _
    rw [fixIter_succ' L M (fixStep L c)]; rfl



/-- `bl_count` of `e` holds the counts `c`. -/
def BcIs (e : DeflateState) (c : Nat → Nat) : Prop :=
  e.bl_count.size = 16 ∧ ∀ b, b < 16 → e.bl_count[b]! = UInt16.ofNat (c b)

/-- The search `while (bl_count[bits] == 0) bits--`. -/
theorem ws_gbSearch {h0 : Heap} {id : Nat} (e : DeflateState) (c : Nat → Nat) (hB : BcIs e c)
    (hsmall : ∀ b, c b < 65536) (bits : Int32) (b : Nat) (hb : bits.toInt = b) (hb15 : b < 16)
    (hex : ∃ b0, 1 ≤ b0 ∧ b0 ≤ b ∧ c b0 ≠ 0) :
    WS h0 id (cwhile (σ := Int32)
        (fun b => do pure (decide ((← Ptr.index (Ptr.ref (WRef.dstate_bl_count id) 0) b.toInt) == 0), b))
        (fun b => isub b 1) bits) e (fun bits' e' => e' = e ∧ ∃ b' : Nat, bits'.toInt = b' ∧ 1 ≤ b' ∧ b' ≤ b ∧
          c b' ≠ 0 ∧ ∀ y, b' < y → y ≤ b → c y = 0) := by
  refine WS.cwhile2 (id := id)
    (fun (bits' : Int32) e' => e' = e ∧ ∃ x : Nat, bits'.toInt = x ∧ x ≤ b ∧ (∃ b0, 1 ≤ b0 ∧ b0 ≤ x ∧ c b0 ≠ 0) ∧
      ∀ y, x < y → y ≤ b → c y = 0)
    (fun (bits' : Int32) _ => bits'.toInt.toNat)
    (fun (bits' : Int32) e' => e' = e ∧ ∃ b' : Nat, bits'.toInt = b' ∧ 1 ≤ b' ∧ b' ≤ b ∧
          c b' ≠ 0 ∧ ∀ y, b' < y → y ≤ b → c y = 0) ?_ ⟨rfl, b, hb, Nat.le_refl _, hex, fun y a b' => by omega⟩
    (by show bits.toInt.toNat < fuel; rw [hb]; simp only [Int.toNat_natCast, fuel]; omega)
  rintro bits' e' ⟨rfl, x, hx, hxb, ⟨b0, h1, h2, h3⟩, hdeep⟩
  have h1i : (1 : Int32).toInt = 1 := rfl
  have hv : WS h0 id (Ptr.index (Ptr.ref (WRef.dstate_bl_count id) 0) bits'.toInt) e'
      (fun v e'' => v = UInt16.ofNat (c x) ∧ e'' = e') := by
    refine WS.mono (ws_index_blc bits'.toInt (by omega) (by rw [hB.1]; omega)) ?_
    rintro v e'' ⟨hv, rfl⟩
    refine ⟨?_, rfl⟩
    rw [hv, show bits'.toInt.toNat = x by omega]; exact hB.2 x (by omega)
  refine WS.bind' hv fun v e1 ⟨hv1, he1⟩ => ?_
  subst e1; subst hv1
  by_cases hz : c x = 0
  · have hb0x : b0 < x := by
      by_cases e : b0 = x
      · subst e; exact absurd hz h3
      · omega
    refine WS.pure' (Or.inr ⟨?_, ?_⟩)
    · simp [hz]
    · refine WS.mono (ws_isub bits' 1 (by omega) (by omega)) ?_
      rintro b2 e2 ⟨hb2, rfl⟩
      refine ⟨⟨rfl, x - 1, by omega, by omega, ⟨b0, h1, by omega, h3⟩, fun y a b' => ?_⟩, ?_⟩
      · by_cases e : y = x
        · rw [e]; exact hz
        · exact hdeep y (by omega) b'
      · show b2.toInt.toNat < bits'.toInt.toNat
        omega
  · refine WS.pure' (Or.inl ⟨?_, ?_⟩)
    · have : (UInt16.ofNat (c x) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro e; apply hz
        have := congrArg UInt16.toNat e
        rw [UInt16.toNat_ofNat'] at this; simp at this; have := hsmall x; omega
      simp [this]
    · refine ⟨rfl, x, hx, ?_, hxb, hz, hdeep⟩
      by_cases e : b0 = x
      · omega
      · omega


theorem c_le_of {L NL : Nat} {c : Nat → Nat} (hc0 : ∀ b, L < b → c b = 0) (ht : rs c (L + 1) = NL) (x : Nat) :
    c x ≤ NL := by
  by_cases hx : x ≤ L
  · rw [← ht]; exact le_rs (F := c) (by omega)
  · rw [hc0 x (by omega)]; omega

theorem u16_sub1 (a : Nat) (h1 : 1 ≤ a) : UInt16.ofNat a - 1 = UInt16.ofNat (a - 1) := by
  have e : UInt16.ofNat a = UInt16.ofNat (a - 1) + 1 := by
    rw [show (1 : UInt16) = UInt16.ofNat 1 from rfl, ← UInt16.ofNat_add]; congr 1; omega
  rw [e, UInt16.add_sub_cancel]

theorem u16_add_k (a k : Nat) : UInt16.ofNat a + (UInt16.ofNat k) = UInt16.ofNat (a + k) := by
  rw [UInt16.ofNat_add]

theorem BcIs_set {e : DeflateState} {c : Nat → Nat} (hB : BcIs e c) (i : Nat) (hi : i < 16) (f : UInt16 → UInt16)
    (v : Nat) (hf : f (UInt16.ofNat (c i)) = UInt16.ofNat v) :
    BcIs { e with bl_count := e.bl_count.set! i (f e.bl_count[i]!) } (updN c i v) := by
  refine ⟨by simp [size_set!, hB.1], fun b hb => ?_⟩
  show (e.bl_count.set! i (f e.bl_count[i]!))[b]! = _
  rw [getD_set _ _ _ _ (by rw [hB.1]; exact hi)]
  by_cases eb : b = i
  · subst eb; simp only [ite_true, updN]; rw [hB.2 b hb, hf]
  · simp only [eb, ite_false, updN]; exact hB.2 b hb

/-- Invariant of the repair loop with `R` rounds left. -/
def FixInvX (L NL R : Nat) (ov : Int32) (c : Nat → Nat) (e1 e : DeflateState) : Prop :=
  ov.toInt = 2 * (R : Int) ∧ BcIs e c ∧ c 0 = 0 ∧ (∀ b, L < b → c b = 0) ∧ kc c L = 2 ^ L + R ∧
    R + 1 ≤ c L ∧ rs c (L + 1) = NL ∧ ∃ Bc, e = { e1 with bl_count := Bc }

theorem ws_gbFixRound {h0 : Heap} {id : Nat} (e1 : DeflateState) (ml : Int32) (L NL R : Nat) (hmlv : ml.toInt = L) (hL1 : 1 ≤ L)
    (hL15 : L ≤ 15) (hNL : NL ≤ 2 ^ L) (hNL2 : NL ≤ 1000) (ov : Int32) (c : Nat → Nat) (e : DeflateState)
    (hI : FixInvX L NL (R + 1) ov c e1 e) :
    WS h0 id (gbFix (Sp id) ml ov) e (fun ov' e' => FixInvX L NL R ov' (fixStep L c) e1 e') := by
  obtain ⟨ho, hB, hc0, hchi, hk, hcL, htot, Bc0, hex⟩ := hI
  have hle : ∀ x, c x ≤ NL := c_le_of hchi htot
  have hsmall : ∀ x, c x < 65536 := fun x => by have := hle x; omega
  obtain ⟨b0, hb01, hb0L, hb0⟩ := exists_short c L (R + 1) (by omega) hk (by omega) hc0
  have h1i : (1 : Int32).toInt = 1 := rfl
  have h2i : (2 : Int32).toInt = 2 := rfl
  have h2p : (2 : Int) ^ L = ((2 ^ L : Nat) : Int) := by push_cast; rfl
  have hp15 : 2 ^ L ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hL15
  unfold gbFix
  refine WS.bind' (ws_isub ml 1 (by omega) (by omega)) fun bits0 e1 ⟨hbits0, he1⟩ => ?_
  subst e1
  refine WS.bind' ws_pBlCount fun bc e1 ⟨hbc, he1⟩ => ?_
  subst e1; subst hbc
  refine WS.bind' (ws_gbSearch e c hB hsmall bits0 (L - 1) (by omega) (by omega) ⟨b0, hb01, by omega, hb0⟩)
    fun bits e1 ⟨he1, b, hbI, hb1, hbL, hcb, hdeep⟩ => ?_
  subst e1
  have hdb : deepestX c (L - 1) = b := deepestX_eq c (L - 1) b hb1 hbL hcb hdeep
  have hcb1 : 1 ≤ c b := by have : c b ≠ 0 := hcb; omega
  have e2lit : (2 : UInt16) = UInt16.ofNat 2 := rfl
  have hbl : bits.toInt.toNat = b := by omega
  -- bl_count[b]--
  refine WS.bind' (ws_index_blc bits.toInt (by omega) (by rw [hB.1]; omega)) fun v1 e1 ⟨hv1, he1⟩ => ?_
  subst e1; subst hv1
  refine WS.bind' (ws_setAt_blc bits.toInt _ (by omega) (by rw [hB.1]; omega)) fun _ e1 he1 => ?_
  subst e1
  rw [hbl]
  have hB1 : BcIs { e with bl_count := e.bl_count.set! b (e.bl_count[b]! - 1) } (updN c b (c b - 1)) :=
    BcIs_set hB b (by omega) (fun x => x - 1) (c b - 1) (u16_sub1 _ hcb1)
  -- bl_count[bits + 1] += 2
  refine WS.bind' (ws_iadd bits 1 (by omega) (by omega)) fun b1 e1 ⟨hb1', he1⟩ => ?_
  subst e1
  have hbl1 : b1.toInt.toNat = b + 1 := by omega
  refine WS.bind' (ws_index_blc b1.toInt (by omega) (by rw [(hB1).1]; omega)) fun v2 e1 ⟨hv2, he1⟩ => ?_
  subst e1; subst hv2
  refine WS.bind' (ws_setAt_blc b1.toInt _ (by omega) (by rw [(hB1).1]; omega)) fun _ e1 he1 => ?_
  subst e1
  rw [hbl1]
  have hle1 := hle (b + 1)
  have hB2 := BcIs_set hB1 (b + 1) (by omega) (fun x => x + 2) (updN c b (c b - 1) (b + 1) + 2)
    (by rw [e2lit, u16_add_k])
  -- bl_count[max_length]--
  have hc1 : ∀ x, x ≠ b → updN c b (c b - 1) x = c x := fun x hx => by simp [updN, hx]
  have hc1b : updN c b (c b - 1) (b + 1) = c (b + 1) := hc1 _ (by omega)
  have hc2L : 1 ≤ updN (updN c b (c b - 1)) (b + 1) (updN c b (c b - 1) (b + 1) + 2) L := by
    by_cases e : L = b + 1
    · simp [updN, e]
    · simp only [updN, e, ite_false, show L ≠ b by omega]; omega
  refine WS.bind' (ws_index_blc ml.toInt (by omega) (by rw [(hB2).1]; omega)) fun v3 e1 ⟨hv3, he1⟩ => ?_
  subst e1; subst hv3
  refine WS.bind' (ws_setAt_blc ml.toInt _ (by omega) (by rw [(hB2).1]; omega)) fun _ e1 he1 => ?_
  subst e1
  rw [show ml.toInt.toNat = L by omega]
  have hB3 := BcIs_set hB2 L (by omega) (fun x => x - 1)
    (updN (updN c b (c b - 1)) (b + 1) (updN c b (c b - 1) (b + 1) + 2) L - 1) (u16_sub1 _ hc2L)
  have hleL' := hle L
  refine WS.mono (ws_isub ov 2 (by omega) (by omega)) ?_
  rintro ov' e' ⟨hov', rfl⟩
  have hfs : fixStep L c = updN (updN (updN c b (c b - 1)) (b + 1) (updN c b (c b - 1) (b + 1) + 2)) L
      (updN (updN c b (c b - 1)) (b + 1) (updN c b (c b - 1) (b + 1) + 2) L - 1) := by
    unfold fixStep; rw [hdb]
  rw [hfs]
  have hrel : ∀ x ≤ L, updN (updN (updN c b (c b - 1)) (b + 1) (updN c b (c b - 1) (b + 1) + 2)) L
      (updN (updN c b (c b - 1)) (b + 1) (updN c b (c b - 1) (b + 1) + 2) L - 1) x + ind (x = b) + ind (x = L) =
      c x + 2 * ind (x = b + 1) := by
    intro x hx
    simp only [updN, ind]; repeat' split <;> (try subst_vars)
    all_goals omega
  obtain ⟨hr1, hr2⟩ := round_kraft c _ L b (by omega) hrel
  have hleL := hle L
  refine ⟨by rw [hov', h2i, ho]; omega, hB3, ?_, ?_, ?_, ?_, ?_, _, by rw [hex]⟩
  · simp only [updN]; repeat' split <;> (try subst_vars)
    all_goals omega
  · intro x hx
    have := hchi x hx
    simp only [updN]; repeat' split <;> (try subst_vars)
    all_goals omega
  · omega
  · by_cases e : L = b + 1
    · subst e; simp [updN]; omega
    · simp [updN, e, show L ≠ b by omega]; omega
  · omega


/-- **The repair loop.** From `R + 1` rounds left, the loop ends with the counts `fixIter L (R + 1) c0`. -/
theorem ws_gbFixLoop {h0 : Heap} {id : Nat} (e1 : DeflateState) (ml : Int32) (L NL R : Nat) (hmlv : ml.toInt = L) (hL1 : 1 ≤ L)
    (hL15 : L ≤ 15) (hNL : NL ≤ 2 ^ L) (hNL2 : NL ≤ 1000) (ov : Int32) (c0 : Nat → Nat) (e : DeflateState)
    (hI : FixInvX L NL (R + 1) ov c0 e1 e) :
    WS h0 id (cdoWhile (σ := Int32) (gbFix (Sp id) ml)
      (fun overflow => pure (decide (overflow.toInt > 0), overflow)) ov) e
      (fun o e' => FixInvX L NL 0 o (fixIter L (R + 1) c0) e1 e') := by
  refine WS.cdoWhile2 (id := id)
    (fun (o : Int32) e' => ∃ k, k ≤ R ∧ FixInvX L NL (k + 1) o (fixIter L (R - k) c0) e1 e')
    (fun (o : Int32) _ => o.toInt.toNat)
    (fun (o : Int32) e' => FixInvX L NL 0 o (fixIter L (R + 1) c0) e1 e') ?_
    ⟨R, Nat.le_refl _, by rw [Nat.sub_self]; exact hI⟩ (by
      have := hI.1; simp only [fuel]; have := ov.toInt_le
      have e : Int32.maxValue.toInt = 2147483647 := by decide
      omega)
  rintro o e' ⟨k, hk, hIk⟩
  refine WS.mono (ws_gbFixRound (h0 := h0) (id := id) e1 ml L NL k hmlv hL1 hL15 hNL hNL2 o _ e' hIk) ?_
  rintro o' e'' hI'
  refine WS.pure' ?_
  have ho' := hI'.1
  have ho := hIk.1
  cases k with
  | zero =>
    refine Or.inl ⟨?_, ?_⟩
    · simp only [decide_eq_false_iff_not]; omega
    · rw [← fixIter_succ'] at hI'; simpa using hI'
  | succ k' =>
    refine Or.inr ⟨?_, ⟨k', by omega, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]; omega
    · rw [← fixIter_succ'] at hI'
      rw [show R - k' = R - (k' + 1) + 1 by omega]; exact hI'
    · show o'.toInt.toNat < o.toInt.toNat
      omega

end Zlib.Trees.Proofs
