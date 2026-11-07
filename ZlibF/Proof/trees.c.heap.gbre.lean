import ZlibF.Proof.«trees.c.heap.gbfix»

/-!
# trees.c: `gen_bitlen`, reassignment of the lengths

`for (bits = max_length; bits != 0; bits--) { n = bl_count[bits]; while (n != 0) { m = heap[--h]; if (m > max_code)
continue; if (tree[m].Len != bits) { opt_len += (bits - tree[m].Len) * tree[m].Freq; tree[m].Len = bits; } n--; } }`.
The counting facts (`scnt`, `stot`, `utot`, `Aab`) and `kraft_of_counts` are copied from the earlier attempt
(`GenBitlenRe.lean`).
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB

/-- Scanned leaves (positions `≥ hc`) of length `x`. -/
def scnt (H : Nat → Nat) (hm maxc J hc : Nat) (len : Nat → Nat) (x : Nat) : Nat :=
  rs (fun i => if hc ≤ hm + 1 + i ∧ H (hm + 1 + i) ≤ maxc ∧ len (H (hm + 1 + i)) = x then 1 else 0) (2 * J)

/-- Scanned leaves. -/
def stot (H : Nat → Nat) (hm maxc J hc : Nat) : Nat :=
  rs (fun i => if hc ≤ hm + 1 + i ∧ H (hm + 1 + i) ≤ maxc then 1 else 0) (2 * J)

/-- Unscanned leaves. -/
def utot (H : Nat → Nat) (hm maxc J hc : Nat) : Nat :=
  rs (fun i => if hm + 1 + i < hc ∧ H (hm + 1 + i) ≤ maxc then 1 else 0) (2 * J)

/-- `Σ_{b < x ≤ L} c x`. -/
def Aab (c : Nat → Nat) (L b : Nat) : Nat := rs (fun x => if b < x then c x else 0) (L + 1)

theorem stot_utot (H : Nat → Nat) (hm maxc J hc : Nat) :
    stot H hm maxc J hc + utot H hm maxc J hc = nLeaves H hm J maxc := by
  unfold stot utot nLeaves; rw [← rs_add]; apply rs_congr; intro i _
  by_cases a : H (hm + 1 + i) ≤ maxc
  · by_cases b : hc ≤ hm + 1 + i
    · rw [ite_eq_left ⟨b, a⟩, ite_eq_right (fun h => by omega), ite_eq_left a]
    · rw [ite_eq_right (fun h => b h.1), ite_eq_left ⟨by omega, a⟩, ite_eq_left a]
  · rw [ite_eq_right (fun h => a h.2), ite_eq_right (fun h => a h.2), ite_eq_right a]

theorem Aab_pred (c : Nat → Nat) (L b : Nat) (hb : 1 ≤ b) (hbL : b ≤ L) :
    Aab c L (b - 1) = Aab c L b + c b := by
  unfold Aab
  rw [← rs_single' c b (L + 1) (by omega), ← rs_add]
  apply rs_congr; intro x _
  by_cases e : b = x
  · subst e; rw [ite_eq_left (by omega), ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]; omega
  · rw [ite_eq_right e]
    by_cases f : b < x
    · rw [ite_eq_left (by omega), ite_eq_left f]; omega
    · rw [ite_eq_right (by omega), ite_eq_right f]

theorem Aab_zero (c : Nat → Nat) (L : Nat) (h0 : c 0 = 0) : Aab c L 0 = rs c (L + 1) := by
  unfold Aab; apply rs_congr; intro x _
  by_cases e : x = 0
  · subst e; rw [ite_eq_right (Nat.lt_irrefl _), h0]
  · rw [ite_eq_left (by omega)]

theorem Aab_le (c : Nat → Nat) (L b : Nat) (hb : b ≤ L) : Aab c L b + c b ≤ rs c (L + 1) := by
  have := rs_le (n := L + 1) (F := fun x => (if b < x then c x else 0) + (if x = b then c x else 0)) (G := c)
    (fun x _ => by split <;> split <;> omega)
  rw [rs_add, rs_single, ite_eq_left (by omega)] at this
  unfold Aab; omega

theorem ite_iff {p q : Prop} [Decidable p] [Decidable q] {α : Type} (a b : α) (h : p ↔ q) :
    (if p then a else b) = (if q then a else b) := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left (h.mp hp)]
  · rw [ite_eq_right hp, ite_eq_right (fun hq => hp (h.mpr hq))]


/-- Kraft equality of the reassigned lengths (by position). -/
theorem kraft_of_counts (H : Nat → Nat) (hm J maxc L : Nat) (len c : Nat → Nat) (hc0 : c 0 = 0)
    (hkc : kc c L = 2 ^ L)
    (hle : ∀ i < 2 * J, H (hm + 1 + i) ≤ maxc → len (H (hm + 1 + i)) ≤ L)
    (hcnt : ∀ x, blP H hm maxc len (2 * J) x = if 0 < x ∧ x ≤ L then c x else 0) :
    rs (fun i => if H (hm + 1 + i) ≤ maxc then 2 ^ (L - len (H (hm + 1 + i))) else 0) (2 * J) = 2 ^ L := by
  rw [rs_regroup (fun i => H (hm + 1 + i) ≤ maxc) (fun i => len (H (hm + 1 + i))) (fun b => 2 ^ (L - b))
    (2 * J) (L + 1) (fun i hi hl => by have := hle i hi hl; omega)]
  rw [← hkc]; unfold kc; apply rs_congr; intro x hx
  have := hcnt x; unfold blP at this; rw [this]
  by_cases e : x = 0
  · subst e; rw [ite_eq_right (fun h => by omega), hc0]
  · rw [ite_eq_left ⟨by omega, by omega⟩]



/-! ### One scan step on the counts -/

theorem scnt_step (H : Nat → Nat) (hm maxc J hc : Nat) (len len' : Nat → Nat) (x : Nat) (hc2 : hm + 2 ≤ hc)
    (hcJ : hc ≤ hm + 1 + 2 * J)
    (hsame : ∀ i, i < 2 * J → hc ≤ hm + 1 + i → len' (H (hm + 1 + i)) = len (H (hm + 1 + i))) :
    scnt H hm maxc J (hc - 1) len' x = scnt H hm maxc J hc len x +
      (if H (hc - 1) ≤ maxc ∧ len' (H (hc - 1)) = x then 1 else 0) := by
  unfold scnt
  have key : ∀ i < 2 * J, (if hc - 1 ≤ hm + 1 + i ∧ H (hm + 1 + i) ≤ maxc ∧ len' (H (hm + 1 + i)) = x then 1 else 0) =
      (if hc ≤ hm + 1 + i ∧ H (hm + 1 + i) ≤ maxc ∧ len (H (hm + 1 + i)) = x then 1 else 0) +
      (if i = hc - 2 - hm then (if H (hc - 1) ≤ maxc ∧ len' (H (hc - 1)) = x then 1 else 0) else 0) := by
    intro i hi
    by_cases e : i = hc - 2 - hm
    · have hA : hm + 1 + i = hc - 1 := by omega
      have hn : ¬ hc ≤ hc - 1 := by omega
      rw [ite_eq_left e]; simp [hA, hn]
    · by_cases h1 : hc ≤ hm + 1 + i
      · have h1' : hc - 1 ≤ hm + 1 + i := by omega
        simp [e, h1, h1', hsame i hi h1]
      · have h1' : ¬ hc - 1 ≤ hm + 1 + i := by omega
        simp [e, h1, h1']
  rw [rs_congr key, rs_add, rs_single, ite_eq_left (by omega)]

theorem stot_step (H : Nat → Nat) (hm maxc J hc : Nat) (hc2 : hm + 2 ≤ hc) (hcJ : hc ≤ hm + 1 + 2 * J) :
    stot H hm maxc J (hc - 1) = stot H hm maxc J hc + (if H (hc - 1) ≤ maxc then 1 else 0) := by
  unfold stot
  have key : ∀ i < 2 * J, (if hc - 1 ≤ hm + 1 + i ∧ H (hm + 1 + i) ≤ maxc then 1 else 0) =
      (if hc ≤ hm + 1 + i ∧ H (hm + 1 + i) ≤ maxc then 1 else 0) +
      (if i = hc - 2 - hm then (if H (hc - 1) ≤ maxc then 1 else 0) else 0) := by
    intro i hi
    by_cases e : i = hc - 2 - hm
    · have hA : hm + 1 + i = hc - 1 := by omega
      have hn : ¬ hc ≤ hc - 1 := by omega
      rw [ite_eq_left e]; simp [hA, hn]
    · by_cases h1 : hc ≤ hm + 1 + i
      · have h1' : hc - 1 ≤ hm + 1 + i := by omega
        simp [e, h1, h1']
      · have h1' : ¬ hc - 1 ≤ hm + 1 + i := by omega
        simp [e, h1, h1']
  rw [rs_congr key, rs_add, rs_single, ite_eq_left (by omega)]

theorem costP_set (H : Nat → Nat) (hm maxc J : Nat) (fr len : Nat → Nat) (xb : Nat → Nat) (ip b : Nat)
    (hip : ip < 2 * J) (hleaf : H (hm + 1 + ip) ≤ maxc)
    (hinj : ∀ i, i < 2 * J → i ≠ ip → H (hm + 1 + i) ≠ H (hm + 1 + ip)) :
    costP H hm maxc fr (fun v => if v = H (hm + 1 + ip) then b else len v) xb (2 * J) +
        fr (H (hm + 1 + ip)) * len (H (hm + 1 + ip)) =
      costP H hm maxc fr len xb (2 * J) + fr (H (hm + 1 + ip)) * b := by
  unfold costP
  have key : ∀ i < 2 * J, (if H (hm + 1 + i) ≤ maxc then fr (H (hm + 1 + i)) *
        ((fun v => if v = H (hm + 1 + ip) then b else len v) (H (hm + 1 + i)) + xb (H (hm + 1 + i))) else 0) +
      (if i = ip then fr (H (hm + 1 + ip)) * len (H (hm + 1 + ip)) else 0) =
      (if H (hm + 1 + i) ≤ maxc then fr (H (hm + 1 + i)) * (len (H (hm + 1 + i)) + xb (H (hm + 1 + i))) else 0) +
      (if i = ip then fr (H (hm + 1 + ip)) * b else 0) := by
    intro i hi
    by_cases e : i = ip
    · subst e; simp only [ite_true, hleaf]
      rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    · simp only [ite_eq_right e, Nat.add_zero, hinj i hi e, ite_false]
  have := rs_congr key
  rw [rs_add, rs_add, rs_single, rs_single, ite_eq_left hip, ite_eq_left hip] at this
  exact this


theorem opt_upd (opt0 : UInt64) (cOld cNew fr lm b : Nat) (hN : cNew + fr * lm = cOld + fr * b) :
    opt0 + UInt64.ofNat cOld + (UInt64.ofNat b - UInt64.ofNat lm) * UInt64.ofNat fr = opt0 + UInt64.ofNat cNew := by
  have hN' : cNew + lm * fr = cOld + b * fr := by rw [Nat.mul_comm lm, Nat.mul_comm b]; exact hN
  have h1 : (UInt64.ofNat b - UInt64.ofNat lm) * UInt64.ofNat fr + UInt64.ofNat (lm * fr) = UInt64.ofNat (b * fr) := by
    rw [UInt64.ofNat_mul, UInt64.ofNat_mul, ← UInt64.add_mul, UInt64.sub_add_cancel]
  have h2 : UInt64.ofNat cNew + UInt64.ofNat (lm * fr) = UInt64.ofNat cOld + UInt64.ofNat (b * fr) := by
    rw [← UInt64.ofNat_add, ← UInt64.ofNat_add, hN']
  rw [UInt64.add_assoc]
  congr 1
  have h3 : (UInt64.ofNat cOld + (UInt64.ofNat b - UInt64.ofNat lm) * UInt64.ofNat fr) + UInt64.ofNat (lm * fr)
      = UInt64.ofNat cNew + UInt64.ofNat (lm * fr) := by
    rw [UInt64.add_assoc, h1, h2]
  have h4 := congrArg (fun z => z - UInt64.ofNat (lm * fr)) h3
  simp only [UInt64.add_sub_cancel] at h4
  exact h4

/-! ### The state of the reassignment -/

open Zlib.Trees.Proofs.GB

/-- `tree[v].Len`. -/
def curL (T : Array CtData) (v : Nat) : Nat := (T[v]!).dl.toNat

/-- The record `e0` with the tree array replaced and `opt_len` set. -/
def mkP2 (tk : TK) (e0 : DeflateState) (Tc : Array CtData) (O : UInt64) : DeflateState :=
  { tk.setArr e0 Tc with opt_len := O }

@[simp] theorem tk_arr_mkP2 (tk : TK) (e0 Tc O) : tk.arr (mkP2 tk e0 Tc O) = Tc := by cases tk <;> rfl
@[simp] theorem mkP2_opt_len (tk : TK) (e0 Tc O) : (mkP2 tk e0 Tc O).opt_len = O := by cases tk <;> rfl
@[simp] theorem mkP2_heap (tk : TK) (e0 Tc O) : (mkP2 tk e0 Tc O).heap = e0.heap := by cases tk <;> rfl
@[simp] theorem mkP2_bl_count (tk : TK) (e0 Tc O) : (mkP2 tk e0 Tc O).bl_count = e0.bl_count := by cases tk <;> rfl
theorem setArr_mkP2 (tk : TK) (e0 Tc O A) : tk.setArr (mkP2 tk e0 Tc O) A = mkP2 tk e0 A O := by cases tk <;> rfl
theorem optlen_mkP2 (tk : TK) (e0 Tc O O') : ({ mkP2 tk e0 Tc O with opt_len := O' } : DeflateState) = mkP2 tk e0 Tc O' := by
  cases tk <;> rfl

/-- Preconditions of the reassignment. -/
structure RCtx (tk : TK) (e0 : DeflateState) (hm J elems maxc L : Nat) (c : Nat → Nat) : Prop where
  hsz : e0.heap.size = 573
  hnn : ∀ q, hm ≤ q → q < 573 → 0 ≤ (e0.heap[q]!).toInt
  shape : PShape (Hn e0) hm J elems maxc
  nc : elems + J ≤ (tk.arr e0).size
  tsz : (tk.arr e0).size ≤ 600
  L1 : 1 ≤ L
  L15 : L ≤ 15
  c0 : c 0 = 0
  ctot : rs c (L + 1) = nLeaves (Hn e0) hm J maxc

/-- The state of the scan: positions `≥ hc` scanned, lengths `L .. b + 1` all given out, `c b - n` leaves of length `b`. -/
def ReSt (tk : TK) (e0 : DeflateState) (hm J maxc L : Nat) (xb : Nat → Nat) (c : Nat → Nat) (opt0 : UInt64)
    (hc b n : Nat) (e : DeflateState) : Prop :=
  ∃ (Tc : Array CtData) (O : UInt64), e = mkP2 tk e0 Tc O ∧ Tc.size = (tk.arr e0).size ∧ hm + 1 ≤ hc ∧ hc ≤ 573 ∧
    n ≤ c b ∧
    O = opt0 + UInt64.ofNat (costP (Hn e0) hm maxc (frn (tk.arr e0)) (curL Tc) xb (2 * J)) ∧
    (∀ v : Nat, (Tc[v]!).fc = ((tk.arr e0)[v]!).fc) ∧
    (∀ v : Nat, (∀ q, hm ≤ q → q < 573 → Hn e0 q ≠ v) → (Tc[v]!).dl = ((tk.arr e0)[v]!).dl) ∧
    (∀ x, scnt (Hn e0) hm maxc J hc (curL Tc) x = if b < x ∧ x ≤ L then c x else if x = b then c b - n else 0) ∧
    stot (Hn e0) hm maxc J hc = Aab c L b + (c b - n)


theorem i2u_toNat (x : Int32) (h : 0 ≤ x.toInt) (hb : x.toInt < 65536) : (i2u x).toNat = x.toInt.toNat := by
  unfold i2u
  rw [UInt32.toNat_ofNat']
  omega

theorem i2ul_eq (x : Int32) (h : 0 ≤ x.toInt) (hb : x.toInt < 65536) : i2ul x = UInt64.ofNat x.toInt.toNat := by
  unfold i2ul; congr 1; omega

theorem i2us_eq (x : Int32) (h : 0 ≤ x.toInt) (hb : x.toInt < 65536) : i2us x = UInt16.ofNat x.toInt.toNat := by
  unfold i2us; congr 1; omega

theorem bne_u32 (lm : UInt16) (x : Int32) (h : 0 ≤ x.toInt) (hb : x.toInt < 65536) :
    ((lm.toUInt32 != i2u x) = true) ↔ lm.toNat ≠ x.toInt.toNat := by
  rw [bne_iff_ne, ne_eq, ne_eq, ← UInt32.toNat_inj, UInt16.toNat_toUInt32, i2u_toNat x h hb]

theorem curL_setLen (T : Array CtData) (v c : Nat) (hv : v < T.size) (hc : c < 65536) :
    curL (setLen T v c) = fun w => if w = v then c else curL T w := by
  funext w
  unfold curL setLen
  rw [getD_set T v w _ hv]
  by_cases e : w = v
  · subst e; simp [UInt16.toNat_ofNat']; omega
  · simp [e]

theorem ws_gbInner {h0 : Heap} {id : Nat} {tk : TK} {e0 : DeflateState} {hm J elems maxc L : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64} (ctx : RCtx tk e0 hm J elems maxc L c)
    (mc bitsv : Int32) (hmc : mc.toInt = maxc) (b : Nat) (hb1 : 1 ≤ b) (hbL : b ≤ L) (hbv : bitsv.toInt = b)
    (n hc : Nat) (nI hI : Int32) (hnI : nI.toInt = n) (hhI : hI.toInt = hc) (hn : 1 ≤ n) (e : DeflateState)
    (hR : ReSt tk e0 hm J maxc L xb c opt0 hc b n e) :
    WS h0 id (gbInner (Sp id) (Ptr.ref (tk.ref id) 0) mc bitsv (nI, hI)) e (fun r e' =>
      ∃ (hc' n' : Nat), r.1.toInt = (n' : Int) ∧ r.2.toInt = (hc' : Int) ∧ hc' < hc ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b n' e') := by
  obtain ⟨Tc, O, rfl, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩ := hR
  have PS := ctx.shape
  have hm_eq := PS.hm_eq
  have hsz := ctx.hsz
  have hL15 := ctx.L15
  have hL1 := ctx.L1
  have hcb : c b ≤ 600 := by
    have h1 := le_rs (F := c) (n := L + 1) (i := b) (by omega)
    have h2 := nLeaves_le ctx.shape
    have h3 := ctx.shape.maxc_lt
    have h4 := ctx.nc; have h5 := ctx.tsz
    rw [ctx.ctot] at h1; omega
  have hut : 1 ≤ utot (Hn e0) hm maxc J hc := by
    have := stot_utot (Hn e0) hm maxc J hc
    have := Aab_le c L b hbL
    have := ctx.ctot
    omega
  have hcp : hm + 2 ≤ hc := by
    by_cases hx : hm + 2 ≤ hc
    · exact hx
    · exfalso
      have : utot (Hn e0) hm maxc J hc = 0 := rs_eq_zero (fun i _ => by rw [ite_eq_right (fun h => by omega)])
      omega
  have hp573 : hc - 1 < 573 := by omega
  have hnn := ctx.hnn (hc - 1) (by omega) hp573
  have hnode : Hn e0 (hc - 1) < elems + J := by
    rcases PS.kind (hc - 1) (by omega) hp573 with h1 | h1
    · have := PS.maxc_lt; omega
    · omega
  have hnc' := ctx.nc
  have h1i : (1 : Int32).toInt = 1 := rfl
  have hinj : ∀ i, i < 2 * J → hc ≤ hm + 1 + i → Hn e0 (hm + 1 + i) ≠ Hn e0 (hc - 1) := by
    intro i hi h1 e
    have := PS.inj (hm + 1 + i) (hc - 1) (by omega) (by omega) (by omega) hp573 e; omega
  unfold gbInner
  simp only []
  refine WS.bind' (ws_isub hI 1 (by omega) (by omega)) fun h' e1 ⟨hh', he1⟩ => ?_
  subst e1
  have hh'v : h'.toInt = (hc - 1 : Nat) := by omega
  refine WS.bind' (ws_heapAt h' (by omega) (by rw [mkP2_heap]; omega)) fun m e1 ⟨hmv, he1⟩ => ?_
  subst e1
  have hmI : m.toInt = (Hn e0 (hc - 1) : Int) := by
    rw [mkP2_heap] at hmv
    have : h'.toInt.toNat = hc - 1 := by omega
    rw [this] at hmv; rw [hmv]; unfold Hn; omega
  have hcJ : hc ≤ hm + 1 + 2 * J := by omega
  -- the common ending: isub n 1, then the result
  have fin : ∀ (Tn : Array CtData) (On : UInt64), Tn.size = (tk.arr e0).size →
      On = opt0 + UInt64.ofNat (costP (Hn e0) hm maxc (frn (tk.arr e0)) (curL Tn) xb (2 * J)) →
      (curL Tn = fun v => if v = Hn e0 (hc - 1) then b else curL Tc v) →
      (∀ v : Nat, (Tn[v]!).fc = ((tk.arr e0)[v]!).fc) →
      (∀ v : Nat, (∀ q, hm ≤ q → q < 573 → Hn e0 q ≠ v) → (Tn[v]!).dl = ((tk.arr e0)[v]!).dl) →
      Hn e0 (hc - 1) ≤ maxc →
      WS h0 id (do let r ← isub nI 1; pure (r, h')) (mkP2 tk e0 Tn On) (fun r e' =>
        ∃ (hc' n' : Nat), r.1.toInt = (n' : Int) ∧ r.2.toInt = (hc' : Int) ∧ hc' < hc ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b n' e') := by
    intro Tn On hTn hOn hcur hfcn houtn hleaf
    refine WS.bind' (ws_isub nI 1 (by omega) (by omega)) fun r e1 ⟨hr, he1⟩ => ?_
    subst e1
    refine WS.pure' ⟨hc - 1, n - 1, by simp only; omega, by simp only; omega, by omega, Tn, On, rfl, hTn, by omega,
      by omega, by omega, hOn, hfcn, houtn, ?_, ?_⟩
    · intro x
      have hs := scnt_step (Hn e0) hm maxc J hc (curL Tc) (curL Tn) x hcp hcJ (fun i hi h1 => by
        rw [hcur]; simp [hinj i hi h1])
      rw [hs, hsc x, hcur]
      simp only [ite_true, hleaf]
      by_cases e1 : b < x ∧ x ≤ L
      · rw [ite_eq_left e1, ite_eq_left e1]; have : x ≠ b := by omega
        simp [this, Ne.symm this]
      · rw [ite_eq_right e1, ite_eq_right e1]
        by_cases e2 : x = b
        · subst e2; simp; omega
        · simp [e2, Ne.symm e2]
    · rw [stot_step (Hn e0) hm maxc J hc hcp hcJ, hst, ite_eq_left hleaf]; omega
  have hmt : m.toInt.toNat = Hn e0 (hc - 1) := by omega
  have hmlt : 0 ≤ m.toInt ∧ m.toInt < ((tk.arr (mkP2 tk e0 Tc O)).size : Int) := by
    rw [tk_arr_mkP2, hTs]; omega
  by_cases hleaf : Hn e0 (hc - 1) ≤ maxc
  · refine WS.ite' (fun hh => absurd hh (by omega)) (fun _ => ?_)
    refine WS.bind' (ws_getDl tk m.toInt hmlt.1 hmlt.2) fun lm e1 ⟨hlm, he1⟩ => ?_
    subst e1
    have hlm' : lm = (Tc[Hn e0 (hc - 1)]!).dl := by rw [hlm, tk_arr_mkP2, hmt]
    refine WS.ite' (fun hch => ?_) (fun hnch => ?_)
    · -- the length changes
      have hne := (bne_u32 lm bitsv (by omega) (by omega)).mp hch
      refine WS.bind' (ws_getFc tk m.toInt hmlt.1 hmlt.2) fun fm e1 ⟨hfm, he1⟩ => ?_
      subst e1
      have hfm' : fm.toNat = frn (tk.arr e0) (Hn e0 (hc - 1)) := by
        rw [hfm, tk_arr_mkP2, hmt, hfc]; rfl
      refine WS.bind' (ws_md _) fun _ e1 he1 => ?_
      subst e1
      rw [optlen_mkP2]
      refine WS.bind' (ws_setDl tk m.toInt (i2us bitsv) hmlt.1 (by rw [tk_arr_mkP2, hTs]; omega)) fun _ e1 he1 => ?_
      subst e1
      rw [setArr_mkP2, tk_arr_mkP2, hmt, i2us_eq bitsv (by omega) (by omega)]
      have hbn : bitsv.toInt.toNat = b := by omega
      rw [hbn]
      have hvT : Hn e0 (hc - 1) < Tc.size := by omega
      have hcur := curL_setLen Tc (Hn e0 (hc - 1)) b hvT (by omega)
      refine fin (setLen Tc (Hn e0 (hc - 1)) b) _ (by unfold setLen; rw [size_set!]; exact hTs) ?_ hcur ?_ ?_ hleaf
      · simp only [mkP2_opt_len]
        rw [hcur, i2ul_eq bitsv (by omega) (by omega), hbn, u16_u64 lm, u16_u64 fm, hfm', hlm', hO]
        have hcs := costP_set (Hn e0) hm maxc J (frn (tk.arr e0)) (curL Tc) xb (hc - 2 - hm) b (by omega)
          (by have : hm + 1 + (hc - 2 - hm) = hc - 1 := by omega
              rw [this]; exact hleaf)
          (fun i hi hne => by
            have : hm + 1 + (hc - 2 - hm) = hc - 1 := by omega
            rw [this]
            intro e; have := PS.inj (hm + 1 + i) (hc - 1) (by omega) (by omega) (by omega) hp573 e; omega)
        have e5 : hm + 1 + (hc - 2 - hm) = hc - 1 := by omega
        rw [e5] at hcs
        have := opt_upd opt0 (costP (Hn e0) hm maxc (frn (tk.arr e0)) (curL Tc) xb (2 * J))
          (costP (Hn e0) hm maxc (frn (tk.arr e0)) (fun v => if v = Hn e0 (hc - 1) then b else curL Tc v) xb (2 * J))
          (frn (tk.arr e0) (Hn e0 (hc - 1))) (curL Tc (Hn e0 (hc - 1))) b hcs
        have e6 : curL Tc (Hn e0 (hc - 1)) = (Tc[Hn e0 (hc - 1)]!).dl.toNat := rfl
        rw [e6] at this; rw [this]
      · intro v
        unfold setLen; rw [getD_set Tc _ v _ hvT]
        by_cases e : v = Hn e0 (hc - 1)
        · subst e; simp [hfc]
        · simp [e, hfc v]
      · intro v hv
        unfold setLen; rw [getD_set Tc _ v _ hvT, ite_eq_right]
        · exact hout v hv
        · intro e; exact hv (hc - 1) (by omega) hp573 e.symm
    · have heq : lm.toNat = b := by
        have hh : lm.toNat = bitsv.toInt.toNat := by
          by_cases e : lm.toNat = bitsv.toInt.toNat
          · exact e
          · exact absurd ((bne_u32 lm bitsv (by omega) (by omega)).mpr e) hnch
        omega
      have hcm : curL Tc (Hn e0 (hc - 1)) = b := by unfold curL; rw [← hlm']; exact heq
      refine fin Tc O hTs hO ?_ hfc hout hleaf
      funext v
      by_cases e : v = Hn e0 (hc - 1)
      · subst e; simp [hcm]
      · simp [e]
  · refine WS.ite' (fun _ => ?_) (fun hh => absurd (by omega) hh)
    refine WS.pure' ⟨hc - 1, n, hnI, hh'v, by omega, Tc, O, rfl, hTs, by omega, by omega, hnc, hO, hfc, hout, ?_, ?_⟩
    · intro x
      have hs := scnt_step (Hn e0) hm maxc J hc (curL Tc) (curL Tc) x hcp hcJ (fun i hi h1 => rfl)
      have hz : ¬ (Hn e0 (hc - 1) ≤ maxc ∧ curL Tc (Hn e0 (hc - 1)) = x) := fun h => hleaf h.1
      rw [hs, hsc x, ite_eq_right hz, Nat.add_zero]
    · rw [stot_step (Hn e0) hm maxc J hc hcp hcJ, hst, ite_eq_right hleaf]; rfl


theorem bne_zero_iff (n : Int32) : (n != 0) = true ↔ n.toInt ≠ 0 := by
  rw [bne_iff_ne, ne_eq, ne_eq, ← Int32.toInt_inj]
  have : (0 : Int32).toInt = 0 := rfl
  rw [this]

/-- The inner loop: `n` leaves of length `b` are taken from the heap, going down. -/
theorem ws_gbInnerLoop {h0 : Heap} {id : Nat} {tk : TK} {e0 : DeflateState} {hm J elems maxc L : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64} (ctx : RCtx tk e0 hm J elems maxc L c)
    (mc bitsv : Int32) (hmc : mc.toInt = maxc) (b : Nat) (hb1 : 1 ≤ b) (hbL : b ≤ L) (hbv : bitsv.toInt = b)
    (n hc : Nat) (nI hI : Int32) (hnI : nI.toInt = n) (hhI : hI.toInt = hc) (e : DeflateState)
    (hR : ReSt tk e0 hm J maxc L xb c opt0 hc b n e) :
    WS h0 id (cwhile (σ := Int32 × Int32) (fun (n, h) => pure (n != 0, (n, h)))
      (gbInner (Sp id) (Ptr.ref (tk.ref id) 0) mc bitsv) (nI, hI)) e (fun r e' =>
      ∃ hc' : Nat, r.2.toInt = (hc' : Int) ∧ r.1.toInt = 0 ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b 0 e') := by
  refine WS.cwhile2 (id := id)
    (fun (st : Int32 × Int32) e' => ∃ n hc : Nat, st.1.toInt = (n : Int) ∧ st.2.toInt = (hc : Int) ∧ ReSt tk e0 hm J maxc L xb c opt0 hc b n e')
    (fun (st : Int32 × Int32) _ => st.2.toInt.toNat)
    (fun (st : Int32 × Int32) e' => ∃ hc' : Nat, st.2.toInt = (hc' : Int) ∧ st.1.toInt = 0 ∧ ReSt tk e0 hm J maxc L xb c opt0 hc' b 0 e')
    ?_ ⟨n, hc, hnI, hhI, hR⟩ (by
      have := ctx.hsz; simp only [fuel]
      have := hI.toInt_le
      have e : Int32.maxValue.toInt = 2147483647 := by decide
      omega)
  rintro ⟨n1, h1⟩ e' ⟨n2, hc2, hn2, hh2, hR2⟩
  simp only at hn2 hh2
  refine WS.pure' ?_
  by_cases hz : n2 = 0
  · refine Or.inl ⟨?_, hc2, hh2, by show n1.toInt = 0; omega, by subst hz; exact hR2⟩
    have : ¬ n1.toInt ≠ 0 := by omega
    have h' := mt (bne_zero_iff n1).mp this
    simpa using h'
  · refine Or.inr ⟨?_, ?_⟩
    · exact (bne_zero_iff n1).mpr (by omega)
    · refine WS.mono (ws_gbInner ctx mc bitsv hmc b hb1 hbL hbv n2 hc2 n1 h1 hn2 hh2 (by omega) e' hR2) ?_
      rintro r e'' ⟨hc', n', hr1, hr2, hlt, hR'⟩
      exact ⟨⟨n', hc', hr1, hr2, hR'⟩, by show r.2.toInt.toNat < h1.toInt.toNat; omega⟩


theorem ReSt_down {tk : TK} {e0 : DeflateState} {hm J maxc L : Nat} {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64}
    {hc b : Nat} {e : DeflateState} (hb1 : 1 ≤ b) (hbL : b ≤ L)
    (hR : ReSt tk e0 hm J maxc L xb c opt0 hc b 0 e) : ReSt tk e0 hm J maxc L xb c opt0 hc (b - 1) (c (b - 1)) e := by
  obtain ⟨Tc, O, he, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩ := hR
  refine ⟨Tc, O, he, hTs, hc1, hc2, Nat.le_refl _, hO, hfc, hout, fun x => ?_, ?_⟩
  · rw [hsc x]
    by_cases e1 : b < x ∧ x ≤ L
    · rw [ite_eq_left e1, ite_eq_left (show b - 1 < x ∧ x ≤ L from ⟨by omega, e1.2⟩)]
    · by_cases e2 : x = b
      · rw [ite_eq_right e1, ite_eq_left e2, ite_eq_left (show b - 1 < x ∧ x ≤ L from ⟨by omega, by omega⟩), Nat.sub_zero, e2]
      · by_cases e3 : x = b - 1
        · rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right (show ¬ (b - 1 < x ∧ x ≤ L) from fun h => by omega), ite_eq_left e3, Nat.sub_self]
        · rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right (show ¬ (b - 1 < x ∧ x ≤ L) from fun h => by omega), ite_eq_right e3]
  · rw [hst, Aab_pred c L b hb1 hbL, Nat.sub_zero, Nat.sub_self]; omega

/-- The reassignment loop. -/
theorem ws_gbOuter {h0 : Heap} {id : Nat} {tk : TK} {e0 : DeflateState} {hm J elems maxc L : Nat}
    {xb : Nat → Nat} {c : Nat → Nat} {opt0 : UInt64} (ctx : RCtx tk e0 hm J elems maxc L c) (hB : BcIs e0 c)
    (mc ml : Int32) (hmc : mc.toInt = maxc) (hml : ml.toInt = L) (hI : Int32) (hhI : hI.toInt = 573) (e : DeflateState)
    (hR : ReSt tk e0 hm J maxc L xb c opt0 573 L (c L) e) :
    WS h0 id (cfor (σ := Int32 × Int32) (fun (bits, _) => pure (bits != 0))
      (fun (bits, h) => do pure (← isub bits 1, h)) (gbOuter (Sp id) (Ptr.ref (tk.ref id) 0) mc) (ml, hI)) e
      (fun r e' => ∃ hc, ReSt tk e0 hm J maxc L xb c opt0 hc 0 0 e') := by
  have hL15 := ctx.L15
  have hL1 := ctx.L1
  have hcL : ∀ x, x ≤ L → c x ≤ 600 := by
    intro x hx
    have h1 := le_rs (F := c) (n := L + 1) (i := x) (by omega)
    have h2 := nLeaves_le ctx.shape
    have h3 := ctx.shape.maxc_lt
    have h4 := ctx.nc; have h5 := ctx.tsz
    rw [ctx.ctot] at h1; omega
  have h1i : (1 : Int32).toInt = 1 := rfl
  have hfuel : ml.toInt.toNat < fuel := by
    have := ml.toInt_le
    have e : Int32.maxValue.toInt = 2147483647 := by decide
    simp only [fuel]; omega
  refine WS.cfor2 (id := id)
    (fun (st : Int32 × Int32) e' => ∃ b hc : Nat, st.1.toInt = (b : Int) ∧ st.2.toInt = (hc : Int) ∧ b ≤ L ∧
      ReSt tk e0 hm J maxc L xb c opt0 hc b (c b) e')
    (fun (st : Int32 × Int32) _ => st.1.toInt.toNat)
    (fun (st : Int32 × Int32) e' => ∃ hc, ReSt tk e0 hm J maxc L xb c opt0 hc 0 0 e') ?_
    ⟨L, 573, hml, hhI, Nat.le_refl _, hR⟩ hfuel
  rintro ⟨bits, h⟩ e' ⟨b, hc, hb, hh, hbL, hR2⟩
  simp only at hb hh
  refine WS.pure' ?_
  by_cases hz : b = 0
  · subst hz
    refine Or.inl ⟨?_, hc, ?_⟩
    · have : ¬ bits.toInt ≠ 0 := by omega
      simpa using mt (bne_zero_iff bits).mp this
    · rw [ctx.c0] at hR2; exact hR2
  · refine Or.inr ⟨?_, ?_⟩
    · exact (bne_zero_iff bits).mpr (by omega)
    · -- the body, then the step
      have hbody : WS h0 id (gbOuter (Sp id) (Ptr.ref (tk.ref id) 0) mc (bits, h)) e'
          (fun r e'' => r.1 = bits ∧ ∃ hc' : Nat, r.2.toInt = (hc' : Int) ∧
            ReSt tk e0 hm J maxc L xb c opt0 hc' b 0 e'') := by
        unfold gbOuter
        simp only []
        refine WS.bind' ws_pBlCount fun bc e1 ⟨hbc, he1⟩ => ?_
        subst e1; subst hbc
        obtain ⟨Tc, O, he, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩ := hR2
        subst he
        have hcb := hcL b hbL
        refine WS.bind' (ws_index_blc bits.toInt (by omega) (by rw [mkP2_bl_count, hB.1]; omega)) fun v e1 ⟨hv, he1⟩ => ?_
        subst e1
        have hv' : v = UInt16.ofNat (c b) := by
          rw [hv, mkP2_bl_count, show bits.toInt.toNat = b by omega]; exact hB.2 b (by omega)
        have hu : (u16i v).toInt = (c b : Int) := by
          rw [u16i_toInt, hv', UInt16.toNat_ofNat']; omega
        refine WS.bind' (ws_gbInnerLoop ctx mc bits hmc b (by omega) hbL hb (c b) hc (u16i v) h hu hh _
          ⟨Tc, O, rfl, hTs, hc1, hc2, hnc, hO, hfc, hout, hsc, hst⟩) fun r e1 ⟨hc', hr2, hr1, hR3⟩ => ?_
        obtain ⟨n3, h3⟩ := r
        exact WS.pure' ⟨rfl, hc', hr2, hR3⟩
      refine WS.bind' hbody fun r e1 ⟨hr1, hc', hr2, hR3⟩ => ?_
      have hr1' : r.1.toInt = bits.toInt := by rw [hr1]
      refine WS.bind' (ws_isub r.1 1 (by omega) (by omega)) fun b2 e2 ⟨hb2, he2⟩ => ?_
      subst e2
      refine WS.pure' ⟨⟨b - 1, hc', by show b2.toInt = ((b - 1 : Nat) : Int); omega, hr2, by omega, ReSt_down (by omega) hbL hR3⟩, ?_⟩
      show b2.toInt.toNat < bits.toInt.toNat
      omega

end Zlib.Trees.Proofs
