import ZlibF.Proof.«trees.c.heap.gbre»
import ZlibF.Proof.«trees.c.heap.gbsym»

/-!
# trees.c: `gen_bitlen` (safe and correct)

The proof chains the loops: `bl_count` zeroing, the root `Len := 0`, the first pass (`ws_gbPass1`), and, when the
clamped depths overflowed, the repair (`ws_gbFixLoop`) and the reassignment (`ws_gbOuter`).
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB

theorem mk_eq (tk : TK) (d : DeflateState) (B0 : Array UInt16) (A : Array CtData) :
    tk.setArr { d with bl_count := B0 } A = mkP1 tk d A B0 d.opt_len d.static_len := by cases tk <;> rfl

/-- The state after the zeroing of `bl_count` and the root `Len := 0` is the start of the first pass. -/
theorem p1_init {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState} {stree : CtDataPtr} {extra : IPtr}
    {mc base ml : Int32} {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (ctx : P1Ctx h0 id tk d stree extra mc base ml hm J elems maxc L baseN xb slOpt) (B0 : Array UInt16)
    (hB0s : B0.size = 16) (hB0z : ∀ i, i < 16 → B0[i]! = 0) :
    P1State tk d hm J elems maxc L xb slOpt 0
      (mkP1 tk d (setLen (tk.arr d) (Hn d hm) 0) B0 d.opt_len d.static_len) := by
  have PS := ctx.shape
  have hm_eq := PS.hm_eq
  have hC : Clamped (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) := clK_clamped PS
  have hnT : Hn d hm < (tk.arr d).size := by
    rcases PS.kind hm (Nat.le_refl _) (by omega) with h1 | h1
    · have := PS.maxc_lt; have := ctx.nc; omega
    · have := ctx.nc; omega
  have hget : ∀ v, (setLen (tk.arr d) (Hn d hm) 0)[v]! =
      if v = Hn d hm then { (tk.arr d)[Hn d hm]! with dl := UInt16.ofNat 0 } else (tk.arr d)[v]! := fun v => by
    unfold setLen; exact getD_set _ _ v _ hnT
  refine ⟨setLen (tk.arr d) (Hn d hm) 0, B0, d.opt_len, d.static_len, rfl, ?_, ?_, ?_, hB0s, ?_, ?_, ?_, ?_, ?_⟩
  · show d.opt_len = d.opt_len + UInt64.ofNat 0
    rw [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
  · cases slOpt with
    | none => rfl
    | some sl => show d.static_len = d.static_len + UInt64.ofNat 0; rw [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
  · unfold setLen; rw [size_set!]
  · intro q h1 h2
    have : q = hm := by omega
    subst this
    rw [hget, if_pos rfl, hC.root]
  · intro i _ hi
    rw [hget, if_neg]
    · exact ctx.dad i hi
    · intro e; have := PS.inj (hm + 1 + i) hm (by omega) (by omega) (Nat.le_refl _) (by omega) e; omega
  · intro v; rw [hget]; split
    · rename_i e; subst e; rfl
    · rfl
  · intro v hv; rw [hget, if_neg]
    intro e; exact hv hm (Nat.le_refl _) (by omega) e.symm
  · intro b hb; rw [hB0z b hb]; show (0 : UInt16) = UInt16.ofNat 0; rfl


/-- What `gen_bitlen` establishes: the tree array `Tf` holds the lengths, `Bf` the counts. -/
def GBDone (tk : TK) (d : DeflateState) (hm J maxc L : Nat) (xb : Nat → Nat) (slOpt : Option (Nat → Nat))
    (e : DeflateState) : Prop :=
  ∃ (Tf : Array CtData) (Bf : Array UInt16) (O S : UInt64), e = mkP1 tk d Tf Bf O S ∧ Tf.size = (tk.arr d).size ∧
    Bf.size = 16 ∧ (∀ v : Nat, (Tf[v]!).fc = ((tk.arr d)[v]!).fc) ∧
    (∀ v : Nat, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → (Tf[v]!).dl = ((tk.arr d)[v]!).dl) ∧
    (∀ i, i < 2 * J → Hn d (hm + 1 + i) ≤ maxc →
      1 ≤ curL Tf (Hn d (hm + 1 + i)) ∧ curL Tf (Hn d (hm + 1 + i)) ≤ L) ∧
    rs (fun i => if Hn d (hm + 1 + i) ≤ maxc then 2 ^ (L - curL Tf (Hn d (hm + 1 + i))) else 0) (2 * J) = 2 ^ L ∧
    (∀ b, b < 16 → Bf[b]! = UInt16.ofNat (if b = 0 then 0 else blP (Hn d) hm maxc (curL Tf) (2 * J) b)) ∧
    O = d.opt_len + UInt64.ofNat (costP (Hn d) hm maxc (frn (tk.arr d)) (curL Tf) xb (2 * J)) ∧
    S = addOpt d.static_len (slOpt.map fun sl => costP (Hn d) hm maxc (frn (tk.arr d)) sl xb (2 * J))

/-- No overflow: the clamped depths are the lengths. -/
theorem done_noovf {tk : TK} {d : DeflateState} {hm J elems maxc L : Nat} {xb : Nat → Nat}
    {slOpt : Option (Nat → Nat)} {e : DeflateState} (PS : PShape (Hn d) hm J elems maxc) (hL1 : 1 ≤ L) (hL15 : L ≤ 15)
    (hov : ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 0)
    (hP : P1State tk d hm J elems maxc L xb slOpt (2 * J) e) : GBDone tk d hm J maxc L xb slOpt e := by
  have hm_eq := PS.hm_eq
  have hC : Clamped (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) := clK_clamped PS
  obtain ⟨Tk, Bk, O, S, he, hO, hS, hTs, hBs, hcl, hdad, hfc, hout, hbl⟩ := hP
  have hcur : ∀ i, i < 2 * J → curL Tk (Hn d (hm + 1 + i)) = clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + i)) := by
    intro i hi
    unfold curL
    rw [hcl (hm + 1 + i) (by omega) (by omega), UInt16.toNat_ofNat']
    have := hC.le_all PS (hm + 1 + i) (by omega) (by omega)
    omega
  have hcl1 : ∀ i, i < 2 * J → 1 ≤ clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + i)) := by
    intro i hi
    rw [hC.step i hi]
    have := hC.dad_le PS i hi
    omega
  have hkr := kraft_clamped PS hC hL1
  have hovC : ovfC (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) = 0 := hov
  refine ⟨Tk, Bk, O, S, he, hTs, hBs, hfc, hout, fun i hi _ => ?_, ?_, fun b hb => ?_, ?_, hS⟩
  · rw [hcur i hi]; exact ⟨hcl1 i hi, (hC.le_all PS (hm + 1 + i) (by omega) (by omega))⟩
  · unfold kraftC at hkr
    rw [hovC, Nat.pow_succ] at hkr
    rw [← show (2 : Nat) ^ L = 2 ^ L from rfl]
    have : rs (fun i => if Hn d (hm + 1 + i) ≤ maxc then 2 ^ (L - curL Tk (Hn d (hm + 1 + i))) else 0) (2 * J) =
        rs (fun i => if Hn d (hm + 1 + i) ≤ maxc then 2 ^ (L - clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + i))) else 0) (2 * J) :=
      rs_congr (fun i hi => by rw [hcur i hi])
    rw [this]; omega
  · rw [hbl b hb]
    by_cases e0 : b = 0
    · subst e0; rw [if_pos rfl]
      have := blC_zero PS hC hL1
      unfold blC at this
      rw [show blP (Hn d) hm maxc (clK (Hn d) hm elems L (2 * J)) (2 * J) 0 = 0 from this]
    · rw [if_neg e0]
      have e1 : blP (Hn d) hm maxc (clK (Hn d) hm elems L (2 * J)) (2 * J) b = blP (Hn d) hm maxc (curL Tk) (2 * J) b := by
        unfold blP; apply rs_congr; intro i hi; rw [hcur i hi]
      rw [e1]
  · rw [hO]
    have e1 : costP (Hn d) hm maxc (frn (tk.arr d)) (clK (Hn d) hm elems L (2 * J)) xb (2 * J) =
        costP (Hn d) hm maxc (frn (tk.arr d)) (curL Tk) xb (2 * J) := by
      unfold costP; apply rs_congr; intro i hi; rw [hcur i hi]
    rw [e1]


theorem mkP2_mkP1 (tk : TK) (d Tk Bk O S Tc O') : mkP2 tk (mkP1 tk d Tk Bk O S) Tc O' = mkP1 tk d Tc Bk O' S := by
  cases tk <;> rfl

@[simp] theorem Hn_mkP1 (tk : TK) (d Tk Bk O S) : Hn (mkP1 tk d Tk Bk O S) = Hn d := by
  funext q; unfold Hn; rw [mkP1_heap]

/-- The facts about the state `ef` after the repair that the reassignment needs. -/
theorem rctx_of {tk : TK} {d e2 ef : DeflateState} {hm J elems maxc L : Nat} {c' : Nat → Nat} {ov : Int32} {Tk Bk O S}
    (he2 : e2 = mkP1 tk d Tk Bk O S) (hTs : Tk.size = (tk.arr d).size)
    (PS : PShape (Hn d) hm J elems maxc) (hsz : d.heap.size = 573) (hnn : ∀ q, hm ≤ q → q < 573 → 0 ≤ (d.heap[q]!).toInt)
    (hnc : elems + J ≤ (tk.arr d).size) (htsz : (tk.arr d).size ≤ 600) (hL1 : 1 ≤ L) (hL15 : L ≤ 15)
    (hfix : FixInvX L (nLeaves (Hn d) hm J maxc) 0 ov c' e2 ef) :
    RCtx tk ef hm J elems maxc L c' := by
  obtain ⟨-, -, hc0, -, -, -, htot, Bc, hef⟩ := hfix
  have hef' : ef = mkP1 tk d Tk Bc O S := by rw [hef, he2, bl_mkP1]
  have hh : ef.heap = d.heap := by rw [hef', mkP1_heap]
  have hHn : Hn ef = Hn d := by rw [hef', Hn_mkP1]
  refine ⟨by rw [hh]; exact hsz, fun q h1 h2 => by rw [hh]; exact hnn q h1 h2, by rw [hHn]; exact PS, ?_, ?_, hL1, hL15, hc0, by rw [hHn]; exact htot⟩
  · rw [hef', tk_arr_mkP1, hTs]; exact hnc
  · rw [hef', tk_arr_mkP1, hTs]; exact htsz


theorem curL_clK {tk : TK} {d : DeflateState} {hm J elems maxc L : Nat} (PS : PShape (Hn d) hm J elems maxc)
    {Tk : Array CtData} (hL15 : L ≤ 15)
    (hcl : ∀ q, hm ≤ q → q ≤ hm + 2 * J → (Tk[Hn d q]!).dl = UInt16.ofNat (clK (Hn d) hm elems L (2 * J) (Hn d q))) :
    ∀ i, i < 2 * J → curL Tk (Hn d (hm + 1 + i)) = clK (Hn d) hm elems L (2 * J) (Hn d (hm + 1 + i)) := by
  have hm_eq := PS.hm_eq
  have hC : Clamped (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) := clK_clamped PS
  intro i hi
  unfold curL
  rw [hcl (hm + 1 + i) (by omega) (by omega), UInt16.toNat_ofNat']
  have := hC.le_all PS (hm + 1 + i) (by omega) (by omega)
  omega


theorem reinit {tk : TK} {d e2 ef : DeflateState} {hm J elems maxc L : Nat} {xb : Nat → Nat}
    {slOpt : Option (Nat → Nat)} {c' : Nat → Nat} {ov : Int32}
    (PS : PShape (Hn d) hm J elems maxc) (hL15 : L ≤ 15) (hsz : d.heap.size = 573)
    (hP : P1State tk d hm J elems maxc L xb slOpt (2 * J) e2)
    (hfix : FixInvX L (nLeaves (Hn d) hm J maxc) 0 ov c' e2 ef) :
    ReSt tk ef hm J maxc L xb c' d.opt_len 573 L (c' L) ef := by
  have hm_eq := PS.hm_eq
  obtain ⟨Tk, Bk, O, S, he2, hO, hS, hTs, hBs, hcl, hdad, hfc, hout, hbl⟩ := hP
  obtain ⟨-, -, hc0, -, -, -, htot, Bc, hef⟩ := hfix
  have hef' : ef = mkP1 tk d Tk Bc O S := by rw [hef, he2, bl_mkP1]
  have hcur := curL_clK (tk := tk) (elems := elems) (L := L) PS hL15 (fun q h1 h2 => hcl q h1 (by omega))
  have hfr : frn Tk = frn (tk.arr d) := by funext v; unfold frn; rw [hfc v]
  refine ⟨tk.arr ef, ef.opt_len, by cases tk <;> rfl, rfl, by omega, Nat.le_refl _, Nat.le_refl _, ?_, fun v => rfl,
    fun v hv => rfl, fun x => ?_, ?_⟩
  · rw [hef', tk_arr_mkP1, Hn_mkP1]
    show O = _
    rw [hO, hfr]
    congr 2
    unfold costP; apply rs_congr; intro i hi; rw [hcur i hi]
  · have h0 : scnt (Hn ef) hm maxc J 573 (curL (tk.arr ef)) x = 0 := by
      unfold scnt; exact rs_eq_zero (fun i hi => by rw [if_neg (fun h => by omega)])
    rw [h0]
    by_cases e1 : L < x ∧ x ≤ L
    · omega
    · rw [if_neg e1]; by_cases e2 : x = L
      · rw [if_pos e2, Nat.sub_self]
      · rw [if_neg e2]
  · have h0 : stot (Hn ef) hm maxc J 573 = 0 := by
      unfold stot; exact rs_eq_zero (fun i hi => by rw [if_neg (fun h => by omega)])
    rw [h0, Nat.sub_self]
    unfold Aab
    rw [rs_eq_zero (fun x hx => by rw [if_neg (by omega)])]


/-- Overflow: the lengths after the reassignment. -/
theorem done_ovf {tk : TK} {d e2 ef efin : DeflateState} {hm J elems maxc L : Nat} {xb : Nat → Nat}
    {slOpt : Option (Nat → Nat)} {c' : Nat → Nat} {ov : Int32} {hc : Nat}
    (PS : PShape (Hn d) hm J elems maxc) (hL1 : 1 ≤ L) (hL15 : L ≤ 15)
    (hP : P1State tk d hm J elems maxc L xb slOpt (2 * J) e2)
    (hfix : FixInvX L (nLeaves (Hn d) hm J maxc) 0 ov c' e2 ef)
    (hre : ReSt tk ef hm J maxc L xb c' d.opt_len hc 0 0 efin) : GBDone tk d hm J maxc L xb slOpt efin := by
  have hm_eq := PS.hm_eq
  obtain ⟨Tk, Bk, O, S, he2, hO, hS, hTs, hBs, hcl, hdad, hfc, hout, hbl⟩ := hP
  obtain ⟨hfv, hBcI, hc0, hchi, hkc, -, htot, Bc, hef⟩ := hfix
  have hef' : ef = mkP1 tk d Tk Bc O S := by rw [hef, he2, bl_mkP1]
  obtain ⟨Tc, O2, hefin, hTcs, hc1, hc2, -, hO2, hfcc, houtc, hsc, hst⟩ := hre
  have hefin' : efin = mkP1 tk d Tc Bc O2 S := by rw [hefin, hef', mkP2_mkP1]
  have hHn : Hn ef = Hn d := by rw [hef', Hn_mkP1]
  have hTarr : tk.arr ef = Tk := by rw [hef', tk_arr_mkP1]
  have hfr : frn Tk = frn (tk.arr d) := by funext v; unfold frn; rw [hfc v]
  rw [hHn] at hsc hst hO2
  rw [hTarr, hfr] at hO2
  rw [hTarr] at hTcs
  have hmL : ∀ i, i < 2 * J → Hn d (hm + 1 + i) ≤ maxc → hc ≤ hm + 1 + i := by
    intro i hi hl
    by_cases h : hc ≤ hm + 1 + i
    · exact h
    · exfalso
      have h1 := stot_utot (Hn d) hm maxc J hc
      rw [hst] at h1
      simp only [Nat.sub_zero] at h1
      have h2 : Aab c' L 0 = rs c' (L + 1) := Aab_zero c' L hc0
      have h3 : 1 ≤ utot (Hn d) hm maxc J hc := by
        have := le_rs (F := fun j => if hm + 1 + j < hc ∧ Hn d (hm + 1 + j) ≤ maxc then 1 else 0) (n := 2 * J) (i := i) hi
        unfold utot
        rw [if_pos ⟨by omega, hl⟩] at this
        exact this
      omega
  have hcnt : ∀ x, blP (Hn d) hm maxc (curL Tc) (2 * J) x = if 0 < x ∧ x ≤ L then c' x else 0 := by
    intro x
    have h := hsc x
    have e1 : scnt (Hn d) hm maxc J hc (curL Tc) x = blP (Hn d) hm maxc (curL Tc) (2 * J) x := by
      unfold scnt blP; apply rs_congr; intro i hi
      by_cases hl : Hn d (hm + 1 + i) ≤ maxc
      · by_cases hx : curL Tc (Hn d (hm + 1 + i)) = x
        · simp [hl, hx, hmL i hi hl]
        · simp [hx]
      · rw [if_neg (fun h => hl h.2.1), if_neg (fun h => hl h.1)]
    rw [← e1, h]
    by_cases e : 0 < x ∧ x ≤ L
    · simp [e]
    · by_cases e0 : x = 0
      · subst e0; simp [hc0]
      · have e' : ¬ (0 < x ∧ x ≤ L) := e
        simp [e', e0]
  have hrange : ∀ i, i < 2 * J → Hn d (hm + 1 + i) ≤ maxc →
      1 ≤ curL Tc (Hn d (hm + 1 + i)) ∧ curL Tc (Hn d (hm + 1 + i)) ≤ L := by
    intro i hi hl
    have h1 := hcnt (curL Tc (Hn d (hm + 1 + i)))
    have h2 : 1 ≤ blP (Hn d) hm maxc (curL Tc) (2 * J) (curL Tc (Hn d (hm + 1 + i))) := by
      have := le_rs (F := fun j => if Hn d (hm + 1 + j) ≤ maxc ∧ curL Tc (Hn d (hm + 1 + j)) = curL Tc (Hn d (hm + 1 + i)) then 1 else 0)
        (n := 2 * J) (i := i) hi
      unfold blP
      rw [if_pos ⟨hl, rfl⟩] at this
      exact this
    by_cases e : 0 < curL Tc (Hn d (hm + 1 + i)) ∧ curL Tc (Hn d (hm + 1 + i)) ≤ L
    · exact ⟨e.1, e.2⟩
    · rw [if_neg e] at h1; omega
  have hBcs : Bc.size = 16 := by have := hBcI.1; rw [hef', mkP1_bl_count] at this; exact this
  have hBcv : ∀ b, b < 16 → Bc[b]! = UInt16.ofNat (c' b) := by
    intro b hb; have := hBcI.2 b hb; rw [hef', mkP1_bl_count] at this; exact this
  refine ⟨Tc, Bc, O2, S, hefin', by rw [hTcs, hTs], hBcs, ?_, ?_, hrange, ?_, fun b hb => ?_, ?_, hS⟩
  · intro v; rw [hfcc v, hTarr]; exact hfc v
  · intro v hv; rw [houtc v (fun q h1 h2 => by rw [hHn]; exact hv q h1 h2), hTarr]; exact hout v hv
  · exact kraft_of_counts (Hn d) hm J maxc L (curL Tc) c' hc0 (by rw [hkc]; rfl) (fun i hi hl => (hrange i hi hl).2) hcnt
  · rw [hBcv b hb]
    by_cases e0 : b = 0
    · subst e0; rw [if_pos rfl, hc0]
    · rw [if_neg e0, hcnt b]
      by_cases e : 0 < b ∧ b ≤ L
      · rw [if_pos e]
      · rw [if_neg e, hchi b (by omega)]
  · rw [hO2]


@[simp] theorem mkP1_heap_max (tk : TK) (d Tk Bk O S) : (mkP1 tk d Tk Bk O S).heap_max = d.heap_max := by cases tk <;> rfl

theorem ws_ldTreeDesc {h0 : Heap} {id : Nat} {d : DeflateState} (r : TreeDescRef) (dd : TreeDesc)
    (h : r.get (setD h0 id d) = some dd) : WS h0 id (ldTreeDesc (some r)) d (fun v d' => v = dd ∧ d' = d) :=
  WS.of_eq (ldTreeDesc_ok h) ⟨rfl, rfl⟩

theorem ws_ldStaticTreeDesc {h0 : Heap} {id : Nat} {d : DeflateState} (sref : StaticTreeDescRef) (sd : StaticTreeDesc)
    (h : StaticTreeDescRef.get h0 sref = some sd) :
    WS h0 id (ldStaticTreeDesc (some sref)) d (fun v d' => v = sd ∧ d' = d) :=
  WS.of_eq (ldStaticTreeDesc_ok (by cases sref <;> simpa [StaticTreeDescRef.get, setD] using h)) ⟨rfl, rfl⟩

/-- **`gen_bitlen`.** -/
theorem ws_gen_bitlen {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState} {r : TreeDescRef} {sref : StaticTreeDescRef}
    {dd : TreeDesc} {sd : StaticTreeDesc} {hm J elems maxc L baseN : Nat} {xb : Nat → Nat}
    {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length hm J elems maxc L baseN
      xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ d' => GBDone tk d hm J maxc L xb slOpt d') := by
  have PS := ctx.shape
  have hm_eq := PS.hm_eq
  rw [gen_bitlen_eq]
  unfold gbTop
  simp only []
  refine WS.bind' (ws_ldTreeDesc r dd hdd) fun dd' e1 ⟨hdd', he1⟩ => ?_
  subst e1; subst dd'
  rw [hstat]
  refine WS.bind' (ws_ldStaticTreeDesc sref sd hsd) fun sd' e1 ⟨hsd', he1⟩ => ?_
  subst e1; subst sd'
  rw [htree]
  refine WS.bind' (ws_gbZero d ctx.bsz) fun _ e1 ⟨B0, he1, hB0s, hB0z⟩ => ?_
  subst e1
  have hhsz := ctx.hsz
  have hnn0 := ctx.hnn hm (Nat.le_refl _) (by omega)
  have hnT : Hn d hm < (tk.arr d).size := by
    rcases PS.kind hm (Nat.le_refl _) (by omega) with h1 | h1
    · have := PS.maxc_lt; have := ctx.nc; omega
    · have := ctx.nc; omega
  have h1i : (1 : Int32).toInt = 1 := rfl
  refine WS.bind' ws_rd fun dz e1 ⟨hz, he1⟩ => ?_
  subst e1; subst hz
  refine WS.bind' (ws_heapAt d.heap_max (by omega) (by show _ < (d.heap.size : Int); omega)) fun r0 e1 ⟨hr0, he1⟩ => ?_
  subst e1
  have hr0n : r0.toInt = (Hn d hm : Int) := by
    rw [hr0]; show (d.heap[d.heap_max.toInt.toNat]!).toInt = _
    have : d.heap_max.toInt.toNat = hm := by omega
    rw [this]; unfold Hn; omega
  refine WS.bind' (ws_setDl tk r0.toInt 0 (by omega) (by rw [tk_arr_bl_count]; omega)) fun _ e1 he1 => ?_
  have hr0nat : r0.toInt.toNat = Hn d hm := by omega
  rw [tk_arr_bl_count, hr0nat] at he1
  change e1 = tk.setArr { d with bl_count := B0 } (setLen (tk.arr d) (Hn d hm) 0) at he1
  rw [mk_eq] at he1
  subst e1
  refine WS.bind' ws_rd fun dz e1 ⟨hz, he1⟩ => ?_
  subst e1; subst hz
  refine WS.bind' (ws_iadd _ 1 (by simp only [mkP1_heap_max]; omega) (by simp only [mkP1_heap_max]; omega))
    fun h0v e1 ⟨hh0, he1⟩ => ?_
  subst e1
  simp only [mkP1_heap_max] at hh0
  have hp1 := ws_gbPass1 ctx h0v (by omega) _ (p1_init ctx B0 hB0s hB0z)
  refine WS.bind' hp1 fun x e2 ⟨hx1, hx2, hP⟩ => ?_
  have hC : Clamped (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) := clK_clamped PS
  have hL1 := ctx.L1
  have hL15 := ctx.L15
  have hmlv := ctx.mlv
  by_cases hov : ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 0
  · refine WS.ite' (fun _ => ?_) (fun hh => absurd (by
      have : x.snd.toInt = 0 := by rw [hx2, hov]; rfl
      have : x.snd = 0 := Int32.toInt_inj.mp (by rw [this]; rfl)
      simp [this]) hh)
    exact WS.pure' (done_noovf PS hL1 hL15 hov hP)
  · refine WS.ite' (fun hh => absurd ?_ hov) (fun _ => ?_)
    · have : x.snd = 0 := by simpa using hh
      have h1 : x.snd.toInt = 0 := by rw [this]; rfl
      rw [hx2] at h1; omega
    · -- overflow: repair, then reassign
      have hovpos : 0 < ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) := Nat.pos_of_ne_zero hov
      have hovE := blC_top PS hC hL1
      have hkr := kraft_clamped PS hC hL1
      have hex := exactC_pos PS hC hL1 hovpos
      obtain ⟨R, hR⟩ : ∃ R, ovfC (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) = 2 * (R + 1) :=
        ⟨ovfC (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) / 2 - 1, by
          have := hovE.1; have : 0 < ovfC (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) := hovpos
          omega⟩
      have hNL := nLeaves_le PS
      have hmc := PS.maxc_lt
      have hnc := ctx.nc
      have htsz := ctx.tsz
      obtain ⟨Tk, Bk, O, S, he2, hO, hS, hTs, hBs, hcl, hdad, hfc, hout, hbl⟩ := hP
      have hP' : P1State tk d hm J elems maxc L xb slOpt (2 * J) e2 :=
        ⟨Tk, Bk, O, S, he2, hO, hS, hTs, hBs, hcl, hdad, hfc, hout, hbl⟩
      let c0 : Nat → Nat := fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) b
      have hI : FixInvX L (nLeaves (Hn d) hm J maxc) (R + 1) x.snd c0 e2 e2 := by
        refine ⟨by rw [hx2]; show ((ovfC (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) : Nat) : Int) = _; rw [hR]; omega, ?_, blC_zero PS hC hL1, fun b hb => blC_high PS hC b hb, ?_, ?_, blC_total PS hC, e2.bl_count, rfl⟩
        · rw [he2]; simp only [BcIs, mkP1_bl_count]
          exact ⟨hBs, fun b hb => (hbl b hb).trans rfl⟩
        · show kc c0 L = _
          unfold kc
          have := kraftC_eq PS hC
          rw [← this]
          unfold kraftC at hkr ⊢
          have hp : ovfC (Hn d) hm J elems L (clK (Hn d) hm elems L (2 * J)) = 2 * (R + 1) := hR
          rw [Nat.pow_succ] at hkr
          omega
        · have := hovE.2
          show R + 1 + 1 ≤ blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) L
          omega
      have hNLa : nLeaves (Hn d) hm J maxc ≤ 2 ^ L := by omega
      have hNLb : nLeaves (Hn d) hm J maxc ≤ 1000 := by omega
      refine WS.bind' (ws_gbFixLoop (h0 := h0) (id := id) e2 sd.max_length L (nLeaves (Hn d) hm J maxc) R hmlv hL1 hL15
        hNLa hNLb x.snd c0 e2 hI) fun ov' ef hfix => ?_
      have rctx := rctx_of he2 hTs PS ctx.hsz ctx.hnn ctx.nc ctx.tsz hL1 hL15 hfix
      have hR0 := reinit PS hL15 ctx.hsz hP' hfix
      refine WS.bind' (ws_gbOuter rctx hfix.2.1 dd.max_code sd.max_length ctx.mcv hmlv x.fst hx1 ef hR0)
        fun r efin ⟨hc, hre⟩ => ?_
      exact WS.pure' (done_ovf PS hL1 hL15 hP' hfix hre)


/-- **`gen_bitlen`: correct.** On the heap `h` with the deflate state `id` (the record `d`), called on the tree
descriptor `r` (one of `l_desc`, `d_desc`, `bl_desc` of the same state) whose `dyn_tree` is the tree array `tk` of
that state, `max_code = maxc`, and whose static descriptor `sd` has `elems`, `max_length = L`, `extra_base = baseN`:

* the tree is laid out as `build_tree` leaves it (`P1Ctx.shape`: `J ≥ 1` internal nodes `elems .. elems+J-1`, the root
  at `heap[heap_max]`, `heap_max = hm`, the node `elems + j` stored below its children at `572 - 2j`, `571 - 2j`, the other
  entries symbols `≤ maxc < elems`, all distinct) and the `Dad` of each non-root node is `dadP elems position`;
* `1 ≤ L ≤ 15` (`bl_count` has 16 entries), `elems ≤ 2^L` (so a node can always be found below the limit: F8), the tree
  array has `elems + J ≤ size ≤ 600` entries, the heap array has 573, `bl_count` 16;
* the extra bits (`xb`) and the static lengths (`slOpt`, none when `static_tree` is null) are read from static arrays
  that are large enough for the symbols `≤ maxc`.

The call runs to the end without a fault, only the tree array, `bl_count`, `opt_len` and `static_len` change, and
(`GBDone`) the leaves get lengths in `[1, L]` forming a complete prefix code (`Σ 2^(L - len) = 2^L`), `bl_count[b]` is the number
of leaves of length `b` (`bl_count[0] = 0`), and `opt_len`, `static_len` grow by `Σ freq * (len + extra bits)`, resp. the same with
the static lengths (modulo `2^64`). -/
theorem gen_bitlen_correct {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) {tk : TK}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get h = some dd) (hsd : StaticTreeDescRef.get h sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length hm J elems maxc L baseN
      xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) :
    ∃ d', gen_bitlen (Sp id) (some r) h = .ok ((), setD h id d') ∧ GBDone tk d hm J maxc L xb slOpt d' := by
  have hdd' : r.get (setD h id d) = some dd := by rw [setD_self hd]; exact hdd
  obtain ⟨_, d', e, hq⟩ := ws_gen_bitlen (h0 := h) hdd' hsd hstat htree ctx hHM hel
  rw [setD_self hd] at e
  exact ⟨d', e, hq⟩

/-- **`gen_bitlen` does not fault.** Same preconditions as `gen_bitlen_correct` (they are what `build_tree` establishes
before the call): the call returns normally, every index into `heap`, `bl_count` and the tree is inside its array
(including the search `while (bl_count[bits] == 0) bits--`, which stays at `bits ≥ 1`, and the scan `heap[--h]`, which
stays above the root). -/
theorem gen_bitlen_safe {h : Heap} {id : Nat} {d : DeflateState} (hd : h.dstates id = some d) {tk : TK}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get h = some dd) (hsd : StaticTreeDescRef.get h sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length hm J elems maxc L baseN
      xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) :
    ∃ h', gen_bitlen (Sp id) (some r) h = .ok ((), h') := by
  obtain ⟨d', e, -⟩ := gen_bitlen_correct hd hdd hsd hstat htree ctx hHM hel
  exact ⟨_, e⟩

end Zlib.Trees.Proofs
