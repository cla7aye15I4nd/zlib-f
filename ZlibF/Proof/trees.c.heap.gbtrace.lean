import ZlibF.Proof.«trees.c.heap.gbtop»
import ZlibF.Proof.«trees.c.heap.gbfix-model»

/-! # Actual bit-length construction retains its first-pass and repair data -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- Data from the actual source stages, on their actual returned states.
The no-overflow branch retains the exact clamped first pass. The overflow
branch retains the precise initial histogram, number of repair rounds,
model count vector and source reassignment result. Rank-wise monotonicity
of the reassigned leaf lengths is a separate execution obligation. -/
def GBStageTrace (tk : TK) (d : DeflateState) (hm J elems maxc L : Nat)
    (xb : Nat → Nat) (slOpt : Option (Nat → Nat)) (result : DeflateState) : Prop :=
  (ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 0 ∧
    P1State tk d hm J elems maxc L xb slOpt (2 * J) result) ∨
  ∃ (R : Nat) (ov : Int32) (first repaired : DeflateState) (hc : Nat),
    ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 2 * (R + 1) ∧
    P1State tk d hm J elems maxc L xb slOpt (2 * J) first ∧
    FixInvX L (nLeaves (Hn d) hm J maxc) 0 ov
      (HuffmanAbstract.repairIter L (R + 1)
        (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) b)) first repaired ∧
    ReSt tk repaired hm J maxc L xb
      (HuffmanAbstract.repairIter L (R + 1)
        (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) b)) d.opt_len hc 0 0 result

/-- The complete actual gen_bitlen preserves the old safety, Kraft and
cost conclusions and also records the exact source stage data needed to
refine length limiting. All callees are proved executions. -/
theorem ws_gen_bitlen_trace {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState} {r : TreeDescRef} {sref : StaticTreeDescRef}
    {dd : TreeDesc} {sd : StaticTreeDesc} {hm J elems maxc L baseN : Nat} {xb : Nat → Nat}
    {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = Ptr.ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length hm J elems maxc L baseN
      xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) :
    WS h0 id (gen_bitlen (Sp id) (some r)) d (fun _ result => GBDone tk d hm J maxc L xb slOpt result ∧
      GBStageTrace tk d hm J elems maxc L xb slOpt result) := by
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
    exact WS.pure' ⟨done_noovf PS hL1 hL15 hov hP, Or.inl ⟨hov, hP⟩⟩
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
      refine WS.bind' (ws_gbFixLoop_repair_model (h0 := h0) (id := id) e2 sd.max_length L (nLeaves (Hn d) hm J maxc) R hmlv hL1 hL15
        hNLa hNLb x.snd c0 e2 hI) fun ov' ef hfix => ?_
      have rctx := rctx_of he2 hTs PS ctx.hsz ctx.hnn ctx.nc ctx.tsz hL1 hL15 hfix
      have hR0 := reinit PS hL15 ctx.hsz hP' hfix
      refine WS.bind' (ws_gbOuter rctx hfix.2.1 dd.max_code sd.max_length ctx.mcv hmlv x.fst hx1 ef hR0)
        fun r efin ⟨hc, hre⟩ => ?_
      refine WS.pure' ⟨done_ovf PS hL1 hL15 hP' hfix hre,
        Or.inr ⟨R, ov', e2, ef, hc, ?_, hP', hfix, hre⟩⟩
      exact hR


end Zlib.Trees.Proofs
