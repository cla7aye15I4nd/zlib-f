import ZlibF.Proof.«trees.c.scan-tree»
import ZlibF.Math.DeflateBlIndex

/-! # trees.c: constructing the bit-length alphabet

The descending index search follows the reference EmitBlTree structure.
All called-function behavior comes from proofs about the actual translation.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The actual two scans at the start of build_bl_tree. -/
def blScanPair (s : DeflateStatePtr) : M Unit := do
  scan_tree s (← pLtree s) (← rd s).l_desc.max_code
  scan_tree s (← pDtree s) (← rd s).d_desc.max_code

/-- The actual bit-length construction after frequency scanning. -/
def blBuild (s : DeflateStatePtr) : M Unit := do
  blScanPair s
  build_tree s (← pBldesc s)

def blIndexBody (s : DeflateStatePtr) : Int32 × Bool → M (Int32 × Bool) :=
  fun (mb, _) => do
    if (← getDl (← pBltree s) (u8i (← blOrder mb.toInt)).toInt) != 0 then return (mb, true)
    pure (← isub mb 1, false)

/-- The actual descending index search, including its break flag. -/
def blIndexLoop (s : DeflateStatePtr) : M (Int32 × Bool) :=
  cwhile (fun (mb, brk) => pure (!brk && decide (mb.toInt ≥ 3), (mb, brk)))
    (blIndexBody s) (BL_CODES - 1, false)

def blFinish (s : DeflateStatePtr) : M Int32 := do
  let (mb, _) ← blIndexLoop s
  md s fun d => { d with opt_len := d.opt_len + (3 * (i2ul mb + 1) + 5 + 5 + 4) }
  return mb

/-- Whole-function source equality, in the original call and statement order. -/
theorem build_bl_tree_eq (s : DeflateStatePtr) :
    build_bl_tree s = (do blBuild s; blFinish s) := by
  unfold build_bl_tree blBuild blScanPair blFinish blIndexLoop blIndexBody
  simp only [M_bind_assoc, M_pure_bind]

/-- Literal and distance data needed by the actual scans. This is a state
representation; it contains no callee specification or execution premise. -/
structure BLInput (d : DeflateState) : Prop where
  l0 : 0 ≤ d.l_desc.max_code.toInt
  l286 : d.l_desc.max_code.toInt < 286
  d0 : 0 ≤ d.d_desc.max_code.toInt
  d30 : d.d_desc.max_code.toInt < 30
  llen : ∀ i ≤ d.l_desc.max_code.toInt.toNat, d.dyn_ltree[i]!.dl.toNat ≤ 15
  dlen : ∀ i ≤ d.d_desc.max_code.toInt.toNat, d.dyn_dtree[i]!.dl.toNat ≤ 15

/-- The source alphabets with their actual sentinel writes. -/
def blScannedState (d : DeflateState) (B : Array CtData) : DeflateState :=
  { d with
    dyn_ltree := scGuard d.dyn_ltree d.l_desc.max_code.toInt.toNat,
    dyn_dtree := scGuard d.dyn_dtree d.d_desc.max_code.toInt.toNat, bl_tree := B }

/-- Mathematical frequency increments of the two source alphabets. -/
def blScanCount (d : DeflateState) (k : Nat) : Nat :=
  Out.scanFreqUpTo (Out.guarded (fun i => d.dyn_ltree[i]!.dl.toNat) d.l_desc.max_code.toInt.toNat)
    (d.l_desc.max_code.toInt.toNat + 1) k +
  Out.scanFreqUpTo (Out.guarded (fun i => d.dyn_dtree[i]!.dl.toNat) d.d_desc.max_code.toInt.toNat)
    (d.d_desc.max_code.toInt.toNat + 1) k

/-- Both actual scans compose on one live heap. Their exact record effects
retain both sentinels and sum their 16-bit frequency additions. -/
theorem bl_scan_pair {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (e : DeflateState) (B : Array CtData),
      blScanPair (Sp id) h = .ok ((), setD h id e) ∧ e = blScannedState d B ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d ∧
      B.size = d.bl_tree.size ∧ (∀ k : Nat, B[k]!.dl = d.bl_tree[k]!.dl) ∧
      ∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat (blScanCount d k) := by
  obtain ⟨e1, B1, hr1, he1, hI1, hout1, hB1, hdl1, hfc1⟩ :=
    scan_tree_preserves hI .lit (by decide +kernel) d.l_desc.max_code hin.l0 hin.l286 hin.llen
  have hdesc : e1.d_desc = d.d_desc := by rw [he1]; rfl
  have htree : e1.dyn_dtree = d.dyn_dtree := by rw [he1]; rfl
  have hdlen : ∀ i ≤ e1.d_desc.max_code.toInt.toNat, e1.dyn_dtree[i]!.dl.toNat ≤ 15 := by
    rw [hdesc, htree]
    exact hin.dlen
  obtain ⟨e2, B2, hr2, he2, hI2, hout2, hB2, hdl2, hfc2⟩ :=
    scan_tree_preserves hI1 .dist (by decide +kernel) e1.d_desc.max_code
      (by rw [hdesc]; exact hin.d0) (by rw [hdesc]; exact hin.d30) hdlen
  have heB1 : e1.bl_tree = B1 := by rw [he1]
  rw [setD_setD] at hr2 hI2
  simp only [TK.ref] at hr1 hr2
  refine ⟨e2, B2, ?_, ?_, hI2, hout2.trans hout1, ?_, ?_, ?_⟩
  · have hp1 := Out.pLtree_run hI.base.dstate
    have hd1 := Out.rd_run hI.base.dstate
    have hp2 := Out.pDtree_run (setD_dstates_same h id e1)
    have hd2 := Out.rd_run (setD_dstates_same h id e1)
    unfold blScanPair
    rw [bind_app, hp1]
    simp only []
    rw [bind_app, hd1]
    simp only []
    rw [bind_app, hr1]
    simp only []
    rw [bind_app, hp2]
    simp only []
    rw [bind_app, hd2]
    exact hr2
  · rw [he2, he1]
    rfl
  · rw [hB2, heB1, hB1]
  · intro k
    rw [hdl2 k, heB1, hdl1 k]
  · intro k
    rw [hfc2 k, heB1, hfc1 k]
    simp only [TK.arr, hdesc, htree, blScanCount, UInt16.ofNat_add, UInt16.add_assoc]

/-- The bit-length symbol at each rank of the actual fixed permutation. -/
def blUsed (d : DeflateState) (m : Nat) : Bool :=
  d.bl_tree[bl_order[m]!.toNat]!.dl != 0

theorem bl_order_bound (m : Nat) (hm : m < 19) : bl_order[m]!.toNat < 19 := by
  have h : ∀ i : Fin 19, bl_order[i.val]!.toNat < 19 := by decide +kernel
  exact h ⟨m, hm⟩

theorem ws_blPtr {h0 : Heap} {id : Nat} {d : DeflateState} :
    WS h0 id (pBltree (Sp id)) d (fun p e => p = .ref (.dstate_bl_tree id) 0 ∧ e = d) := by
  unfold pBltree
  refine WS.bind' ws_sid fun i e ⟨hi, he⟩ => ?_
  subst i; subst e
  exact WS.pure' ⟨rfl, rfl⟩

theorem ws_blOrder {h0 : Heap} {id : Nat} {d : DeflateState} (i : Int)
    (hi0 : 0 ≤ i) (hi19 : i < 19) :
    WS h0 id (blOrder i) d (fun v e => v = bl_order[i.toNat]! ∧ e = d) := by
  unfold blOrder
  rw [ite_eq_left ⟨hi0, hi19⟩]
  exact WS.pure' ⟨rfl, rfl⟩

/-- The actual read/test/decrement body does not change the heap. -/
theorem ws_blIndexBody {h0 : Heap} {id : Nat} {d : DeflateState} (mb : Int32) (m : Nat)
    (hm : mb.toInt = m) (hm3 : 3 ≤ m) (hm18 : m ≤ 18) (hB : 19 ≤ d.bl_tree.size) :
    WS h0 id (blIndexBody (Sp id) (mb, false)) d (fun r e => e = d ∧
      ((r.1 = mb ∧ r.2 = true ∧ blUsed d m = true) ∨
       (r.1.toInt = (m : Int) - 1 ∧ r.2 = false ∧ blUsed d m = false))) := by
  have hmN : mb.toInt.toNat = m := by omega
  unfold blIndexBody
  refine WS.bind' ws_blPtr fun p e ⟨hp, he⟩ => ?_
  subst p; subst e
  refine WS.bind' (ws_blOrder mb.toInt (by omega) (by omega)) fun ord e ⟨ho, he⟩ => ?_
  subst e; subst ord
  rw [hmN]
  have hu : (u8i bl_order[m]!).toInt = bl_order[m]!.toNat := by
    unfold u8i
    have hbyte := (bl_order[m]!).toNat_lt
    exact Out.i32_ofInt_toInt (by omega) (by omega)
  have hi := bl_order_bound m (by omega)
  refine WS.bind' (ws_getDl .bl (u8i bl_order[m]!).toInt (by omega)
    (by change (u8i bl_order[m]!).toInt < d.bl_tree.size; omega)) fun len e ⟨hlen, he⟩ => ?_
  subst e; subst len
  have hidx : (u8i bl_order[m]!).toInt.toNat = bl_order[m]!.toNat := by rw [hu]; rfl
  simp only [hidx]
  change WS h0 id (if blUsed d m = true then pure (mb, true) else do pure (← isub mb 1, false)) d _
  by_cases hz : blUsed d m = true
  · rw [ite_eq_left hz]
    exact WS.pure' ⟨rfl, Or.inl ⟨rfl, rfl, hz⟩⟩
  · rw [ite_eq_right hz]
    have hone : (1 : Int32).toInt = 1 := rfl
    refine WS.bind' (ws_isub mb 1 (by omega) (by omega)) fun mb1 e ⟨hmb1, he⟩ => ?_
    subst e
    exact WS.pure' ⟨rfl, Or.inr ⟨by dsimp only; omega, rfl, Bool.eq_false_iff.mpr hz⟩⟩

/-- Complete actual descending search, with its exact mathematical maximum.
The generic search can return two. A four-entry header requires the separate
caller-history argument showing a used rank at least three. -/
theorem ws_blIndexLoop {h0 : Heap} {id : Nat} {d : DeflateState} (hB : 19 ≤ d.bl_tree.size) :
    WS h0 id (blIndexLoop (Sp id)) d (fun r e =>
      e = d ∧ r.1.toInt = Math.blMaxIdx (blUsed d) 18) := by
  let R := Math.blMaxIdx (blUsed d) 18
  let Inv : Int32 × Bool → DeflateState → Prop := fun r e =>
    e = d ∧ ∃ m : Nat, 2 ≤ m ∧ m ≤ 18 ∧ r.1.toInt = m ∧
      ((r.2 = false ∧ Math.blMaxIdx (blUsed d) m = R) ∨ (r.2 = true ∧ m = R))
  unfold blIndexLoop
  refine WS.cwhile2 Inv (fun r _ => if r.2 then 0 else r.1.toInt.toNat) _ ?_
    ⟨rfl, 18, by omega, by omega, rfl, Or.inl ⟨rfl, rfl⟩⟩ (by simp only [fuel]; decide +kernel)
  rintro ⟨mb, brk⟩ e ⟨he, m, hm2, hm18, hm, hcase⟩
  subst e
  dsimp only at hm hcase ⊢
  rcases hcase with ⟨hbrk, hmax⟩ | ⟨hbrk, hmax⟩
  · subst brk
    by_cases hm3 : 3 ≤ m
    · refine WS.pure' (Or.inr ⟨by simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq]; omega, ?_⟩)
      refine WS.mono (ws_blIndexBody mb m hm hm3 hm18 hB) ?_
      rintro r e ⟨he, hbranch⟩
      subst e
      rcases hbranch with hused | hzero
      · obtain ⟨hr, hb, hu⟩ := hused
        have hR : m = R := by
          rw [Math.blMaxIdx_step (blUsed d) m hm3, ite_eq_left hu] at hmax
          exact hmax
        refine ⟨⟨rfl, m, hm2, hm18, by rw [hr]; exact hm, Or.inr ⟨hb, hR⟩⟩, ?_⟩
        change (if r.2 then 0 else r.1.toInt.toNat) < mb.toInt.toNat
        rw [hb]
        change 0 < mb.toInt.toNat
        omega
      · obtain ⟨hr, hb, hu⟩ := hzero
        have hmax' : Math.blMaxIdx (blUsed d) (m - 1) = R := by
          rw [Math.blMaxIdx_step (blUsed d) m hm3, ite_eq_right (show ¬ blUsed d m = true by rw [hu]; decide +kernel)] at hmax
          exact hmax
        refine ⟨⟨rfl, m - 1, by omega, by omega, by omega, Or.inl ⟨hb, hmax'⟩⟩, ?_⟩
        simp only [hb, Bool.false_eq_true, ite_false]
        omega
    · refine WS.pure' (Or.inl ⟨by simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not]; omega, ?_⟩)
      have hmval : m = 2 := by omega
      rw [hmval] at hm hmax
      exact ⟨rfl, hm.trans (show (2 : Int) = R from by change (2 : Int) = (R : Nat); rw [← hmax]; rfl)⟩
  · subst brk
    refine WS.pure' (Or.inl ⟨by simp, rfl, ?_⟩)
    exact hm.trans (by rw [hmax])

/-- Mathematical header cost, computed with the same unsigned arithmetic. -/
def blHeaderCost (m : Nat) : UInt64 := 3 * (UInt64.ofNat m + 1) + 5 + 5 + 4

/-- The actual search and unsigned cost update, with exact returned index. -/
theorem ws_blFinish {h0 : Heap} {id : Nat} {d : DeflateState} (hB : 19 ≤ d.bl_tree.size) :
    WS h0 id (blFinish (Sp id)) d (fun mb e =>
      mb.toInt = Math.blMaxIdx (blUsed d) 18 ∧
      e = { d with opt_len := d.opt_len + blHeaderCost (Math.blMaxIdx (blUsed d) 18) }) := by
  have hlo := Math.blMaxIdx_ge (blUsed d) 18 (by omega)
  have hhi := Math.blMaxIdx_le (blUsed d) 18
  unfold blFinish
  refine WS.bind' (ws_blIndexLoop hB) fun r e ⟨he, hmb⟩ => ?_
  subst e
  rcases r with ⟨mb, brk⟩
  dsimp only at hmb ⊢
  have hul : i2ul mb = UInt64.ofNat (Math.blMaxIdx (blUsed d) 18) := by
    rw [i2ul_eq mb (by omega) (by omega)]
    congr 1
    omega
  rw [hul]
  refine WS.bind' (ws_md _) fun _ e he => ?_
  subst e
  refine WS.pure' ⟨hmb, ?_⟩
  with_reducible dsimp only [blHeaderCost]

/-- Code-array facts for the actual bit-length alphabet. The source state
records the frequencies seen by build_tree. The result uses the independent
format decoder, actual descriptor maximum and final stored code words. -/
def BLCodeResult (source built : DeflateState) : Prop :=
  ∃ maxc : Nat, maxc < 19 ∧ built.bl_desc.max_code.toInt = maxc ∧
    ZlibF.Spec.Acceptable .codeLength
      (Zlib.Inftrees.Proofs.lensOf (fun v => built.bl_tree[v]!.dl.toNat) (maxc + 1)) ∧
    ∀ v < 19, source.bl_tree[v]!.fc ≠ 0 →
      (1 ≤ built.bl_tree[v]!.dl.toNat ∧ built.bl_tree[v]!.dl.toNat ≤ 7 ∧
        built.bl_tree[v]!.fc.toNat = Math.storedCode
          (fun b => built.bl_count[b]!.toNat) (fun n => built.bl_tree[n]!.dl.toNat) v ∧
        built.bl_tree[v]!.fc.toNat < 2 ^ built.bl_tree[v]!.dl.toNat) ∧
      ∀ suffix : List Bool,
        ZlibF.Spec.decodeSym
          (Zlib.Inftrees.Proofs.lensOf (fun n => built.bl_tree[n]!.dl.toNat) (maxc + 1))
          (Out.natBits built.bl_tree[v]!.fc.toNat built.bl_tree[v]!.dl.toNat ++ suffix) = some (v, suffix)

/-- Scanning both source trees and constructing the bit-length tree compose
using actual callees. Their exact frequency source and output frame remain
available alongside the independent symbol-decoding result. -/
theorem bl_build {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (scanned built : DeflateState) (B : Array CtData),
      blBuild (Sp id) h = .ok ((), setD h id built) ∧
      scanned = blScannedState d B ∧ B.size = d.bl_tree.size ∧
      (∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat (blScanCount d k)) ∧
      BTBuildFrame .bl .bl scanned built ∧ Out.TreesInvAt (setD h id built) id built b buf ∧
      Out.outBits buf built = Out.outBits buf d ∧ BLCodeResult scanned built := by
  obtain ⟨scanned, B, hr, hs, hIS, houtS, hBs, hdl, hfreq⟩ := bl_scan_pair hI hin
  obtain ⟨a, built, hbuild, hframe, husable, M, hM, hmax, haccept, hdecode⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0)
    (merge_ws_and (ws_build_tree_usable_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0)
      (ws_build_tree_decodable_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0))
  have ha : a = () := Subsingleton.elim _ _
  subst a
  have hIB := hframe.treesInvAt hIS
  rw [setD_setD] at hIB
  refine ⟨scanned, built, B, ?_, hs, hBs, hfreq, hframe, hIB,
    (hframe.outBits buf).trans houtS, ?_⟩
  · have hp : pBldesc (Sp id) (setD h id scanned) =
        .ok (some (.in_dstate_bl_desc id), setD h id scanned) := by
      unfold pBldesc
      rw [bind_app, Out.sid_run (setD_dstates_same h id scanned)]
      rfl
    unfold blBuild
    rw [bind_app, hr]
    simp only []
    rw [bind_app, hp]
    exact hbuild
  · refine ⟨M, hM, hmax, haccept .codeLength, ?_⟩
    intro v hv hf
    exact ⟨husable v hv hf, hdecode v hv hf⟩

/-- Changing the unsigned tree-description cost retains every code and
output field. -/
theorem blCost_frame (d : DeflateState) (O : UInt64) :
    BTBuildFrame .bl .bl d { d with opt_len := O } := by
  refine ⟨d.bl_tree, d.heap, d.depth, d.bl_count, d.heap_len, d.heap_max,
    d.bl_desc.max_code, O, d.static_len, rfl, rfl, rfl, rfl, rfl⟩

/-- `local int build_bl_tree(deflate_state *s)`.
The complete actual function executes from the literal/distance data supplied
by their constructors. It returns the exact descending-search index, applies
the exact unsigned header cost, preserves output state and establishes the
bit-length codes' independent decoder meaning. The generic index bound is
two through eighteen; proving the four-code format minimum needs the actual
source-tree/frequency history, not a stronger assumed search invariant. -/
theorem build_bl_tree_checked {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (mb : Int32) (scanned built e : DeflateState) (B : Array CtData),
      build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧
      scanned = blScannedState d B ∧
      (∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat (blScanCount d k)) ∧
      BTBuildFrame .bl .bl scanned built ∧
      e = { built with opt_len := built.opt_len + blHeaderCost (Math.blMaxIdx (blUsed built) 18) } ∧
      mb.toInt = Math.blMaxIdx (blUsed built) 18 ∧ 2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      (∀ rank, mb.toInt.toNat < rank → rank ≤ 18 → blUsed e rank = false) ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d ∧
      BLCodeResult scanned e := by
  obtain ⟨scanned, built, B, hb, hs, hBs, hfreq, hframe, hIB, houtB, hcodes⟩ := bl_build hI hin
  obtain ⟨mb, e, hfinish, hmb, he⟩ := ws_blFinish (h0 := h) (id := id) (d := built)
    (by obtain ⟨hl, hd, hbl, rest⟩ := hIB.base.wf; omega)
  have hcost := blCost_frame built (built.opt_len + blHeaderCost (Math.blMaxIdx (blUsed built) 18))
  have hIe := hcost.treesInvAt hIB
  rw [setD_setD] at hIe
  have hlo := Math.blMaxIdx_ge (blUsed built) 18 (by omega)
  have hhi := Math.blMaxIdx_le (blUsed built) 18
  refine ⟨mb, scanned, built, e, B, ?_, hs, hfreq, hframe, he, hmb, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [build_bl_tree_eq, bind_app, hb]
    exact hfinish
  · intro rank hr hr18
    rw [he]
    change blUsed built rank = false
    exact Math.blMaxIdx_suffix (blUsed built) 18 rank (by omega) hr18
  · rw [he]; exact hIe
  · rw [he]
    exact (hcost.outBits buf).trans houtB
  · rw [he]
    exact hcodes

/-- A tree constructor retains every other descriptor exactly. -/
theorem BTBuildFrame.other_desc {tk dk : TK} {d e : DeflateState}
    (hi : BTBuildFrame tk dk d e) (other : TK) (hne : other ≠ dk) :
    other.getDesc e = other.getDesc d := by
  obtain ⟨T, H, D, B, hl, hm, mc, O, S, rfl, rest⟩ := hi
  cases tk <;> cases dk <;> cases other <;> first | exact False.elim (hne rfl) | rfl

/-- The adjacent literal and distance construction calls in _tr_flush_block. -/
def blPrepare (s : DeflateStatePtr) : M Unit := do
  build_tree s (← pLdesc s)
  build_tree s (← pDdesc s)

/-- Actual literal and distance construction establishes the complete input
representation for build_bl_tree. Their calls preserve the bit-length
frequencies, so the later zero-initialization history can be transported. -/
theorem bl_prepare {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) :
    ∃ e : DeflateState, blPrepare (Sp id) h = .ok ((), setD h id e) ∧
      BLInput e ∧ Out.TreesInvAt (setD h id e) id e b buf ∧
      e.bl_tree = d.bl_tree ∧ Out.outBits buf e = Out.outBits buf d := by
  obtain ⟨aL, lit, hrL, hframeL, ML, hML, hmaxL, haccL, hdecodeL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0)
    (ws_build_tree_decodable_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0)
  have haL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self hI.base.dstate] at hrL
  have hIL := hframeL.treesInvAt hI
  obtain ⟨aD, dist, hrD, hframeD, MD, hMD, hmaxD, haccD, hdecodeD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist hIL.base.wf hIL.base.static hIL.run.to0)
    (ws_build_tree_decodable_initialized (h0 := h) .dist hIL.base.wf hIL.base.static hIL.run.to0)
  have haD : aD = () := Subsingleton.elim _ _
  subst aD
  simp only [TK.descRef] at hrL hrD
  have hID := hframeD.treesInvAt hIL
  rw [setD_setD] at hID
  have hlDesc := hframeD.other_desc .lit (by decide +kernel)
  have hlTree := hframeD.other_tree .lit (by decide +kernel)
  have hbTreeL := hframeL.other_tree .bl (by decide +kernel)
  have hbTreeD := hframeD.other_tree .bl (by decide +kernel)
  have hlenL := acceptable_scan_lengths .lit lit ML (haccL .codeLength)
  have hlenD := acceptable_scan_lengths .dist dist MD (haccD .codeLength)
  simp only [TK.getDesc, TK.arr] at hlDesc hlTree hbTreeL hbTreeD hmaxL hmaxD hlenL hlenD
  change ML < 286 at hML
  change MD < 30 at hMD
  have hin : BLInput dist := by
    refine ⟨by rw [hlDesc]; omega, by rw [hlDesc]; omega, by omega, by omega, ?_, ?_⟩
    · intro i hi
      rw [hlDesc] at hi
      rw [hlTree]
      exact hlenL i (by omega)
    · intro i hi
      exact hlenD i (by omega)
  refine ⟨dist, ?_, hin, hID, hbTreeD.trans hbTreeL,
    (hframeD.outBits buf).trans (hframeL.outBits buf)⟩
  have hpL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
    unfold pLdesc
    rw [bind_app, Out.sid_run hI.base.dstate]
    rfl
  have hpD : pDdesc (Sp id) (setD h id lit) =
      .ok (some (.in_dstate_d_desc id), setD h id lit) := by
    unfold pDdesc
    rw [bind_app, Out.sid_run (setD_dstates_same h id lit)]
    rfl
  unfold blPrepare
  rw [bind_app, hpL]
  simp only []
  rw [bind_app, hrL]
  simp only []
  rw [bind_app, hpD]
  exact hrD

/-- The three actual tree constructors and both actual code-length scans
compose from the existing live tree representation. BLInput is established
by actual earlier calls, rather than assumed at this entry. This remains a
local tree-description theorem; full block emission and engine integration
are separate obligations. -/
theorem prepare_build_bl_tree {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) :
    ∃ (mb : Int32) (ready scanned built e : DeflateState) (B : Array CtData),
      blPrepare (Sp id) h = .ok ((), setD h id ready) ∧ BLInput ready ∧
      (do blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id e) ∧
      scanned = blScannedState ready B ∧
      (∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat (blScanCount ready k)) ∧
      BTBuildFrame .bl .bl scanned built ∧
      e = { built with opt_len := built.opt_len + blHeaderCost (Math.blMaxIdx (blUsed built) 18) } ∧
      mb.toInt = Math.blMaxIdx (blUsed built) 18 ∧ 2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d ∧
      BLCodeResult scanned e := by
  obtain ⟨ready, hready, hin, hIR, hBready, houtR⟩ := bl_prepare hI
  obtain ⟨mb, scanned, built, e, B, hbuild, hs, hfreq, hframe, he, hmb, hlo, hhi, htail, hIe, hout, hcodes⟩ :=
    build_bl_tree_checked hIR hin
  rw [setD_setD] at hbuild hIe
  refine ⟨mb, ready, scanned, built, e, B, hready, hin, ?_, hs, ?_, hframe, he, hmb, hlo, hhi,
    hIe, hout.trans houtR, hcodes⟩
  · rw [bind_app, hready]
    exact hbuild
  · intro k
    rw [hfreq k, hBready]

/-- Frequency increments are bounded by the finite alphabets, independently
of total input size or the old frequency values. -/
theorem blScanCount_le (d : DeflateState) (hin : BLInput d) (k : Nat) : blScanCount d k ≤ 316 := by
  have hl : ∀ i, Out.guarded (fun i => d.dyn_ltree[i]!.dl.toNat) d.l_desc.max_code.toInt.toNat i < 65536 := by
    intro i
    unfold Out.guarded
    split
    · decide +kernel
    · exact UInt16.toNat_lt _
  have hd : ∀ i, Out.guarded (fun i => d.dyn_dtree[i]!.dl.toNat) d.d_desc.max_code.toInt.toNat i < 65536 := by
    intro i
    unfold Out.guarded
    split
    · decide +kernel
    · exact UInt16.toNat_lt _
  have hL := scanFreq_le _ hl (d.l_desc.max_code.toInt.toNat + 1) k
  have hD := scanFreq_le _ hd (d.d_desc.max_code.toInt.toNat + 1) k
  have hL0 := hin.l0
  have hL286 := hin.l286
  have hD0 := hin.d0
  have hD30 := hin.d30
  unfold blScanCount
  omega

/-- Zero initialization makes the actual two-scan frequency cells exact
natural counts, with no 16-bit wrap. This is an internal data premise; the
following init-to-scans theorem establishes it by actual initialization. -/
theorem bl_scan_pair_zero {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d)
    (hz : ∀ k < 19, d.bl_tree[k]!.fc = 0) :
    ∃ (e : DeflateState) (B : Array CtData),
      blScanPair (Sp id) h = .ok ((), setD h id e) ∧ e = blScannedState d B ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧
      ∀ k < 19, B[k]!.fc.toNat = blScanCount d k ∧ B[k]!.fc.toNat ≤ 316 := by
  obtain ⟨e, B, hr, he, hIe, hout, hBs, hdl, hfc⟩ := bl_scan_pair hI hin
  refine ⟨e, B, hr, he, hIe, ?_⟩
  intro k hk
  have hb := blScanCount_le d hin k
  have hv : B[k]!.fc.toNat = blScanCount d k := by
    rw [hfc k, hz k hk, UInt16.zero_add, UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨hv, by omega⟩

/-- Actual init_block establishes zero bit-length frequencies. Both actual
source-tree constructors preserve them, and both scans then store their
exact natural counts. This is an init-to-call composition; it is not yet the
streaming proof that arbitrary intervening symbol tallies retain the same
entry facts. -/
theorem init_prepare_scans {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) :
    ∃ (initialized ready scanned : DeflateState) (B : Array CtData),
      (do init_block (Sp id); blPrepare (Sp id); blScanPair (Sp id)) h =
        .ok ((), setD h id scanned) ∧
      init_block (Sp id) h = .ok ((), setD h id initialized) ∧
      BLInput ready ∧ scanned = blScannedState ready B ∧
      Out.TreesInvAt (setD h id scanned) id scanned b buf ∧
      ∀ k < 19, B[k]!.fc.toNat = blScanCount ready k ∧ B[k]!.fc.toNat ≤ 316 := by
  obtain ⟨aL, aD, aB, initialized, hinit, hII, heI, hLs, hDs, hBs,
    hLzero, hEOB, hDzero, hBzero, hLdl, hDdl, hBdl⟩ := Out.init_block_spec0 hI.base hI.run.to0
  change init_block (Sp id) h = .ok ((), setD h id initialized) at hinit
  change Out.TreesInvAt (setD h id initialized) id initialized b buf at hII
  have hzI : ∀ k < 19, initialized.bl_tree[k]!.fc = 0 := by
    intro k hk
    rw [heI]
    exact hBzero k hk
  obtain ⟨ready, hprepare, hin, hIR, hBready, hout⟩ := bl_prepare hII
  have hzR : ∀ k < 19, ready.bl_tree[k]!.fc = 0 := by
    rw [hBready]
    exact hzI
  obtain ⟨scanned, B, hscan, hs, hIS, hcounts⟩ := bl_scan_pair_zero hIR hin hzR
  rw [setD_setD] at hprepare
  simp only [setD_setD] at hscan hIS
  refine ⟨initialized, ready, scanned, B, ?_, hinit, hin, hs, hIS, hcounts⟩
  rw [bind_app, hinit]
  simp only []
  rw [bind_app, hprepare]
  exact hscan

/-- Scanning only changes the literal sentinel beyond the live alphabet. -/
theorem blScannedState_lit_get (d : DeflateState) (B : Array CtData) (i : Nat)
    (hi : i ≤ d.l_desc.max_code.toInt.toNat) :
    (blScannedState d B).dyn_ltree[i]! = d.dyn_ltree[i]! := by
  unfold blScannedState scGuard
  rw [Out.getElem!_set!]
  rw [ite_eq_right (show ¬ (d.l_desc.max_code.toInt.toNat + 1 = i ∧
    d.l_desc.max_code.toInt.toNat + 1 < d.dyn_ltree.size) by omega)]

/-- Scanning only changes the distance sentinel beyond the live alphabet. -/
theorem blScannedState_dist_get (d : DeflateState) (B : Array CtData) (i : Nat)
    (hi : i ≤ d.d_desc.max_code.toInt.toNat) :
    (blScannedState d B).dyn_dtree[i]! = d.dyn_dtree[i]! := by
  unfold blScannedState scGuard
  rw [Out.getElem!_set!]
  rw [ite_eq_right (show ¬ (d.d_desc.max_code.toInt.toNat + 1 = i ∧
    d.d_desc.max_code.toInt.toNat + 1 < d.dyn_dtree.size) by omega)]

/-- Complete actual build_bl_tree preserves both live source alphabets'
code words, lengths and descriptors. This transports their decoder meaning
to the same heap on which the tree descriptions and block will be emitted. -/
theorem build_bl_preserves_source_codes {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (mb : Int32) (e : DeflateState),
      build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧
      e.l_desc = d.l_desc ∧ e.d_desc = d.d_desc ∧
      (∀ i ≤ d.l_desc.max_code.toInt.toNat, e.dyn_ltree[i]! = d.dyn_ltree[i]!) ∧
      (∀ i ≤ d.d_desc.max_code.toInt.toNat, e.dyn_dtree[i]! = d.dyn_dtree[i]!) ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d := by
  obtain ⟨mb, scanned, built, e, B, hr, hs, hfreq, hframe, he, hmb, hlo, hhi, htail, hIe, hout, hcodes⟩ :=
    build_bl_tree_checked hI hin
  have hlDesc := hframe.other_desc .lit (by decide +kernel)
  have hdDesc := hframe.other_desc .dist (by decide +kernel)
  have hlTree := hframe.other_tree .lit (by decide +kernel)
  have hdTree := hframe.other_tree .dist (by decide +kernel)
  simp only [TK.getDesc, TK.arr] at hlDesc hdDesc hlTree hdTree
  refine ⟨mb, e, hr, ?_, ?_, ?_, ?_, hIe, hout⟩
  · rw [he]
    change built.l_desc = d.l_desc
    rw [hlDesc, hs]
    rfl
  · rw [he]
    change built.d_desc = d.d_desc
    rw [hdDesc, hs]
    rfl
  · intro i hi
    rw [he]
    change built.dyn_ltree[i]! = d.dyn_ltree[i]!
    rw [hlTree, hs]
    exact blScannedState_lit_get d B i hi
  · intro i hi
    rw [he]
    change built.dyn_dtree[i]! = d.dyn_dtree[i]!
    rw [hdTree, hs]
    exact blScannedState_dist_get d B i hi

/-- Every ordinary length symbol is beyond the first three repetition-only
ranks of the actual fixed permutation. -/
theorem bl_order_nonrepeat_rank (code : Nat) (hc : code < 16) :
    ∃ rank : Nat, 3 ≤ rank ∧ rank ≤ 18 ∧ bl_order[rank]!.toNat = code := by
  have h : ∀ c : Fin 16, ∃ r : Fin 19, 3 ≤ r.val ∧ bl_order[r.val]!.toNat = c.val := by
    decide +kernel
  obtain ⟨r, hr3, he⟩ := h ⟨code, hc⟩
  exact ⟨r.val, hr3, by have := r.isLt; omega, he⟩

/-- A represented non-repeat length code supplies the table/search part of
the four-entry format minimum. Actual scan-frequency support must establish
the premise; it is not a new caller precondition. -/
theorem bl_index_ge_of_nonrepeat (d : DeflateState) (code : Nat) (hc : code < 16)
    (hlen : d.bl_tree[code]!.dl ≠ 0) : 3 ≤ Math.blMaxIdx (blUsed d) 18 := by
  obtain ⟨rank, hr3, hr18, he⟩ := bl_order_nonrepeat_rank code hc
  have hu : blUsed d rank = true := by
    unfold blUsed
    rw [he]
    exact bne_iff_ne.mpr hlen
  have hb := Math.blMaxIdx_ge_of_used (blUsed d) 18 rank hr3 hr18 hu
  omega

end Zlib.Trees.Proofs
