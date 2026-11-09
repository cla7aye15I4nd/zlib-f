import ZlibF.Proof.«trees.c.optimal-counter»
import ZlibF.Proof.«trees.c.header-budget»
import ZlibF.Math.DeflateWeightedMass

/-! # Actual BL scan frequencies count the dynamic header bits

Original frequencies are measured before the BL constructor overwrites
their union cells with canonical words. The resulting cost is then
compared with the actual sender's shared run-length bit sequence.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem bl_extra_ordinary (k : Nat) (fit : k < 16) : TK.bl.buildExtra k = 0 := by
  have table : ∀ i : Fin 16, TK.bl.buildExtra i.val = 0 := by decide +kernel
  exact table ⟨k, fit⟩

private theorem weighted_run_single (coefficient : Nat → Nat) (key amount : Nat)
    (fit : key < 19) :
    mass (fun k => (if k = key then amount else 0) * coefficient k) 19 = amount * coefficient key := by
  have point : (fun k => (if k = key then amount else 0) * coefficient k) =
      (fun k => if k = key then amount * coefficient key else 0) := by
    funext k
    by_cases same : k = key <;> simp [same]
  rw [point, mass_single_value, ite_eq_left fit]

/-- One scan packet counts exactly the sender's code and repeat extras. -/
theorem bl_run_frequency_cost (words : Nat → UInt16 × UInt16) (cur count minimum : Nat) (prev : Int)
    (fit : cur < 16) :
    mass (fun k => runFreq (some (cur, prev, count, minimum)) k *
      ((words k).2.toNat + TK.bl.buildExtra k)) 19 =
      (runBits words (some (cur, prev, count, minimum))).length := by
  by_cases short : count < minimum
  · simp only [runFreq, runBits, ite_eq_left short]
    rw [weighted_run_single _ cur count (by omega), repeated_bits_length, codeBits_length,
      bl_extra_ordinary cur fit, Nat.add_zero]
  · by_cases nonzero : cur ≠ 0
    · by_cases different : (cur : Int) ≠ prev
      · simp only [runFreq, runBits, ite_eq_right short, ite_eq_left nonzero,
          ite_eq_left different, and_iff_right different, Nat.add_mul, mass_add]
        rw [weighted_run_single _ cur 1 (by omega), weighted_run_single _ 16 1 (by decide +kernel)]
        simp only [Nat.one_mul, List.length_append, codeBits_length, natBits_length,
          bl_extra_ordinary cur fit]
        change _ + (_ + 2) = _
        omega
      · simp only [runFreq, runBits, ite_eq_right short, ite_eq_left nonzero,
          different, false_and, ite_false, Nat.zero_add]
        rw [weighted_run_single _ 16 1 (by decide +kernel)]
        simp only [Nat.one_mul, List.length_append, codeBits_length, natBits_length]
        rfl
    · by_cases small : count ≤ 10
      · simp only [runFreq, runBits, ite_eq_right short, ite_eq_right nonzero, ite_eq_left small]
        rw [weighted_run_single _ 17 1 (by decide +kernel)]
        simp only [Nat.one_mul, List.length_append, codeBits_length, natBits_length]
        rfl
      · simp only [runFreq, runBits, ite_eq_right short, ite_eq_right nonzero, ite_eq_right small]
        rw [weighted_run_single _ 18 1 (by decide +kernel)]
        simp only [Nat.one_mul, List.length_append, codeBits_length, natBits_length]
        rfl

/-- Every completed prefix uses the same histogram as the actual scans. -/
theorem tree_bits_frequency_cost (words : Nat → UInt16 × UInt16) (lengths : Nat → Nat) (n : Nat)
    (fit : ∀ i, i < n → lengths i < 16) :
    mass (fun k => scanFreqUpTo lengths n k * ((words k).2.toNat + TK.bl.buildExtra k)) 19 =
      (treeBitsUpTo words lengths n).length := by
  induction n with
  | zero => simp only [scanFreqUpTo, Nat.zero_mul, mass_zero, treeBitsUpTo, List.length_nil]
  | succ n ih =>
    have previous := ih (fun i bound => fit i (by omega))
    have current : (runAt lengths n).next < 16 := by rw [runAt_next]; exact fit n (by omega)
    have packet : mass (fun k => runFreq (runStep lengths n (runAt lengths n)).2 k *
        ((words k).2.toNat + TK.bl.buildExtra k)) 19 =
        (runBits words (runStep lengths n (runAt lengths n)).2).length := by
      simp only [runStep]
      split
      · simp only [runFreq, runBits, Nat.zero_mul, mass_zero, List.length_nil]
      · exact bl_run_frequency_cost words _ _ _ _ current
    simp only [scanFreqUpTo, Nat.add_mul, mass_add, treeBitsUpTo, List.length_append]
    rw [previous, packet]

/-- `local int build_bl_tree(deflate_state *s)`.
The actual two scans, BL constructor, index search and final unsigned
counter update add exactly the complete dynamic header's wire length.
Zero initial BL frequencies are explicit internal state data, established
by init/reset and retained by the separate symbol-ledger history. No
constructor or sender contract is assumed. -/
theorem build_bl_tree_header_cost {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (input : BLInput d)
    (zero : ∀ k, k < 19 → d.bl_tree[k]!.fc = 0) :
    ∃ (mb : Int32) (result : DeflateState),
      build_bl_tree (Sp id) h = .ok (mb, setD h id result) ∧
      TreesInvAt (setD h id result) id result b buf ∧ outBits buf result = outBits buf d ∧
      result.opt_len = d.opt_len + UInt64.ofNat (dynamicHeaderBits result mb).length := by
  obtain ⟨scanned, B, scan, scans, treesS, outputS, _sizeB, _lengthB, frequency⟩ :=
    bl_scan_pair trees input
  obtain ⟨returned, built, build, frame, cost⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .bl treesS.base.wf treesS.base.static treesS.run.to0)
    (ws_build_tree_initialized_optimal_cost (h0 := h) .bl treesS.base.wf treesS.base.static treesS.run.to0)
  have returnedEq : returned = () := Subsingleton.elim _ _
  subst returned
  change build_tree (Sp id) (some (.in_dstate_bl_desc id)) (setD h id scanned) = .ok ((), setD h id built) at build
  have treesB := frame.treesInvAt treesS
  obtain ⟨mb, result, finishRun, index, finish⟩ := ws_blFinish
    (h0 := h) (id := id) (d := built) (by obtain ⟨_, _, bound, _⟩ := treesB.base.wf; omega)
  have costFrame := blCost_frame built (built.opt_len + blHeaderCost (Math.blMaxIdx (blUsed built) 18))
  have treesR := costFrame.treesInvAt treesB
  rw [← finish] at treesR
  simp only [setD_setD] at treesR
  have run : build_bl_tree (Sp id) h = .ok (mb, setD h id result) := by
    have pointer : pBldesc (Sp id) (setD h id scanned) =
        .ok (some (.in_dstate_bl_desc id), setD h id scanned) := by
      unfold pBldesc
      rw [bind_app, sid_run treesS.base.dstate]
      rfl
    rw [build_bl_tree_eq]
    unfold blBuild
    simp only [M_bind_assoc]
    rw [bind_app, scan]
    simp only [bind_app, pointer]
    simp only [build]
    exact finishRun
  have ltree := frame.other_tree .lit (by decide +kernel)
  have dtree := frame.other_tree .dist (by decide +kernel)
  have ldesc := frame.other_desc .lit (by decide +kernel)
  have ddesc := frame.other_desc .dist (by decide +kernel)
  simp only [TK.arr, TK.getDesc] at ltree dtree ldesc ddesc
  have literalTree : result.dyn_ltree = scGuard d.dyn_ltree d.l_desc.max_code.toInt.toNat := by
    rw [finish]
    change built.dyn_ltree = _
    rw [ltree, scans]
    rfl
  have distanceTree : result.dyn_dtree = scGuard d.dyn_dtree d.d_desc.max_code.toInt.toNat := by
    rw [finish]
    change built.dyn_dtree = _
    rw [dtree, scans]
    rfl
  have literalDesc : result.l_desc = d.l_desc := by rw [finish]; change built.l_desc = _; rw [ldesc, scans]; rfl
  have distanceDesc : result.d_desc = d.d_desc := by rw [finish]; change built.d_desc = _; rw [ddesc, scans]; rfl
  have literalLengths : sendLengths result .lit =
      guarded (fun i => d.dyn_ltree[i]!.dl.toNat) d.l_desc.max_code.toInt.toNat := by
    funext i
    change result.dyn_ltree[i]!.dl.toNat = _
    rw [literalTree]
    apply scGuard_lengths
    obtain ⟨extent, _⟩ := trees.base.wf
    have bound := input.l286
    omega
  have distanceLengths : sendLengths result .dist =
      guarded (fun i => d.dyn_dtree[i]!.dl.toNat) d.d_desc.max_code.toInt.toNat := by
    funext i
    change result.dyn_dtree[i]!.dl.toNat = _
    rw [distanceTree]
    apply scGuard_lengths
    obtain ⟨_, extent, _⟩ := trees.base.wf
    have bound := input.d30
    omega
  have frequencies : ∀ k, k < 19 → scanned.bl_tree[k]!.fc.toNat = blScanCount d k := by
    intro k fit
    rw [scans]
    change B[k]!.fc.toNat = _
    rw [frequency k, zero k fit, UInt16.zero_add, UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by have := blScanCount_le d input k; omega)
  have words : blWords result = blWords built := by rw [finish]; rfl
  have payload : btLeafCost .bl 19 (fun k => curL built.bl_tree k + TK.bl.buildExtra k) scanned =
      (sendTreeBits (blWords result) (sendLengths result .lit) d.l_desc.max_code.toInt.toNat).length +
      (sendTreeBits (blWords result) (sendLengths result .dist) d.d_desc.max_code.toInt.toNat).length := by
    change mass (fun k => scanned.bl_tree[k]!.fc.toNat * ((blWords built k).2.toNat + TK.bl.buildExtra k)) 19 = _
    rw [← words]
    rw [mass_congr (fun k fit => by rw [frequencies k fit])]
    simp only [blScanCount, Nat.add_mul, mass_add, literalLengths, distanceLengths, sendTreeBits]
    rw [tree_bits_frequency_cost, tree_bits_frequency_cost]
    · intro i fit
      rw [guarded, ite_eq_right (by omega)]
      have bound := input.dlen i (by omega)
      omega
    · intro i fit
      rw [guarded, ite_eq_right (by omega)]
      have bound := input.llen i (by omega)
      omega
  have header : blHeaderCost (Math.blMaxIdx (blUsed built) 18) =
      UInt64.ofNat (14 + 3 * (mb.toInt.toNat + 1)) := by
    have same : Math.blMaxIdx (blUsed built) 18 = mb.toInt.toNat := by rw [index]; rfl
    rw [same]
    have natural : 14 + 3 * (mb.toInt.toNat + 1) = 3 * (mb.toInt.toNat + 1) + 5 + 5 + 4 := by omega
    rw [natural]
    simp only [blHeaderCost, UInt64.ofNat_add, UInt64.ofNat_mul]
    rfl
  have output : outBits buf result = outBits buf d := by
    rw [finish]
    exact (costFrame.outBits buf).trans ((frame.outBits buf).trans outputS)
  refine ⟨mb, result, run, ?_, output, ?_⟩
  · exact treesR
  · have counter : result.opt_len = built.opt_len + blHeaderCost (Math.blMaxIdx (blUsed built) 18) := by rw [finish]
    have start : scanned.opt_len = d.opt_len := by rw [scans]; rfl
    change built.opt_len = scanned.opt_len + UInt64.ofNat
      (btLeafCost .bl 19 (fun k => curL built.bl_tree k + TK.bl.buildExtra k) scanned) at cost
    rw [counter, cost, start, payload, header]
    rw [UInt64.add_assoc, ← UInt64.ofNat_add]
    congr 1
    rw [dynamicHeaderBits, allTreesBits_length, literalDesc, distanceDesc]
    simp only [Nat.add_sub_cancel]
    ac_rfl

end Zlib.Trees.Proofs
