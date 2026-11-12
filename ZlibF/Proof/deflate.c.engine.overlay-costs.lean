import ZlibF.Proof.«trees.c.universal-overlay-costs»
import ZlibF.Proof.«trees.c.build.optimal-initialized»
import ZlibF.Proof.«trees.c.bl-tree»
import ZlibF.Proof.«deflate.c.engine.symbol-excess»
import ZlibF.Proof.«deflate.c.engine.dynamic-cost»
import ZlibF.Proof.«deflate.c.engine.bl-symbol-excess»
import ZlibF.Proof.«deflate.c.engine.dynamic-payload-data»
import ZlibF.Proof.«deflate.c.engine.block-initial»
import ZlibF.Proof.«trees.c.header-budget»
import ZlibF.Proof.«deflate.c.engine.filtered-static-budget»

/-!
# deflate.c: `opt_len` at the dynamic choice is the dynamic block length (for `TinyOverlay`)

The bit-length construction `blBuild` with the cost `build_tree` adds for the bit-length tree.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- `blBuild` (both scans, then the bit-length tree), with the cost of the bit-length tree:
its scanned frequencies at the code lengths it gets, plus their extra bits. -/
theorem bl_build_cost {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (scanned built : DeflateState) (B : Array CtData),
      blBuild (Sp id) h = .ok ((), setD h id built) ∧
      scanned = blScannedState d B ∧ B.size = d.bl_tree.size ∧
      (∀ k : Nat, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat (blScanCount d k)) ∧
      BTBuildFrame .bl .bl scanned built ∧ Out.TreesInvAt (setD h id built) id built b buf ∧
      built.opt_len = scanned.opt_len + UInt64.ofNat
        (btLeafCost .bl TK.bl.buildDesc.elems.toInt.toNat (fun v => curL (TK.arr .bl built) v + TK.bl.buildExtra v)
          scanned) := by
  obtain ⟨scanned, B, hr, hs, hIS, _houtS, hBs, _hdl, hfreq⟩ := bl_scan_pair hI hin
  obtain ⟨a, built, hbuild, hframe, hcost⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0)
    (ws_build_tree_initialized_optimal_cost (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0)
  have ha : a = () := Subsingleton.elim _ _
  subst a
  have hIB := hframe.treesInvAt hIS
  rw [setD_setD] at hIB
  refine ⟨scanned, built, B, ?_, hs, hBs, hfreq, hframe, hIB, hcost⟩
  have hp : pBldesc (Sp id) (setD h id scanned) =
      .ok (some (.in_dstate_bl_desc id), setD h id scanned) := by
    unfold pBldesc
    rw [bind_app, Out.sid_run (setD_dstates_same h id scanned)]
    rfl
  unfold blBuild
  rw [bind_app, hr]
  simp only []
  rw [bind_app, hp]
  exact hbuild

end Zlib.Trees.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare BLInput blScannedState blScanCount BTBuildFrame TK curL btLeafCost
  same_record_of_runs bl_build_cost ws_blFinish build_bl_tree_eq blHeaderCost dynamicHeaderBits sourceWords
  SourceLengthFacts)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The counter chain of the dynamic choice: after both data trees, both scans, the bit-length
tree and its header cost, `opt_len` is the payload (the dynamic symbol codes and the end-of-block
code), plus the bit-length tree's cost, plus the fixed header fields. -/
theorem dynamic_opt_len_parts {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (ledger : SymbolLedger buf d xs) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (clear : BlockInit.BlockClear d) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    ∃ (readyP scanned built : DeflateState) (B : Array CtData),
      TreesInvAt (setD h ds readyP) ds readyP pb buf ∧ BLInput readyP ∧ SourceLengthFacts d readyP ∧
      scanned = blScannedState readyP B ∧ BTBuildFrame .bl .bl scanned built ∧
      (∀ k : Nat, B[k]!.fc = readyP.bl_tree[k]!.fc + UInt16.ofNat (blScanCount readyP k)) ∧
      readyP.bl_tree = d.bl_tree ∧
      ready = { built with opt_len := built.opt_len + blHeaderCost mb.toInt.toNat } ∧ mb.toInt.toNat ≤ 18 ∧
      ready.opt_len = UInt64.ofNat
        ((xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits (sourceWords readyP .lit)
            (sourceWords readyP .dist) (s.distance, s.value)) ++
          Zlib.Trees.Proofs.Out.codeBits (sourceWords readyP .lit) 256).length) +
        UInt64.ofNat (btLeafCost .bl TK.bl.buildDesc.elems.toInt.toNat
          (fun v => curL (TK.arr .bl built) v + TK.bl.buildExtra v) scanned) +
        blHeaderCost mb.toInt.toNat := by
  obtain ⟨literal, readyP, prepare, _goodR, treesR, _buffersR, _sizes, _storage, input, frameL, frameD,
    facts, _excess⟩ := source_trees_symbol_excess_engine (ob := 0) good trees buffers ledger count
  obtain ⟨resP, runP, costP⟩ := bl_prepare_dynamic_payload_cost trees ledger
  have eP : readyP = resP := same_record_of_runs prepare runP
  subst eP
  have runB : Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds readyP) = .ok (mb, setD h ds ready) := by
    rw [bind_app, prepare] at run
    exact run
  obtain ⟨scanned, built, B, blRun, hs, _hBs, hfreq, hframe, hIB, hcost⟩ := bl_build_cost treesR input
  have bridge : Zlib.Trees.Proofs.setD (setD h ds readyP) ds built = setD h ds built := by
    simp only [Zlib.Trees.Proofs.setD, setD, upd_upd]
  rw [bridge] at blRun
  have sizeB : 19 ≤ built.bl_tree.size := by
    obtain ⟨_, _, _, _⟩ := hIB.base.wf
    omega
  obtain ⟨mbF, eF, finRun, hmb, heF⟩ := ws_blFinish (h0 := h) (id := ds) (d := built) sizeB
  have full : Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds readyP) = .ok (mbF, setD h ds eF) := by
    rw [build_bl_tree_eq, bind_app, blRun]
    exact finRun
  have same := runB.symm.trans full
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨rfl, sameH⟩ := same
  have eR : ready = eF := by
    have := congrArg (fun heap : Heap => heap.dstates ds) sameH
    simpa only [setD_dstates_same, Option.some.injEq] using this
  subst eR
  have blKeep : readyP.bl_tree = d.bl_tree := by
    have one := frameL.other_tree .bl (by decide +kernel)
    have two := frameD.other_tree .bl (by decide +kernel)
    simp only [TK.arr] at one two
    rw [two, one]
  have idx : Zlib.Trees.Proofs.Math.blMaxIdx (Zlib.Trees.Proofs.blUsed built) 18 = mb.toInt.toNat := by
    rw [hmb]; simp
  rw [idx] at heF
  have mbLe : mb.toInt.toNat ≤ 18 := by
    rw [← idx]; exact Zlib.Trees.Proofs.Math.blMaxIdx_le _ 18
  refine ⟨readyP, scanned, built, B, treesR, input, facts, hs, hframe, hfreq, blKeep, heF, mbLe, ?_⟩
  rw [heF]
  simp only []
  rw [hcost, hs]
  simp only [blScannedState]
  rw [costP, clear.opt]
  simp only [UInt64.zero_add]

theorem payload_length (d : DeflateState) (xs : List Symbol) :
    (xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits (sourceWords d .lit) (sourceWords d .dist)
        (s.distance, s.value)) ++ Zlib.Trees.Proofs.Out.codeBits (sourceWords d .lit) 256).length =
      (dynamicSymbolCosts d xs).sum + curL d.dyn_ltree 256 := by
  rw [List.length_append, List.length_flatMap]
  congr 1
  · simp only [dynamicSymbolCosts]
    congr 1
    apply List.map_congr_left
    intro s _
    exact dynamic_symbol_bits_length d s
  · simp only [Zlib.Trees.Proofs.Out.codeBits, Zlib.Trees.Proofs.Out.natBits_length, sourceWords,
      Zlib.Trees.Proofs.PayloadTree.words, Zlib.Trees.Proofs.PayloadTree.arr, TK.arr, curL]

theorem blHeaderCost_eq (m : Nat) (hm : m ≤ 18) : blHeaderCost m = UInt64.ofNat (3 * (m + 1) + 14) := by
  have key : ∀ k, k < 19 → blHeaderCost k = UInt64.ofNat (3 * (k + 1) + 14) := by decide
  exact key m (by omega)

/-- **`opt_len` at the dynamic choice** (for `TinyOverlay`, batch 1's request): after the
preparation run of `_tr_flush_block`, `opt_len` is the length of the dynamic header plus the
dynamic codes of the symbols, extra bits included, plus the end-of-block code. -/
theorem dynamic_opt_len {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (ledger : SymbolLedger buf d xs) (count : d.sym_next.toNat ≤ d.sym_end.toNat)
    (clear : BlockInit.BlockClear d) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    ready.opt_len = UInt64.ofNat ((dynamicHeaderBits ready mb).length + (dynamicSymbolCosts ready xs).sum +
      curL ready.dyn_ltree 256) := by
  obtain ⟨readyP, scanned, built, B, treesP, input, facts, hs, hframe, hfreq, blKeep, hready, mbLe, hopt⟩ :=
    dynamic_opt_len_parts good trees buffers ledger count clear run
  -- the trees and descriptors of `ready`
  have litB := hframe.other_tree .lit (by decide +kernel)
  have distB := hframe.other_tree .dist (by decide +kernel)
  have lDescB := hframe.other_desc .lit (by decide +kernel)
  have dDescB := hframe.other_desc .dist (by decide +kernel)
  simp only [TK.arr, TK.getDesc] at litB distB lDescB dDescB
  have rL : ready.dyn_ltree = Zlib.Trees.Proofs.scGuard readyP.dyn_ltree readyP.l_desc.max_code.toInt.toNat := by
    rw [hready]; simp only []; rw [litB, hs]; rfl
  have rD : ready.dyn_dtree = Zlib.Trees.Proofs.scGuard readyP.dyn_dtree readyP.d_desc.max_code.toInt.toNat := by
    rw [hready]; simp only []; rw [distB, hs]; rfl
  have rLd : ready.l_desc = readyP.l_desc := by rw [hready]; simp only []; rw [lDescB, hs]; rfl
  have rDd : ready.d_desc = readyP.d_desc := by rw [hready]; simp only []; rw [dDescB, hs]; rfl
  have rB : ready.bl_tree = built.bl_tree := by rw [hready]
  obtain ⟨szL, szD, _, _, _, _⟩ := treesP.base.wf
  have l0 := input.l0
  have l286 := input.l286
  have d0 := input.d0
  have d30 := input.d30
  -- the lengths `send_tree` reads are the guarded lengths `scan_tree` reads
  have sendL : Zlib.Trees.Proofs.sendLengths ready .lit =
      Zlib.Trees.Proofs.Out.guarded (fun i => readyP.dyn_ltree[i]!.dl.toNat) readyP.l_desc.max_code.toInt.toNat := by
    funext i
    simp only [Zlib.Trees.Proofs.sendLengths, TK.arr]
    rw [rL]
    exact Zlib.Trees.Proofs.scGuard_lengths _ _ (by omega) i
  have sendD : Zlib.Trees.Proofs.sendLengths ready .dist =
      Zlib.Trees.Proofs.Out.guarded (fun i => readyP.dyn_dtree[i]!.dl.toNat) readyP.d_desc.max_code.toInt.toNat := by
    funext i
    simp only [Zlib.Trees.Proofs.sendLengths, TK.arr]
    rw [rD]
    exact Zlib.Trees.Proofs.scGuard_lengths _ _ (by omega) i
  -- the bit-length tree cost is the scanned frequencies at their weights
  have cost : btLeafCost .bl TK.bl.buildDesc.elems.toInt.toNat
      (fun v => curL (TK.arr .bl built) v + TK.bl.buildExtra v) scanned =
      mass (fun k => blScanCount readyP k * Zlib.Trees.Proofs.Out.blWeight (Zlib.Trees.Proofs.Out.blWords ready) k) 19 := by
    have N : TK.bl.buildDesc.elems.toInt.toNat = 19 := by decide +kernel
    have extra : ∀ v, v < 19 → TK.bl.buildExtra v = Zlib.Trees.Proofs.Out.blExtraBits v := by decide +kernel
    rw [N]
    unfold btLeafCost
    apply mass_congr
    intro v hv
    have bound := Zlib.Trees.Proofs.blScanCount_le readyP input v
    show (Zlib.Trees.Proofs.btFreq .bl scanned v).toNat * _ = _
    have fv : (Zlib.Trees.Proofs.btFreq .bl scanned v).toNat = blScanCount readyP v := by
      simp only [Zlib.Trees.Proofs.btFreq, TK.arr]
      rw [hs]
      simp only [blScannedState]
      rw [hfreq v, blKeep, clear.bl v hv]
      simp only [UInt16.zero_add]
      exact UInt16.toNat_ofNat_of_lt' (by unfold UInt16.size; omega)
    rw [fv]
    show blScanCount readyP v * (curL (TK.arr .bl built) v + TK.bl.buildExtra v) = _
    rw [extra v hv]
    simp only [Zlib.Trees.Proofs.Out.blWeight, Zlib.Trees.Proofs.Out.blWords, curL, TK.arr, rB]
  -- the scanned frequencies weigh as much as `send_tree` emits
  have small : ∀ (T : Array CtData) (M : Nat), (∀ i ≤ M, T[i]!.dl.toNat ≤ 15) →
      ∀ i, i < M + 1 → Zlib.Trees.Proofs.Out.guarded (fun n => T[n]!.dl.toNat) M i ≤ 15 := by
    intro T M fit i lt
    simp only [Zlib.Trees.Proofs.Out.guarded, show i ≠ M + 1 by omega, if_false]
    exact fit i (by omega)
  have tl := Zlib.Trees.Proofs.Out.treeBits_length (Zlib.Trees.Proofs.Out.blWords ready) _ _
    (small readyP.dyn_ltree readyP.l_desc.max_code.toInt.toNat input.llen)
  have td := Zlib.Trees.Proofs.Out.treeBits_length (Zlib.Trees.Proofs.Out.blWords ready) _ _
    (small readyP.dyn_dtree readyP.d_desc.max_code.toInt.toNat input.dlen)
  have scanSplit : mass (fun k => blScanCount readyP k *
      Zlib.Trees.Proofs.Out.blWeight (Zlib.Trees.Proofs.Out.blWords ready) k) 19 =
      (Zlib.Trees.Proofs.Out.treeBitsUpTo (Zlib.Trees.Proofs.Out.blWords ready)
        (Zlib.Trees.Proofs.Out.guarded (fun i => readyP.dyn_ltree[i]!.dl.toNat) readyP.l_desc.max_code.toInt.toNat)
        (readyP.l_desc.max_code.toInt.toNat + 1)).length +
      (Zlib.Trees.Proofs.Out.treeBitsUpTo (Zlib.Trees.Proofs.Out.blWords ready)
        (Zlib.Trees.Proofs.Out.guarded (fun i => readyP.dyn_dtree[i]!.dl.toNat) readyP.d_desc.max_code.toInt.toNat)
        (readyP.d_desc.max_code.toInt.toNat + 1)).length := by
    rw [tl, td]
    unfold blScanCount
    exact Zlib.Trees.Proofs.Out.mass_mul_add _ _ _ 19
  -- the header
  have hdr : (dynamicHeaderBits ready mb).length = 14 + 3 * (mb.toInt.toNat + 1) +
      (Zlib.Trees.Proofs.Out.treeBitsUpTo (Zlib.Trees.Proofs.Out.blWords ready)
        (Zlib.Trees.Proofs.Out.guarded (fun i => readyP.dyn_ltree[i]!.dl.toNat) readyP.l_desc.max_code.toInt.toNat)
        (readyP.l_desc.max_code.toInt.toNat + 1)).length +
      (Zlib.Trees.Proofs.Out.treeBitsUpTo (Zlib.Trees.Proofs.Out.blWords ready)
        (Zlib.Trees.Proofs.Out.guarded (fun i => readyP.dyn_dtree[i]!.dl.toNat) readyP.d_desc.max_code.toInt.toNat)
        (readyP.d_desc.max_code.toInt.toNat + 1)).length := by
    unfold dynamicHeaderBits
    rw [Zlib.Trees.Proofs.Out.allTreesBits_length, rLd, rDd, sendL, sendD]
    simp only [Zlib.Trees.Proofs.Out.sendTreeBits, Nat.add_sub_cancel]
  -- the symbol costs of `ready` are those of the trees as built
  have agreeL : ∀ i ≤ readyP.l_desc.max_code.toInt.toNat, ready.dyn_ltree[i]! = readyP.dyn_ltree[i]! := by
    intro i le
    rw [rL]
    unfold Zlib.Trees.Proofs.scGuard
    rw [Zlib.Trees.Proofs.getD_set _ _ _ _ (by omega), if_neg (by omega)]
  have agreeD : ∀ i ≤ readyP.d_desc.max_code.toInt.toNat, ready.dyn_dtree[i]! = readyP.dyn_dtree[i]! := by
    intro i le
    rw [rD]
    unfold Zlib.Trees.Proofs.scGuard
    rw [Zlib.Trees.Proofs.getD_set _ _ _ _ (by omega), if_neg (by omega)]
  have costsSame := dynamicSymbolCosts_live_congr ledger facts agreeL agreeD
  have eobUsed : (d.dyn_ltree[256]!).fc ≠ 0 := by
    intro zero
    have freq := ledger.literal 256 (by decide)
    rw [zero] at freq
    simp only [UInt16.toNat_zero, literalFrequency, if_pos] at freq
    omega
  have eob : curL ready.dyn_ltree 256 = curL readyP.dyn_ltree 256 := by
    unfold curL
    rw [agreeL 256 (facts.literal_used 256 (by decide) eobUsed)]
  rw [hopt, cost, scanSplit, blHeaderCost_eq _ mbLe, payload_length, hdr, costsSame, eob,
    ← UInt64.ofNat_add, ← UInt64.ofNat_add]
  congr 1
  omega

set_option maxRecDepth 10000 in
/-- **`static_len` at the dynamic choice**: the fixed codes of the symbols, extra bits included,
plus the seven-bit end-of-block code. -/
theorem dynamic_static_len {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    ready.static_len = UInt64.ofNat (7 + (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum +
      (xs.map staticDistanceSymbolCost).sum) := by
  obtain ⟨mb', result, run', _, _, _, _, _, _, static, _⟩ :=
    all_trees_static_budget_engine (ob := 0) good trees buffers ledger clear
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  have eR : ready = result := by
    have := congrArg (fun heap : Heap => heap.dstates ds) same.2
    simpa only [setD_dstates_same, Option.some.injEq] using this
  subst eR
  rw [static]
  congr 1
  have literal : mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 =
      7 + (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.literal v fit]),
      literal_frequency_cost symbolLengthCode xs staticLiteralCost 286 (by decide +kernel)
        (fun s member => valid_literal_key (ledger.valid s member))]
    rfl
  have distance : mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30 =
      (xs.map staticDistanceSymbolCost).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.distance v fit])]
    exact weighted_optional_key (Symbol.distanceKey dcodeN) 30 staticDistanceCost
      (fun s member _ selected => valid_distance_key (ledger.valid s member) selected)
  unfold originalStaticCost
  rw [literal, distance]

#print axioms dynamic_opt_len
#print axioms dynamic_static_len

end Zlib.Deflate.Engine.Proofs
