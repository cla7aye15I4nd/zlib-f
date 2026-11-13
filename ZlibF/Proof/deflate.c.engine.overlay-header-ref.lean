import ZlibF.Proof.«deflate.c.engine.overlay-costs»
import ZlibF.Proof.«deflate.c.engine.overlay-lengths»
import ZlibF.Proof.«deflate.c.engine.overlay-mem2c»
import ZlibF.Proof.«deflate.c.engine.overlay-mem1w»
import ZlibF.Proof.«trees.c.build.rank-leaves»
import ZlibF.Proof.«trees.c.overlay-scan-count»
import ZlibF.Proof.«trees.c.universal-overlay-at»

/-!
# deflate.c: the dynamic header against a reference bit-length code (H3), and `TinyOverlay`

For every prepared block (`TinyPrepared`) the dynamic header is `14 + 3(mb+1)` bits (at most 71)
plus the scanned bit-length frequencies `f` at their bit-length code lengths and extra bits
(`dynamic_header_rank`). The bit-length tree is the 7-bit tree `build_tree` builds for `f`
(`bl_build_rank`), so `BTRankLeaves.cost_le_15/13` bound `Σ f·len` by a reference code:

* `lit_bufsize = 256`: every data-tree length is at most 11 (`prepared_lengths_256`), so the
  bit-length symbols 12..15 are absent and at most 15 symbols are used; `κ0` is complete. So
  `HeaderRefBound 245`.
* `lit_bufsize = 128`: lengths at most 9, symbols 10..15 absent, at most 13 used; `κ1` is
  complete on them. So `HeaderRefBound128W 29`.

With `dynamic_overlay_256c` and `dynamic_overlay_128_w` this gives `TinyOverlayAt 256`,
`TinyOverlayAt 128` and `TinyOverlay` with no hypothesis.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass mass_add mass_congr)
set_option autoImplicit false

/-- The bit-length tree weighs at most `286 + 30 = 316`. -/
theorem blScanCount_mass_le (d : DeflateState) (hin : BLInput d) : mass (blScanCount d) 19 ≤ 316 := by
  have split : mass (blScanCount d) 19 =
      mass (Out.scanFreqUpTo (Out.guarded (fun i => d.dyn_ltree[i]!.dl.toNat) d.l_desc.max_code.toInt.toNat)
        (d.l_desc.max_code.toInt.toNat + 1)) 19 +
      mass (Out.scanFreqUpTo (Out.guarded (fun i => d.dyn_dtree[i]!.dl.toNat) d.d_desc.max_code.toInt.toNat)
        (d.d_desc.max_code.toInt.toNat + 1)) 19 := mass_add _ _ 19
  have l := Out.scan_mass_le (Out.guarded (fun i => d.dyn_ltree[i]!.dl.toNat) d.l_desc.max_code.toInt.toNat)
    (d.l_desc.max_code.toInt.toNat + 1)
  have r := Out.scan_mass_le (Out.guarded (fun i => d.dyn_dtree[i]!.dl.toNat) d.d_desc.max_code.toInt.toNat)
    (d.d_desc.max_code.toInt.toNat + 1)
  have l286 := hin.l286
  have l0 := hin.l0
  have d30 := hin.d30
  have d0 := hin.d0
  omega

/-- `blBuild` with `BTRankLeaves` for the bit-length tree, at a block start (bit-length
frequencies zero). -/
theorem bl_build_rank {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d) (zero : ∀ v, v < 19 → d.bl_tree[v]!.fc = 0) :
    ∃ (scanned built : DeflateState) (B : Array CtData),
      blBuild (Sp id) h = .ok ((), setD h id built) ∧
      scanned = blScannedState d B ∧
      (∀ v, v < 19 → (btFreq .bl scanned v).toNat = blScanCount d v) ∧
      BTBuildFrame .bl .bl scanned built ∧ Out.TreesInvAt (setD h id built) id built b buf ∧
      BTRankLeaves .bl 19 7 scanned built := by
  obtain ⟨scanned, B, hr, hs, hIS, _houtS, _hBs, _hdl, hfreq⟩ := bl_scan_pair hI hin
  have fv : ∀ v, v < 19 → (btFreq .bl scanned v).toNat = blScanCount d v := by
    intro v hv
    have bound := blScanCount_le d hin v
    simp only [btFreq, TK.arr]
    rw [hs]
    simp only [blScannedState]
    rw [hfreq v, zero v hv]
    simp only [UInt16.zero_add]
    exact UInt16.toNat_ofNat_of_lt' (by unfold UInt16.size; omega)
  have N19 : TK.bl.buildDesc.elems.toInt.toNat = 19 := by decide +kernel
  have budget : mass (fun v => (btFreq .bl scanned v).toNat) TK.bl.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16 := by
    rw [N19, mass_congr fv]
    have := blScanCount_mass_le d hin
    omega
  obtain ⟨a, built, hbuild, hframe, hrank⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0)
    (ws_build_tree_rank_leaves_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0 budget)
  have ha : a = () := Subsingleton.elim _ _
  subst a
  have hIB := hframe.treesInvAt hIS
  rw [setD_setD] at hIB
  rw [N19, bl_max_length] at hrank
  refine ⟨scanned, built, B, ?_, hs, fv, hframe, hIB, hrank⟩
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
open Zlib.Trees.Proofs (blPrepare BLInput blScannedState blScanCount BTBuildFrame TK curL btFreq
  same_record_of_runs bl_build_rank ws_blFinish build_bl_tree_eq dynamicHeaderBits BTRankLeaves
  sendLengths)
open Zlib.Trees.Proofs.Out (TreesInvAt scanFreqUpTo guarded blExtraBits refWeight scanFreq_absent)
open ZlibF.Math.DeflateSymbols (mass mass_add mass_congr)
open Zlib.Deflate.Universal.Block (TinyOverlay TinyOverlayAt tinyOverlay_of_two)
set_option autoImplicit false

/-- **The header after the preparation run**, with the bit-length tree as `BTRankLeaves`: the
header is `14 + 3(mb+1)` bits plus the scanned bit-length frequencies at their code lengths and
extra bits, and the lengths `send_tree` reads are the guarded lengths `scan_tree` reads. -/
theorem dynamic_header_rank {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d pb buf) (clear : BlockInit.BlockClear d) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    ∃ (readyP scanned built : DeflateState),
      BLInput readyP ∧
      (∀ k, scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
        scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k = blScanCount readyP k) ∧
      (∀ v, v < 19 → (btFreq .bl scanned v).toNat = blScanCount readyP v) ∧
      BTRankLeaves .bl 19 7 scanned built ∧
      (dynamicHeaderBits ready mb).length = 14 + 3 * (mb.toInt.toNat + 1) +
        mass (fun k => blScanCount readyP k * (curL (TK.arr .bl built) k + blExtraBits k)) 19 ∧
      mb.toInt.toNat ≤ 18 := by
  obtain ⟨readyP, prepare, input, treesR, blKeep, _⟩ := Zlib.Trees.Proofs.bl_prepare trees
  replace prepare : blPrepare (some (.tab ds)) h = .ok ((), setD h ds readyP) := prepare
  replace treesR : TreesInvAt (setD h ds readyP) ds readyP pb buf := treesR
  have runB : Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds readyP) = .ok (mb, setD h ds ready) := by
    rw [bind_app, prepare] at run
    exact run
  have zeroBl : ∀ v, v < 19 → readyP.bl_tree[v]!.fc = 0 := by
    intro v hv
    rw [blKeep]
    exact clear.bl v hv
  obtain ⟨scanned, built, B, blRun, hs, fv, hframe, hIB, hrank⟩ := bl_build_rank treesR input zeroBl
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
  have idx : Zlib.Trees.Proofs.Math.blMaxIdx (Zlib.Trees.Proofs.blUsed built) 18 = mb.toInt.toNat := by
    rw [hmb]; simp
  rw [idx] at heF
  have mbLe : mb.toInt.toNat ≤ 18 := by
    rw [← idx]; exact Zlib.Trees.Proofs.Math.blMaxIdx_le _ 18
  -- the trees and descriptors of `ready`
  have litB := hframe.other_tree .lit (by decide +kernel)
  have distB := hframe.other_tree .dist (by decide +kernel)
  have lDescB := hframe.other_desc .lit (by decide +kernel)
  have dDescB := hframe.other_desc .dist (by decide +kernel)
  simp only [TK.arr, TK.getDesc] at litB distB lDescB dDescB
  have rL : ready.dyn_ltree = Zlib.Trees.Proofs.scGuard readyP.dyn_ltree readyP.l_desc.max_code.toInt.toNat := by
    rw [heF]; simp only []; rw [litB, hs]; rfl
  have rD : ready.dyn_dtree = Zlib.Trees.Proofs.scGuard readyP.dyn_dtree readyP.d_desc.max_code.toInt.toNat := by
    rw [heF]; simp only []; rw [distB, hs]; rfl
  have rLd : ready.l_desc = readyP.l_desc := by rw [heF]; simp only []; rw [lDescB, hs]; rfl
  have rDd : ready.d_desc = readyP.d_desc := by rw [heF]; simp only []; rw [dDescB, hs]; rfl
  have rB : ready.bl_tree = built.bl_tree := by rw [heF]
  obtain ⟨szL, szD, _, _, _, _⟩ := treesR.base.wf
  have l0 := input.l0
  have l286 := input.l286
  have d0 := input.d0
  have d30 := input.d30
  have sendL : sendLengths ready .lit =
      guarded (fun i => readyP.dyn_ltree[i]!.dl.toNat) readyP.l_desc.max_code.toInt.toNat := by
    funext i
    simp only [sendLengths, TK.arr]
    rw [rL]
    exact Zlib.Trees.Proofs.scGuard_lengths _ _ (by omega) i
  have sendD : sendLengths ready .dist =
      guarded (fun i => readyP.dyn_dtree[i]!.dl.toNat) readyP.d_desc.max_code.toInt.toNat := by
    funext i
    simp only [sendLengths, TK.arr]
    rw [rD]
    exact Zlib.Trees.Proofs.scGuard_lengths _ _ (by omega) i
  have small : ∀ (T : Array CtData) (M : Nat), (∀ i ≤ M, T[i]!.dl.toNat ≤ 15) →
      ∀ i, i < M + 1 → guarded (fun n => T[n]!.dl.toNat) M i ≤ 15 := by
    intro T M fit i lt
    simp only [guarded, show i ≠ M + 1 by omega, if_false]
    exact fit i (by omega)
  have tl := Zlib.Trees.Proofs.Out.treeBits_length (Zlib.Trees.Proofs.Out.blWords ready) _ _
    (small readyP.dyn_ltree readyP.l_desc.max_code.toInt.toNat input.llen)
  have td := Zlib.Trees.Proofs.Out.treeBits_length (Zlib.Trees.Proofs.Out.blWords ready) _ _
    (small readyP.dyn_dtree readyP.d_desc.max_code.toInt.toNat input.dlen)
  have hdr : (dynamicHeaderBits ready mb).length = 14 + 3 * (mb.toInt.toNat + 1) +
      (Zlib.Trees.Proofs.Out.treeBitsUpTo (Zlib.Trees.Proofs.Out.blWords ready)
        (guarded (fun i => readyP.dyn_ltree[i]!.dl.toNat) readyP.l_desc.max_code.toInt.toNat)
        (readyP.l_desc.max_code.toInt.toNat + 1)).length +
      (Zlib.Trees.Proofs.Out.treeBitsUpTo (Zlib.Trees.Proofs.Out.blWords ready)
        (guarded (fun i => readyP.dyn_dtree[i]!.dl.toNat) readyP.d_desc.max_code.toInt.toNat)
        (readyP.d_desc.max_code.toInt.toNat + 1)).length := by
    unfold dynamicHeaderBits
    rw [Zlib.Trees.Proofs.Out.allTreesBits_length, rLd, rDd, sendL, sendD]
    simp only [Zlib.Trees.Proofs.Out.sendTreeBits, Nat.add_sub_cancel]
  have weight : ∀ k, Zlib.Trees.Proofs.Out.blWeight (Zlib.Trees.Proofs.Out.blWords ready) k =
      curL (TK.arr .bl built) k + blExtraBits k := by
    intro k
    simp only [Zlib.Trees.Proofs.Out.blWeight, Zlib.Trees.Proofs.Out.blWords, curL, TK.arr, rB]
  refine ⟨readyP, scanned, built, input, ?_, fv, hrank, ?_, mbLe⟩
  · intro k
    rw [sendL, sendD, rLd, rDd]
    rfl
  · rw [hdr, tl, td, Nat.add_assoc, ← Zlib.Trees.Proofs.Out.mass_mul_add]
    congr 1
    apply mass_congr
    intro k _
    rw [weight]
    rfl

/-- `Σ a·(b + e) = Σ a·b + Σ a·e`. -/
theorem mass_mul_add_right (a b e : Nat → Nat) (n : Nat) :
    mass (fun k => a k * (b k + e k)) n = mass (fun k => a k * b k) n + mass (fun k => a k * e k) n := by
  rw [← mass_add]
  apply mass_congr
  intro k _
  rw [Nat.mul_add]

/-- The bit-length symbols of the lengths `scan_tree` reads above `top` are absent. -/
theorem scan_absent {ready readyP : DeflateState} (top : Nat)
    (scanEq : ∀ k, scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
      scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k = blScanCount readyP k)
    (lit : ∀ v, v ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit v ≤ top)
    (dist : ∀ v, v ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist v ≤ top) :
    ∀ k, top < k → k < 16 → blScanCount readyP k = 0 := by
  intro k lo hi
  rw [← scanEq k, scanFreq_absent _ _ k hi (fun i lt => by have := lit i (by omega); omega),
    scanFreq_absent _ _ k hi (fun i lt => by have := dist i (by omega); omega)]

/-- The bit-length symbols that can occur at `lit_bufsize = 256`: lengths up to 11 and 16..18. -/
def allowed256 (v : Nat) : Bool := decide (v ≤ 11 ∨ 16 ≤ v)

/-- The bit-length symbols that can occur at `lit_bufsize = 128`: lengths up to 9 and 16..18. -/
def allowed128 (v : Nat) : Bool := decide (v ≤ 9 ∨ 16 ≤ v)

/-- **H3 at `lit_bufsize = 256`**: the header is at most `71 + 245` bits plus the `κ0` header. -/
theorem header_ref_bound_256 : HeaderRefBound 245 := by
  intro h ds d xs mb ready prep size
  obtain ⟨pb, buf, trees, ledger⟩ := prep.base
  obtain ⟨readyP, scanned, built, input, scanEq, fv, rank, hdr, mbLe⟩ :=
    dynamic_header_rank trees prep.clear prep.run
  obtain ⟨litS, distS⟩ := prepared_lengths_256 trees ledger size prep.run
  have absent := scan_absent 11 scanEq litS distS
  have refEq : refHeaderCost ready = mass (fun k => blScanCount readyP k * refWeight k) 19 := by
    unfold refHeaderCost
    apply mass_congr
    intro k _
    rw [scanEq]
  have allowed : ∀ v, v < 19 → (btFreq .bl scanned v).toNat ≠ 0 → allowed256 v = true := by
    intro v hv nz
    rw [fv v hv] at nz
    simp only [allowed256, decide_eq_true_eq]
    by_cases lo : v ≤ 11
    · exact Or.inl lo
    · by_cases hi : 16 ≤ v
      · exact Or.inr hi
      · exact absurd (absent v (by omega) (by omega)) nz
  have bound : ∀ v, v < 19 → allowed256 v = true → 1 ≤ ZlibF.Math.DeflateOverlayCertificate.refLen v ∧
      ZlibF.Math.DeflateOverlayCertificate.refLen v ≤ 7 := by decide +kernel
  have kraft : Zlib.Trees.Proofs.GB.rs (fun v => if allowed256 v then 2 ^ (7 - ZlibF.Math.DeflateOverlayCertificate.refLen v) else 0)
      19 ≤ 2 ^ 7 := by decide +kernel
  have count : Zlib.Trees.Proofs.GB.rs (fun v => if allowed256 v then 1 else 0) 19 ≤ 15 := by decide +kernel
  have weightLe : Zlib.Trees.Proofs.GB.rs (fun v => (btFreq .bl scanned v).toNat) 19 ≤ 316 := by
    rw [Zlib.Trees.Proofs.rs_eq_mass, mass_congr fv]
    exact Zlib.Trees.Proofs.blScanCount_mass_le readyP input
  have core := rank.cost_le_15 allowed256 7 ZlibF.Math.DeflateOverlayCertificate.refLen allowed bound kraft count weightLe
  rw [Zlib.Trees.Proofs.rs_eq_mass, Zlib.Trees.Proofs.rs_eq_mass] at core
  have e1 : mass (fun v => (btFreq .bl scanned v).toNat * curL (TK.arr .bl built) v) 19 =
      mass (fun v => blScanCount readyP v * curL (TK.arr .bl built) v) 19 :=
    mass_congr (fun v hv => by rw [fv v hv])
  have e2 : mass (fun v => (btFreq .bl scanned v).toNat * ZlibF.Math.DeflateOverlayCertificate.refLen v) 19 =
      mass (fun v => blScanCount readyP v * ZlibF.Math.DeflateOverlayCertificate.refLen v) 19 :=
    mass_congr (fun v hv => by rw [fv v hv])
  rw [e1, e2] at core
  rw [hdr, refEq, mass_mul_add_right]
  unfold refWeight
  rw [mass_mul_add_right]
  omega

/-- **H3 at `lit_bufsize = 128`**: twice the header is at most `2·(71 + 29) + W` plus twice the
`κ1` header. -/
theorem header_ref_bound_128w : HeaderRefBound128W 29 := by
  intro h ds d xs mb ready prep size
  obtain ⟨pb, buf, trees, ledger⟩ := prep.base
  obtain ⟨readyP, scanned, built, input, scanEq, fv, rank, hdr, mbLe⟩ :=
    dynamic_header_rank trees prep.clear prep.run
  obtain ⟨litS, distS⟩ := prepared_lengths_128 trees ledger size prep.run
  have absent := scan_absent 9 scanEq litS distS
  have refEq : refHeaderCost128 ready = mass (fun k => blScanCount readyP k * refWeight1 k) 19 := by
    unfold refHeaderCost128
    apply mass_congr
    intro k _
    rw [scanEq]
  have wEq : bitLengthCount ready = mass (blScanCount readyP) 19 := by
    unfold bitLengthCount
    apply mass_congr
    intro k _
    rw [scanEq]
  have allowed : ∀ v, v < 19 → (btFreq .bl scanned v).toNat ≠ 0 → allowed128 v = true := by
    intro v hv nz
    rw [fv v hv] at nz
    simp only [allowed128, decide_eq_true_eq]
    by_cases lo : v ≤ 9
    · exact Or.inl lo
    · by_cases hi : 16 ≤ v
      · exact Or.inr hi
      · exact absurd (absent v (by omega) (by omega)) nz
  have bound : ∀ v, v < 19 → allowed128 v = true → 1 ≤ ZlibF.Math.DeflateOverlayCertificate128.refLen1 v ∧
      ZlibF.Math.DeflateOverlayCertificate128.refLen1 v ≤ 8 := by decide +kernel
  have kraft : Zlib.Trees.Proofs.GB.rs
      (fun v => if allowed128 v then 2 ^ (8 - ZlibF.Math.DeflateOverlayCertificate128.refLen1 v) else 0) 19 ≤ 2 ^ 8 := by
    decide +kernel
  have count : Zlib.Trees.Proofs.GB.rs (fun v => if allowed128 v then 1 else 0) 19 ≤ 13 := by decide +kernel
  have weightLe : Zlib.Trees.Proofs.GB.rs (fun v => (btFreq .bl scanned v).toNat) 19 ≤ 316 := by
    rw [Zlib.Trees.Proofs.rs_eq_mass, mass_congr fv]
    exact Zlib.Trees.Proofs.blScanCount_mass_le readyP input
  have core := rank.cost_le_13 allowed128 8 ZlibF.Math.DeflateOverlayCertificate128.refLen1 allowed bound kraft count weightLe
  rw [Zlib.Trees.Proofs.rs_eq_mass, Zlib.Trees.Proofs.rs_eq_mass, Zlib.Trees.Proofs.rs_eq_mass] at core
  have e1 : mass (fun v => (btFreq .bl scanned v).toNat * curL (TK.arr .bl built) v) 19 =
      mass (fun v => blScanCount readyP v * curL (TK.arr .bl built) v) 19 :=
    mass_congr (fun v hv => by rw [fv v hv])
  have e2 : mass (fun v => (btFreq .bl scanned v).toNat * ZlibF.Math.DeflateOverlayCertificate128.refLen1 v) 19 =
      mass (fun v => blScanCount readyP v * ZlibF.Math.DeflateOverlayCertificate128.refLen1 v) 19 :=
    mass_congr (fun v hv => by rw [fv v hv])
  have e3 : mass (fun v => (btFreq .bl scanned v).toNat) 19 = mass (blScanCount readyP) 19 :=
    mass_congr (fun v hv => by rw [fv v hv])
  rw [e1, e2, e3] at core
  rw [hdr, refEq, wEq, mass_mul_add_right]
  unfold refWeight1
  rw [mass_mul_add_right]
  omega

/-- **`TinyOverlayAt 256`**, with no hypothesis. -/
theorem tinyOverlayAt_256 : TinyOverlayAt 256 := by
  intro h r ds pb z d buf xs good trees ledger clear pending bits size z'
  exact dynamic_overlay_256c (by decide) header_ref_bound_256 good trees ledger clear pending bits size z'

/-- **`TinyOverlayAt 128`**, with no hypothesis. -/
theorem tinyOverlayAt_128 : TinyOverlayAt 128 := by
  intro h r ds pb z d buf xs good trees ledger clear pending bits size z'
  exact dynamic_overlay_128_w (by decide) header_ref_bound_128w good trees ledger clear pending bits size z'

/-- **`TinyOverlay`**, with no hypothesis. -/
theorem tinyOverlay : TinyOverlay := tinyOverlay_of_two tinyOverlayAt_128 tinyOverlayAt_256

#print axioms header_ref_bound_256
#print axioms header_ref_bound_128w
#print axioms tinyOverlayAt_256
#print axioms tinyOverlayAt_128
#print axioms tinyOverlay

end Zlib.Deflate.Engine.Proofs
