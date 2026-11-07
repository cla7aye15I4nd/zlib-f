import ZlibF.Proof.«trees.c.bl-tree»
import ZlibF.Proof.«trees.c.build.lengths»
import ZlibF.Math.DeflateRunSupport

/-! # trees.c: deriving the minimum dynamic-header length count

The search's lower bound comes from actual source-frequency support and
zero initialization, not an assumed result of the search.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- A successful independent decoder result is an actual alphabet index. -/
theorem decodeSym_index_bound {lens : List Nat} {bits rest : List Bool} {v : Nat}
    (hd : ZlibF.Spec.decodeSym lens bits = some (v, rest)) : v < lens.length := by
  unfold ZlibF.Spec.decodeSym at hd
  split at hd
  · rename_i w hw
    have hm := List.mem_of_find?_eq_some hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, hrest⟩ := hd
    exact List.mem_range.mp hm
  · contradiction

/-- Two actual runs of the same computation have the same live record. -/
theorem same_record_of_runs {α : Type} {m : M α} {h : Heap} {id : Nat}
    {a a' : α} {d d' : DeflateState}
    (hr : m h = .ok (a, setD h id d)) (hr' : m h = .ok (a', setD h id d')) : d = d' := by
  have hp := (Prod.mk.inj (Except.ok.inj (hr.symm.trans hr'))).2
  have hs := congrArg (fun heap : Heap => heap.dstates id) hp
  exact Option.some.inj (by simpa only [setD_dstates_same] using hs)

/-- A positive literal-tree length contributes positive ordinary-symbol
frequency to the actual scan model. The sentinel completes its pending run. -/
theorem blScanCount_literal_support (d : DeflateState) (hin : BLInput d) (v : Nat)
    (hv : v ≤ d.l_desc.max_code.toInt.toNat) (hp : 0 < d.dyn_ltree[v]!.dl.toNat) :
    0 < blScanCount d d.dyn_ltree[v]!.dl.toNat := by
  let L := fun i : Nat => d.dyn_ltree[i]!.dl.toNat
  let M := d.l_desc.max_code.toInt.toNat
  have hdone := scan_guard_finishes L M hin.llen
  have hseen : Out.guarded L M v = L v := by
    simp only [Out.guarded, ite_eq_right (show v ≠ M + 1 by omega)]
  have hf := Out.scanFreq_seen_done (Out.guarded L M) (M + 1) v (L v) (by omega) hp hseen hdone
  dsimp only [L, M] at hf
  unfold blScanCount
  omega

/-- The actual literal/distance constructor pair retains a positive length
and a containing final alphabet for every originally used literal symbol. -/
theorem bl_prepare_used {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (v : Nat) (hv : v < 286) (hf : d.dyn_ltree[v]!.fc ≠ 0) :
    ∃ e : DeflateState, blPrepare (Sp id) h = .ok ((), setD h id e) ∧
      1 ≤ e.dyn_ltree[v]!.dl.toNat ∧ v ≤ e.l_desc.max_code.toInt.toNat := by
  obtain ⟨aL, lit, hrL, hframeL, husable, M, hM, hmax, haccept, hdecode⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0)
    (merge_ws_and (ws_build_tree_usable_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0)
      (ws_build_tree_decodable_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0))
  have haL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self hI.base.dstate] at hrL
  have hIL := hframeL.treesInvAt hI
  obtain ⟨aD, dist, hrD, hframeD⟩ := ws_build_tree_frame_initialized (h0 := h) .dist
    hIL.base.wf hIL.base.static hIL.run.to0
  have haD : aD = () := Subsingleton.elim _ _
  subst aD
  have hlDesc := hframeD.other_desc .lit (by decide +kernel)
  have hlTree := hframeD.other_tree .lit (by decide +kernel)
  simp only [TK.getDesc, TK.arr] at hlDesc hlTree hmax
  have hlen := (husable v hv hf).1
  have hbound := decodeSym_index_bound (hdecode v hv hf [])
  simp only [Zlib.Inftrees.Proofs.lensOf, List.length_map, List.length_range] at hbound
  simp only [TK.descRef] at hrL hrD
  refine ⟨dist, ?_, ?_, ?_⟩
  · have hpL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
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
  · rw [hlTree]
    exact hlen
  · rw [hlDesc]
    omega

/-- Nonzero END_BLOCK frequency and the cleared bit-length frequencies are
internal block data. Actual constructors and scans turn them into a search
index at least three. No index bound or callee contract is assumed. The
following theorem establishes both data premises by actual init_block. -/
theorem prepare_build_bl_min {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hEOB : d.dyn_ltree[256]!.fc ≠ 0)
    (hzero : ∀ k < 19, d.bl_tree[k]!.fc = 0) :
    ∃ (mb : Int32) (e : DeflateState),
      (do blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id e) ∧
      3 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d := by
  obtain ⟨ready, hready, hin, hIR, hBready, houtR⟩ := bl_prepare hI
  obtain ⟨used, hused, hpos, hcontained⟩ := bl_prepare_used hI 256 (by decide +kernel) hEOB
  have heq : used = ready := same_record_of_runs hused hready
  subst used
  let code := ready.dyn_ltree[256]!.dl.toNat
  have hc0 : 0 < code := by dsimp [code]; omega
  have hc16 : code < 16 := by have := hin.llen 256 hcontained; dsimp [code]; omega
  have hcount : 0 < blScanCount ready code := blScanCount_literal_support ready hin 256 hcontained hc0
  have hbound := blScanCount_le ready hin code
  have hzeroR : ready.bl_tree[code]!.fc = 0 := by rw [hBready]; exact hzero code (by omega)
  obtain ⟨mb, scanned, built, e, B, hbuild, hs, hfreq, hframe, he, hmb, hlo, hhi, htail, hIe, hout, hcodes⟩ :=
    build_bl_tree_checked hIR hin
  have hBnat : B[code]!.fc.toNat = blScanCount ready code := by
    rw [hfreq code, hzeroR, UInt16.zero_add, UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hsource : scanned.bl_tree[code]!.fc ≠ 0 := by
    rw [hs]
    change B[code]!.fc ≠ 0
    intro hz
    rw [hz] at hBnat
    change 0 = blScanCount ready code at hBnat
    omega
  obtain ⟨maxc, hmaxc, hdesc, haccept, hsymbols⟩ := hcodes
  have hlen := (hsymbols code (by omega) hsource).1.1
  have hnonzero : e.bl_tree[code]!.dl ≠ 0 := by
    intro hz
    rw [hz] at hlen
    change 1 ≤ 0 at hlen
    omega
  have hindex := bl_index_ge_of_nonrepeat e code hc16 hnonzero
  have husedEq : blUsed e = blUsed built := by rw [he]; rfl
  rw [husedEq] at hindex
  rw [setD_setD] at hbuild hIe
  refine ⟨mb, e, ?_, by omega, hhi, hIe, hout.trans houtR⟩
  rw [bind_app, hready]
  exact hbuild

/-- Actual block initialization discharges END_BLOCK support and cleared
bit-length frequencies. The actual constructor/search sequence then returns
3..18, so its transmitted entry count is 4..19. Streaming tally preservation
and full block emission remain separate obligations. -/
theorem init_prepare_build_bl_min {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) :
    ∃ (mb : Int32) (e : DeflateState),
      (do init_block (Sp id); blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, setD h id e) ∧
      3 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      Out.TreesInvAt (setD h id e) id e b buf := by
  obtain ⟨aL, aD, aB, initialized, hinit, hII, heI, hLs, hDs, hBs,
    hLzero, hEOB, hDzero, hBzero, hLdl, hDdl, hBdl⟩ := Out.init_block_spec0 hI.base hI.run.to0
  change init_block (Sp id) h = .ok ((), setD h id initialized) at hinit
  change Out.TreesInvAt (setD h id initialized) id initialized b buf at hII
  have hEOBI : initialized.dyn_ltree[256]!.fc ≠ 0 := by
    rw [heI]
    change aL[256]!.fc ≠ 0
    rw [hEOB]
    decide +kernel
  have hzI : ∀ k < 19, initialized.bl_tree[k]!.fc = 0 := by
    intro k hk
    rw [heI]
    exact hBzero k hk
  obtain ⟨mb, e, hbuild, hlo, hhi, hIe, hout⟩ := prepare_build_bl_min hII hEOBI hzI
  rw [setD_setD] at hbuild hIe
  refine ⟨mb, e, ?_, hlo, hhi, hIe⟩
  rw [bind_app, hinit]
  exact hbuild

/-- Complete actual bit-length construction bounds all nineteen lengths,
including unused symbols above the final alphabet maximum. -/
theorem build_bl_tree_all_lengths {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (mb : Int32) (e : DeflateState),
      build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧
      (∀ v < 19, e.bl_tree[v]!.dl.toNat ≤ 7) ∧
      (∀ v < 19, e.bl_desc.max_code.toInt.toNat < v → e.bl_tree[v]!.dl = 0) ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d := by
  obtain ⟨scanned, B, hscan, hs, hIS, houtS, hBs, hdl, hfreq⟩ := bl_scan_pair hI hin
  obtain ⟨a, built, hcodes, hframe, hlen, hupper⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0)
    (ws_build_tree_all_lengths_initialized (h0 := h) .bl hIS.base.wf hIS.base.static hIS.run.to0)
  have ha : a = () := Subsingleton.elim _ _
  subst a
  have hIB := hframe.treesInvAt hIS
  rw [setD_setD] at hIB
  have hbuild : blBuild (Sp id) h = .ok ((), setD h id built) := by
    have hp : pBldesc (Sp id) (setD h id scanned) =
        .ok (some (.in_dstate_bl_desc id), setD h id scanned) := by
      unfold pBldesc
      rw [bind_app, Out.sid_run (setD_dstates_same h id scanned)]
      rfl
    unfold blBuild
    rw [bind_app, hscan]
    simp only []
    rw [bind_app, hp]
    exact hcodes
  obtain ⟨mb, e, hfinish, hmb, he⟩ := ws_blFinish (h0 := h) (id := id) (d := built)
    (by obtain ⟨hl, hd, hbl, rest⟩ := hIB.base.wf; omega)
  have hcost := blCost_frame built (built.opt_len + blHeaderCost (Math.blMaxIdx (blUsed built) 18))
  have hIe := hcost.treesInvAt hIB
  rw [setD_setD] at hIe
  refine ⟨mb, e, ?_, ?_, ?_, ?_, ?_⟩
  · rw [build_bl_tree_eq, bind_app, hbuild]
    exact hfinish
  · rw [he]
    exact hlen
  · rw [he]
    exact hupper
  · rw [he]; exact hIe
  · rw [he]
    exact (hcost.outBits buf).trans ((hframe.outBits buf).trans houtS)

/-- All dynamic-header count ranges and all nineteen three-bit length
values are derived on the same returned heap. END_BLOCK and cleared BL
frequencies are internal block data, not assumed callee specifications. -/
theorem prepare_build_bl_fields {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (hEOB : d.dyn_ltree[256]!.fc ≠ 0)
    (hzero : ∀ k < 19, d.bl_tree[k]!.fc = 0) :
    ∃ (mb : Int32) (e : DeflateState),
      (do blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id e) ∧
      3 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      257 ≤ e.l_desc.max_code.toInt + 1 ∧ e.l_desc.max_code.toInt + 1 ≤ 286 ∧
      1 ≤ e.d_desc.max_code.toInt + 1 ∧ e.d_desc.max_code.toInt + 1 ≤ 30 ∧
      (∀ v < 19, e.bl_tree[v]!.dl.toNat ≤ 7) ∧
      (∀ v < 19, e.bl_desc.max_code.toInt.toNat < v → e.bl_tree[v]!.dl = 0) ∧
      Out.TreesInvAt (setD h id e) id e b buf ∧ Out.outBits buf e = Out.outBits buf d := by
  obtain ⟨ready, hready, hin, hIR, hBready, houtR⟩ := bl_prepare hI
  obtain ⟨used, hused, hpos, hcontained⟩ := bl_prepare_used hI 256 (by decide +kernel) hEOB
  have heq : used = ready := same_record_of_runs hused hready
  subst used
  obtain ⟨mb, e, hr, hlen, hupper, hIe, hout⟩ := build_bl_tree_all_lengths hIR hin
  obtain ⟨mbS, eS, hrS, hLdesc, hDdesc, hLtree, hDtree, hIS, houtS⟩ :=
    build_bl_preserves_source_codes hIR hin
  have heqS : eS = e := same_record_of_runs hrS hr
  subst eS
  rw [setD_setD] at hr hIe
  have hfull : (do blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id e) := by
    rw [bind_app, hready]
    exact hr
  obtain ⟨mbMin, eMin, hrMin, hlo, hhi, hIMin, houtMin⟩ := prepare_build_bl_min hI hEOB hzero
  have hv : mb = mbMin := (Prod.mk.inj (Except.ok.inj (hfull.symm.trans hrMin))).1
  rw [← hv] at hlo hhi
  have hl0 := hin.l0
  have hl286 := hin.l286
  have hd0 := hin.d0
  have hd30 := hin.d30
  refine ⟨mb, e, hfull, hlo, hhi, ?_, ?_, ?_, ?_, hlen, hupper, hIe, hout.trans houtR⟩
  · rw [hLdesc]
    omega
  · rw [hLdesc]
    omega
  · rw [hDdesc]
    omega
  · rw [hDdesc]
    omega

/-- Actual initialization and the complete actual tree-description prefix
supply the format's HLIT, HDIST and HCLEN ranges and every transmitted
three-bit length bound. This theorem does not yet execute send_all_trees or
prove preservation through intervening streaming tallies. -/
theorem init_prepare_build_bl_fields {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) :
    ∃ (mb : Int32) (e : DeflateState),
      (do init_block (Sp id); blPrepare (Sp id); build_bl_tree (Sp id)) h = .ok (mb, setD h id e) ∧
      3 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      257 ≤ e.l_desc.max_code.toInt + 1 ∧ e.l_desc.max_code.toInt + 1 ≤ 286 ∧
      1 ≤ e.d_desc.max_code.toInt + 1 ∧ e.d_desc.max_code.toInt + 1 ≤ 30 ∧
      (∀ v < 19, e.bl_tree[v]!.dl.toNat ≤ 7) ∧
      (∀ v < 19, e.bl_desc.max_code.toInt.toNat < v → e.bl_tree[v]!.dl = 0) ∧
      Out.TreesInvAt (setD h id e) id e b buf := by
  obtain ⟨aL, aD, aB, initialized, hinit, hII, heI, hLs, hDs, hBs,
    hLzero, hEOB, hDzero, hBzero, hLdl, hDdl, hBdl⟩ := Out.init_block_spec0 hI.base hI.run.to0
  change init_block (Sp id) h = .ok ((), setD h id initialized) at hinit
  change Out.TreesInvAt (setD h id initialized) id initialized b buf at hII
  have hEOBI : initialized.dyn_ltree[256]!.fc ≠ 0 := by
    rw [heI]
    change aL[256]!.fc ≠ 0
    rw [hEOB]
    decide +kernel
  have hzI : ∀ k < 19, initialized.bl_tree[k]!.fc = 0 := by
    intro k hk
    rw [heI]
    exact hBzero k hk
  obtain ⟨mb, e, hbuild, hlo, hhi, hlL, hlH, hdL, hdH, hlen, hupper, hIe, hout⟩ :=
    prepare_build_bl_fields hII hEOBI hzI
  rw [setD_setD] at hbuild hIe
  refine ⟨mb, e, ?_, hlo, hhi, hlL, hlH, hdL, hdH, hlen, hupper, hIe⟩
  rw [bind_app, hinit]
  exact hbuild

end Zlib.Trees.Proofs
