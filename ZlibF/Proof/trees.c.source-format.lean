import ZlibF.Proof.«trees.c.header-decode»

/-! # trees.c: source-alphabet format facts from actual construction -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- Data facts for the constructed literal/length and distance alphabets. -/
structure SourceFormatData (d : DeflateState) : Prop where
  lit : ZlibF.Spec.Acceptable .litLen
    (lens (sendLengths d .lit) (d.l_desc.max_code.toInt.toNat + 1))
  dist : ZlibF.Spec.Acceptable .dist
    (lens (sendLengths d .dist) (d.d_desc.max_code.toInt.toNat + 1))
  eob : ZlibF.Spec.HasEndOfBlock
    (lens (sendLengths d .lit) (d.l_desc.max_code.toInt.toNat + 1))

/-- Actual literal and distance construction establish the independent
source-alphabet acceptance rules and retain the used END_BLOCK symbol. -/
theorem bl_prepare_source_format {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hEOB : d.dyn_ltree[256]!.fc ≠ 0) :
    ∃ e : DeflateState, blPrepare (Sp id) h = .ok ((), setD h id e) ∧ SourceFormatData e := by
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
  have hlDesc := hframeD.other_desc .lit (by decide +kernel)
  have hlTree := hframeD.other_tree .lit (by decide +kernel)
  simp only [TK.getDesc, TK.arr] at hlDesc hlTree hmaxL hmaxD
  have hLN : dist.l_desc.max_code.toInt.toNat = ML := by rw [hlDesc, hmaxL]; omega
  have hDN : dist.d_desc.max_code.toInt.toNat = MD := by rw [hmaxD]; omega
  have hLit : lens (sendLengths dist .lit) (dist.l_desc.max_code.toInt.toNat + 1) =
      Zlib.Inftrees.Proofs.lensOf (fun n => lit.dyn_ltree[n]!.dl.toNat) (ML + 1) := by
    rw [hLN]
    unfold lens Zlib.Inftrees.Proofs.lensOf sendLengths
    simp only [TK.arr, hlTree]
  have hDist : lens (sendLengths dist .dist) (dist.d_desc.max_code.toInt.toNat + 1) =
      Zlib.Inftrees.Proofs.lensOf (fun n => dist.dyn_dtree[n]!.dl.toNat) (MD + 1) := by
    rw [hDN]
    rfl
  obtain ⟨used, hused, hpositive, hbound⟩ := bl_prepare_used hI 256 (by decide +kernel) hEOB
  simp only [TK.descRef] at hrL hrD
  have hrun : blPrepare (Sp id) h = .ok ((), setD h id dist) := by
    have hpL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
      unfold pLdesc
      rw [bind_app, sid_run hI.base.dstate]
      rfl
    have hpD : pDdesc (Sp id) (setD h id lit) = .ok (some (.in_dstate_d_desc id), setD h id lit) := by
      unfold pDdesc
      rw [bind_app, sid_run (setD_dstates_same h id lit)]
      rfl
    unfold blPrepare
    rw [bind_app, hpL]
    simp only []
    rw [bind_app, hrL]
    simp only []
    rw [bind_app, hpD]
    exact hrD
  have he : used = dist := same_record_of_runs hused hrun
  subst used
  refine ⟨dist, hrun, ?_, ?_, ?_⟩
  · rw [hLit]
    exact haccL .litLen
  · rw [hDist]
    exact haccD .dist
  · change (lens (sendLengths dist .lit) (dist.l_desc.max_code.toInt.toNat + 1)).getD 256 0 ≠ 0
    have hi : 256 < dist.l_desc.max_code.toInt.toNat + 1 := by omega
    rw [lens, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    change dist.dyn_ltree[256]!.dl.toNat ≠ 0
    omega

/-- Actual BL construction preserves both independent source-alphabet
acceptance rules and END_BLOCK, including the scan sentinel writes. -/
theorem build_bl_preserves_source_format {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hin : BLInput d) (hf : SourceFormatData d) :
    ∃ (mb : Int32) (e : DeflateState), build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧ SourceFormatData e := by
  obtain ⟨mb, e, hr, hLD, hDD, hLT, hDT, hIe, hout⟩ := build_bl_preserves_source_codes hI hin
  have hL : lens (sendLengths e .lit) (e.l_desc.max_code.toInt.toNat + 1) =
      lens (sendLengths d .lit) (d.l_desc.max_code.toInt.toNat + 1) := by
    rw [hLD]
    apply lens_congr
    intro i hi
    change e.dyn_ltree[i]!.dl.toNat = d.dyn_ltree[i]!.dl.toNat
    rw [hLT i (by omega)]
  have hD : lens (sendLengths e .dist) (e.d_desc.max_code.toInt.toNat + 1) =
      lens (sendLengths d .dist) (d.d_desc.max_code.toInt.toNat + 1) := by
    rw [hDD]
    apply lens_congr
    intro i hi
    change e.dyn_dtree[i]!.dl.toNat = d.dyn_dtree[i]!.dl.toNat
    rw [hDT i (by omega)]
  exact ⟨mb, e, hr, ⟨hL.symm ▸ hf.lit, hD.symm ▸ hf.dist, hL.symm ▸ hf.eob⟩⟩

/-- Initialization and actual tallies establish END_BLOCK frequency;
actual source and BL constructors then establish the source-format data. -/
theorem init_tallies_source_format {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hcapacity : 3 * symbols.length ≤ d.sym_end.toNat) :
    ∃ (mb : Int32) (e : DeflateState) (buf' : Array UInt8),
      (do init_block (Sp id); tallyCalls (Sp id) symbols
          blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, Out.setD (Out.setB h b buf') id e) ∧ SourceFormatData e := by
  obtain ⟨aL, aD, aB, initialized, hinit, hII, heI, hLs, hDs, hBs,
    hLzero, hEOB, hDzero, hBzero, hLdl, hDdl, hBdl⟩ := init_block_spec0 hI.base hI.run.to0
  have hroomI : initialized.sym_next.toNat + 3 * symbols.length ≤ initialized.sym_end.toNat := by
    rw [heI]
    change (0 : UInt32).toNat + 3 * symbols.length ≤ d.sym_end.toNat
    simpa using hcapacity
  obtain ⟨counted, buf', htally, hIC, hEC, hBC, hcount, hEnd⟩ :=
    tallyCalls_preserves hII symbols hlegal hroomI
  have hCEOB : counted.dyn_ltree[256]!.fc ≠ 0 := by
    rw [hEC, heI]
    change aL[256]!.fc ≠ 0
    rw [hEOB]
    decide +kernel
  obtain ⟨ready, hprepare, hin, hIR, hBready, hout⟩ := bl_prepare hIC
  obtain ⟨formatted, hformatted, hfmt⟩ := bl_prepare_source_format hIC hCEOB
  have hEq : formatted = ready := same_record_of_runs hformatted hprepare
  subst formatted
  obtain ⟨mb, e, hbuild, hFe⟩ := build_bl_preserves_source_format hIR hin hfmt
  have hDsame : Zlib.Trees.Proofs.setD = Out.setD := rfl
  simp only [hDsame, Out.setB_setD, Out.setD_setD] at htally hprepare hbuild
  refine ⟨mb, e, buf', ?_, hFe⟩
  simp only [bind_app, hinit, htally, hprepare]
  exact hbuild

/-- Actual construction establishes every header-format premise. The
actual count-argument call emits that header under exact bit room. The
header composes with any independent payload for these source alphabets;
the actual compressor's payload and its overlay bound remain open. -/
theorem atPrepared_dynamic_header {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hcapacity : 3 * symbols.length ≤ d.sym_end.toNat) :
    ∃ (mb : Int32) (built : DeflateState) (prepared : Array UInt8),
      (do init_block (Sp id); tallyCalls (Sp id) symbols
          blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, Out.setD (Out.setB h b prepared) id built) ∧
      (let L := built.l_desc.max_code.toInt.toNat + 1
       let D := built.d_desc.max_code.toInt.toNat + 1
       let B := mb.toInt.toNat + 1
       let bits := allTreesBits (blWords built) (sendLengths built .lit) (sendLengths built .dist) L D B
       (∀ (dict history out : List UInt8) (payload rest : List Bool),
         ZlibF.Spec.Symbols (lens (sendLengths built .lit) L) (lens (sendLengths built .dist) D)
           dict history payload rest out →
         ZlibF.Spec.Body dict 2 history (bits ++ payload) rest out) ∧
       (8 * built.pending.toNat + built.bi_valid.toInt.toNat + bits.length ≤ 8 * prepared.size →
         ∃ (e : DeflateState) (buf' : Array UInt8),
           atPrepared (Sp id) symbols h = .ok ((), Out.setD (Out.setB h b buf') id e) ∧
           TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' ∧
           outBits buf' e = outBits prepared built ++ bits ∧ BitsDiff built e)) := by
  obtain ⟨mb, built, prepared, hbuild, hIb, hdata, hguards, htable, hlo, hhi⟩ :=
    init_tallies_header_tables hI symbols hlegal hcapacity
  obtain ⟨mb2, e2, buf2, hr2, hformat⟩ := init_tallies_source_format hI symbols hlegal hcapacity
  have hpair := Prod.mk.inj (Except.ok.inj (hbuild.symm.trans hr2))
  have hrecord := congrArg (fun H : Heap => H.dstates id) hpair.2
  simp only [Out.setD_dstates_same] at hrecord
  have he : built = e2 := Option.some.inj hrecord
  subst e2
  refine ⟨mb, built, prepared, hbuild, ?_⟩
  dsimp only
  refine ⟨?_, ?_⟩
  · intro dict history out payload rest hp
    exact allTreeData_dynamic_body hdata hguards htable hformat.eob hformat.lit hformat.dist
      dict history out payload rest hp
  · intro hroom
    obtain ⟨buf', e, hcall, hIe, hbits, hsize, hframe, hplo, hphi, hdiff⟩ :=
      atCall_emit hIb mb _ _ _ hdata (by omega) hroom
    refine ⟨e, buf', ?_, ?_, hbits, hdiff⟩
    · rw [atPrepared_eq, bind_app, hbuild]
      simpa only [Out.setB_setD, Out.setB_setB, Out.setD_setD] using hcall
    · simpa only [Out.setB_setD, Out.setB_setB, Out.setD_setD] using hIe

end Zlib.Trees.Proofs
