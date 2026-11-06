import ZlibF.Proof.«trees.c.send-tree»
import ZlibF.Proof.«trees.c.tally-support»

/-! # trees.c: deriving send_tree's data premises from actual construction -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- Length values actually read by the tree-description writer. -/
def sendLengths (d : DeflateState) (tk : TK) (i : Nat) : Nat := (tk.arr d)[i]!.dl.toNat

/-- Source storage and code data for the actual writer. No callee contract
or output-capacity assumption is a field. -/
structure SendTreeData (d : DeflateState) (tk : TK) : Prop where
  nonneg : 0 ≤ (tk.getDesc d).max_code.toInt
  max285 : (tk.getDesc d).max_code.toInt ≤ 285
  capacity : (tk.getDesc d).max_code.toInt.toNat + 1 < (tk.arr d).size
  lengths : ∀ i ≤ (tk.getDesc d).max_code.toInt.toNat, sendLengths d tk i ≤ 15
  codes : ∀ k < 19, 0 < scanFreqUpTo (sendLengths d tk) ((tk.getDesc d).max_code.toInt.toNat + 1) k →
    CodeFits (blWords d) k ∧ ∀ suffix : List Bool,
      ZlibF.Spec.decodeSym (Zlib.Inftrees.Proofs.lensOf (fun n => d.bl_tree[n]!.dl.toNat)
        (d.bl_desc.max_code.toInt.toNat + 1))
        (codeBits (blWords d) k ++ suffix) = some (k, suffix)

/-- Derived data and exact bit room suffice for the actual writer. -/
theorem SendTreeData.emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (tk : TK) (hd : SendTreeData d tk)
    (hr : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
      (sendTreeBits (blWords d) (sendLengths d tk) (tk.getDesc d).max_code.toInt.toNat).length ≤ 8 * buf.size) :
    Emit id b (send_tree (Sp id) (.ref (tk.ref id) 0) (tk.getDesc d).max_code) h d buf
      (sendTreeBits (blWords d) (sendLengths d tk) (tk.getDesc d).max_code.toInt.toNat)
      (d.bi_valid.toInt.toNat + (sendTreeBits (blWords d) (sendLengths d tk) (tk.getDesc d).max_code.toInt.toNat).length) := by
  exact send_tree_emit hI tk (sendLengths d tk) _ _ (by have := hd.nonneg; omega)
    (by have := hd.max285; omega) hd.capacity (fun _ _ => rfl) (fun _ => UInt16.toNat_lt _)
    hd.lengths (fun k hk hpos => (hd.codes k hk hpos).1) hr

/-- Complete actual BL construction establishes the source and code data
for both real send_tree calls. Initial zero BL frequencies prevent wrapping
from erasing a positively used source symbol. Output room is not assumed. -/
theorem build_bl_tree_ready_to_send {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hin : BLInput d)
    (hzero : ∀ k < 19, d.bl_tree[k]!.fc = 0) :
    ∃ (mb : Int32) (e : DeflateState), build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧
      TreesInvAt (setD h id e) id e b buf ∧
      (∀ tk : TK, tk ≠ .bl → SendTreeData e tk) := by
  obtain ⟨mb, scanned, built, e, B, hr, hs, hfreq, hframe, he, hmb, hlo, hhi, htail, hIe, hout, hcodes⟩ :=
    build_bl_tree_checked hI hin
  have hLT := hframe.other_tree .lit (by decide +kernel)
  have hDT := hframe.other_tree .dist (by decide +kernel)
  have hLD := hframe.other_desc .lit (by decide +kernel)
  have hDD := hframe.other_desc .dist (by decide +kernel)
  simp only [TK.arr] at hLT hDT
  simp only [TK.getDesc] at hLD hDD
  have hEL : e.dyn_ltree = scGuard d.dyn_ltree d.l_desc.max_code.toInt.toNat := by
    rw [he]
    change built.dyn_ltree = _
    rw [hLT, hs]
    rfl
  have hED : e.dyn_dtree = scGuard d.dyn_dtree d.d_desc.max_code.toInt.toNat := by
    rw [he]
    change built.dyn_dtree = _
    rw [hDT, hs]
    rfl
  have hELD : e.l_desc = d.l_desc := by
    rw [he]
    change built.l_desc = _
    rw [hLD, hs]
    rfl
  have hEDD : e.d_desc = d.d_desc := by
    rw [he]
    change built.d_desc = _
    rw [hDD, hs]
    rfl
  have hLsize := hI.base.wf.1
  have hDsize := hI.base.wf.2.1
  have hLM := hin.l286
  have hDM := hin.d30
  have hL0 := hin.l0
  have hD0 := hin.d0
  have hLCap : d.l_desc.max_code.toInt.toNat + 1 < d.dyn_ltree.size := by omega
  have hDCap : d.d_desc.max_code.toInt.toNat + 1 < d.dyn_dtree.size := by omega
  have hLfun : sendLengths e .lit = guarded (fun i => d.dyn_ltree[i]!.dl.toNat) d.l_desc.max_code.toInt.toNat := by
    funext i
    change e.dyn_ltree[i]!.dl.toNat = _
    rw [hEL]
    exact scGuard_lengths _ _ hLCap i
  have hDfun : sendLengths e .dist = guarded (fun i => d.dyn_dtree[i]!.dl.toNat) d.d_desc.max_code.toInt.toNat := by
    funext i
    change e.dyn_dtree[i]!.dl.toNat = _
    rw [hED]
    exact scGuard_lengths _ _ hDCap i
  have hfits : ∀ k < 19, 0 < blScanCount d k → CodeFits (blWords e) k ∧ ∀ suffix : List Bool,
      ZlibF.Spec.decodeSym (Zlib.Inftrees.Proofs.lensOf (fun n => e.bl_tree[n]!.dl.toNat)
        (e.bl_desc.max_code.toInt.toNat + 1))
        (codeBits (blWords e) k ++ suffix) = some (k, suffix) := by
    intro k hk hpos
    have hbound := blScanCount_le d hin k
    have hnat : B[k]!.fc.toNat = blScanCount d k := by
      rw [hfreq k, hzero k hk, UInt16.zero_add, UInt16.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have hnz : scanned.bl_tree[k]!.fc ≠ 0 := by
      rw [hs]
      change B[k]!.fc ≠ 0
      intro hz
      rw [hz] at hnat
      change 0 = blScanCount d k at hnat
      omega
    obtain ⟨maxc, hmax, hdesc, hacc, hword⟩ := hcodes
    have hdata := (hword k hk hnz).1
    refine ⟨?_, ?_⟩
    · change e.bl_tree[k]!.dl.toNat ≤ 15 ∧ e.bl_tree[k]!.fc.toNat < 2 ^ e.bl_tree[k]!.dl.toNat
      exact ⟨by have := hdata.2.1; omega, hdata.2.2.2⟩
    · rw [hdesc]
      simpa only [Int.toNat_natCast, codeBits, blWords] using (hword k hk hnz).2
  refine ⟨mb, e, hr, hIe, ?_⟩
  intro tk hne
  cases tk
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ e.l_desc.max_code.toInt
      rw [hELD]
      exact hL0
    · change e.l_desc.max_code.toInt ≤ 285
      rw [hELD]
      omega
    · change e.l_desc.max_code.toInt.toNat + 1 < e.dyn_ltree.size
      rw [hELD, hEL]
      simpa only [scGuard, Array.size_set!] using hLCap
    · intro i hi
      change i ≤ e.l_desc.max_code.toInt.toNat at hi
      rw [hELD] at hi
      rw [hLfun]
      rw [guarded, ite_eq_right (by omega)]
      exact hin.llen i hi
    · intro k hk hpos
      rw [hLfun] at hpos
      change 0 < scanFreqUpTo _ (e.l_desc.max_code.toInt.toNat + 1) k at hpos
      rw [hELD] at hpos
      exact hfits k hk (by unfold blScanCount; omega)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ e.d_desc.max_code.toInt
      rw [hEDD]
      exact hD0
    · change e.d_desc.max_code.toInt ≤ 285
      rw [hEDD]
      omega
    · change e.d_desc.max_code.toInt.toNat + 1 < e.dyn_dtree.size
      rw [hEDD, hED]
      simpa only [scGuard, Array.size_set!] using hDCap
    · intro i hi
      change i ≤ e.d_desc.max_code.toInt.toNat at hi
      rw [hEDD] at hi
      rw [hDfun]
      rw [guarded, ite_eq_right (by omega)]
      exact hin.dlen i hi
    · intro k hk hpos
      rw [hDfun] at hpos
      change 0 < scanFreqUpTo _ (e.d_desc.max_code.toInt.toNat + 1) k at hpos
      rw [hEDD] at hpos
      exact hfits k hk (by unfold blScanCount; omega)
  · exact False.elim (hne rfl)

/-- Actual block initialization, any capacity-bounded list of legal actual
tallies, and all three actual tree constructors establish both senders'
data and independent symbol meaning. This is a call-composition result;
strategy input history, full header emission and overlay room remain separate. -/
theorem init_tallies_ready_to_send {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hroom : 3 * symbols.length ≤ d.sym_end.toNat) :
    ∃ (mb : Int32) (e : DeflateState) (buf' : Array UInt8),
      (do init_block (Sp id); tallyCalls (Sp id) symbols
          blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, Out.setD (Out.setB h b buf') id e) ∧
      TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' ∧
      (∀ tk : TK, tk ≠ .bl → SendTreeData e tk) := by
  obtain ⟨aL, aD, aB, initialized, hinit, hII, heI, hLs, hDs, hBs,
    hLzero, hEOB, hDzero, hBzero, hLdl, hDdl, hBdl⟩ := init_block_spec0 hI.base hI.run.to0
  have hroomI : initialized.sym_next.toNat + 3 * symbols.length ≤ initialized.sym_end.toNat := by
    rw [heI]
    change (0 : UInt32).toNat + 3 * symbols.length ≤ d.sym_end.toNat
    simpa using hroom
  obtain ⟨counted, buf', htally, hIC, hEC, hBC, hcount, hEnd⟩ :=
    tallyCalls_preserves hII symbols hlegal hroomI
  obtain ⟨ready, hprepare, hin, hIR, hBready, hout⟩ := bl_prepare hIC
  have hzeroR : ∀ k < 19, ready.bl_tree[k]!.fc = 0 := by
    intro k hk
    rw [hBready, hBC, heI]
    exact hBzero k hk
  obtain ⟨mb, e, hbuild, hIe, hdata⟩ := build_bl_tree_ready_to_send hIR hin hzeroR
  have hDsame : Zlib.Trees.Proofs.setD = Out.setD := rfl
  simp only [hDsame, Out.setB_setD, Out.setD_setD] at htally hprepare hbuild hIe
  refine ⟨mb, e, buf', ?_, hIe, hdata⟩
  simp only [bind_app, hinit, htally, hprepare]
  exact hbuild

end Zlib.Trees.Proofs
