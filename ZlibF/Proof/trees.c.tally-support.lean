import ZlibF.Proof.«trees.c.bl-support»
import ZlibF.Proof.«trees.c.tally»

/-! # trees.c: retaining dynamic-header entry facts through actual tallies -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- Neither a literal nor a match tally writes the END_BLOCK frequency. -/
theorem tallyRec_end_block (d : DeflateState) (dist lc : UInt32)
    (hlit : dist = 0 → lc.toNat < 256) :
    (Out.tallyRec d dist lc).dyn_ltree[256]!.fc = d.dyn_ltree[256]!.fc := by
  unfold Out.tallyRec Out.tallyMatchRec Out.bumpFc
  split
  · rename_i hz
    have hne : ¬ (lc.toNat = 256 ∧ lc.toNat < d.dyn_ltree.size) := by
      have := hlit hz
      omega
    rw [Out.getElem!_set!, ite_eq_right hne]
  · rw [Out.getElem!_set!]
    rw [ite_eq_right (by omega)]

/-- Tallies leave the bit-length tree unchanged. -/
theorem tallyRec_bl_tree (d : DeflateState) (dist lc : UInt32) :
    (Out.tallyRec d dist lc).bl_tree = d.bl_tree := by
  unfold Out.tallyRec Out.tallyMatchRec
  split <;> rfl

/-- The three symbol stores advance sym_next by three. -/
theorem tallyRec_sym_next (d : DeflateState) (dist lc : UInt32) :
    (Out.tallyRec d dist lc).sym_next = d.sym_next + 1 + 1 + 1 := by
  unfold Out.tallyRec Out.tallyMatchRec
  split <;> rfl

/-- A finite composition of actual tally calls. This is a proof harness for
one block, not a replacement for a translated strategy loop. -/
def tallyCalls (s : DeflateStatePtr) : List (UInt32 × UInt32) → M Unit
  | [] => pure ()
  | (dist, lc) :: rest => do
      let _ ← «_tr_tally» s dist lc
      tallyCalls s rest

/-- Any capacity-bounded sequence of actual valid tallies retains the
END_BLOCK frequency and all bit-length frequencies on its actual heap.
No claim about the strategy's input history or emitted output is made here. -/
theorem tallyCalls_preserves {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hroom : d.sym_next.toNat + 3 * symbols.length ≤ d.sym_end.toNat) :
    ∃ (e : DeflateState) (buf' : Array UInt8),
      tallyCalls (Sp id) symbols h = .ok ((), Out.setD (Out.setB h b buf') id e) ∧
      Out.TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' ∧
      e.dyn_ltree[256]!.fc = d.dyn_ltree[256]!.fc ∧ e.bl_tree = d.bl_tree ∧
      e.sym_next.toNat = d.sym_next.toNat + 3 * symbols.length ∧ e.sym_end = d.sym_end := by
  induction symbols generalizing h d buf with
  | nil =>
    refine ⟨d, buf, ?_, ?_, rfl, rfl, by simp, rfl⟩
    · simp only [tallyCalls, pure_app, Out.setB_self hI.base.bytes, Out.setD_self hI.base.dstate]
    · simpa only [Out.setB_self hI.base.bytes, Out.setD_self hI.base.dstate] using hI
  | cons t rest ih =>
    obtain ⟨dist, lc⟩ := t
    have hvalid := hlegal (dist, lc) (by simp)
    have hstepRoom : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := by
      simp only [List.length_cons] at hroom
      omega
    obtain ⟨buf1, r, hstep, hI1, hflag, hsize, hbytes⟩ :=
      Out.tr_tally_spec hI dist lc hstepRoom (fun _ => hvalid.1) (fun _ => hvalid)
    let mid := Out.tallyRec d dist lc
    have hnext : mid.sym_next.toNat = d.sym_next.toNat + 3 := by
      have hbound : d.sym_next.toNat + 3 < 2 ^ 32 := by
        have := hI.base.sym_end
        have := hI.base.lit_hi
        omega
      rw [tallyRec_sym_next]
      have h1 := Out.toNat_add_one_u32 (x := d.sym_next) (by omega)
      have h2 := Out.toNat_add_one_u32 (x := d.sym_next + 1) (by rw [h1]; omega)
      have h3 := Out.toNat_add_one_u32 (x := d.sym_next + 1 + 1) (by rw [h2, h1]; omega)
      rw [h3, h2, h1]
    have hend : mid.sym_end = d.sym_end := (Out.tallyRec_fields d dist lc).2.2.2.2.1
    have hrestRoom : mid.sym_next.toNat + 3 * rest.length ≤ mid.sym_end.toNat := by
      rw [hnext, hend]
      simp only [List.length_cons] at hroom
      omega
    obtain ⟨e, buf', hrest, hIe, hEOB, hBL, hcount, hEnd⟩ :=
      ih hI1 (fun t ht => hlegal t (by simp [ht])) hrestRoom
    refine ⟨e, buf', ?_, ?_, ?_, ?_, ?_, hEnd.trans hend⟩
    · simp only [tallyCalls, bind_app, hstep]
      simpa only [Out.setB_setD, Out.setB_setB, Out.setD_setD] using hrest
    · simpa only [Out.setB_setD, Out.setB_setB, Out.setD_setD] using hIe
    · exact hEOB.trans (tallyRec_end_block d dist lc (fun _ => hvalid.1))
    · exact hBL.trans (tallyRec_bl_tree d dist lc)
    · rw [hcount, hnext, List.length_cons]
      omega

/-- Valid tallies within one block establish the actual dynamic-header
construction premises. The result is on the same heap after all calls. -/
theorem tallyCalls_prepare_bl_fields {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hroom : d.sym_next.toNat + 3 * symbols.length ≤ d.sym_end.toNat)
    (hEOB : d.dyn_ltree[256]!.fc ≠ 0) (hzero : ∀ k < 19, d.bl_tree[k]!.fc = 0) :
    ∃ (mb : Int32) (e : DeflateState) (buf' : Array UInt8),
      (do tallyCalls (Sp id) symbols; blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, Out.setD (Out.setB h b buf') id e) ∧
      3 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      257 ≤ e.l_desc.max_code.toInt + 1 ∧ e.l_desc.max_code.toInt + 1 ≤ 286 ∧
      1 ≤ e.d_desc.max_code.toInt + 1 ∧ e.d_desc.max_code.toInt + 1 ≤ 30 ∧
      (∀ v < 19, e.bl_tree[v]!.dl.toNat ≤ 7) ∧
      (∀ v < 19, e.bl_desc.max_code.toInt.toNat < v → e.bl_tree[v]!.dl = 0) ∧
      Out.TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' := by
  obtain ⟨counted, buf', htally, hIC, hEC, hBC, hcount, hEnd⟩ :=
    tallyCalls_preserves hI symbols hlegal hroom
  have hEC' : counted.dyn_ltree[256]!.fc ≠ 0 := by rwa [hEC]
  have hBC' : ∀ k < 19, counted.bl_tree[k]!.fc = 0 := by rwa [hBC]
  obtain ⟨mb, e, hbuild, hlo, hhi, hlL, hlH, hdL, hdH, hlen, hupper, hIe, hout⟩ :=
    prepare_build_bl_fields hIC hEC' hBC'
  refine ⟨mb, e, buf', ?_, hlo, hhi, hlL, hlH, hdL, hdH, hlen, hupper, ?_⟩
  · change (do blPrepare (Sp id); build_bl_tree (Sp id))
        (Out.setD (Out.setB h b buf') id counted) =
        .ok (mb, Out.setD (Out.setD (Out.setB h b buf') id counted) id e) at hbuild
    rw [bind_app, htally]
    simpa only [Out.setD_setD] using hbuild
  · change Out.TreesInvAt (Out.setD (Out.setD (Out.setB h b buf') id counted) id e) id e b buf' at hIe
    simpa only [Out.setD_setD] using hIe

/-- Actual init_block, any capacity-bounded list of valid actual tallies,
and actual literal/distance/bit-length construction supply all dynamic-header
field ranges. This proves the call composition, not the strategy loop that
produces the tallies, header emission, or the output/symbol overlay bound. -/
theorem init_tallies_prepare_bl_fields {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (symbols : List (UInt32 × UInt32))
    (hlegal : ∀ t ∈ symbols, t.2.toNat < 256 ∧ t.1.toNat ≤ 32768)
    (hroom : 3 * symbols.length ≤ d.sym_end.toNat) :
    ∃ (mb : Int32) (e : DeflateState) (buf' : Array UInt8),
      (do init_block (Sp id); tallyCalls (Sp id) symbols
          blPrepare (Sp id); build_bl_tree (Sp id)) h =
        .ok (mb, Out.setD (Out.setB h b buf') id e) ∧
      3 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧
      257 ≤ e.l_desc.max_code.toInt + 1 ∧ e.l_desc.max_code.toInt + 1 ≤ 286 ∧
      1 ≤ e.d_desc.max_code.toInt + 1 ∧ e.d_desc.max_code.toInt + 1 ≤ 30 ∧
      (∀ v < 19, e.bl_tree[v]!.dl.toNat ≤ 7) ∧
      (∀ v < 19, e.bl_desc.max_code.toInt.toNat < v → e.bl_tree[v]!.dl = 0) ∧
      Out.TreesInvAt (Out.setD (Out.setB h b buf') id e) id e b buf' := by
  obtain ⟨aL, aD, aB, initialized, hinit, hII, heI, hLs, hDs, hBs,
    hLzero, hEOB, hDzero, hBzero, hLdl, hDdl, hBdl⟩ := Out.init_block_spec0 hI.base hI.run.to0
  have hEI : initialized.dyn_ltree[256]!.fc ≠ 0 := by
    rw [heI]
    change aL[256]!.fc ≠ 0
    rw [hEOB]
    decide +kernel
  have hzI : ∀ k < 19, initialized.bl_tree[k]!.fc = 0 := by
    intro k hk
    rw [heI]
    exact hBzero k hk
  have hroomI : initialized.sym_next.toNat + 3 * symbols.length ≤ initialized.sym_end.toNat := by
    rw [heI]
    change (0 : UInt32).toNat + 3 * symbols.length ≤ d.sym_end.toNat
    simpa using hroom
  obtain ⟨mb, e, buf', hbuild, hlo, hhi, hlL, hlH, hdL, hdH, hlen, hupper, hIe⟩ :=
    tallyCalls_prepare_bl_fields hII symbols hlegal hroomI hEI hzI
  refine ⟨mb, e, buf', ?_, hlo, hhi, hlL, hlH, hdL, hdH, hlen, hupper, ?_⟩
  · rw [bind_app, hinit]
    simpa only [Out.setB_setD, Out.setD_setD] using hbuild
  · simpa only [Out.setB_setD, Out.setD_setD] using hIe

end Zlib.Trees.Proofs
