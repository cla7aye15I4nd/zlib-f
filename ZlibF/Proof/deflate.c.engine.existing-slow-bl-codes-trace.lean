import ZlibF.Proof.«deflate.c.engine.existing-slow-bl-rank-trace»
import ZlibF.Proof.«trees.c.build.emit»
namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false
/-- The actual canonical-code stores retain the maximum-seven repaired
rank lengths obtained from the real gen_bitlen execution. -/
theorem ws_btCodes_bl_rank_trace {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (helem : elems ≤ 286)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → (tk.arr d)[v]!.dl = 0)
    (limit : L = 7) :
    WS h0 id (btCodes (Sp id) (some r) (.ref (tk.ref id) 0) dd.max_code) d (fun _ result =>
      ∃ mid, GBDone tk d hm J maxc L xb slOpt mid ∧ GBStageTrace tk d hm J elems maxc L xb slOpt mid ∧
        (∃ a : Array CtData, result = tk.setArr mid a ∧ a.size = (tk.arr mid).size ∧
          ∀ j < a.size, a[j]! =
            if j < (dd.max_code.toInt + 1).toNat ∧ (tk.arr mid)[j]!.dl ≠ 0 then
              { (tk.arr mid)[j]! with fc := UInt16.ofNat (Math.storedCode
                (fun i => mid.bl_count[i]!.toNat) (fun i => (tk.arr mid)[i]!.dl.toNat) j) }
            else (tk.arr mid)[j]!) ∧
        BLRepairRanks tk d hm J elems maxc result) := by
  unfold btCodes
  refine WS.bind' (ws_gen_bitlen_bl_rank_trace hdd hsd hstat htree ctx hHM hel limit) ?_
  intro _ mid ⟨done, stage, ranks⟩
  have capacity : elems ≤ (tk.arr d).size := by have := ctx.nc; omega
  obtain ⟨counts, treeSize, lengths⟩ := done.code_inputs ctx.shape capacity ctx.L15 hzero
  have maxCode := ctx.mcv
  have maxBound := ctx.shape.maxc_lt
  have iterations : (dd.max_code.toInt + 1).toNat = maxc + 1 := by omega
  refine WS.bind' ws_pBlCount fun p e ⟨pointer, unchanged⟩ => ?_
  subst e; subst p
  refine WS.mono (ws_gen_codes mid tk dd.max_code (by omega) (by omega) (by omega)
    (by rw [iterations]; exact treeSize) (fun v bound => lengths v (by rw [iterations] at bound; omega))) ?_
  intro _ result ⟨a, fields, size, words⟩
  have lengths := code_stores_lengths fields size words
  refine ⟨mid,done,stage,⟨a,fields,size,words⟩,?_⟩
  intro nonzero
  obtain ⟨M,positive,rounds,rankLengths⟩ := ranks nonzero
  refine ⟨M,positive,rounds,?_⟩
  intro rank lower upper
  have equal : LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank =
      LeafRank.value (Hn d) (curL (tk.arr mid)) hm J maxc rank := by
    unfold LeafRank.value curL
    rw [lengths]
  rw [equal]
  exact rankLengths rank lower upper

#print axioms ws_btCodes_bl_rank_trace
end Zlib.Trees.Proofs
