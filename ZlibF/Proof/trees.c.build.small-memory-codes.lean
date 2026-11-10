import ZlibF.Proof.«trees.c.build.small-memory-source»
import ZlibF.Proof.«trees.c.build.tail»

/-! # Actual canonical-code assignment retains small-tree direct Fibonacci bounds -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- The actual final two build_tree calls establish FibPush on the final
stored lengths. gen_codes writes the frequency/code union but preserves
every length. Weights refer to the input tree before the union is reused.
All input weight facts are data established by actual heap construction. -/
theorem ws_btCodes_small_direct_fib {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (helem : elems ≤ 286)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → (tk.arr d)[v]!.dl = 0)
    (limit : L = 15)
    (sums : ∀ a, a < J → frn (tk.arr d) (elems + a) =
      frn (tk.arr d) (Hn d (572 - 2 * a)) + frn (tk.arr d) (Hn d (571 - 2 * a)))
    (ordered : ∀ q q', hm + 1 ≤ q' → q' ≤ q → q < 573 →
      frn (tk.arr d) (Hn d q) ≤ frn (tk.arr d) (Hn d q'))
    (positive : ∀ q, hm < q → q < 573 → 1 ≤ frn (tk.arr d) (Hn d q))
    (rootSmall : frn (tk.arr d) (Hn d hm) ≤ 1026) :
    WS h0 id (btCodes (Sp id) (some r) (.ref (tk.ref id) 0) dd.max_code) d (fun _ result =>
      ∃ mid, GBDone tk d hm J maxc L xb slOpt mid ∧ GBStageTrace tk d hm J elems maxc L xb slOpt mid ∧
        (∃ a : Array CtData, result = tk.setArr mid a ∧ a.size = (tk.arr mid).size ∧
          ∀ j < a.size, a[j]! =
            if j < (dd.max_code.toInt + 1).toNat ∧ (tk.arr mid)[j]!.dl ≠ 0 then
              { (tk.arr mid)[j]! with fc := UInt16.ofNat (Math.storedCode
                (fun i => mid.bl_count[i]!.toNat) (fun i => (tk.arr mid)[i]!.dl.toNat) j) }
            else (tk.arr mid)[j]!) ∧
        ∀ rank, 1 ≤ rank → rank ≤ LeafRank.count (Hn d) hm J maxc →
          LeafRank.value (Hn d) (frn (tk.arr d)) hm J maxc rank *
            HuffmanAbstract.fib (LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank + 1) ≤
              frn (tk.arr d) (Hn d hm)) := by
  unfold btCodes
  refine WS.bind' (ws_gen_bitlen_small_direct_fib hdd hsd hstat htree ctx hHM hel limit sums ordered positive rootSmall) ?_
  intro _ mid ⟨done, stage, fib⟩
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
  have lengthEqual (v : Nat) (bound : v ≤ maxc) : curL (tk.arr result) v = curL (tk.arr mid) v := by
    rw [fields, tk_arr_setArr]
    unfold curL
    rw [words v (by omega)]
    split <;> rfl
  refine ⟨mid, done, stage, ⟨a, fields, size, words⟩, ?_⟩
  intro rank lower upper
  have spec := LeafRank.index_spec lower upper
  have equal : LeafRank.value (Hn d) (curL (tk.arr result)) hm J maxc rank =
      LeafRank.value (Hn d) (curL (tk.arr mid)) hm J maxc rank := lengthEqual _ spec.2.1
  have claim := fib rank lower upper
  rw [equal]
  exact claim

end Zlib.Trees.Proofs

#print axioms Zlib.Trees.Proofs.ws_btCodes_small_direct_fib
