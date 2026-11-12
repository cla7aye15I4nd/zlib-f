import ZlibF.Proof.«deflate.c.engine.fill-slide-invariant»
import ZlibF.Proof.«deflate.c.engine.pos-heap»

/-! # The slide of `fill_window` and the positional chains

`slide_heap_pchains` is `slide_heap_chains` for `PHeapChains`: the slid tables satisfy the positional
chains with `top` and the frontier lowered by `w_size`.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The arrays of the positional chains are those of the environment. -/
theorem pheap_arrays {h : Heap} {d : DeflateState} {w q p : Nat} {wa : Array UInt8} {qa pa : Array UInt16}
    {top stop : Nat} (env : HashEnv h d w q p wa qa pa) (chains : PHeapChains h d top stop) :
    PosChains (wfn qa) (wfn pa) d.hash_size d.w_size.toNat top stop := by
  obtain ⟨p0, q0, pa0, qa0, prev, head, hp, hq, H⟩ := chains
  have pe : p0 = p := by simpa only [env.prevp, Ptr.ref.injEq, WRef.blk.injEq, and_true] using prev.symm
  have qe : q0 = q := by simpa only [env.headp, Ptr.ref.injEq, WRef.blk.injEq, and_true] using head.symm
  subst p0 q0
  have pae : pa0 = pa := Option.some.inj (hp.symm.trans env.pwords)
  have qae : qa0 = qa := Option.some.inj (hq.symm.trans env.hwords)
  subst pa0 qa0
  exact H

/-- **The slide keeps the positional chains**, with `top` and the frontier lowered by `w_size`. -/
theorem slide_heap_pchains {h : Heap} {r : ZStreamRef} {ds w p q top stop : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : PHeapChains h d top stop)
    (head : ∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i)
    (prev : ∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) :
    PHeapChains (slideHeap h ds w p q d wa pa' qa') (slideState d) (top - d.w_size.toNat) (stop - d.w_size.toNat) := by
  have H := pheap_arrays env chains
  have sizes := slide_window_sizes good
  have slid := pos_slide (h2 := wfn qa') (p2 := wfn pa') H good.inv.wsize (by omega)
    (fun i hi => by rw [head, if_pos hi]) (fun i hi => by rw [prev, if_pos hi])
  refine ⟨p, q, pa', qa', env.prevp, env.headp, ?_, ?_, slid⟩
  · simp [slideHeap, setD, setW]
  · simp [slideHeap, setD, setW, upd_ne _ _ _ _ env.hne]

end Zlib.Deflate.Engine.Proofs
