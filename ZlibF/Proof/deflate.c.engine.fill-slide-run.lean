import ZlibF.Proof.«deflate.c.engine.fill-slide-source»

/-! # Execution of fill_window's complete sliding prefix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def slideWindow (d : DeflateState) (wa : Array UInt8) : Array UInt8 :=
  copyRange wa wa 0 d.w_size.toNat (d.w_size - fillMore d).toNat

def slideHeap (h : Heap) (ds w p q : Nat) (d : DeflateState) (wa : Array UInt8)
    (pa qa : Array UInt16) : Heap :=
  setD (setW (setW { h with bytes := upd h.bytes w (some (slideWindow d wa)) } q qa) p pa)
    ds (slideState d)

set_option maxHeartbeats 1200000 in
/-- The actual copy, both unsigned position updates, checked signed block
subtraction, insertion clamp and complete slide_hash loops all execute.
The signed bound is derived from the real ledger and block balance.
Fresh previous-chain entries remain arbitrary before slide_hash reads them.
-/
theorem fill_slide_run {h : Heap} {r : ZStreamRef} {ds w p q b : Nat}
    {z : ZStream} {d : DeflateState} {wa buf : Array UInt8} {pa qa : Array UInt16}
    {xs : List Symbol} {credit : Int}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (balance : BlockBalance d xs credit)
    (lo : 0 ≤ credit) (hi : credit ≤ 1) (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ qa' pa', fillSlide (some (.tab ds)) d d.w_size (fillMore d) h =
      .ok ((), slideHeap h ds w p q d wa pa' qa') ∧
      qa'.size = qa.size ∧ pa'.size = pa.size ∧
      (∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i) ∧
      (∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) := by
  have geometry := fill_slide_counts good env.win env.wbytes range taken
  let copied := slideWindow d wa
  let hc := { h with bytes := upd h.bytes w (some copied) }
  let hp := setD hc ds (slideBeforeHash d)
  have add : padd d.window d.w_size.toNat h = .ok (.ref (.blk w) d.w_size.toNat, h) := by
    rw [env.win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := d.w_size.toNat)
      (show Space.get h (BRef.blk w) = some wa from env.wbytes) (by omega)
  have copy : memcpyB d.window (.ref (.blk w) d.w_size.toNat) (d.w_size - fillMore d).toNat h =
      .ok ((), hc) := by
    rw [env.win]
    exact Ptr.memcpy_ok (od := 0) (os := d.w_size.toNat)
      (show Space.get h (BRef.blk w) = some wa from env.wbytes) env.wbytes env.wro
      (by omega) geometry.2.2.2.1 (Or.inr (Or.inl (by omega)))
  have signed := (block_start_slide_run good base ledger count balance lo hi range).1
  have getH : hp.words q = some qa := env.hwords
  have getP : hp.words p = some pa := env.pwords
  have bounds := slide_window_sizes good
  have hashPositive : 1 ≤ d.hash_size.toNat := by
    obtain ⟨bits, _, _, size, _, _⟩ := env.params.bits
    rw [size]
    exact Nat.two_pow_pos _
  obtain ⟨qa', pa', hash, sizeH, sizeP, viewH, viewP⟩ := slide_hash_ok (h := hp) (sr := ds)
    (d := slideBeforeHash d) (by simp [hp]) env.headp env.prevp getH getP env.hne
    env.hsize env.wsize hashPositive (by change 1 ≤ d.w_size.toNat; omega)
  refine ⟨qa', pa', ?_, sizeH, sizeP, viewH, viewP⟩
  have dsCopy : hc.dstates ds = some d := good.live.hs
  unfold fillSlide
  simp only [bind_app, add, copy, wrD_eq, rdD_eq, dsCopy, setD_dstates_same, setD_setD, signed, pure_app]
  simpa only [hp, hc, copied, slideBeforeHash, slideState, slideHeap, setD, setW, upd_upd] using hash

end Zlib.Deflate.Engine.Proofs
