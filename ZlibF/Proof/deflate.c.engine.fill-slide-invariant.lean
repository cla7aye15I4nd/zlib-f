import ZlibF.Proof.«deflate.c.engine.fill-slide-run»
import ZlibF.Proof.«deflate.c.engine.fill-history»

/-! # The engine boundary on the exact sliding result -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem slide_good {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (sizeP : pa'.size = pa.size) (sizeH : qa'.size = qa.size) :
    DGood (slideHeap h ds w p q d wa pa' qa') r ds z (slideState d) := by
  let hc := { h with bytes := upd h.bytes w (some (slideWindow d wa)) }
  have goodC : DGood hc r ds z d := good.bytes_set w (slideWindow d wa) wa env.wbytes
    (size_copyRange _ _ _ _ _)
  have goodH := goodC.words_set q qa' qa env.hwords sizeH
  have getP : (setW hc q qa').words p = some pa := by
    simp only [setW, upd_ne _ _ _ _ env.hne.symm]
    exact env.pwords
  have goodP := goodH.words_set p pa' pa getP sizeP
  have inv : DStInv (setW (setW hc q qa') p pa') ds (slideState d) :=
    { goodP.inv with blocks := goodP.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact goodP.setD' rfl goodP.live.status inv (by trkeep)

theorem slide_window_view {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∀ i, i + d.w_size.toNat < fillEnd d →
      bfn (slideWindow d wa) i = bfn wa (i + d.w_size.toNat) := by
  have counts := fill_slide_counts good win get range taken
  have extent := window_extent good win get
  intro i bound
  have inside := copy_range_inside wa wa 0 d.w_size.toNat (d.w_size - fillMore d).toNat i
    (by omega) (by omega) (by omega)
  simpa only [slideWindow, Nat.sub_zero, Nat.add_comm] using inside

theorem slide_heap_chains {h : Heap} {r : ZStreamRef} {ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (fillEnd d))
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (head : ∀ i, wfn qa' i = if i < d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i)
    (prev : ∀ i, wfn pa' i = if i < d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) :
    HeapChains (slideHeap h ds w p q d wa pa' qa') (slideState d) (top - d.w_size.toNat) := by
  have counts := fill_slide_counts good env.win env.wbytes range taken
  have sizes := slide_window_sizes good
  have slid := chains_slide (h2 := wfn qa') (p2 := wfn pa') (w' := bfn (slideWindow d wa))
    chains good.inv.wsize (by omega)
    (fun i bound => by rw [head i, if_pos bound])
    (fun i bound => by rw [prev i, if_pos bound])
    (slide_window_view good env.win env.wbytes range taken)
  refine ⟨w, p, q, slideWindow d wa, pa', qa', env.win, env.prevp, env.headp,
    ?_, ?_, ?_, ?_⟩
  · simp [slideHeap]
  · simp [slideHeap, setW]
  · simp [slideHeap, setW, upd_ne _ _ _ _ env.hne]
  · change HashChains (wfn qa') (wfn pa') (bfn (slideWindow d wa)) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat (top - d.w_size.toNat) (fillEnd (slideState d))
    rw [counts.2.2.2.2.2.1]
    exact slid

theorem slide_pending_frame {h : Heap} {r : ZStreamRef} {ds w p q b : Nat}
    {z : ZStream} {d : DeflateState} {wa buf : Array UInt8} {pa' qa' : Array UInt16}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0)
    (pending : d.pending_buf = .ref (.blk b) 0) (get : h.bytes b = some buf) :
    (slideHeap h ds w p q d wa pa' qa').bytes b = some buf := by
  obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
  have windowId : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pendingId : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  simpa [slideHeap, upd_ne _ _ _ _ blocks.wb.symm] using get

theorem slide_ledger {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) : SymbolLedger buf (slideState d) xs :=
  ledger.keep rfl rfl rfl rfl

theorem slide_balance {h : Heap} {r : ZStreamRef} {ds w b : Nat}
    {z : ZStream} {d : DeflateState} {wa buf : Array UInt8} {xs : List Symbol} {credit : Int}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (balance : BlockBalance d xs credit)
    (lo : 0 ≤ credit) (hi : credit ≤ 1) (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    BlockBalance (slideState d) xs credit := by
  have counts := fill_slide_counts good win get range taken
  apply balance_slide balance (by omega) rfl
  exact (block_start_slide_run good base ledger count balance lo hi range).2

theorem slide_lazy_history {h : Heap} {r : ZStreamRef} {ds w origin : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {input : Nat → UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (history : LazyHistory input origin d) :
    LazyHistory input (origin + d.w_size.toNat) (slideState d) := by
  have counts := fill_slide_counts good win get range taken
  exact logical_history_slide history counts.1

end Zlib.Deflate.Engine.Proofs
