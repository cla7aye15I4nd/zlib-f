import ZlibF.Proof.«deflate.c.engine.fill-slide-caller»

/-! # Sliding when the caller has no further input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem slide_form {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (large : 3 ≤ d.lookahead.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    InsHForm (slideState d).hash_shift (slideState d).hash_mask (bfn (slideWindow d wa))
      (slideState d).strstart.toNat (slideState d).ins_h := by
  have counts := fill_slide_counts good win get range taken
  have start := counts.2.2.2.2.1
  change InsHForm d.hash_shift d.hash_mask (bfn (slideWindow d wa)) (slideState d).strstart.toNat d.ins_h
  apply form_congr form
  · rw [slide_window_view good win get range taken _ (by dsimp only [fillEnd]; omega)]
    congr 1
    omega
  · rw [slide_window_view good win get range taken _ (by dsimp only [fillEnd]; omega)]
    congr 1
    omega

set_option maxHeartbeats 2500000 in
/-- A taken slide executes even with avail_in=0. The complete call
terminates after its real outer-loop condition and performs high-water
padding as required. No input pointer, wrapper choice, insert=0 or
already-padded-window premise is needed for this source path.
-/
theorem fill_window_slide_empty {h : Heap} {r : ZStreamRef} {ds w p q b top origin : Nat}
    {z : ZStream} {d : DeflateState} {wa buf : Array UInt8} {pa qa : Array UInt16}
    {input : Nat → UInt8} {xs : List Symbol} {credit : Int}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (fillEnd d))
    (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (balance : BlockBalance d xs credit) (lo : 0 ≤ credit) (hi : credit ≤ 1)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (empty : z.avail_in = 0)
    (history : LazyHistory input origin d)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i))
    (form : 3 ≤ d.lookahead.toNat → InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ after result output,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ HeapChains after result (top - d.w_size.toNat) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some output ∧
      result.strstart.toNat = d.strstart.toNat - d.w_size.toNat ∧ result.lookahead = d.lookahead ∧
      fillEnd result ≤ result.window_size.toNat ∧
      min (fillEnd result + 258) result.window_size.toNat ≤ result.high_water.toNat ∧
      (3 ≤ result.lookahead.toNat → InsHForm result.hash_shift result.hash_mask
        (bfn output) result.strstart.toNat result.ins_h) ∧
      LazyHistory input (origin + d.w_size.toNat) result ∧ DeferredByte result ∧
      (∀ i, i < fillEnd result → bfn output i = input (origin + d.w_size.toNat + i)) ∧
      after.bytes b = some buf ∧ SymbolLedger buf result xs ∧ BlockBalance result xs credit := by
  have count := good.inv.sym.2.2.1
  obtain ⟨qa', pa', prefixRun, sizeH, sizeP, head, prev⟩ :=
    fill_slide_run good env base ledger count balance lo hi range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  let moved := slideWindow d wa
  let result := paddedState slid
  let output := fillRange moved (paddingStart slid) (paddingCount slid) 0
  let after := paddedHeap hs ds w slid moved
  have goodS : DGood hs r ds z slid := slide_good good env sizeP sizeH
  have getS : hs.bytes w = some moved := by simp [hs, moved, slideHeap]
  have winS : slid.window = .ref (.blk w) 0 := env.win
  have chainsS : HeapChains hs slid (top - d.w_size.toNat) :=
    slide_heap_chains good env chains range taken head prev
  have geometry := fill_slide_counts good env.win env.wbytes range taken
  have rangeS : fillEnd slid ≤ slid.window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := good.inv.wsz
    omega
  have noSlide : ¬ slid.strstart ≥ slid.w_size + (slid.w_size - MIN_LOOKAHEAD_u) := geometry.2.2.2.2.2.2.2.2
  have loop := do_once (fill_body_no_input goodS empty noSlide) (fill_cond_break (some (.tab ds)) hs)
  have pad := fill_high_water_complete goodS winS getS (window_writable goodS winS) rangeS
  have run : fill_window (some (.tab ds)) hs = .ok ((), after) := by
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, goodS.live.hs, loop]
    exact pad
  have historyS : LazyHistory input (origin + d.w_size.toNat) slid :=
    slide_lazy_history good env.win env.wbytes range taken history
  have balanceS : BlockBalance slid xs credit :=
    slide_balance good env.win env.wbytes base ledger count balance lo hi range taken
  have pendingS : hs.bytes b = some buf := slide_pending_frame good env.win base.pbuf base.bytes
  have distinct := window_pending_separate good env.win base.pbuf
  refine ⟨after, result, output, ?_, padded_good goodS winS getS rangeS,
    padded_chains goodS chainsS winS getS rangeS, winS, ?_, geometry.2.2.2.2.1, rfl,
    rangeS, padded_initialized goodS winS getS rangeS, ?_, historyS, ?_, ?_, ?_, ?_, balanceS⟩
  · exact (fill_window_slide_transfer good env sizeP sizeH range taken prefixRun).trans run
  · simp [after, output, paddedHeap]
  · intro large
    exact padded_form goodS winS getS rangeS large
      (slide_form good env.win env.wbytes range taken large (form large))
  · intro _
    change 1 ≤ (slideState d).strstart.toNat
    omega
  · intro i bound
    have before : i < fillEnd slid := bound
    have oldBound : i + d.w_size.toNat < fillEnd d := by
      change i < fillEnd (slideState d) at before
      omega
    rw [padded_prefix goodS winS getS rangeS i before,
      slide_window_view good env.win env.wbytes range taken i oldBound, view _ oldBound]
    congr 1
    omega
  · simpa only [after, paddedHeap, setD_bytes, upd_ne _ _ _ _ distinct.symm] using pendingS
  · exact (slide_ledger ledger).keep rfl rfl rfl rfl

end Zlib.Deflate.Engine.Proofs
