import ZlibF.Proof.«deflate.c.engine.fill-pending-boundary»

/-! # Sliding retains the deferred-insertion frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem slide_insert_count (d : DeflateState) :
    (slideState d).insert.toNat = min d.insert.toNat (slideState d).strstart.toNat := by
  by_cases small : d.insert > d.strstart - d.w_size
  · simp only [slideState, slideBeforeHash, small, if_true]
    exact (Nat.min_eq_right (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp small))).symm
  · simp only [slideState, slideBeforeHash, small, if_false]
    exact (Nat.min_eq_left (by
      have bound : ¬ (d.strstart - d.w_size).toNat < d.insert.toNat := by
        simpa only [GT.gt, UInt32.lt_iff_toNat_lt] using small
      omega)).symm

/-- The actual slide maps the lower frontier through unsigned clamping.
The pending count is retained when it still fits and otherwise clamped
exactly as in the source. No insert=0 assumption is used. -/
theorem slide_pending_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ w p q wa pa qa pa' qa',
      HashEnv h d w q p wa qa pa ∧ pa'.size = pa.size ∧ qa'.size = qa.size ∧
      fillSlide (some (.tab ds)) d d.w_size (fillMore d) h =
        .ok ((), slideHeap h ds w p q d wa pa' qa') ∧
      PendingBoundary (slideHeap h ds w p q d wa pa' qa') r ds z (slideState d)
        input (origin + d.w_size.toNat) xs := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.frontier
  obtain ⟨w0, wa0, win, get, view, form⟩ := boundary.data
  have windowId : w0 = w := by
    simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win.symm
  subst w0
  have arrayId : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  have credit := deferred_credit_bounds d
  have count := boundary.good.inv.sym.2.2.1
  obtain ⟨qa', pa', run, sizeH, sizeP, head, prev⟩ := fill_slide_run boundary.good env trees.base ledger
    count balance credit.1 credit.2 boundary.range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  have goodS : DGood hs r ds z slid := slide_good boundary.good env sizeP sizeH
  have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
  have insertCount : slid.insert.toNat = min d.insert.toNat slid.strstart.toNat := slide_insert_count d
  have frontierEq : slid.strstart.toNat - slid.insert.toNat =
      (d.strstart.toNat - d.insert.toNat) - d.w_size.toNat := by
    have start := geometry.2.2.2.2.1
    have pending := boundary.insert_le
    change slid.strstart.toNat = _ at start
    omega
  have frontierS : HeapChains hs slid (slid.strstart.toNat - slid.insert.toNat) := by
    rw [frontierEq]
    exact slide_heap_chains boundary.good env chains boundary.range taken head prev
  have rangeS : fillEnd slid ≤ slid.window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := boundary.good.inv.wsz
    omega
  have pendingS : slid.pending_buf = .ref (.blk b) 0 := trees.base.pbuf
  have dataS : hs.bytes b = some buf := slide_pending_frame boundary.good env.win trees.base.pbuf trees.base.bytes
  have balanceS : BlockBalance slid xs (deferredCredit slid) := slide_balance boundary.good env.win env.wbytes
    trees.base ledger count balance credit.1 credit.2 boundary.range taken
  have symbolS := symbol_boundary_of_ledger goodS pendingS dataS (slide_ledger ledger) balanceS
  refine ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, run, ⟨goodS, heap_chains_raise frontierS (Nat.sub_le _ _), rangeS,
    slide_lazy_history boundary.good env.win env.wbytes boundary.range taken boundary.history,
    ?_, symbolS, w, slideWindow d wa, env.win, by simp [hs, slideHeap], ?_, ?_⟩, ?_, frontierS, ?_⟩
  · intro _
    change 1 ≤ (slideState d).strstart.toNat
    omega
  · intro i bound
    have oldBound : i + d.w_size.toNat < fillEnd d := by
      change i < fillEnd (slideState d) at bound
      omega
    rw [slide_window_view boundary.good env.win env.wbytes boundary.range taken i oldBound, view _ oldBound]
    congr 1
    omega
  · intro large
    exact slide_form boundary.good env.win env.wbytes boundary.range taken large (form large)
  · change slid.insert.toNat ≤ slid.strstart.toNat
    omega
  · intro large
    have zero := boundary.ready large
    have small : ¬ d.insert > d.strstart - d.w_size := by
      simp [zero, UInt32.lt_iff_toNat_lt]
    simp [slid, slideState, slideBeforeHash, small, zero]

/-- Empty input exits before priming. Padding preserves the lower frontier
and the insertion counter on the exact returned heap. -/
theorem fill_window_empty_pending_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs) (empty : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z (paddedState d) input origin xs := by
  obtain ⟨after, run, core⟩ := fill_window_empty_slow_boundary boundary.toSlowBoundary empty noSlide
  obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
  have loop := do_once (fill_body_no_input boundary.good empty noSlide) (fill_cond_break (some (.tab ds)) h)
  have pad := fill_high_water_complete boundary.good win get (window_writable boundary.good win) boundary.range
  have actual : fill_window (some (.tab ds)) h = .ok ((), paddedHeap h ds w d wa) := by
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, boundary.good.live.hs, loop]
    exact pad
  have same : after = paddedHeap h ds w d wa := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
  refine ⟨after, run, core, boundary.insert_le, ?_, boundary.ready⟩
  rw [same]
  exact padded_chains boundary.good boundary.frontier win get boundary.range

set_option maxHeartbeats 3000000 in
/-- A complete call with new input handles the actual slide and pending
insertions. Input facts are obtained before the private slide writes. -/
theorem fill_window_slide_pending_boundary {h : Heap} {r : ZStreamRef} {ds origin io : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    {ref : BRef} (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (nonempty : z.avail_in ≠ 0) :
    ∃ used after z' result extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z' result extended (origin + d.w_size.toNat) xs ∧
      StreamAccounting z z' used 0 ∧
      result.strstart.toNat = d.strstart.toNat - d.w_size.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧
      result.insert.toNat = min (slideState d).insert.toNat (2 - result.lookahead.toNat) ∧ result.wrap = 1 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧
      result = { slideState d with
        lookahead := result.lookahead, ins_h := result.ins_h, insert := result.insert, high_water := result.high_water } := by
  obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
    slide_pending_boundary boundary taken
  have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
  have noSlide : ¬ (slideState d).strstart ≥ (slideState d).w_size + ((slideState d).w_size - MIN_LOOKAHEAD_u) :=
    geometry.2.2.2.2.2.2.2.2
  obtain ⟨ia, data, inputBound⟩ := caller_input_array boundary.good buffers pointer
  have separate := caller_input_window_separate boundary.good buffers env.win pointer
  have dataS : Space.get (slideHeap h ds w p q d wa pa' qa') ref = some ia := by
    rw [slide_input_frame boundary.good separate]
    exact data
  obtain ⟨used, after, z', result, extended, run, boundaryA, account, startA, lookA, insertA,
      wrapA, prefixA, stopped, fields⟩ :=
    fill_window_pending_boundary_read boundaryS short noSlide wrap pointer dataS inputBound nonempty
      (fun _ win => caller_input_window_separate boundary.good buffers win pointer)
  refine ⟨used, after, z', result, extended, ?_, boundaryA, account, ?_, lookA, insertA, wrapA,
    ?_, stopped, fields⟩
  · exact (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run
  · rw [startA]
    exact geometry.2.2.2.2.1
  · intro i before
    apply prefixA i
    rw [geometry.2.2.2.2.2.1]
    have start := geometry.1
    omega

/-- The empty-input full call composes sliding, the real loop exit and
padding while retaining pending positions. -/
theorem fill_window_slide_empty_pending_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs) (empty : z.avail_in = 0)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z (paddedState (slideState d)) input (origin + d.w_size.toNat) xs := by
  obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
    slide_pending_boundary boundary taken
  have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
  obtain ⟨after, run, boundaryA⟩ := fill_window_empty_pending_boundary boundaryS empty geometry.2.2.2.2.2.2.2.2
  exact ⟨after, (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run,
    boundaryA⟩

end Zlib.Deflate.Engine.Proofs
