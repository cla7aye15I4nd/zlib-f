import ZlibF.Proof.«deflate.c.engine.slow-boundary»
import ZlibF.Proof.«deflate.c.engine.fill-slide-empty»

/-! # Input refill preserves the same initialized slow boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

set_option maxHeartbeats 3000000 in
/-- The actual non-sliding read and padding preserve SlowBoundary.
The readable input and disjoint private window are facts about this
caller state. No read_buf or fill_window execution is assumed.
-/
theorem fill_window_resume_slow_read {h : Heap} {r : ZStreamRef} {ds origin io : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    {ref : BRef} {ia : Array UInt8}
    (boundary : SlowBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1) (pointer : z.next_in = .ref ref io)
    (data : Space.get h ref = some ia) (inputBound : io + z.avail_in.toNat ≤ ia.size)
    (nonempty : z.avail_in ≠ 0)
    (separate : ∀ w, d.window = .ref (.blk w) 0 → BRef.blk w ≠ ref) :
    ∃ used after z' result extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      SlowBoundary after r ds z' result extended origin xs ∧ StreamAccounting z z' used 0 ∧
      result.strstart = d.strstart ∧ result.lookahead.toNat = d.lookahead.toNat + used ∧
      result.insert = 0 ∧ result.wrap = 1 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧
      result = { d with
        lookahead := result.lookahead, ins_h := result.ins_h, high_water := result.high_water } := by
  obtain ⟨w, wa, win, get, view, _⟩ := boundary.data
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let read := resumeReadState d n copied
  let result := resumedFillState d n copied
  let output := fillRange copied (paddingStart read) (paddingCount read) 0
  let after := resumedFillHeap h r ds w z d ref io ia wa
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let extended := extendInput input (origin + fillEnd d) ia io
  obtain ⟨run, goodA, chainsA, winA, bytesA, rangeA, _, formA⟩ :=
    fill_window_resume_complete boundary.good boundary.chains win get boundary.range short noSlide insert wrap
      pointer data inputBound nonempty (Or.inl (separate w win))
  obtain ⟨historyA, deferredA, viewA⟩ := resumed_fill_history (ref := ref)
    boundary.good win get boundary.range inputBound boundary.history boundary.deferred view
  have counts := resume_read_counts boundary.good win get boundary.range
  have inputCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  obtain ⟨key, high, fields⟩ := resumed_fill_record d n copied
  change result = _ at fields
  have startA : result.strstart = d.strstart := by rw [fields]
  have lookA : result.lookahead.toNat = d.lookahead.toNat + n.toNat := by rw [fields]; exact counts.2.1
  have distinct := window_pending_separate boundary.good win trees.base.pbuf
  have pendingA : result.pending_buf = .ref (.blk b) 0 := by rw [fields]; exact trees.base.pbuf
  have dataA : after.bytes b = some buf := by
    simpa only [after, resumedFillHeap, paddedHeap, resumeReadHeap, setD_bytes, ZStreamRef.put_bytes,
      upd_ne _ _ _ _ distinct.symm] using trees.base.bytes
  have ledgerA : SymbolLedger buf result xs := by rw [fields]; exact ledger.keep rfl rfl rfl rfl
  have balanceA : BlockBalance result xs (deferredCredit result) := by rw [fields]; exact balance
  have symbolA := symbol_boundary_of_ledger goodA pendingA dataA ledgerA balanceA
  refine ⟨n.toNat, after, z', result, extended, run, ?_,
    read_stream_accounting z n ref io _ pointer (by omega), startA, lookA, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨goodA, ?_, rangeA, historyA, deferredA, symbolA,
      w, output, winA, bytesA, viewA, formA⟩
    rw [startA]
    exact chainsA
  · rw [fields]
    exact insert
  · rw [fields]
    exact wrap
  · intro i before
    simp only [extended, extendInput, before, if_true]
  · by_cases enough : 262 ≤ result.lookahead.toNat
    · exact Or.inl enough
    · right
      have room := fill_room_no_slide boundary.good win get boundary.range short noSlide
      have all : n = z.avail_in := UInt32.toNat_inj.mp (by omega)
      simp only [z', readStream, all, UInt32.sub_self]
  · rw [fields]

/-- Public buffers discharge the input facts for a real resumed call. -/
theorem fill_window_resume_slow_boundary {h : Heap} {r : ZStreamRef} {ds origin io : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    {ref : BRef} (boundary : SlowBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (nonempty : z.avail_in ≠ 0) :
    ∃ used after z' result extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      SlowBoundary after r ds z' result extended origin xs ∧ StreamAccounting z z' used 0 ∧
      result.strstart = d.strstart ∧ result.lookahead.toNat = d.lookahead.toNat + used ∧
      result.insert = 0 ∧ result.wrap = 1 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧
      result = { d with
        lookahead := result.lookahead, ins_h := result.ins_h, high_water := result.high_water } := by
  obtain ⟨ia, data, bound⟩ := caller_input_array boundary.good buffers pointer
  exact fill_window_resume_slow_read boundary short noSlide insert wrap pointer data bound nonempty
    (fun _ win => caller_input_window_separate boundary.good buffers win pointer)

/-- An empty-input call preserves the boundary while doing any required
padding. Neither insert=0 nor an already padded window is assumed. -/
theorem fill_window_empty_slow_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : SlowBoundary h r ds z d input origin xs) (empty : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      SlowBoundary after r ds z (paddedState d) input origin xs := by
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  let output := fillRange wa (paddingStart d) (paddingCount d) 0
  let after := paddedHeap h ds w d wa
  have goodA := padded_good boundary.good win get boundary.range
  have chainsA := padded_chains boundary.good boundary.chains win get boundary.range
  have loop := do_once (fill_body_no_input boundary.good empty noSlide) (fill_cond_break (some (.tab ds)) h)
  have pad := fill_high_water_complete boundary.good win get (window_writable boundary.good win) boundary.range
  have run : fill_window (some (.tab ds)) h = .ok ((), after) := by
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, boundary.good.live.hs, loop]
    exact pad
  have distinct := window_pending_separate boundary.good win trees.base.pbuf
  have pendingA : (paddedState d).pending_buf = .ref (.blk b) 0 := trees.base.pbuf
  have dataA : after.bytes b = some buf := by
    simpa only [after, paddedHeap, setD_bytes, upd_ne _ _ _ _ distinct.symm] using trees.base.bytes
  have ledgerA : SymbolLedger buf (paddedState d) xs := ledger.keep rfl rfl rfl rfl
  have balanceA : BlockBalance (paddedState d) xs (deferredCredit (paddedState d)) := balance
  have symbolA := symbol_boundary_of_ledger goodA pendingA dataA ledgerA balanceA
  refine ⟨after, run, goodA, chainsA, boundary.range, boundary.history, boundary.deferred, symbolA,
    w, output, win, ?_, ?_, ?_⟩
  · simp [after, output, paddedHeap]
  · intro i bound
    rw [padded_prefix boundary.good win get boundary.range i bound]
    exact view i bound
  · intro large
    exact padded_form boundary.good win get boundary.range large (form large)

/-- The real sliding prefix preserves the same slow boundary and changes
the logical window origin by exactly one window. -/
theorem slide_slow_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : SlowBoundary h r ds z d input origin xs)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ w p q wa pa qa pa' qa',
      HashEnv h d w q p wa qa pa ∧ pa'.size = pa.size ∧ qa'.size = qa.size ∧
      fillSlide (some (.tab ds)) d d.w_size (fillMore d) h =
        .ok ((), slideHeap h ds w p q d wa pa' qa') ∧
      SlowBoundary (slideHeap h ds w p q d wa pa' qa') r ds z (slideState d)
        input (origin + d.w_size.toNat) xs := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
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
  have chainsS : HeapChains hs slid slid.strstart.toNat := by
    rw [geometry.2.2.2.2.1]
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
  refine ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, run, goodS, chainsS, rangeS,
    slide_lazy_history boundary.good env.win env.wbytes boundary.range taken boundary.history,
    ?_, symbolS, w, slideWindow d wa, env.win, by simp [hs, slideHeap], ?_, ?_⟩
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

set_option maxHeartbeats 3000000 in
/-- A taken-slide call with new input preserves the initialized boundary.
Caller-buffer facts are derived before sliding and transported by the
actual private-memory frame. No buffers predicate on a hypothetical
intermediate heap is supplied by the caller.
-/
theorem fill_window_slide_slow_boundary {h : Heap} {r : ZStreamRef} {ds origin io : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    {ref : BRef} (boundary : SlowBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (nonempty : z.avail_in ≠ 0) :
    ∃ used after z' result extended,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      SlowBoundary after r ds z' result extended (origin + d.w_size.toNat) xs ∧
      StreamAccounting z z' used 0 ∧
      result.strstart.toNat = d.strstart.toNat - d.w_size.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧ result.insert = 0 ∧ result.wrap = 1 ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧
      result = { slideState d with
        lookahead := result.lookahead, ins_h := result.ins_h, high_water := result.high_water } := by
  obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
    slide_slow_boundary boundary taken
  have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
  have noSlide : ¬ (slideState d).strstart ≥ (slideState d).w_size + ((slideState d).w_size - MIN_LOOKAHEAD_u) :=
    geometry.2.2.2.2.2.2.2.2
  have insertS : (slideState d).insert = 0 := by
    simp [slideState, slideBeforeHash, insert, UInt32.lt_iff_toNat_lt]
  obtain ⟨ia, data, inputBound⟩ := caller_input_array boundary.good buffers pointer
  have separate := caller_input_window_separate boundary.good buffers env.win pointer
  have dataS : Space.get (slideHeap h ds w p q d wa pa' qa') ref = some ia := by
    rw [slide_input_frame boundary.good separate]
    exact data
  obtain ⟨used, after, z', result, extended, run, boundaryA, account, startA, lookA, insertA,
      wrapA, prefixA, stopped, fields⟩ :=
    fill_window_resume_slow_read boundaryS short noSlide insertS wrap pointer dataS inputBound nonempty
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

/-- With no further input the same boundary survives the real slide,
outer-loop exit and padding. Wrapper and insertion count are unrestricted. -/
theorem fill_window_slide_empty_slow_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : SlowBoundary h r ds z d input origin xs) (empty : z.avail_in = 0)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      SlowBoundary after r ds z (paddedState (slideState d)) input (origin + d.w_size.toNat) xs := by
  obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, boundaryS⟩ :=
    slide_slow_boundary boundary taken
  have geometry := fill_slide_counts boundary.good env.win env.wbytes boundary.range taken
  obtain ⟨after, run, boundaryA⟩ := fill_window_empty_slow_boundary boundaryS empty geometry.2.2.2.2.2.2.2.2
  exact ⟨after, (fill_window_slide_transfer boundary.good env sizeP sizeH boundary.range taken prefixRun).trans run,
    boundaryA⟩

end Zlib.Deflate.Engine.Proofs
