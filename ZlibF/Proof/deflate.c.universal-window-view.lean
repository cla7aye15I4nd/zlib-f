import ZlibF.Proof.«deflate.c.engine.view-chains»
import ZlibF.Proof.«deflate.c.universal-ops-dictionary»

/-!
# deflate.c: `fill_window` with the chains read through a table view

`fill_window_input` (`deflate.c.universal-ops-dictionary`) with the chain fact of the tables read
through a view `v` (`deflate.c.engine.view-chains`): exact, slid once, or no fact. The frontier is
the insertion frontier `strstart - insert`. `deflateSetDictionary` runs `fill_window` on a level-0
stream with one or two pending slides, where the invariant gives the slid view or nothing; these
statements carry that view through. The proofs are those of `deflate.c.universal-window` with the
laws of the view.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
open Zlib.Deflate.Universal (InputRange input_window_separate input_array)
set_option autoImplicit false

variable {v : TabView} {roll : Prop}

/-- `FillPre` with the chains through the view `v` at the insertion frontier. -/
structure FillPreV (v : TabView) (roll : Prop) (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream)
    (d : DeflateState) : Prop where
  good : DGood h r ds z d
  chains : VHeapChains v h d (d.strstart.toNat - d.insert.toNat)
  pending : d.insert.toNat ≤ d.strstart.toNat
  range : fillEnd d ≤ d.window_size.toNat
  form : 3 ≤ d.lookahead.toNat → d.insert = 0 ∧ (roll → ∃ w wa, d.window = .ref (.blk w) 0 ∧
    h.bytes w = some wa ∧ InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)
  globals : d.wrap = 2 → CrcGlobals h

/-- `FillPost` with the chains through the view `v` at the insertion frontier. -/
structure FillPostV (v : TabView) (roll : Prop) (h after : Heap) (r : ZStreamRef) (ds : Nat) (z z' : ZStream)
    (d result : DeflateState) : Prop where
  good : DGood after r ds z' result
  chains : VHeapChains v after result (result.strstart.toNat - result.insert.toNat)
  pending : result.insert.toNat ≤ result.strstart.toNat
  range : fillEnd result ≤ result.window_size.toNat
  water : fillEnd result ≤ result.high_water.toNat
  form : 3 ≤ result.lookahead.toNat → result.insert = 0 ∧ (roll → ∃ w wa, result.window = .ref (.blk w) 0 ∧
    after.bytes w = some wa ∧ InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h)
  stopped : 262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0
  noSlide : ¬ result.strstart ≥ result.w_size + (result.w_size - MIN_LOOKAHEAD_u)
  fields : ∃ base, (base = d ∨ (d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) ∧ base = slideState d)) ∧
    result = fillResult base result
  consumed : z'.avail_in.toNat + result.lookahead.toNat = z.avail_in.toNat + d.lookahead.toNat
  stream : z' = z ∨ ∃ n ref io ia, z.next_in = .ref ref io ∧ Space.get h ref = some ia ∧
    io + n.toNat ≤ ia.size ∧ n.toNat ≤ z.avail_in.toNat ∧
    z' = readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
  byteFrame : ByteFrame h after (DeflateOwned ds d)
  outside : ∀ w b, d.window = .ref (.blk w) 0 → b ≠ w → after.bytes b = h.bytes b
  shape : Shape h after
  frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
  live : LiveChange h after (fun _ => False) (fun _ => False)
  nalloc : after.nalloc = h.nalloc
  nextBlk : after.nextBlk = h.nextBlk
  insertLe : result.insert.toNat ≤ d.insert.toNat

set_option maxHeartbeats 3000000 in
/-- The non-sliding refill with new input, through the view. -/
theorem fill_window_pending_complete_full_storage_v {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : VHeapChains v h d (d.strstart.toNat - d.insert.toNat))
    (pending : d.insert.toNat ≤ d.strstart.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (globals : d.wrap = 2 → CrcGlobals h)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let z' := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
    ∃ after result output,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧ DGood after r ds z' result ∧
      VHeapChains v after result (result.strstart.toNat - result.insert.toNat) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some output ∧
      fillEnd result ≤ result.window_size.toNat ∧
      min (fillEnd result + 258) result.window_size.toNat ≤ result.high_water.toNat ∧
      (3 ≤ result.lookahead.toNat → result.insert = 0 ∧
        InsHForm result.hash_shift result.hash_mask (bfn output) result.strstart.toNat result.ins_h) ∧
      result = { d with
        lookahead := d.lookahead + n, ins_h := result.ins_h, insert := result.insert, high_water := result.high_water } ∧
      result.insert.toNat = min d.insert.toNat (2 - result.lookahead.toNat) ∧
      (∀ b, b ≠ w → after.bytes b = h.bytes b) ∧
      (∀ i, i < fillEnd result → bfn output i = bfn copied i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ ByteFrame h after (DeflateOwned ds d) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat))
  let hr := pendingReadHeapAny h r ds w z d ref io ia wa
  let dr := pendingReadState d n
  have goodR : DGood hr r ds z' dr := pending_read_good_any good get
  have chainsR : VHeapChains v hr dr (dr.strstart.toNat - dr.insert.toNat) :=
    pending_read_vchains_any good chains win get range
  have counts := resume_read_counts good win get range
  have rangeR : fillEnd dr ≤ dr.window_size.toNat := counts.2.2
  have getR : hr.bytes w = some copied := by simp [hr, pendingReadHeapAny, n, copied]
  have winR : dr.window = .ref (.blk w) 0 := win
  obtain ⟨hp, dp, primeRun, goodP, chainsP, bytesP, frameP, countP, formP, storageP, shapeP, fullP, allocP, nextP⟩ :=
    fill_prime_pending_full_storage_v goodR chainsR winR getR rangeR pending
  change fillPrime (some (.tab ds)) (pendingReadHeapAny h r ds w z d ref io ia wa) = .ok ((), hp) at primeRun
  have fields : dp = { d with lookahead := d.lookahead + n, ins_h := dp.ins_h, insert := dp.insert } := by
    unfold PendingInsertFrame at frameP
    rw [frameP]
    rfl
  have rangeP : fillEnd dp ≤ dp.window_size.toNat := by rw [fields]; exact counts.2.2
  have winP : dp.window = .ref (.blk w) 0 := by rw [fields]; exact win
  have getP : hp.bytes w = some copied := by rw [bytesP]; exact getR
  have capacity := fill_room_no_slide good win get range short noSlide
  have inputCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have exhausted : dp.lookahead < MIN_LOOKAHEAD_u → z'.avail_in = 0 := by
    intro small
    have less : dp.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    have all : n = z.avail_in := UInt32.toNat_inj.mp (by
      have lookP : dp.lookahead.toNat = d.lookahead.toNat + n.toNat := by rw [fields]; exact counts.2.1
      omega)
    simp only [z', readStream, all, UInt32.sub_self]
  have condition : fillCond (some (.tab ds)) false hp = .ok ((false, false), hp) := by
    unfold fillCond
    simp only [bind_app, ldDeflateState_tab goodP.live.hs, Bool.false_eq_true, ite_false, goodP.live.back]
    by_cases small : dp.lookahead < MIN_LOOKAHEAD_u
    · simp only [small, ite_true, bind_app, zrd_eq, goodP.live.hz, exhausted small]
      rfl
    · simp only [small, ite_false]
      rfl
  have body : fillBody (some (.tab ds)) d.w_size false h = .ok (false, hp) := by
    rw [fill_body_slide_source]
    simp only [bind_app, ldDeflateState_tab good.live.hs, noSlide, ite_false]
    rw [fill_after_slide_read_prefix_any good win get range short noSlide globals pointer input inputBound nonempty separate]
    simp only [bind_app, primeRun, pure_app]
  have loop := do_once body condition
  have pad := fill_high_water_complete goodP winP getP (window_writable goodP winP) rangeP
  let after := paddedHeap hp ds w dp copied
  let result := paddedState dp
  let output := fillRange copied (paddingStart dp) (paddingCount dp) 0
  have run : fill_window (some (.tab ds)) h = .ok ((), after) := by
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, good.live.hs, loop]
    exact pad
  have readFrame : ByteFrame h hr (DeflateOwned ds d) :=
    pending_read_storage_frame_any h r ds w z d ref io ia wa _ (Or.inl rfl) (Or.inr (Or.inl win))
  have primeFrame : ByteFrame hr hp (DeflateOwned ds d) :=
    storageP.weaken (fun i equal => Or.inl equal)
  have wholeFrame : ByteFrame h after (DeflateOwned ds d) :=
    (readFrame.trans primeFrame).trans
      (padded_storage_frame hp ds w dp copied _ (Or.inl rfl) (Or.inr (Or.inl win)))
  obtain ⟨shapeR, fullR, _liveR, allocR, nextR⟩ := pending_read_heap_full_storage_any good win get
  obtain ⟨shapePad, fullPad, _livePad, allocPad, nextPad⟩ := padded_heap_full_storage goodP winP getP
  have ownedP : DeflateOwned ds dp = DeflateOwned ds d := by rw [fields]; rfl
  have fullPad' : Frame hp after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    rw [← ownedP]
    exact fullPad
  have shape := (shapeR.trans shapeP).trans shapePad
  have full := full_frame_trans_shape (full_frame_trans_shape fullR fullP shapeR) fullPad' (shapeR.trans shapeP)
  refine ⟨after, result, output, run, padded_good goodP winP getP rangeP,
    padded_vchains goodP chainsP winP getP rangeP, winP, ?_, rangeP,
    padded_initialized goodP winP getP rangeP, ?_, ?_, ?_, ?_, ?_, ?_, wholeFrame, shape, full, full_shape_live_change shape,
    allocPad.trans (allocP.trans allocR), nextPad.trans (nextP.trans nextR)⟩
  · simp [after, output, paddedHeap]
  · intro large
    obtain ⟨zero, form⟩ := formP large
    exact ⟨zero, padded_form goodP winP getP rangeP large form⟩
  · dsimp only [result, paddedState]
    rw [fields]
  · change dp.insert.toNat = min d.insert.toNat (2 - dp.lookahead.toNat)
    have look : dp.lookahead = dr.lookahead := congrArg (·.lookahead) frameP
    rw [look]
    exact countP
  · intro b different
    change (paddedHeap hp ds w dp copied).bytes b = _
    simp only [paddedHeap, setD_bytes, bytesP,
      hr, pendingReadHeapAny, setD_bytes, ZStreamRef.put_bytes, upd_ne _ _ _ _ different]
  · exact padded_prefix goodP winP getP rangeP
  · by_cases enough : 262 ≤ dp.lookahead.toNat
    · exact Or.inl enough
    · right
      exact exhausted (UInt32.lt_iff_toNat_lt.mpr (by change dp.lookahead.toNat < 262; omega))

/-- The slide prefix from `FillPreV`. -/
theorem fill_slide_pre_v {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPreV v roll h r ds z d) (blockLow : -(2 : Int) ^ 62 ≤ d.block_start.toInt)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ w p q wa pa qa pa' qa', HashEnv h d w q p wa qa pa ∧ pa'.size = pa.size ∧ qa'.size = qa.size ∧
      fillSlide (some (.tab ds)) d d.w_size (fillMore d) h = .ok ((), slideHeap h ds w p q d wa pa' qa') ∧
      FillPreV v roll (slideHeap h ds w p q d wa pa' qa') r ds z (slideState d) := by
  obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := vheap_environment pre.good pre.chains
  obtain ⟨qa', pa', run, sizeH, sizeP, head, prev⟩ := fill_slide_run_any pre.good env
    (block_start_slide_signed pre.good blockLow) pre.range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  have goodS : DGood hs r ds z slid := slide_good pre.good env sizeP sizeH
  have geometry := fill_slide_counts pre.good env.win env.wbytes pre.range taken
  have insertCount : slid.insert.toNat = min d.insert.toNat slid.strstart.toNat := slide_insert_count d
  have frontierLe : d.strstart.toNat - d.insert.toNat - d.w_size.toNat ≤ slid.strstart.toNat - slid.insert.toNat := by
    have start := geometry.2.2.2.2.1
    change slid.strstart.toNat = _ at start
    omega
  have frontierS : VHeapChains v hs slid (slid.strstart.toNat - slid.insert.toNat) :=
    vheap_up (slide_heap_vchains pre.good env chains pre.range taken head prev) frontierLe
  have rangeS : fillEnd slid ≤ slid.window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := pre.good.inv.wsz
    omega
  refine ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, run, ⟨goodS, frontierS, ?_, rangeS, ?_, ?_⟩⟩
  · change slid.insert.toNat ≤ slid.strstart.toNat
    omega
  · intro large
    have large' : 3 ≤ d.lookahead.toNat := large
    obtain ⟨zero, rolled⟩ := pre.form large'
    refine ⟨?_, fun yes => ?_⟩
    · have small : ¬ d.insert > d.strstart - d.w_size := by
        simp [zero, UInt32.lt_iff_toNat_lt]
      simp [slid, slideState, slideBeforeHash, small, zero]
    · obtain ⟨w0, wa0, win0, get0, form⟩ := rolled yes
      have wid : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
      subst w0
      have aid : wa0 = wa := Option.some.inj (get0.symm.trans env.wbytes)
      subst wa0
      exact ⟨w, slideWindow d wa, env.win, by simp [slideHeap],
        slide_form pre.good env.win env.wbytes pre.range taken large' form⟩
  · intro two
    obtain ⟨t1, t2⟩ := pre.globals two
    exact ⟨by simpa [hs, slideHeap, setD, setW] using t1, by simpa [hs, slideHeap, setD, setW] using t2⟩

theorem fill_window_window_v {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPreV v roll h r ds z d) : ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa := by
  obtain ⟨w, p, q, wa, pa, qa, env, _⟩ := vheap_environment pre.good pre.chains
  exact ⟨w, wa, env.win, env.wbytes⟩

/-- Empty caller input and no slide: only the high-water padding. -/
theorem fill_window_empty_post_v {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPreV v roll h r ds z d) (empty : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after result, fill_window (some (.tab ds)) h = .ok ((), after) ∧ FillPostV v roll h after r ds z z d result := by
  obtain ⟨w, wa, win, get⟩ := fill_window_window_v pre
  obtain ⟨run, byteFrame⟩ := fill_window_empty_storage pre.good win get pre.range empty noSlide
  obtain ⟨shape, frame, live, alloc, next⟩ := padded_heap_full_storage pre.good win get
  refine ⟨_, paddedState d, run, ⟨padded_good pre.good win get pre.range,
    padded_vchains pre.good pre.chains win get pre.range, pre.pending, pre.range,
    padded_water pre.good win get pre.range, ?_, Or.inr empty, noSlide,
    ⟨d, Or.inl rfl, rfl⟩, rfl, Or.inl rfl, byteFrame, ?_, shape, frame, live, alloc, next, Nat.le_refl _⟩⟩
  · intro large
    obtain ⟨zero, rolled⟩ := pre.form large
    refine ⟨zero, fun yes => ?_⟩
    obtain ⟨w0, wa0, win0, get0, form⟩ := rolled yes
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans get)
    subst wa0
    exact ⟨w, _, win, by simp [paddedHeap], padded_form pre.good win get pre.range large form⟩
  · intro w0 b win0 other
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    simp [paddedHeap, upd_ne _ _ _ _ other]

set_option maxHeartbeats 1600000 in
/-- New caller input and no slide: the read, the pending insertions and the padding. -/
theorem fill_window_read_post_v {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {ref : BRef} {io : Nat} {ia : Array UInt8}
    (pre : FillPreV v roll h r ds z d) (short : d.lookahead.toNat < 262)
    (nonempty : z.avail_in ≠ 0) (pointer : z.next_in = .ref ref io) (data : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size)
    (separated : ∀ w, d.window = .ref (.blk w) 0 → BRef.blk w ≠ ref)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after z' result, fill_window (some (.tab ds)) h = .ok ((), after) ∧ FillPostV v roll h after r ds z z' d result := by
  obtain ⟨w, wa, win, get⟩ := fill_window_window_v pre
  have separate := separated w win
  obtain ⟨after, result, output, run, goodA, chainsA, winA, getA, rangeA, initA, formA, fields,
      countA, outside, _prefix, stopped, byteFrame, shape, frame, live, alloc, next⟩ :=
    fill_window_pending_complete_full_storage_v pre.good pre.chains pre.pending win get pre.range short noSlide
      pre.globals pointer data inputBound nonempty separate
  have counts := resume_read_counts pre.good win get pre.range
  have nCount : (rbLen z.avail_in (fillMore d)).toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have look : result.lookahead.toNat = d.lookahead.toNat + (rbLen z.avail_in (fillMore d)).toNat := by
    rw [fields]; exact counts.2.1
  have startEq : result.strstart = d.strstart := by rw [fields]
  have sizesEq : result.w_size = d.w_size := by rw [fields]
  have waterA : fillEnd result ≤ result.high_water.toNat := by omega
  refine ⟨after, _, result, run, ⟨goodA, chainsA, ?_, rangeA, waterA, ?_, stopped, ?_, ⟨d, Or.inl rfl,
    fill_result_of_eq fields⟩, ?_, Or.inr ⟨_, ref, io, ia, pointer, data, by omega, by omega, rfl⟩,
    byteFrame, ?_, shape, frame, live, alloc, next, by omega⟩⟩
  · rw [startEq]
    have := pre.pending
    omega
  · intro large
    obtain ⟨zero, form⟩ := formA large
    exact ⟨zero, fun _ => ⟨w, output, winA, getA, form⟩⟩
  · rw [startEq, sizesEq]; exact noSlide
  · change (z.avail_in - rbLen z.avail_in (fillMore d)).toNat + result.lookahead.toNat = _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), look]
    omega
  · intro w0 b win0 other
    have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    exact outside b other

/-- A slide followed by a call that does not slide composes, from the input range. -/
theorem fill_post_after_slide_input_v {h hs after : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z z' : ZStream} {d result : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (pre : FillPreV v roll h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (heap : hs = slideHeap h ds w p q d wa pa' qa') (input : InputRange h r)
    (post : FillPostV v roll hs after r ds z z' (slideState d) result) : FillPostV v roll h after r ds z z' d result := by
  subst hs
  have geometry := fill_slide_counts pre.good env.win env.wbytes pre.range taken
  obtain ⟨shapeS, frameS, _liveS, allocS, nextS⟩ :=
    slide_heap_full_storage pre.good env.win env.prevp env.headp env.wbytes env.pwords env.hwords pa' qa'
  have shape := shapeS.trans post.shape
  have slideFrame : ByteFrame h (slideHeap h ds w p q d wa pa' qa') (DeflateOwned ds d) :=
    slide_storage_frame h ds w p q d wa pa' qa' _ (Or.inl rfl) (Or.inr (Or.inl env.win))
  refine ⟨post.good, post.chains, post.pending, post.range, post.water, post.form, post.stopped, post.noSlide, ?_,
    post.consumed, ?_, slideFrame.trans post.byteFrame, ?_, shape, full_frame_trans_shape frameS post.frame shapeS,
    full_shape_live_change shape, post.nalloc.trans allocS, post.nextBlk.trans nextS, ?_⟩
  · obtain ⟨base, choice, eq⟩ := post.fields
    rcases choice with same | ⟨again, _⟩
    · exact ⟨base, Or.inr ⟨taken, same⟩, eq⟩
    · exact False.elim (geometry.2.2.2.2.2.2.2.2 again)
  · rcases post.stream with same | ⟨n, ref, io, ia, pointer, data, bound, count, value⟩
    · exact Or.inl same
    · have separate := input_window_separate pre.good input env.win pointer
      refine Or.inr ⟨n, ref, io, ia, pointer, ?_, bound, count, value⟩
      rw [← slide_input_frame pre.good separate]
      exact data
  · intro w0 b win0 other
    have wid : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    rw [post.outside w b env.win other]
    simp [slideHeap, setD, setW, upd_ne _ _ _ _ other]
  · have := post.insertLe
    have := slide_insert_count d
    omega

/-- **`fill_window` from the input range, through the view**: every parameter tuple, both slide
choices, empty or new input. -/
theorem fill_window_input_v {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (pre : FillPreV v roll h r ds z d) (blockLow : -(2 : Int) ^ 62 ≤ d.block_start.toInt)
    (short : d.lookahead.toNat < 262) (input : InputRange h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result, fill_window (some (.tab ds)) h = .ok ((), after) ∧ FillPostV v roll h after r ds z z' d result := by
  by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
  · obtain ⟨w, p, q, wa, pa, qa, pa', qa', env, sizeP, sizeH, prefixRun, preS⟩ := fill_slide_pre_v pre blockLow taken
    have geometry := fill_slide_counts pre.good env.win env.wbytes pre.range taken
    have transfer := fill_window_slide_transfer pre.good env sizeP sizeH pre.range taken prefixRun
    have shortS : (slideState d).lookahead.toNat < 262 := short
    by_cases empty : z.avail_in = 0
    · obtain ⟨after, result, run, post⟩ := fill_window_empty_post_v preS empty geometry.2.2.2.2.2.2.2.2
      exact ⟨after, z, result, transfer.trans run, fill_post_after_slide_input_v pre env taken rfl input post⟩
    · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
        cases pointer : z.next_in with
        | null => exact False.elim (inputValid empty pointer)
        | ref ref io => exact ⟨ref, io, rfl⟩
      obtain ⟨ia, data, inputBound⟩ := input_array pre.good input pointer
      have separate := input_window_separate pre.good input env.win pointer
      have dataS : Space.get (slideHeap h ds w p q d wa pa' qa') ref = some ia := by
        rw [slide_input_frame pre.good separate]; exact data
      obtain ⟨after, z', result, run, post⟩ := fill_window_read_post_v preS shortS empty pointer dataS inputBound
        (fun _ win => input_window_separate pre.good input win pointer) geometry.2.2.2.2.2.2.2.2
      exact ⟨after, z', result, transfer.trans run, fill_post_after_slide_input_v pre env taken rfl input post⟩
  · by_cases empty : z.avail_in = 0
    · obtain ⟨after, result, run, post⟩ := fill_window_empty_post_v pre empty taken
      exact ⟨after, z, result, run, post⟩
    · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
        cases pointer : z.next_in with
        | null => exact False.elim (inputValid empty pointer)
        | ref ref io => exact ⟨ref, io, rfl⟩
      obtain ⟨ia, data, inputBound⟩ := input_array pre.good input pointer
      exact fill_window_read_post_v pre short empty pointer data inputBound
        (fun _ win => input_window_separate pre.good input win pointer) taken

/-! ## What `FillPostV` gives -/

/-- The input `fill_window` consumed, as stream accounting. -/
theorem FillPostV.account {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPostV v roll h after r ds z z' d result) :
    ∃ used, StreamAccounting z z' used 0 ∧ result.lookahead.toNat = d.lookahead.toNat + used := by
  rcases post.stream with same | ⟨n, ref, io, ia, pointer, data, bound, count, value⟩
  · subst same
    exact ⟨0, stream_accounting_self z', by have := post.consumed; omega⟩
  · have account := read_stream_accounting z n ref io
      (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)) pointer count
    rw [← value] at account
    exact ⟨n.toNat, account, by have := post.consumed; have := account.2.2.1; omega⟩

theorem FillPostV.keys {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPostV v roll h after r ds z z' d result) :
    result.window = d.window ∧ result.prev = d.prev ∧ result.head = d.head ∧
      result.pending_buf = d.pending_buf := by
  obtain ⟨base, choice, eq⟩ := post.fields
  rcases choice with same | ⟨_, same⟩ <;> subst same <;> rw [eq] <;> exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
theorem FillPostV.same {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPostV v roll h after r ds z z' d result) :
    result.level = d.level ∧ result.strategy = d.strategy ∧ result.w_size = d.w_size ∧
    result.window_size = d.window_size ∧ result.match_length = d.match_length ∧
    result.match_available = d.match_available ∧ result.prev_length = d.prev_length ∧
    result.sym_next = d.sym_next ∧ result.sym_end = d.sym_end ∧ result.lit_bufsize = d.lit_bufsize ∧
    result.dyn_ltree = d.dyn_ltree ∧ result.dyn_dtree = d.dyn_dtree ∧ result.bl_tree = d.bl_tree ∧
    result.opt_len = d.opt_len ∧ result.static_len = d.static_len ∧ result.pending = d.pending ∧
    result.pending_out = d.pending_out ∧ result.pending_buf = d.pending_buf ∧
    result.last_flush = d.last_flush ∧ result.wrap = d.wrap ∧ result.status = d.status ∧
    result.bi_valid = d.bi_valid ∧ result.«matches» = d.«matches» := by
  obtain ⟨base, choice, eq⟩ := post.fields
  rcases choice with same | ⟨_, same⟩ <;> subst same <;>
    exact ⟨(congrArg DeflateState.level eq).trans rfl, (congrArg DeflateState.strategy eq).trans rfl, (congrArg DeflateState.w_size eq).trans rfl, (congrArg DeflateState.window_size eq).trans rfl, (congrArg DeflateState.match_length eq).trans rfl, (congrArg DeflateState.match_available eq).trans rfl, (congrArg DeflateState.prev_length eq).trans rfl, (congrArg DeflateState.sym_next eq).trans rfl, (congrArg DeflateState.sym_end eq).trans rfl, (congrArg DeflateState.lit_bufsize eq).trans rfl, (congrArg DeflateState.dyn_ltree eq).trans rfl, (congrArg DeflateState.dyn_dtree eq).trans rfl, (congrArg DeflateState.bl_tree eq).trans rfl, (congrArg DeflateState.opt_len eq).trans rfl, (congrArg DeflateState.static_len eq).trans rfl, (congrArg DeflateState.pending eq).trans rfl, (congrArg DeflateState.pending_out eq).trans rfl, (congrArg DeflateState.pending_buf eq).trans rfl, (congrArg DeflateState.last_flush eq).trans rfl, (congrArg DeflateState.wrap eq).trans rfl, (congrArg DeflateState.status eq).trans rfl, (congrArg DeflateState.bi_valid eq).trans rfl, (congrArg DeflateState.«matches» eq).trans rfl⟩

theorem FillPostV.position {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (post : FillPostV v roll h after r ds z z' d result) :
    (result.strstart = d.strstart ∧ result.match_start = d.match_start ∧ result.block_start = d.block_start) ∨
    (d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) ∧ result.strstart = d.strstart - d.w_size ∧
      result.match_start = d.match_start - d.w_size ∧
      result.block_start = Int64.ofInt (d.block_start.toInt - (d.w_size.toNat : Int))) := by
  obtain ⟨base, choice, eq⟩ := post.fields
  rcases choice with same | ⟨taken, same⟩ <;> subst same <;> rw [eq]
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨taken, rfl, rfl, rfl⟩

end Zlib.Deflate.Engine.Proofs
