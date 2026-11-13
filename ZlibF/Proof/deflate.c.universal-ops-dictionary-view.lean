import ZlibF.Proof.«deflate.c.universal-window-view»

/-!
# deflate.c: the body of `deflateSetDictionary` with the chains read through a table view

`setdict_body` (`deflate.c.universal-ops-dictionary`) for every table view
(`deflate.c.engine.view-chains`): the chains of the tables as they are, through one pending slide,
or no chain fact. A level-0 stream with one or two stored slides not yet applied to the tables
(`matches` 1 or 2) reaches the body with the slid view or with none; the body reads the dictionary
through `fill_window` and inserts it into the tables as they are, and the view chains hold at the
end at the insertion frontier. The proofs are those of `deflate.c.universal-ops-dictionary` with
`HeapChains` replaced by `VHeapChains v` and the insertion frontier `strstart - insert` as the
frontier of the chains.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

variable {v : TabView}

set_option maxHeartbeats 1000000 in
/-- One insertion at the cursor `str`, with the chains up to the cursor. -/
theorem dict_insert_step_v {h : Heap} {r : ZStreamRef} {ds w : Nat} {z : ZStream} {d : DeflateState} {str : UInt32}
    {wa : Array UInt8} (good : DGood h r ds z d) (chains : VHeapChains v h d str.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (data : str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) (n : UInt32) :
    ∃ key after, dictBody (some (.tab ds)) (str, n) h = .ok ((str + 1, n), after) ∧
      DGood after r ds z { d with ins_h := key } ∧
      VHeapChains v after { d with ins_h := key } (str.toNat + 1) ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Zlib.Deflate.Proofs.Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧ after.libcErrorBorrow = h.libcErrorBorrow := by
  obtain ⟨w0, p, q, wa0, pa, qa, env, H⟩ := vheap_environment good chains
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
  subst w0
  have aid : wa0 = wa := Option.some.inj (env.wbytes.symm.trans get)
  subst wa0
  have extent := window_extent good win get
  have wsHi := (slide_window_sizes good).2
  have wsz := good.inv.wsz
  obtain ⟨key, after, run, goodA, chainsA, formA⟩ := insert_string_good_vchains good env H str good.inv.wsize
    good.inv.wmask (Nat.le_refl _) data (by omega) (by omega) form
  obtain ⟨shape, frame, _, alloc, next⟩ :=
    insert_string_run_full_storage good env str (by omega) (by omega) run
  have bytesA : after.bytes = h.bytes := by
    obtain ⟨key', _, _, expected⟩ := INSERT_STRING_ok good.live.hs env str (by omega) (by omega)
    have eq := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
    rw [← eq]
  have staticA : after.static = h.static := by
    obtain ⟨key', _, _, expected⟩ := INSERT_STRING_ok good.live.hs env str (by omega) (by omega)
    have eq := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
    rw [← eq]
  have roA : after.ro = h.ro := by
    obtain ⟨key', _, _, expected⟩ := INSERT_STRING_ok good.live.hs env str (by omega) (by omega)
    have eq := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
    rw [← eq]
  have dstatesA : ∀ i, i ≠ ds → after.dstates i = h.dstates i := by
    obtain ⟨key', _, _, expected⟩ := INSERT_STRING_ok good.live.hs env str (by omega) (by omega)
    have eq := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
    intro i ne
    rw [← eq]
    simp [setD, setW, upd_ne _ _ _ _ ne]
  have borrowA : after.libcErrorBorrow = h.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_INSERT_STRING _ _ _ _ _ run
  refine ⟨key, after, ?_, goodA, chainsA, formA, bytesA,
    ⟨staticA, fun i _ => by rw [bytesA], fun i ne => dstatesA i ne, fun i _ => by rw [roA]⟩,
    shape, frame, alloc, next, borrowA⟩
  rw [dict_body_insert, bind_app, run]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The inner insertion loop** of `deflateSetDictionary`: from `strstart` with at least three
bytes of lookahead, it inserts the `lookahead - 2` positions that have three bytes. -/
theorem dict_insert_loop_v {h : Heap} {r : ZStreamRef} {ds w : Nat} {z : ZStream} {d : DeflateState}
    {wa : Array UInt8} (good : DGood h r ds z d) (chains : VHeapChains v h d d.strstart.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (look : 3 ≤ d.lookahead.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ str n key after,
      cdoWhile (dictBody (some (.tab ds))) dictCond (d.strstart, d.lookahead - (MIN_MATCH_u - 1)) h =
        .ok ((str, n), after) ∧
      str.toNat = d.strstart.toNat + d.lookahead.toNat - 2 ∧
      DGood after r ds z { d with ins_h := key } ∧
      VHeapChains v after { d with ins_h := key } str.toNat ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat key ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Zlib.Deflate.Proofs.Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧ after.libcErrorBorrow = h.libcErrorBorrow := by
  have extent := window_extent good win get
  have wsHi := (slide_window_sizes good).2
  have wsz := good.inv.wsz
  let total := d.strstart.toNat + d.lookahead.toNat - 2
  let Inv : UInt32 × UInt32 → Heap → Prop := fun c heap => ∃ key,
    DGood heap r ds z { d with ins_h := key } ∧ VHeapChains v heap { d with ins_h := key } c.1.toNat ∧
    InsHForm d.hash_shift d.hash_mask (bfn wa) c.1.toNat key ∧
    1 ≤ c.2.toNat ∧ c.1.toNat + c.2.toNat = total ∧
    heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧
    Zlib.Deflate.Proofs.Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
    heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk ∧ heap.libcErrorBorrow = h.libcErrorBorrow
  let Q : UInt32 × UInt32 → Heap → Prop := fun c heap => ∃ key,
    c.1.toNat = total ∧
    DGood heap r ds z { d with ins_h := key } ∧ VHeapChains v heap { d with ins_h := key } c.1.toNat ∧
    InsHForm d.hash_shift d.hash_mask (bfn wa) c.1.toNat key ∧
    heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds) ∧
    Zlib.Deflate.Proofs.Shape h heap ∧ Frame h heap (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
    heap.nalloc = h.nalloc ∧ heap.nextBlk = h.nextBlk ∧ heap.libcErrorBorrow = h.libcErrorBorrow
  let rank : UInt32 × UInt32 → Heap → Nat := fun c _ => c.2.toNat
  have step : ∀ c heap, Inv c heap → ∃ c1 h1 b c2 h2,
      dictBody (some (.tab ds)) c heap = .ok (c1, h1) ∧ dictCond c1 h1 = .ok ((b, c2), h2) ∧
      (b = false → Q c2 h2) ∧ (b = true → Inv c2 h2 ∧ rank c2 h2 < rank c heap) := by
    rintro ⟨str, n⟩ heap ⟨key, goodS, chainsS, formS, pos, sum, bytesS, bframeS, shapeS, frameS, allocS, nextS,
      borrowS⟩
    dsimp only at chainsS formS pos sum
    have getS : heap.bytes w = some wa := by rw [bytesS]; exact get
    obtain ⟨key', after, run, goodA, chainsA, formA, bytesA, bframeA, shapeA, frameA, allocA, nextA, borrowA⟩ :=
      dict_insert_step_v (str := str) goodS chainsS win getS room (by show str.toNat + 3 ≤ d.strstart.toNat + d.lookahead.toNat; omega) formS n
    have strNext : (str + 1).toNat = str.toNat + 1 := by
      rw [UInt32.toNat_add]; simp only [show (1 : UInt32).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have nDown : (n - 1).toNat = n.toNat - 1 :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using pos))
    have dEq : ({ { d with ins_h := key } with ins_h := key' } : DeflateState) = { d with ins_h := key' } := rfl
    rw [dEq] at goodA chainsA
    have frameA' : Frame heap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := frameA
    refine ⟨(str + 1, n), after, n - 1 != 0, (str + 1, n - 1), after, run, rfl, ?_, ?_⟩
    · intro stop
      have zero : n - 1 = 0 := by simpa only [bne_eq_false_iff_eq] using stop
      have one : n.toNat = 1 := by have := congrArg UInt32.toNat zero; rw [nDown] at this; simp at this; omega
      refine ⟨key', by change (str + 1).toNat = total; rw [strNext]; omega, goodA, ?_, ?_, bytesA.trans bytesS,
        bframeS.trans bframeA, shapeS.trans shapeA, full_frame_trans_shape frameS frameA' shapeS,
        allocA.trans allocS, nextA.trans nextS, borrowA.trans borrowS⟩
      · change VHeapChains v after _ (str + 1).toNat; rw [strNext]; exact chainsA
      · change InsHForm _ _ _ (str + 1).toNat key'; rw [strNext]; exact formA
    · intro more
      have nonzero : n - 1 ≠ 0 := by simpa only [bne_iff_ne] using more
      have pos' : 1 ≤ (n - 1).toNat := by
        have ne : (n - 1).toNat ≠ 0 := fun e => nonzero (UInt32.toNat_inj.mp e)
        omega
      refine ⟨⟨key', goodA, ?_, ?_, pos', ?_, bytesA.trans bytesS, bframeS.trans bframeA, shapeS.trans shapeA,
        full_frame_trans_shape frameS frameA' shapeS, allocA.trans allocS, nextA.trans nextS,
        borrowA.trans borrowS⟩, ?_⟩
      · change VHeapChains v after _ (str + 1).toNat; rw [strNext]; exact chainsA
      · change InsHForm _ _ _ (str + 1).toNat key'; rw [strNext]; exact formA
      · change (str + 1).toNat + (n - 1).toNat = total; rw [strNext, nDown]; omega
      · change (n - 1).toNat < n.toNat; omega
  have nInit : (d.lookahead - (MIN_MATCH_u - 1)).toNat = d.lookahead.toNat - 2 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 2 ≤ _; omega))
  have initial : Inv (d.strstart, d.lookahead - (MIN_MATCH_u - 1)) h :=
    ⟨d.ins_h, good, chains, form, by change 1 ≤ (d.lookahead - (MIN_MATCH_u - 1)).toNat; omega,
      by change d.strstart.toNat + (d.lookahead - (MIN_MATCH_u - 1)).toNat = total; omega,
      rfl, ByteFrame.refl h _, Zlib.Deflate.Proofs.Shape.refl h, (by simp [Frame]), rfl, rfl, rfl⟩
  have fuelBound : rank (d.strstart, d.lookahead - (MIN_MATCH_u - 1)) h < fuel := by
    change (d.lookahead - (MIN_MATCH_u - 1)).toNat < 18446744073709551616
    omega
  obtain ⟨⟨str, n⟩, after, run, key, strEq, rest⟩ := do_heap_rank Inv rank Q step initial fuelBound
  exact ⟨str, n, key, after, run, strEq, rest⟩

/-! ## The outer loop -/

/-- The state of the outer loop of `deflateSetDictionary`, relative to the heap `h0` and the state
`base` where it started. `C` bounds `strstart - block_start` plus the data still to come. -/
structure DictLoopV (v : TabView) (h0 h : Heap) (r : ZStreamRef) (ds : Nat) (base : DeflateState) (C : Nat)
    (z : ZStream) (d : DeflateState) : Prop where
  pre : FillPreV v True h r ds z d
  input : InputRange h r
  valid : z.avail_in ≠ 0 → z.next_in ≠ .null
  span : ((d.strstart.toNat + d.lookahead.toNat + z.avail_in.toNat : Nat) : Int) - d.block_start.toInt ≤ C
  water : fillEnd d ≤ d.high_water.toNat
  fields : DictFields base d
  alloc : DefAlloc z
  shape : Zlib.Deflate.Proofs.Shape h0 h
  frame : Frame h0 h (fun b => StreamRoot r b ∨ DeflateOwned ds base b)
  nalloc : h.nalloc = h0.nalloc
  nextBlk : h.nextBlk = h0.nextBlk
  borrow : h.libcErrorBorrow = h0.libcErrorBorrow
  bytes : ∀ w b, base.window = .ref (.blk w) 0 → b ≠ w → h.bytes b = h0.bytes b

theorem DictLoopV.low {h0 h : Heap} {r : ZStreamRef} {ds : Nat} {base : DeflateState} {C : Nat}
    {z : ZStream} {d : DeflateState} (L : DictLoopV v h0 h r ds base C z d) (small : C ≤ 2 ^ 61) :
    -(2 : Int) ^ 62 ≤ d.block_start.toInt := by
  have := L.span
  have p61 : (2 : Int) ^ 62 = 4611686018427387904 := rfl
  have p : ((2 ^ 61 : Nat) : Int) = 2305843009213693952 := rfl
  have : (C : Int) ≤ 2305843009213693952 := by rw [← p]; exact_mod_cast small
  omega

set_option maxHeartbeats 8000000 in
/-- **The outer loop** of `deflateSetDictionary`: rounds of insertion and refill while three bytes
of lookahead remain. -/
theorem dict_outer_loop_v {h0 h : Heap} {r : ZStreamRef} {ds : Nat} {base : DeflateState} {C : Nat}
    {z : ZStream} {d : DeflateState} (start : DictLoopV v h0 h r ds base C z d) (small : C ≤ 2 ^ 61)
    (wrap0 : base.wrap = 0) :
    ∃ after, cwhile (dictOuterCond (some (.tab ds))) (dictOuterBody (some (.tab ds))) () h = .ok ((), after) ∧
      ∃ z' d', DictLoopV v h0 after r ds base C z' d' ∧ d'.lookahead.toNat < 3 := by
  let I : Unit → Heap → Prop := fun _ heap => ∃ z d, DictLoopV v h0 heap r ds base C z d
  let Q : Unit → Heap → Prop := fun _ heap => ∃ z d, DictLoopV v h0 heap r ds base C z d ∧ d.lookahead.toNat < 3
  let μ : Unit → Heap → Nat := fun _ heap =>
    ((r.get heap).map (·.avail_in.toNat)).getD 0 + ((heap.dstates ds).map (·.lookahead.toNat)).getD 0
  have step : ∀ u heap, I u heap → ∃ c u1 h1, dictOuterCond (some (.tab ds)) u heap = .ok ((c, u1), h1) ∧
      (c = true → ∃ u2 h2, dictOuterBody (some (.tab ds)) u1 h1 = .ok (u2, h2) ∧ I u2 h2 ∧ μ u2 h2 < μ u heap) ∧
      (c = false → Q u1 h1) := by
    rintro ⟨⟩ heap ⟨z, d, L⟩
    have good := L.pre.good
    have condRun : dictOuterCond (some (.tab ds)) () heap =
        .ok ((decide (d.lookahead ≥ MIN_MATCH_u), ()), heap) := by
      simp [dictOuterCond, rdD_eq, good.live.hs, bind_app]
    refine ⟨_, (), heap, condRun, fun more => ?_, fun stop => ⟨z, d, L, ?_⟩⟩
    rotate_left
    · have : ¬ d.lookahead ≥ MIN_MATCH_u := by simpa using stop
      rw [GE.ge, UInt32.le_iff_toNat_le] at this
      exact Nat.lt_of_not_le this
    have ready : 3 ≤ d.lookahead.toNat := by
      have : d.lookahead ≥ MIN_MATCH_u := by simpa using more
      rw [GE.ge, UInt32.le_iff_toNat_le] at this
      exact this
    obtain ⟨zero, formE⟩ := L.pre.form ready
    obtain ⟨w, wa, win, get, form⟩ := formE trivial
    have topS : chainTop d = d.strstart.toNat := by
      unfold chainTop; rw [zero]
      have z0 : (0 : UInt32).toNat = 0 := rfl
      rw [z0]; omega
    have chainsS : VHeapChains v heap d d.strstart.toNat := by rw [← topS]; exact L.pre.chains
    have range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat := L.pre.range
    obtain ⟨str, n, key, h1, run1, strEq, good1, chains1, form1, bytes1, bframe1, shape1, frame1, alloc1,
      next1, borrow1⟩ := dict_insert_loop_v good chainsS win get range ready form
    let d2 : DeflateState := { { d with ins_h := key } with strstart := str, lookahead := MIN_MATCH_u - 1 }
    obtain ⟨h2, h2def⟩ : ∃ x, x = setD h1 ds d2 := ⟨_, rfl⟩
    have wrRun : wr (some (.tab ds)) (fun d => { d with strstart := str, lookahead := MIN_MATCH_u - 1 }) h1 =
        .ok ((), h2) := by rw [h2def, wrD_eq, good1.live.hs]
    have good2 : DGood h2 r ds z d2 := by rw [h2def]; exact engine_update_good good1 rfl
    have ss2 : d2.strstart.toNat = d.strstart.toNat + d.lookahead.toNat - 2 := strEq
    have la2 : d2.lookahead.toNat = 2 := rfl
    have ins2 : d2.insert = 0 := zero
    have top2 : chainTop d2 = str.toNat := by
      unfold chainTop; rw [ins2, la2]
      have z0 : (0 : UInt32).toNat = 0 := rfl
      rw [z0]; change min (str.toNat - 0) (str.toNat + 2 - 2) = str.toNat; omega
    have chains2 : VHeapChains v h2 d2 (chainTop d2) := by
      rw [top2, h2def]
      obtain ⟨w', p', q', wa', pa', qa', win', prev', hd', hw', hp', hq', H⟩ := chains1
      refine ⟨w', p', q', wa', pa', qa', win', prev', hd', by simpa [setD] using hw', by simpa [setD] using hp',
        by simpa [setD] using hq', ?_⟩
      have e : d2.strstart.toNat + d2.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := by
        rw [ss2, la2]; omega
      change ViewChains v _ _ _ _ _ _ _ _ (d2.strstart.toNat + d2.lookahead.toNat)
      rw [e]
      exact H
    have wrapB : d.wrap = 0 := by rw [L.fields]; exact wrap0
    have pre2 : FillPreV v True h2 r ds z d2 :=
      ⟨good2, chains2, by rw [ins2]; exact Nat.zero_le _,
        by change d2.strstart.toNat + d2.lookahead.toNat ≤ d.window_size.toNat; rw [ss2, la2]; omega,
        fun large => by rw [la2] at large; omega, fun two => by change d.wrap = 2 at two; rw [wrapB] at two; cases two⟩
    have bframe2 : ByteFrame heap h2 (fun i => i = ds) := by
      rw [h2def]; exact bframe1.trans (byte_frame_setD h1 ds d2)
    have owned2 := stream_owned_keys good good2 rfl rfl rfl rfl
    have borrow2 : h2.libcErrorBorrow = heap.libcErrorBorrow := by rw [h2def]; exact borrow1
    have input2 : InputRange h2 r := by
      obtain ⟨z0, get0, caller⟩ := L.input
      have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
      subst z0
      refine ⟨z, good2.live.hz, ?_⟩
      have := caller_range_advance (used := 0) (remaining := z.avail_in.toNat) caller bframe2
        (fun b same => (stream_owned_deflate good b).mpr (Or.inl same)) owned2 (by omega) borrow2
      rwa [advance_zero] at this
    have spanB := L.span
    have small2 : -(2 : Int) ^ 62 ≤ d2.block_start.toInt := L.low small
    obtain ⟨after, z', d', fillRun, post⟩ :=
      fill_window_input_v pre2 small2 (by rw [la2]; omega) input2 L.valid
    have fillRun' : fill_window (some (.tab ds)) h2 = .ok ((), after) := fillRun
    obtain ⟨used, account, lookUsed⟩ := post.account
    obtain ⟨winK, prevK, headK, pbufK⟩ := post.keys
    obtain ⟨sLevel, sStrategy, sWsize, sWinSize, sMl, sMa, sPl, sSym, sEnd, sLit, sLt, sDt, sBl, sOpt, sStc,
      sPending, sPout, sPbuf, sLf, sWrap, sStatus, sBv, sMatches⟩ := post.same
    have bodyRun : dictOuterBody (some (.tab ds)) () heap = .ok ((), after) := by
      unfold dictOuterBody
      rw [bind_app, ldDeflateState_tab good.live.hs]
      simp only []
      rw [bind_app, run1]
      simp only []
      rw [bind_app, wrRun]
      simp only []
      rw [bind_app, fillRun']
      rfl
    have sums := post.consumed
    have la2N : d2.lookahead.toNat = 2 := la2
    refine ⟨(), after, bodyRun, ⟨z', d', ?_⟩, ?_⟩
    · -- the invariant after the refill
      have fields2 : DictFields base d2 := by
        unfold DictFields at *
        have e := L.fields
        change { { d with ins_h := key } with strstart := str, lookahead := MIN_MATCH_u - 1 } = _
        rw [e]
      have fieldsA : DictFields base d' := by
        unfold DictFields at *
        obtain ⟨b0, choice, eq⟩ := post.fields
        rcases choice with same | ⟨_, same⟩ <;> subst same <;> rw [eq] <;> rw [fields2] <;> rfl
      have inputA : InputRange after r := by
        obtain ⟨z0, get0, caller⟩ := input2
        have same : z0 = z := Option.some.inj (get0.symm.trans good2.live.hz)
        subst z0
        refine ⟨z', post.good.live.hz, ?_⟩
        have frameB : ByteFrame h2 after (fun b => StreamOwned h2 r b) := by
          obtain ⟨st, by_, dst, ro⟩ := post.byteFrame
          exact ⟨st, fun i ni => by_ i (fun o => ni ((stream_owned_deflate good2 i).mpr o)),
            fun i ni => dst i (fun o => ni ((stream_owned_deflate good2 i).mpr o)),
            fun i ni => ro i (fun o => ni ((stream_owned_deflate good2 i).mpr o))⟩
        have := caller_range_advance (used := used) (remaining := z'.avail_in.toNat) caller frameB
          (fun b o => o) (stream_owned_keys good2 post.good winK prevK headK pbufK)
          (by have := account.2.2.1; omega) (Zlib.Deflate.BorrowProofs.stable_fill_window _ _ _ _ fillRun)
        rw [account.2.2.2.2.1]
        exact this
      refine ⟨⟨post.good, post.chains, post.pending, post.range,
          fun large => ⟨(post.form large).1, fun _ => (post.form large).2 trivial⟩,
          fun two => by rw [sWrap] at two; change d.wrap = 2 at two; rw [wrapB] at two; cases two⟩,
        inputA, ?_, ?_, post.water, fieldsA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro nz
        rw [account.2.2.2.2.1]
        refine input_advance_ne_null _ (L.valid fun e => nz (UInt32.toNat_inj.mp ?_))
        have a1 := account.2.2.1
        have e0 : z.avail_in.toNat = 0 := by rw [e]; rfl
        change z'.avail_in.toNat = 0
        omega
      · have fe : fillEnd d' = d'.strstart.toNat + d'.lookahead.toNat := rfl
        rcases post.position with ⟨e1, _, e3⟩ | ⟨taken, e1, _, e3⟩
        · rw [e1, e3]
          change (((d2.strstart.toNat + d'.lookahead.toNat + z'.avail_in.toNat : Nat)) : Int) - d.block_start.toInt ≤ C
          rw [ss2]
          omega
        · have threshold := slide_threshold good2
          rw [GE.ge, UInt32.le_iff_toNat_le, threshold] at taken
          have wsz := good2.inv.wsz
          have ws2 := slide_window_sizes good2
          rw [e1, e3, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]
          have low := small2
          have high := Int64.toInt_lt d2.block_start
          have p62 : (2 : Int) ^ 62 = 4611686018427387904 := rfl
          have p63 : (2 : Int) ^ 63 = 9223372036854775808 := rfl
          rw [Int64.toInt_ofInt, Int.bmod_eq_of_le (by change -9223372036854775808 ≤ _; omega)
            (by change _ < 9223372036854775808; omega)]
          change (((d2.strstart.toNat - d2.w_size.toNat + d'.lookahead.toNat + z'.avail_in.toNat : Nat)) : Int) -
            (d.block_start.toInt - (d2.w_size.toNat : Int)) ≤ C
          rw [ss2]
          omega
      · exact ⟨account.2.2.2.2.2.2.2.1.trans L.alloc.1, account.2.2.2.2.2.2.2.2.1.trans L.alloc.2⟩
      · have shapeH : Zlib.Deflate.Proofs.Shape heap h2 := by
          rw [h2def]; exact shape1.trans (shape_setD good1.live.hs d2)
        exact (L.shape.trans shapeH).trans post.shape
      · have shapeH : Zlib.Deflate.Proofs.Shape heap h2 := by
          rw [h2def]; exact shape1.trans (shape_setD good1.live.hs d2)
        have frameH : Frame heap h2 (fun b => StreamRoot r b ∨ DeflateOwned ds base b) := by
          rw [h2def]
          have f1 : Frame heap h1 (fun b => StreamRoot r b ∨ DeflateOwned ds base b) := by
            apply full_frame_weaken frame1
            intro b o
            rcases o with root | own
            · exact Or.inl root
            · right; rw [L.fields] at own; exact own
          exact full_frame_trans_shape f1 (full_frame_weaken (state_store_full_frame h1 ds d2)
            (fun _ same => Or.inr (Or.inl same))) shape1
        have frameP : Frame h2 after (fun b => StreamRoot r b ∨ DeflateOwned ds base b) := by
          apply full_frame_weaken post.frame
          intro b o
          rcases o with root | own
          · exact Or.inl root
          · right; rw [fields2] at own; exact own
        exact full_frame_trans_shape (full_frame_trans_shape L.frame frameH L.shape) frameP
          (L.shape.trans shapeH)
      · rw [post.nalloc, h2def]; change h1.nalloc = h0.nalloc; rw [alloc1, L.nalloc]
      · rw [post.nextBlk, h2def]; change h1.nextBlk = h0.nextBlk; rw [next1, L.nextBlk]
      · rw [Zlib.Deflate.BorrowProofs.stable_fill_window _ _ _ _ fillRun, borrow2, L.borrow]
      · intro w0 b win0 other
        have winD : d2.window = .ref (.blk w0) 0 := by rw [fields2]; exact win0
        rw [post.outside w0 b winD other, h2def]
        change h1.bytes b = h0.bytes b
        rw [bytes1, L.bytes w0 b win0 other]
    · -- the measure
      simp only [μ, post.good.live.hz, post.good.live.hs, good.live.hz, good.live.hs, Option.map_some,
        Option.getD_some]
      omega
  have initial : I () h := ⟨z, d, start⟩
  have bound : μ () h < fuel := by
    simp only [μ, start.pre.good.live.hz, start.pre.good.live.hs, Option.map_some, Option.getD_some]
    have := z.avail_in.toNat_lt
    have := d.lookahead.toNat_lt
    change _ < 18446744073709551616
    omega
  obtain ⟨u, after, run, q⟩ := cwhile_measure I Q μ step initial bound
  exact ⟨after, run, q⟩

/-- `DictFields` after `fill_window`. -/
theorem dict_fields_fill_v {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {base d d' : DeflateState} (fields : DictFields base d) (post : FillPostV v roll h after r ds z z' d d') :
    DictFields base d' := by
  unfold DictFields at *
  obtain ⟨b0, choice, eq⟩ := post.fields
  rcases choice with same | ⟨_, same⟩ <;> subst same <;> rw [eq] <;> rw [fields] <;> rfl

/-- The span of `fill_window`: data in the window and still to come, behind the block start. -/
theorem fill_span_v {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d d' : DeflateState} (good : DGood h r ds z d) (low : -(2 : Int) ^ 62 ≤ d.block_start.toInt)
    (post : FillPostV v roll h after r ds z z' d d') :
    ((d'.strstart.toNat + d'.lookahead.toNat + z'.avail_in.toNat : Nat) : Int) - d'.block_start.toInt =
      ((d.strstart.toNat + d.lookahead.toNat + z.avail_in.toNat : Nat) : Int) - d.block_start.toInt := by
  have sums := post.consumed
  rcases post.position with ⟨e1, _, e3⟩ | ⟨taken, e1, _, e3⟩
  · rw [e1, e3]; omega
  · have threshold := slide_threshold good
    rw [GE.ge, UInt32.le_iff_toNat_le, threshold] at taken
    have ws2 := slide_window_sizes good
    rw [e1, e3, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]
    have high := Int64.toInt_lt d.block_start
    have p62 : (2 : Int) ^ 62 = 4611686018427387904 := rfl
    have p63 : (2 : Int) ^ 63 = 9223372036854775808 := rfl
    rw [Int64.toInt_ofInt, Int.bmod_eq_of_le (by change -9223372036854775808 ≤ _; omega)
      (by change _ < 9223372036854775808; omega)]
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The tail of `deflateSetDictionary`** from a prepared state (`wrap` 0, no lookahead, chains
at the frontier): read the dictionary, insert it, end with no lookahead and restore the caller's
input and `wrap`. The invariant holds afterwards. The chains are read through the view `v`; `hashOk` turns the view chains of the end state into its hash state. -/
theorem setdict_tail_v {h0 hA : Heap} {r : ZStreamRef} {ds : Nat} {z0 zA : ZStream} {d0 dA : DeflateState}
    {dict : BPtr} {len : UInt32} {X0 : Nat}
    (inv : DInv h0 r ds z0 d0) (goodA : DGood hA r ds zA dA)
    (fieldsA : DictFields { d0 with wrap := 0 } dA)
    (chainsA : VHeapChains v hA dA (chainTop dA))
    (hashOk : ∀ (heap : Heap) (dF : DeflateState), dF.«matches» = d0.«matches» → dF.lookahead = 0 →
      VHeapChains v heap dF (chainTop dF) → Hashing heap dF)
    (laA : dA.lookahead = 0) (insA : dA.insert.toNat ≤ dA.strstart.toNat)
    (roomA : dA.strstart.toNat ≤ dA.window_size.toNat)
    (waterA : dA.strstart.toNat ≤ dA.high_water.toNat)
    (spanA : (dA.strstart.toNat : Int) - dA.block_start.toInt ≤ X0) (small : X0 + len.toNat ≤ 2 ^ 61)
    (input : CallerRange hA r dict len.toNat false) (valid : len ≠ 0 → dict ≠ .null)
    (allocA : DefAlloc zA)
    (shapeA : Zlib.Deflate.Proofs.Shape h0 hA) (frameA : Frame h0 hA (fun b => StreamRoot r b ∨ DeflateOwned ds d0 b))
    (nallocA : hA.nalloc = h0.nalloc) (nextA : hA.nextBlk = h0.nextBlk)
    (borrowA : hA.libcErrorBorrow = h0.libcErrorBorrow)
    (bytesA : ∀ w b, d0.window = .ref (.blk w) 0 → b ≠ w → hA.bytes b = h0.bytes b)
    (staticA : hA.static = h0.static) (sym0 : d0.sym_next = 0) :
    ∃ after zF dF, setdictTail (some r) (some (.tab ds)) dict len d0.wrap hA = .ok (Z_OK, after) ∧
      DInv after r ds zF dF ∧ Zlib.Deflate.Proofs.Shape h0 after ∧
      Frame h0 after (fun b => StreamRoot r b ∨ DeflateOwned ds d0 b) ∧
      after.nalloc = h0.nalloc ∧ after.nextBlk = h0.nextBlk ∧ (∀ b, DeflateOwned ds dF b ↔ DeflateOwned ds d0 b) ∧
      (HeaderInv d0 → HeaderInv dF) ∧
      (dF.status = d0.status ∧ dF.sym_next = d0.sym_next ∧ dF.gzhead = d0.gzhead ∧ (CallFacts d0 → CallFacts dF)) := by
  have shape0 := inv.shape
  have wrapA : dA.wrap = 0 := by rw [fieldsA]
  -- the dictionary as input
  let zB : ZStream := { zA with avail_in := len, next_in := dict }
  obtain ⟨hB, hBdef⟩ : ∃ x, x = r.put hA zB := ⟨_, rfl⟩
  have zwrB : zwr (some r) (fun z => { z with avail_in := len, next_in := dict }) hA = .ok ((), hB) := by
    rw [zwr_eq, goodA.live.hz, hBdef]
  have goodB : DGood hB r ds zB dA := by rw [hBdef]; exact good_put goodA zB rfl rfl rfl
  have chainsB : VHeapChains v hB dA (chainTop dA) := by
    rw [hBdef]
    obtain ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, H⟩ := chainsA
    exact ⟨w, p, q, wa, pa, qa, win, prev, hd, by simpa using hw, by simpa using hp, by simpa using hq, H⟩
  have borrowB : hB.libcErrorBorrow = hA.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_zwr _ _ _ _ _ zwrB
  have inputB : InputRange hB r := by
    refine ⟨zB, goodB.live.hz, ?_⟩
    have frame : ByteFrame hA hB (fun _ => False) :=
      ⟨by rw [hBdef]; simp, fun _ _ => by rw [hBdef]; simp, fun _ _ => by rw [hBdef]; simp,
        fun _ _ => by rw [hBdef]; simp⟩
    have := caller_range_advance (used := 0) (remaining := len.toNat) input frame (fun _ f => f.elim)
      (stream_owned_keys goodA goodB rfl rfl rfl rfl) (by omega) borrowB
    rwa [advance_zero] at this
  have preB : FillPreV v True hB r ds zB dA :=
    ⟨goodB, chainsB, insA, by change dA.strstart.toNat + dA.lookahead.toNat ≤ _; rw [laA]; simpa using roomA,
      fun large => by rw [laA] at large; exact absurd large (by decide),
      fun two => by rw [wrapA] at two; cases two⟩
  have lowB : -(2 : Int) ^ 62 ≤ dA.block_start.toInt := by
    have p62 : (2 : Int) ^ 62 = 4611686018427387904 := rfl
    have : (X0 : Int) ≤ 2305843009213693952 := by
      have : ((2 ^ 61 : Nat) : Int) = 2305843009213693952 := rfl
      omega
    omega
  obtain ⟨after1, z1, d1, fillRun1, post1⟩ :=
    fill_window_input_v preB lowB (by rw [laA]; decide) inputB valid
  have fillRun1' : fill_window (some (.tab ds)) hB = .ok ((), after1) := fillRun1
  obtain ⟨used1, account1, _⟩ := post1.account
  obtain ⟨winK, prevK, headK, pbufK⟩ := post1.keys
  -- the loop state after the first refill
  have ownedA : ∀ b, DeflateOwned ds dA b ↔ DeflateOwned ds d0 b := by
    intro b; rw [fieldsA]; exact Iff.rfl
  have frameAB : Frame h0 hB (fun b => StreamRoot r b ∨ DeflateOwned ds dA b) := by
    have f1 : Frame h0 hA (fun b => StreamRoot r b ∨ DeflateOwned ds dA b) :=
      full_frame_weaken frameA (fun b o => by rcases o with o | o; exact Or.inl o; exact Or.inr ((ownedA b).2 o))
    rw [hBdef]
    exact full_frame_trans_shape f1 (full_frame_weaken (stream_store_full_frame hA r zB) (fun _ o => Or.inl o)) shapeA
  have shapeAB : Zlib.Deflate.Proofs.Shape h0 hB := by
    rw [hBdef]; exact shapeA.trans (shape_put goodA.live.hz zB)
  have L1 : DictLoopV v h0 after1 r ds dA (X0 + len.toNat) z1 d1 := by
    have inputA1 : InputRange after1 r := by
      obtain ⟨z0', get0, caller⟩ := inputB
      have same : z0' = zB := Option.some.inj (get0.symm.trans goodB.live.hz)
      subst z0'
      refine ⟨z1, post1.good.live.hz, ?_⟩
      have frameB : ByteFrame hB after1 (fun b => StreamOwned hB r b) := by
        obtain ⟨st, by_, dst, ro⟩ := post1.byteFrame
        exact ⟨st, fun i ni => by_ i (fun o => ni ((stream_owned_deflate goodB i).mpr o)),
          fun i ni => dst i (fun o => ni ((stream_owned_deflate goodB i).mpr o)),
          fun i ni => ro i (fun o => ni ((stream_owned_deflate goodB i).mpr o))⟩
      have := caller_range_advance (used := used1) (remaining := z1.avail_in.toNat) caller frameB
        (fun b o => o) (stream_owned_keys goodB post1.good winK prevK headK pbufK)
        (by have := account1.2.2.1; omega) (Zlib.Deflate.BorrowProofs.stable_fill_window _ _ _ _ fillRun1)
      rw [account1.2.2.2.2.1]
      exact this
    refine ⟨⟨post1.good, post1.chains, post1.pending, post1.range,
        fun large => ⟨(post1.form large).1, fun _ => (post1.form large).2 trivial⟩,
        fun two => by rw [post1.same.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, wrapA] at two; cases two⟩,
      inputA1, ?_, ?_, post1.water, dict_fields_fill_v (by unfold DictFields; rfl) post1, ?_,
      shapeAB.trans post1.shape, full_frame_trans_shape frameAB (full_frame_weaken post1.frame (fun _ o => o)) shapeAB,
      by rw [post1.nalloc, hBdef]; simpa using nallocA, by rw [post1.nextBlk, hBdef]; simpa using nextA,
      by rw [Zlib.Deflate.BorrowProofs.stable_fill_window _ _ _ _ fillRun1, borrowB, borrowA], ?_⟩
    · intro nz
      rw [account1.2.2.2.2.1]
      refine input_advance_ne_null _ (valid fun e => nz (UInt32.toNat_inj.mp ?_))
      have a1 := account1.2.2.1
      have e0 : zB.avail_in.toNat = 0 := by change len.toNat = 0; rw [e]; rfl
      change z1.avail_in.toNat = 0
      omega
    · rw [fill_span_v goodB lowB post1]
      change ((dA.strstart.toNat + dA.lookahead.toNat + len.toNat : Nat) : Int) - dA.block_start.toInt ≤ _
      rw [laA]
      push_cast
      have z0 : ((0 : UInt32).toNat : Int) = 0 := rfl
      omega
    · exact ⟨account1.2.2.2.2.2.2.2.1.trans allocA.1, account1.2.2.2.2.2.2.2.2.1.trans allocA.2⟩
    · intro w b win other
      rw [post1.outside w b win other, hBdef]
      simp only [ZStreamRef.put_bytes]
      have e : dA.window = d0.window := by rw [fieldsA]
      exact bytesA w b (by rw [← e]; exact win) other
  -- the loop
  obtain ⟨after2, loopRun, z2, d2, L2, short2⟩ := dict_outer_loop_v L1 small wrapA
  have good2 := L2.pre.good
  obtain ⟨after3, writesRun, goodF, bytes3, words3, static3, shape3, frame3, nalloc3, next3⟩ :=
    setdict_writes good2 zA.next_in zA.avail_in d0.wrap inv.good.inv.wrap_lo inv.good.inv.wrap_hi
  let dF := setdictEnd d2 d0.wrap
  let zF : ZStream := { z2 with next_in := zA.next_in, avail_in := zA.avail_in }
  have tailRun : setdictTail (some r) (some (.tab ds)) dict len d0.wrap hA = .ok (Z_OK, after3) := by
    unfold setdictTail
    rw [bind_app, ldZStream_ok goodA.live.hz]
    simp only []
    rw [bind_app, zwrB]
    simp only []
    rw [bind_app, fillRun1']
    simp only []
    rw [bind_app, loopRun]
    simp only []
    unfold setdictWrites at writesRun
    exact writesRun
  -- the fields of the end state
  have e2 : ∀ {β : Type} (g : DeflateState → β), (∀ x : DeflateState, g { x with strstart := d2.strstart, lookahead := d2.lookahead, ins_h := d2.ins_h, insert := d2.insert, high_water := d2.high_water, block_start := d2.block_start, match_start := d2.match_start, slid := d2.slid } = g x) → g d2 = g dA :=
    fun g hg => (congrArg g L2.fields).trans (hg dA)
  have eA : ∀ {β : Type} (g : DeflateState → β), (∀ x : DeflateState, g { x with strstart := dA.strstart, lookahead := dA.lookahead, ins_h := dA.ins_h, insert := dA.insert, high_water := dA.high_water, block_start := dA.block_start, match_start := dA.match_start, slid := dA.slid } = g x) → g dA = g { d0 with wrap := 0 } :=
    fun g hg => (congrArg g fieldsA).trans (hg _)
  have eLv : d2.level = d0.level := (e2 DeflateState.level fun _ => rfl).trans (eA DeflateState.level fun _ => rfl)
  have eSt : d2.strategy = d0.strategy := (e2 DeflateState.strategy fun _ => rfl).trans (eA DeflateState.strategy fun _ => rfl)
  have eWs : d2.window_size = d0.window_size := (e2 DeflateState.window_size fun _ => rfl).trans (eA DeflateState.window_size fun _ => rfl)
  have eW : d2.w_size = d0.w_size := (e2 DeflateState.w_size fun _ => rfl).trans (eA DeflateState.w_size fun _ => rfl)
  have eWin : d2.window = d0.window := (e2 DeflateState.window fun _ => rfl).trans (eA DeflateState.window fun _ => rfl)
  have ePrev : d2.prev = d0.prev := (e2 DeflateState.prev fun _ => rfl).trans (eA DeflateState.prev fun _ => rfl)
  have eHead : d2.head = d0.head := (e2 DeflateState.head fun _ => rfl).trans (eA DeflateState.head fun _ => rfl)
  have ePb : d2.pending_buf = d0.pending_buf := (e2 DeflateState.pending_buf fun _ => rfl).trans (eA DeflateState.pending_buf fun _ => rfl)
  have ePo : d2.pending_out = d0.pending_out := (e2 DeflateState.pending_out fun _ => rfl).trans (eA DeflateState.pending_out fun _ => rfl)
  have ePd : d2.pending = d0.pending := (e2 DeflateState.pending fun _ => rfl).trans (eA DeflateState.pending fun _ => rfl)
  have eSym : d2.sym_next = d0.sym_next := (e2 DeflateState.sym_next fun _ => rfl).trans (eA DeflateState.sym_next fun _ => rfl)
  have eEnd : d2.sym_end = d0.sym_end := (e2 DeflateState.sym_end fun _ => rfl).trans (eA DeflateState.sym_end fun _ => rfl)
  have eLit : d2.lit_bufsize = d0.lit_bufsize := (e2 DeflateState.lit_bufsize fun _ => rfl).trans (eA DeflateState.lit_bufsize fun _ => rfl)
  have eLt : d2.dyn_ltree = d0.dyn_ltree := (e2 DeflateState.dyn_ltree fun _ => rfl).trans (eA DeflateState.dyn_ltree fun _ => rfl)
  have eDt : d2.dyn_dtree = d0.dyn_dtree := (e2 DeflateState.dyn_dtree fun _ => rfl).trans (eA DeflateState.dyn_dtree fun _ => rfl)
  have eBl : d2.bl_tree = d0.bl_tree := (e2 DeflateState.bl_tree fun _ => rfl).trans (eA DeflateState.bl_tree fun _ => rfl)
  have eOpt : d2.opt_len = d0.opt_len := (e2 DeflateState.opt_len fun _ => rfl).trans (eA DeflateState.opt_len fun _ => rfl)
  have eStc : d2.static_len = d0.static_len := (e2 DeflateState.static_len fun _ => rfl).trans (eA DeflateState.static_len fun _ => rfl)
  have eLf : d2.last_flush = d0.last_flush := (e2 DeflateState.last_flush fun _ => rfl).trans (eA DeflateState.last_flush fun _ => rfl)
  have eStat : d2.status = d0.status := (e2 DeflateState.status fun _ => rfl).trans (eA DeflateState.status fun _ => rfl)
  have eBits : d2.bi_valid = d0.bi_valid := (e2 DeflateState.bi_valid fun _ => rfl).trans (eA DeflateState.bi_valid fun _ => rfl)
  have eBv : d2.bi_valid = d0.bi_valid := (e2 DeflateState.bi_valid fun _ => rfl).trans (eA DeflateState.bi_valid fun _ => rfl)
  have eMt : d2.«matches» = d0.«matches» := (e2 DeflateState.«matches» fun _ => rfl).trans (eA DeflateState.«matches» fun _ => rfl)
  have eHs : d2.hash_size = d0.hash_size := (e2 DeflateState.hash_size fun _ => rfl).trans (eA DeflateState.hash_size fun _ => rfl)
  have eGz : d2.gzhead = d0.gzhead := (e2 DeflateState.gzhead fun _ => rfl).trans (eA DeflateState.gzhead fun _ => rfl)
  have room2 : d2.strstart.toNat + d2.lookahead.toNat ≤ d2.window_size.toNat := L2.pre.range
  have water2 : d2.strstart.toNat + d2.lookahead.toNat ≤ d2.high_water.toNat := L2.water
  have wsz2 := good2.inv.wsz
  have wsHi := (slide_window_sizes good2).2
  have ssF : dF.strstart.toNat = d2.strstart.toNat + d2.lookahead.toNat := by
    change (d2.strstart + d2.lookahead).toNat = _
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have laF : dF.lookahead.toNat = 0 := rfl
  have bsF : dF.block_start.toInt = (dF.strstart.toNat : Int) := u32_toInt64_toInt _
  have insF : dF.insert = d2.lookahead := rfl
  have two : (MIN_MATCH_u - 1).toNat = 2 := rfl
  have zeroMa : (0 : UInt32) = 0 := rfl
  have shapeF : Shape dF := by
    refine ⟨?_, ?_, fun large => by rw [laF] at large; omega, by show (MIN_MATCH_u - 1).toNat ≤ 258; rw [two]; omega,
      by show (MIN_MATCH_u - 1).toNat ≤ 258; rw [two]; omega, Or.inl rfl, by rw [bsF]; exact Int.le_refl _, ?_, ?_,
      fun ne => absurd rfl ne, fun large => by change 3 ≤ (MIN_MATCH_u - 1).toNat at large; rw [two] at large; omega,
      fun _ _ _ _ => ⟨by show (MIN_MATCH_u - 1).toNat ≤ 2; decide, by show (MIN_MATCH_u - 1).toNat ≤ 2; decide⟩,
      by show d2.high_water.toNat ≤ d2.window_size.toNat; exact good2.inv.hw, ?_,
      by show -2 ≤ d2.last_flush.toInt ∧ d2.last_flush.toInt ≤ 5; rw [eLf]; exact shape0.lastFlush,
      by show d2.status = INIT_STATE ∨ d2.status = GZIP_STATE → d2.last_flush = -2 ∨ d2.last_flush = -1
         rw [eStat, eLf]; exact shape0.headerFlush,
      by show d0.wrap.toInt < 0 → d2.status = FINISH_STATE; rw [eStat]; exact shape0.trailer,
      by show d2.bi_valid.toInt ≤ 7; rw [eBv]; exact shape0.biValid,
      by show d2.pending = 0 → d2.pending_out = d2.pending_buf; rw [ePd, ePo, ePb]; exact shape0.cursor,
      by show d2.sym_next.toNat < d2.sym_end.toNat; rw [eSym, eEnd]; exact shape0.symRoom,
      by show d2.«matches».toNat ≤ 2 ∧ (d2.level ≠ 0 → d2.«matches» = 0); rw [eMt, eLv]; exact shape0.slides,
      fun large => by change 3 ≤ (MIN_MATCH_u - 1).toNat at large; rw [two] at large; omega,
      fun nz => absurd (show d2.sym_next = 0 by rw [eSym]; exact sym0) nz,
      fun ne => absurd rfl ne, fun ne => absurd rfl ne⟩
    · rw [ssF, laF]; show _ ≤ d2.window_size.toNat; omega
    · rw [insF, ssF]; omega
    · intro _; rw [bsF]
      have : (0 : Int) ≤ 258 * ((dF.sym_next.toNat / 3 : Nat) : Int) + dF.match_available.toInt := by
        have : dF.match_available.toInt = 0 := rfl
        rw [this]; omega
      omega
    · intro zero
      have z0 : d0.level = 0 := by rw [← eLv]; exact zero
      refine ⟨by rw [bsF]; omega, rfl, ?_⟩
      show d2.sym_next = 0; rw [eSym]; exact (shape0.levelZero z0).2.2
    · rw [ssF, laF]; show _ ≤ d2.high_water.toNat; omega
  -- the hash state
  have chainsF : VHeapChains v after3 dF (chainTop dF) := by
    obtain ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, H⟩ := L2.pre.chains
    refine ⟨w, p, q, wa, pa, qa, win, prev, hd, by rw [bytes3]; exact hw, by rw [words3]; exact hp,
      by rw [words3]; exact hq, ?_⟩
    have lim : dF.strstart.toNat + dF.lookahead.toNat = d2.strstart.toNat + d2.lookahead.toNat := by rw [ssF, laF]; omega
    change ViewChains v _ _ _ _ _ _ _ _ (dF.strstart.toNat + dF.lookahead.toNat)
    rw [lim]
    refine view_mono H ?_ (Nat.le_refl _)
    unfold chainTop
    rw [ssF, laF, insF]
    omega
  have hashingF : Hashing after3 dF := by
    exact hashOk after3 dF eMt rfl chainsF
  -- the symbols
  obtain ⟨⟨xs, ⟨b, a, pbuf, getB, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
  obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
  have wb : b ≠ w0 := by
    have be : b0 = b := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst be; exact blocks.wb.symm
  have getBF : after3.bytes b = some a := by
    rw [bytes3, L2.bytes w0 b (by rw [fieldsA]; exact blocks.win) wb, ← getB]
  have symbolsF : Symbols after3 dF := by
    refine ⟨⟨xs, ⟨b, a, by show d2.pending_buf = _; rw [ePb]; exact pbuf, getBF,
        ledger.keep (result := dF) eSym eLit eLt eDt⟩, fun s mem => by show s.distance ≤ d2.w_size.toNat - 262; rw [eW]; exact dist s mem⟩,
      ⟨fun k hk => by show (d2.bl_tree[k]!).fc = 0; rw [eBl]; exact clear.bl k hk,
        by show d2.opt_len = 0; rw [eOpt]; exact clear.opt, by show d2.static_len = 0; rw [eStc]; exact clear.fixed⟩, ?_⟩
    intro b1 off pout nz
    change d2.pending_out = _ at pout
    change d2.sym_next ≠ 0 at nz
    change off + d2.pending.toNat ≤ d2.lit_bufsize.toNat
    rw [ePo] at pout; rw [eSym] at nz; rw [ePd, eLit]
    exact below b1 off pout nz
  have globalsF : LibraryGlobals after3 := by
    unfold LibraryGlobals
    rw [static3, ← L2.frame.1]
    exact inv.globals
  have invF : DInv after3 r ds zF dF :=
    ⟨goodF, ⟨L2.alloc.1, L2.alloc.2⟩, globalsF, shapeF, hashingF, symbolsF⟩
  have ownedF : ∀ b, DeflateOwned ds dF b ↔ DeflateOwned ds d0 b := by
    intro b
    unfold DeflateOwned
    change b = ds ∨ d2.window = _ ∨ d2.prev = _ ∨ d2.head = _ ∨ d2.pending_buf = _ ↔ _
    rw [eWin, ePrev, eHead, ePb]
  have frameL : Frame h0 after2 (fun b => StreamRoot r b ∨ DeflateOwned ds d0 b) :=
    full_frame_weaken L2.frame (fun b o => by rcases o with o | o; exact Or.inl o; exact Or.inr ((ownedA b).1 o))
  refine ⟨after3, zF, dF, tailRun, invF, L2.shape.trans shape3,
    full_frame_trans_shape frameL (full_frame_weaken frame3
      (fun b o => by rcases o with o | o; exact Or.inl o; exact Or.inr (Or.inl o))) L2.shape,
    nalloc3.trans L2.nalloc, next3.trans L2.nextBlk, ownedF, fun hd => hd.keep eStat eSym eGz, eStat, eSym, eGz,
    fun calls => setdictEnd_callfacts d0.wrap calls eLf eSym eStat eBits⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The body of `deflateSetDictionary`** after accepted checks, with the chains read through
the view `v`; `hashOk` turns the view chains of the end state into its hash state. -/
theorem setdict_body_v {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (dict : BPtr) (len : UInt32)
    (args : CallerRange h r dict len.toNat false) (nonnull : dict ≠ .null)
    (chains0 : VHeapChains v h d (chainTop d))
    (hashOk : ∀ (heap : Heap) (dF : DeflateState), dF.«matches» = d.«matches» → dF.lookahead = 0 →
      VHeapChains v heap dF (chainTop dF) → Hashing heap dF)
    (la0 : d.lookahead = 0) (sym0 : d.sym_next = 0) :
    ∃ after zF dF, setdictBody (some r) (some (.tab ds)) dict len d h = .ok (Z_OK, after) ∧
      DInv after r ds zF dF ∧ Zlib.Deflate.Proofs.Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧ (∀ b, DeflateOwned ds dF b ↔ DeflateOwned ds d b) ∧
      (HeaderInv d → HeaderInv dF) ∧
      (dF.status = d.status ∧ dF.sym_next = d.sym_next ∧ dF.gzhead = d.gzhead ∧ (CallFacts d → CallFacts dF)) := by
  have good := inv.good
  have shape := inv.shape
  -- the dictionary bytes
  obtain ⟨ref, off, array, ptr, getArr, fit⟩ : ∃ ref off array, dict = .ref ref off ∧
      Space.get h ref = some array ∧ off + len.toNat ≤ array.size := by
    rcases args with null | ⟨⟨xs, bytes⟩, _, _⟩
    · exact absurd null nonnull
    · rcases bytes with ⟨null, _, _⟩ | ⟨ref, off, array, ptr, getArr, fit, _⟩
      · exact absurd null nonnull
      · exact ⟨ref, off, array, ptr, getArr, fit⟩
  -- the checksum
  obtain ⟨z1, h1, adlerRun, good1, eq1, args1, frame1, shape1, borrow1, byteFrame1⟩ : ∃ z1 h1,
      (if d.wrap == 1 then (do
          let a ← zrd (some r) (·.adler)
          let v ← Zlib.Adler32.adler32 a dict len
          zwr (some r) (fun z => { z with adler := v })) else pure ()) h = .ok ((), h1) ∧
      DGood h1 r ds z1 d ∧ (z1.state = z.state ∧ z1.zalloc = z.zalloc ∧ z1.zfree = z.zfree) ∧
      CallerRange h1 r dict len.toNat false ∧
      Frame h h1 (fun b => StreamRoot r b) ∧ Zlib.Deflate.Proofs.Shape h h1 ∧
      h1.libcErrorBorrow = h.libcErrorBorrow ∧ (h1.bytes = h.bytes ∧ h1.words = h.words ∧ h1.static = h.static ∧
        h1.nalloc = h.nalloc ∧ h1.nextBlk = h.nextBlk) := by
    by_cases w1 : d.wrap = 1
    · have w1B : (d.wrap == 1) = true := by simp [w1]
      obtain ⟨v, adler⟩ := adler32_ok getArr z.adler off len fit
      let z1 : ZStream := { z with adler := v }
      have zrdRun : zrd (some r) (·.adler) h = .ok (z.adler, h) := by rw [zrd_eq, good.live.hz]
      have putRun : zwr (some r) (fun z => { z with adler := v }) h = .ok ((), r.put h z1) := by
        rw [zwr_eq, good.live.hz]
      have good1 : DGood (r.put h z1) r ds z1 d := good_put good z1 rfl rfl rfl
      have borrow1 : (r.put h z1).libcErrorBorrow = h.libcErrorBorrow :=
        Zlib.Deflate.BorrowProofs.stable_zwr _ _ _ _ _ putRun
      refine ⟨z1, r.put h z1, ?_, good1, ⟨rfl, rfl, rfl⟩, ?_, stream_store_full_frame h r z1,
        shape_put good.live.hz z1, borrow1, by simp, by simp, by simp, by simp, by simp⟩
      · rw [if_pos w1B, bind_app, zrdRun]
        simp only []
        rw [bind_app, ptr, adler]
        simp only []
        exact putRun
      · have frame : ByteFrame h (r.put h z1) (fun _ => False) := ⟨by simp, fun _ _ => by simp, fun _ _ => by simp,
          fun _ _ => by simp⟩
        have := caller_range_advance (used := 0) (remaining := len.toNat) args frame (fun _ f => f.elim)
          (stream_owned_keys good good1 rfl rfl rfl rfl) (by omega) borrow1
        rwa [advance_zero] at this
    · have w1B : (d.wrap == 1) = false := by simp [w1]
      refine ⟨z, h, by rw [if_neg (by simp [w1B])]; rfl, good, ⟨rfl, rfl, rfl⟩, args, by simp [Frame],
        Zlib.Deflate.Proofs.Shape.refl h, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨bytes1, words1, static1, nalloc1, next1⟩ := byteFrame1
  -- `s->wrap = 0`
  let dW : DeflateState := { d with wrap := 0 }
  have invW : DStInv h1 ds dW := { good1.inv with blocks := good1.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, wrap_lo := (by show (-2 : Int) ≤ (0 : Int32).toInt; decide), wrap_hi := (by show (0 : Int32).toInt ≤ 2; decide) }
  obtain ⟨h2, h2def⟩ : ∃ x, x = setD h1 ds dW := ⟨_, rfl⟩
  have wrRun : wr (some (.tab ds)) (fun d => { d with wrap := 0 }) h1 = .ok ((), h2) := by
    rw [h2def, wrD_eq, good1.live.hs]
  have good2 : DGood h2 r ds z1 dW := by rw [h2def]; exact good1.setD' rfl good1.live.status invW (by trkeep)
  have chains2 : VHeapChains v h2 dW (chainTop dW) := by
    obtain ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, H⟩ := chains0
    exact ⟨w, p, q, wa, pa, qa, win, prev, hd, by rw [h2def, setD_bytes, bytes1]; exact hw,
      by rw [h2def]; simpa [setD, words1] using hp, by rw [h2def]; simpa [setD, words1] using hq, H⟩
  have shape2 : Zlib.Deflate.Proofs.Shape h h2 := by
    rw [h2def]; exact shape1.trans (shape_setD good1.live.hs dW)
  have frame2 : Frame h h2 (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    rw [h2def]
    exact full_frame_trans_shape (full_frame_weaken frame1 (fun _ o => Or.inl o))
      (full_frame_weaken (state_store_full_frame h1 ds dW) (fun _ e => Or.inr (Or.inl e))) shape1
  have borrow2 : h2.libcErrorBorrow = h.libcErrorBorrow := by rw [h2def]; exact borrow1
  have owned2 := stream_owned_keys good1 good2 rfl rfl rfl rfl
  have args2 : CallerRange h2 r dict len.toNat false := by
    have frame : ByteFrame h1 h2 (fun b => b = ds) := by rw [h2def]; exact byte_frame_setD h1 ds dW
    have := caller_range_advance (used := 0) (remaining := len.toNat) args1 frame
      (fun b e => (stream_owned_deflate good1 b).mpr (Or.inl e)) owned2 (by omega) (by rw [h2def]; rfl)
    rwa [advance_zero] at this
  have span0 := dinv_span inv
  have ssLt := d.strstart.toNat_lt
  have room0 := shape.room
  have water0 := shape.windowInit
  rw [la0] at room0 water0
  have z0N : (0 : UInt32).toNat = 0 := rfl
  rw [z0N, Nat.add_zero] at room0 water0
  have bytesH2 : ∀ w b, d.window = .ref (.blk w) 0 → b ≠ w → h2.bytes b = h.bytes b := by
    intro w b _ _; rw [h2def, setD_bytes, bytes1]
  by_cases big : len ≥ d.w_size
  · -- only the last `w_size` bytes of the dictionary are used
    have bigN : d.w_size.toNat ≤ len.toNat := UInt32.le_iff_toNat_le.mp big
    have skipN : (len - d.w_size).toNat = len.toNat - d.w_size.toNat :=
      UInt32.toNat_sub_of_le _ _ big
    have wsHi := (slide_window_sizes good).2
    -- the prepared state, with or without the hash clearing
    obtain ⟨hA, dA, prepRun, goodA, fieldsA, chainsA, laA, insA, roomA, waterA, spanA, shapeA, frameA, nallocA,
        nextA, borrowA, bytesA, staticA, bytesA_eq, dstA, roA⟩ : ∃ hA dA,
        (if d.wrap == 0 then (do
            CLEAR_HASH (some (.tab ds))
            wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 })) else pure ()) h2 =
          .ok ((), hA) ∧ DGood hA r ds z1 dA ∧ DictFields { d with wrap := 0 } dA ∧ VHeapChains v hA dA (chainTop dA) ∧
        dA.lookahead = 0 ∧ dA.insert.toNat ≤ dA.strstart.toNat ∧ dA.strstart.toNat ≤ dA.window_size.toNat ∧
        dA.strstart.toNat ≤ dA.high_water.toNat ∧ (dA.strstart.toNat : Int) - dA.block_start.toInt ≤ 2 ^ 40 ∧
        Zlib.Deflate.Proofs.Shape h hA ∧ Frame h hA (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
        hA.nalloc = h.nalloc ∧ hA.nextBlk = h.nextBlk ∧ hA.libcErrorBorrow = h.libcErrorBorrow ∧
        (∀ w b, d.window = .ref (.blk w) 0 → b ≠ w → hA.bytes b = h.bytes b) ∧ hA.static = h.static ∧
        hA.bytes = h2.bytes ∧ (∀ i, i ≠ ds → hA.dstates i = h2.dstates i) ∧ hA.ro = h2.ro := by
      by_cases w0 : d.wrap = 0
      · have w0B : (d.wrap == 0) = true := by simp [w0]
        obtain ⟨w, p, q, b, blocks⟩ := good2.inv.blocks
        obtain ⟨qa, getQ, sizeQ⟩ := blocks.qa
        have hashLo : 1 ≤ dW.hash_size.toNat := by rw [good2.inv.hsize]; exact Nat.one_le_two_pow
        have clearRun := clearHash_run good2.live.hs blocks.head getQ hashLo (by omega)
        let cleared := setW h2 q (clearHead qa dW.hash_size.toNat)
        have goodW : DGood cleared r ds z1 dW := good2.words_set q _ qa getQ (size_clearHead _ _)
        let dC : DeflateState := { dW with slid := 0 }
        have invC : DStInv cleared ds dC := { goodW.inv with blocks := goodW.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
        have goodC : DGood (setD cleared ds dC) r ds z1 dC := goodW.setD' rfl goodW.live.status invC (by trkeep)
        let dA : DeflateState := { dC with strstart := 0, block_start := 0, insert := 0 }
        have invA : DStInv (setD cleared ds dC) ds dA := { goodC.inv with blocks := goodC.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
        have goodA : DGood (setD (setD cleared ds dC) ds dA) r ds z1 dA := goodC.setD' rfl goodC.live.status invA (by trkeep)
        have wrA : wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 })
            (setD cleared ds dC) = .ok ((), setD (setD cleared ds dC) ds dA) := by
          rw [wrD_eq, setD_dstates_same]
        have shapeW : Zlib.Deflate.Proofs.Shape h2 cleared := shape_setW getQ _
        have shapeC := shapeW.trans (shape_setD (by simpa [cleared] using good2.live.hs) dC)
        have shapeAll := shapeC.trans (shape_setD (setD_dstates_same cleared ds dC) dA)
        have frameAll : Frame h2 (setD (setD cleared ds dC) ds dA) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
          have fW : Frame h2 cleared (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
            full_frame_weaken (word_store_full_frame h2 q _) (fun b e => by
              subst e; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl blocks.head)))))
          have fC : Frame cleared (setD cleared ds dC) (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
            full_frame_weaken (state_store_full_frame cleared ds dC) (fun b e => Or.inr (Or.inl e))
          have fA := full_frame_weaken (state_store_full_frame (setD cleared ds dC) ds dA)
            (fun b e => Or.inr (Or.inl e) : ∀ b, b = ds → StreamRoot r b ∨ DeflateOwned ds d b)
          exact full_frame_trans_shape (full_frame_trans_shape fW fC shapeW) fA shapeC
        refine ⟨setD (setD cleared ds dC) ds dA, dA, ?_, goodA, by unfold DictFields; rfl, ?_, la0,
          by show (0 : UInt32).toNat ≤ (0 : UInt32).toNat; exact Nat.le_refl _,
          by show (0 : UInt32).toNat ≤ d.window_size.toNat; exact Nat.zero_le _,
          by show (0 : UInt32).toNat ≤ d.high_water.toNat; exact Nat.zero_le _,
          by show ((0 : UInt32).toNat : Int) - (0 : Int64).toInt ≤ 2 ^ 40; decide, shape2.trans shapeAll, full_frame_trans_shape frame2 frameAll shape2,
          by simp [cleared, setW, h2def, nalloc1], by simp [cleared, setW, h2def, next1], ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [if_pos w0B, bind_app, clearRun]
          simp only []
          exact wrA
        · obtain ⟨w', p', q', wa', pa', qa', win', prev', hd', hw', hp', hq', _⟩ := chains2
          have qEq : q' = q := by
            have := hd'.symm.trans blocks.head; simpa using this
          subst qEq
          refine ⟨w', p', q', wa', pa', clearHead qa dW.hash_size.toNat, win', prev', hd', ?_, ?_, ?_, ?_⟩
          · simpa [cleared, setW] using hw'
          · have pEq : p' = p := by have := prev'.symm.trans blocks.prev; simpa using this
            have pq : p' ≠ q' := by rw [pEq]; exact blocks.pq
            simpa [cleared, setW, upd_ne _ _ _ _ pq] using hp'
          · simp [cleared, setW]
          · apply view_empty (by show d.w_size.toNat ≤ 65536; have := (slide_window_sizes good).2; omega)
            intro k hk
            have zero := clear_head_zero qa dW.hash_size.toNat (by omega) (by omega) k hk
            simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]
        · subst h2def; exact borrow1
        · intro _ _ _ _; subst h2def; show h1.bytes _ = _; rw [bytes1]
        · subst h2def; exact static1
        · rfl
        · intro i ne; simp [cleared, setW, setD, upd_ne _ _ _ _ ne]
        · rfl
      · have w0B : (d.wrap == 0) = false := by simp [w0]
        refine ⟨h2, dW, by rw [if_neg (by simp [w0B])]; rfl, good2, by unfold DictFields; rfl, chains2, la0,
          shape.insert, room0, water0, span0, shape2, frame2, by rw [h2def]; exact nalloc1, by rw [h2def]; exact next1,
          borrow2, bytesH2, by rw [h2def]; exact static1, rfl, fun _ _ => rfl, rfl⟩
    -- the pointer to the last `w_size` bytes
    have argsA : CallerRange hA r dict len.toNat false := by
      have frame : ByteFrame h2 hA (fun b => b = ds) :=
        ⟨by rw [staticA, h2def]; exact static1.symm, fun i _ => by rw [bytesA_eq], fun i ne => dstA i ne,
          fun i _ => by rw [roA]⟩
      have := caller_range_advance (used := 0) (remaining := len.toNat) args2 frame
        (fun b e => (stream_owned_deflate good2 b).mpr (Or.inl e)) (stream_owned_keys good2 goodA
          (by rw [fieldsA]) (by rw [fieldsA]) (by rw [fieldsA]) (by rw [fieldsA])) (by omega)
        (by rw [borrowA, borrow2])
      rwa [advance_zero] at this
    obtain ⟨arrayA, getA, fitA⟩ : ∃ a, Space.get hA ref = some a ∧ off + len.toNat ≤ a.size := by
      rcases argsA with null | ⟨⟨xs, bytes⟩, _, _⟩
      · exact absurd null nonnull
      · rcases bytes with ⟨null, _, _⟩ | ⟨ref', off', a', ptr', get', fit', _⟩
        · exact absurd null nonnull
        · rw [ptr] at ptr'
          cases ptr'
          exact ⟨a', get', fit'⟩
    have paddRun : padd dict (len - d.w_size).toNat hA = .ok (.ref ref (off + (len - d.w_size).toNat), hA) := by
      rw [ptr]
      exact Ptr.add_nat_ok (h := hA) (r := ref) (a := arrayA) (off := off) (n := (len - d.w_size).toNat) getA
        (by omega)
    have argsT : CallerRange hA r (.ref ref (off + (len - d.w_size).toNat)) d.w_size.toNat false := by
      have := caller_range_advance (used := (len - d.w_size).toNat) (remaining := d.w_size.toNat) argsA
        (ByteFrame.refl hA (fun _ => False)) (fun _ (f : False) => f.elim) (fun _ => Iff.rfl) (by omega) rfl
      rw [ptr] at this
      exact this
    obtain ⟨after, zF, dF, tailRun, invF, shapeF, frameF, nallocF, nextF, ownedF, headerF, keptF⟩ :=
      setdict_tail_v (X0 := 2 ^ 40) inv goodA fieldsA chainsA hashOk laA insA roomA waterA spanA
        (by omega) argsT (fun _ => by simp) ⟨eq1.2.1.trans inv.alloc.1, eq1.2.2.trans inv.alloc.2⟩ shapeA frameA
        nallocA nextA borrowA bytesA staticA sym0
    refine ⟨after, zF, dF, ?_, invF, shapeF, frameF, nallocF, nextF, ownedF, headerF, keptF⟩
    rw [setdict_body_seq, bind_app, adlerRun]
    simp only []
    rw [bind_app, wrRun]
    simp only []
    rw [if_pos big, bind_app, prepRun]
    simp only []
    rw [bind_app, paddRun]
    exact tailRun
  · -- the dictionary fits the window: no hash clearing, the whole dictionary
    obtain ⟨after, zF, dF, tailRun, invF, shapeF, frameF, nallocF, nextF, ownedF, headerF, keptF⟩ :=
      setdict_tail_v (X0 := 2 ^ 40) (dA := dW) inv good2 (by unfold DictFields; rfl) chains2 hashOk la0
        shape.insert room0 water0 span0 (by have := len.toNat_lt; omega) args2
        (fun _ => nonnull) ⟨eq1.2.1.trans inv.alloc.1, eq1.2.2.trans inv.alloc.2⟩ shape2 frame2
        (by rw [h2def]; exact nalloc1) (by rw [h2def]; exact next1) borrow2 bytesH2
        (by rw [h2def]; exact static1) sym0
    refine ⟨after, zF, dF, ?_, invF, shapeF, frameF, nallocF, nextF, ownedF, headerF, keptF⟩
    rw [setdict_body_seq, bind_app, adlerRun]
    simp only []
    rw [bind_app, wrRun]
    simp only []
    rw [if_neg big]
    exact tailRun

end Zlib.Deflate.Universal
