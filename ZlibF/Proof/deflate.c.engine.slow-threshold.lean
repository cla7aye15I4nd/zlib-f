import ZlibF.Proof.«deflate.c.engine.slow-defer»

/-! # A complete slow call at the first matching threshold -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem slow_resume_short_body {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (input : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat + d.lookahead.toNat + 258) d.window_size.toNat ≤ d.high_water.toNat)
    (short : d.lookahead < MIN_LOOKAHEAD_u) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h =
      .ok ({ st with ret := some need_more }, h) := by
  have fill := fill_window_resume_no_input good input noSlide range padded
  rw [slow_body_source]
  simp only [bind_app, rdD_eq, good.live.hs, short, if_true, fill, Z_NO_FLUSH,
    show ((0 : Int32) == 0) = true from rfl, Bool.true_and]
  rfl

set_option maxHeartbeats 1000000 in
/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
With exactly MIN_LOOKAHEAD bytes in the first window and no further input,
the real strategy searches, defers one byte, resumes fill_window and
returns need_more. This is a whole strategy call, including its loop.
The public wrapper and block-emission paths are separate obligations. -/
theorem slow_threshold_call {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat 0 (d.strstart.toNat + d.lookahead.toNat))
    (start : d.strstart = 0) (lookahead : d.lookahead = 262) (ws : d.w_size = 32768)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat + d.lookahead.toNat + 258) d.window_size.toNat ≤ d.high_water.toNat)
    (input : z.avail_in = 0) (length : d.match_length = 2) (available : d.match_available = 0)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ after result,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      DGood after r ds z result ∧ HeapChains after result 1 ∧
      result.strstart = 1 ∧ result.lookahead = 261 ∧ result.match_available = 1 := by
  obtain ⟨key, pos, len, after, first, goodA, chainsA, ss, la, rangeA⟩ :=
    slow_body_first_defer good env chains (by simp [start]) range
      (by rw [lookahead]; decide) length available form Z_NO_FLUSH {}
  let result := deferOne (matchState (lazyPrepare { d with ins_h := key }) pos len)
  let st : LoopS := { hash_head := (wfn qa key.toNat).toUInt32, bflush := false }
  have ssA : result.strstart = 1 := by
    apply UInt32.toNat_inj.mp
    exact ss.trans (by rw [start]; rfl)
  have laA : result.lookahead = 261 := by
    apply UInt32.toNat_inj.mp
    exact la.trans (by rw [lookahead]; rfl)
  have noSlide : ¬ result.strstart ≥ result.w_size + (result.w_size - MIN_LOOKAHEAD_u) := by
    change ¬ result.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    rw [ssA, ws]
    decide
  have paddedA : min (result.strstart.toNat + result.lookahead.toNat + 258)
      result.window_size.toNat ≤ result.high_water.toNat := by
    change min (result.strstart.toNat + result.lookahead.toNat + 258)
      d.window_size.toNat ≤ d.high_water.toNat
    have endpoint : result.strstart.toNat + result.lookahead.toNat =
        d.strstart.toNat + d.lookahead.toNat := by
      rw [ssA, laA, start, lookahead]
      rfl
    rw [endpoint]
    exact padded
  have second := slow_resume_short_body goodA input noSlide rangeA paddedA
    (by rw [laA]; decide) st
  have loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h =
      .ok ({ st with ret := some need_more }, after) := by
    unfold cwhile
    change cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
      (18446744073709551613 + 3) {} h = _
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH {} >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
        (18446744073709551613 + 2) x) h = _
    rw [bind_app, first]
    simp only []
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st >>= fun x =>
      cwhile.go forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH)
        (18446744073709551613 + 1) x) after = _
    rw [bind_app, second]
    simp only []
    rw [cwhile.go]
    rfl
  refine ⟨after, result, ?_, goodA, ?_, ssA, laA, rfl⟩
  · unfold deflate_slow
    rw [bind_app, loop]
    rfl
  · have top : d.strstart.toNat + 1 = 1 := by rw [start]; rfl
    rwa [top] at chainsA

theorem slow_call_prepend_fill {h after : Heap} {ds : Nat} {d df : DeflateState}
    (state : h.dstates ds = some d) (empty : d.lookahead = 0)
    (fill : fill_window (some (.tab ds)) h = .ok ((), after))
    (result : after.dstates ds = some df) (ready : ¬ df.lookahead < MIN_LOOKAHEAD_u)
    (flush : Int32) :
    deflate_slow (some (.tab ds)) flush h = deflate_slow (some (.tab ds)) flush after := by
  have body : deflate_slow_body (some (.tab ds)) flush {} h =
      deflate_slow_body (some (.tab ds)) flush {} after := by
    rw [slow_body_source]
    simp only [bind_app, rdD_eq, state, empty,
      show (0 : UInt32) < MIN_LOOKAHEAD_u from by decide, if_true, fill,
      result, ready, if_false, decide_false, Bool.false_and, Bool.false_eq_true,
      show ¬ (df.lookahead == 0) = true from by
        simp only [beq_iff_eq]
        intro zero
        apply ready
        rw [zero]
        decide]
  have loop : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h =
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} after := by
    unfold cwhile
    change cwhile.go forever (deflate_slow_body (some (.tab ds)) flush)
        (18446744073709551615 + 1) {} h =
      cwhile.go forever (deflate_slow_body (some (.tab ds)) flush)
        (18446744073709551615 + 1) {} after
    rw [cwhile.go]
    change (deflate_slow_body (some (.tab ds)) flush {} >>= fun x =>
        cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) 18446744073709551615 x) h =
      (deflate_slow_body (some (.tab ds)) flush {} >>= fun x =>
        cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) 18446744073709551615 x) after
    simp only [bind_app, body]
  unfold deflate_slow
  simp only [bind_app, loop]

set_option maxHeartbeats 1000000 in
/-- A complete first slow NO_FLUSH call with 262 caller bytes. The actual
first fill, search, deferred-byte step, resumed fill and loop return are
composed here. Input contents and the fresh predecessor bytes are arbitrary.
This supporting path does not restrict the public deflate goal. -/
theorem slow_first_threshold {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d 0)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (writable : h.ro w = false) (size : wa.size = 65536)
    (ss : d.strstart = 0) (la : d.lookahead = 0) (ins : d.insert = 0) (hw : d.high_water = 0)
    (ws : d.w_size = 32768) (wsz : d.window_size = 65536) (wrap : d.wrap = 1)
    (length : d.match_length = 2) (available : d.match_available = 0)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (count : z.avail_in = 262)
    (separate : BRef.blk w ≠ ref ∨ (rbLen z.avail_in 65536).toNat ≤ io ∨
      io + (rbLen z.avail_in 65536).toNat ≤ 0) :
    let n := rbLen z.avail_in 65536
    let z' := readStream z n ref io
      (ZlibF.Spec.Public.adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    ∃ after result,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (need_more, after) ∧
      DGood after r ds z' result ∧ HeapChains after result 1 ∧
      result.strstart = 1 ∧ result.lookahead = 261 ∧ result.match_available = 1 := by
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let padded := fillRange copied n.toNat (firstPadding n).toNat 0
  let filled := firstFillHeap h r ds w z d ref io ia wa
  let df := firstFillState d n copied
  have nonzero : z.avail_in ≠ 0 := by rw [count]; decide
  have nval : n = 262 := by change rbLen z.avail_in 65536 = 262; rw [count]; decide
  obtain ⟨fill, goodF, chainsF, rangeF, formF⟩ := fill_window_first_complete good chains win get
    writable size ss la ins hw ws wsz wrap pointer input inputBound nonzero separate
  have keep : df.strstart = d.strstart ∧ df.lookahead = n ∧ df.w_size = d.w_size ∧
      df.window_size = d.window_size ∧ df.window = d.window ∧
      df.match_length = d.match_length ∧ df.match_available = d.match_available := by
    unfold df firstFillState primeState
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨wb, pb, qb, bytes, prev, head, env, H⟩ := heap_chains_environment goodF chainsF
  have wid : wb = w := by
    have eq := env.win.symm.trans (keep.2.2.2.2.1.trans win)
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using eq
  subst wb
  have array : bytes = padded := by
    have actual : filled.bytes w = some padded := by
      simp [filled, firstFillHeap, padded, copied, n]
    exact Option.some.inj (env.wbytes.symm.trans actual)
  have start : df.strstart = 0 := keep.1.trans ss
  have look : df.lookahead = 262 := keep.2.1.trans nval
  have form : InsHForm df.hash_shift df.hash_mask (bfn bytes) df.strstart.toNat df.ins_h := by
    rw [array, start]
    exact formF (by change n ≥ 3; rw [nval]; decide)
  have padding : min (df.strstart.toNat + df.lookahead.toNat + 258)
      df.window_size.toNat ≤ df.high_water.toNat :=
    first_fill_padding ss wsz (by rw [nval]; decide)
  have inputF : (readStream z n ref io
      (ZlibF.Spec.Public.adlerValue z.adler ((ia.toList.drop io).take n.toNat))).avail_in = 0 := by
    change z.avail_in - n = 0
    rw [count, nval]
    decide
  obtain ⟨after, result, run, goodA, chainsA, startA, lookA, availA⟩ :=
    slow_threshold_call goodF env H start look (keep.2.2.1.trans ws) rangeF padding inputF
      (keep.2.2.2.2.2.1.trans length) (keep.2.2.2.2.2.2.trans available) form
  refine ⟨after, result, ?_, goodA, chainsA, startA, lookA, availA⟩
  rw [slow_call_prepend_fill good.live.hs la fill goodF.live.hs
    (by rw [look]; decide) Z_NO_FLUSH]
  exact run

end Zlib.Deflate.Engine.Proofs
