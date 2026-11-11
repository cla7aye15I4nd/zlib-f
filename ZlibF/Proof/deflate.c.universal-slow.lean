import ZlibF.Proof.«deflate.c.universal-strategy-specs»
import ZlibF.Proof.«deflate.c.engine.short-match-frontier-loop»
import ZlibF.Proof.«deflate.c.borrow-stable-strategies»

/-!
# deflate.c, universal engine: `deflate_slow`

Batch B of the deflate skeleton. `deflate_slow` (levels 4 to 9, strategies other than
`Z_HUFFMAN_ONLY` and `Z_RLE`) looks one position ahead: the match found at `strstart - 1`
(`prev_length`, `prev_match`) is emitted only if the match at `strstart` is not longer; otherwise
the byte at `strstart - 1` is emitted as a literal (`match_available`). The lazy state between
iterations is part of `DInv` (`Shape.available`, `Shape.pendingMatch`, `Shape.blockSpan`).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The levels and strategies `deflate_slow` serves. -/
def SlowKind (d : DeflateState) : Prop :=
  4 ≤ d.level.toInt ∧ d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3

theorem slow_kind_keep : ∀ d d' : DeflateState, d'.strategy = d.strategy → d'.level = d.level →
    SlowKind d → SlowKind d' := by
  intro d d' es el k
  unfold SlowKind at *
  rw [es, el]; exact k

open Zlib.Deflate.BorrowProofs in
theorem stable_slowSearch (ds : Nat) : C.LibcBorrow.StableM (slowSearch (some (.tab ds))) := by
  unfold slowSearch slowFind
  repeat' strategy_borrow_step

/-- What the search of `deflate_slow` leaves. -/
structure SlowOut (h h2 : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d d2 : DeflateState) : Prop where
  good : DGood h2 r ds z d2
  update : EngineUpdate d d2
  strstart : d2.strstart = d.strstart
  lookahead : d2.lookahead = d.lookahead
  insert : d2.insert = d.insert
  available : d2.match_available = d.match_available
  prevLength : d2.prev_length = d.match_length
  prevMatch : d2.prev_match = d.match_start
  bytes : h2.bytes = h.bytes
  frame : ByteFrame h h2 (fun i => i = ds)
  borrow : h2.libcErrorBorrow = h.libcErrorBorrow
  chains : HeapChains h2 d2 (if 3 ≤ d.lookahead.toNat then d.strstart.toNat + 1 else chainTop d)
  form : 3 ≤ d.lookahead.toNat → ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
    InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d2.ins_h
  matchShape : d2.match_length.toNat ≤ 258
  matchLook : d2.match_length.toNat ≤ d.lookahead.toNat ∨ d2.match_length.toNat = 2
  matched : 3 ≤ d2.match_length.toNat → d.match_length.toNat < d2.match_length.toNat →
    ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
      GoodMatch wa d.strstart.toNat d.w_size.toNat d2.match_start.toNat d2.match_length.toNat

set_option maxHeartbeats 2000000 in
/-- **The search of `deflate_slow`**: insertion at `strstart`, the lazy fields, the conditional
`longest_match` and the short-match filter. -/
theorem slow_search_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (head : Head SlowKind h r ds z d) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ hh h2 d2, slowSearch (some (.tab ds)) h = .ok (hh, h2) ∧ SlowOut h h2 r ds z d d2 := by
  have inv := head.inv
  have good := inv.good
  have shape := inv.shape
  obtain ⟨_, s2, s3⟩ := head.kind
  by_cases ready : 3 ≤ d.lookahead.toNat
  · obtain ⟨w, p, q, wa, pa, qa, env, H⟩ := heap_chains_environment good (inv.chains head.level)
    obtain ⟨w0, wa0, win0, get0, form⟩ := inv.hashing.rolling s2 s3 ready
    have wid : w0 = w := by simpa only [env.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
    subst w0
    have aid : wa0 = wa := Option.some.inj (get0.symm.trans env.wbytes)
    subst wa0
    obtain ⟨key, after, pos, len, run, goodA, chainsA, lenBound, lenLook, evidence, bytesA, nextForm, frameA⟩ :=
      slow_search_room_storage good env H (by have := chainTop_le d; omega) shape.room ready room
        shape.matchLength form
    have borrowA : after.libcErrorBorrow = h.libcErrorBorrow := stable_slowSearch ds h _ after run
    refine ⟨_, after, _, run, ⟨goodA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, bytesA, frameA, borrowA,
      by rw [if_pos ready]; exact chainsA, fun _ => ⟨w, wa, env.win, env.wbytes, nextForm⟩, lenBound,
      Or.inl lenLook, fun large longer => ⟨w, wa, env.win, env.wbytes, evidence large longer⟩⟩⟩
  · obtain ⟨run, goodA, chainsA, frameA⟩ := slow_search_fewer_three good (inv.chains head.level) (by omega)
    refine ⟨0, _, lazyPrepare d, run, ⟨goodA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, frameA, rfl,
      by rw [if_neg ready]; exact chainsA, fun r3 => absurd r3 ready, by show (2 : UInt32).toNat ≤ 258; decide,
      Or.inr rfl, fun (large : 3 ≤ (2 : UInt32).toNat) => absurd large (by decide)⟩⟩


/-! ## The decision -/

/-- The literal at `strstart - 1` that a match did not replace. -/
def slowPending (s : DeflateStatePtr) (st : LoopS) (hash_head : UInt32) (d : DeflateState) : M LoopS := do
  let c ← index8 d.window (d.strstart - 1).toNat
  let bflush ← tally_lit s c
  if bflush then FLUSH_BLOCK_ONLY s 0
  wr s (fun d => { d with strstart := d.strstart + 1, lookahead := d.lookahead - 1 })
  if (← zrd d.strm (·.avail_out)) == 0 then return { st with hash_head, bflush, ret := some need_more }
  return { st with hash_head, bflush }

theorem slow_decision_source (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    slowDecision s flush st hash_head = (do
      let d ← ldDeflateState s
      if d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length then
        let bflush ← tally_dist s (d.strstart - 1 - d.prev_match) (d.prev_length - MIN_MATCH_u)
        let hh ← slowMatchAdvance s (d.strstart + d.lookahead - MIN_MATCH_u) hash_head
        lazyTail s st hh bflush
      else if d.match_available != 0 then slowPending s st hash_head d
      else
        wr s (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 1 })
        return { st with hash_head, bflush := false }) := by
  unfold slowDecision slowPending lazyTail
  simp only [Zlib.Deflate.Engine.Proofs.M_bind_assoc, Zlib.Deflate.Engine.Proofs.M_pure_bind, fill_ite_bind]
  rfl


/-- A state reached from the search by engine-field writes keeps the invariant once its shape and
hash state are shown; the caller ranges are kept. -/
theorem engine_after_search {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d2 d3 : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : SlowOut h h2 r ds z d d2)
    (update : EngineUpdate d2 d3) (shape : Shape d3) (hashing : Hashing (setD h2 ds d3) d3) :
    DInv (setD h2 ds d3) r ds z d3 ∧ StreamBuffers (setD h2 ds d3) r := by
  have good := engine_update_good out.good update
  have upd := out.update
  refine ⟨⟨good, inv.alloc, by unfold LibraryGlobals; rw [show (setD h2 ds d3).static = h.static from out.frame.static]; exact inv.globals,
    shape, hashing, ?_⟩, ?_⟩
  · obtain ⟨⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
    rw [update, upd]
    exact ⟨⟨xs, ⟨b, a, pbuf, by rw [setD_bytes, out.bytes]; exact get, ledger.keep rfl rfl rfl rfl⟩, dist⟩,
      ⟨clear.bl, clear.opt, clear.fixed⟩, below⟩
  · obtain ⟨win, prev, hd, pb⟩ : d3.window = d.window ∧ d3.prev = d.prev ∧ d3.head = d.head ∧
        d3.pending_buf = d.pending_buf := by rw [update, upd]; exact ⟨rfl, rfl, rfl, rfl⟩
    exact stream_buffers_private_read inv.good.live.hz good.live.hz buffers
      (out.frame.trans (byte_frame_setD h2 ds d3))
      (fun i mine => (stream_owned_deflate inv.good i).mpr (Or.inl mine))
      (stream_owned_keys inv.good good win prev hd pb) (stream_accounting_self z) out.borrow

/-- The state after `match_available = 1; strstart++; lookahead--`. -/
def markState (d2 : DeflateState) : DeflateState :=
  { d2 with match_available := 1, strstart := d2.strstart + 1, lookahead := d2.lookahead - 1 }

set_option maxHeartbeats 4000000 in
/-- **No match is emitted and no literal is pending**: the byte at `strstart` becomes the pending
literal. -/
theorem slow_mark {h h2 : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d d2 : DeflateState}
    (head : Head SlowKind h r ds z d) (look : 1 ≤ d.lookahead.toNat) (out : SlowOut h h2 r ds z d d2)
    (noMatch : ¬ (3 ≤ d2.prev_length.toNat ∧ d2.match_length.toNat ≤ d2.prev_length.toNat))
    (idle : d2.match_available = 0) :
    wr (some (.tab ds)) (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 1 }) h2 =
        .ok ((), setD h2 ds (markState d2)) ∧
      DInv (setD h2 ds (markState d2)) r ds z (markState d2) ∧ StreamBuffers (setD h2 ds (markState d2)) r := by
  have inv := head.inv
  have shape := inv.shape
  have upd := out.update
  refine ⟨by rw [wrD_eq, out.good.live.hs]; rfl, ?_⟩
  have ssLt := d.strstart.toNat_lt
  have room := shape.room
  have wsz := inv.good.inv.wsz
  have wsHi := (slide_window_sizes inv.good).2
  have eSs := out.strstart
  have eLa := out.lookahead
  have eIns := out.insert
  have ss3 : (markState d2).strstart.toNat = d.strstart.toNat + 1 := by
    show (d2.strstart + 1).toNat = _; rw [eSs, UInt32.toNat_add]; simp; omega
  have la3 : (markState d2).lookahead.toNat = d.lookahead.toNat - 1 := by
    show (d2.lookahead - 1).toNat = _; rw [eLa]
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using look))
  have ePl : d2.prev_length = d.match_length := out.prevLength
  have eMa : d2.match_available = d.match_available := out.available
  have level4 : 4 ≤ d.level.toInt := head.kind.1
  have dist : 3 ≤ d2.match_length.toNat → 1 ≤ ((markState d2).strstart - 1 - (markState d2).match_start).toNat ∧
      ((markState d2).strstart - 1 - (markState d2).match_start).toNat ≤ (markState d2).w_size.toNat - 262 ∧
      d2.match_length.toNat ≤ (markState d2).lookahead.toNat + 1 := by
    intro large
    have longer : d.match_length.toNat < d2.match_length.toNat := by
      rw [ePl] at noMatch; omega
    obtain ⟨w, wa, win, get, good⟩ := out.matched large longer
    obtain ⟨lt, far, _, _⟩ := good
    have back : (markState d2).strstart - 1 = d2.strstart := by
      show d2.strstart + 1 - 1 = d2.strstart; simp
    rw [back, eSs]
    have ws2 : (markState d2).w_size = d.w_size := by show d2.w_size = d.w_size; rw [upd]
    rw [ws2, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by show d2.match_start.toNat ≤ _; omega))]
    have lk : d2.match_length.toNat ≤ d.lookahead.toNat := by
      rcases out.matchLook with l | two
      · exact l
      · omega
    refine ⟨by show 1 ≤ d.strstart.toNat - d2.match_start.toNat; omega,
      by show d.strstart.toNat - d2.match_start.toNat ≤ _; omega, by rw [la3]; omega⟩
  have shapeA : Shape (markState d2) := by
    refine ⟨?_, ?_, ?_, ?_, out.matchShape, Or.inr rfl, ?_, ?_, ?_, ?_, dist, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ss3, la3]; show _ ≤ d2.window_size.toNat; rw [show d2.window_size = d.window_size by rw [upd]]; omega
    · rw [ss3]; show d2.insert.toNat ≤ _; rw [eIns]; have := shape.insert; omega
    · intro large; rw [la3] at large; show d2.insert = 0; rw [eIns]; exact shape.insertDone (by omega)
    · show d2.prev_length.toNat ≤ 258; rw [ePl]; exact shape.matchLength
    · show d2.block_start.toInt ≤ _; rw [show d2.block_start = d.block_start by rw [upd], ss3]
      have := shape.blockStart; omega
    · intro levelNe
      show ((markState d2).strstart.toNat : Int) - d2.block_start.toInt ≤ 258 * (d2.sym_next.toNat / 3 : Nat) +
        (1 : Int32).toInt
      rw [ss3, show d2.block_start = d.block_start by rw [upd], show d2.sym_next = d.sym_next by rw [upd]]
      have span := shape.blockSpan head.level
      rw [← eMa, idle] at span
      have z0 : (0 : Int32).toInt = 0 := rfl
      have o1 : (1 : Int32).toInt = 1 := rfl
      rw [z0] at span; rw [o1]; push_cast; omega
    · intro zero; change d2.level = 0 at zero; rw [show d2.level = d.level by rw [upd]] at zero; exact absurd zero head.level
    · intro _; rw [ss3]; omega
    · intro lo hi
      exfalso
      have e : (markState d2).level = d.level := by show d2.level = d.level; rw [upd]
      rw [e] at hi; omega
    · show d2.high_water.toNat ≤ d2.window_size.toNat
      rw [show d2.high_water = d.high_water by rw [upd], show d2.window_size = d.window_size by rw [upd]]
      exact shape.highWater
    · rw [ss3, la3]; show _ ≤ d2.high_water.toNat; rw [show d2.high_water = d.high_water by rw [upd]]
      have := shape.windowInit; omega
    · show -2 ≤ d2.last_flush.toInt ∧ d2.last_flush.toInt ≤ 5; rw [show d2.last_flush = d.last_flush by rw [upd]]; exact shape.lastFlush
    · show d2.status = INIT_STATE ∨ d2.status = GZIP_STATE → d2.last_flush = -2 ∨ d2.last_flush = -1
      rw [show d2.status = d.status by rw [upd], show d2.last_flush = d.last_flush by rw [upd]]; exact shape.headerFlush
    · show d2.wrap.toInt < 0 → d2.status = FINISH_STATE
      rw [show d2.wrap = d.wrap by rw [upd], show d2.status = d.status by rw [upd]]; exact shape.trailer
    · show d2.bi_valid.toInt ≤ 7; rw [show d2.bi_valid = d.bi_valid by rw [upd]]; exact shape.biValid
    · show d2.pending = 0 → d2.pending_out = d2.pending_buf
      rw [show d2.pending = d.pending by rw [upd], show d2.pending_out = d.pending_out by rw [upd],
        show d2.pending_buf = d.pending_buf by rw [upd]]; exact shape.cursor
    · show d2.sym_next.toNat < d2.sym_end.toNat
      rw [show d2.sym_next = d.sym_next by rw [upd], show d2.sym_end = d.sym_end by rw [upd]]; exact shape.symRoom
    · show d2.«matches».toNat ≤ 2 ∧ (d2.level ≠ 0 → d2.«matches» = 0)
      rw [show d2.«matches» = d.«matches» by rw [upd], show d2.level = d.level by rw [upd]]; exact shape.slides
  have hashingA : Hashing (setD h2 ds (markState d2)) (markState d2) := by
    have chains := out.chains
    refine ⟨fun _ => ?_, fun one => ?_, fun _ _ large => ?_⟩
    · obtain ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, H⟩ := chains
      refine ⟨w, p, q, wa, pa, qa, win, prev, hd, hw, hp, hq, ?_⟩
      apply chains_mono H _ (by show _ ≤ (markState d2).strstart.toNat + (markState d2).lookahead.toNat; rw [ss3, la3, eSs, eLa]; omega)
      change _ ≤ min ((markState d2).strstart.toNat - d2.insert.toNat)
        ((markState d2).strstart.toNat + (markState d2).lookahead.toNat - 2)
      rw [ss3, la3, eIns]
      by_cases ready : 3 ≤ d.lookahead.toNat
      · rw [if_pos ready]
        have z0 : d.insert.toNat = 0 := by rw [shape.insertDone ready]; rfl
        omega
      · rw [if_neg ready]; unfold chainTop; omega
    · have zero := shape.slides.2 head.level
      change d2.«matches» = 1 at one
      rw [show d2.«matches» = d.«matches» by rw [upd], zero] at one; cases one
    · change 3 ≤ (markState d2).lookahead.toNat at large
      rw [la3] at large
      obtain ⟨w, wa, win, get, form⟩ := out.form (by omega)
      refine ⟨w, wa, by show d2.window = _; rw [show d2.window = d.window by rw [upd]]; exact win,
        by rw [setD_bytes, out.bytes]; exact get, ?_⟩
      show InsHForm d2.hash_shift d2.hash_mask (bfn wa) (markState d2).strstart.toNat d2.ins_h
      rw [ss3, show d2.hash_shift = d.hash_shift by rw [upd], show d2.hash_mask = d.hash_mask by rw [upd]]
      exact form
  exact engine_after_search inv head.buffers out rfl shapeA hashingA

end Zlib.Deflate.Universal
