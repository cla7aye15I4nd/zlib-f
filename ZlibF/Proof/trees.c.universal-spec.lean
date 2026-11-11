import ZlibF.Proof.«trees.c.universal-flush»
import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-output-base»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-arrays»
import ZlibF.Proof.«deflate.c.engine.flush-storage-frame»

/-!
# trees.c: `FLUSH_BLOCK_ONLY` from the deflate invariant

Batch C of the deflate skeleton. `flush_block_dinv` reads the premises of `flush_block_only_safe`
from `DInv` (engine invariants, recorded symbols with their frequencies, cleared costs, the bit
bound, the pending cursor, the window shape and block span) and from the entry premises of a
block flush (`StreamBuffers`, a non-`NULL` output pointer, a positive level, nothing pending). The dynamic overlay
room is a premise (`DynamicOverlay`); for `memLevel ≥ 5` it is `dynamic_overlay_large`
(`flush_block_dinv_large`).
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The tree invariant of the live state record. -/
theorem trees_of_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) : ∃ pb buf, TreesInvAt h ds d pb buf := by
  obtain ⟨d', pb, buf, trees⟩ := good.trees
  have same : d' = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst same
  exact ⟨pb, buf, trees⟩

/-- A non-`NULL` caller output pointer is a byte block or a foreign `depth` array. -/
theorem output_pointer_cases {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null) :
    ∃ ob, (∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo) := by
  obtain ⟨z0, get0, _, caller, _⟩ := buffers
  have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
  subst same
  rcases caller with null | ⟨_, writable, _⟩
  · exact absurd null out
  · cases pointer : z0.next_out with
    | null => exact absurd pointer out
    | ref ref off =>
      rw [pointer] at writable
      rcases writable_reference_cases (writable rfl) with ⟨b, rfl⟩ | ⟨owner, rfl⟩
      · exact ⟨b, Or.inl ⟨off, rfl⟩⟩
      · exact ⟨owner, Or.inr ⟨off, rfl⟩⟩

/-- **`FLUSH_BLOCK_ONLY(s, last)` from `DInv`.** `last` is 0 or 1, as at every call site. -/
theorem flush_block_dinv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0)
    (overlay : ∀ xs, Recorded h d xs → ∀ z', DynamicOverlay (r.put h z') ds d xs) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ (∃ b, SymbolLedger b result []) ∧ result.bi_valid.toInt < 8 ∧
      (last = true → result.bi_valid.toInt = 0) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      (result.pending = 0 ∨ z'.avail_out = 0) ∧ result.«matches» = 0 := by
  have good := inv.dgood
  obtain ⟨pb, buf, trees⟩ := trees_of_good good
  obtain ⟨xs, recorded, _distance⟩ := inv.recorded
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  have blockSame : b = pb := by
    have := pbuf.symm.trans trees.base.pbuf
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using this
  subst blockSame
  have arraySame : a = buf := Option.some.inj (bytes.symm.trans trees.base.bytes)
  subst arraySame
  obtain ⟨w, p, q, b0, blocks⟩ := good.inv.blocks
  obtain ⟨window, getWindow, _⟩ := blocks.wa
  have shape : Zlib.Deflate.Universal.Shape d := inv.shape'
  have bsHigh : d.block_start.toInt ≤ d.strstart.toNat := shape.blockStart
  have room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat := shape.room
  have biValid : d.bi_valid.toInt ≤ 7 := shape.biValid
  have cursor : d.pending_out = d.pending_buf := shape.cursor pending
  have clear : BlockInit.BlockClear d := inv.symbols.clear
  have span : (d.strstart.toNat : Int) - d.block_start.toInt ≤ 4294967296 := by
    have bound := shape.blockSpan (by intro zero; rw [zero] at level; exact absurd level (by decide))
    have symbols := trees.run.sym_next_le
    have endBound := trees.base.sym_end
    have litHigh := trees.base.lit_hi
    have available : d.match_available.toInt ≤ 1 := by
      rcases shape.matchAvailable with hz | ho
      · rw [hz]; decide
      · rw [ho]; decide
    have count : d.sym_next.toNat / 3 ≤ 32767 := by omega
    omega
  obtain ⟨ob, pointer⟩ := output_pointer_cases good buffers out
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, _sizes, _storage, clearA, ledgerA,
    low, final, cursorA, frame, drained, matchesA⟩ :=
    flush_block_only_safe (ob := ob) good trees buffers level pointer cursor pending
      biValid ledger clear blocks.win getWindow span bsHigh (by omega)
      (overlay xs ⟨b, a, pbuf, bytes, ledger⟩) last
  exact ⟨produced, after, z', result, run, goodA, buffersA, account, clearA, ledgerA, low, final, cursorA,
    frame, drained, matchesA⟩

/-- `flush_block_dinv` for `memLevel ≥ 5` (`lit_bufsize ≥ 2048`), where the overlay room is proved. -/
theorem flush_block_dinv_large {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0)
    (large : 2048 ≤ d.lit_bufsize.toNat) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧ (∃ b, SymbolLedger b result []) ∧ result.bi_valid.toInt < 8 ∧
      (last = true → result.bi_valid.toInt = 0) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      (result.pending = 0 ∨ z'.avail_out = 0) ∧ result.«matches» = 0 := by
  refine flush_block_dinv inv buffers out level pending ?_ last
  intro xs recorded z'
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  have good := inv.dgood
  obtain ⟨pb, buf, trees⟩ := trees_of_good good
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have lowLit := trees.base.lit_lo
    omega
  exact dynamic_overlay_large large pending (show d.bi_valid.toInt ≤ 7 from (inv.shape' : Zlib.Deflate.Universal.Shape d).biValid) capacity

end Zlib.Deflate.Universal.Block

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `(long)s->strstart` as a signed value. -/
theorem uint32_toInt64_toInt (x : UInt32) : x.toUInt64.toInt64.toInt = (x.toNat : Int) := by
  have bound := x.toNat_lt
  rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp
    omega

/-- An empty ledger does not depend on the bytes of the symbol buffer. -/
theorem SymbolLedger.empty_bytes {a b : Array UInt8} {d : DeflateState} (ledger : SymbolLedger a d []) :
    SymbolLedger b d [] :=
  ⟨ledger.count, ledger.valid, fun i s selected => by simp at selected, ledger.literal, ledger.distance⟩

/-- **The block flush keeps the deflate invariant** (`flush_block_spec` of the skeleton, with
`last` 0 or 1 and the dynamic overlay room as a premise). -/
theorem flush_block_spec_of_overlay {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0)
    (overlay : ∀ xs, Recorded h d xs → ∀ z', DynamicOverlay (r.put h z') ds d xs) (last : Bool) :
    ∃ after z' d' produced,
      C.run (FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      d'.sym_next = 0 := by
  have good := inv.dgood
  obtain ⟨pb, buf, trees⟩ := trees_of_good good
  obtain ⟨xs, recorded, _distance⟩ := inv.recorded
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  have blockSame : b = pb := by
    have := pbuf.symm.trans trees.base.pbuf
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using this
  subst blockSame
  have arraySame : a = buf := Option.some.inj (bytes.symm.trans trees.base.bytes)
  subst arraySame
  obtain ⟨w, p, q, b0, blocks⟩ := good.inv.blocks
  have pbSame : b0 = b := by
    have := blocks.pbuf.symm.trans pbuf
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using this
  subst pbSame
  obtain ⟨window, getWindow, _⟩ := blocks.wa
  obtain ⟨prevArr, getPrev, _⟩ := blocks.pa
  obtain ⟨headArr, getHead, _⟩ := blocks.qa
  have shape : Zlib.Deflate.Universal.Shape d := inv.shape'
  have bsHigh : d.block_start.toInt ≤ d.strstart.toNat := shape.blockStart
  have room : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat := shape.room
  have biValid : d.bi_valid.toInt ≤ 7 := shape.biValid
  have cursor : d.pending_out = d.pending_buf := shape.cursor pending
  have clear : BlockInit.BlockClear d := inv.symbols.clear
  have levelNe : d.level ≠ 0 := by intro zero; rw [zero] at level; exact absurd level (by decide)
  have span : (d.strstart.toNat : Int) - d.block_start.toInt ≤ 4294967296 := by
    have bound := shape.blockSpan levelNe
    have symbols := trees.run.sym_next_le
    have endBound := trees.base.sym_end
    have litHigh := trees.base.lit_hi
    have available : d.match_available.toInt ≤ 1 := by
      rcases shape.matchAvailable with hz | ho
      · rw [hz]; decide
      · rw [ho]; decide
    have count : d.sym_next.toNat / 3 ≤ 32767 := by omega
    omega
  obtain ⟨ob, pointer⟩ := output_pointer_cases good buffers out
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, _sizes, storage, clearA, ledgerA,
    lowA, _final, cursorA, frame, _drained, matchesA⟩ :=
    flush_block_only_safe (ob := ob) good trees buffers level pointer cursor pending
      biValid ledger clear blocks.win getWindow span bsHigh (by omega)
      (overlay xs ⟨b0, a, pbuf, bytes, ledger⟩) last
  -- the private arrays are unchanged
  have arrays : after.bytes w = some window ∧ after.words p = some prevArr ∧ after.words q = some headArr := by
    rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
    · exact storage.private_arrays good buffers pointer blocks.win getWindow blocks.prev getPrev
        blocks.head getHead blocks.pbuf
    · exact storage.foreign_private_arrays good buffers pointer blocks.win getWindow blocks.prev getPrev
        blocks.head getHead blocks.pbuf
  -- the record frame
  have fr := frame
  unfold FlushFrame at fr
  have fields : result.strstart = d.strstart ∧ result.lookahead = d.lookahead ∧ result.insert = d.insert ∧
      result.window_size = d.window_size ∧ result.prev_length = d.prev_length ∧
      result.match_length = d.match_length ∧ result.match_available = d.match_available ∧
      result.match_start = d.match_start ∧ result.w_size = d.w_size ∧ result.level = d.level ∧
      result.strategy = d.strategy ∧ result.high_water = d.high_water ∧ result.last_flush = d.last_flush ∧
      result.wrap = d.wrap ∧ result.status = d.status ∧ result.window = d.window ∧ result.prev = d.prev ∧
      result.head = d.head ∧ result.hash_size = d.hash_size ∧ result.hash_shift = d.hash_shift ∧
      result.hash_mask = d.hash_mask ∧ result.ins_h = d.ins_h ∧ result.pending_buf = d.pending_buf ∧
      result.block_start = d.strstart.toUInt64.toInt64 ∧ result.sym_end = d.sym_end := by
    rw [fr]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨fStart, fLook, fInsert, fWinSize, fPrevLen, fMatchLen, fAvail, fMatchStart, fWSize, fLevel,
    fStrategy, fHigh, fLast, fWrap, fStatus, fWindow, fPrev, fHead, fHashSize, fHashShift, fHashMask,
    fIns, fPbuf, fBlock, fSymEnd⟩ := fields
  have countA : result.sym_next = 0 := by
    obtain ⟨_, ledgerR⟩ := ledgerA
    apply UInt32.toNat_inj.mp
    have count := ledgerR.count
    simp only [List.length_nil, Nat.mul_zero] at count
    rw [count]; rfl
  have startCast : result.block_start.toInt = result.strstart.toNat := by
    rw [fBlock, fStart]
    exact uint32_toInt64_toInt d.strstart
  have shapeA : Zlib.Deflate.Universal.Shape result := by
    refine ⟨?room, ?insert, ?insertDone, ?prevLength, ?matchLength, ?matchAvailable, ?blockStart,
      ?blockSpan, ?levelZero, ?available, ?pendingMatch, ?fastLazy, ?highWater, ?lastFlush, ?trailer,
      ?biValid, ?cursor, ?symRoom, ?slides⟩
    · rw [fStart, fLook, fWinSize]; exact shape.room
    · rw [fInsert, fStart]; exact shape.insert
    · rw [fLook, fInsert]; exact shape.insertDone
    · rw [fPrevLen]; exact shape.prevLength
    · rw [fMatchLen]; exact shape.matchLength
    · rw [fAvail]; exact shape.matchAvailable
    · rw [startCast]
      exact Int.le_refl _
    · intro _
      rw [startCast]
      have availableNonneg : 0 ≤ result.match_available.toInt := by
        rw [fAvail]
        rcases shape.matchAvailable with hz | ho
        · rw [hz]; decide
        · rw [ho]; decide
      omega
    · intro zero; rw [fLevel] at zero; exact absurd zero levelNe
    · rw [fAvail, fStart]; exact shape.available
    · rw [fMatchLen, fStart, fMatchStart, fLook, fWSize]; exact shape.pendingMatch
    · rw [fLevel, fStrategy, fMatchLen, fPrevLen]; exact shape.fastLazy
    · rw [fHigh, fWinSize]; exact shape.highWater
    · rw [fLast]; exact shape.lastFlush
    · rw [fWrap, fStatus]; exact shape.trailer
    · omega
    · exact cursorA
    · rw [countA, fSymEnd]
      have endBound := trees.base.sym_end
      have lowLit := trees.base.lit_lo
      simp only [UInt32.toNat_zero]
      omega
    · rw [matchesA]
      exact ⟨by decide, fun _ => rfl⟩
  have dMatches : d.«matches» = 0 := shape.slides.2 levelNe
  have chainsA : Chains after result := by
    have chains : Chains h d := inv.hashing.chains dMatches
    unfold Chains at chains ⊢
    rw [fStart, fInsert]
    rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
    · exact flush_frames_chains storage good buffers pointer blocks.pbuf frame.work chains
    · exact foreign_flush_frames_chains storage good buffers pointer blocks.pbuf frame.work chains
  have hashingA : Hashing after result := by
    refine ⟨fun _ => chainsA, (fun one => by rw [matchesA] at one; exact absurd one (by decide)), ?_⟩
    intro notHuff notRle enough
    rw [fStrategy] at notHuff notRle
    rw [fLook] at enough
    obtain ⟨w1, wa, win1, get1, form⟩ := inv.hashing.rolling notHuff notRle enough
    have wSame : w1 = w := by
      have := win1.symm.trans blocks.win
      simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using this
    subst wSame
    have waSame : wa = window := Option.some.inj (get1.symm.trans getWindow)
    subst waSame
    refine ⟨w1, wa, by rw [fWindow]; exact win1, arrays.1, ?_⟩
    rw [fHashShift, fHashMask, fStart, fIns]
    exact form
  obtain ⟨wA, pA, qA, bA, blocksA⟩ := goodA.inv.blocks
  obtain ⟨arrA, getArrA, _⟩ := blocksA.ba
  have bSame : bA = b0 := by
    have := blocksA.pbuf.symm.trans (fPbuf.trans pbuf)
    simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using this
  subst bSame
  obtain ⟨bufR, ledgerR⟩ := ledgerA
  have symbolsA : Symbols after result := by
    refine ⟨⟨[], ⟨bA, arrA, blocksA.pbuf, getArrA, (SymbolLedger.empty_bytes ledgerR)⟩, fun s member => by cases member⟩,
      clearA, ?_⟩
    intro _ _ _ nonzero
    exact absurd countA nonzero
  have globalsA : LibraryGlobals after := by
    have staticEq := storage.frame.1
    unfold LibraryGlobals
    rw [← staticEq]
    exact inv.globals
  have allocA : DefAlloc z' := by
    obtain ⟨_, _, _, _, _, _, _, zalloc, zfree, _⟩ := account
    have base := inv.defAlloc
    exact ⟨zalloc.trans base.1, zfree.trans base.2⟩
  exact ⟨after, z', result, produced, run, ⟨goodA, allocA, globalsA, shapeA, hashingA, symbolsA⟩,
    buffersA, account, countA⟩

/-- `flush_block_spec_of_overlay` for `memLevel ≥ 5` (`lit_bufsize ≥ 2048`). -/
theorem flush_block_spec_large {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0) (large : 2048 ≤ d.lit_bufsize.toNat)
    (last : Bool) :
    ∃ after z' d' produced,
      C.run (FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      d'.sym_next = 0 := by
  refine flush_block_spec_of_overlay inv buffers out level pending ?_ last
  intro xs recorded z'
  obtain ⟨b, a, pbuf, bytes, ledger⟩ := recorded
  obtain ⟨pb, buf, trees⟩ := trees_of_good inv.dgood
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have lowLit := trees.base.lit_lo
    omega
  exact dynamic_overlay_large large pending
    (show d.bi_valid.toInt ≤ 7 from (inv.shape' : Zlib.Deflate.Universal.Shape d).biValid) capacity

end Zlib.Deflate.Universal.Block
