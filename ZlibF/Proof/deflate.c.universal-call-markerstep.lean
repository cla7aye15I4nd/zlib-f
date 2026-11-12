import ZlibF.Proof.«deflate.c.universal-call-headerentry»

/-!
# deflate.c: the flush markers of one `deflate` call on the invariant

Batch C (`deflate_call` / `marker_step`). After a strategy returns `block_done`, `marker_tail`
writes the marker the flush asks for and flushes. The block is flushed (`sym_next = 0`) and no lazy
match is pending (`match_available = 0`), which the strategy meaning gives. Without a full flush
only the pending, bit and `last_flush` fields change, and `DInv.lift_empty` carries the invariant.
After a full flush `CLEAR_HASH` zeroes the `head` table, so the chains hold for any frontier
(`Hashing.cleared`), and with no lookahead the positions are reset to zero; `Shape.of_marker`
re-establishes the shape clauses that read the positions.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- A marker shape with the positions and `slid` kept is a header-field shape. -/
theorem MarkerShape.header_fields {d d' : DeflateState} (shape : MarkerShape d d')
    (ss : d'.strstart = d.strstart) (bs : d'.block_start = d.block_start) (ins : d'.insert = d.insert)
    (sl : d'.slid = d.slid) : HeaderFields d d' := by
  obtain ⟨p, po, bb, bv, bu, lf, sl', ss', bs', ins', rfl⟩ := shape
  change ss' = d.strstart at ss
  change bs' = d.block_start at bs
  change ins' = d.insert at ins
  change sl' = d.slid at sl
  subst ss bs ins sl
  rfl

/-- The fields a marker keeps. -/
theorem MarkerShape.keeps {d d' : DeflateState} (shape : MarkerShape d d') :
    d'.status = d.status ∧ d'.sym_next = d.sym_next ∧ d'.gzhead = d.gzhead ∧ d'.lookahead = d.lookahead ∧
    d'.window = d.window ∧ d'.prev = d.prev ∧ d'.head = d.head ∧ d'.hash_size = d.hash_size ∧
    d'.ins_h = d.ins_h ∧ d'.hash_shift = d.hash_shift ∧ d'.hash_mask = d.hash_mask ∧
    d'.strategy = d.strategy ∧ d'.wrap = d.wrap := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := shape
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`Shape` after a flush marker**: the clauses that read the pending, bit and `last_flush`
fields are premises; the positions are kept, or reset to zero on a state with no lookahead, no
symbols and no pending lazy match. -/
theorem Shape.of_marker {d d' : DeflateState} (shape : Shape d) (ms : MarkerShape d d')
    (lastFlush : -2 ≤ d'.last_flush.toInt ∧ d'.last_flush.toInt ≤ 5)
    (headerFlush : d'.status = INIT_STATE ∨ d'.status = GZIP_STATE → d'.last_flush = -2 ∨ d'.last_flush = -1)
    (biValid : d'.bi_valid.toInt ≤ 7) (cursor : d'.pending = 0 → d'.pending_out = d'.pending_buf)
    (pos : (d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert) ∨
      (d'.strstart = 0 ∧ d'.block_start = 0 ∧ d'.insert = 0 ∧ d.lookahead = 0 ∧ d.match_available = 0 ∧
        d.sym_next = 0)) :
    Shape d' := by
  obtain ⟨p, po, bb, bv, bu, lf, sl, ss, bs, ins, rfl⟩ := ms
  rcases pos with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, look, ma, sym⟩
  · change ss = d.strstart at e1
    change bs = d.block_start at e2
    change ins = d.insert at e3
    subst e1 e2 e3
    exact { shape with lastFlush, headerFlush, biValid, cursor }
  · change ss = 0 at e1
    change bs = 0 at e2
    change ins = 0 at e3
    subst e1 e2 e3
    have pending : ∀ m : 3 ≤ d.match_length.toNat, False := by
      intro m
      have b := (shape.pendingMatch m).2.2.1
      rw [look] at b; simp at b; omega
    exact { shape with
      lastFlush, headerFlush, biValid, cursor
      room := by simp [look]
      insert := by simp
      insertDone := fun _ => rfl
      blockStart := by simp
      blockSpan := fun _ => by simp [ma, sym]
      levelZero := fun _ => ⟨by simp, look, sym⟩
      available := fun e => absurd ma e
      pendingMatch := fun m => absurd m (fun m' => pending m')
      windowInit := by simp [look]
      symBlock := fun e => absurd sym e
      lazyStart := fun e => absurd ma e }

/-- `Symbols` with no recorded symbol across a flush marker. -/
theorem Symbols.marker_empty {h h' : Heap} {d d' : DeflateState} (symbols : Symbols h d)
    (empty : d.sym_next = 0) (shape : MarkerShape d d')
    (pbuf : ∀ b, d.pending_buf = .ref (.blk b) 0 → ∃ a', h'.bytes b = some a') : Symbols h' d' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := shape
  obtain ⟨⟨xs, ⟨b, a, ptr, _, ledger⟩, near⟩, clear, _⟩ := symbols
  have nil : xs = [] := by
    have := ledger.count
    rw [empty] at this
    exact List.eq_nil_of_length_eq_zero (by simp at this; omega)
  subst nil
  obtain ⟨a', get'⟩ := pbuf b ptr
  refine ⟨⟨[], ⟨b, a', ptr, get',
    (Zlib.Deflate.Universal.Block.SymbolLedger.empty_bytes (b := a') ledger).keep rfl rfl rfl rfl⟩, by simp⟩,
    ⟨clear.bl, clear.opt, clear.fixed⟩, ?_⟩
  intro _ _ _ nz
  exact absurd empty nz

/-- What the marker step leaves. -/
def MarkerOut (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState) (buf : Array UInt8)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DInv after r ds z' d' ∧ HeaderInv d' ∧ CallFacts d' ∧ StreamBuffers after r ∧
    (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
    StreamAccounting z z' 0 produced ∧ MarkerFrame h after r ds pb d z z' produced ∧ MarkerShape d d' ∧
    z'.next_out ≠ .null ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1) ∨
     (run = k after ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush))

/-- **The marker step**: the flush markers keep `DInv ∧ HeaderInv ∧ CallFacts`, for every flush
value. `empty` and `idle`: the strategy returned `block_done`, which leaves no recorded symbol and
no pending lazy match; `lastFlush`: the entry phase has stored the flush value. -/
theorem marker_step {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d)
    (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (out : z.next_out ≠ .null) (empty : d.sym_next = 0)
    (idle : d.match_available = 0) (lastFlush : d.last_flush ≠ -2) (flush : Int32) (k : M Int32) :
    MarkerOut h r ds pb z d buf (markerTail (some r) (some (.tab ds)) flush k h) k := by
  have good := inv.good
  obtain ⟨after, z', d', produced, good', treesA, buffers', account, frame, low, ms, cur', out', notFull, full,
    outcome⟩ := marker_tail good trees buffers cursor pending inv.shape.biValid out flush k
  obtain ⟨stEq, symEq, gzEq, lookEq, winEq, prevEq, headEq, hsEq, insEq, shiftEq, maskEq, stratEq, wrapEq⟩ :=
    ms.keeps
  obtain ⟨_, _, _, static, win, prv, pres⟩ := MarkerFrame.call_facts frame good buffers trees.base.pbuf out
  have alloc : DefAlloc z' :=
    ⟨by rw [account.2.2.2.2.2.2.2.1]; exact inv.alloc.1, by rw [account.2.2.2.2.2.2.2.2.1]; exact inv.alloc.2⟩
  have lfCase : d'.last_flush = -1 ∨ d'.last_flush = d.last_flush := by
    rcases outcome with ⟨_, lf⟩ | ⟨_, _, _, lf⟩
    · exact Or.inl lf
    · exact Or.inr lf
  have shapeOf : ((d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert) ∨
      (d'.strstart = 0 ∧ d'.block_start = 0 ∧ d'.insert = 0 ∧ d.lookahead = 0 ∧ d.match_available = 0 ∧
        d.sym_next = 0)) → Shape d' := by
    intro pos
    refine Shape.of_marker inv.shape ms ?_ ?_ (by omega) cur' pos
    · rcases lfCase with e | e
      · rw [e]; decide
      · rw [e]; exact inv.shape.lastFlush
    · intro st
      rcases lfCase with e | e
      · exact Or.inr e
      · rw [e]; exact inv.shape.headerFlush (by rw [← stEq]; exact st)
  have callFacts : CallFacts d' := by
    have notReset : d'.last_flush ≠ -2 := by
      rcases lfCase with e | e
      · rw [e]; decide
      · rw [e]; exact lastFlush
    exact ⟨fun e => absurd e notReset, fun e => absurd e notReset, fun _ => symEq.trans empty,
      fun st => lookEq.trans (facts.finishLook (by rw [← stEq]; exact st))⟩
  have headerA : HeaderInv d' := header.keep stEq symEq gzEq
  have dinv : DInv after r ds z' d' := by
    by_cases isFull : flush = Z_FULL_FLUSH
    · obtain ⟨zeroHead, keepPos, resetPos⟩ := full isFull
      obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
      obtain ⟨wa, getW, _⟩ := blocks.wa
      obtain ⟨pa, getP, _⟩ := blocks.pa
      obtain ⟨qa, getQ, zero⟩ := zeroHead q blocks.head
      have pos : (d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert) ∨
          (d'.strstart = 0 ∧ d'.block_start = 0 ∧ d'.insert = 0 ∧ d.lookahead = 0 ∧ d.match_available = 0 ∧
            d.sym_next = 0) := by
        by_cases look : d.lookahead = 0
        · obtain ⟨a, b', c⟩ := resetPos look
          exact Or.inr ⟨a, b', c, look, idle, empty⟩
        · exact Or.inl (keepPos look)
      have hashing : Hashing after d' := by
        refine Hashing.cleared inv.hashing (by rw [winEq]; exact blocks.win) (by rw [prevEq]; exact blocks.prev)
          (by rw [headEq]; exact blocks.head) (by rw [win w blocks.win]; exact getW)
          (by rw [prv p blocks.prev]; exact getP) getQ (fun j hj => zero j (by rw [← hsEq]; exact hj)) ?_
        by_cases look : d.lookahead = 0
        · right; rw [lookEq, look]; decide
        · left
          exact ⟨winEq, win w blocks.win, (keepPos look).1, lookEq, insEq, shiftEq, maskEq, stratEq⟩
      exact ⟨good', alloc, by unfold LibraryGlobals at *; rw [static]; exact inv.globals, shapeOf pos, hashing,
        Symbols.marker_empty inv.symbols empty ms pres⟩
    · obtain ⟨ss, bs, ins, sl, hd⟩ := notFull isFull
      exact DInv.lift_empty inv good' alloc static (shapeOf (Or.inl ⟨ss, bs, ins⟩))
        (ms.header_fields ss bs ins sl) empty win prv hd pres
  exact ⟨after, z', d', produced, dinv, headerA, callFacts, buffers', treesA, account, frame, ms, out', outcome⟩

end Zlib.Deflate.Universal.Call
