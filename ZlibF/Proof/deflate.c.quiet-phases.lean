import ZlibF.Proof.«deflate.c.quiet-phi»
import ZlibF.Proof.«deflate.c.universal-call-headerstep»
import ZlibF.Proof.«deflate.c.universal-call-markerstep»

/-!
# deflate.c: the flush marker and the header phase, with the facts `DeflateQuiet` needs

`marker_quiet` is `marker_step` with a byte bound: the flush marker of a call adds at most 6 bytes
(the bytes the flush delivers plus the bytes left pending), the output facts of its two outcomes,
and the positions (kept, or reset to zero by a full flush).

`header_quiet` is `header_step_mid` from a drained `pending_buf`, with progress on its early
return: the header rank drops, or the status is kept and `gzindex` grows. The stage lemmas of the
header phase are restated here with that progress; their proofs follow the originals.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-! ## The flush marker -/

theorem marker_flush_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) (out : z.next_out ≠ .null)
    (k : M Int32) :
    ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
      DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ StageFrame h after r ds pb d z z' produced ∧
      d'.bi_valid.toInt < 8 ∧ d'.pending_buf = d.pending_buf ∧ z'.next_out ≠ .null ∧
      MarkerShape d d' ∧ d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert ∧
      d'.slid = d.slid ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      ((markerFlush (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧ z'.avail_out = 0 ∧ d'.last_flush = -1) ∨
       (markerFlush (some r) (some (.tab ds)) k h = k after ∧ z'.avail_out ≠ 0 ∧
         d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush ∧
         d' = { d with
           pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf,
           bi_valid := d'.bi_valid, bi_used := d'.bi_used })) ∧
      d'.pending.toNat + produced = d.pending.toNat + d.bi_valid.toInt.toNat / 8 := by
  obtain ⟨produced, H1, z1, d1, run1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, copied, left, low1, fields1,
    empty1⟩ := room_flush good trees buffers cursor room out
  have out1 : z1.next_out ≠ .null := by rw [account1.2.2.2.2.2.1]; exact Call.advance_ne_null out _
  have pbuf1 : d1.pending_buf = d.pending_buf := by rw [fields1]
  have stage1 := StageFrame.of_flush_room good trees buffers cursor room out run1 good1.live.hz account1
  have shape1 : HeaderShape d d1 := ⟨_, _, _, _, _, _, _, _, fields1⟩
  have mshape1 : MarkerShape d d1 := MarkerShape.of_bits fields1
  have ss1 : d1.strstart = d.strstart := by have e := congrArg DeflateState.strstart fields1; exact e
  have bs1 : d1.block_start = d.block_start := by have e := congrArg DeflateState.block_start fields1; exact e
  have ins1 : d1.insert = d.insert := by have e := congrArg DeflateState.insert fields1; exact e
  have sl1 : d1.slid = d.slid := by have e := congrArg DeflateState.slid fields1; exact e
  by_cases full : z1.avail_out = 0
  · obtain ⟨good5, buffers5, _⟩ := last_flush_frame (pb := pb) good1 trees1 buffers1 (-1)
    refine ⟨_, z1, _, produced, good5, ⟨buf1, trees_at_buffer good5 trees1.base.pbuf trees1.base.bytes, size1⟩,
      buffers5, account1,
      by
        have s := StageFrame.trans stage1 (StageFrame.state good1 buffers1 trees1.base.pbuf { d1 with last_flush := -1 })
          (HeaderShape.owned shape1) good buffers
        rwa [Nat.add_zero] at s,
      low1, pbuf1, out1, mshape1.trans (MarkerShape.lastFlush d1 (-1)), ss1, bs1, ins1, sl1,
      fun z0 => empty1 z0, Or.inl ⟨?_, full, rfl⟩, left⟩
    unfold markerFlush
    simp only [bind_app]
    rw [run1]
    simp [zrd_eq, good1.live.hz, full, wrD_eq, good1.live.hs]
  · have avail : produced < z.avail_out.toNat := by
      have a := account1.2.2.2.1
      have : z1.avail_out.toNat ≠ 0 := fun e => full (UInt32.toNat_inj.mp (by rw [e]; rfl))
      omega
    have zero : d1.pending = 0 := by
      have : d1.pending.toNat = 0 := by rw [copied] at left avail; omega
      exact UInt64.toNat_inj.mp (by rw [this]; rfl)
    refine ⟨H1, z1, d1, produced, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, low1, pbuf1, out1,
      mshape1, ss1, bs1, ins1, sl1, empty1, Or.inr ⟨?_, full, zero, empty1 zero, by rw [fields1], fields1⟩, left⟩
    unfold markerFlush
    simp only [bind_app]
    rw [run1]
    simp [zrd_eq, good1.live.hz, full]


theorem marker_tail_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (out : z.next_out ≠ .null)
    (flush : Int32) (k : M Int32) :
    ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
      DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ MarkerFrame h after r ds pb d z z' produced ∧
      d'.bi_valid.toInt < 8 ∧ MarkerShape d d' ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      z'.next_out ≠ .null ∧
      (flush ≠ Z_FULL_FLUSH → d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert ∧
        d'.slid = d.slid ∧ ∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧
      (flush = Z_FULL_FLUSH →
        (∀ q, d.head = .ref (.blk q) 0 → ∃ qa, after.words q = some qa ∧ ∀ j, j < d.hash_size.toNat → wfn qa j = 0) ∧
        (d.lookahead ≠ 0 → d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.insert = d.insert) ∧
        (d.lookahead = 0 → d'.strstart = 0 ∧ d'.block_start = 0 ∧ d'.insert = 0)) ∧
      ((markerTail (some r) (some (.tab ds)) flush k h = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧
          z'.avail_out = 0) ∨
       (markerTail (some r) (some (.tab ds)) flush k h = k after ∧ d'.pending = 0 ∧
         d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush ∧ z'.avail_out ≠ 0)) ∧
      d'.pending.toNat + produced ≤ 6 := by
  have zeroN : d.pending.toNat = 0 := by rw [pending]; rfl
  have sizeLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have bitsLo := trees.run.bi_lo
  have keepD : ∀ {d1 : DeflateState}, BitsDiff d d1 → d1.last_flush = d.last_flush ∧ d1.strstart = d.strstart ∧
      d1.block_start = d.block_start ∧ d1.insert = d.insert ∧ d1.lookahead = d.lookahead ∧
      d1.hash_size = d.hash_size ∧ d1.slid = d.slid := by
    intro d1 diff; obtain ⟨_, _, _, _, rfl⟩ := diff; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the flush from the state after the marker
  have finish : ∀ {H : Heap} {d1 : DeflateState} {buf1 : Array UInt8},
      DGood H r ds z d1 → TreesInvAt H ds d1 pb buf1 → buf1.size = buf.size → StreamBuffers H r →
      d1.pending_out = d1.pending_buf → 8 * d1.pending.toNat + d1.bi_valid.toInt.toNat ≤ 8 * buf1.size →
      MarkerFrame h H r ds pb d z z 0 → (∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b) → d1.head = d.head →
      MarkerShape d d1 → d1.last_flush = d.last_flush →
      ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
        DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
        StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ MarkerFrame h after r ds pb d z z' produced ∧
        d'.bi_valid.toInt < 8 ∧ MarkerShape d d' ∧
        d'.strstart = d1.strstart ∧ d'.block_start = d1.block_start ∧ d'.insert = d1.insert ∧
        d'.slid = d1.slid ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧ z'.next_out ≠ .null ∧
        (∀ q, d.head = .ref (.blk q) 0 → after.words q = H.words q) ∧
        ((markerFlush (some r) (some (.tab ds)) k H = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧
            z'.avail_out = 0) ∨
         (markerFlush (some r) (some (.tab ds)) k H = k after ∧ d'.pending = 0 ∧
           d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush ∧ z'.avail_out ≠ 0)) ∧
        d'.pending.toNat + produced = d1.pending.toNat + d1.bi_valid.toInt.toNat / 8 := by
    intro H d1 buf1 good1 trees1 size1 buffers1 cursor1 room1 pre owned1 head1 shape0 lf0
    obtain ⟨after, z', d', produced, goodA, ⟨b', tA, sA⟩, buffersA, account, stageA, low, _, outA, shapeF, ssF, bsF,
      insF, slF, curF, outcome, cnt⟩ := marker_flush_q good1 trees1 buffers1 cursor1 room1 out k
    have keepsA := StageFrame.keeps stageA good1 buffers1 trees1.base.pbuf out
    have mf := MarkerFrame.trans pre (MarkerFrame.of_stage stageA) owned1 head1 good buffers
    rw [Nat.zero_add] at mf
    refine ⟨after, z', d', produced, goodA, ⟨b', tA, sA.trans size1⟩, buffersA, account, mf, low,
      shape0.trans shapeF, ssF, bsF, insF, slF, curF, outA, fun q hq => keepsA.2.2.2.1 q (by rw [head1]; exact hq), ?_,
      cnt⟩
    rcases outcome with ⟨e, fo, lf⟩ | ⟨e, nz, zero, cur, lfk, _⟩
    · exact Or.inl ⟨e, lf, fo⟩
    · exact Or.inr ⟨e, zero, cur, lfk.trans lf0, nz⟩
  by_cases isPartial : flush = Z_PARTIAL_FLUSH
  · subst isPartial
    obtain ⟨next, d1, run, trees1, outBits1, size, _, _, _, diff⟩ :=
      Zlib.Trees.Proofs.Out.tr_align_emit trees (by omega)
    obtain ⟨good1, buffers1, cursor1, _⟩ := bits_step good trees buffers cursor size diff trees1
    have len := congrArg List.length outBits1
    simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append,
      Zlib.Trees.Proofs.Out.natBits_length, List.length_nil] at len
    have o1 : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b := by
      obtain ⟨_, _, _, _, e⟩ := diff; rw [e]; exact fun _ => Iff.rfl
    have q1 : d1.head = d.head := by obtain ⟨_, _, _, _, e⟩ := diff; rw [e]
    have k1 := keepD diff
    have stage0 := StageFrame.bytes good buffers trees.base.pbuf trees.base.bytes next d1
    have keeps1 := StageFrame.keeps stage0 good buffers trees.base.pbuf out
    obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
      outcome, cnt⟩ := finish good1 trees1 size buffers1 cursor1 (by rw [size]; omega)
        (MarkerFrame.of_stage stage0) o1 q1 (MarkerShape.of_diff diff) k1.1
    refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
      fun _ => ⟨ssA.trans k1.2.1, bsA.trans k1.2.2.1, insA.trans k1.2.2.2.1, slA.trans k1.2.2.2.2.2.2,
        fun q hq => (wordsA q hq).trans (keeps1.2.2.2.1 q hq)⟩,
      fun e => absurd e (by decide), ?_, ?_⟩
    have eq : markerTail (some r) (some (.tab ds)) Z_PARTIAL_FLUSH k h =
        markerFlush (some r) (some (.tab ds)) k (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds d1) := by
      unfold markerTail markerFlush
      simp only [show (Z_PARTIAL_FLUSH == Z_PARTIAL_FLUSH) = true from rfl, ite_true, bind_app]
      rw [run]
      rfl
    · rw [eq]; exact outcome
    · omega
  · have np : (flush == Z_PARTIAL_FLUSH) = false := beq_eq_false_iff_ne.mpr isPartial
    by_cases isBlock : flush = Z_BLOCK
    · subst isBlock
      obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
        outcome, cnt⟩ := finish good trees rfl buffers cursor (by rw [zeroN]; omega)
          (MarkerFrame.of_stage (StageFrame.refl good buffers trees.base.pbuf)) (fun _ => Iff.rfl) rfl
          (MarkerShape.refl d) rfl
      refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
        fun _ => ⟨ssA, bsA, insA, slA, wordsA⟩, fun e => absurd e (by decide), ?_, ?_⟩
      have eq : markerTail (some r) (some (.tab ds)) Z_BLOCK k h = markerFlush (some r) (some (.tab ds)) k h := by
        unfold markerTail markerFlush
        simp only [np, Bool.false_eq_true, ite_false, show (Z_BLOCK != Z_BLOCK) = false from rfl, bind_app, pure_app]
      · rw [eq]; exact outcome
      · omega
    · have nb : (flush != Z_BLOCK) = true := bne_iff_ne.mpr isBlock
      obtain ⟨H1, d1, buf1, run1, good1, trees1, size1, buffers1, cursor1, _, zero1, pend1, diff1, stage1⟩ :=
        empty_stored_block good trees buffers cursor pending bits
      have o1 : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b := by
        obtain ⟨_, _, _, _, e⟩ := diff1; rw [e]; exact fun _ => Iff.rfl
      have q1 : d1.head = d.head := by obtain ⟨_, _, _, _, e⟩ := diff1; rw [e]
      have k1 := keepD diff1
      have look1 : d1.lookahead = d.lookahead := k1.2.2.2.2.1
      have keeps1 := StageFrame.keeps stage1 good buffers trees.base.pbuf out
      by_cases isFull : flush = Z_FULL_FLUSH
      · subst isFull
        obtain ⟨H2, run2, good2, trees2, buffers2, bytes2, clear2, cleared2⟩ := clear_hash_step good1 trees1 buffers1
        have mf2 := MarkerFrame.trans (MarkerFrame.of_stage stage1) clear2 o1 q1 good buffers
        have room2 : 8 * ({ d1 with slid := 0 } : DeflateState).pending.toNat +
            ({ d1 with slid := 0 } : DeflateState).bi_valid.toInt.toNat ≤ 8 * buf1.size := by
          change 8 * d1.pending.toNat + d1.bi_valid.toInt.toNat ≤ _; rw [zero1, size1]; simp; omega
        have zeroHead : ∀ {G : Heap}, (∀ q, d.head = .ref (.blk q) 0 → G.words q = H2.words q) →
            ∀ q, d.head = .ref (.blk q) 0 → ∃ qa, G.words q = some qa ∧ ∀ j, j < d.hash_size.toNat → wfn qa j = 0 := by
          intro G words q hq
          obtain ⟨qa, getQ, zero⟩ := cleared2 q (by rw [q1]; exact hq)
          exact ⟨qa, (words q hq).trans getQ, fun j hj => zero j (by rw [k1.2.2.2.2.2.1]; exact hj)⟩
        by_cases look : d1.lookahead = 0
        · obtain ⟨good3, trees3, buffers3⟩ := positions_reset good2 trees2 buffers2
          have mf3 := MarkerFrame.trans mf2 (MarkerFrame.of_stage (StageFrame.state good2 buffers2 trees2.base.pbuf
            { ({ d1 with slid := 0 } : DeflateState) with strstart := 0, block_start := 0, insert := 0 }))
            (fun b => o1 b) q1 good buffers
          obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
            outcome, cnt⟩ := finish good3 trees3 size1 buffers3 cursor1 room2 (by simpa using mf3) (fun b => o1 b) q1
              ((MarkerShape.of_diff diff1).trans ((MarkerShape.slid d1).trans (MarkerShape.positions _))) k1.1
          refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
            fun ne => absurd rfl ne,
            fun _ => ⟨zeroHead wordsA, fun hl => absurd (by rw [← look1]; exact look) hl,
              fun _ => ⟨ssA, bsA, insA⟩⟩, ?_, ?_⟩
          have eq : markerTail (some r) (some (.tab ds)) Z_FULL_FLUSH k h =
              markerFlush (some r) (some (.tab ds)) k (setD H2 ds
                { ({ d1 with slid := 0 } : DeflateState) with strstart := 0, block_start := 0, insert := 0 }) := by
            unfold markerTail markerFlush
            simp only [show (Z_FULL_FLUSH == Z_PARTIAL_FLUSH) = false from rfl,
              show (Z_FULL_FLUSH != Z_BLOCK) = true from rfl, show (Z_FULL_FLUSH == Z_FULL_FLUSH) = true from rfl,
              Bool.false_eq_true, ite_false, ite_true, bind_app]
            rw [run1]; simp only []
            rw [run2]
            simp only [rdD_eq, good2.live.hs]
            simp only [look, show ((0 : UInt32) == 0) = true from rfl, ite_true, bind_app, wrD_eq, good2.live.hs]
          · rw [eq]; exact outcome
          · dsimp only at cnt; omega
        · obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
            outcome, cnt⟩ := finish good2 trees2 size1 buffers2 cursor1 room2 (by simpa using mf2) (fun b => o1 b) q1
              ((MarkerShape.of_diff diff1).trans (MarkerShape.slid d1)) k1.1
          refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
            fun ne => absurd rfl ne,
            fun _ => ⟨zeroHead wordsA, fun _ => ⟨ssA.trans k1.2.1, bsA.trans k1.2.2.1, insA.trans k1.2.2.2.1⟩,
              fun hl => absurd (by rw [look1]; exact hl) look⟩, ?_, ?_⟩
          have eq : markerTail (some r) (some (.tab ds)) Z_FULL_FLUSH k h =
              markerFlush (some r) (some (.tab ds)) k H2 := by
            unfold markerTail markerFlush
            simp only [show (Z_FULL_FLUSH == Z_PARTIAL_FLUSH) = false from rfl,
              show (Z_FULL_FLUSH != Z_BLOCK) = true from rfl, show (Z_FULL_FLUSH == Z_FULL_FLUSH) = true from rfl,
              Bool.false_eq_true, ite_false, ite_true, bind_app]
            rw [run1]; simp only []
            rw [run2]
            simp only [rdD_eq, good2.live.hs, beq_eq_false_iff_ne.mpr look, Bool.false_eq_true, ite_false, pure_app]
            rfl
          · rw [eq]; exact outcome
          · dsimp only at cnt; omega
      · obtain ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, ssA, bsA, insA, slA, curA, outA, wordsA,
          outcome, cnt⟩ := finish good1 trees1 size1 buffers1 cursor1 (by rw [zero1]; simp; omega)
            (MarkerFrame.of_stage stage1) o1 q1 (MarkerShape.of_diff diff1) k1.1
        refine ⟨after, z', d', produced, goodA, treesA, buffersA, account, mf, low, shapeA, curA, outA,
          fun _ => ⟨ssA.trans k1.2.1, bsA.trans k1.2.2.1, insA.trans k1.2.2.2.1, slA.trans k1.2.2.2.2.2.2,
            fun q hq => (wordsA q hq).trans (keeps1.2.2.2.1 q hq)⟩,
          fun e => absurd e isFull, ?_, ?_⟩
        have eq : markerTail (some r) (some (.tab ds)) flush k h = markerFlush (some r) (some (.tab ds)) k H1 := by
          unfold markerTail markerFlush
          simp only [np, nb, beq_eq_false_iff_ne.mpr isFull, Bool.false_eq_true, ite_false, ite_true, bind_app]
          rw [run1]
        · rw [eq]; exact outcome
        · omega


/-- What the marker step leaves (`MarkerOut`), with the output facts of the two outcomes, the bytes the
marker adds, and the positions. -/
def MarkerQuietOut (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DInv after r ds z' d' ∧ HeaderInv d' ∧ CallFacts d' ∧ StreamBuffers after r ∧
    (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
    StreamAccounting z z' 0 produced ∧ MarkerFrame h after r ds pb d z z' produced ∧ MarkerShape d d' ∧
    z'.next_out ≠ .null ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧ z'.avail_out = 0) ∨
     (run = k after ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧ d'.last_flush = d.last_flush ∧
       z'.avail_out ≠ 0)) ∧
    produced + d'.pending.toNat ≤ 6 ∧
    ((d'.strstart = d.strstart ∧ d'.block_start = d.block_start) ∨ (d'.strstart = 0 ∧ d'.block_start = 0))

/-- **The marker step for `DeflateQuiet`**: `marker_step`, and the marker adds at most 6 bytes
(delivered plus pending): on a drained `pending_buf` with fewer than 8 bits held, `_tr_align`
emits 10 bits, the empty stored block leaves at most 6 bytes and no bit, `Z_BLOCK` emits nothing.
The output is full on the early return and not full on the way on; the positions are kept, or
reset to zero by a full flush with no lookahead. -/
theorem marker_quiet {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d)
    (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (out : z.next_out ≠ .null) (empty : d.sym_next = 0)
    (idle : d.match_available = 0) (lastFlush : d.last_flush ≠ -2) (busyNow : d.status = BUSY_STATE)
    (flush : Int32) (k : M Int32) :
    MarkerQuietOut h r ds pb z d buf (markerTail (some r) (some (.tab ds)) flush k h) k := by
  have good := inv.good
  obtain ⟨after, z', d', produced, good', treesA, buffers', account, frame, low, ms, cur', out', notFull, full,
    outcome, bound⟩ := marker_tail_q good trees buffers cursor pending inv.shape.biValid out flush k
  have positions : (d'.strstart = d.strstart ∧ d'.block_start = d.block_start) ∨
      (d'.strstart = 0 ∧ d'.block_start = 0) := by
    by_cases isFull : flush = Z_FULL_FLUSH
    · obtain ⟨_, keepPos, resetPos⟩ := full isFull
      by_cases look : d.lookahead = 0
      · obtain ⟨a, b, _⟩ := resetPos look; exact Or.inr ⟨a, b⟩
      · obtain ⟨a, b, _⟩ := keepPos look; exact Or.inl ⟨a, b⟩
    · obtain ⟨a, b, _⟩ := notFull isFull; exact Or.inl ⟨a, b⟩
  obtain ⟨stEq, symEq, gzEq, lookEq, winEq, prevEq, headEq, hsEq, insEq, shiftEq, maskEq, stratEq, wrapEq⟩ :=
    ms.keeps
  obtain ⟨_, _, _, static, win, prv, pres⟩ := MarkerFrame.call_facts frame good buffers trees.base.pbuf out
  have alloc : DefAlloc z' :=
    ⟨by rw [account.2.2.2.2.2.2.2.1]; exact inv.alloc.1, by rw [account.2.2.2.2.2.2.2.2.1]; exact inv.alloc.2⟩
  have lfCase : d'.last_flush = -1 ∨ d'.last_flush = d.last_flush := by
    rcases outcome with ⟨_, lf, _⟩ | ⟨_, _, _, lf, _⟩
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
      fun st => lookEq.trans (facts.finishLook (by rw [← stEq]; exact st)), fun st => absurd (busyNow.symm.trans (stEq.symm.trans st)) (by decide)⟩
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
  exact ⟨after, z', d', produced, dinv, headerA, callFacts, buffers', treesA, account, frame, ms, out', outcome,
    by omega, positions⟩


/-! ## The header phase -/

/-- The header rank of a status (`rank` of `deflate.c.quiet-phi.lean`). -/
def rankOf (s : Int32) : Nat :=
  if s = INIT_STATE ∨ s = GZIP_STATE then 6
  else if s = EXTRA_STATE then 5
  else if s = NAME_STATE then 4
  else if s = COMMENT_STATE then 3
  else if s = HCRC_STATE then 2
  else 0

theorem rank_eq (d : DeflateState) : rank d = rankOf d.status := rfl

theorem rank_le_of {d d' : DeflateState} {a b : Int32} (ha : d'.status = a) (hb : d.status = b)
    (c : rankOf a ≤ rankOf b) : rank d' ≤ rank d := by
  rw [rank_eq, rank_eq, ha, hb]; exact c

theorem rank_lt_of {d d' : DeflateState} {a b : Int32} (ha : d'.status = a) (hb : d.status = b)
    (c : rankOf a < rankOf b) : rank d' < rank d := by
  rw [rank_eq, rank_eq, ha, hb]; exact c

theorem rank_le_of_status {d d' : DeflateState} (e : d'.status = d.status) : rank d' ≤ rank d :=
  Nat.le_of_eq (by rw [rank_eq, rank_eq, e])

/-- Progress of an early return: the header rank drops, or the status is kept and `gzindex` grows. -/
def QProg (d d' : DeflateState) : Prop :=
  rank d' < rank d ∨ (d'.status = d.status ∧ d.gzindex.toNat < d'.gzindex.toNat)

/-- What an early return of the header phase gives: the rank does not grow, and from a drained
`pending_buf` there is progress. -/
def QZProg (d d' : DeflateState) : Prop :=
  rank d' ≤ rank d ∧ (d.pending = 0 → QProg d d')

theorem pending_lt_of_zero {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d pb buf) (zero : d.pending = 0) : d.pending.toNat < buf.size := by
  have : d.pending.toNat = 0 := by rw [zero]; rfl
  have := trees.base.size; have := trees.base.lit_lo
  omega

theorem ok_bind {α β : Type} {m : M α} {f : α → M β} {H H' : Heap} {b : β}
    (e : (m >>= f) H = .ok (b, H')) : ∃ a H1, f a H1 = .ok (b, H') := by
  rw [bind_app] at e
  split at e
  · exact ⟨_, _, e⟩
  · cases e

/-- `strRead` keeps the early-return flag. -/
theorem str_read_ret {s : DeflateStatePtr} {sel : GzHeader → BPtr} {st st1 : StrS} {H H' : Heap}
    (run : strRead s sel st H = .ok (st1, H')) : st1.ret = st.ret := by
  unfold strRead at run
  obtain ⟨_, _, run⟩ := ok_bind run
  obtain ⟨_, _, run⟩ := ok_bind run
  obtain ⟨_, _, run⟩ := ok_bind run
  obtain ⟨⟨⟩, _, run⟩ := ok_bind run
  obtain ⟨⟨⟩, _, run⟩ := ok_bind run
  cases run
  rfl

/-- **The early return of a string-loop iteration** happens only on a full `pending_buf`, and keeps
`gzindex`. -/
theorem str_body_ret {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (sel : GzHeader → BPtr) (st : StrS) (notRet : st.ret = false) (begLe : st.beg.toNat ≤ d.pending.toNat)
    {st1 : StrS} {after : Heap} (run : strBody (some r) (some (.tab ds)) sel st h = .ok (st1, after))
    (ret : st1.ret = true) :
    d.pending.toNat = buf.size ∧ ∃ d1, after.dstates ds = some d1 ∧ d1.gzindex = d.gzindex := by
  have psize := trees.base.psize
  by_cases full : d.pending = d.pending_buf_size
  · have fullN : d.pending.toNat = buf.size := by rw [full, psize]
    refine ⟨fullN, ?_⟩
    obtain ⟨H2, z2, good2, trees2, buffers2, account2, frame2, run2⟩ :=
      hcrc_update good trees buffers globals record getg st.beg begLe
    have next2 : z2.next_out = z.next_out := by
      rw [account2.2.2.2.2.2.1]; cases z.next_out <;> rfl
    have out2 : z2.next_out ≠ .null := by rw [next2]; exact out
    obtain ⟨produced, H3, z3, d3, run3, good3, trees3, buffers3, account3, copied, left, fields3, empty3,
      _adler3, gz3, static3, _sizes3⟩ := header_flush good2 trees2 buffers2 low cursor out2
    by_cases zero : d3.pending = 0
    · exfalso
      have eq : strBody (some r) (some (.tab ds)) sel st h =
          strRead (some (.tab ds)) sel { st with beg := 0 } H3 := by
        unfold strBody
        simp only [bind_app, ldDeflateState_tab good.live.hs, full, beq_self_eq_true, ite_true]
        rw [run2]; simp only []
        rw [run3]
        simp only [rdD_eq, good3.live.hs, zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
      rw [eq] at run
      have := str_read_ret run
      rw [ret] at this
      exact absurd (this.trans notRet) (by decide)
    · have eq : strBody (some r) (some (.tab ds)) sel st h =
          .ok ({ st with ret := true }, setD H3 ds { d3 with last_flush := -1 }) := by
        unfold strBody
        simp only [bind_app, ldDeflateState_tab good.live.hs, full, beq_self_eq_true, ite_true]
        rw [run2]; simp only []
        rw [run3]
        simp [rdD_eq, good3.live.hs, zero, wrD_eq]
      rw [eq] at run
      cases run
      exact ⟨{ d3 with last_flush := -1 }, setD_dstates_same _ _ _,
        by have a := congrArg DeflateState.gzindex fields3; exact a⟩
  · exfalso
    have eq : strBody (some r) (some (.tab ds)) sel st h = strRead (some (.tab ds)) sel st h := by
      unfold strBody
      simp only [bind_app, ldDeflateState_tab good.live.hs, beq_eq_false_iff_ne.mpr full, Bool.false_eq_true,
        ite_false]
    rw [eq] at run
    have := str_read_ret run
    rw [ret, notRet] at this
    exact absurd this (by decide)

/-- `gzindex` at a loop head of the extra field: it has not decreased, and has grown once the loop
returned early. -/
def ExtraMono (ds : Nat) (d : DeflateState) (st : ExtraS) (H : Heap) : Prop :=
  ∃ e, H.dstates ds = some e ∧ d.gzindex.toNat ≤ e.gzindex.toNat ∧
    (st.ret = true → d.gzindex.toNat < e.gzindex.toNat)

/-- `gzindex` at a loop head of a string: it has not decreased, and from a stage entered with room
in `pending_buf`, `pending_buf` still has room while no byte was read. -/
def StrMono (ds : Nat) (d : DeflateState) (buf : Array UInt8) (H : Heap) : Prop :=
  ∃ e, H.dstates ds = some e ∧ d.gzindex.toNat ≤ e.gzindex.toNat ∧
    (d.pending.toNat < buf.size → e.gzindex.toNat = d.gzindex.toNat → e.pending.toNat < buf.size)

/-- The progress of an early return of the string loop. -/
def StrProg (ds : Nat) (d : DeflateState) (buf : Array UInt8) (st : StrS) (H : Heap) : Prop :=
  st.ret = true → d.pending.toNat < buf.size → ∃ e, H.dstates ds = some e ∧ d.gzindex.toNat < e.gzindex.toNat

theorem busy_flush_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      DGood after r ds z1 d1 ∧ (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧
      StreamBuffers after r ∧ StreamAccounting z z1 0 produced ∧
      (∀ i g, h.gzheaders i = some g → after.gzheaders i = some g) ∧ after.static = h.static ∧
      d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧ d1.pending_buf = d.pending_buf ∧
      d1.pending_buf_size = d.pending_buf_size ∧ HeaderShape d d1 ∧ StageFrame h after r ds pb d z z1 produced ∧
      z1.next_out ≠ .null ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧
      d1.pending.toNat + produced = d.pending.toNat ∧
      ((busyTail (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧ d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧
         d1.status ≠ FINISH_STATE ∧ z1.avail_out = 0) ∨
       (busyTail (some r) (some (.tab ds)) k h = k after ∧ d1.status = BUSY_STATE ∧ d1.pending = 0 ∧
         d1.pending_out = d1.pending_buf ∧ d1.last_flush = d.last_flush)) ∧
      d1.status = BUSY_STATE := by
  obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers BUSY_STATE (by simp [GoodStatus])
  obtain ⟨produced, H2, z2, d2, run2, good2, ⟨buf2, trees2, size2⟩, buffers2, account2, copied, left, fields2,
    empty2, _adler2, gz2, static2, _sizes2⟩ := header_flush good1 trees1 buffers1 low cursor out
  have keys : d2.gzhead = d.gzhead ∧ d2.bi_valid = d.bi_valid ∧ d2.pending_buf = d.pending_buf ∧
      d2.pending_buf_size = d.pending_buf_size ∧ d2.status = BUSY_STATE ∧ d2.last_flush = d.last_flush := by
    rw [fields2]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have out2 : z2.next_out ≠ .null := by rw [account2.2.2.2.2.2.1]; exact Call.advance_ne_null out _
  have shape2 : HeaderShape d d2 := HeaderShape.trans ⟨_, _, _, _, _, _, _, _, rfl⟩ ⟨_, _, _, _, _, _, _, _, fields2⟩
  have stage2 : StageFrame h H2 r ds pb d z z2 produced := by
    have s := StageFrame.trans (StageFrame.state good buffers trees.base.pbuf { d with status := BUSY_STATE })
      (StageFrame.of_flush good1 trees1 buffers1 low cursor out run2 good2.live.hz account2) (fun _ => Iff.rfl)
      good buffers
    rwa [Nat.zero_add] at s
  by_cases zero : d2.pending = 0
  · refine ⟨H2, z2, d2, produced, good2, ⟨buf2, trees2, size2⟩, buffers2, account2, gz2, static2, keys.1,
      keys.2.1, keys.2.2.1, keys.2.2.2.1, shape2, stage2, out2, copied, left, Or.inr ⟨?_, keys.2.2.2.2.1, zero, empty2 zero,
      keys.2.2.2.2.2⟩, keys.2.2.2.2.1⟩
    unfold busyTail
    simp only [bind_app, wrD_eq, good.live.hs]
    rw [run2]
    simp [rdD_eq, good2.live.hs, zero]
  · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good2 trees2 buffers2 (-1)
    refine ⟨_, z2, _, produced, good5, ⟨buf2, trees_at_buffer good5 trees2.base.pbuf trees2.base.bytes, size2⟩,
      buffers5, account2, (fun i g get => by rw [frame5.gzheaders]; exact gz2 i g get),
      (by rw [frame5.static, static2]; rfl),
      keys.1, keys.2.1, keys.2.2.1, keys.2.2.2.1, shape2.trans ⟨_, _, _, _, _, _, _, _, rfl⟩,
      by
        have s := StageFrame.trans stage2 (StageFrame.state good2 buffers2 trees2.base.pbuf { d2 with last_flush := -1 })
          (HeaderShape.owned shape2) good buffers
        rwa [Nat.add_zero] at s,
      out2, copied, left, Or.inl ⟨?_, zero, rfl, by show d2.status ≠ _; rw [keys.2.2.2.2.1]; decide,
        full_of_left account2 copied left (pending_toNat_ne zero)⟩, keys.2.2.2.2.1⟩
    unfold busyTail
    simp only [bind_app, wrD_eq, good.live.hs]
    rw [run2]
    simp [rdD_eq, good2.live.hs, zero, wrD_eq]


theorem hcrc_stage_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (status : d.status = HCRC_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      StageBase h r ds pb z d buf i g after z1 d1 produced ∧
      ((hcrcStage (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧
          d1.last_flush = -1 ∧ d1.pending ≠ 0 ∧ d1.status ≠ FINISH_STATE ∧ z1.avail_out = 0 ∧
          (d1.status = BUSY_STATE ∨ (d1.status = HCRC_STATE ∧ d.pending ≠ 0))) ∨
       (hcrcStage (some r) (some (.tab ds)) k h = k after ∧ d1.status = BUSY_STATE ∧ d1.pending = 0 ∧
         d1.pending_out = d1.pending_buf ∧ (produced = 0 → d.pending.toNat = 0) ∧ d1.last_flush = d.last_flush)) := by
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have st : (d.status == HCRC_STATE) = true := by rw [status]; rfl
  have psize := trees.base.psize
  have bufLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have bufHi : buf.size ≤ 131072 := by have := trees.base.size; have := trees.base.lit_hi; omega
  have stageEq : ∀ K : M Int32, hcrcStage (some r) (some (.tab ds)) K h =
      (if g.hcrc != 0 then hcrcBytes' (some r) (some (.tab ds)) d (busyTail (some r) (some (.tab ds)) K)
       else busyTail (some r) (some (.tab ds)) K) h := by
    intro K
    rw [hcrc_stage_split]
    unfold hcrcStage'
    simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg, hcrc_bytes_split]
  -- the busy flush from any state reached in the stage
  have finish : ∀ {H : Heap} {z2 : ZStream} {d2 : DeflateState} {buf2 : Array UInt8} {p2 : Nat},
      DGood H r ds z2 d2 → TreesInvAt H ds d2 pb buf2 → buf2.size = buf.size → StreamBuffers H r →
      StreamAccounting z z2 0 p2 → H.gzheaders i = some g → H.static = h.static →
      d2.gzhead = d.gzhead → d2.bi_valid = d.bi_valid → d2.pending_buf = d.pending_buf →
      d2.pending_buf_size = d.pending_buf_size → d2.pending_out = d2.pending_buf → z2.next_out ≠ .null →
      HeaderShape d d2 → StageFrame h H r ds pb d z z2 p2 → d2.last_flush = d.last_flush →
      (p2 = 0 → d2.pending.toNat = 0 → d.pending.toNat = 0) →
      ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
        StageBase h r ds pb z d buf i g after z1 d1 produced ∧
        ((busyTail (some r) (some (.tab ds)) k H = .ok (Z_OK, after) ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧
           d1.last_flush = -1 ∧ d1.pending ≠ 0 ∧ d1.status ≠ FINISH_STATE ∧ z1.avail_out = 0 ∧
           (d1.status = BUSY_STATE ∨ (d1.status = HCRC_STATE ∧ d.pending ≠ 0))) ∨
         (busyTail (some r) (some (.tab ds)) k H = k after ∧ d1.status = BUSY_STATE ∧ d1.pending = 0 ∧
           d1.pending_out = d1.pending_buf ∧ (produced = 0 → d.pending.toNat = 0) ∧ d1.last_flush = d.last_flush)) := by
    intro H z2 d2 buf2 p2 good2 trees2 size2 buffers2 account2 gz2 static2 gzhead2 bits2 pbuf2 pbs2 cursor2
      out2 shape2 stage2 lfd2 zeroP
    obtain ⟨H3, z3, d3, p3, good3, trees3, buffers3, account3, gz3, static3, gzhead3, bits3, pbuf3, pbs3, shape3,
      stage3, out3, produced3, left3, outcome, busy3⟩ := busy_flush_q good2 trees2 buffers2 cursor2 (by rw [bits2]; exact low) out2 k
    obtain ⟨buf3, trees3', size3⟩ := trees3
    have base : StageBase h r ds pb z d buf i g H3 z3 d3 (p2 + p3) :=
      ⟨good3, ⟨buf3, trees3', size3.trans size2⟩, buffers3, stream_accounting_trans account2 account3,
        gz3 i g gz2, static3.trans static2, gzhead3.trans gzhead2, bits3.trans bits2, pbuf3.trans pbuf2,
        pbs3.trans pbs2, out3, shape2.trans shape3, StageFrame.trans stage2 stage3 (HeaderShape.owned shape2) good buffers⟩
    have a2 := account2.2.2.2.1
    rcases outcome with ⟨run3, pend3, lf3, sf3, fo3⟩ | ⟨run3, status3, zero3, cursor3, lfc⟩
    · refine ⟨H3, z3, d3, p2 + p3, base, Or.inl ⟨run3, ?_, lf3, pend3, sf3, fo3, Or.inl busy3⟩⟩
      have pn : d3.pending.toNat ≠ 0 := fun e => pend3 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      by_cases a0 : z.avail_out.toNat = 0
      · exact Or.inr a0
      · left
        rw [produced3] at left3 ⊢
        omega
    · refine ⟨H3, z3, d3, p2 + p3, base, Or.inr ⟨run3, status3, zero3, cursor3, fun none => ?_, lfc.trans lfd2⟩⟩
      have z0 : d3.pending.toNat = 0 := by rw [zero3]; rfl
      exact zeroP (by omega) (by omega)
  by_cases crc : g.hcrc = 0
  · obtain ⟨after, z1, d1, produced, base, outcome⟩ := finish good trees rfl buffers (stream_accounting_zero z) getg rfl
      rfl rfl rfl rfl cursor out (HeaderShape.refl d) (StageFrame.refl good buffers trees.base.pbuf) rfl (fun _ e => e)
    refine ⟨after, z1, d1, produced, base, ?_⟩
    rw [stageEq]; simp only [crc, bne_self_eq_false, Bool.false_eq_true, ite_false]; exact outcome
  · have crcT : (g.hcrc != 0) = true := bne_iff_ne.mpr crc
    by_cases big : d.pending + 2 > d.pending_buf_size
    · have bigN : buf.size < d.pending.toNat + 2 := by
        have := UInt64.lt_iff_toNat_lt.mp big
        rw [UInt64.toNat_add, show (2 : UInt64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        omega
      have pendNZ : d.pending ≠ 0 := by
        intro e
        have : d.pending.toNat = 0 := by rw [e]; rfl
        omega
      obtain ⟨p1, H1, z1, d1, run1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, copied1, left1, fields1,
        empty1, _adler1, gz1, static1, _sizes1⟩ := header_flush good trees buffers low cursor out
      have keys1 : d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧ d1.pending_buf = d.pending_buf ∧
          d1.pending_buf_size = d.pending_buf_size := by
        rw [fields1]; exact ⟨rfl, rfl, rfl, rfl⟩
      have out1 : z1.next_out ≠ .null := by rw [account1.2.2.2.2.2.1]; exact Call.advance_ne_null out _
      by_cases zero : d1.pending = 0
      · obtain ⟨H2, z2, d2, buf2, run2, good2, trees2, size2, buffers2, account2, frame2, fields2, count2⟩ :=
          hcrc_put good1 trees1 buffers1 (empty1 zero) (by rw [zero, size1]; simp; omega)
            (busyTail (some r) (some (.tab ds)) k)
        have keys2 : d2.gzhead = d.gzhead ∧ d2.bi_valid = d.bi_valid ∧ d2.pending_buf = d.pending_buf ∧
            d2.pending_buf_size = d.pending_buf_size ∧ d2.pending_out = d2.pending_buf := by
          rw [fields2]; exact ⟨keys1.1, keys1.2.1, keys1.2.2.1, keys1.2.2.2, empty1 zero⟩
        obtain ⟨after, z3, d3, produced, base, outcome⟩ := finish good2 trees2 (size2.trans size1) buffers2
          (by simpa only [Nat.add_zero] using stream_accounting_trans account1 account2)
          (by rw [frame2.gzheaders]; exact gz1 i g getg) (by rw [frame2.static, static1])
          keys2.1 keys2.2.1 keys2.2.2.1 keys2.2.2.2.1 keys2.2.2.2.2
          (by rw [account2.2.2.2.2.2.1]; exact Call.advance_ne_null out1 _)
          (HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields1⟩ ⟨_, _, _, _, _, _, _, _, fields2⟩)
          (by
            have s := StageFrame.trans (StageFrame.of_flush good trees buffers low cursor out run1 good1.live.hz account1)
              (StageFrame.of_header frame2 good1 buffers1 trees1.base.pbuf account2 good2.live.hz)
              (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
            rwa [Nat.add_zero] at s)
          (by have a := congrArg DeflateState.last_flush fields2; have b := congrArg DeflateState.last_flush fields1; simp only at a b; rw [a, b])
          (fun none _ => by
            have z0 : d1.pending.toNat = 0 := by rw [zero]; rfl
            rw [copied1] at none left1; omega)
        refine ⟨after, z3, d3, produced, base, ?_⟩
        rw [stageEq]
        simp only [crcT, ite_true]
        unfold hcrcBytes'
        simp only [big, decide_true, ite_true, bind_app]
        rw [run1]
        simp only [rdD_eq, good1.live.hs, zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
        rw [run2]; exact outcome
      · obtain ⟨good5, buffers5, frame5⟩ := last_flush_frame (pb := pb) good1 trees1 buffers1 (-1)
        refine ⟨_, z1, _, p1, ⟨good5, ⟨buf1, trees_at_buffer good5 trees1.base.pbuf trees1.base.bytes, size1⟩,
          buffers5, account1, (by rw [frame5.gzheaders]; exact gz1 i g getg), (by rw [frame5.static, static1]),
          keys1.1, keys1.2.1, keys1.2.2.1, keys1.2.2.2, out1,
          HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields1⟩ ⟨_, _, _, _, _, _, _, _, rfl⟩,
          by
            have s := StageFrame.trans (StageFrame.of_flush good trees buffers low cursor out run1 good1.live.hz account1)
              (StageFrame.state good1 buffers1 trees1.base.pbuf { d1 with last_flush := -1 })
              (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
            rwa [Nat.add_zero] at s⟩, Or.inl ⟨?_, ?_, rfl, zero,
            by have a := congrArg DeflateState.status fields1; simp only at a; show d1.status ≠ _; rw [a, status]; decide,
            full_of_left account1 copied1 left1 (pending_toNat_ne zero),
            Or.inr ⟨by have a := congrArg DeflateState.status fields1; simp only at a; show d1.status = _; rw [a, status],
              pendNZ⟩⟩⟩
        · rw [stageEq]
          simp only [crcT, ite_true]
          unfold hcrcBytes'
          simp only [big, decide_true, ite_true, bind_app]
          rw [run1]
          simp [rdD_eq, good1.live.hs, zero, wrD_eq]
        · by_cases a0 : z.avail_out.toNat = 0
          · exact Or.inr a0
          · left; rw [copied1]; omega
    · have roomN : d.pending.toNat + 2 ≤ buf.size := by
        have := mt UInt64.lt_iff_toNat_lt.mpr big
        rw [UInt64.toNat_add, show (2 : UInt64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        omega
      obtain ⟨H2, z2, d2, buf2, run2, good2, trees2, size2, buffers2, account2, frame2, fields2, count2⟩ :=
        hcrc_put good trees buffers cursor roomN (busyTail (some r) (some (.tab ds)) k)
      have keys2 : d2.gzhead = d.gzhead ∧ d2.bi_valid = d.bi_valid ∧ d2.pending_buf = d.pending_buf ∧
          d2.pending_buf_size = d.pending_buf_size ∧ d2.pending_out = d2.pending_buf := by
        rw [fields2]; exact ⟨rfl, rfl, rfl, rfl, cursor⟩
      obtain ⟨after, z3, d3, produced, base, outcome⟩ := finish good2 trees2 size2 buffers2 account2
        (by rw [frame2.gzheaders]; exact getg) frame2.static
        keys2.1 keys2.2.1 keys2.2.2.1 keys2.2.2.2.1 keys2.2.2.2.2
        (by rw [account2.2.2.2.2.2.1]; exact Call.advance_ne_null out _)
        ⟨_, _, _, _, _, _, _, _, fields2⟩
        (StageFrame.of_header frame2 good buffers trees.base.pbuf account2 good2.live.hz)
        (by have a := congrArg DeflateState.last_flush fields2; simp only at a; rw [a])
        (fun _ e => by omega)
      refine ⟨after, z3, d3, produced, base, ?_⟩
      rw [stageEq]
      simp only [crcT, ite_true]
      unfold hcrcBytes'
      simp only [big, decide_false, ite_false]
      rw [run2]; exact outcome



theorem extra_loop_q {H0 H : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {i : Nat} {g : GzHeader} {rs : BRef} {eo : Nat} {ea : Array UInt8}
    (extra : g.extra = .ref rs eo) (other : rs ≠ .blk pb) (sizeLo : 1 ≤ buf.size)
    (left0 : Nat) (span : eo + d.gzindex.toNat + left0 ≤ ea.size)
    (small : d.gzindex.toNat + left0 < 2 ^ 16) (globals : LibraryGlobals H0)
    (good0 : DGood H0 r ds z d) (buffers0 : StreamBuffers H0 r)
    (record : d.gzhead = some (.tab i)) (low : d.bi_valid.toInt < 8) (psize : d.pending_buf_size.toNat = buf.size)
    (st : ExtraS) (head : ExtraHead H0 r ds pb z d buf i g rs ea left0 st H) (mono : ExtraMono ds d st H) :
    ∃ st' H', cwhile (extraCond (some (.tab ds))) (extraBody (some r) (some (.tab ds))) st H = .ok (st', H') ∧
      ExtraHead H0 r ds pb z d buf i g rs ea left0 st' H' ∧ ExtraMono ds d st' H' ∧
      (st'.ret = false → ∃ d', H'.dstates ds = some d' ∧ d'.pending.toNat + st'.left.toNat ≤ buf.size) := by
  refine cwhile_measure (fun st H => ExtraHead H0 r ds pb z d buf i g rs ea left0 st H ∧ ExtraMono ds d st H)
    (fun st' H' => ExtraHead H0 r ds pb z d buf i g rs ea left0 st' H' ∧ ExtraMono ds d st' H' ∧
      (st'.ret = false → ∃ d', H'.dstates ds = some d' ∧ d'.pending.toNat + st'.left.toNat ≤ buf.size))
    (fun st H => if st.ret then 0 else st.left.toNat + 1) ?_ ⟨head, mono⟩ (by
      unfold fuel; split
      · omega
      · rename_i notRet
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rest⟩ := head
        have := (rest (by simpa using notRet)).1
        omega)
  rintro st H ⟨inv, monoI⟩
  have inv0 := inv
  obtain ⟨z1, d1, p1, buf1, ea1, good1, trees1, bufSize1, buffers1, account1, gz1, static1, view1, eaSize1,
    status1, gzhead1, bits1, pbuf1, pbs1, out1, keep1, shape1, stage1, retFacts1, headFacts1⟩ := inv
  have bufHi : buf1.size ≤ 131072 := by have := trees1.base.size; have := trees1.base.lit_hi; omega
  have bufLo : 512 ≤ buf1.size := by have := trees1.base.size; have := trees1.base.lit_lo; omega
  have sizes1 : d1.pending_buf_size.toNat = buf1.size := trees1.base.psize
  refine ⟨_, st, H, extra_cond_run good1.live.hs st, ?_, ?_⟩
  · intro c
    have cond : st.ret = false ∧ d1.pending + st.left > d1.pending_buf_size := by
      simpa using c
    obtain ⟨notRet, gt⟩ := cond
    obtain ⟨idx1, cursor1, beg1, below1, last1, zero1⟩ := headFacts1 notRet
    have noWrap : d1.pending.toNat + st.left.toNat < 2 ^ 64 := by omega
    have more1 : buf1.size < d1.pending.toNat + st.left.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp gt
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap] at this
      omega
    have globals1 : LibraryGlobals H := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    obtain ⟨st2, H2, z2, d2, p2, run2, good2, buffers2, account2, trees2, produced2, drained2, gz2, static2,
      view2, status2, gzhead2, bits2, pbuf2, pbs2, idx2, ret2, cont2, out2, keepB, shapeB, stageB⟩ :=
      extra_body good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1
        (by rw [gzhead1]; exact record) gz1 extra view1 other st notRet
        (by omega) beg1 (by omega) more1 (by omega)
    obtain ⟨buf2, trees2', size2⟩ := trees2
    obtain ⟨ea2, view2', eaSize2⟩ := view2
    have avail1 : z1.avail_out.toNat + p1 = z.avail_out.toNat := account1.2.2.2.1
    refine ⟨st2, H2, run2, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨z2, d2, p1 + p2, buf2, ea2, good2, trees2', size2.trans bufSize1, buffers2,
        stream_accounting_trans account1 account2, gz2, static2.trans static1, view2', eaSize2.trans eaSize1,
        status2.trans status1, gzhead2.trans gzhead1, bits2.trans bits1, pbuf2.trans pbuf1, pbs2.trans pbs1,
        out2, keep1.trans keepB account1, shape1.trans shapeB,
        StageFrame.trans stage1 stageB (HeaderShape.owned shape1) good0 buffers0, ?_, ?_⟩
      · intro retTrue
        obtain ⟨pend2, lf2⟩ := ret2 retTrue
        refine ⟨pend2, lf2, ?_, full_of_left account2 produced2 drained2 (pending_toNat_ne pend2)⟩
        by_cases zeroAvail : z.avail_out.toNat = 0
        · exact Or.inr zeroAvail
        · left
          rw [produced2]
          omega
      · intro retFalse
        obtain ⟨pend2, cur2, lf2, beg2, left2⟩ := cont2 retFalse
        refine ⟨by omega, cur2, by rw [beg2]; simp, by rw [pend2]; simp; omega, lf2.trans last1, ?_⟩
        intro none
        exfalso
        have : p2 = 0 := by omega
        rw [pend2] at drained2
        simp at drained2
        omega
    · obtain ⟨e1, hs1, le1, _⟩ := monoI
      have same : e1 = d1 := Option.some.inj (hs1.symm.trans good1.live.hs)
      subst same
      exact ⟨d2, good2.live.hs, by omega, fun _ => by omega⟩
    · show (if st2.ret then 0 else st2.left.toNat + 1) < (if st.ret then 0 else st.left.toNat + 1)
      rw [notRet]
      cases e : st2.ret
      · obtain ⟨_, _, _, _, left2⟩ := cont2 e
        simp only [Bool.false_eq_true, ite_false]
        omega
      · simp
  · intro c
    refine ⟨inv0, monoI, fun notRet => ⟨d1, good1.live.hs, ?_⟩⟩
    have no : ¬ (d1.pending + st.left > d1.pending_buf_size) := by
      intro gt; simp [notRet, gt] at c
    obtain ⟨idx1, _, _, below1, _, _⟩ := headFacts1 notRet
    have noWrap : d1.pending.toNat + st.left.toNat < 2 ^ 64 := by omega
    have := mt UInt64.lt_iff_toNat_lt.mpr no
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap] at this
    omega


theorem extra_stage_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = EXTRA_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (extraMem : g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
      eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb)
    (progress : g.extra ≠ .null → d.gzindex.toNat ≤ g.extra_len.toNat % 2 ^ 16)
    (below : d.pending.toNat < buf.size) (k : M Int32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
      after.gzheaders i = some g ∧ after.static = h.static ∧ z'.next_out ≠ .null ∧
      CallerKeep h after z ds pb ∧ HeaderShape d d' ∧ StageFrame h after r ds pb d z z' produced ∧
      d'.gzhead = d.gzhead ∧ d'.bi_valid = d.bi_valid ∧
      ((extraStage (some r) (some (.tab ds)) k h = .ok (Z_OK, after) ∧
          (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧ d'.last_flush = -1 ∧ d'.pending ≠ 0 ∧ d'.status ≠ FINISH_STATE ∧
          z'.avail_out = 0 ∧ d'.status = d.status ∧ d.gzindex.toNat < d'.gzindex.toNat) ∨
       (extraStage (some r) (some (.tab ds)) k h = k after ∧ d'.status = NAME_STATE ∧
          d'.pending_out = d'.pending_buf ∧ d'.pending.toNat ≤ buf.size ∧
          (produced = 0 → d.pending.toNat ≤ d'.pending.toNat) ∧
          (d'.gzindex = 0 ∨ (g.extra = .null ∧ d'.gzindex = d.gzindex)) ∧ d'.last_flush = d.last_flush)) := by
  have psize := trees.base.psize
  have sizeLo : 1 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have extraState : (d.status == EXTRA_STATE) = true := by rw [status]; rfl
  by_cases ex : g.extra = .null
  · obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers NAME_STATE (by simp [GoodStatus])
    refine ⟨0, _, z, _, good1, buffers1, stream_accounting_zero z, ⟨buf, trees1, rfl⟩, getg, rfl, out,
      CallerKeep.of_frame (HeaderFrame.state (r := r) pb good.live.hs _ rfl), ⟨_, _, _, _, _, _, _, _, rfl⟩,
      StageFrame.state good buffers trees.base.pbuf _, rfl, rfl,
      Or.inr ⟨?_, rfl, cursor, (by change d.pending.toNat ≤ buf.size; omega), fun _ => Nat.le_refl _,
        Or.inr ⟨ex, rfl⟩, rfl⟩⟩
    rw [extra_stage_split]
    unfold extraStage'
    simp only [bind_app, rdD_eq, good.live.hs, extraState, ite_true, ldDeflateState_tab good.live.hs, ldg,
      ex, bne_self_eq_false, Bool.false_eq_true, ite_false, wrD_eq]
  · obtain ⟨rs, eo, ea, extra, srcGet, span, other⟩ := extraMem ex
    have idx0 := progress ex
    let L := g.extra_len.toNat % 2 ^ 16
    have Lsmall : L < 2 ^ 16 := Nat.mod_lt _ (by decide)
    let st0 : ExtraS := { beg := d.pending, left := (g.extra_len &&& 0xffff).toUInt64 - d.gzindex, ret := false }
    have left0 : st0.left.toNat = L - d.gzindex.toNat := by
      change ((g.extra_len &&& 0xffff).toUInt64 - d.gzindex).toNat = _
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [extra_len_mask]; exact idx0)),
        extra_len_mask]
    have head0 : ExtraHead h r ds pb z d buf i g rs ea (L - d.gzindex.toNat) st0 h :=
      ⟨z, d, 0, buf, ea, good, trees, rfl, buffers, stream_accounting_zero z, getg, rfl, srcGet, rfl,
        rfl, rfl, rfl, rfl, rfl, out, CallerKeep.refl h z ds pb, HeaderShape.refl d,
        StageFrame.refl good buffers trees.base.pbuf, (fun e => Bool.noConfusion e),
        fun _ => ⟨(by rw [left0]), cursor, Nat.le_refl _, below, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩⟩
    obtain ⟨st1, H1, runL, head1, mono1, exit1⟩ :=
      extra_loop_q extra other sizeLo (L - d.gzindex.toNat) (by omega) (by omega) globals good buffers record low psize st0 head0
        ⟨d, good.live.hs, Nat.le_refl _, fun e => Bool.noConfusion e⟩
    have stageEq : extraStage (some r) (some (.tab ds)) k h =
        extraCopy (some r) (some (.tab ds)) d g (do
          wr (some (.tab ds)) (fun d => { d with status := NAME_STATE })
          k) h := by
      rw [extra_stage_split]
      unfold extraStage'
      simp only [bind_app, rdD_eq, good.live.hs, extraState, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.extra != .null) = true from bne_iff_ne.mpr ex]
    obtain ⟨z1, d1, p1, buf1, ea1, good1, trees1, bufSize1, buffers1, account1, gz1, static1, view1, eaSize1,
      status1, gzhead1, bits1, pbuf1, pbs1, out1, keep1, shape1, stage1, retFacts1, headFacts1⟩ := head1
    cases ret1 : st1.ret
    · obtain ⟨idx1, cursor1, beg1, below1, last1, zero1⟩ := headFacts1 ret1
      obtain ⟨d1', state1', fits1⟩ := exit1 ret1
      have same1 : d1 = d1' := Option.some.inj (good1.live.hs.symm.trans state1')
      subst same1
      have pbuf1' := trees1.base.pbuf
      have small1 : st1.left.toNat < 2 ^ 16 := by omega
      have ldg1 : ldGzHeader d1.gzhead H1 = .ok (g, H1) := by
        rw [gzhead1, record]; simp only [ldGzHeader, GzHeaderRef.get, gz1]
      have pp1 : padd d1.pending_buf d1.pending.toNat H1 = .ok (.ref (.blk pb) d1.pending.toNat, H1) := by
        rw [pbuf1']
        have := padd_ok' (r := BRef.blk pb) (off := 0) (n := d1.pending.toNat) (h := H1) trees1.base.bytes
          (by omega)
        simpa using this
      have pe1 : padd g.extra d1.gzindex.toNat H1 = .ok (.ref rs (eo + d1.gzindex.toNat), H1) := by
        rw [extra]; exact padd_ok' view1 (by omega)
      have noWrap : d1.pending.toNat + st1.left.toNat < 2 ^ 64 := by
        have := trees1.base.size; have := trees1.base.lit_hi; omega
      obtain ⟨run2, good2, trees2, buffers2, frame2, size2⟩ :=
        pending_copy (os := eo + d1.gzindex.toNat) good1 trees1 buffers1 cursor1 view1 other st1.left.toNat
          (by omega) (by omega) (d1.pending + st1.left)
          (by rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap])
      let d2 : DeflateState := { d1 with pending := d1.pending + st1.left }
      have count2 : d2.pending.toNat = d1.pending.toNat + st1.left.toNat := by
        change (d1.pending + st1.left).toNat = _; rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap]
      have globals2 : LibraryGlobals (setD (Zlib.Trees.Proofs.Out.setB H1 pb
          (copyRange buf1 ea1 d1.pending.toNat (eo + d1.gzindex.toNat) st1.left.toNat)) ds d2) := by
        unfold LibraryGlobals at globals ⊢; rw [frame2.static, static1, globals]
      obtain ⟨H3, z3, good3, trees3, buffers3, account3, frame3, run3⟩ :=
        hcrc_update good2 trees2 buffers2 globals2 (i := i) (by change d1.gzhead = _; rw [gzhead1, record])
          (by rw [frame2.gzheaders, gz1]) st1.beg (by rw [count2]; omega)
      obtain ⟨good4, trees4, buffers4, frame4⟩ := gzindex_engine good3 trees3 buffers3 0
      obtain ⟨good5, trees5, buffers5⟩ := status_engine good4 trees4 buffers4 NAME_STATE (by simp [GoodStatus])
      have accountT : StreamAccounting z z3 0 p1 := by
        simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans account1 account3
      have frameT := ((frame2.trans frame3).trans frame4).trans
        (HeaderFrame.state (r := r) pb good4.live.hs { d2 with gzindex := 0, status := NAME_STATE } rfl)
      refine ⟨p1, _, z3, _, good5, buffers5, accountT, ⟨_, trees5, size2.trans bufSize1⟩, ?_, ?_, ?_,
        keep1.trans ((CallerKeep.of_frame (((frame2.trans frame3).trans frame4).trans
          (HeaderFrame.state (r := r) pb good4.live.hs _ rfl)))) account1,
        shape1.trans ⟨_, _, _, _, _, _, _, _, rfl⟩, ?_, ?_, ?_,
        Or.inr ⟨?_, rfl, cursor1, ?_, ?_, Or.inl rfl, last1⟩⟩
      · rw [frameT.gzheaders, gz1]
      · rw [frameT.static, static1]
      · rw [account3.2.2.2.2.2.1]; exact Call.advance_ne_null out1 _
      · have s := StageFrame.trans stage1
          (StageFrame.of_header frameT good1 buffers1 trees1.base.pbuf account3 good5.live.hz)
          (HeaderShape.owned shape1) good buffers
        rwa [Nat.add_zero] at s
      · exact gzhead1
      · exact bits1
      · rw [stageEq]
        unfold extraCopy
        simp only [bind_app]
        rw [runL]
        simp only [ret1, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab good1.live.hs, ldg1, pp1, pe1]
        rw [run2]
        simp only [wrD_eq, show (Zlib.Trees.Proofs.Out.setB H1 pb (copyRange buf1 ea1 d1.pending.toNat
          (eo + d1.gzindex.toNat) st1.left.toNat)).dstates ds = some d1 from good1.live.hs]
        rw [run3]
        simp only [wrD_eq, good3.live.hs]
        simp [setD_dstates_same]
      · change d2.pending.toNat ≤ buf.size; rw [count2]; omega
      · intro none
        obtain ⟨e1, _, _⟩ := zero1 none
        change d.pending.toNat ≤ d2.pending.toNat
        rw [count2, e1]; omega
    · obtain ⟨pend1, lf1, del1, full1⟩ := retFacts1 ret1
      have prog1 : d.gzindex.toNat < d1.gzindex.toNat := by
        obtain ⟨e1, hs1, _, lt1⟩ := mono1
        have same : e1 = d1 := Option.some.inj (hs1.symm.trans good1.live.hs)
        subst same
        exact lt1 ret1
      refine ⟨p1, H1, z1, d1, good1, buffers1, account1, ⟨buf1, trees1, bufSize1⟩, gz1, static1, out1, keep1,
        shape1, stage1, gzhead1, bits1, Or.inl ⟨?_, del1, lf1, pend1, by rw [status1, status]; decide, full1, status1, prog1⟩⟩
      rw [stageEq]
      unfold extraCopy
      simp only [bind_app]
      rw [runL]
      simp [ret1, pure_app]


theorem string_loop_q {H0 H : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} {i : Nat} {g : GzHeader} (sel : GzHeader → BPtr) {xs : List UInt8}
    (cstring : 0 ∉ xs ∧ xs.length < 2 ^ 64) (globals : LibraryGlobals H0) (good0 : DGood H0 r ds z d)
    (buffers0 : StreamBuffers H0 r) (low : d.bi_valid.toInt < 8)
    (record : d.gzhead = some (.tab i)) (keys : ∀ b, ByteRoot (sel g) b → b ≠ pb ∧ b ≠ ds) (st : StrS) (head : StrHead H0 r ds pb z d buf i g sel xs st H)
    (mono : StrMono ds d buf H) :
    ∃ st' H', cdoWhile (strBody (some r) (some (.tab ds)) sel) strCond st H = .ok (st', H') ∧
      StrEnd H0 r ds pb z d buf i g st' H' ∧ StrProg ds d buf st' H' := by
  refine cdoWhile_measure (fun st H => StrHead H0 r ds pb z d buf i g sel xs st H ∧ StrMono ds d buf H)
    (fun st H => StrEnd H0 r ds pb z d buf i g st H ∧ StrProg ds d buf st H)
    (fun _ H => match H.dstates ds with | some e => xs.length - e.gzindex.toNat | none => 0) ?_ ⟨head, mono⟩ ?_
  · rintro st H ⟨inv, monoI⟩
    obtain ⟨notRet, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1,
      gzhead1, bits1, pbuf1, pbs1, out1, keep1, shape1, stage1⟩, cursor1, beg1, pend1, last1, gzLe1, unread1, apart1,
      zero1⟩ := inv
    have globals1 : LibraryGlobals H := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    obtain ⟨st2, H2, z2, d2, p2, run2, good2, buffers2, account2, trees2, gz2, static2, status2, gzhead2, bits2,
      pbuf2, pbs2, out2, keepB, shapeB, stageB, ret2, cont2⟩ :=
      str_body good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1
        (by rw [gzhead1]; exact record) gz1 sel gzLe1 unread1 apart1 keys st notRet beg1 (by omega)
    have base2 : StrBase H0 r ds pb z d buf i g H2 z2 d2 (p1 + p2) := by
      obtain ⟨b2, t2, s2⟩ := trees2
      exact ⟨good2, ⟨b2, t2, s2.trans size1⟩, buffers2, stream_accounting_trans account1 account2, gz2,
        static2.trans static1, status2.trans status1, gzhead2.trans gzhead1, bits2.trans bits1,
        pbuf2.trans pbuf1, pbs2.trans pbs1, out2, keep1.trans keepB account1, shape1.trans shapeB,
        StageFrame.trans stage1 stageB (HeaderShape.owned shape1) good0 buffers0⟩
    have avail1 : z1.avail_out.toNat + p1 = z.avail_out.toNat := account1.2.2.2.1
    cases eRet : st2.ret
    · obtain ⟨c, cEq, val2, idx2, cursor2, beg2, pend2, last2, zero2, unread2, apart2⟩ := cont2 eRet
      by_cases atEnd : d1.gzindex.toNat = xs.length
      · have c0 : c = 0 := by
          rw [atEnd] at cEq; simp at cEq; exact cEq.symm
        refine ⟨st2, H2, false, st2, H2, run2, ?_, fun e => Bool.noConfusion e, fun _ => ?_⟩
        · unfold strCond; simp [eRet, val2, c0, pure_app]
        · refine ⟨⟨z2, d2, p1 + p2, base2, fun e => Bool.noConfusion (eRet.symm.trans e), fun _ =>
            ⟨cursor2, beg2, by rw [← size1]; exact pend2, last2.trans last1, fun none => ?_⟩⟩,
            fun e => Bool.noConfusion (eRet.symm.trans e)⟩
          have q1 : p1 = 0 := by omega
          have q2 : p2 = 0 := by omega
          have := zero2 q2; have := zero1 q1; omega
      · have lt : d1.gzindex.toNat < xs.length := by omega
        have cNe : c ≠ 0 := by
          intro c0
          rw [List.getElem?_append_left lt] at cEq
          exact cstring.1 (c0 ▸ List.mem_of_getElem? cEq)
        have idxN : d2.gzindex.toNat = d1.gzindex.toNat + 1 := by
          rw [idx2, UInt64.toNat_add]; simp; omega
        have monoN : StrMono ds d buf H2 := by
          obtain ⟨e1, hs1, le1, _⟩ := monoI
          have same : e1 = d1 := Option.some.inj (hs1.symm.trans good1.live.hs)
          subst same
          exact ⟨d2, good2.live.hs, by omega, fun _ eq => absurd eq (by omega)⟩
        refine ⟨st2, H2, true, st2, H2, run2, ?_, fun _ => ⟨⟨⟨eRet, z2, d2, p1 + p2, base2, cursor2, beg2,
          by rw [← size1]; exact pend2,
          last2.trans last1, by omega, ?_, ?_, fun none => ?_⟩, monoN⟩, ?_⟩, fun e => Bool.noConfusion e⟩
        · unfold strCond
          have : (st2.val != 0) = true := by
            rw [val2]; exact bne_iff_ne.mpr (fun e => cNe (toInt32_eq_zero.mp e))
          simp [eRet, this, pure_app]
        · rw [idxN]
          have := bytes_later unread2 (k := 1) (by omega)
          rw [advance_advance, List.drop_drop] at this
          simpa [Nat.add_comm, Nat.sub_sub] using this
        · rw [idxN, ← advance_advance]
          have := separate_later apart2 (k := 1) (by omega)
          simpa [Nat.sub_sub] using this
        · have q1 : p1 = 0 := by omega
          have q2 : p2 = 0 := by omega
          have := zero2 q2; have := zero1 q1; omega
        · simp only [good1.live.hs, good2.live.hs]
          omega
    · obtain ⟨pend2, lf2, del2, full2⟩ := ret2 eRet
      have progT : StrProg ds d buf st2 H2 := by
        intro _ lt
        obtain ⟨full1, e2, hs2, gz2eq⟩ := str_body_ret good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1
          globals1 (by rw [gzhead1]; exact record) gz1 sel st notRet beg1 run2 eRet
        obtain ⟨e1, hs1, le1, imp1⟩ := monoI
        have same : e1 = d1 := Option.some.inj (hs1.symm.trans good1.live.hs)
        subst same
        refine ⟨e2, hs2, ?_⟩
        rw [gz2eq]
        have ne : e1.gzindex.toNat ≠ d.gzindex.toNat := fun eq => by have := imp1 lt eq; omega
        omega
      refine ⟨st2, H2, false, st2, H2, run2, ?_, fun e => Bool.noConfusion e, fun _ => ?_⟩
      · unfold strCond; simp [eRet, pure_app]
      · refine ⟨⟨z2, d2, p1 + p2, base2, fun _ => ⟨pend2, lf2, ?_, full2⟩, fun e => Bool.noConfusion (eRet.symm.trans e)⟩,
          progT⟩
        rcases del2 with d | d
        · left; omega
        · by_cases a0 : z.avail_out.toNat = 0
          · exact Or.inr a0
          · left
            have := account2.2.1
            omega
  · obtain ⟨_, z1, d1, p1, ⟨good1, _⟩, _⟩ := head
    simp only [good1.live.hs]
    unfold fuel
    omega

/-- **`gz_string_loop`**: copy the name or comment through its NUL, with the header CRC. It returns
`true` exactly at an early return, with bytes pending (a byte delivered, or no output room). -/
theorem string_copy_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (sel : GzHeader → BPtr) {xs : List UInt8} (cstring : 0 ∉ xs ∧ xs.length < 2 ^ 64)
    (gzLe : d.gzindex.toNat ≤ xs.length)
    (unread : Bytes h (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
      ((xs ++ [0]).drop d.gzindex.toNat))
    (apart : Separate (advance (sel g) d.gzindex.toNat) (xs.length + 1 - d.gzindex.toNat)
      z.next_out z.avail_out.toNat)
    (keys : ∀ b, ByteRoot (sel g) b → b ≠ pb ∧ b ≠ ds) (pendLe : d.pending.toNat ≤ buf.size) :
    ∃ (early : Bool) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      gz_string_loop (some r) (some (.tab ds)) sel h = .ok (early, after) ∧
      StrBase h r ds pb z d buf i g after z1 d1 produced ∧
      (early = true → d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧
        z1.avail_out = 0) ∧
      (early = false → d1.pending_out = d1.pending_buf ∧ d1.pending.toNat ≤ buf.size ∧
        d1.last_flush = d.last_flush ∧ (produced = 0 → d.pending.toNat + 1 ≤ d1.pending.toNat)) ∧
      (early = true → d.pending.toNat < buf.size → d.gzindex.toNat < d1.gzindex.toNat) := by
  let st0 : StrS := { beg := d.pending, val := 0, ret := false }
  have head : StrHead h r ds pb z d buf i g sel xs st0 h :=
    ⟨rfl, z, d, 0, ⟨good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z, getg, rfl, rfl, rfl, rfl, rfl, rfl,
      out, CallerKeep.refl h z ds pb, HeaderShape.refl d, StageFrame.refl good buffers trees.base.pbuf⟩, cursor, Nat.le_refl _, pendLe, rfl, gzLe, unread, apart, fun _ => Nat.le_refl _⟩
  obtain ⟨st1, H1, runL, ⟨z1, d1, p1, base1, ret1, cont1⟩, prog1⟩ :=
    string_loop_q sel cstring globals good buffers low record keys st0 head
      ⟨d, good.live.hs, Nat.le_refl _, fun lt _ => lt⟩
  obtain ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1, gzhead1, bits1, pbuf1,
    pbs1, out1, keep1, shape1, stage1⟩ := base1
  have split : gz_string_loop (some r) (some (.tab ds)) sel h =
      (do
        let st ← cdoWhile (strBody (some r) (some (.tab ds)) sel) strCond st0
        if st.ret then return true
        HCRC_UPDATE (some r) (some (.tab ds)) st.beg
        return false) h := by
    rw [string_loop_split]
    simp only [bind_app, rdD_eq, good.live.hs]
    rfl
  cases e : st1.ret
  · obtain ⟨cursor1, beg1, pend1, last1, zero1⟩ := cont1 e
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    obtain ⟨H2, z2, good2, trees2, buffers2, account2, frame2, run2⟩ :=
      hcrc_update good1 trees1 buffers1 globals1 (by rw [gzhead1]; exact record) gz1 st1.beg beg1
    refine ⟨false, H2, z2, d1, p1, ?_, ⟨good2, ⟨buf1, trees2, size1⟩, buffers2, ?_, ?_, ?_, status1, gzhead1,
      bits1, pbuf1, pbs1, ?_, keep1.trans (CallerKeep.of_frame frame2) account1, shape1, ?_⟩, fun e => Bool.noConfusion e,
      fun _ => ⟨cursor1, pend1, last1, zero1⟩, fun e => Bool.noConfusion e⟩
    · rw [split]; simp only [bind_app, runL, e, Bool.false_eq_true, ite_false, run2, pure_app]
    · simpa only [Nat.add_zero] using stream_accounting_trans account1 account2
    · rw [frame2.gzheaders]; exact gz1
    · rw [frame2.static]; exact static1
    · rw [account2.2.2.2.2.2.1]; exact Call.advance_ne_null out1 _
    · have s := StageFrame.trans stage1
        (StageFrame.of_header frame2 good1 buffers1 trees1.base.pbuf account2 good2.live.hz)
        (HeaderShape.owned shape1) good buffers
      rwa [Nat.add_zero] at s
  · refine ⟨true, H1, z1, d1, p1, ?_, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1,
      gzhead1, bits1, pbuf1, pbs1, out1, keep1, shape1, stage1⟩, fun _ => ret1 e, fun e => Bool.noConfusion e,
      fun _ lt => by
        obtain ⟨e1, hs1, lt1⟩ := prog1 e lt
        have same : e1 = d1 := Option.some.inj (hs1.symm.trans good1.live.hs)
        rw [← same]; exact lt1⟩
    rw [split]; simp only [bind_app, runL, e, ite_true, pure_app]


theorem string_ready_copy_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (sel : GzHeader → BPtr) (ready : StringReady h z d ds pb (sel g)) (present : sel g ≠ .null)
    (pendLe : d.pending.toNat ≤ buf.size) :
    ∃ (early : Bool) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      gz_string_loop (some r) (some (.tab ds)) sel h = .ok (early, after) ∧
      StrBase h r ds pb z d buf i g after z1 d1 produced ∧
      (early = true → d1.pending ≠ 0 ∧ d1.last_flush = -1 ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧
        z1.avail_out = 0) ∧
      (early = false → d1.pending_out = d1.pending_buf ∧ d1.pending.toNat ≤ buf.size ∧
        d1.last_flush = d.last_flush ∧ (produced = 0 → d.pending.toNat + 1 ≤ d1.pending.toNat)) ∧
      (early = true → d.pending.toNat < buf.size → d.gzindex.toNat < d1.gzindex.toNat) := by
  obtain ⟨xs, cs, gzLe, apart, keys⟩ := ready present
  exact string_copy_q good trees buffers cursor low out globals record getg sel ⟨cs.2.1, cs.2.2⟩ gzLe
    (bytes_later cs.1 (k := d.gzindex.toNat) (by omega)) (separate_later apart (by omega)) keys pendLe

/-- `StageOut` with the facts of the early return: the status is kept, and `gzindex` grew when the
stage was entered with room in `pending_buf`. -/
def StageOutQ (H0 : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (i : Nat) (g : GzHeader) (next : Int32) (run : Except Fault (Int32 × Heap))
    (k : M Int32) : Prop :=
  ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
    StageBase H0 r ds pb z d buf i g after z1 d1 produced ∧ CallerKeep H0 after z ds pb ∧
    ((run = .ok (Z_OK, after) ∧ (1 ≤ produced ∨ z.avail_out.toNat = 0) ∧ d1.last_flush = -1 ∧ d1.pending ≠ 0 ∧
       d1.status ≠ FINISH_STATE ∧ z1.avail_out = 0 ∧ d1.status = d.status ∧
       (d.pending.toNat < buf.size → d.gzindex.toNat < d1.gzindex.toNat)) ∨
     (run = k after ∧ d1.status = next ∧ d1.pending_out = d1.pending_buf ∧ d1.pending.toNat ≤ buf.size ∧
       (produced = 0 → d.pending.toNat ≤ d1.pending.toNat) ∧
       (next = COMMENT_STATE → (g.name ≠ .null → d1.gzindex = 0) ∧ (g.name = .null → d1.gzindex = d.gzindex)) ∧
       d1.last_flush = d.last_flush))

theorem name_stage_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = NAME_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.name) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    StageOutQ h r ds pb z d buf i g COMMENT_STATE (nameStage (some r) (some (.tab ds)) k h) k := by
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have st : (d.status == NAME_STATE) = true := by rw [status]; rfl
  by_cases present : g.name = .null
  · obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers COMMENT_STATE (by simp [GoodStatus])
    refine ⟨_, z, _, 0, ⟨good1, ⟨buf, trees1, rfl⟩, buffers1, stream_accounting_zero z, getg, rfl, rfl, rfl,
      rfl, rfl, out, ⟨_, _, _, _, _, _, _, _, rfl⟩, StageFrame.state good buffers trees.base.pbuf _⟩,
      CallerKeep.of_frame (HeaderFrame.state (r := r) pb good.live.hs _ rfl),
      Or.inr ⟨?_, rfl, cursor, pendLe, fun _ => Nat.le_refl _, fun _ => ⟨fun e => absurd present e, fun _ => rfl⟩, rfl⟩⟩
    unfold nameStage
    simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg, present,
      bne_self_eq_false, Bool.false_eq_true, ite_false, wrD_eq]
  · obtain ⟨early, H1, z1, d1, p1, run1, base1, ret1, cont1, prog1⟩ :=
      string_ready_copy_q good trees buffers cursor low out globals record getg (·.name) ready present pendLe
    obtain ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1, gzhead1, bits1, pbuf1,
      pbs1, out1, keep1, shape1, stage1⟩ := base1
    cases early
    · obtain ⟨cursor1, pend1, last1, zero1⟩ := cont1 rfl
      obtain ⟨good2, trees2, buffers2, frame2⟩ := gzindex_engine good1 trees1 buffers1 0
      obtain ⟨good3, trees3, buffers3⟩ := status_engine good2 trees2 buffers2 COMMENT_STATE (by simp [GoodStatus])
      refine ⟨_, z1, _, p1, ⟨good3, ⟨buf1, trees3, size1⟩, buffers3, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1, shape1.trans ⟨_, _, _, _, _, _, _, _, rfl⟩,
        by
          have s := StageFrame.trans stage1 (StageFrame.of_header (frame2.trans
            (HeaderFrame.state (r := r) pb good2.live.hs
              ({ ({ d1 with gzindex := 0 } : DeflateState) with status := COMMENT_STATE } : DeflateState) rfl))
            good1 buffers1 trees1.base.pbuf (stream_accounting_zero z1) good3.live.hz) (HeaderShape.owned shape1)
            good buffers
          rwa [Nat.add_zero] at s⟩, keep1.trans (CallerKeep.of_frame (frame2.trans
          (HeaderFrame.state (r := r) pb good2.live.hs _ rfl))) account1, Or.inr ⟨?_, rfl, cursor1, pend1,
        fun none => (by have := zero1 none; change d.pending.toNat ≤ d1.pending.toNat; omega),
        fun _ => ⟨fun _ => rfl, fun e => absurd e present⟩, last1⟩⟩
      unfold nameStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.name != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [wrD_eq, good1.live.hs]
    · refine ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1, shape1, stage1⟩, keep1, Or.inl ⟨?_, (ret1 rfl).2.2.1, (ret1 rfl).2.1, (ret1 rfl).1, by rw [status1, status]; decide,
          (ret1 rfl).2.2.2, status1, prog1 rfl⟩⟩
      unfold nameStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.name != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [pure_app]

/-- **The gzip comment stage.** -/
theorem comment_stage_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = COMMENT_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    StageOutQ h r ds pb z d buf i g HCRC_STATE (commentStage (some r) (some (.tab ds)) k h) k := by
  have ldg : ldGzHeader d.gzhead h = .ok (g, h) := by
    rw [record]; simp only [ldGzHeader, GzHeaderRef.get, getg]
  have st : (d.status == COMMENT_STATE) = true := by rw [status]; rfl
  by_cases present : g.comment = .null
  · obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers HCRC_STATE (by simp [GoodStatus])
    refine ⟨_, z, _, 0, ⟨good1, ⟨buf, trees1, rfl⟩, buffers1, stream_accounting_zero z, getg, rfl, rfl, rfl,
      rfl, rfl, out, ⟨_, _, _, _, _, _, _, _, rfl⟩, StageFrame.state good buffers trees.base.pbuf _⟩,
      CallerKeep.of_frame (HeaderFrame.state (r := r) pb good.live.hs _ rfl),
      Or.inr ⟨?_, rfl, cursor, pendLe, fun _ => Nat.le_refl _, fun e => absurd e (by decide), rfl⟩⟩
    unfold commentStage
    simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg, present,
      bne_self_eq_false, Bool.false_eq_true, ite_false, wrD_eq]
  · obtain ⟨early, H1, z1, d1, p1, run1, base1, ret1, cont1, prog1⟩ :=
      string_ready_copy_q good trees buffers cursor low out globals record getg (·.comment) ready present pendLe
    obtain ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, status1, gzhead1, bits1, pbuf1,
      pbs1, out1, keep1, shape1, stage1⟩ := base1
    cases early
    · obtain ⟨cursor1, pend1, last1, zero1⟩ := cont1 rfl
      obtain ⟨good3, trees3, buffers3⟩ := status_engine good1 trees1 buffers1 HCRC_STATE (by simp [GoodStatus])
      refine ⟨_, z1, _, p1, ⟨good3, ⟨buf1, trees3, size1⟩, buffers3, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1, shape1.trans ⟨_, _, _, _, _, _, _, _, rfl⟩,
        by
          have s := StageFrame.trans stage1
            (StageFrame.state good1 buffers1 trees1.base.pbuf ({ d1 with status := HCRC_STATE } : DeflateState))
            (HeaderShape.owned shape1) good buffers
          rwa [Nat.add_zero] at s⟩, keep1.trans (CallerKeep.of_frame
          (HeaderFrame.state (r := r) pb good1.live.hs _ rfl)) account1, Or.inr ⟨?_, rfl, cursor1, pend1,
        fun none => (by have := zero1 none; change d.pending.toNat ≤ d1.pending.toNat; omega),
        fun e => absurd e (by decide), last1⟩⟩
      unfold commentStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.comment != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [wrD_eq, good1.live.hs]
    · refine ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1,
        pbuf1, pbs1, out1, shape1, stage1⟩, keep1, Or.inl ⟨?_, (ret1 rfl).2.2.1, (ret1 rfl).2.1, (ret1 rfl).1, by rw [status1, status]; decide,
          (ret1 rfl).2.2.2, status1, prog1 rfl⟩⟩
      unfold commentStage
      simp only [bind_app, rdD_eq, good.live.hs, st, ite_true, ldDeflateState_tab good.live.hs, ldg,
        show (g.comment != .null) = true from bne_iff_ne.mpr present]
      rw [run1]
      simp [pure_app]


/-- `HeaderDone` with the facts of an early return (`QZProg`). -/
def HeaderDoneQ (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState) (buf : Array UInt8)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
    StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ StageFrame h after r ds pb d z z' produced ∧
    d'.bi_valid.toInt < 8 ∧
    d'.gzhead = d.gzhead ∧ HeaderShape d d' ∧ (HeaderInv d → HeaderInv d') ∧ z'.next_out ≠ .null ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧ d'.pending ≠ 0 ∧ d'.status ≠ FINISH_STATE ∧
      z'.avail_out = 0 ∧ QZProg d d') ∨
     (run = k after ∧ d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧
       d'.last_flush = d.last_flush))

theorem HeaderDoneQ.back {h h1 : Heap} {r : ZStreamRef} {ds pb : Nat} {z z1 : ZStream} {d d1 : DeflateState}
    {buf buf1 : Array UInt8} {run : Except Fault (Int32 × Heap)} {k : M Int32} {p : Nat}
    (done : HeaderDoneQ h1 r ds pb z1 d1 buf1 run k) (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (stage : StageFrame h h1 r ds pb d z z1 p) (account : StreamAccounting z z1 0 p)
    (shape : HeaderShape d d1) (header : HeaderInv d → HeaderInv d1) (lastFlush : d1.last_flush = d.last_flush)
    (size : buf1.size = buf.size) (lt : rank d1 < rank d) :
    HeaderDoneQ h r ds pb z d buf run k := by
  obtain ⟨after, z', d', q, good', ⟨b', t, s⟩, buffers', acc, stage', bits', gz', shape', header', out, outcome⟩ := done
  refine ⟨after, z', d', p + q, good', ⟨b', t, s.trans size⟩, buffers', stream_accounting_trans account acc,
    StageFrame.trans stage stage' (HeaderShape.owned shape) good buffers,
    bits', gz'.trans shape.gzhead, shape.trans shape', fun hd => header' (header hd), out, ?_⟩
  rcases outcome with ⟨e, lf, pn, sf, fo, le, _⟩ | ⟨e, st, zero, cur, lf⟩
  · exact Or.inl ⟨e, lf, pn, sf, fo, ⟨by omega, fun _ => Or.inl (by omega)⟩⟩
  · exact Or.inr ⟨e, st, zero, cur, lf.trans lastFlush⟩

theorem t_hcrc_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (status : d.status = HCRC_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDoneQ h r ds pb z d buf (hcrcStage (some r) (some (.tab ds)) k h) k := by
  obtain ⟨after, z1, d1, produced, ⟨good1, trees1, buffers1, account1, _, _, gzhead1, bits1, _, _, out1, shape1,
    stage1⟩, outcome⟩ := hcrc_stage_q good trees buffers cursor low out status record getg pendLe k
  refine ⟨after, z1, d1, produced, good1, trees1, buffers1, account1, stage1, by rw [bits1]; exact low, gzhead1, shape1,
    (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, ?_⟩
  rcases outcome with ⟨e, _, lf, pn, sf, fo, stq⟩ | ⟨e, st, zero, cur, _, lfc⟩
  · refine Or.inl ⟨e, lf, pn, sf, fo, ?_⟩
    rcases stq with b | ⟨hc, np⟩
    · exact ⟨rank_le_of b status (by decide), fun _ => Or.inl (rank_lt_of b status (by decide))⟩
    · exact ⟨rank_le_of_status (hc.trans status.symm), fun z0 => absurd z0 np⟩
  · exact Or.inr ⟨e, st, zero, cur, lfc⟩

theorem t_comment_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = COMMENT_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDoneQ h r ds pb z d buf (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, _, gzhead1, bits1, pbuf1, pbs1,
    out1, shape1, stage1⟩, _, outcome⟩ :=
    comment_stage_q good trees buffers cursor low out globals status record getg ready pendLe
      (hcrcStage (some r) (some (.tab ds)) k)
  rcases outcome with ⟨e, _, lf, pn, sf, fo, stEq, prog⟩ | ⟨e, st1, cursor1, pend1, _, _, lf1⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf, pn, sf, fo,
        ⟨rank_le_of_status stEq, fun z0 => Or.inr ⟨stEq, prog (pending_lt_of_zero trees z0)⟩⟩⟩⟩
  · rw [e]
    exact (t_hcrc_q good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 st1
      (by rw [gzhead1]; exact record) gz1 (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) lf1 size1 (rank_lt_of st1 status (by decide))

theorem t_name_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = NAME_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.name) (absent : g.name = .null → d.gzindex = 0)
    (comment : StringLater h z ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDoneQ h r ds pb z d buf (nameStage (some r) (some (.tab ds))
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k)) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1, pbuf1,
    pbs1, out1, shape1, stage1⟩, keep1, outcome⟩ :=
    name_stage_q good trees buffers cursor low out globals status record getg ready pendLe
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))
  rcases outcome with ⟨e, _, lf, pn, sf, fo, stEq, prog⟩ | ⟨e, st1, cursor1, pend1, _, gzi, lf1⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf, pn, sf, fo,
        ⟨rank_le_of_status stEq, fun z0 => Or.inr ⟨stEq, prog (pending_lt_of_zero trees z0)⟩⟩⟩⟩
  · rw [e]
    have zero1 : d1.gzindex = 0 := by
      obtain ⟨present, gone⟩ := gzi rfl
      by_cases n : g.name = .null
      · rw [gone n, absent n]
      · exact present n
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    exact (t_comment_q good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1 st1
      (by rw [gzhead1]; exact record) gz1 ((comment.keep keep1 account1).ready zero1)
      (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) lf1 size1 (rank_lt_of st1 status (by decide))

theorem t_extra_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = EXTRA_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (extraMem : g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
      eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb)
    (progress : g.extra ≠ .null → d.gzindex.toNat ≤ g.extra_len.toNat % 2 ^ 16)
    (absent : g.extra = .null → d.gzindex = 0)
    (name : StringLater h z ds pb g.name) (comment : StringLater h z ds pb g.comment)
    (below : d.pending.toNat < buf.size) (k : M Int32) :
    HeaderDoneQ h r ds pb z d buf (extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds))
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))) h) k := by
  obtain ⟨p1, H1, z1, d1, good1, buffers1, account1, ⟨buf1, trees1, size1⟩, gz1, static1, out1, keep1, shape1,
    stage1, gzhead1, bits1, outcome⟩ :=
    extra_stage_q good trees buffers cursor low out globals status record getg extraMem progress below
      (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k)))
  rcases outcome with ⟨e, _, lf, pn, sf, fo, stEq, prog⟩ | ⟨e, st1, cursor1, pend1, _, gzi, lf1⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf, pn, sf, fo,
        ⟨rank_le_of_status stEq, fun z0 => Or.inr ⟨stEq, prog⟩⟩⟩⟩
  · rw [e]
    have zero1 : d1.gzindex = 0 := by
      rcases gzi with z0 | ⟨n, same⟩
      · exact z0
      · rw [same, absent n]
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    exact (t_name_q good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1 st1
      (by rw [gzhead1]; exact record) gz1 ((name.keep keep1 account1).ready zero1) (fun _ => zero1)
      (comment.keep keep1 account1) (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) lf1 size1 (rank_lt_of st1 status (by decide))

theorem t_gzip_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (avail : z.avail_out ≠ 0) (globals : LibraryGlobals h)
    (status : d.status = GZIP_STATE) (pending : d.pending = 0)
    (header : ∀ i, d.gzhead = some (.tab i) → ∃ g, h.gzheaders i = some g ∧
      (g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
        eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb) ∧
      StringLater h z ds pb g.name ∧ StringLater h z ds pb g.comment)
    (noneOrSome : d.gzhead = none ∨ ∃ i, d.gzhead = some (.tab i)) (k : M Int32) :
    HeaderDoneQ h r ds pb z d buf (gzipStage (some r) (some (.tab ds)) (extraStage (some r) (some (.tab ds))
      (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds))
        (hcrcStage (some r) (some (.tab ds)) k)))) h) k := by
  have sizeLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  rcases noneOrSome with none | ⟨i, record⟩
  · obtain ⟨produced, after, z', d', good', buffers', account, stage, _, _, low', empty', fields, run, full'⟩ :=
      gzip_plain_stage good trees buffers cursor status pending none low avail out
        (extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds)) (commentStage (some r)
          (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))))
    have keys : d'.pending_buf = d.pending_buf ∧ d'.lit_bufsize = d.lit_bufsize ∧ d'.gzhead = d.gzhead ∧
        d'.status = BUSY_STATE := by
      rw [fields]; exact ⟨rfl, rfl, rfl, rfl⟩
    have out' : z'.next_out ≠ .null := by rw [account.2.2.2.2.2.1]; exact Call.advance_ne_null out _
    by_cases zero : d'.pending = 0
    · have skip : extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds)) (commentStage (some r)
          (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))) after = k after := by
        have hs := good'.live.hs
        rw [extra_stage_skip hs _ (by rw [keys.2.2.2]; decide), name_stage_skip hs _ (by rw [keys.2.2.2]; decide),
          comment_stage_skip hs _ (by rw [keys.2.2.2]; decide), hcrc_stage_skip hs _ (by rw [keys.2.2.2]; decide)]
      refine ⟨after, z', d', produced, good', trees_same_buffer good' trees keys.1 keys.2.1, buffers', account,
        stage, low', keys.2.2.1, ⟨_, _, _, _, _, _, _, _, fields⟩, fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out',
        Or.inr ⟨?_, keys.2.2.2, zero, empty' zero, by rw [fields]⟩⟩
      rw [run]; simp [zero, skip]
    · obtain ⟨buf', trees', size'⟩ := trees_same_buffer good' trees keys.1 keys.2.1
      obtain ⟨good5, buffers5, _⟩ := last_flush_frame (pb := pb) good' trees' buffers' (-1)
      refine ⟨_, z', _, produced, good5, ⟨buf', trees_at_buffer good5 trees'.base.pbuf trees'.base.bytes, size'⟩,
        buffers5, account, ?_, low', keys.2.2.1, HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields⟩ ⟨_, _, _, _, _, _, _, _, rfl⟩,
        fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out', Or.inl ⟨?_, rfl, zero,
          by show d'.status ≠ _; rw [keys.2.2.2]; decide, full' zero,
          ⟨rank_le_of keys.2.2.2 status (by decide), fun _ => Or.inl (rank_lt_of keys.2.2.2 status (by decide))⟩⟩⟩
      · have s := StageFrame.trans stage (StageFrame.state good' buffers' trees'.base.pbuf { d' with last_flush := -1 })
          (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields⟩ : HeaderShape d d')) good buffers
        rwa [Nat.add_zero] at s
      · rw [run]; simp [zero]
  · obtain ⟨g, getg, extraMem, name, comment⟩ := header i record
    obtain ⟨H1, z1, d1, buf1, good1, trees1, buffers1, account1, frame1, fields1, lo1, hi1, size1, run1⟩ :=
      gzip_record_stage good trees buffers cursor globals status pending record getg
        (extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds)) (commentStage (some r)
          (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))))
    have keys : d1.status = EXTRA_STATE ∧ d1.gzindex = 0 ∧ d1.gzhead = d.gzhead ∧ d1.bi_valid = d.bi_valid ∧
        d1.pending_out = d1.pending_buf := by
      rw [fields1]; exact ⟨rfl, rfl, rfl, rfl, cursor⟩
    have keep1 : CallerKeep h H1 z ds pb := CallerKeep.of_frame frame1
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [frame1.static, globals]
    have out1 : z1.next_out ≠ .null := by rw [account1.2.2.2.2.2.1]; exact Call.advance_ne_null out _
    rw [run1]
    exact (t_extra_q good1 trees1 buffers1 keys.2.2.2.2 (by rw [keys.2.2.2.1]; exact low) out1 globals1 keys.1
      (by rw [keys.2.2.1]; exact record) (by rw [frame1.gzheaders]; exact getg)
      (fun present => by
        obtain ⟨rs, eo, ea, e, get, fit, ne⟩ := extraMem present
        exact ⟨rs, eo, ea, e, by rw [frame1.views rs ne]; exact get, fit, ne⟩)
      (fun _ => by rw [keys.2.1]; exact Nat.zero_le _) (fun _ => keys.2.1)
      (name.keep keep1 account1) (comment.keep keep1 account1) (by omega) k).back good buffers
      (StageFrame.of_header frame1 good buffers trees.base.pbuf account1 good1.live.hz) account1
      ⟨_, _, _, _, _, _, _, _, fields1⟩
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) ⟨_, _, _, _, _, _, _, _, fields1⟩)
      (by rw [fields1]) size1 (rank_lt_of keys.1 status (by decide))

theorem t_init_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (avail : z.avail_out ≠ 0) (status : d.status = INIT_STATE)
    (pending : d.pending = 0) (k : M Int32) :
    HeaderDoneQ h r ds pb z d buf (wrapStage (some r) (some (.tab ds)) (initStage (some r) (some (.tab ds))
      (gzipStage (some r) (some (.tab ds)) (extraStage (some r) (some (.tab ds))
        (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds))
          (hcrcStage (some r) (some (.tab ds)) k)))))) h) k := by
  have skipAll : ∀ {H : Heap} {e : DeflateState}, H.dstates ds = some e → e.status = BUSY_STATE →
      initStage (some r) (some (.tab ds)) (gzipStage (some r) (some (.tab ds)) (extraStage (some r) (some (.tab ds))
        (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds))
          (hcrcStage (some r) (some (.tab ds)) k))))) H = k H := by
    intro H e hs st
    rw [init_stage_skip hs _ (by rw [st]; decide), gzip_stage_skip hs _ (by rw [st]; decide),
      extra_stage_skip hs _ (by rw [st]; decide), name_stage_skip hs _ (by rw [st]; decide),
      comment_stage_skip hs _ (by rw [st]; decide), hcrc_stage_skip hs _ (by rw [st]; decide)]
  by_cases w : d.wrap = 0
  · obtain ⟨good1, trees1, buffers1⟩ := status_engine good trees buffers BUSY_STATE (by simp [GoodStatus])
    refine ⟨_, z, _, 0, good1, ⟨buf, trees1, rfl⟩, buffers1, stream_accounting_zero z,
      StageFrame.state good buffers trees.base.pbuf _, low, rfl, ⟨_, _, _, _, _, _, _, _, rfl⟩,
      fun _ => HeaderInv.of_busy (Or.inl rfl), out,
      Or.inr ⟨?_, rfl, pending, cursor, rfl⟩⟩
    rw [wrap_stage_busy good.live.hs _ status w]
    exact skipAll (setD_dstates_same _ _ _) rfl
  · rw [wrap_stage_skip good.live.hs _ (fun e => w e.2)]
    obtain ⟨produced, after, z', d', good', buffers', account, _, _, low', empty', fields, run, stage, full'⟩ :=
      init_stage good trees buffers cursor status pending low avail out
        (gzipStage (some r) (some (.tab ds)) (extraStage (some r) (some (.tab ds))
          (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds))
            (hcrcStage (some r) (some (.tab ds)) k)))))
    have keys : d'.pending_buf = d.pending_buf ∧ d'.lit_bufsize = d.lit_bufsize ∧ d'.gzhead = d.gzhead ∧
        d'.status = BUSY_STATE := by
      rw [fields]; exact ⟨rfl, rfl, rfl, rfl⟩
    have out' : z'.next_out ≠ .null := by rw [account.2.2.2.2.2.1]; exact Call.advance_ne_null out _
    by_cases zero : d'.pending = 0
    · refine ⟨after, z', d', produced, good', trees_same_buffer good' trees keys.1 keys.2.1, buffers', account,
        stage, low', keys.2.2.1, ⟨_, _, _, _, _, _, _, _, fields⟩, fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out',
        Or.inr ⟨?_, keys.2.2.2, zero, empty' zero, by rw [fields]⟩⟩
      rw [run]
      have hs := good'.live.hs
      simp only [zero, ne_eq, not_true_eq_false, ite_false]
      rw [gzip_stage_skip hs _ (by rw [keys.2.2.2]; decide), extra_stage_skip hs _ (by rw [keys.2.2.2]; decide),
        name_stage_skip hs _ (by rw [keys.2.2.2]; decide), comment_stage_skip hs _ (by rw [keys.2.2.2]; decide),
        hcrc_stage_skip hs _ (by rw [keys.2.2.2]; decide)]
    · obtain ⟨buf', trees', size'⟩ := trees_same_buffer good' trees keys.1 keys.2.1
      obtain ⟨good5, buffers5, _⟩ := last_flush_frame (pb := pb) good' trees' buffers' (-1)
      refine ⟨_, z', _, produced, good5, ⟨buf', trees_at_buffer good5 trees'.base.pbuf trees'.base.bytes, size'⟩,
        buffers5, account, ?_, low', keys.2.2.1, HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields⟩ ⟨_, _, _, _, _, _, _, _, rfl⟩,
        fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out', Or.inl ⟨?_, rfl, zero,
          by show d'.status ≠ _; rw [keys.2.2.2]; decide, full' zero,
          ⟨rank_le_of keys.2.2.2 status (by decide), fun _ => Or.inl (rank_lt_of keys.2.2.2 status (by decide))⟩⟩⟩
      · have s := StageFrame.trans stage (StageFrame.state good' buffers' trees'.base.pbuf { d' with last_flush := -1 })
          (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields⟩ : HeaderShape d d')) good buffers
        rwa [Nat.add_zero] at s
      · rw [run]; simp [zero]


theorem header_phase_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (entry : HeaderEntry h z d ds pb buf)
    (flush : Int32) (k : M Int32) :
    HeaderDoneQ h r ds pb z d buf (headerPhase (some r) (some (.tab ds)) flush k h) k ∨
      (d.status = FINISH_STATE ∧ headerPhase (some r) (some (.tab ds)) flush k h = k h) := by
  rw [header_stages]
  have hs := good.live.hs
  have st := good.live.status
  unfold GoodStatus at st
  rcases st with e | e | e | e | e | e | e | e
  · obtain ⟨pend, avail⟩ := entry.fresh (Or.inl e)
    exact Or.inl (t_init_q good trees buffers cursor low out avail e pend k)
  · obtain ⟨pend, avail⟩ := entry.fresh (Or.inr e)
    obtain ⟨cases, header⟩ := entry.gzip e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide)]
    exact t_gzip_q good trees buffers cursor low out avail globals e pend header cases k
  · obtain ⟨i, g, record, getg, pendLe, extraFacts, _, _⟩ := entry.writing (Or.inl e)
    obtain ⟨mem, prog, absent, name, comment, below⟩ := extraFacts e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide)]
    exact t_extra_q good trees buffers cursor low out globals e record getg mem prog absent name comment below k
  · obtain ⟨i, g, record, getg, pendLe, _, nameFacts, _⟩ := entry.writing (Or.inr (Or.inl e))
    obtain ⟨ready, absent, comment⟩ := nameFacts e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide)]
    exact t_name_q good trees buffers cursor low out globals e record getg ready absent comment pendLe k
  · obtain ⟨i, g, record, getg, pendLe, _, _, commentFacts⟩ := entry.writing (Or.inr (Or.inr (Or.inl e)))
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide)]
    exact t_comment_q good trees buffers cursor low out globals e record getg (commentFacts e) pendLe k
  · obtain ⟨i, g, record, getg, pendLe, _, _, _⟩ := entry.writing (Or.inr (Or.inr (Or.inr e)))
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide),
      comment_stage_skip hs _ (by rw [e]; decide)]
    exact t_hcrc_q good trees buffers cursor low out e record getg pendLe k
  · have pend := entry.busy (Or.inl e)
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide),
      comment_stage_skip hs _ (by rw [e]; decide), hcrc_stage_skip hs _ (by rw [e]; decide)]
    exact ⟨h, z, d, 0, good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z,
      StageFrame.refl good buffers trees.base.pbuf, low, rfl, HeaderShape.refl d, id, out,
      Or.inr ⟨rfl, e, pend, cursor, rfl⟩⟩
  · right
    refine ⟨e, ?_⟩
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide),
      comment_stage_skip hs _ (by rw [e]; decide), hcrc_stage_skip hs _ (by rw [e]; decide)]


/-- What the header step concludes (`HeaderOut`), with progress on the early return and the fields
the header phase keeps. -/
def HeaderQuietOut (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DInv after r ds z' d' ∧ HeaderInv d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
    StageFrame h after r ds pb d z z' produced ∧ (∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b) ∧
    z'.next_out ≠ .null ∧ d'.lit_bufsize = d.lit_bufsize ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧ d'.pending ≠ 0 ∧
        CallFacts d' ∧ z'.avail_out = 0 ∧
        (rank d' < rank d ∨ (d'.status = d.status ∧ d.gzindex.toNat < d'.gzindex.toNat))) ∨
     (run = k after ∧ d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧
        d'.last_flush = d.last_flush ∧ CallFacts d')) ∧
    d'.lookahead = d.lookahead ∧ d'.match_available = d.match_available ∧ d'.sym_next = d.sym_next ∧
    d'.level = d.level ∧ d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.wrap = d.wrap

/-- **The header phase from a mid-call state, for `DeflateQuiet`**: `header_step_mid` from a drained
`pending_buf` (`pending`), and its early return makes progress: the header rank drops, or the status
is kept and `gzindex` grew. The header phase keeps the positions, the lookahead, the symbols, the
level and `wrap`. -/
theorem header_quiet {h0 h : Heap} {r : ZStreamRef} {ds pb : Nat} {z0 z : ZStream} {d0 d : DeflateState}
    {buf : Array UInt8} (inv0 : DInv h0 r ds z0 d0) (hinv0 : HeaderInv d0)
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (pbuf : d.pending_buf = .ref (.blk pb) 0)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (out : z.next_out ≠ .null)
    (alloc : DefAlloc z) (fields0 : HeaderFields d0 d) (status0 : d.status = d0.status) (wrap0 : d.wrap = d0.wrap)
    (static0 : h.static = h0.static)
    (win0 : ∀ w, d0.window = .ref (.blk w) 0 → h.bytes w = h0.bytes w)
    (prv0 : ∀ p, d0.prev = .ref (.blk p) 0 → h.words p = h0.words p)
    (hd0 : ∀ q, d0.head = .ref (.blk q) 0 → h.words q = h0.words q)
    (low : d.bi_valid.toInt < 8) (lfRange : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5)
    (lfNot : d.last_flush ≠ -2) (writing : Writing d) (entry : HeaderEntry h z d ds pb buf)
    (pending : d.pending = 0) (flush : Int32) (k : M Int32) :
    HeaderQuietOut h r ds pb z d (headerPhase (some r) (some (.tab ds)) flush k h) k := by
  have globals : LibraryGlobals h := by
    have g := inv0.globals
    unfold LibraryGlobals at g ⊢
    rw [static0]; exact g
  have done := (header_phase_q good trees buffers cursor low out globals entry flush k).resolve_right
    (fun ⟨fin, _⟩ => writing.not_finish fin)
  obtain ⟨after, z', d', produced, good', _, buffers', acc, frame, low', _, shape, hinvf, out', branch⟩ := done
  obtain ⟨_, _, _, static, win, prv, hd, pres⟩ := StageFrame.call_facts frame good buffers pbuf out
  have fields : HeaderFields d0 d' := fields0.then_shape shape
  have keepF : d'.lookahead = d.lookahead ∧ d'.match_available = d.match_available ∧ d'.sym_next = d.sym_next ∧
      d'.level = d.level ∧ d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.wrap = d.wrap := by
    obtain ⟨_, _, _, _, _, _, _, _, e⟩ := shape
    rw [e]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have own : ∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b := by
    obtain ⟨_, _, _, _, _, _, _, _, e⟩ := shape
    intro b; rw [e]; exact Iff.rfl
  have writing0 : Writing d0 := by unfold Writing at *; rw [← status0]; exact writing
  have empty : d0.sym_next = 0 := hinv0.empty writing0
  have hinv' : HeaderInv d' := hinvf (HeaderInv.of_fields hinv0 fields0 status0)
  have symEq : d'.sym_next = d0.sym_next := by unfold HeaderFields at fields; rw [fields]
  have wrapEq : d'.wrap = d0.wrap := by
    have w1 : d'.wrap = d.wrap := by obtain ⟨_, _, _, _, _, _, _, _, eq⟩ := shape; rw [eq]
    exact w1.trans wrap0
  have alloc' : DefAlloc z' := by
    obtain ⟨za, zf⟩ := alloc
    exact ⟨acc.2.2.2.2.2.2.2.1.trans za, acc.2.2.2.2.2.2.2.2.1.trans zf⟩
  have keepW : ∀ w, d0.window = .ref (.blk w) 0 → after.bytes w = h0.bytes w := fun w e =>
    (win w (by unfold HeaderFields at fields0; rw [fields0]; exact e)).trans (win0 w e)
  have keepP : ∀ p, d0.prev = .ref (.blk p) 0 → after.words p = h0.words p := fun p e =>
    (prv p (by unfold HeaderFields at fields0; rw [fields0]; exact e)).trans (prv0 p e)
  have keepH : ∀ q, d0.head = .ref (.blk q) 0 → after.words q = h0.words q := fun q e =>
    (hd q (by unfold HeaderFields at fields0; rw [fields0]; exact e)).trans (hd0 q e)
  have keepB : ∀ b, d0.pending_buf = .ref (.blk b) 0 → ∃ a', after.bytes b = some a' := fun b e =>
    pres b (by unfold HeaderFields at fields0; rw [fields0]; exact e)
  have trailer : d'.wrap.toInt < 0 → d'.status = FINISH_STATE := by
    intro neg
    rw [wrapEq] at neg
    exact absurd (inv0.shape.trailer neg) writing0.not_finish
  have bits : d'.bi_valid.toInt ≤ 7 := by omega
  have litEq : d'.lit_bufsize = d.lit_bufsize := by
    have f := HeaderShape.fields shape; unfold HeaderFields at f; rw [f]
  rcases branch with ⟨run, lf, pend, nf, full0, zp⟩ | ⟨run, busy, pend, cur, lf⟩
  · have shape' : Shape d' := Shape.of_fields inv0.shape fields
      ⟨by rw [lf]; decide, by rw [lf]; decide⟩ (fun _ => Or.inr lf) trailer bits (fun e => absurd e pend)
    have inv' := inv0.lift_empty good' alloc' (static.trans static0) shape' fields empty keepW keepP keepH keepB
    refine ⟨after, z', d', produced, inv', hinv', buffers', acc, frame, own, out', litEq, Or.inl ⟨run, lf, pend, ?_, full0, zp.2 pending⟩, keepF⟩
    exact { fresh := fun e => absurd (lf.symm.trans e) (by decide),
            freshStart := fun e => absurd (lf.symm.trans e) (by decide),
            finishSym := fun _ => symEq.trans empty,
            finishLook := fun e => absurd e nf,
            finishBits := fun e => absurd e nf }
  · have shape' : Shape d' := Shape.of_fields inv0.shape fields
      (by rw [lf]; exact lfRange) (fun st => by rw [busy] at st; rcases st with e | e <;> exact absurd e (by decide))
      trailer bits (fun _ => cur)
    have inv' := inv0.lift_empty good' alloc' (static.trans static0) shape' fields empty keepW keepP keepH keepB
    refine ⟨after, z', d', produced, inv', hinv', buffers', acc, frame, own, out', litEq, Or.inr ⟨run, busy, pend, cur, lf, ?_⟩, keepF⟩
    exact { fresh := fun e => absurd (lf.symm.trans e) lfNot,
            freshStart := fun e => absurd (lf.symm.trans e) lfNot,
            finishSym := fun e => by rw [busy] at e; exact absurd e (by decide),
            finishLook := fun e => by rw [busy] at e; exact absurd e (by decide),
            finishBits := fun e => by rw [busy] at e; exact absurd e (by decide) }

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.Quiet.marker_quiet
#print axioms Zlib.Deflate.Universal.Quiet.header_quiet
