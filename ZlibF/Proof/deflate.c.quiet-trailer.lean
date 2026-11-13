import ZlibF.Proof.«deflate.c.quiet-phi»
import ZlibF.Proof.«deflate.c.universal-call-trailerstep»

/-!
# deflate.c: the trailer phase, with the facts `DeflateQuiet` needs

`trailer_quiet` is `trailer_step` with two more facts: with `Z_FINISH` and a trailer due
(`wrap > 0`), the trailer is written and `wrap` negated (C: `if (s->wrap > 0) s->wrap = -s->wrap;`);
and the bytes the trailer phase delivers plus the bytes it leaves pending are at most 8 more than
the bytes pending on entry (the trailer is 4 or 8 bytes). The proofs of `trailer_end` and
`trailer_phase` are restated with these facts.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

theorem trailer_end_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) :
    ∃ (rc : Int32) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      trailerEnd (some r) (some (.tab ds)) h = .ok (rc, after) ∧ DGood after r ds z1 d1 ∧
      (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧ StreamBuffers after r ∧
      StreamAccounting z z1 0 produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      d1 = { d with pending := d1.pending, pending_out := d1.pending_out, wrap := d1.wrap } ∧
      d1.wrap.toInt ≤ 0 ∧ StageFrame h after r ds pb d z z1 produced ∧
      (d1.pending = 0 → d1.pending_out = d1.pending_buf) ∧ (rc = Z_STREAM_END ↔ d1.pending = 0) ∧
      (0 < d.wrap.toInt → d1.wrap.toInt = -d.wrap.toInt) ∧ (rc = Z_OK → z1.avail_out = 0) ∧
      d1.pending.toNat + produced = d.pending.toNat := by
  obtain ⟨produced, H1, z1, d1, run1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, copied1, left1, fields1,
    empty1, _adler1, _gz1, _static1, _sizes1⟩ := header_flush good trees buffers low cursor out
  have stage1 := StageFrame.of_flush good trees buffers low cursor out run1 good1.live.hz account1
  have lo := good.inv.wrap_lo
  have hi := good.inv.wrap_hi
  have wrap1 : d1.wrap = d.wrap := by rw [fields1]
  have endZero : (if d1.pending != 0 then Z_OK else Z_STREAM_END) = Z_STREAM_END → d1.pending = 0 := by
    intro e
    by_cases p : d1.pending = 0
    · exact p
    · rw [if_pos (bne_iff_ne.mpr p)] at e; exact absurd e (by decide)
  have endIff : (if d1.pending != 0 then Z_OK else Z_STREAM_END) = Z_STREAM_END ↔ d1.pending = 0 :=
    ⟨endZero, fun p => by rw [p]; rfl⟩
  have okFull : (if d1.pending != 0 then Z_OK else Z_STREAM_END) = Z_OK → z1.avail_out = 0 := by
    intro e
    refine full_of_left account1 copied1 left1 (pending_toNat_ne ?_)
    intro p; rw [p] at e; exact absurd e (by decide)
  by_cases pos : d.wrap > 0
  · have posI : 0 < d.wrap.toInt := Int32.lt_iff_toInt_lt.mp pos
    have range : -2147483648 ≤ -d.wrap.toInt ∧ -d.wrap.toInt ≤ 2147483647 := by omega
    let nw : Int32 := Int32.ofInt (-d.wrap.toInt)
    have nwVal : nw.toInt = -d.wrap.toInt := Int32.toInt_ofInt_of_le range.1 (by omega)
    obtain ⟨good2, trees2, buffers2, _⟩ := wrap_engine good1 trees1 buffers1 nw (by omega) (by omega)
    refine ⟨if d1.pending != 0 then Z_OK else Z_STREAM_END, _, z1, _, produced, ?_, good2, ⟨buf1, trees2, size1⟩,
      buffers2, account1, by split <;> simp, by rw [fields1], by change nw.toInt ≤ 0; omega,
      by
        have s := StageFrame.trans stage1 (StageFrame.state good1 buffers1 trees1.base.pbuf { d1 with wrap := nw })
          (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
        rwa [Nat.add_zero] at s, fun z0 => empty1 z0, endIff, fun _ => nwVal, okFull, left1⟩
    unfold trailerEnd
    simp only [bind_app]
    rw [run1]
    simp only [rdD_eq, good1.live.hs, wrap1, pos, ite_true, ineg, chk32, range, and_self, pure_app, bind_app]
    simp only [wrD_eq, good1.live.hs, rdD_eq, setD_dstates_same, pure_app]
    rfl
  · refine ⟨if d1.pending != 0 then Z_OK else Z_STREAM_END, H1, z1, d1, produced, ?_, good1, ⟨buf1, trees1, size1⟩,
      buffers1, account1, by split <;> simp, by rw [fields1], ?_, stage1, empty1, endIff,
      fun p => by
        have := mt Int32.lt_iff_toInt_lt.mpr pos; change ¬ (0 < d.wrap.toInt) at this; exact absurd p this, okFull, left1⟩
    · unfold trailerEnd
      simp only [bind_app]
      rw [run1]
      simp [rdD_eq, good1.live.hs, wrap1, pos]
    · rw [wrap1]; have := mt Int32.lt_iff_toInt_lt.mpr pos; change ¬ (0 < d.wrap.toInt) at this; omega

/-- `trailer_phase` with the negated `wrap` and the byte count. -/
theorem trailer_phase_q {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (room : d.pending.toNat + 8 ≤ buf.size) (flush : Int32) :
    ∃ (rc : Int32) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
      trailerPhase (some r) (some (.tab ds)) flush h = .ok (rc, after) ∧ DGood after r ds z1 d1 ∧
      (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧ StreamBuffers after r ∧
      StreamAccounting z z1 0 produced ∧
      d1 = { d with pending := d1.pending, pending_out := d1.pending_out, wrap := d1.wrap } ∧
      StageFrame h after r ds pb d z z1 produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (d1.pending = 0 → d1.pending_out = d1.pending_buf) ∧
      (rc = Z_STREAM_END → d1.pending = 0 ∨ d1.pending = d.pending) ∧
      (flush ≠ Z_FINISH → rc = Z_OK ∧ after = h ∧ d1 = d) ∧
      (d1.wrap = d.wrap ∨ (0 < d.wrap.toInt ∧ d1.wrap.toInt = -d.wrap.toInt)) ∧
      (rc = Z_STREAM_END ↔ (d.wrap.toInt ≤ 0 ∧ d1 = d ∧ flush = Z_FINISH) ∨
        (0 < d.wrap.toInt ∧ flush = Z_FINISH ∧ d1.pending = 0)) ∧
      (rc = Z_OK → flush = Z_FINISH → 0 < d.wrap.toInt → z1.avail_out = 0) ∧
      (0 < d.wrap.toInt → flush = Z_FINISH → d1.wrap.toInt = -d.wrap.toInt) ∧
      produced + d1.pending.toNat ≤ d.pending.toNat + 8 := by
  have lo := good.inv.wrap_lo
  have hi := good.inv.wrap_hi
  rw [trailer_phase_split]
  unfold trailerPhase'
  by_cases fin : flush = Z_FINISH
  · subst fin
    by_cases nonpos : d.wrap ≤ 0
    · refine ⟨Z_STREAM_END, h, z, d, 0, ?_, good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z, rfl,
        StageFrame.refl good buffers trees.base.pbuf, Or.inr rfl, fun _ => cursor, fun _ => Or.inr rfl,
        fun nf => absurd rfl nf, Or.inl rfl,
        ⟨fun _ => Or.inl ⟨Int32.le_iff_toInt_le.mp nonpos, rfl, rfl⟩, fun _ => rfl⟩,
        fun e => absurd e (by decide),
        fun p _ => absurd p (by have := Int32.le_iff_toInt_le.mp nonpos; change d.wrap.toInt ≤ 0 at this; omega), by omega⟩
      simp [bind_app, rdD_eq, good.live.hs, nonpos, pure_app]
    · have pos : 0 < d.wrap.toInt := by
        have := mt Int32.le_iff_toInt_le.mpr nonpos; change ¬ (d.wrap.toInt ≤ 0) at this; omega
      have pre : ∀ K : M Int32, (do
          if Z_FINISH != Z_FINISH then return Z_OK
          if (← rd (some (.tab ds)) (·.wrap)) ≤ 0 then return Z_STREAM_END
          trailerBytes (some r) (some (.tab ds)) K) h = trailerBytes (some r) (some (.tab ds)) K h := by
        intro K
        simp [bind_app, rdD_eq, good.live.hs, nonpos]
      by_cases two : d.wrap = 2
      · obtain ⟨H1, d1, buf1, run1, good1, trees1, size1, buffers1, frame1, fields1, count1⟩ :=
          trailer_gzip good trees buffers cursor room two (trailerEnd (some r) (some (.tab ds)))
        obtain ⟨rc, H2, z2, d2, produced, run2, good2, trees2, buffers2, account2, rcs2, fields2, _, stage2, cur2,
          end2, wrap2, ok2, left2⟩ :=
          trailer_end_q good1 trees1 buffers1 (by rw [fields1]; exact cursor) (by rw [fields1]; exact low) out
        obtain ⟨b2, t2, s2⟩ := trees2
        refine ⟨rc, H2, z2, d2, produced, ?_, good2, ⟨b2, t2, s2.trans size1⟩, buffers2, account2, ?_, ?_, rcs2, cur2,
          fun e => Or.inl (end2.mp e), fun nf => absurd rfl nf,
          Or.inr ⟨pos, by
            have w1 : d1.wrap = d.wrap := by rw [fields1]
            rw [wrap2 (by rw [w1]; exact pos), w1]⟩,
          ⟨fun e => Or.inr ⟨pos, rfl, end2.mp e⟩, fun e => by
            rcases e with ⟨np, _, _⟩ | ⟨_, _, p⟩
            · omega
            · exact end2.mpr p⟩, fun e _ _ => ok2 e,
          fun _ _ => by
            have w1 : d1.wrap = d.wrap := by rw [fields1]
            rw [wrap2 (by rw [w1]; exact pos), w1],
          by omega⟩
        · rw [pre, run1, run2]
        · rw [fields2, fields1]
        · have s := StageFrame.trans
            (StageFrame.of_header frame1 good buffers trees.base.pbuf (stream_accounting_zero z) good1.live.hz)
            stage2 (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
          rwa [Nat.zero_add] at s
      · obtain ⟨H1, d1, buf1, run1, good1, trees1, size1, buffers1, frame1, fields1, count1⟩ :=
          trailer_zlib good trees buffers cursor (by omega) two (trailerEnd (some r) (some (.tab ds)))
        obtain ⟨rc, H2, z2, d2, produced, run2, good2, trees2, buffers2, account2, rcs2, fields2, _, stage2, cur2,
          end2, wrap2, ok2, left2⟩ :=
          trailer_end_q good1 trees1 buffers1 (by rw [fields1]; exact cursor) (by rw [fields1]; exact low) out
        obtain ⟨b2, t2, s2⟩ := trees2
        refine ⟨rc, H2, z2, d2, produced, ?_, good2, ⟨b2, t2, s2.trans size1⟩, buffers2, account2, ?_, ?_, rcs2, cur2,
          fun e => Or.inl (end2.mp e), fun nf => absurd rfl nf,
          Or.inr ⟨pos, by
            have w1 : d1.wrap = d.wrap := by rw [fields1]
            rw [wrap2 (by rw [w1]; exact pos), w1]⟩,
          ⟨fun e => Or.inr ⟨pos, rfl, end2.mp e⟩, fun e => by
            rcases e with ⟨np, _, _⟩ | ⟨_, _, p⟩
            · omega
            · exact end2.mpr p⟩, fun e _ _ => ok2 e,
          fun _ _ => by
            have w1 : d1.wrap = d.wrap := by rw [fields1]
            rw [wrap2 (by rw [w1]; exact pos), w1],
          by omega⟩
        · rw [pre, run1, run2]
        · rw [fields2, fields1]
        · have s := StageFrame.trans
            (StageFrame.of_header frame1 good buffers trees.base.pbuf (stream_accounting_zero z) good1.live.hz)
            stage2 (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields1⟩ : HeaderShape d d1)) good buffers
          rwa [Nat.zero_add] at s
  · refine ⟨Z_OK, h, z, d, 0, ?_, good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z, rfl,
      StageFrame.refl good buffers trees.base.pbuf, Or.inl rfl, fun _ => cursor, fun _ => Or.inr rfl,
      fun _ => ⟨rfl, rfl, rfl⟩, Or.inl rfl,
      ⟨fun e => absurd e (by decide), fun e => by rcases e with ⟨_, _, g⟩ | ⟨_, g, _⟩ <;> exact absurd g fin⟩,
      fun _ g => absurd g fin, fun _ g => absurd g fin, by omega⟩
    simp [bind_app, bne_iff_ne.mpr fin, pure_app]

/-- What the trailer step leaves (`TrailerOut`), with the negated `wrap` of a written trailer and the
bytes of the trailer phase. -/
def TrailerQuietOut (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (buf : Array UInt8) (flush : Int32) (run : Except Fault (Int32 × Heap)) : Prop :=
  ∃ (rc : Int32) (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
    run = .ok (rc, after) ∧ DInv after r ds z1 d1 ∧ HeaderInv d1 ∧ CallFacts d1 ∧ StreamBuffers after r ∧
    (∃ buf1, TreesInvAt after ds d1 pb buf1 ∧ buf1.size = buf.size) ∧
    StreamAccounting z z1 0 produced ∧ StageFrame h after r ds pb d z z1 produced ∧
    d1 = { d with pending := d1.pending, pending_out := d1.pending_out, wrap := d1.wrap } ∧
    (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
    (rc = Z_STREAM_END → flush = Z_FINISH ∧ d1.status = FINISH_STATE ∧ d1.pending = 0) ∧
    (flush ≠ Z_FINISH → rc = Z_OK ∧ after = h ∧ z1 = z ∧ d1 = d) ∧
    (d1.wrap = d.wrap ∨ (0 < d.wrap.toInt ∧ d1.wrap.toInt = -d.wrap.toInt)) ∧
    (rc = Z_STREAM_END ↔ (d.wrap.toInt ≤ 0 ∧ d1 = d ∧ flush = Z_FINISH) ∨
      (0 < d.wrap.toInt ∧ flush = Z_FINISH ∧ d1.pending = 0)) ∧
    (rc = Z_OK → flush = Z_FINISH → 0 < d.wrap.toInt → z1.avail_out = 0) ∧
    (0 < d.wrap.toInt → flush = Z_FINISH → d1.wrap.toInt = -d.wrap.toInt) ∧
    (flush = Z_FINISH → produced + d1.pending.toNat ≤ 8)

/-- **The trailer step for `DeflateQuiet`**: `trailer_step`, and with `Z_FINISH` a due trailer negates
`wrap`, and the phase delivers and leaves pending at most 8 bytes (the trailer, on a drained
`pending_buf`). -/
theorem trailer_quiet {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d)
    (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (flush : Int32) (finish : flush = Z_FINISH → d.status = FINISH_STATE ∧ d.pending = 0) :
    TrailerQuietOut h r ds pb z d buf flush (trailerPhase (some r) (some (.tab ds)) flush h) := by
  by_cases f : flush = Z_FINISH
  · obtain ⟨st, p0⟩ := finish f
    have cursor := inv.shape.cursor p0
    have low : d.bi_valid.toInt < 8 := by have := inv.shape.biValid; omega
    have room : d.pending.toNat + 8 ≤ buf.size := by
      have := trees.base.size; have := trees.base.lit_lo; rw [p0]; simp; omega
    obtain ⟨rc, after, z1, d1, produced, run, good1, trees1, buffers1, account, fields, stage, rcs, cur1, end1, _,
      wrapF, endIff, okFull, negF, bytesF⟩ :=
      trailer_phase_q inv.good trees buffers cursor low out room flush
    have keeps := StageFrame.keeps stage inv.good buffers trees.base.pbuf out
    have kq : d1.lookahead = d.lookahead ∧ d1.sym_next = d.sym_next ∧ d1.match_available = d.match_available ∧
        d1.match_length = d.match_length ∧ d1.prev_length = d.prev_length ∧ d1.block_start = d.block_start ∧
        d1.strstart = d.strstart ∧ d1.status = d.status ∧ d1.bi_buf = d.bi_buf ∧ d1.bi_valid = d.bi_valid ∧
        d1.bi_used = d.bi_used ∧ d1.last_flush = d.last_flush ∧ d1.gzindex = d.gzindex := by
      rw [fields]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨lookEq, symEq, maEq, mlEq, plEq, bsEq, ssEq, sEq, bbEq, bvEq, buEq, lfEq, giEq⟩ := kq
    have hf : HeaderFields d d1 := by
      unfold HeaderFields
      rw [sEq, bbEq, bvEq, buEq, lfEq, giEq]
      exact fields
    have shape' : Shape d1 := by
      refine Shape.of_fields inv.shape hf ?_ ?_ (fun _ => sEq.trans st) ?_ cur1
      · rw [lfEq]; exact inv.shape.lastFlush
      · intro e; rw [sEq, st] at e; rcases e with c | c <;> exact absurd c (by decide)
      · rw [bvEq]; exact inv.shape.biValid
    have alloc : DefAlloc z1 :=
      ⟨by rw [account.2.2.2.2.2.2.2.1]; exact inv.alloc.1, by rw [account.2.2.2.2.2.2.2.2.1]; exact inv.alloc.2⟩
    have empty : d.sym_next = 0 := facts.finishSym st
    have dinv := DInv.lift_empty inv good1 alloc keeps.1 shape' hf empty keeps.2.1 keeps.2.2.1 keeps.2.2.2.1
      keeps.2.2.2.2
    have callFacts : CallFacts d1 := by
      refine ⟨fun e => ?_, fun e => ?_, fun _ => symEq.trans empty, fun _ => lookEq.trans (facts.finishLook st),
        fun _ => bvEq.trans (facts.finishBits st)⟩
      · rw [lookEq, symEq, maEq, mlEq, plEq, bsEq]; exact facts.fresh (by rw [← lfEq]; exact e)
      · rw [bsEq, ssEq]; exact facts.freshStart (by rw [← lfEq]; exact e)
    refine ⟨rc, after, z1, d1, produced, run, dinv, HeaderInv.of_busy (Or.inr (sEq.trans st)), callFacts, buffers1,
      trees1, account, stage, fields, rcs, fun e => ⟨f, sEq.trans st, ?_⟩, fun nf => absurd f nf, wrapF, endIff, okFull,
      negF, fun _ => by
        have : d.pending.toNat = 0 := by rw [p0]; rfl
        omega⟩
    rcases end1 e with z0 | same
    · exact z0
    · rw [same, p0]
  · have run : trailerPhase (some r) (some (.tab ds)) flush h = .ok (Z_OK, h) := by
      rw [trailer_phase_split]
      unfold trailerPhase'
      simp [bind_app, bne_iff_ne.mpr f, pure_app]
    exact ⟨Z_OK, h, z, d, 0, run, inv, header, facts, buffers, ⟨buf, trees, rfl⟩, stream_accounting_zero z,
      StageFrame.refl inv.good buffers trees.base.pbuf, rfl, Or.inl rfl, fun e => absurd e (by decide),
      fun _ => ⟨rfl, rfl, rfl, rfl⟩, Or.inl rfl,
      ⟨fun e => absurd e (by decide), fun e => by rcases e with ⟨_, _, g⟩ | ⟨_, g, _⟩ <;> exact absurd g f⟩,
      fun _ g => absurd g f, fun _ g => absurd g f, fun g => absurd g f⟩

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.Quiet.trailer_quiet
