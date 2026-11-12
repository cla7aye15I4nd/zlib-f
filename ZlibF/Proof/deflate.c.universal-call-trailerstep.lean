import ZlibF.Proof.«deflate.c.universal-call-headerentry»

/-!
# deflate.c: the trailer phase of one `deflate` call on the invariant

Batch C (`deflate_call` / `trailer_step`). After the strategies and the markers, `deflate` returns
`Z_OK` unless the flush is `Z_FINISH`; with `Z_FINISH` it returns `Z_STREAM_END` when no trailer is
due (`wrap ≤ 0`), and otherwise writes the zlib or gzip trailer, flushes, negates `wrap` and
reports whether bytes are left. The trailer runs only on a finished stream with nothing pending
(the premise `finish`, which the strategy meaning gives), so no symbol is recorded
(`CallFacts.finishSym`) and `DInv.lift_empty` carries the invariant.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- What the trailer step leaves. -/
def TrailerOut (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState) (buf : Array UInt8)
    (flush : Int32) (run : Except Fault (Int32 × Heap)) : Prop :=
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
      (0 < d.wrap.toInt ∧ flush = Z_FINISH ∧ d1.pending = 0))

/-- **The trailer step**: the trailer phase keeps `DInv ∧ HeaderInv ∧ CallFacts`. `finish`: with
`Z_FINISH` the trailer phase is reached only on a finished stream with nothing pending. -/
theorem trailer_step {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (inv : DInv h r ds z d) (header : HeaderInv d) (facts : CallFacts d)
    (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (flush : Int32) (finish : flush = Z_FINISH → d.status = FINISH_STATE ∧ d.pending = 0) :
    TrailerOut h r ds pb z d buf flush (trailerPhase (some r) (some (.tab ds)) flush h) := by
  by_cases f : flush = Z_FINISH
  · obtain ⟨st, p0⟩ := finish f
    have cursor := inv.shape.cursor p0
    have low : d.bi_valid.toInt < 8 := by have := inv.shape.biValid; omega
    have room : d.pending.toNat + 8 ≤ buf.size := by
      have := trees.base.size; have := trees.base.lit_lo; rw [p0]; simp; omega
    obtain ⟨rc, after, z1, d1, produced, run, good1, trees1, buffers1, account, fields, stage, rcs, cur1, end1, _,
      wrapF, endIff⟩ :=
      trailer_phase inv.good trees buffers cursor low out room flush
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
      refine ⟨fun e => ?_, fun e => ?_, fun _ => symEq.trans empty, fun _ => lookEq.trans (facts.finishLook st)⟩
      · rw [lookEq, symEq, maEq, mlEq, plEq, bsEq]; exact facts.fresh (by rw [← lfEq]; exact e)
      · rw [bsEq, ssEq]; exact facts.freshStart (by rw [← lfEq]; exact e)
    refine ⟨rc, after, z1, d1, produced, run, dinv, HeaderInv.of_busy (Or.inr (sEq.trans st)), callFacts, buffers1,
      trees1, account, stage, fields, rcs, fun e => ⟨f, sEq.trans st, ?_⟩, fun nf => absurd f nf, wrapF, endIff⟩
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
      ⟨fun e => absurd e (by decide), fun e => by rcases e with ⟨_, _, g⟩ | ⟨_, g, _⟩ <;> exact absurd g f⟩⟩

end Zlib.Deflate.Universal.Call
