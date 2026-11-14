import ZlibF.Proof.«deflate.c.quiet-phases»

/-!
# deflate.c: the header phase's early return, with the stage of a kept status (`DeflateQuietIn`)

`header_quiet2` is `header_quiet` with one more fact on the early return: when the rank is kept,
the status is EXTRA, NAME or COMMENT, the stages that copy a gzip header field. These states have a
gzip header record (`HeaderInv.record`), so with no record the early return lowers the rank. The
stage lemmas are restated with `QProg2`; their proofs follow those of `deflate.c.quiet-phases`.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- `QProg`, and a kept status is one of the field stages. -/
def QProg2 (d d' : DeflateState) : Prop :=
  rank d' < rank d ∨ (d'.status = d.status ∧ d.gzindex.toNat < d'.gzindex.toNat ∧
    (d.status = EXTRA_STATE ∨ d.status = NAME_STATE ∨ d.status = COMMENT_STATE))

/-- `QZProg` with `QProg2`. -/
def QZProg2 (d d' : DeflateState) : Prop :=
  rank d' ≤ rank d ∧ (d.pending = 0 → QProg2 d d')

/-- `HeaderDone` with the facts of an early return (`QZProg2`). -/
def HeaderDoneQ2 (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState) (buf : Array UInt8)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
    StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ StageFrame h after r ds pb d z z' produced ∧
    d'.bi_valid.toInt < 8 ∧
    d'.gzhead = d.gzhead ∧ HeaderShape d d' ∧ (HeaderInv d → HeaderInv d') ∧ z'.next_out ≠ .null ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧ d'.pending ≠ 0 ∧ d'.status ≠ FINISH_STATE ∧
      z'.avail_out = 0 ∧ QZProg2 d d') ∨
     (run = k after ∧ d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧
       d'.last_flush = d.last_flush))

theorem HeaderDoneQ2.back {h h1 : Heap} {r : ZStreamRef} {ds pb : Nat} {z z1 : ZStream} {d d1 : DeflateState}
    {buf buf1 : Array UInt8} {run : Except Fault (Int32 × Heap)} {k : M Int32} {p : Nat}
    (done : HeaderDoneQ2 h1 r ds pb z1 d1 buf1 run k) (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (stage : StageFrame h h1 r ds pb d z z1 p) (account : StreamAccounting z z1 0 p)
    (shape : HeaderShape d d1) (header : HeaderInv d → HeaderInv d1) (lastFlush : d1.last_flush = d.last_flush)
    (size : buf1.size = buf.size) (lt : rank d1 < rank d) :
    HeaderDoneQ2 h r ds pb z d buf run k := by
  obtain ⟨after, z', d', q, good', ⟨b', t, s⟩, buffers', acc, stage', bits', gz', shape', header', out, outcome⟩ := done
  refine ⟨after, z', d', p + q, good', ⟨b', t, s.trans size⟩, buffers', stream_accounting_trans account acc,
    StageFrame.trans stage stage' (HeaderShape.owned shape) good buffers,
    bits', gz'.trans shape.gzhead, shape.trans shape', fun hd => header' (header hd), out, ?_⟩
  rcases outcome with ⟨e, lf, pn, sf, fo, le, _⟩ | ⟨e, st, zero, cur, lf⟩
  · exact Or.inl ⟨e, lf, pn, sf, fo, ⟨by omega, fun _ => Or.inl (by omega)⟩⟩
  · exact Or.inr ⟨e, st, zero, cur, lf.trans lastFlush⟩

theorem t_hcrc_q2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (status : d.status = HCRC_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDoneQ2 h r ds pb z d buf (hcrcStage (some r) (some (.tab ds)) k h) k := by
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

theorem t_comment_q2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = COMMENT_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDoneQ2 h r ds pb z d buf (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, _, gzhead1, bits1, pbuf1, pbs1,
    out1, shape1, stage1⟩, _, outcome⟩ :=
    comment_stage_q good trees buffers cursor low out globals status record getg ready pendLe
      (hcrcStage (some r) (some (.tab ds)) k)
  rcases outcome with ⟨e, _, lf, pn, sf, fo, stEq, prog⟩ | ⟨e, st1, cursor1, pend1, _, _, lf1⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf, pn, sf, fo,
        ⟨rank_le_of_status stEq, fun z0 => Or.inr ⟨stEq, prog (pending_lt_of_zero trees z0), Or.inr (Or.inr status)⟩⟩⟩⟩
  · rw [e]
    exact (t_hcrc_q2 good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 st1
      (by rw [gzhead1]; exact record) gz1 (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) lf1 size1 (rank_lt_of st1 status (by decide))

theorem t_name_q2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = NAME_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.name) (absent : g.name = .null → d.gzindex = 0)
    (comment : StringLater h z ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDoneQ2 h r ds pb z d buf (nameStage (some r) (some (.tab ds))
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k)) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1, pbuf1,
    pbs1, out1, shape1, stage1⟩, keep1, outcome⟩ :=
    name_stage_q good trees buffers cursor low out globals status record getg ready pendLe
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))
  rcases outcome with ⟨e, _, lf, pn, sf, fo, stEq, prog⟩ | ⟨e, st1, cursor1, pend1, _, gzi, lf1⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf, pn, sf, fo,
        ⟨rank_le_of_status stEq, fun z0 => Or.inr ⟨stEq, prog (pending_lt_of_zero trees z0), Or.inr (Or.inl status)⟩⟩⟩⟩
  · rw [e]
    have zero1 : d1.gzindex = 0 := by
      obtain ⟨present, gone⟩ := gzi rfl
      by_cases n : g.name = .null
      · rw [gone n, absent n]
      · exact present n
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    exact (t_comment_q2 good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1 st1
      (by rw [gzhead1]; exact record) gz1 ((comment.keep keep1 account1).ready zero1)
      (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) lf1 size1 (rank_lt_of st1 status (by decide))

theorem t_extra_q2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
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
    HeaderDoneQ2 h r ds pb z d buf (extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds))
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))) h) k := by
  obtain ⟨p1, H1, z1, d1, good1, buffers1, account1, ⟨buf1, trees1, size1⟩, gz1, static1, out1, keep1, shape1,
    stage1, gzhead1, bits1, outcome⟩ :=
    extra_stage_q good trees buffers cursor low out globals status record getg extraMem progress below
      (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k)))
  rcases outcome with ⟨e, _, lf, pn, sf, fo, stEq, prog⟩ | ⟨e, st1, cursor1, pend1, _, gzi, lf1⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf, pn, sf, fo,
        ⟨rank_le_of_status stEq, fun z0 => Or.inr ⟨stEq, prog, Or.inl status⟩⟩⟩⟩
  · rw [e]
    have zero1 : d1.gzindex = 0 := by
      rcases gzi with z0 | ⟨n, same⟩
      · exact z0
      · rw [same, absent n]
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    exact (t_name_q2 good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1 st1
      (by rw [gzhead1]; exact record) gz1 ((name.keep keep1 account1).ready zero1) (fun _ => zero1)
      (comment.keep keep1 account1) (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) lf1 size1 (rank_lt_of st1 status (by decide))

theorem t_gzip_q2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (avail : z.avail_out ≠ 0) (globals : LibraryGlobals h)
    (status : d.status = GZIP_STATE) (pending : d.pending = 0)
    (header : ∀ i, d.gzhead = some (.tab i) → ∃ g, h.gzheaders i = some g ∧
      (g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
        eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb) ∧
      StringLater h z ds pb g.name ∧ StringLater h z ds pb g.comment)
    (noneOrSome : d.gzhead = none ∨ ∃ i, d.gzhead = some (.tab i)) (k : M Int32) :
    HeaderDoneQ2 h r ds pb z d buf (gzipStage (some r) (some (.tab ds)) (extraStage (some r) (some (.tab ds))
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
    exact (t_extra_q2 good1 trees1 buffers1 keys.2.2.2.2 (by rw [keys.2.2.2.1]; exact low) out1 globals1 keys.1
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

theorem t_init_q2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (avail : z.avail_out ≠ 0) (status : d.status = INIT_STATE)
    (pending : d.pending = 0) (k : M Int32) :
    HeaderDoneQ2 h r ds pb z d buf (wrapStage (some r) (some (.tab ds)) (initStage (some r) (some (.tab ds))
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


theorem header_phase_q2 {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (entry : HeaderEntry h z d ds pb buf)
    (flush : Int32) (k : M Int32) :
    HeaderDoneQ2 h r ds pb z d buf (headerPhase (some r) (some (.tab ds)) flush k h) k ∨
      (d.status = FINISH_STATE ∧ headerPhase (some r) (some (.tab ds)) flush k h = k h) := by
  rw [header_stages]
  have hs := good.live.hs
  have st := good.live.status
  unfold GoodStatus at st
  rcases st with e | e | e | e | e | e | e | e
  · obtain ⟨pend, avail⟩ := entry.fresh (Or.inl e)
    exact Or.inl (t_init_q2 good trees buffers cursor low out avail e pend k)
  · obtain ⟨pend, avail⟩ := entry.fresh (Or.inr e)
    obtain ⟨cases, header⟩ := entry.gzip e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide)]
    exact t_gzip_q2 good trees buffers cursor low out avail globals e pend header cases k
  · obtain ⟨i, g, record, getg, pendLe, extraFacts, _, _⟩ := entry.writing (Or.inl e)
    obtain ⟨mem, prog, absent, name, comment, below⟩ := extraFacts e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide)]
    exact t_extra_q2 good trees buffers cursor low out globals e record getg mem prog absent name comment below k
  · obtain ⟨i, g, record, getg, pendLe, _, nameFacts, _⟩ := entry.writing (Or.inr (Or.inl e))
    obtain ⟨ready, absent, comment⟩ := nameFacts e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide)]
    exact t_name_q2 good trees buffers cursor low out globals e record getg ready absent comment pendLe k
  · obtain ⟨i, g, record, getg, pendLe, _, _, commentFacts⟩ := entry.writing (Or.inr (Or.inr (Or.inl e)))
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide)]
    exact t_comment_q2 good trees buffers cursor low out globals e record getg (commentFacts e) pendLe k
  · obtain ⟨i, g, record, getg, pendLe, _, _, _⟩ := entry.writing (Or.inr (Or.inr (Or.inr e)))
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide),
      comment_stage_skip hs _ (by rw [e]; decide)]
    exact t_hcrc_q2 good trees buffers cursor low out e record getg pendLe k
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
def HeaderQuietOut2 (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DInv after r ds z' d' ∧ HeaderInv d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
    StageFrame h after r ds pb d z z' produced ∧ (∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b) ∧
    z'.next_out ≠ .null ∧ d'.lit_bufsize = d.lit_bufsize ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧ d'.pending ≠ 0 ∧
        CallFacts d' ∧ z'.avail_out = 0 ∧
        (rank d' < rank d ∨ (d'.status = d.status ∧ d.gzindex.toNat < d'.gzindex.toNat ∧
          (d.status = EXTRA_STATE ∨ d.status = NAME_STATE ∨ d.status = COMMENT_STATE)))) ∨
     (run = k after ∧ d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧
        d'.last_flush = d.last_flush ∧ CallFacts d')) ∧
    d'.lookahead = d.lookahead ∧ d'.match_available = d.match_available ∧ d'.sym_next = d.sym_next ∧
    d'.level = d.level ∧ d'.strstart = d.strstart ∧ d'.block_start = d.block_start ∧ d'.wrap = d.wrap

/-- **The header phase from a mid-call state, for `DeflateQuiet`**: `header_step_mid` from a drained
`pending_buf` (`pending`), and its early return makes progress: the header rank drops, or the status
is kept and `gzindex` grew. The header phase keeps the positions, the lookahead, the symbols, the
level and `wrap`. -/
theorem header_quiet2 {h0 h : Heap} {r : ZStreamRef} {ds pb : Nat} {z0 z : ZStream} {d0 d : DeflateState}
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
    HeaderQuietOut2 h r ds pb z d (headerPhase (some r) (some (.tab ds)) flush k h) k := by
  have globals : LibraryGlobals h := by
    have g := inv0.globals
    unfold LibraryGlobals at g ⊢
    rw [static0]; exact g
  have done := (header_phase_q2 good trees buffers cursor low out globals entry flush k).resolve_right
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

#print axioms Zlib.Deflate.Universal.Quiet.header_quiet2
