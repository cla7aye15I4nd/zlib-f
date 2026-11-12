import ZlibF.Proof.«deflate.c.universal-call-markers»

/-!
# deflate.c: the header phase of one `deflate` call

Batch C (`deflate_header_trailer`). `headerPhase` is the chain of the header stages
(`header_stages`); a stage whose status test fails passes the heap on unchanged.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

section skip
variable {h : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} (state : h.dstates ds = some d) (k : M Int32)
include state

theorem wrap_stage_skip (no : ¬ (d.status = INIT_STATE ∧ d.wrap = 0)) :
    wrapStage (some r) (some (.tab ds)) k h = k h := by
  unfold wrapStage
  by_cases st : d.status = INIT_STATE
  · have w : d.wrap ≠ 0 := fun e => no ⟨st, e⟩
    simp [bind_app, rdD_eq, state, st, w]
  · simp [bind_app, rdD_eq, state, st]

theorem wrap_stage_busy (st : d.status = INIT_STATE) (w : d.wrap = 0) :
    wrapStage (some r) (some (.tab ds)) k h = k (setD h ds { d with status := BUSY_STATE }) := by
  unfold wrapStage
  simp [bind_app, rdD_eq, state, st, w, wrD_eq]

theorem init_stage_skip (no : d.status ≠ INIT_STATE) : initStage (some r) (some (.tab ds)) k h = k h := by
  unfold initStage; simp [bind_app, rdD_eq, state, no]

theorem gzip_stage_skip (no : d.status ≠ GZIP_STATE) : gzipStage (some r) (some (.tab ds)) k h = k h := by
  unfold gzipStage; simp [bind_app, rdD_eq, state, no]

theorem extra_stage_skip (no : d.status ≠ EXTRA_STATE) : extraStage (some r) (some (.tab ds)) k h = k h := by
  unfold extraStage; simp [bind_app, rdD_eq, state, no]

theorem name_stage_skip (no : d.status ≠ NAME_STATE) : nameStage (some r) (some (.tab ds)) k h = k h := by
  unfold nameStage; simp [bind_app, rdD_eq, state, no]

theorem comment_stage_skip (no : d.status ≠ COMMENT_STATE) : commentStage (some r) (some (.tab ds)) k h = k h := by
  unfold commentStage; simp [bind_app, rdD_eq, state, no]

theorem hcrc_stage_skip (no : d.status ≠ HCRC_STATE) : hcrcStage (some r) (some (.tab ds)) k h = k h := by
  unfold hcrcStage; simp [bind_app, rdD_eq, state, no]

end skip

/-- The end of the header phase from some stage on: `Z_OK` with the invariants, or the rest of the
call in `BUSY_STATE` with nothing pending. -/
def HeaderDone (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState) (buf : Array UInt8)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
    StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ StageFrame h after r ds pb d z z' produced ∧
    d'.bi_valid.toInt < 8 ∧
    d'.gzhead = d.gzhead ∧ HeaderShape d d' ∧ (HeaderInv d → HeaderInv d') ∧ z'.next_out ≠ .null ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1) ∨
     (run = k after ∧ d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf))

/-- From a header state with the record attached, the header facts hold after any change of the
header stages (`sym_next` and `gzhead` are kept). -/
theorem header_inv_writing {d d' : DeflateState} (header : HeaderInv d)
    (writing : d.status = INIT_STATE ∨ d.status = GZIP_STATE ∨ d.status = EXTRA_STATE ∨
      d.status = NAME_STATE ∨ d.status = COMMENT_STATE ∨ d.status = HCRC_STATE)
    (record : d.gzhead ≠ none) (shape : HeaderShape d d') : HeaderInv d' :=
  ⟨fun _ => shape.sym_next.trans (header.empty writing), fun _ => by rw [shape.gzhead]; exact record⟩

/-- A later `HeaderDone` is one for an earlier state that led to it. -/
theorem HeaderDone.back {h h1 : Heap} {r : ZStreamRef} {ds pb : Nat} {z z1 : ZStream} {d d1 : DeflateState}
    {buf buf1 : Array UInt8} {run : Except Fault (Int32 × Heap)} {k : M Int32} {p : Nat}
    (done : HeaderDone h1 r ds pb z1 d1 buf1 run k) (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (stage : StageFrame h h1 r ds pb d z z1 p) (account : StreamAccounting z z1 0 p)
    (shape : HeaderShape d d1) (header : HeaderInv d → HeaderInv d1) (size : buf1.size = buf.size) :
    HeaderDone h r ds pb z d buf run k := by
  obtain ⟨after, z', d', q, good', ⟨b', t, s⟩, buffers', acc, stage', bits', gz', shape', header', out, outcome⟩ := done
  exact ⟨after, z', d', p + q, good', ⟨b', t, s.trans size⟩, buffers', stream_accounting_trans account acc,
    StageFrame.trans stage stage' (HeaderShape.owned shape) good buffers,
    bits', gz'.trans shape.gzhead, shape.trans shape', fun hd => header' (header hd), out, outcome⟩

theorem t_hcrc {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (status : d.status = HCRC_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDone h r ds pb z d buf (hcrcStage (some r) (some (.tab ds)) k h) k := by
  obtain ⟨after, z1, d1, produced, ⟨good1, trees1, buffers1, account1, _, _, gzhead1, bits1, _, _, out1, shape1,
    stage1⟩, outcome⟩ := hcrc_stage good trees buffers cursor low out status record getg pendLe k
  refine ⟨after, z1, d1, produced, good1, trees1, buffers1, account1, stage1, by rw [bits1]; exact low, gzhead1, shape1,
    (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, ?_⟩
  rcases outcome with ⟨e, _, lf⟩ | ⟨e, st, zero, cur, _⟩
  · exact Or.inl ⟨e, lf⟩
  · exact Or.inr ⟨e, st, zero, cur⟩

theorem t_comment {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = COMMENT_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDone h r ds pb z d buf (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, _, gzhead1, bits1, pbuf1, pbs1,
    out1, shape1, stage1⟩, _, outcome⟩ :=
    comment_stage good trees buffers cursor low out globals status record getg ready pendLe
      (hcrcStage (some r) (some (.tab ds)) k)
  rcases outcome with ⟨e, _, lf⟩ | ⟨e, st1, cursor1, pend1, _, _⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf⟩⟩
  · rw [e]
    exact (t_hcrc good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 st1
      (by rw [gzhead1]; exact record) gz1 (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) size1

/-- A caller string the call will read later: a C string apart from the output and the stream. -/
def StringLater (h : Heap) (z : ZStream) (ds pb : Nat) (p : BPtr) : Prop :=
  p ≠ .null → ∃ xs, CString h p xs ∧ Separate p (xs.length + 1) z.next_out z.avail_out.toNat ∧
    (∀ b, ByteRoot p b → b ≠ pb ∧ b ≠ ds)

/-- A later string survives a step that keeps the caller bytes. -/
theorem StringLater.keep {h h1 : Heap} {z z1 : ZStream} {ds pb produced : Nat} {p : BPtr}
    (later : StringLater h z ds pb p) (keep : CallerKeep h h1 z ds pb) (account : StreamAccounting z z1 0 produced) :
    StringLater h1 z1 ds pb p := by
  intro present
  obtain ⟨xs, cs, apart, keys⟩ := later present
  refine ⟨xs, ⟨keep p _ _ cs.1 apart keys, cs.2.1, cs.2.2⟩, ?_, keys⟩
  rw [account.2.2.2.2.2.1]; exact separate_advance apart account.2.2.2.1

theorem StringLater.ready {h : Heap} {z : ZStream} {d : DeflateState} {ds pb : Nat} {p : BPtr}
    (later : StringLater h z ds pb p) (zero : d.gzindex = 0) : StringReady h z d ds pb p := by
  intro present
  obtain ⟨xs, cs, apart, keys⟩ := later present
  exact ⟨xs, cs, by rw [zero]; exact Nat.zero_le _, apart, keys⟩

theorem t_name {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = NAME_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.name) (absent : g.name = .null → d.gzindex = 0)
    (comment : StringLater h z ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDone h r ds pb z d buf (nameStage (some r) (some (.tab ds))
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k)) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1, pbuf1,
    pbs1, out1, shape1, stage1⟩, keep1, outcome⟩ :=
    name_stage good trees buffers cursor low out globals status record getg ready pendLe
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))
  rcases outcome with ⟨e, _, lf⟩ | ⟨e, st1, cursor1, pend1, _, gzi⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf⟩⟩
  · rw [e]
    have zero1 : d1.gzindex = 0 := by
      obtain ⟨present, gone⟩ := gzi rfl
      by_cases n : g.name = .null
      · rw [gone n, absent n]
      · exact present n
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    exact (t_comment good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1 st1
      (by rw [gzhead1]; exact record) gz1 ((comment.keep keep1 account1).ready zero1)
      (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) size1

theorem t_extra {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
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
    HeaderDone h r ds pb z d buf (extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds))
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))) h) k := by
  obtain ⟨p1, H1, z1, d1, good1, buffers1, account1, ⟨buf1, trees1, size1⟩, gz1, static1, out1, keep1, shape1,
    stage1, gzhead1, bits1, outcome⟩ :=
    extra_stage good trees buffers cursor low out globals status record getg extraMem progress below
      (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k)))
  rcases outcome with ⟨e, _, lf⟩ | ⟨e, st1, cursor1, pend1, _, gzi⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, stage1, (by rw [bits1]; exact low), gzhead1, shape1,
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1), out1, Or.inl ⟨e, lf⟩⟩
  · rw [e]
    have zero1 : d1.gzindex = 0 := by
      rcases gzi with z0 | ⟨n, same⟩
      · exact z0
      · rw [same, absent n]
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    exact (t_name good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1 st1
      (by rw [gzhead1]; exact record) gz1 ((name.keep keep1 account1).ready zero1) (fun _ => zero1)
      (comment.keep keep1 account1) (by rw [size1]; exact pend1) k).back good buffers stage1 account1 shape1 (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) shape1) size1

/-- The `pending_buf` of a good state with the same buffer pointer and size as an earlier one. -/
theorem trees_same_buffer {h h0 : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d d0 : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees0 : TreesInvAt h0 ds d0 pb buf)
    (pbuf : d.pending_buf = d0.pending_buf) (lit : d.lit_bufsize = d0.lit_bufsize) :
    ∃ buf', TreesInvAt h ds d pb buf' ∧ buf'.size = buf.size := by
  obtain ⟨pb', buf', trees⟩ := Block.trees_of_good good
  have same : pb' = pb := by
    have p1 := trees.base.pbuf; rw [pbuf, trees0.base.pbuf] at p1; simpa using p1.symm
  subst same
  refine ⟨buf', trees, ?_⟩
  rw [trees.base.size, trees0.base.size, lit]

theorem t_gzip {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (avail : z.avail_out ≠ 0) (globals : LibraryGlobals h)
    (status : d.status = GZIP_STATE) (pending : d.pending = 0)
    (header : ∀ i, d.gzhead = some (.tab i) → ∃ g, h.gzheaders i = some g ∧
      (g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
        eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb) ∧
      StringLater h z ds pb g.name ∧ StringLater h z ds pb g.comment)
    (noneOrSome : d.gzhead = none ∨ ∃ i, d.gzhead = some (.tab i)) (k : M Int32) :
    HeaderDone h r ds pb z d buf (gzipStage (some r) (some (.tab ds)) (extraStage (some r) (some (.tab ds))
      (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds))
        (hcrcStage (some r) (some (.tab ds)) k)))) h) k := by
  have sizeLo : 512 ≤ buf.size := by have := trees.base.size; have := trees.base.lit_lo; omega
  rcases noneOrSome with none | ⟨i, record⟩
  · obtain ⟨produced, after, z', d', good', buffers', account, stage, _, _, low', empty', fields, run⟩ :=
      gzip_plain_stage good trees buffers cursor status pending none low avail out
        (extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds)) (commentStage (some r)
          (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))))
    have keys : d'.pending_buf = d.pending_buf ∧ d'.lit_bufsize = d.lit_bufsize ∧ d'.gzhead = d.gzhead ∧
        d'.status = BUSY_STATE := by
      rw [fields]; exact ⟨rfl, rfl, rfl, rfl⟩
    have out' : z'.next_out ≠ .null := by rw [account.2.2.2.2.2.1]; exact advance_ne_null out _
    by_cases zero : d'.pending = 0
    · have skip : extraStage (some r) (some (.tab ds)) (nameStage (some r) (some (.tab ds)) (commentStage (some r)
          (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))) after = k after := by
        have hs := good'.live.hs
        rw [extra_stage_skip hs _ (by rw [keys.2.2.2]; decide), name_stage_skip hs _ (by rw [keys.2.2.2]; decide),
          comment_stage_skip hs _ (by rw [keys.2.2.2]; decide), hcrc_stage_skip hs _ (by rw [keys.2.2.2]; decide)]
      refine ⟨after, z', d', produced, good', trees_same_buffer good' trees keys.1 keys.2.1, buffers', account,
        stage, low', keys.2.2.1, ⟨_, _, _, _, _, _, _, _, fields⟩, fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out',
        Or.inr ⟨?_, keys.2.2.2, zero, empty' zero⟩⟩
      rw [run]; simp [zero, skip]
    · obtain ⟨buf', trees', size'⟩ := trees_same_buffer good' trees keys.1 keys.2.1
      obtain ⟨good5, buffers5, _⟩ := last_flush_frame (pb := pb) good' trees' buffers' (-1)
      refine ⟨_, z', _, produced, good5, ⟨buf', trees_at_buffer good5 trees'.base.pbuf trees'.base.bytes, size'⟩,
        buffers5, account, ?_, low', keys.2.2.1, HeaderShape.trans ⟨_, _, _, _, _, _, _, _, fields⟩ ⟨_, _, _, _, _, _, _, _, rfl⟩,
        fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out', Or.inl ⟨?_, rfl⟩⟩
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
    have out1 : z1.next_out ≠ .null := by rw [account1.2.2.2.2.2.1]; exact advance_ne_null out _
    rw [run1]
    exact (t_extra good1 trees1 buffers1 keys.2.2.2.2 (by rw [keys.2.2.2.1]; exact low) out1 globals1 keys.1
      (by rw [keys.2.2.1]; exact record) (by rw [frame1.gzheaders]; exact getg)
      (fun present => by
        obtain ⟨rs, eo, ea, e, get, fit, ne⟩ := extraMem present
        exact ⟨rs, eo, ea, e, by rw [frame1.views rs ne]; exact get, fit, ne⟩)
      (fun _ => by rw [keys.2.1]; exact Nat.zero_le _) (fun _ => keys.2.1)
      (name.keep keep1 account1) (comment.keep keep1 account1) (by omega) k).back good buffers
      (StageFrame.of_header frame1 good buffers trees.base.pbuf account1 good1.live.hz) account1
      ⟨_, _, _, _, _, _, _, _, fields1⟩
      (fun hd => header_inv_writing hd (by rw [status]; decide) (by rw [record]; simp) ⟨_, _, _, _, _, _, _, _, fields1⟩)
      size1

theorem t_init {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (avail : z.avail_out ≠ 0) (status : d.status = INIT_STATE)
    (pending : d.pending = 0) (k : M Int32) :
    HeaderDone h r ds pb z d buf (wrapStage (some r) (some (.tab ds)) (initStage (some r) (some (.tab ds))
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
      Or.inr ⟨?_, rfl, pending, cursor⟩⟩
    rw [wrap_stage_busy good.live.hs _ status w]
    exact skipAll (setD_dstates_same _ _ _) rfl
  · rw [wrap_stage_skip good.live.hs _ (fun e => w e.2)]
    obtain ⟨produced, after, z', d', good', buffers', account, _, _, low', empty', fields, run, stage⟩ :=
      init_stage good trees buffers cursor status pending low avail out
        (gzipStage (some r) (some (.tab ds)) (extraStage (some r) (some (.tab ds))
          (nameStage (some r) (some (.tab ds)) (commentStage (some r) (some (.tab ds))
            (hcrcStage (some r) (some (.tab ds)) k)))))
    have keys : d'.pending_buf = d.pending_buf ∧ d'.lit_bufsize = d.lit_bufsize ∧ d'.gzhead = d.gzhead ∧
        d'.status = BUSY_STATE := by
      rw [fields]; exact ⟨rfl, rfl, rfl, rfl⟩
    have out' : z'.next_out ≠ .null := by rw [account.2.2.2.2.2.1]; exact advance_ne_null out _
    by_cases zero : d'.pending = 0
    · refine ⟨after, z', d', produced, good', trees_same_buffer good' trees keys.1 keys.2.1, buffers', account,
        stage, low', keys.2.2.1, ⟨_, _, _, _, _, _, _, _, fields⟩, fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out',
        Or.inr ⟨?_, keys.2.2.2, zero, empty' zero⟩⟩
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
        fun _ => HeaderInv.of_busy (Or.inl keys.2.2.2), out', Or.inl ⟨?_, rfl⟩⟩
      · have s := StageFrame.trans stage (StageFrame.state good' buffers' trees'.base.pbuf { d' with last_flush := -1 })
          (HeaderShape.owned (⟨_, _, _, _, _, _, _, _, fields⟩ : HeaderShape d d')) good buffers
        rwa [Nat.add_zero] at s
      · rw [run]; simp [zero]

/-- What the header phase needs at its entry, by status. -/
structure HeaderEntry (h : Heap) (z : ZStream) (d : DeflateState) (ds pb : Nat) (buf : Array UInt8) : Prop where
  fresh : d.status = INIT_STATE ∨ d.status = GZIP_STATE → d.pending = 0 ∧ z.avail_out ≠ 0
  gzip : d.status = GZIP_STATE → (d.gzhead = none ∨ ∃ i, d.gzhead = some (.tab i)) ∧
    ∀ i, d.gzhead = some (.tab i) → ∃ g, h.gzheaders i = some g ∧
      (g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
        eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb) ∧
      StringLater h z ds pb g.name ∧ StringLater h z ds pb g.comment
  writing : d.status = EXTRA_STATE ∨ d.status = NAME_STATE ∨ d.status = COMMENT_STATE ∨ d.status = HCRC_STATE →
    ∃ i g, d.gzhead = some (.tab i) ∧ h.gzheaders i = some g ∧ d.pending.toNat ≤ buf.size ∧
      (d.status = EXTRA_STATE →
        (g.extra ≠ .null → ∃ rs eo ea, g.extra = .ref rs eo ∧ Space.get h rs = some ea ∧
          eo + g.extra_len.toNat % 2 ^ 16 ≤ ea.size ∧ rs ≠ .blk pb) ∧
        (g.extra ≠ .null → d.gzindex.toNat ≤ g.extra_len.toNat % 2 ^ 16) ∧ (g.extra = .null → d.gzindex = 0) ∧
        StringLater h z ds pb g.name ∧ StringLater h z ds pb g.comment ∧ d.pending.toNat < buf.size) ∧
      (d.status = NAME_STATE → StringReady h z d ds pb g.name ∧ (g.name = .null → d.gzindex = 0) ∧
        StringLater h z ds pb g.comment) ∧
      (d.status = COMMENT_STATE → StringReady h z d ds pb g.comment)
  busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE → d.pending = 0

/-- **The header phase** of a `deflate` call, for every entry status. -/
theorem header_phase {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (entry : HeaderEntry h z d ds pb buf)
    (flush : Int32) (k : M Int32) :
    HeaderDone h r ds pb z d buf (headerPhase (some r) (some (.tab ds)) flush k h) k ∨
      (d.status = FINISH_STATE ∧ headerPhase (some r) (some (.tab ds)) flush k h = k h) := by
  rw [header_stages]
  have hs := good.live.hs
  have st := good.live.status
  unfold GoodStatus at st
  rcases st with e | e | e | e | e | e | e | e
  · obtain ⟨pend, avail⟩ := entry.fresh (Or.inl e)
    exact Or.inl (t_init good trees buffers cursor low out avail e pend k)
  · obtain ⟨pend, avail⟩ := entry.fresh (Or.inr e)
    obtain ⟨cases, header⟩ := entry.gzip e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide)]
    exact t_gzip good trees buffers cursor low out avail globals e pend header cases k
  · obtain ⟨i, g, record, getg, pendLe, extraFacts, _, _⟩ := entry.writing (Or.inl e)
    obtain ⟨mem, prog, absent, name, comment, below⟩ := extraFacts e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide)]
    exact t_extra good trees buffers cursor low out globals e record getg mem prog absent name comment below k
  · obtain ⟨i, g, record, getg, pendLe, _, nameFacts, _⟩ := entry.writing (Or.inr (Or.inl e))
    obtain ⟨ready, absent, comment⟩ := nameFacts e
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide)]
    exact t_name good trees buffers cursor low out globals e record getg ready absent comment pendLe k
  · obtain ⟨i, g, record, getg, pendLe, _, _, commentFacts⟩ := entry.writing (Or.inr (Or.inr (Or.inl e)))
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide)]
    exact t_comment good trees buffers cursor low out globals e record getg (commentFacts e) pendLe k
  · obtain ⟨i, g, record, getg, pendLe, _, _, _⟩ := entry.writing (Or.inr (Or.inr (Or.inr e)))
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide),
      comment_stage_skip hs _ (by rw [e]; decide)]
    exact t_hcrc good trees buffers cursor low out e record getg pendLe k
  · have pend := entry.busy (Or.inl e)
    left
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide),
      comment_stage_skip hs _ (by rw [e]; decide), hcrc_stage_skip hs _ (by rw [e]; decide)]
    exact ⟨h, z, d, 0, good, ⟨buf, trees, rfl⟩, buffers, stream_accounting_zero z,
      StageFrame.refl good buffers trees.base.pbuf, low, rfl, HeaderShape.refl d, id, out,
      Or.inr ⟨rfl, e, pend, cursor⟩⟩
  · right
    refine ⟨e, ?_⟩
    rw [wrap_stage_skip hs _ (fun c => by rw [e] at c; exact absurd c.1 (by decide)),
      init_stage_skip hs _ (by rw [e]; decide), gzip_stage_skip hs _ (by rw [e]; decide),
      extra_stage_skip hs _ (by rw [e]; decide), name_stage_skip hs _ (by rw [e]; decide),
      comment_stage_skip hs _ (by rw [e]; decide), hcrc_stage_skip hs _ (by rw [e]; decide)]

end Zlib.Deflate.Universal.Call
