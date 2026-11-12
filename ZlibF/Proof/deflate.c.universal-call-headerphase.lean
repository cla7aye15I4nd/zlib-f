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
def HeaderDone (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState) (buf : Array UInt8)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DGood after r ds z' d' ∧ (∃ buf', TreesInvAt after ds d' pb buf' ∧ buf'.size = buf.size) ∧
    StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ d'.bi_valid = d.bi_valid ∧
    d'.gzhead = d.gzhead ∧ z'.next_out ≠ .null ∧
    (run = .ok (Z_OK, after) ∨
     (run = k after ∧ d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf))

/-- A later `HeaderDone` is one for an earlier state that led to it. -/
theorem HeaderDone.back {r : ZStreamRef} {ds pb : Nat} {z z1 : ZStream} {d d1 : DeflateState}
    {buf buf1 : Array UInt8} {run : Except Fault (Int32 × Heap)} {k : M Int32} {p : Nat}
    (done : HeaderDone r ds pb z1 d1 buf1 run k) (account : StreamAccounting z z1 0 p)
    (bits : d1.bi_valid = d.bi_valid) (gzhead : d1.gzhead = d.gzhead) (size : buf1.size = buf.size) :
    HeaderDone r ds pb z d buf run k := by
  obtain ⟨after, z', d', q, good, ⟨b', t, s⟩, buffers, acc, bits', gz', out, outcome⟩ := done
  exact ⟨after, z', d', p + q, good, ⟨b', t, s.trans size⟩, buffers, stream_accounting_trans account acc,
    bits'.trans bits, gz'.trans gzhead, out, outcome⟩

theorem t_hcrc {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (status : d.status = HCRC_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDone r ds pb z d buf (hcrcStage (some r) (some (.tab ds)) k h) k := by
  obtain ⟨after, z1, d1, produced, ⟨good1, trees1, buffers1, account1, _, _, gzhead1, bits1, _, _, out1⟩,
    outcome⟩ := hcrc_stage good trees buffers cursor low out status record getg pendLe k
  refine ⟨after, z1, d1, produced, good1, trees1, buffers1, account1, bits1, gzhead1, out1, ?_⟩
  rcases outcome with ⟨e, _⟩ | ⟨e, st, zero, cur, _⟩
  · exact Or.inl e
  · exact Or.inr ⟨e, st, zero, cur⟩

theorem t_comment {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) (globals : LibraryGlobals h) (status : d.status = COMMENT_STATE)
    {i : Nat} {g : GzHeader} (record : d.gzhead = some (.tab i)) (getg : h.gzheaders i = some g)
    (ready : StringReady h z d ds pb g.comment) (pendLe : d.pending.toNat ≤ buf.size) (k : M Int32) :
    HeaderDone r ds pb z d buf (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, _, gzhead1, bits1, pbuf1, pbs1,
    out1⟩, _, outcome⟩ :=
    comment_stage good trees buffers cursor low out globals status record getg ready pendLe
      (hcrcStage (some r) (some (.tab ds)) k)
  rcases outcome with ⟨e, _⟩ | ⟨e, st1, cursor1, pend1, _, _⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, bits1, gzhead1, out1, Or.inl e⟩
  · rw [e]
    exact (t_hcrc good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 st1
      (by rw [gzhead1]; exact record) gz1 (by rw [size1]; exact pend1) k).back account1 bits1 gzhead1 size1

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
    HeaderDone r ds pb z d buf (nameStage (some r) (some (.tab ds))
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k)) h) k := by
  obtain ⟨H1, z1, d1, p1, ⟨good1, ⟨buf1, trees1, size1⟩, buffers1, account1, gz1, static1, gzhead1, bits1, pbuf1,
    pbs1, out1⟩, keep1, outcome⟩ :=
    name_stage good trees buffers cursor low out globals status record getg ready pendLe
      (commentStage (some r) (some (.tab ds)) (hcrcStage (some r) (some (.tab ds)) k))
  rcases outcome with ⟨e, _⟩ | ⟨e, st1, cursor1, pend1, _, gzi⟩
  · exact ⟨H1, z1, d1, p1, good1, ⟨buf1, trees1, size1⟩, buffers1, account1, bits1, gzhead1, out1, Or.inl e⟩
  · rw [e]
    have zero1 : d1.gzindex = 0 := by
      obtain ⟨present, gone⟩ := gzi rfl
      by_cases n : g.name = .null
      · rw [gone n, absent n]
      · exact present n
    have globals1 : LibraryGlobals H1 := by unfold LibraryGlobals at globals ⊢; rw [static1, globals]
    exact (t_comment good1 trees1 buffers1 cursor1 (by rw [bits1]; exact low) out1 globals1 st1
      (by rw [gzhead1]; exact record) gz1 ((comment.keep keep1 account1).ready zero1)
      (by rw [size1]; exact pend1) k).back account1 bits1 gzhead1 size1

end Zlib.Deflate.Universal.Call
