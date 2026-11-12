import ZlibF.Proof.«deflate.c.universal-call-header»
import ZlibF.Proof.«deflate.c.universal-strategy-frame»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-storage»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
import ZlibF.Proof.«deflate.c.engine.pending-counters»
import ZlibF.Proof.«deflate.c.engine.output-full-storage»

/-!
# deflate.c: the heap frame of the header, marker and trailer parts of a call

Batch C (`deflate_header_trailer`, for `deflate_call`). `StageFrame` is what a part of these
phases does to the heap, from its entry: batch B's `StratFrame` (the counts, the totals, the
written interval of the caller's output, the heap shape) and the narrow block frame
`OutputStorage` (only the stream root, the state record, `pending_buf` and the output block
change). Parts compose with `StageFrame.trans`; the facts `deflate_call` needs of the window,
`prev`, `head` and the static tables follow with `StageFrame.keeps`.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The heap frame of a part of the header, marker or trailer phase that reads no input. -/
def StageFrame (h after : Heap) (r : ZStreamRef) (ds pb : Nat) (d : DeflateState) (z z' : ZStream)
    (produced : Nat) : Prop :=
  StratFrame h after r ds d z z' 0 produced ∧ ∀ ob, ByteRoot z.next_out ob → OutputStorage h after r ds pb ob

/-- What the header stages change in the state record: the status, the pending and bit fields,
`gzindex` and `last_flush`. Every other field, among them `sym_next`, `gzhead`, the window and the
hash fields, is kept. -/
def HeaderShape (d d' : DeflateState) : Prop :=
  ∃ (st : Int32) (p : UInt64) (po : BPtr) (bb : UInt16) (bv bu : Int32) (gi : UInt64) (lf : Int32),
    d' = { d with
      status := st, pending := p, pending_out := po, bi_buf := bb, bi_valid := bv,
      bi_used := bu, gzindex := gi, last_flush := lf }

theorem HeaderShape.refl (d : DeflateState) : HeaderShape d d :=
  ⟨d.status, d.pending, d.pending_out, d.bi_buf, d.bi_valid, d.bi_used, d.gzindex, d.last_flush, rfl⟩

theorem HeaderShape.trans {a b c : DeflateState} (first : HeaderShape a b) (second : HeaderShape b c) :
    HeaderShape a c := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := first
  obtain ⟨st, p, po, bb, bv, bu, gi, lf, rfl⟩ := second
  exact ⟨st, p, po, bb, bv, bu, gi, lf, rfl⟩

/-- A record equation of the header stages gives the shape. -/
theorem HeaderShape.of_eq {d d' : DeflateState}
    (eq : d' = { d with
      status := d'.status, pending := d'.pending, pending_out := d'.pending_out,
      bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used, gzindex := d'.gzindex,
      last_flush := d'.last_flush }) : HeaderShape d d' :=
  ⟨_, _, _, _, _, _, _, _, eq⟩

theorem HeaderShape.sym_next {d d' : DeflateState} (shape : HeaderShape d d') : d'.sym_next = d.sym_next := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := shape; rfl

theorem HeaderShape.gzhead {d d' : DeflateState} (shape : HeaderShape d d') : d'.gzhead = d.gzhead := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := shape; rfl


theorem HeaderShape.owned {ds : Nat} {d d' : DeflateState} (shape : HeaderShape d d') :
    ∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := shape
  intro b; exact Iff.rfl

theorem byte_root_advance {p : BPtr} {k b : Nat} : ByteRoot (advance p k) b ↔ ByteRoot p b := by
  cases p with
  | null => rfl
  | ref r i => cases r <;> rfl

/-- A part that changes only the stream root (keeping its counts and totals), the state record
and `pending_buf`. -/
theorem StageFrame.of_private {h after : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState}
    {z z' : ZStream} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk pb) 0)
    (frame : Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = pb)) (shape : Zlib.Deflate.Proofs.Shape h after)
    (nalloc : after.nalloc = h.nalloc) (nextBlk : after.nextBlk = h.nextBlk)
    (account : StreamAccounting z z' 0 0) (totalIn : z'.total_in = z.total_in)
    (totalOut : z'.total_out = z.total_out) : StageFrame h after r ds pb d z z' 0 := by
  refine ⟨?_, fun ob _ => ⟨shape, nalloc, nextBlk, full_frame_weaken frame ?_⟩⟩
  · refine strat_frame_private account (by simpa using totalIn) totalOut (full_frame_weaken frame ?_) shape
      (full_shape_live_change shape) nalloc good.uniq (output_target good buffers)
    intro b changed
    rcases changed with root | same | same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · subst b; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr pbuf))))
  · intro b changed
    rcases changed with root | same | same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (Or.inl same))

theorem frame_refl (h : Heap) (changed : Nat → Prop) : Frame h h changed :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem StageFrame.refl {h : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState} {z : ZStream}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (pbuf : d.pending_buf = .ref (.blk pb) 0) :
    StageFrame h h r ds pb d z z 0 :=
  StageFrame.of_private good buffers pbuf (frame_refl h _) (Zlib.Deflate.Proofs.Shape.refl h) rfl rfl (stream_accounting_zero z) rfl rfl

/-- Writing the state record is a stage. -/
theorem StageFrame.state {h : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState} {z : ZStream}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (pbuf : d.pending_buf = .ref (.blk pb) 0)
    (d' : DeflateState) : StageFrame h (setD h ds d') r ds pb d z z 0 := by
  refine StageFrame.of_private good buffers pbuf ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    (shape_setD good.live.hs d') rfl rfl (stream_accounting_zero z) rfl rfl
  intro x _ out
  exact Zlib.Deflate.Proofs.DefaultInit.slot_setD_except h ds d' x (fun e => out (Or.inr (Or.inl e)))

/-- Writing `pending_buf` and then the state record is a stage. -/
theorem StageFrame.bytes {h : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState} {z : ZStream}
    {a0 : Array UInt8} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some a0) (a : Array UInt8)
    (d' : DeflateState) :
    StageFrame h (setD (Zlib.Trees.Proofs.Out.setB h pb a) ds d') r ds pb d z z 0 := by
  have stateB : (Zlib.Trees.Proofs.Out.setB h pb a).dstates ds = some d := good.live.hs
  refine StageFrame.of_private good buffers pbuf ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    ((shape_setB get a).trans (shape_setD stateB d')) rfl rfl (stream_accounting_zero z) rfl rfl
  intro x _ out
  have notDs : x ≠ ds := fun e => out (Or.inr (Or.inl e))
  have notPb : x ≠ pb := fun e => out (Or.inr (Or.inr e))
  simp [Zlib.Deflate.Proofs.DefaultInit.SlotSame, setD, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ notDs,
    upd_ne _ _ _ _ notPb]

/-- Writing the stream record, with the same counts and totals, is a stage. -/
theorem StageFrame.stream {h : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState} {z : ZStream}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (pbuf : d.pending_buf = .ref (.blk pb) 0)
    (z1 : ZStream) (account : StreamAccounting z z1 0 0) (totalIn : z1.total_in = z.total_in)
    (totalOut : z1.total_out = z.total_out) : StageFrame h (r.put h z1) r ds pb d z z1 0 := by
  have frame := stream_store_full_frame h r z1
  have counts : (r.put h z1).nalloc = h.nalloc ∧ (r.put h z1).nextBlk = h.nextBlk := by
    cases r <;> simp only [ZStreamRef.put] <;> (try split) <;> exact ⟨rfl, rfl⟩
  exact StageFrame.of_private good buffers pbuf (full_frame_weaken frame (fun _ c => Or.inl c))
    (shape_put good.live.hz z1) counts.1 counts.2 account totalIn totalOut

/-- Writing the stream record (same counts and totals) and then the state record is a stage. -/
theorem StageFrame.stream_state {h : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState} {z : ZStream}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (pbuf : d.pending_buf = .ref (.blk pb) 0)
    (z1 : ZStream) (account : StreamAccounting z z1 0 0) (totalIn : z1.total_in = z.total_in)
    (totalOut : z1.total_out = z.total_out) (d' : DeflateState) :
    StageFrame h (setD (r.put h z1) ds d') r ds pb d z z1 0 := by
  have counts : (r.put h z1).nalloc = h.nalloc ∧ (r.put h z1).nextBlk = h.nextBlk := by
    cases r <;> simp only [ZStreamRef.put] <;> (try split) <;> exact ⟨rfl, rfl⟩
  have stateP : (r.put h z1).dstates ds = some d := by simpa using good.live.hs
  have frame : Frame h (setD (r.put h z1) ds d') (fun b => StreamRoot r b ∨ b = ds ∨ b = pb) := by
    obtain ⟨st, al, ga, nb, na, _⟩ := stream_store_full_frame h r z1
    refine ⟨st, al, ga, nb, na, fun x _ out => ?_⟩
    exact (Zlib.Deflate.Proofs.DefaultInit.slot_put_except h r z1 x (fun e => out (Or.inl e))).trans
      (Zlib.Deflate.Proofs.DefaultInit.slot_setD_except (r.put h z1) ds d' x (fun e => out (Or.inr (Or.inl e))))
  exact StageFrame.of_private good buffers pbuf frame ((shape_put good.live.hz z1).trans (shape_setD stateP d'))
    counts.1 counts.2 account totalIn totalOut

/-- Two adjacent parts compose; the second starts from a state with the same owned blocks. -/
theorem StageFrame.trans {h m k : Heap} {r : ZStreamRef} {ds pb : Nat} {d d1 : DeflateState}
    {z z1 z2 : ZStream} {p1 p2 : Nat}
    (one : StageFrame h m r ds pb d z z1 p1) (two : StageFrame m k r ds pb d1 z1 z2 p2)
    (owned : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    StageFrame h k r ds pb d z z2 (p1 + p2) := by
  obtain ⟨strat1, storage1⟩ := one
  obtain ⟨strat2, storage2⟩ := two
  have next1 : z1.next_out = advance z.next_out p1 := strat1.1.1.2.2.2.2.2.1
  refine ⟨by simpa using StratFrame.trans strat1 strat2 owned good.uniq (output_target good buffers), ?_⟩
  intro ob root
  exact (storage1 ob root).trans (storage2 ob (by rw [next1]; exact byte_root_advance.mpr root))

/-- **A low-bit `flush_pending`** (at most seven held bits) is a stage. -/
theorem StageFrame.of_flush {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z z' : ZStream}
    {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf) (out : z.next_out ≠ .null)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    StageFrame h after r ds pb d z z' produced := by
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers ptr
    have separate : ob ≠ pb := by
      intro same; subst ob; exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
    obtain ⟨_, after', _, _, _, _, run', _, _, sizes, _, _, _, _, _, _, storage⟩ :=
      flush_pending_low_raw_bits_storage good trees low cursor ptr outGet writable separate outBound
    have same : after' = after := (Prod.mk.inj (Except.ok.inj (run'.symm.trans run))).2
    subst same
    have totals := flush_pending_low_run_counter_effects good buffers ptr low run live account
    obtain ⟨next, getN, sizeN, keep⟩ :=
      flush_pending_low_run_output_interval good buffers ptr low run live account outGet
    have frame : Frame h after' (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b = ob) := by
      apply full_frame_weaken (storage.private_frame trees.base.pbuf)
      intro b changed
      rcases changed with root | owned | output
      · exact Or.inl (Or.inl root)
      · exact Or.inl (Or.inr owned)
      · exact Or.inr output
    have buffer : BufferFrame h after' (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
        [⟨z.next_out, produced⟩] := by
      rw [ptr]
      exact raw_buffer_frame_of_interval frame storage.shape good.uniq outGet getN (sizes.ro (.blk ob)) sizeN keep
    refine ⟨⟨⟨account, by simpa using totals.1, totals.2, buffer, full_shape_live_change storage.shape,
      storage.nalloc⟩, storage.shape⟩, fun ob' root => ?_⟩
    rw [ptr] at root
    change ob' = ob at root
    subst root
    exact storage
  · have storage := low_foreign_pending_run_storage good buffers trees.base.pbuf ptr low run
    obtain ⟨foreign, outGet, outBound, different, _, _⟩ := caller_foreign_output good buffers ptr
    obtain ⟨produced2, after', z2, _, _, _, run', good2, account2, _, _, _, _, _, _, _, bufferA⟩ :=
      flush_pending_low_foreign_bits_frame good trees low cursor ptr outGet different outBound
    have same : after = after' := (Prod.mk.inj (Except.ok.inj (run.symm.trans run'))).2
    subst same
    have sameZ : z2 = z' := Option.some.inj (good2.live.hz.symm.trans live)
    subst sameZ
    have sameP : produced = produced2 := by
      have a1 := account.2.2.2.1; have a2 := account2.2.2.2.1; omega
    subst sameP
    have scalars := flush_pending_low_foreign_run_scalar_effects good buffers ptr low run live account
    have buffer : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
        [⟨z.next_out, produced⟩] := by
      refine ⟨full_frame_weaken bufferA.1 ?_, bufferA.2⟩
      intro b changed
      rcases changed with root | same
      · exact Or.inl root
      · exact Or.inr (Or.inl same)
    refine ⟨⟨⟨account, by simpa using scalars.2.1, scalars.2.2.1, buffer, full_shape_live_change storage.shape,
      storage.nalloc⟩, storage.shape⟩, fun ob' root => ?_⟩
    rw [ptr] at root
    change ob' = ob at root
    subst root
    exact storage

/-- **What a stage keeps** for the invariant: the static tables, the window bytes, the `prev` and
`head` words, and the `pending_buf` block. -/
theorem StageFrame.keeps {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {d : DeflateState}
    {z z' : ZStream} (frame : StageFrame h after r ds pb d z z' produced) (good : DGood h r ds z d)
    (buffers : StreamBuffers h r) (pbuf : d.pending_buf = .ref (.blk pb) 0) (out : z.next_out ≠ .null) :
    after.static = h.static ∧
    (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
    (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
    (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧
    (∀ b, d.pending_buf = .ref (.blk b) 0 → ∃ a', after.bytes b = some a') := by
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  have root : ByteRoot z.next_out ob := by
    rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩ <;> rw [ptr] <;> rfl
  have storage := frame.2 ob root
  have outside := output_target good buffers
  have notOb : ∀ x, DeflateOwned ds d x → x ≠ ob := by
    intro x owned same
    subst same
    rcases outside with null | ⟨ob', oo, arr, ptr, _, no⟩ | ⟨owner, oo, f, ptr, _, no⟩
    · rw [null] at root; exact root
    · rw [ptr] at root; change x = ob' at root; subst root; exact no (Or.inr owned)
    · rw [ptr] at root; change x = owner at root; subst root; exact no (Or.inr owned)
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have slots := storage.frame.2.2.2.2.2
  have keep : ∀ x, DeflateOwned ds d x → x ≠ ds → x ≠ pb → h.live x → Zlib.Deflate.Proofs.DefaultInit.SlotSame h after x := by
    intro x owned notDs notPb live
    refine slots x live ?_
    rintro (rootX | e | e | e)
    · rcases owned with e | e | e | e | e
      · exact notDs e
      all_goals
        have only : h.streams x = none ∧ h.gzstates x = none := by
          first
            | (rw [blocks.win] at e; cases e; obtain ⟨a, ga, _⟩ := blocks.wa
               exact ⟨(good.uniq.bytes_only ga).2.1, (good.uniq.bytes_only ga).2.2.2.2.2⟩)
            | (rw [blocks.prev] at e; cases e; obtain ⟨a, ga, _⟩ := blocks.pa
               exact ⟨(good.uniq.words_only ga).2.1, (good.uniq.words_only ga).2.2.2.2.2⟩)
            | (rw [blocks.head] at e; cases e; obtain ⟨a, ga, _⟩ := blocks.qa
               exact ⟨(good.uniq.words_only ga).2.1, (good.uniq.words_only ga).2.2.2.2.2⟩)
            | (rw [blocks.pbuf] at e; cases e; obtain ⟨a, ga, _⟩ := blocks.ba
               exact ⟨(good.uniq.bytes_only ga).2.1, (good.uniq.bytes_only ga).2.2.2.2.2⟩)
        exact not_root_of_unique good.uniq good.live.hz only rootX
    · exact notDs e
    · exact notPb e
    · exact notOb x owned e
  have bpb : b = pb := by have e := blocks.pbuf; rw [pbuf] at e; cases e; rfl
  subst bpb
  have hs := good.live.hs
  obtain ⟨wa, gw, _⟩ := blocks.wa
  obtain ⟨pa, gp, _⟩ := blocks.pa
  obtain ⟨qa, gq, _⟩ := blocks.qa
  obtain ⟨ba, gb, _⟩ := blocks.ba
  have wDs : w ≠ ds := by intro e; rw [e] at gw; rw [(good.uniq.bytes_only gw).2.2.2.1] at hs; cases hs
  have pDs : p ≠ ds := by intro e; rw [e] at gp; rw [(good.uniq.words_only gp).2.2.2.1] at hs; cases hs
  have qDs : q ≠ ds := by intro e; rw [e] at gq; rw [(good.uniq.words_only gq).2.2.2.1] at hs; cases hs
  have pB : p ≠ b := by intro e; rw [e] at gp; rw [(good.uniq.words_only gp).1] at gb; cases gb
  have qB : q ≠ b := by intro e; rw [e] at gq; rw [(good.uniq.words_only gq).1] at gb; cases gb
  refine ⟨storage.frame.1.symm, ?_, ?_, ?_, ?_⟩
  · intro w' e
    rw [blocks.win] at e; cases e
    exact (keep w (Or.inr (Or.inl blocks.win)) wDs blocks.wb (by simp [Heap.live, gw])).1
  · intro p' e
    rw [blocks.prev] at e; cases e
    exact (keep p (Or.inr (Or.inr (Or.inl blocks.prev))) pDs pB (by simp [Heap.live, gp])).2.1
  · intro q' e
    rw [blocks.head] at e; cases e
    exact (keep q (Or.inr (Or.inr (Or.inr (Or.inl blocks.head)))) qDs qB (by simp [Heap.live, gq])).2.1
  · intro b' e
    rw [blocks.pbuf] at e; cases e
    have some := (storage.shape b).1
    rw [gb] at some
    cases ga : after.bytes b with
    | none => rw [ga] at some; cases some
    | some a' => exact ⟨a', rfl⟩

end Zlib.Deflate.Universal.Call

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- **The facts of a stage for `deflate_call`**, in the forms of `CallFrame` and `DInv.lift_empty`:
the totals, the output frame, the static tables, the window, `prev` and `head`, and `pending_buf`. -/
theorem StageFrame.call_facts {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {d : DeflateState}
    {z z' : ZStream} (frame : StageFrame h after r ds pb d z z' produced) (good : DGood h r ds z d)
    (buffers : StreamBuffers h r) (pbuf : d.pending_buf = .ref (.blk pb) 0) (out : z.next_out ≠ .null) :
    z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] ∧
    after.static = h.static ∧
    (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
    (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
    (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) ∧
    (∀ b, d.pending_buf = .ref (.blk b) 0 → ∃ a', after.bytes b = some a') := by
  obtain ⟨⟨_, totalIn, totalOut, buffer, _, _⟩, _⟩ := frame.1
  exact ⟨by simpa using totalIn, totalOut, buffer, frame.keeps good buffers pbuf out⟩

end Zlib.Deflate.Universal.Call
