import ZlibF.Proof.«deflate.c.universal-call-header»
import ZlibF.Proof.«deflate.c.universal-call-stages»
import ZlibF.Proof.«deflate.c.universal-call-stageframe»
import ZlibF.Proof.«deflate.c.life.reset»
import ZlibF.Proof.«deflate.c.engine.pending-checksum»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»

/-!
# deflate.c: the zlib header stage of one `deflate` call

Batch C (`call_frame`, `deflate_header_trailer`). For every level, strategy, window size and
memory level, with or without a preset dictionary and with any held bits: the stage writes the
two header bytes (and the dictionary identifier), resets the checksum, enters `BUSY_STATE` and
flushes. With output room it delivers at least one byte.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- `flush_pending` keeps the stream checksum, for either kind of output view. -/
theorem flush_pending_adler {h after : Heap} {r : ZStreamRef} {ds pb ob produced : Nat}
    {z z' : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : (∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo))
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) : z'.adler = z.adler := by
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · exact flush_pending_run_adler good trees buffers ptr cursor room run live account
  · obtain ⟨next, prepared, _bitRun, goodP, treesP, _bits, low, size, fields, _pending, _valid, sameRun⟩ :=
      flush_pending_prepare good trees cursor room
    have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size fields treesP
    exact (flush_pending_low_foreign_run_scalar_effects goodP buffersP ptr low (sameRun.symm.trans run)
      live account).1

/-- **The end of the zlib header stage.** With header bytes pending and output room, the flush
delivers at least one byte; the stage returns `Z_OK` if bytes are left, else it continues. -/
theorem init_tail {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (pending : 1 ≤ d.pending.toNat) (avail : z.avail_out ≠ 0) (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      1 ≤ produced ∧ z'.adler = 1 ∧
      d'.bi_valid.toInt < 8 ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      d' = { d with
        status := BUSY_STATE, pending := d'.pending, pending_out := d'.pending_out,
        bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      initTail (some r) (some (.tab ds)) k h =
        (if d'.pending ≠ 0 then .ok (Z_OK, setD after ds { d' with last_flush := -1 }) else k after) := by
  let z1 : ZStream := { z with adler := 1 }
  let d1 : DeflateState := { d with status := BUSY_STATE }
  obtain ⟨good1, trees1, buffers1, _sizes1, account1⟩ :=
    adler_status_engine good trees buffers 1 BUSY_STATE (by simp [GoodStatus])
  change DGood (setD (r.put h z1) ds d1) r ds z1 d1 at good1
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good1 buffers1 (show z1.next_out ≠ .null from out)
  have pointerK := pointer
  have published : ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      flush_pending (some r) (setD (r.put h z1) ds d1) = .ok ((), after) ∧ DGood after r ds z' d' ∧
      StreamBuffers after r ∧ StreamAccounting z1 z' 0 produced ∧
      produced = min (d1.pending.toNat + d1.bi_valid.toInt.toNat / 8) z1.avail_out.toNat ∧
      d' = { d1 with
        pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf,
        bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      d'.bi_valid.toInt < 8 ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) := by
    rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, _left,
        low', _valid, fields, _b, _p, _o⟩ := flush_pending_raw_bits good1 trees1 buffers1 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, fields, low',
        raw_pending_run_empty_cursor good1 trees1 buffers1 ptr cursor room run goodA.live.hs⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, _left,
        low', _valid, fields, _b, _p, _o, _bf⟩ := flush_pending_foreign_bits_frame good1 trees1 buffers1 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, fields, low',
        foreign_pending_run_empty_cursor good1 trees1 buffers1 ptr cursor room run goodA.live.hs⟩
  obtain ⟨produced, after, z', d', run, goodA, buffersA, account, copied, fields, lowA, emptyA⟩ := published
  have availPos : 1 ≤ z.avail_out.toNat := by
    have : z.avail_out.toNat ≠ 0 := fun e => avail (UInt32.toNat_inj.mp (by simpa using e))
    omega
  have one : 1 ≤ produced := by
    rw [copied]
    change 1 ≤ min (d.pending.toNat + _) z.avail_out.toNat
    omega
  have accountT : StreamAccounting z z' 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans account1 account
  have adler : z'.adler = 1 :=
    flush_pending_adler good1 trees1 buffers1 pointerK cursor room run goodA.live.hz account
  refine ⟨produced, after, z', d', goodA, buffersA, accountT, one, adler, lowA, emptyA, ?_, ?_⟩
  · rw [fields]
  · unfold initTail
    simp only [bind_app, adler32_null, pure_app, zwr_eq, good.live.hz, wrD_eq, ZStreamRef.put_dstates,
      good.live.hs]
    simp only [z1, d1] at run
    rw [run]
    by_cases zero : d'.pending = 0
    · simp [rdD_eq, goodA.live.hs, zero]
    · simp [rdD_eq, goodA.live.hs, zero, wrD_eq]

/-- The heap after `putShortMSB`, as a function of the word. -/
def shortHeap (h : Heap) (ds pb : Nat) (d : DeflateState) (buf : Array UInt8) (v : UInt32) : Heap :=
  let first := buf.set! d.pending.toNat (v >>> 8).toUInt8
  let mid := setD (Zlib.Trees.Proofs.Out.setB h pb first) ds { d with pending := d.pending + 1 }
  setD (Zlib.Trees.Proofs.Out.setB mid pb (first.set! (d.pending + 1).toNat (v &&& 0xff).toUInt8)) ds
    { d with pending := d.pending + 1 + 1 }

/-- The buffer after `putShortMSB`. -/
def shortBuf (d : DeflateState) (buf : Array UInt8) (v : UInt32) : Array UInt8 :=
  (buf.set! d.pending.toNat (v >>> 8).toUInt8).set! (d.pending + 1).toNat (v &&& 0xff).toUInt8

/-- **Two header bytes**, with the heap given for every word. -/
theorem header_short_eq {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat + 2 ≤ buf.size) :
    (∀ v, putShortMSB (some (.tab ds)) v h = .ok ((), shortHeap h ds pb d buf v)) ∧
    (∀ v, DGood (shortHeap h ds pb d buf v) r ds z { d with pending := d.pending + 2 } ∧
      TreesInvAt (shortHeap h ds pb d buf v) ds { d with pending := d.pending + 2 } pb (shortBuf d buf v) ∧
      StreamBuffers (shortHeap h ds pb d buf v) r ∧
      (d.pending + 2).toNat = d.pending.toNat + 2 ∧ (shortBuf d buf v).size = buf.size) := by
  have small := trees.base.pending_small
  have sz := trees.base.size
  have lh := trees.base.lit_hi
  have two : d.pending + 1 + 1 = d.pending + 2 := by
    apply UInt64.toNat_inj.mp
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 (by rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 small]; omega),
      Zlib.Trees.Proofs.Out.toNat_add_one_u64 small, Zlib.Trees.Proofs.Out.toNat_add_two_u64 small]
  have runs : ∀ v, putShortMSB (some (.tab ds)) v h = .ok ((), shortHeap h ds pb d buf v) := by
    intro v
    obtain ⟨run1, good1, trees1, buffers1, _, _, count1, size1, cursor1⟩ :=
      header_byte (ob := 0) good trees buffers cursor (by omega) (v >>> 8).toUInt8
    obtain ⟨run2, _⟩ := header_byte (ob := 0) good1 trees1 buffers1 cursor1
      (by rw [count1, size1]; omega) (v &&& 0xff).toUInt8
    unfold putShortMSB
    rw [bind_app, run1]
    exact run2
  refine ⟨runs, fun v => ?_⟩
  obtain ⟨after, next, run, goodA, treesA, buffersA, _, _, count, size⟩ :=
    header_short (ob := 0) good trees buffers cursor room v
  have same : after = shortHeap h ds pb d buf v :=
    (Prod.mk.inj (Except.ok.inj (run.symm.trans (runs v)))).2
  subst same
  have bytes : next = shortBuf d buf v := by
    have get := treesA.base.bytes
    have known : (shortHeap h ds pb d buf v).bytes pb = some (shortBuf d buf v) := by
      simp [shortHeap, shortBuf, setD, Zlib.Trees.Proofs.Out.setB]
    exact Option.some.inj (get.symm.trans known)
  subst bytes
  exact ⟨goodA, treesA, buffersA, count, size⟩

/-- The zlib header stage writes some header word with `putShortMSB`, then the dictionary part. -/
theorem init_stage_word {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (status : d.status = INIT_STATE) (pending : d.pending = 0) (k : M Int32) :
    ∃ W, initStage (some r) (some (.tab ds)) k h =
      initDict (some r) (some (.tab ds)) (initTail (some r) (some (.tab ds)) k) (shortHeap h ds pb d buf W) := by
  have sz := trees.base.size
  have lo := trees.base.lit_lo
  have zeroN : d.pending.toNat = 0 := by rw [pending]; rfl
  obtain ⟨runs1, _⟩ := header_short_eq good trees buffers cursor (by omega)
  rw [init_stage_split]
  unfold initStage'
  simp only [bind_app, rdD_eq, good.live.hs, status, show (INIT_STATE == INIT_STATE) = true from rfl,
    ite_true, ldDeflateState_tab good.live.hs, runs1]
  by_cases dict : d.strstart = 0
  · simp only [dict, bne_self_eq_false, Bool.false_eq_true, ite_false, bind_app, runs1]
    exact ⟨_, rfl⟩
  · simp only [show (d.strstart != 0) = true from bne_iff_ne.mpr dict, ite_true, bind_app, runs1]
    exact ⟨_, rfl⟩

/-- **The zlib header stage**, for every level, strategy, window size and memory level, with or
without a preset dictionary, and any held bits. With output room it delivers at least one byte. -/
theorem init_stage {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (status : d.status = INIT_STATE) (pending : d.pending = 0)
    (avail : z.avail_out ≠ 0) (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      1 ≤ produced ∧ z'.adler = 1 ∧
      d'.bi_valid.toInt < 8 ∧ (d'.pending = 0 → d'.pending_out = d'.pending_buf) ∧
      d' = { d with
        status := BUSY_STATE, pending := d'.pending, pending_out := d'.pending_out,
        bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      initStage (some r) (some (.tab ds)) k h =
        (if d'.pending ≠ 0 then .ok (Z_OK, setD after ds { d' with last_flush := -1 }) else k after) := by
  have sz := trees.base.size
  have lo := trees.base.lit_lo
  have bits := trees.run.bi_hi
  have bitsLo := trees.run.bi_lo
  have zeroN : d.pending.toNat = 0 := by rw [pending]; rfl
  obtain ⟨W, eqW⟩ := init_stage_word good trees buffers cursor status pending k
  obtain ⟨_, facts1⟩ := header_short_eq good trees buffers cursor (by omega)
  obtain ⟨good2, trees2, buffers2, count2, size2⟩ := facts1 W
  have two : (d.pending + 2).toNat = 2 := by rw [count2, zeroN]
  rw [eqW]
  by_cases dict : d.strstart = 0
  · have dictEq : ∀ K : M Int32, initDict (some r) (some (.tab ds)) K (shortHeap h ds pb d buf W) =
        K (shortHeap h ds pb d buf W) := by
      intro K
      unfold initDict
      simp [bind_app, rdD_eq, good2.live.hs, dict]
    obtain ⟨produced, after, z', d', goodA, buffersA, account, one, adler, lowA, emptyA, fields, run⟩ :=
      init_tail good2 trees2 buffers2 cursor
        (by change 8 * (d.pending + 2).toNat + d.bi_valid.toInt.toNat ≤ 8 * (shortBuf d buf W).size
            rw [two, size2]; omega)
        (by change 1 ≤ (d.pending + 2).toNat; omega) avail out k
    refine ⟨produced, after, z', d', goodA, buffersA, account, one, adler, lowA, emptyA, ?_, ?_⟩
    · rw [fields]
    · rw [dictEq, run]
  · let d2 : DeflateState := { d with pending := d.pending + 2 }
    have cursor2 : d2.pending_out = d2.pending_buf := cursor
    obtain ⟨runs3, facts3⟩ := header_short_eq good2 trees2 buffers2 cursor2
      (by change (d.pending + 2).toNat + 2 ≤ (shortBuf d buf W).size; rw [two, size2]; omega)
    let A1 : UInt32 := (z.adler >>> 16).toUInt32
    let A2 : UInt32 := (z.adler &&& 0xffff).toUInt32
    obtain ⟨good3, trees3, buffers3, count3, size3⟩ := facts3 A1
    let d3 : DeflateState := { d2 with pending := d2.pending + 2 }
    have cursor3 : d3.pending_out = d3.pending_buf := cursor
    have four : (d2.pending + 2).toNat = 4 := by rw [count3]; change (d.pending + 2).toNat + 2 = 4; rw [two]
    obtain ⟨runs4, facts4⟩ := header_short_eq good3 trees3 buffers3 cursor3
      (by change (d2.pending + 2).toNat + 2 ≤ (shortBuf d2 (shortBuf d buf W) A1).size
          rw [four, size3, size2]; omega)
    obtain ⟨good4, trees4, buffers4, count4, size4⟩ := facts4 A2
    have six : (d3.pending + 2).toNat = 6 := by rw [count4]; change (d2.pending + 2).toNat + 2 = 6; rw [four]
    let H2 := shortHeap h ds pb d buf W
    let H3 := shortHeap H2 ds pb d2 (shortBuf d buf W) A1
    let H4 := shortHeap H3 ds pb d3 (shortBuf d2 (shortBuf d buf W) A1) A2
    have dictEq : ∀ K : M Int32, initDict (some r) (some (.tab ds)) K H2 = K H4 := by
      intro K
      unfold initDict
      rw [bind_app, rdD_eq, good2.live.hs]
      simp only [show (d.strstart != 0) = true from bne_iff_ne.mpr dict, ite_true, bind_app, zrd_eq]
      rw [show r.get H2 = some z from good2.live.hz]
      simp only []
      rw [runs3 A1]
      simp only []
      rw [runs4 A2]
    obtain ⟨produced, after, z', d', goodA, buffersA, account, one, adler, lowA, emptyA, fields, run⟩ :=
      init_tail good4 trees4 buffers4 cursor
        (by change 8 * (d3.pending + 2).toNat + d.bi_valid.toInt.toNat ≤
              8 * (shortBuf d3 (shortBuf d2 (shortBuf d buf W) A1) A2).size
            rw [six, size4, size3, size2]; omega)
        (by change 1 ≤ (d3.pending + 2).toNat; omega) avail out k
    refine ⟨produced, after, z', d', goodA, buffersA, account, one, adler, lowA, emptyA, ?_, ?_⟩
    · rw [fields]
    · rw [dictEq, run]

end Zlib.Deflate.Universal.Call
