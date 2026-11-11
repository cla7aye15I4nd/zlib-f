import ZlibF.Proof.«deflate.c.universal-stored-io»

/-!
# deflate.c, universal engine: the copy loop of `deflate_stored`

The first loop of `deflate_stored` emits stored blocks straight into the caller's output: an empty
stored header with the four length bytes patched in, `flush_pending`, then the block's bytes, first
from the window (`left`) and then from the input (`read_buf` into `next_out`).
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The emission of an iteration: an empty stored block, its length patched into the last four
pending bytes, and the flush of the pending bytes. -/
def storedEmit (s : DeflateStatePtr) (strm : ZStreamPtr) (len : UInt32) (last : Int32) : M Unit := do
  Zlib.Trees._tr_stored_block s (Ptr.null : BPtr) 0 last
  let d ← ldDeflateState s
  store8 (← padd d.pending_buf (d.pending - 4).toNat) len.toUInt8
  store8 (← padd d.pending_buf (d.pending - 3).toNat) (len >>> 8).toUInt8
  store8 (← padd d.pending_buf (d.pending - 2).toNat) (~~~len).toUInt8
  store8 (← padd d.pending_buf (d.pending - 1).toNat) ((~~~len) >>> 8).toUInt8
  flush_pending strm

/-- The direct copies of an iteration: `left` bytes of the window, then the rest from the input. -/
def storedDirect (s : DeflateStatePtr) (strm : ZStreamPtr) (left len : UInt32) : M (UInt32 × UInt32) := do
  let mut left := left
  let mut len := len
  if left != 0 then
    if left > len then left := len
    let d ← ldDeflateState s
    let z ← ldZStream strm
    memcpyB z.next_out (← Ptr.add d.window d.block_start.toInt) left.toNat
    let no ← padd z.next_out left.toNat
    zwr strm (fun z => { z with next_out := no, avail_out := z.avail_out - left, total_out := z.total_out + left.toUInt64 })
    let bs ← ladd d.block_start left.toUInt64.toInt64
    wr s (fun d => { d with block_start := bs })
    len := len - left
  if len != 0 then
    let _ ← read_buf strm (← zrd strm (·.next_out)) len
    let no ← padd (← zrd strm (·.next_out)) len.toNat
    zwr strm (fun z => { z with next_out := no, avail_out := z.avail_out - len, total_out := z.total_out + len.toUInt64 })
  pure (left, len)

/-- The body of the first loop of `deflate_stored`, with the emission and the copies named. -/
def storedBody (s : DeflateStatePtr) (flush : Int32) (strm : ZStreamPtr) (min_block : UInt32) (st : StoredS) :
    M StoredS := do
  let mut st := { st with len := MAX_STORED }
  let d ← ldDeflateState s
  let hv : UInt32 := (d.bi_valid.toUInt32 + 42) >>> 3
  let z ← ldZStream strm
  if z.avail_out < hv then return { st with have_ := hv, brk := true }
  let mut have_ := z.avail_out - hv
  let left : UInt32 := (← lsub d.strstart.toUInt64.toInt64 d.block_start).toUInt64.toUInt32
  let mut len := st.len
  if left < len && z.avail_in < len - left then len := left + z.avail_in
  if len > have_ then len := have_
  let all := len ≥ left && len - left == z.avail_in
  if len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH || !all) then
    return { st with len, left, have_, all, brk := true }
  let last : Int32 := if flush == Z_FINISH && all then 1 else 0
  storedEmit s strm len last
  let moved ← storedDirect s strm left len
  pure { st with last, len := moved.2, left := moved.1, have_, all, brk := false }

/-- The part of `deflate_stored` after the first loop. -/
def storedEnd (s : DeflateStatePtr) (flush : Int32) (strm : ZStreamPtr) (min_block0 used0 : UInt32)
    (st : StoredS) : M block_state := do
  let mut min_block := min_block0
  let mut used := used0
  let mut last := st.last
  used := used - (← zrd strm (·.avail_in))
  if used != 0 then
    let d ← ldDeflateState s
    if used ≥ d.w_size then
      memcpyB d.window (← psub (← zrd strm (·.next_in)) d.w_size.toNat) d.w_size.toNat
      wr s (fun d => { d with «matches» := 2, strstart := d.w_size, insert := d.w_size })
    else
      if d.window_size - d.strstart.toUInt64 ≤ used.toUInt64 then
        let ss := d.strstart - d.w_size
        memcpyB d.window (← padd d.window d.w_size.toNat) ss.toNat
        wr s (fun d => { d with
          strstart := ss,
          «matches» := if d.«matches» < 2 then d.«matches» + 1 else d.«matches»,
          insert := if d.insert > ss then ss else d.insert })
      let d ← ldDeflateState s
      memcpyB (← padd d.window d.strstart.toNat) (← psub (← zrd strm (·.next_in)) used.toNat) used.toNat
      wr s (fun d => { d with strstart := d.strstart + used,
                              insert := d.insert + MIN used (d.w_size - d.insert) })
    wr s (fun d => { d with block_start := d.strstart.toUInt64.toInt64 })
  wr s (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water })
  if last != 0 then
    wr s (fun d => { d with bi_used := 8 })
    return finish_done
  let d ← ldDeflateState s
  if flush != Z_NO_FLUSH && flush != Z_FINISH && (← zrd strm (·.avail_in)) == 0 &&
      d.strstart.toUInt64.toInt64 == d.block_start then
    return block_done
  let mut have_ : UInt32 := (d.window_size - d.strstart.toUInt64).toUInt32
  if (← zrd strm (·.avail_in)) > have_ && d.block_start ≥ d.w_size.toUInt64.toInt64 then
    let bs ← lsub d.block_start d.w_size.toUInt64.toInt64
    let ss := d.strstart - d.w_size
    memcpyB d.window (← padd d.window d.w_size.toNat) ss.toNat
    wr s (fun d => { d with
      block_start := bs, strstart := ss,
      «matches» := if d.«matches» < 2 then d.«matches» + 1 else d.«matches»,
      insert := if d.insert > ss then ss else d.insert })
    have_ := have_ + d.w_size
  let ai ← zrd strm (·.avail_in)
  if have_ > ai then have_ := ai
  if have_ != 0 then
    let d ← ldDeflateState s
    let _ ← read_buf strm (← padd d.window d.strstart.toNat) have_
    wr s (fun d => { d with strstart := d.strstart + have_,
                            insert := d.insert + MIN have_ (d.w_size - d.insert) })
  wr s (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water })
  let d ← ldDeflateState s
  have_ := (d.bi_valid.toUInt32 + 42) >>> 3
  have_ := (MIN (d.pending_buf_size - have_.toUInt64) MAX_STORED.toUInt64).toUInt32
  min_block := MIN have_ d.w_size
  let left : UInt32 := (← lsub d.strstart.toUInt64.toInt64 d.block_start).toUInt64.toUInt32
  let ai ← zrd strm (·.avail_in)
  if left ≥ min_block ||
      ((left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH && ai == 0 && left ≤ have_) then
    let len := MIN left have_
    last := if flush == Z_FINISH && ai == 0 && len == left then 1 else 0
    Zlib.Trees._tr_stored_block s (← Ptr.add d.window d.block_start.toInt) len.toUInt64 last
    let bs ← ladd d.block_start len.toUInt64.toInt64
    wr s (fun d => { d with block_start := bs })
    flush_pending strm
  if last != 0 then wr s (fun d => { d with bi_used := 8 })
  return if last != 0 then finish_started else need_more

theorem deflate_stored_source (s : DeflateStatePtr) (flush : Int32) :
    deflate_stored s flush = (do
      let d ← ldDeflateState s
      let used ← zrd d.strm (·.avail_in)
      let st ← cdoWhile (storedBody s flush d.strm (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32)
        (fun st => pure (!st.brk && st.last == 0, st))
        { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false }
      storedEnd s flush d.strm (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 used st) := by
  unfold deflate_stored storedBody storedEmit storedDirect storedEnd
  simp only [Zlib.Deflate.Engine.Proofs.M_bind_assoc, Zlib.Deflate.Engine.Proofs.M_pure_bind, fill_ite_bind]


/-! ## The emission of an iteration -/

open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff) in
theorem trees_set_bytes {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h id d b buf) (buf' : Array UInt8) (size : buf'.size = buf.size) :
    TreesInvAt (Zlib.Trees.Proofs.Out.setB h b buf') id d b buf' :=
  ⟨⟨trees.base.dstate, trees.base.wf, trees.base.static, trees.base.pbuf, upd_same _ _ _, trees.base.rw,
    by rw [size]; exact trees.base.size, by rw [size]; exact trees.base.psize, trees.base.sym,
    trees.base.lit_lo, trees.base.lit_hi, trees.base.sym_end, trees.base.pending_le⟩, trees.run⟩

/-- `s->pending_buf[k] = v` on the pending block: the address and the store. -/
theorem pending_store {h : Heap} {ds pb : Nat} {e : DeflateState} {next : Array UInt8}
    (pbuf : e.pending_buf = .ref (.blk pb) 0) (ro : h.ro pb = false) (k : Nat) (hk : k < next.size)
    (v : UInt8) :
    padd e.pending_buf k (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds e) =
        .ok (.ref (.blk pb) k, setD (Zlib.Trees.Proofs.Out.setB h pb next) ds e) ∧
      store8 (.ref (.blk pb) k) v (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds e) =
        .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb (next.set! k v)) ds e) := by
  have get : Space.get (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds e) (BRef.blk pb) = some next := by
    show (upd h.bytes pb (some next)) pb = some next
    exact upd_same _ _ _
  refine ⟨?_, ?_⟩
  · rw [pbuf]
    have := Ptr.add_nat_ok get (by omega : 0 + k ≤ next.size)
    simpa only [OkOn, padd, Nat.zero_add] using this
  · have store := Ptr.store_ok (v := v) get ro hk
    simp only [store8]
    rw [store,
      show Space.put (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds e) (BRef.blk pb) (next.set! k v) =
        setD (Zlib.Trees.Proofs.Out.setB (Zlib.Trees.Proofs.Out.setB h pb next) pb (next.set! k v)) ds e from rfl,
      Zlib.Trees.Proofs.Out.setB_setB]

set_option maxHeartbeats 2000000 in
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff) in
/-- **The emission of an iteration.** From an empty pending buffer with at most seven bits, and
an output with room for the header (`have = (bi_valid + 42) >> 3` bytes), the empty stored block,
the length patch and `flush_pending` deliver exactly the header: afterwards nothing is pending,
no bit is held, and only the bit fields and the pending cursor of the state changed. -/
theorem stored_emit {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf)
    (bits : d.bi_valid.toInt ≤ 7) (strm : d.strm = some r)
    (room : (d.bi_valid.toInt.toNat + 42) / 8 ≤ z.avail_out.toNat) (len : UInt32) (last : Bool) :
    ∃ after z' e, storedEmit (some (.tab ds)) (some r) len (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' e ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 ((d.bi_valid.toInt.toNat + 42) / 8) ∧
      e = { d with pending := e.pending, pending_out := e.pending_out, bi_buf := e.bi_buf, bi_valid := e.bi_valid, bi_used := e.bi_used } ∧
      e.pending = 0 ∧ e.pending_out = e.pending_buf ∧ e.bi_valid.toInt = 0 ∧
      after.static = h.static ∧ after.nalloc = h.nalloc ∧
      (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
      (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
      (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, getB, sizeB⟩ := blocks.ba
  have trees : TreesInvAt h ds d pb buf := Zlib.Deflate.Universal.trees_at_of_good good blocks.pbuf getB
  have lit := trees.base.lit_lo
  have room6 : d.pending.toNat + 6 ≤ buf.size := by rw [pending]; simp; omega
  obtain ⟨next1, r1, run1, trees1, size1, aligned1, pending1, diff1⟩ :=
    Zlib.Trees.Proofs.Out.stored_block_empty trees bits room6 last
  rw [pending] at pending1
  simp only [UInt64.toNat_zero, Nat.zero_add] at pending1
  replace run1 : Zlib.Trees._tr_stored_block (some (.tab ds)) (Ptr.null : BPtr) 0 (if last then 1 else 0) h =
      .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next1) ds r1) := run1
  replace trees1 : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next1) ds r1) ds r1 pb next1 := trees1
  have bvLo := trees.run.bi_lo
  obtain ⟨P, hP⟩ : ∃ P, P = (d.bi_valid.toInt.toNat + 42) / 8 := ⟨_, rfl⟩
  rw [← hP] at pending1 room ⊢
  have P5 : 5 ≤ P := by omega
  have P6 : P ≤ 6 := by omega
  have pbuf1 : r1.pending_buf = .ref (.blk pb) 0 := trees1.base.pbuf
  have ro1 : h.ro pb = false := blocks.bro
  have state1 : (setD (Zlib.Trees.Proofs.Out.setB h pb next1) ds r1).dstates ds = some r1 := by simp [setD]
  have sub : ∀ k : Nat, k ≤ 4 → 1 ≤ k → (r1.pending - UInt64.ofNat k).toNat = P - k := by
    intro k hk1 hk2
    rw [UInt64.toNat_sub_of_le]
    · rw [pending1]; simp; omega
    · rw [UInt64.le_iff_toNat_le, pending1]; simp; omega
  obtain ⟨a1, ha1⟩ : ∃ a, a = next1.set! (P - 4) len.toUInt8 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a, a = a1.set! (P - 3) (len >>> 8).toUInt8 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a, a = a2.set! (P - 2) (~~~len).toUInt8 := ⟨_, rfl⟩
  obtain ⟨a4, ha4⟩ : ∃ a, a = a3.set! (P - 1) ((~~~len) >>> 8).toUInt8 := ⟨_, rfl⟩
  have s1 : a1.size = buf.size := by simp [ha1, size1]
  have s2 : a2.size = buf.size := by simp [ha2, s1]
  have s3 : a3.size = buf.size := by simp [ha3, s2]
  have s4 : a4.size = buf.size := by simp [ha4, s3]
  have lim : P < buf.size := by omega
  have st1 := pending_store (ds := ds) (e := r1) (next := next1) (h := h) pbuf1 ro1 (P - 4) (by omega) len.toUInt8
  have st2 := pending_store (ds := ds) (e := r1) (next := a1) (h := h) pbuf1 ro1 (P - 3) (by omega) (len >>> 8).toUInt8
  have st3 := pending_store (ds := ds) (e := r1) (next := a2) (h := h) pbuf1 ro1 (P - 2) (by omega) (~~~len).toUInt8
  have st4 := pending_store (ds := ds) (e := r1) (next := a3) (h := h) pbuf1 ro1 (P - 1) (by omega)
    ((~~~len) >>> 8).toUInt8
  have k4 : (r1.pending - 4).toNat = P - 4 := sub 4 (by omega) (by omega)
  have k3 : (r1.pending - 3).toNat = P - 3 := sub 3 (by omega) (by omega)
  have k2 : (r1.pending - 2).toNat = P - 2 := sub 2 (by omega) (by omega)
  have k1 : (r1.pending - 1).toNat = P - 1 := sub 1 (by omega) (by omega)
  let H2 := setD (Zlib.Trees.Proofs.Out.setB h pb a4) ds r1
  have trees2 : TreesInvAt H2 ds r1 pb a4 := by
    have t := trees_set_bytes trees1 a4 (by rw [s4, size1])
    have e : Zlib.Trees.Proofs.Out.setB (setD (Zlib.Trees.Proofs.Out.setB h pb next1) ds r1) pb a4 = H2 := by
      show setD (Zlib.Trees.Proofs.Out.setB (Zlib.Trees.Proofs.Out.setB h pb next1) pb a4) ds r1 = _
      rw [Zlib.Trees.Proofs.Out.setB_setB]
    rw [e] at t
    exact t
  have good2 : DGood H2 r ds z r1 := output_bits_good good cursor getB s4 diff1 trees2
  have buffers2 : StreamBuffers H2 r := output_bits_buffers good buffers cursor getB s4 diff1 trees2
  have cursor2 : r1.pending_out = r1.pending_buf := by
    obtain ⟨_, _, _, _, e⟩ := diff1; rw [e]; exact cursor
  have room2 : 8 * r1.pending.toNat + r1.bi_valid.toInt.toNat ≤ 8 * a4.size := by
    rw [pending1, aligned1, s4]; simp; omega
  have emitEq : storedEmit (some (.tab ds)) (some r) len (if last then 1 else 0) h = flush_pending (some r) H2 := by
    unfold storedEmit
    obtain ⟨p1, t1⟩ := st1
    obtain ⟨p2, t2⟩ := st2
    obtain ⟨p3, t3⟩ := st3
    obtain ⟨p4, t4⟩ := st4
    rw [← ha1] at t1
    rw [← ha2] at t2
    rw [← ha3] at t3
    rw [← ha4] at t4
    simp only [bind_app, run1, ldDeflateState_tab state1, k4, k3, k2, k1, p1, t1, p2, t2, p3, t3, p4, t4]
    rfl
  have bv0 : r1.bi_valid.toInt.toNat / 8 = 0 := by rw [aligned1]; rfl
  have keepH2 : ∀ x, x ≠ pb → H2.bytes x = h.bytes x := fun x ne => upd_ne _ _ _ _ ne
  have wordsH2 : H2.words = h.words := rfl
  have staticH2 : H2.static = h.static := rfl
  have fieldsR1 : r1.window = d.window ∧ r1.prev = d.prev ∧ r1.head = d.head ∧ r1.pending_buf = d.pending_buf := by
    obtain ⟨_, _, _, _, e⟩ := diff1; rw [e]; exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨ob, pointer⟩ := Zlib.Deflate.Universal.output_reference good.live.hz buffers out
  obtain ⟨wa, getW, _⟩ := blocks.wa
  obtain ⟨pa, getP, _⟩ := blocks.pa
  obtain ⟨qa, getQ, _⟩ := blocks.qa
  have getW2 : H2.bytes w = some wa := by rw [keepH2 w blocks.wb]; exact getW
  have arrays : ∀ after : Heap, (after.bytes w = some wa ∧ after.words p = some pa ∧ after.words q = some qa) →
      (∀ w', d.window = .ref (.blk w') 0 → after.bytes w' = h.bytes w') ∧
      (∀ p', d.prev = .ref (.blk p') 0 → after.words p' = h.words p') ∧
      (∀ q', d.head = .ref (.blk q') 0 → after.words q' = h.words q') := by
    intro after ⟨aw, ap, aq⟩
    refine ⟨fun w' e => ?_, fun p' e => ?_, fun q' e => ?_⟩
    · have : w' = w := by simpa only [blocks.win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
      subst this; rw [aw, getW]
    · have : p' = p := by simpa only [blocks.prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using e.symm
      subst this; rw [ap, getP]
    · have : q' = q := by simpa only [blocks.head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using e.symm
      subst this; rw [aq, getQ]
  have finish : ∀ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      flush_pending (some r) H2 = .ok ((), after) → DGood after r ds z' result → StreamBuffers after r →
      StreamAccounting z z' 0 produced →
      produced = min (r1.pending.toNat + r1.bi_valid.toInt.toNat / 8) z.avail_out.toNat →
      result.pending.toNat + produced = r1.pending.toNat + r1.bi_valid.toInt.toNat / 8 →
      result.bi_valid.toInt.toNat = r1.bi_valid.toInt.toNat % 8 →
      result = { r1 with pending := result.pending, pending_out := result.pending_out, bi_buf := result.bi_buf, bi_valid := result.bi_valid, bi_used := result.bi_used } →
      (result.pending = 0 → result.pending_out = result.pending_buf) →
      OutputStorage H2 after r ds pb ob →
      (after.bytes w = some wa ∧ after.words p = some pa ∧ after.words q = some qa) →
      ∃ after z' e, storedEmit (some (.tab ds)) (some r) len (if last then 1 else 0) h = .ok ((), after) ∧
        DGood after r ds z' e ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 P ∧
        e = { d with pending := e.pending, pending_out := e.pending_out, bi_buf := e.bi_buf, bi_valid := e.bi_valid, bi_used := e.bi_used } ∧
        e.pending = 0 ∧ e.pending_out = e.pending_buf ∧ e.bi_valid.toInt = 0 ∧
        after.static = h.static ∧ after.nalloc = h.nalloc ∧
        (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
        (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
        (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) := by
    intro produced after z' result run goodA buffersA account count left valid fields cursorA storage kept
    have count' : produced = min P z.avail_out.toNat := by rw [count, pending1, bv0, Nat.add_zero]
    have left' : result.pending.toNat + produced = P := by rw [left, pending1, bv0, Nat.add_zero]
    have prodEq : produced = P := by rw [count']; omega
    have pend0 : result.pending = 0 := UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; omega)
    have bv : result.bi_valid.toInt = 0 := by
      rw [aligned1] at valid
      have := goodA.inv.bits.1
      have v2 : result.bi_valid.toInt.toNat = 0 := by rw [valid]; rfl
      omega
    refine ⟨after, z', result, by rw [emitEq]; exact run, goodA, buffersA, by rw [← prodEq]; exact account,
      ?_, pend0, cursorA pend0, bv, ?_, storage.nalloc, (arrays after kept).1, (arrays after kept).2.1,
      (arrays after kept).2.2⟩
    · obtain ⟨_, _, _, _, e⟩ := diff1
      rw [e] at fields
      exact fields.trans rfl
    · rw [← staticH2]; exact storage.frame.1.symm
  rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      _sizesA, storageA, count, left, _low, validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
      flush_pending_raw_bits good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := raw_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.private_arrays good2 buffers2 pointer (by rw [fieldsR1.1]; exact blocks.win) getW2
      (by rw [fieldsR1.2.1]; exact blocks.prev) getP (by rw [fieldsR1.2.2.1]; exact blocks.head) getQ pbuf1
    exact finish produced after z' result run goodA buffersA accountA count left validA fieldsA cursorA storageA kept
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      _sizesA, storageA, count, left, _low, validA, fieldsA, _bytes, _pendingA, _outputA, _bufferA⟩ :=
      flush_pending_foreign_bits_frame good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := foreign_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.foreign_private_arrays good2 buffers2 pointer (by rw [fieldsR1.1]; exact blocks.win) getW2
      (by rw [fieldsR1.2.1]; exact blocks.prev) getP (by rw [fieldsR1.2.2.1]; exact blocks.head) getQ pbuf1
    exact finish produced after z' result run goodA buffersA accountA count left validA fieldsA cursorA storageA kept


end Zlib.Deflate.Engine.Proofs
