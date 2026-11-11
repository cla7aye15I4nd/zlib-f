import ZlibF.Proof.«deflate.c.universal-stored-io»
import ZlibF.Proof.«public-uncompress-loop-rule»

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

/-- The rest of an iteration once the length is chosen: the break test, the emission and the copies. -/
def storedRest (s : DeflateStatePtr) (flush : Int32) (strm : ZStreamPtr) (min_block : UInt32) (st : StoredS)
    (have_ left len : UInt32) (z : ZStream) : M StoredS := do
  let all := len ≥ left && len - left == z.avail_in
  if len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH || !all) then
    return { st with len, left, have_, all, brk := true }
  let last : Int32 := if flush == Z_FINISH && all then 1 else 0
  storedEmit s strm len last
  let moved ← storedDirect s strm left len
  pure { st with last, len := moved.2, left := moved.1, have_, all, brk := false }

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
  storedRest s flush strm min_block st have_ left len z

/-- After the loop: keep the last `used` bytes of the consumed input in the window. -/
def storedKeep (s : DeflateStatePtr) (strm : ZStreamPtr) (used : UInt32) : M Unit := do
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

/-- The refill of the window from the input, with a slide when the window is full. -/
def storedRefill (s : DeflateStatePtr) (strm : ZStreamPtr) (d : DeflateState) : M Unit := do
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

/-- The final stored block from the window, when enough is there. -/
def storedFinal (s : DeflateStatePtr) (flush : Int32) (strm : ZStreamPtr) (last0 : Int32) : M block_state := do
  let mut last := last0
  let d ← ldDeflateState s
  let mut have_ : UInt32 := (d.bi_valid.toUInt32 + 42) >>> 3
  have_ := (MIN (d.pending_buf_size - have_.toUInt64) MAX_STORED.toUInt64).toUInt32
  let min_block := MIN have_ d.w_size
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

/-- The part of `deflate_stored` after the first loop. -/
def storedEnd (s : DeflateStatePtr) (flush : Int32) (strm : ZStreamPtr) (_min_block0 used0 : UInt32)
    (st : StoredS) : M block_state := do
  let used := used0 - (← zrd strm (·.avail_in))
  if used != 0 then storedKeep s strm used
  wr s (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water })
  if st.last != 0 then
    wr s (fun d => { d with bi_used := 8 })
    return finish_done
  let d ← ldDeflateState s
  if flush != Z_NO_FLUSH && flush != Z_FINISH && (← zrd strm (·.avail_in)) == 0 &&
      d.strstart.toUInt64.toInt64 == d.block_start then
    return block_done
  storedRefill s strm d
  storedFinal s flush strm st.last

theorem deflate_stored_source (s : DeflateStatePtr) (flush : Int32) :
    deflate_stored s flush = (do
      let d ← ldDeflateState s
      let used ← zrd d.strm (·.avail_in)
      let st ← cdoWhile (storedBody s flush d.strm (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32)
        (fun st => pure (!st.brk && st.last == 0, st))
        { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false }
      storedEnd s flush d.strm (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 used st) := by
  unfold deflate_stored storedBody storedRest storedEmit storedDirect storedEnd storedKeep storedRefill storedFinal
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
      after.static = h.static ∧ after.nalloc = h.nalloc ∧ ByteSizes h after ∧
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
      OutputStorage H2 after r ds pb ob → ByteSizes H2 after →
      (after.bytes w = some wa ∧ after.words p = some pa ∧ after.words q = some qa) →
      ∃ after z' e, storedEmit (some (.tab ds)) (some r) len (if last then 1 else 0) h = .ok ((), after) ∧
        DGood after r ds z' e ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 P ∧
        e = { d with pending := e.pending, pending_out := e.pending_out, bi_buf := e.bi_buf, bi_valid := e.bi_valid, bi_used := e.bi_used } ∧
        e.pending = 0 ∧ e.pending_out = e.pending_buf ∧ e.bi_valid.toInt = 0 ∧
        after.static = h.static ∧ after.nalloc = h.nalloc ∧ ByteSizes h after ∧
        (∀ w, d.window = .ref (.blk w) 0 → after.bytes w = h.bytes w) ∧
        (∀ p, d.prev = .ref (.blk p) 0 → after.words p = h.words p) ∧
        (∀ q, d.head = .ref (.blk q) 0 → after.words q = h.words q) := by
    intro produced after z' result run goodA buffersA account count left valid fields cursorA storage sizesF kept
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
      ?_, pend0, cursorA pend0, bv, ?_, storage.nalloc, (output_bits_sizes good getB s4 diff1).chain sizesF,
      (arrays after kept).1, (arrays after kept).2.1,
      (arrays after kept).2.2⟩
    · obtain ⟨_, _, _, _, e⟩ := diff1
      rw [e] at fields
      exact fields.trans rfl
    · rw [← staticH2]; exact storage.frame.1.symm
  rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      sizesA, storageA, count, left, _low, validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
      flush_pending_raw_bits good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := raw_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.private_arrays good2 buffers2 pointer (by rw [fieldsR1.1]; exact blocks.win) getW2
      (by rw [fieldsR1.2.1]; exact blocks.prev) getP (by rw [fieldsR1.2.2.1]; exact blocks.head) getQ pbuf1
    exact finish produced after z' result run goodA buffersA accountA count left validA fieldsA cursorA storageA sizesA kept
  · obtain ⟨produced, after, z', result, _written, _remaining, run, goodA, buffersA, accountA,
      sizesA, storageA, count, left, _low, validA, fieldsA, _bytes, _pendingA, _outputA, _bufferA⟩ :=
      flush_pending_foreign_bits_frame good2 trees2 buffers2 pointer cursor2 room2
    have cursorA := foreign_pending_run_empty_cursor good2 trees2 buffers2 pointer cursor2 room2 run goodA.live.hs
    have kept := storageA.foreign_private_arrays good2 buffers2 pointer (by rw [fieldsR1.1]; exact blocks.win) getW2
      (by rw [fieldsR1.2.1]; exact blocks.prev) getP (by rw [fieldsR1.2.2.1]; exact blocks.head) getQ pbuf1
    exact finish produced after z' result run goodA buffersA accountA count left validA fieldsA cursorA storageA sizesA kept



/-! ## The direct copies of an iteration -/

/-- The window part of the direct copies: `n` bytes from `window + block_start`. -/
def storedCopyA (s : DeflateStatePtr) (strm : ZStreamPtr) (n : UInt32) : M Unit := do
  let d ← ldDeflateState s
  let z ← ldZStream strm
  memcpyB z.next_out (← Ptr.add d.window d.block_start.toInt) n.toNat
  let no ← padd z.next_out n.toNat
  zwr strm (fun z => { z with next_out := no, avail_out := z.avail_out - n, total_out := z.total_out + n.toUInt64 })
  let bs ← ladd d.block_start n.toUInt64.toInt64
  wr s (fun d => { d with block_start := bs })

/-- The input part of the direct copies: `n` bytes read into `next_out`. -/
def storedReadB (strm : ZStreamPtr) (n : UInt32) : M Unit := do
  let _ ← read_buf strm (← zrd strm (·.next_out)) n
  let no ← padd (← zrd strm (·.next_out)) n.toNat
  zwr strm (fun z => { z with next_out := no, avail_out := z.avail_out - n, total_out := z.total_out + n.toUInt64 })

/-- The window bytes `storedDirect` copies: none without a window part, else at most `len`. -/
def directLeft (left len : UInt32) : UInt32 := if left > len then len else left

theorem stored_direct_source (s : DeflateStatePtr) (strm : ZStreamPtr) (left len : UInt32) :
    storedDirect s strm left len = (do
      if left != 0 then storedCopyA s strm (directLeft left len)
      if len - directLeft left len != 0 then storedReadB strm (len - directLeft left len)
      pure (directLeft left len, len - directLeft left len)) := by
  unfold storedDirect storedCopyA storedReadB directLeft
  by_cases l0 : left = 0
  · subst l0
    by_cases ln : len = 0
    · subst ln; simp
    · simp [ln, Zlib.Deflate.Engine.Proofs.M_bind_assoc]
  · by_cases big : left > len
    · simp [l0, big, Zlib.Deflate.Engine.Proofs.M_bind_assoc]
    · simp [l0, big, Zlib.Deflate.Engine.Proofs.M_bind_assoc]


theorem ladd_value (a b : Int64) (h : Heap) (lo : -(2 : Int) ^ 62 ≤ a.toInt + b.toInt)
    (hi : a.toInt + b.toInt ≤ 2 ^ 62) : ladd a b h = .ok (Int64.ofInt (a.toInt + b.toInt), h) := by
  unfold ladd chk64
  rw [if_pos (by omega)]
  rfl

theorem lsub_value (a b : Int64) (h : Heap) (lo : -(2 : Int) ^ 62 ≤ a.toInt - b.toInt)
    (hi : a.toInt - b.toInt ≤ 2 ^ 62) : lsub a b h = .ok (Int64.ofInt (a.toInt - b.toInt), h) := by
  unfold lsub chk64
  rw [if_pos (by omega)]
  rfl

theorem int64_ofInt_toInt (x : Int) (lo : -(2 : Int) ^ 62 ≤ x) (hi : x ≤ 2 ^ 62) : (Int64.ofInt x).toInt = x := by
  apply Int64.toInt_ofInt_of_le <;> omega

/-- A write of the block start keeps the stream invariants and the output frame. -/
theorem block_start_step {h g : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream} {e : DeflateState}
    (step : OutStep h g r ds z' e) (state : g.dstates ds = some e) (bs : Int64) :
    wr (some (.tab ds)) (fun d => { d with block_start := bs }) g = .ok ((), setD g ds { e with block_start := bs }) ∧
      OutStep h (setD g ds { e with block_start := bs }) r ds z' { e with block_start := bs } := by
  have inv : DStInv g ds { e with block_start := bs } :=
    { step.good.inv with blocks := step.good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have good := step.good.setD' (d' := { e with block_start := bs }) rfl step.good.live.status inv (by trkeep)
  refine ⟨by rw [wrD_eq, state], good,
    Zlib.Deflate.Universal.state_write_buffers step.good step.buffers ⟨rfl, rfl, rfl, rfl⟩ good,
    step.static, step.words, fun b mine => step.private_ b mine, step.nalloc,
    step.sizes.chain ⟨fun ref a get => ⟨a, by
        rw [byte_view_setD_depth (result := { e with block_start := bs }) state rfl]; exact get, rfl⟩,
      fun ref => by cases ref <;> rfl⟩⟩

/-- **The window part of the direct copies.** `n` bytes of the window from `block_start` go to the
caller's output, and `block_start` moves past them. -/
theorem stored_copy_a {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {e : DeflateState}
    (good : DGood h r ds z e) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (low : 0 ≤ e.block_start.toInt) (n : UInt32)
    (span : e.block_start.toInt + n.toNat ≤ e.strstart.toNat) (range : e.strstart.toNat ≤ e.window_size.toNat)
    (room : n.toNat ≤ z.avail_out.toNat) :
    ∃ g z', storedCopyA (some (.tab ds)) (some r) n h = .ok ((), g) ∧
      OutStep h g r ds z' { e with block_start := Int64.ofInt (e.block_start.toInt + n.toNat) } ∧
      StreamAccounting z z' 0 n.toNat := by
  obtain ⟨w, wa, win, getW, sizeW⟩ := Zlib.Deflate.Universal.window_block good
  obtain ⟨dst, oo, old, pointer, get, ro, cap, kind⟩ := output_view good buffers out
  have apart : dst ≠ .blk w := by
    intro same; subst same
    rcases kind with ⟨ob, e1, outside⟩ | ⟨_, _, e1, _, _⟩
    · cases e1; exact outside (Or.inr (Or.inr (Or.inl win)))
    · cases e1
  have bsNat : (e.block_start.toInt.toNat : Int) = e.block_start.toInt := Int.toNat_of_nonneg low
  obtain ⟨copy, step, write, outStep, account⟩ := output_copy (so := e.block_start.toInt.toNat) good buffers
    pointer get ro cap kind (src := .blk w) (sa := wa) getW apart n room (by omega)
  have add : Ptr.add e.window e.block_start.toInt h = .ok (.ref (.blk w) e.block_start.toInt.toNat, h) := by
    rw [win]
    have := Ptr.add_ok (off := 0) (k := e.block_start.toInt) (show Space.get h (BRef.blk w) = some wa from getW)
      (by omega) (by omega)
    have e0 : ((0 : Nat) : Int) + e.block_start.toInt = e.block_start.toInt := by omega
    rw [e0] at this
    exact this
  have nInt : n.toUInt64.toInt64.toInt = (n.toNat : Int) := Zlib.Deflate.Universal.u32_toInt64_toInt n
  obtain ⟨g1, hg1⟩ : ∃ g1, g1 = r.put (Space.put h dst (copyRange old wa oo e.block_start.toInt.toNat n.toNat))
      (outStream z (.ref dst (oo + n.toNat)) n) := ⟨_, rfl⟩
  rw [← hg1] at write outStep
  have stateG : g1.dstates ds = some e := by
    rw [hg1]
    rw [ZStreamRef.put_dstates, view_put_dstates]
    · exact good.live.hs
    · intro o e1
      rcases kind with ⟨ob, e2, _⟩ | ⟨owner, _, e2, _, different⟩
      · rw [e1] at e2; cases e2
      · rw [e1] at e2; cases e2; exact different
  have nlt : n.toNat < 2 ^ 32 := n.toNat_lt
  have sslt : e.strstart.toNat < 2 ^ 32 := e.strstart.toNat_lt
  have addB := ladd_value e.block_start n.toUInt64.toInt64 g1 (by omega) (by omega)
  rw [nInt] at addB
  obtain ⟨wrRun, final⟩ := block_start_step outStep stateG (Int64.ofInt (e.block_start.toInt + n.toNat))
  refine ⟨_, _, ?_, final, account⟩
  unfold storedCopyA
  simp only [bind_app, ldDeflateState_tab good.live.hs, ldZ_eq, good.live.hz, add, copy, step, write, addB, wrRun]


/-- **The input part of the direct copies.** -/
theorem stored_read_b {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {e : DeflateState}
    (good : DGood h r ds z e) (buffers : StreamBuffers h r) (globals : LibraryGlobals h)
    (out : z.next_out ≠ .null) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (n : UInt32) (nonzero : n ≠ 0)
    (room : n.toNat ≤ z.avail_out.toNat) (avail : n.toNat ≤ z.avail_in.toNat) :
    ∃ g z', storedReadB (some r) n h = .ok ((), g) ∧ OutStep h g r ds z' e ∧
      StreamAccounting z z' n.toNat n.toNat := by
  obtain ⟨dst, oo, old, pointer, get, ro, cap, kind⟩ := output_view good buffers out
  obtain ⟨h1, g, z', run, readOut, readOut1, step, write, outStep, account⟩ :=
    output_read good buffers globals pointer get ro cap kind inputValid n nonzero room avail
  refine ⟨g, z', ?_, outStep, account⟩
  unfold storedReadB
  simp only [bind_app, readOut, run, readOut1, step, write]

theorem OutStep.trans {h g j : Heap} {r : ZStreamRef} {ds : Nat} {z1 z2 : ZStream} {d1 d2 : DeflateState}
    (first : OutStep h g r ds z1 d1) (second : OutStep g j r ds z2 d2)
    (keys : d2.window = d1.window ∧ d2.prev = d1.prev ∧ d2.head = d1.head ∧ d2.pending_buf = d1.pending_buf) :
    OutStep h j r ds z2 d2 := by
  refine ⟨second.good, second.buffers, second.static.trans first.static, second.words.trans first.words,
    fun b mine => ?_, second.nalloc.trans first.nalloc, first.sizes.chain second.sizes⟩
  rw [second.private_ b mine]
  apply first.private_ b
  unfold DeflateOwned at mine ⊢
  rw [keys.1, keys.2.1, keys.2.2.1, keys.2.2.2] at mine
  exact mine

theorem directLeft_le (left len : UInt32) : (directLeft left len).toNat ≤ len.toNat ∧
    (directLeft left len).toNat ≤ left.toNat := by
  unfold directLeft
  split
  · rename_i big
    have := UInt32.lt_iff_toNat_lt.mp big
    omega
  · rename_i small
    have : ¬ len.toNat < left.toNat := fun c => small (UInt32.lt_iff_toNat_lt.mpr c)
    omega

theorem ite_seq {α : Type} (c : Prop) [Decidable c] (A : M Unit) (R : M α) :
    (if c then (A >>= fun _ => R) else R) = ((if c then A else pure ()) >>= fun _ => R) := by
  split <;> rfl

/-- **The direct copies of an iteration.** -/
theorem stored_direct {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {e : DeflateState}
    (good : DGood h r ds z e) (buffers : StreamBuffers h r) (globals : LibraryGlobals h)
    (out : z.next_out ≠ .null) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (low : 0 ≤ e.block_start.toInt) (left len : UInt32)
    (span : e.block_start.toInt + left.toNat ≤ e.strstart.toNat) (range : e.strstart.toNat ≤ e.window_size.toNat)
    (room : len.toNat ≤ z.avail_out.toNat)
    (avail : (len - directLeft left len).toNat ≤ z.avail_in.toNat) :
    ∃ g z', storedDirect (some (.tab ds)) (some r) left len h =
        .ok ((directLeft left len, len - directLeft left len), g) ∧
      OutStep h g r ds z'
        { e with block_start := Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat) } ∧
      StreamAccounting z z' (len - directLeft left len).toNat len.toNat := by
  have dl := directLeft_le left len
  have rest : (len - directLeft left len).toNat = len.toNat - (directLeft left len).toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr dl.1)
  rw [stored_direct_source]
  -- the window part
  obtain ⟨g1, z1, e1, runA, stepA, accA, e1def⟩ : ∃ g1 z1 e1,
      (if left != 0 then storedCopyA (some (.tab ds)) (some r) (directLeft left len) else pure ()) h = .ok ((), g1) ∧
      OutStep h g1 r ds z1 e1 ∧ StreamAccounting z z1 0 (directLeft left len).toNat ∧
      e1 = { e with block_start := Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat) } := by
    by_cases l0 : left = 0
    · have d0 : directLeft left len = 0 := by subst l0; unfold directLeft; simp
      refine ⟨h, z, e, by simp [l0], ?_, by rw [d0]; exact stream_accounting_self z, ?_⟩
      · exact ⟨good, buffers, rfl, rfl, fun _ _ => rfl, rfl, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩
      · rw [d0]; simp
    · obtain ⟨g1, z1, run, step, acc⟩ := stored_copy_a good buffers out low (directLeft left len)
        (by omega) range (by omega)
      exact ⟨g1, z1, _, by simp [l0, run], step, acc, rfl⟩
  have good1 := stepA.good
  -- the input part
  have avail1 : (len - directLeft left len).toNat ≤ z1.avail_in.toNat := by
    have := accA.2.2.1; omega
  have room1 : (len - directLeft left len).toNat ≤ z1.avail_out.toNat := by
    have := accA.2.2.2.1; omega
  have out1 : z1.next_out ≠ .null := by
    rw [accA.2.2.2.2.2.1]; cases p : z.next_out with
    | null => exact absurd p out
    | ref _ _ => simp [advance]
  have input1 : z1.avail_in ≠ 0 → z1.next_in ≠ .null := by
    intro nz; rw [accA.2.2.2.2.1, advance_zero]; exact inputValid (by
      intro zero; apply nz; apply UInt32.toNat_inj.mp; have := accA.2.2.1; rw [zero] at this; simp at this ⊢; omega)
  have globals1 : LibraryGlobals g1 := by unfold LibraryGlobals at globals ⊢; rw [stepA.static]; exact globals
  by_cases l1 : len - directLeft left len = 0
  · refine ⟨g1, z1, ?_, by rw [← e1def]; exact stepA, ?_⟩
    · simp only [l1, bne_self_eq_false, Bool.false_eq_true, ite_false]
      rw [ite_seq]
      simp only [bind_app, runA]
      rfl
    · rw [l1]
      have := accA
      simpa [UInt32.toNat_zero] using (by
        have r0 : (len - directLeft left len).toNat = 0 := by rw [l1]; rfl
        have : len.toNat = (directLeft left len).toNat := by omega
        rw [this]; exact accA)
  · obtain ⟨g2, z2, runB, stepB, accB⟩ := stored_read_b good1 stepA.buffers globals1 out1 input1
      (len - directLeft left len) l1 room1 avail1
    refine ⟨g2, z2, ?_, ?_, ?_⟩
    · simp only [show (len - directLeft left len != 0) = true by simpa using l1, ite_true]
      rw [ite_seq]
      simp only [bind_app, runA, runB]
      rfl
    · rw [← e1def]; exact stepA.trans stepB ⟨rfl, rfl, rfl, rfl⟩
    · have t := stream_accounting_trans accA accB
      have e2 : (directLeft left len).toNat + (len - directLeft left len).toNat = len.toNat := by omega
      rw [e2, Nat.zero_add] at t
      exact t


/-! ## The invariant across one iteration -/

/-- The fields one iteration of the stored loop changes: the block start, the pending cursor and
the bit buffer. -/
def StoredFields (d d' : DeflateState) : Prop :=
  d' = { d with block_start := d'.block_start, pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used }

theorem StoredFields.refl (d : DeflateState) : StoredFields d d := rfl

theorem StoredFields.trans {a b c : DeflateState} (first : StoredFields a b) (second : StoredFields b c) :
    StoredFields a c := by
  unfold StoredFields at *
  rw [second, first]

open Zlib.Deflate.Universal in
/-- A step that changes only the block start, the pending cursor and the bit buffer, and leaves the
window, the hash tables and the static tables alone, keeps `DInv` once the new shape holds. -/
theorem dinv_stored_keep {h g : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (good : DGood g r ds z' d') (fields : StoredFields d d') (shape : Shape d')
    (sym0 : d.sym_next = 0) (static : g.static = h.static)
    (window : ∀ w, d.window = .ref (.blk w) 0 → g.bytes w = h.bytes w)
    (prev : ∀ p, d.prev = .ref (.blk p) 0 → g.words p = h.words p)
    (head : ∀ q, d.head = .ref (.blk q) 0 → g.words q = h.words q)
    (alloc : z'.zalloc = z.zalloc) (free : z'.zfree = z.zfree) : DInv g r ds z' d' := by
  have carry : ∀ {w p q : Nat} {wa : Array UInt8} {pa qa : Array UInt16},
      d.window = .ref (.blk w) 0 → d.prev = .ref (.blk p) 0 → d.head = .ref (.blk q) 0 →
      h.bytes w = some wa → h.words p = some pa → h.words q = some qa →
      g.bytes w = some wa ∧ g.words p = some pa ∧ g.words q = some qa := by
    intro w p q wa pa qa win prv hd hw hp hq
    exact ⟨by rw [window w win]; exact hw, by rw [prev p prv]; exact hp, by rw [head q hd]; exact hq⟩
  refine ⟨good, ⟨alloc.trans inv.alloc.1, free.trans inv.alloc.2⟩, ?_, shape, ?_, ?_⟩
  · unfold LibraryGlobals; rw [static]; exact inv.globals
  · obtain ⟨chains, slid, rolling⟩ := inv.hashing
    rw [fields]
    refine ⟨fun zero => ?_, fun one => ?_, fun a b large => ?_⟩
    · obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := chains zero
      obtain ⟨gw, gp, gq⟩ := carry win prv hd hw hp hq
      exact ⟨w, p, q, wa, pa, qa, win, prv, hd, gw, gp, gq, H⟩
    · obtain ⟨w, p, q, wa, pa, qa, win, prv, hd, hw, hp, hq, H⟩ := slid one
      obtain ⟨gw, gp, gq⟩ := carry win prv hd hw hp hq
      exact ⟨w, p, q, wa, pa, qa, win, prv, hd, gw, gp, gq, H⟩
    · obtain ⟨w, wa, win, hw, form⟩ := rolling a b large
      exact ⟨w, wa, win, by rw [window w win]; exact hw, form⟩
  · obtain ⟨⟨xs, ⟨b, a, pbuf, get, ledger⟩, dist⟩, clear, below⟩ := inv.symbols
    have empty : xs = [] := by
      have count := ledger.count
      rw [sym0] at count
      simp at count
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst empty
    obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
    obtain ⟨a', get', _⟩ := blocks.ba
    have bid : b0 = b := by
      have e1 := blocks.pbuf
      rw [fields] at e1
      simp only at e1
      rw [pbuf] at e1
      simpa only [Ptr.ref.injEq, BRef.blk.injEq, and_true] using e1.symm
    subst b0
    have ledger' : SymbolLedger a' d' [] := by
      rw [fields]; exact ledger_empty_any (ledger.keep rfl rfl rfl rfl)
    refine ⟨⟨[], ⟨b, a', by rw [fields]; exact pbuf, get', ledger'⟩, by simp⟩, ?_, ?_⟩
    · rw [fields]; exact ⟨clear.bl, clear.opt, clear.fixed⟩
    · intro b1 off _ nonzero
      exact absurd (by rw [fields]; exact sym0) nonzero


open Zlib.Deflate.Universal in
/-- The shape after a stored step at level 0: only the block start and the bit fields moved. -/
theorem shape_stored {d d' : DeflateState} (shape : Shape d) (fields : StoredFields d d') (level : d.level = 0)
    (low : 0 ≤ d'.block_start.toInt) (high : d'.block_start.toInt ≤ d.strstart.toNat)
    (bits : d'.bi_valid.toInt ≤ 7) (cursor : d'.pending = 0 → d'.pending_out = d'.pending_buf) : Shape d' := by
  have zero := shape.levelZero level
  rw [fields] at low high bits cursor ⊢
  exact ⟨shape.room, shape.insert, shape.insertDone, shape.prevLength, shape.matchLength, shape.matchAvailable,
    high, fun ne => absurd level ne, fun _ => ⟨low, zero.2.1, zero.2.2⟩, shape.available, shape.pendingMatch,
    shape.fastLazy, shape.highWater, shape.lastFlush, shape.headerFlush, shape.trailer, bits, cursor,
    shape.symRoom, shape.slides⟩

open Zlib.Deflate.Universal in
/-- What holds at the head of the first loop of `deflate_stored`, relative to the state `d` and
stream `z` at the start of an iteration. -/
structure StoredStep (h g : Heap) (r : ZStreamRef) (ds : Nat) (z z' : ZStream) (d d' : DeflateState) : Prop where
  inv : DInv g r ds z' d'
  buffers : StreamBuffers g r
  pending : d'.pending = 0
  out : z'.next_out ≠ .null
  input : z'.avail_in ≠ 0 → z'.next_in ≠ .null
  fields : StoredFields d d'
  account : ∃ used produced, StreamAccounting z z' used produced
  sizes : ByteSizes h g

theorem input_valid_after {z z' : ZStream} {used produced : Nat} (account : StreamAccounting z z' used produced)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) : z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
  intro nz
  rw [account.2.2.2.2.1]
  cases p : z.next_in with
  | null =>
    have zero : z.avail_in = 0 := by
      by_cases e : z.avail_in = 0
      · exact e
      · exact absurd p (input e)
    have := account.2.2.1
    rw [zero] at this
    exact absurd (UInt32.toNat_inj.mp (by simp at this ⊢; omega)) nz
  | ref _ _ => simp [advance]

theorem output_valid_after {z z' : ZStream} {used produced : Nat} (account : StreamAccounting z z' used produced)
    (out : z.next_out ≠ .null) : z'.next_out ≠ .null := by
  rw [account.2.2.2.2.2.1]
  cases p : z.next_out with
  | null => exact absurd p out
  | ref _ _ => simp [advance]


set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **The rest of an iteration.** With the header room (`have = avail_out - hv`), a length within
it whose input part is available, and `left = strstart - block_start`, the break test, the
emission and the direct copies keep the loop invariant; a completed iteration consumes output. -/
theorem stored_rest {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) (have_ left len : UInt32)
    (haveEq : have_.toNat + (d.bi_valid.toInt.toNat + 42) / 8 = z.avail_out.toNat)
    (leftEq : (left.toNat : Int) = d.strstart.toNat - d.block_start.toInt)
    (lenHave : len.toNat ≤ have_.toNat)
    (lenIn : (len - directLeft left len).toNat ≤ z.avail_in.toNat) :
    ∃ st' g z' d', storedRest (some (.tab ds)) flush (some r) min_block st have_ left len z h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  unfold storedRest
  by_cases stop : (len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH ||
      !(len ≥ left && len - left == z.avail_in))) = true
  · refine ⟨_, h, z, d, by simp only [stop, ite_true]; rfl, ⟨inv, buffers, pend0, out, input, StoredFields.refl d,
      ⟨0, 0, Zlib.Deflate.Engine.Proofs.stream_accounting_self z⟩, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩,
      fun no => by simp at no⟩
  · have stopF : (len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH ||
        !(len ≥ left && len - left == z.avail_in))) = false := by simpa using stop
    have bits := inv.bi_valid_le
    obtain ⟨after, z1, e, runE, goodE, buffersE, accE, fieldsE, pendE, cursorE, bitsE, staticE, _, sizesE,
        winE, prevE, headE⟩ :=
      stored_emit good buffers out pend0 (shape.cursor pend0) bits.2 good.live.back (by omega) len
        (flush == Z_FINISH && (len ≥ left && len - left == z.avail_in))
    have avail1 : z1.avail_out.toNat + (d.bi_valid.toInt.toNat + 42) / 8 = z.avail_out.toNat := accE.2.2.2.1
    have in1 : z1.avail_in.toNat = z.avail_in.toNat := by have := accE.2.2.1; omega
    have globalsE : LibraryGlobals after := by unfold LibraryGlobals; rw [staticE]; exact inv.globals
    have bsE : e.block_start = d.block_start := by rw [fieldsE]
    have ssE : e.strstart = d.strstart := by rw [fieldsE]
    have wsE : e.window_size = d.window_size := by rw [fieldsE]
    have room := shape.room
    obtain ⟨g, z2, runD, stepD, accD⟩ := stored_direct goodE buffersE globalsE (output_valid_after accE out)
      (input_valid_after accE input) (by rw [bsE]; exact zero.1) left len
      (by rw [bsE, ssE]; omega) (by rw [ssE, wsE]; omega) (by omega) (by omega)
    let e2 := { e with block_start := Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat) }
    have dl := directLeft_le left len
    have fields2 : StoredFields d e2 := by
      show e2 = _
      have f1 : StoredFields d e := by unfold StoredFields; rw [fieldsE]
      exact f1.trans rfl
    have bs2 : e2.block_start.toInt = d.block_start.toInt + (directLeft left len).toNat := by
      show (Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat)).toInt = _
      rw [bsE]
      have := d.strstart.toNat_lt
      exact int64_ofInt_toInt _ (by omega) (by omega)
    have shape2 : Shape e2 := shape_stored shape fields2 level0 (by rw [bs2]; omega) (by rw [bs2]; omega)
      (by show e.bi_valid.toInt ≤ 7; omega) (fun _ => cursorE)
    have account := stream_accounting_trans accE accD
    have invG : DInv g r ds z2 e2 := dinv_stored_keep inv stepD.good fields2 shape2 zero.2.2
      (stepD.static.trans staticE)
      (fun w win => by
        rw [stepD.private_ w (Or.inr (Or.inr (Or.inl (by show e.window = _; rw [fieldsE]; exact win))))]
        exact winE w win)
      (fun p prv => by rw [stepD.words]; exact prevE p prv)
      (fun q hd => by rw [stepD.words]; exact headE q hd)
      account.2.2.2.2.2.2.2.1 account.2.2.2.2.2.2.2.2.1
    let all := decide (len ≥ left) && len - left == z.avail_in
    let last : Int32 := if (flush == Z_FINISH && all) = true then 1 else 0
    have run : (if (decide (len < min_block) && (len == 0 && flush != Z_FINISH || flush == Z_NO_FLUSH || !all)) = true
        then (pure { st with len, left, have_, all, brk := true } : M StoredS)
        else (do
          storedEmit (some (.tab ds)) (some r) len last
          let moved ← storedDirect (some (.tab ds)) (some r) left len
          pure { st with last, len := moved.2, left := moved.1, have_, all, brk := false })) h =
        .ok ({ st with last, len := len - directLeft left len, left := directLeft left len, have_, all, brk := false }, g) := by
      dsimp only [all, last]
      simp only [stopF, Bool.false_eq_true, ite_false, bind_app, runE, runD]
      rfl
    refine ⟨_, g, z2, e2, run, ⟨invG, stepD.buffers, by show e.pending = 0; exact pendE,
      output_valid_after account out, input_valid_after account input, fields2, ⟨_, _, account⟩,
      sizesE.chain stepD.sizes⟩, fun (_ : false = false) => ?_⟩
    have := account.2.2.2.1
    omega


theorem header_bytes_value (bv : Int32) (lo : 0 ≤ bv.toInt) (hi : bv.toInt ≤ 7) :
    ((bv.toUInt32 + 42) >>> 3).toNat = (bv.toInt.toNat + 42) / 8 := by
  have cast : bv.toUInt32.toNat = bv.toInt.toNat := by
    rw [Int32.toNat_toUInt32_of_le]
    · rfl
    · rw [Int32.le_iff_toInt_le]; simpa using lo
  have small : bv.toInt.toNat ≤ 7 := by omega
  rw [UInt32.toNat_shiftRight, UInt32.toNat_add, cast, Nat.shiftRight_eq_div_pow]
  have e42 : (42 : UInt32).toNat = 42 := rfl
  have e3 : (3 : UInt32).toNat % 32 = 3 := rfl
  rw [e42, e3, Nat.mod_eq_of_lt (by omega)]

/-- The input part of a length chosen as in the loop is available. -/
theorem stored_len_input (left len avail : UInt32)
    (cap : len.toNat ≤ 65535)
    (choice : left.toNat < 65535 ∧ avail.toNat < 65535 - left.toNat → len.toNat ≤ left.toNat + avail.toNat) :
    (len - directLeft left len).toNat ≤ avail.toNat := by
  have dl := directLeft_le left len
  rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr dl.1)]
  unfold directLeft at dl ⊢
  split
  · omega
  · rename_i small
    have : ¬ len.toNat < left.toNat := fun c => small (UInt32.lt_iff_toNat_lt.mpr c)
    by_cases c : left.toNat < 65535 ∧ avail.toNat < 65535 - left.toNat
    · have := choice c; omega
    · omega

set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **One iteration of the first loop of `deflate_stored`.** -/
theorem stored_iteration {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) :
    ∃ st' g z' d', storedBody (some (.tab ds)) flush (some r) min_block st h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  have bits := inv.bi_valid_le
  have hvN := header_bytes_value d.bi_valid bits.1 bits.2
  unfold storedBody
  simp only [bind_app, ldDeflateState_tab good.live.hs, ldZ_eq, good.live.hz]
  by_cases full : z.avail_out < (d.bi_valid.toUInt32 + 42) >>> 3
  · refine ⟨_, h, z, d, by simp only [full, decide_true, ite_true]; rfl,
      ⟨inv, buffers, pend0, out, input, StoredFields.refl d,
      ⟨0, 0, Zlib.Deflate.Engine.Proofs.stream_accounting_self z⟩, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩,
      fun no => by simp at no⟩
  · have fullN : ¬ z.avail_out.toNat < ((d.bi_valid.toUInt32 + 42) >>> 3).toNat :=
      fun c => full (UInt32.lt_iff_toNat_lt.mpr c)
    rw [hvN] at fullN
    have room := shape.room
    have ws := good.inv.wsz
    have wsize := good.inv.wsize
    have wbits := good.inv.wbits_hi
    have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
    obtain ⟨lsubEq, word, _⟩ := Zlib.Deflate.Universal.Block.flush_length_general (d := d) (by omega)
      shape.blockStart (by omega)
    have lsubRun := congrFun lsubEq h
    have leftN : ((Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32).toNat =
        ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
      rw [UInt64.toNat_toUInt32, word]
      apply Nat.mod_eq_of_lt
      omega
    simp only [full, decide_false, Bool.false_eq_true, ite_false, bind_app, lsubRun, pure_app]
    obtain ⟨left, hleft⟩ : ∃ l, l = (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32 :=
      ⟨_, rfl⟩
    rw [← hleft]
    rw [← hleft] at leftN
    have leftEq : (left.toNat : Int) = d.strstart.toNat - d.block_start.toInt := by
      rw [leftN]; have := shape.blockStart; omega
    have haveN : (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat + (d.bi_valid.toInt.toNat + 42) / 8 =
        z.avail_out.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hvN]; omega)), hvN]
      omega
    have maxN : MAX_STORED.toNat = 65535 := rfl
    have leftLt : left.toNat < 2 ^ 32 := left.toNat_lt
    by_cases c1 : (decide (left < MAX_STORED) && decide (z.avail_in < MAX_STORED - left)) = true
    · have c1N : left.toNat < 65535 ∧ z.avail_in.toNat < 65535 - left.toNat := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at c1
        obtain ⟨a, b⟩ := c1
        have a' := UInt32.lt_iff_toNat_lt.mp a
        have b' := UInt32.lt_iff_toNat_lt.mp b
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))] at b'
        omega
      have sumN : (left + z.avail_in).toNat = left.toNat + z.avail_in.toNat := by
        rw [UInt32.toNat_add]; omega
      simp only [c1, ite_true]
      by_cases c2 : left + z.avail_in > z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3
      · simp only [c2, decide_true, ite_true]
        exact stored_rest inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; omega)
            (fun _ => by have := UInt32.lt_iff_toNat_lt.mp c2; omega))
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < (left + z.avail_in).toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        exact stored_rest inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by omega) (stored_len_input _ _ _ (by omega) (fun _ => by omega))
    · simp only [c1, Bool.false_eq_true, ite_false]
      have c1N : ¬ (left.toNat < 65535 ∧ z.avail_in.toNat < 65535 - left.toNat) := by
        intro ⟨a, b⟩
        apply c1
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨UInt32.lt_iff_toNat_lt.mpr (by rw [maxN]; exact a), UInt32.lt_iff_toNat_lt.mpr ?_⟩
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [maxN]; omega)), maxN]
        exact b
      by_cases c2 : MAX_STORED > z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3
      · simp only [c2, decide_true, ite_true]
        exact stored_rest inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; rw [maxN] at this; omega)
            (fun c => absurd c c1N))
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < MAX_STORED.toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        rw [maxN] at c2N
        exact stored_rest inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by rw [maxN]; omega) (stored_len_input _ _ _ (by rw [maxN]; exact Nat.le_refl _) (fun c => absurd c c1N))


theorem StoredStep.trans {h g j : Heap} {r : ZStreamRef} {ds : Nat} {z1 z2 z3 : ZStream} {d1 d2 d3 : DeflateState}
    (first : StoredStep h g r ds z1 z2 d1 d2) (second : StoredStep g j r ds z2 z3 d2 d3) :
    StoredStep h j r ds z1 z3 d1 d3 := by
  obtain ⟨u1, p1, a1⟩ := first.account
  obtain ⟨u2, p2, a2⟩ := second.account
  exact ⟨second.inv, second.buffers, second.pending, second.out, second.input, first.fields.trans second.fields,
    ⟨_, _, Zlib.Deflate.Engine.Proofs.stream_accounting_trans a1 a2⟩, first.sizes.chain second.sizes⟩

theorem StoredStep.refl {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : Zlib.Deflate.Universal.DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) : StoredStep h h r ds z z d d :=
  ⟨inv, buffers, pend0, out, input, StoredFields.refl d,
    ⟨0, 0, Zlib.Deflate.Engine.Proofs.stream_accounting_self z⟩, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩

/-- **The first loop of `deflate_stored`.** It ends, and the invariant holds afterwards. -/
theorem stored_loop {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : Zlib.Deflate.Universal.DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st0 : StoredS) :
    ∃ st g z' d', cdoWhile (storedBody (some (.tab ds)) flush (some r) min_block)
        (fun st => pure (!st.brk && st.last == 0, st)) st0 h = .ok (st, g) ∧
      StoredStep h g r ds z z' d d' := by
  let P : StoredS → Heap → Prop := fun _ g => ∃ z' d', StoredStep h g r ds z z' d d'
  let μ : StoredS → Heap → Nat := fun _ g => match r.get g with | some z' => z'.avail_out.toNat | none => 0
  have step : ∀ s g, P s g → ∃ s1 g1 c s2 g2, storedBody (some (.tab ds)) flush (some r) min_block s g = .ok (s1, g1) ∧
      (fun st : StoredS => (pure (!st.brk && st.last == 0, st) : M (Bool × StoredS))) s1 g1 = .ok ((c, s2), g2) ∧
      (c = true → P s2 g2 ∧ μ s2 g2 < μ s g) ∧ (c = false → P s2 g2) := by
    intro s g ⟨z1, d1, now⟩
    have level1 : d1.level = 0 := by rw [now.fields]; exact level0
    obtain ⟨s1, g1, z2, d2, run, next, dec⟩ := stored_iteration now.inv now.buffers now.pending now.out now.input
      level1 flush min_block s
    have total := now.trans next
    refine ⟨s1, g1, !s1.brk && s1.last == 0, s1, g1, run, rfl, fun c => ⟨⟨z2, d2, total⟩, ?_⟩,
      fun _ => ⟨z2, d2, total⟩⟩
    have brk : s1.brk = false := by
      cases e : s1.brk
      · rfl
      · rw [e] at c; simp at c
    show (match r.get g1 with | some z' => z'.avail_out.toNat | none => 0) <
      (match r.get g with | some z' => z'.avail_out.toNat | none => 0)
    rw [next.inv.good.live.hz, now.inv.good.live.hz]
    exact dec brk
  have bound : μ st0 h < fuel := by
    show (match r.get h with | some z' => z'.avail_out.toNat | none => 0) < 2 ^ 64
    rw [inv.good.live.hz]
    have := z.avail_out.toNat_lt
    show z.avail_out.toNat < 2 ^ 64
    omega
  obtain ⟨st, g, run, ⟨z', d', final⟩⟩ := C.cdoWhile_decreasing P P μ step
    ⟨z, d, StoredStep.refl inv buffers pend0 out input⟩ bound
  exact ⟨st, g, z', d', run, final⟩

end Zlib.Deflate.Engine.Proofs
