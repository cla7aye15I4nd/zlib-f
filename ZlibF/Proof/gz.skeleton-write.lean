import ZlibF.Proof.«gz.skeleton-model»
import ZlibF.Proof.«gzwrite.c.safe-init»
import ZlibF.Proof.«gz.record-free»
import ZlibF.Proof.«deflate.c.quiet-call»

/-!
# gz file interface, safety skeleton: the write side (skeleton)

Open lemmas of `gzwrite.c` (owner: batch C), and the deflate quiescence lemma `deflate_quiet` that `gz_comp`'s
deflate loop needs to terminate (owner: batch C). Each is a statement with `sorry`.

The codec steps are embedded through `GzWriteInv.codec` (`StreamReachable .deflate`): `gz_init`'s
`deflateInit2_` is the `deflateInit` constructor; `deflate`, `deflateReset` and `deflateParams` are `step`s;
the gz writes of the four buffer fields are `rebuffer`s; `gzclose_w`'s `deflateEnd` is part 3 of the deflate
sequence goal. `Zlib.Gzlib.Spec.Uniq` is `Zlib.Deflate.Spec.Uniq` (`gz_uniq_iff_deflate`, `Iff.rfl`).

Inside `gz_write`'s large path `next_in` points into the caller's buffer, so `gz_comp` and `gz_zero` are stated
for `GzInvUpToInput` (the invariant of the record with no pending input) and an explicit input region.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- The record with no pending input (`avail_in = 0`, `next_in` NULL), which meets W4 whatever `next_in` was. -/
def clearIn (s : GzState) : GzState := { s with strm := { s.strm with avail_in := 0, next_in := .null } }

/-- **The writer invariant up to the pending input**: `GzInv` of the record with no pending input, and the pending
input lies in `src`, which is the `in` buffer or a caller region the handle does not own. -/
def GzInvUpToInput (h : Heap) (i : Nat) (s : GzState) (src : Region) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearIn s)) i (clearIn s) ∧ s.mode = GZ_WRITE ∧
  ((s.strm.next_in = .null ∧ s.strm.avail_in = 0) ∨
    ∃ a, s.strm.next_in = padv src.pointer a ∧ a + s.strm.avail_in.toNat ≤ src.length) ∧
  (src.pointer = s.«in» ∧ src.length = s.size.toNat ∨
    (∃ xs, Bytes h src.pointer src.length xs) ∧ ∀ b, ByteRoot src.pointer b → ¬ GzOwned h i s b)

/-- `GzInvUpToInput` without the readability of a caller region: what holds after `gz_comp` fails. A failed write
calls `gz_error(Z_ERRNO, zstrerror())`, and `zstrerror` invalidates a borrowed `strerror` view, which a caller may
have passed as the input region (`GzRange` admits it); the C does not read the input after `-1` (`gz_write` resets
`next_in` to `in`). -/
def GzInvUpToInputWeak (h : Heap) (i : Nat) (s : GzState) (src : Region) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearIn s)) i (clearIn s) ∧ s.mode = GZ_WRITE ∧
  ((s.strm.next_in = .null ∧ s.strm.avail_in = 0) ∨
    ∃ a, s.strm.next_in = padv src.pointer a ∧ a + s.strm.avail_in.toNat ≤ src.length) ∧
  (src.pointer = s.«in» ∧ src.length = s.size.toNat ∨ ∀ b, ByteRoot src.pointer b → ¬ GzOwned h i s b)

/-! ## Deflate quiescence (a functional fact of deflate a safety proof needs: in scope) -/

/-- **`DeflateQuiet`** (statement corrected 2026-11-12, agreed with batch 1 and batch C): a potential `Φ` and a
predicate `Quiet`, per flush value, for `deflate` calls with no input.
1. A call with at least 8 bytes of room that fills the output lowers `Φ`.
2. A call that ends with room leaves the stream `Quiet`.
3. From `Quiet`, a call produces nothing.
4. A rebuffering of the output alone (what `gz_comp` does between calls) keeps `Φ` and `Quiet`.
So `gz_comp`'s `do { deflate } while (have)` ends when its buffer has at least 8 bytes (`GzCommon.want`: `gzbuffer`
clamps to 8; zlib.h: `avail_out` should exceed six when a flush marker begins): the calls that fill are bounded by
`Φ`, and a call that ends with room is followed by at most one call, which produces nothing.

Clauses 1–3 assume the deflate arguments of the history (`StreamBuffers`, `ActiveHeader`) and a non-NULL `next_out`:
with `next_out = NULL` the call is refused with the state and the room unchanged, so clause 2 would fail, and
`CallerRange` allows NULL. Clause 4 assumes reachability: `Φ` and `Quiet` read the deflate state, which a rebuffer
keeps only for a stream that owns it. `gz_comp` has all of them (`GzWriteInv` W4, W5, W6).

The intended witnesses (batch 3): `Φ` is lexicographic, encoded in `Nat`: (2 before `FINISH_STATE`, 1 while the
trailer is due, 0 after; the header rank, INIT/GZIP 6, EXTRA 5, NAME 4, COMMENT 3, HCRC 2, else 0; 2^64 − `gzindex`;
the work 3·`lookahead` + 2·`match_available` + [`sym_next` ≠ 0] + at level 0 `strstart` − `block_start`; `pending`).
`Quiet flush`: `pending` = 0 with `last_flush` = flush ≠ `Z_FINISH` or a finished stream with `wrap` ≤ 0, or
`FINISH_STATE` with flush ≠ `Z_FINISH`. On the real C (1.3M configurations, 86.5M calls: levels 0–9, strategies 0–4,
memLevel 1/8/9, raw/zlib/gzip and `windowBits` 9, a gzip header with long extra, name and comment, `deflatePrime`;
buffers of at least 8 bytes) no clause is violated. The earlier form (every output-producing call with any room
lowers `Φ`) is false: with an output buffer of 1..7 bytes the real C cycles (a marker fills the output,
`last_flush = -1`, the next call emits the marker again); batch C's harness, `batchc-deflate-quiet.md`. A "flush
owed" component (`last_flush` ≠ flush) before `pending` is also false: the call that flushes a pending gzip trailer
lowers `pending` and sets `last_flush = -1`. Owner: batch 3. -/
def DeflateQuiet : Prop :=
  ∃ (Φ : Int32 → Heap → ZStreamRef → Nat) (Quiet : Int32 → Heap → ZStreamRef → Prop),
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r < Φ flush h r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out ≠ 0 → Quiet flush after r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      Quiet flush h r → 0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = z.avail_out) ∧
    (∀ (flush : Int32) (h after : Heap) (r : ZStreamRef) (z z' : ZStream), StreamReachable .deflate h r →
      Rebuffer h after r → r.get h = some z →
      r.get after = some z' → z'.next_in = z.next_in → z'.avail_in = z.avail_in →
      Φ flush after r = Φ flush h r ∧ (Quiet flush h r → Quiet flush after r))

/-- **`deflate_quiet`** (batch 3, proved on dev: `deflate_quiet_holds`, dde03ce6). -/
theorem deflate_quiet : DeflateQuiet := Zlib.Deflate.Universal.Quiet.deflate_quiet_holds

/-! ## Internal helpers -/

/-- `gz_init(state)`: allocates `in` (`2·want`), and for a compressing writer `out` (`want`) and the deflate state
(`deflateInit2_(level, 31, 8, strategy)`: the `deflateInit` step); W2 becomes W3, W5, W6; on failure frees what it
allocated and records `Z_MEM_ERROR` (ledger: nothing new). -/
theorem gz_init_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) :
    RunSafe (Zlib.Gzwrite.gz_init (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  Zlib.Gzwrite.SafeInit.gz_init_safe' i h fs s inv hfs hm hsz

/-- `gz_comp(state, flush)`: the transparent write loop, the deflate loop (`deflate_quiet`, with `GzCommon.want`'s
buffer of at least 8 bytes) with its write-out
loop (M2: a nonempty write returns `-1` or at least 1), and `deflateReset` after a finish. Only the `in`/`out`
buffers and the deflate state are written; the input region is only read. On `-1` the input region may have
become unreadable (a borrowed `strerror` view invalidated by `zstrerror`): the post-state is `GzInvUpToInputWeak`. -/
theorem gz_comp_safe (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 4) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) := by
  sorry

/-- `gz_zero(state)`: compresses `skip` zeros through `in`; `x.pos` bounded (local patch for W7). -/
theorem gz_zero_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_zero (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  sorry

/-- `gz_write(state, buf, len)`: the small path copies into `in` (W4 keeps `copy = size - have` from wrapping);
the large path points `next_in` at the caller's buffer only inside the call and resets it to `in`, also on error.
`x.pos` bounded (local patch for W7). -/
theorem gz_write_safe (i : Nat) (buf : BPtr) (len : UInt64) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE)
    (hbuf : len = 0 ∨ GzRange h i s buf len.toNat false) :
    RunSafe (Zlib.Gzwrite.gz_write (gzSt i) buf len) fs h True fun r fs' after =>
      r.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  sorry

/-- `gz_vacate(state)`: makes room for `gzvprintf`; returns 0 with the input window ending at `in + size`, or 1. -/
theorem gz_vacate_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_vacate (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = 1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  sorry

/-! ## Public calls (shape `GzCallSafe`) -/

/-- `gzwrite`: the `int` check, then `gz_write`. Relies on the local patch for W7. -/
theorem gzwrite_step (i : Nat) (buf : BPtr) (len : UInt32) :
    GzCallSafe i (.gzwrite (some (.in_gzstate_x i)) buf len) := by
  sorry

/-- `gzfwrite`: the `size_t` product check, then `gz_write`. Relies on the local patch for W7. -/
theorem gzfwrite_step (i : Nat) (buf : BPtr) (size nitems : UInt64) :
    GzCallSafe i (.gzfwrite buf size nitems (some (.in_gzstate_x i))) := by
  sorry

/-- `gzputc`: the byte into `in` when there is room, else `gz_write` of a local block (freed). Relies on the
local patch for W7. -/
theorem gzputc_step (i : Nat) (c : Int32) : GzCallSafe i (.gzputc (some (.in_gzstate_x i)) c) := by
  sorry

/-- `gzputs`: `strlen`, the `int` check, then `gz_write`. Relies on the local patch for W7. -/
theorem gzputs_step (i : Nat) (str : BPtr) : GzCallSafe i (.gzputs (some (.in_gzstate_x i)) str) := by
  sorry

/-- `gzvprintf`: `gz_vacate`, `vsnprintf` into `[in + have, in + have + size)` (batch C's oracle M6: `-1` past
`INT_MAX` or on an oracle failure, never a fault), the sentinel check and the stall paths. Relies on batch C's
`vsnprintf` change and on the local patch for W7. -/
theorem gzvprintf_step (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzvprintf (some (.in_gzstate_x i)) format va) := by
  sorry

/-- `gzprintf` is `gzvprintf` (definitionally). -/
theorem gzprintf_step (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzprintf (some (.in_gzstate_x i)) format va) :=
  gzvprintf_step i format va

/-- `gzflush`: `gz_zero` then `gz_comp(flush)` for `0 ≤ flush ≤ 4`. -/
theorem gzflush_step (i : Nat) (flush : Int32) : GzCallSafe i (.gzflush (some (.in_gzstate_x i)) flush) := by
  sorry

/-- `gzsetparams`: `gz_zero`, `gz_comp(Z_BLOCK)` and `deflateParams` (a `step` of the deflate history). -/
theorem gzsetparams_step (i : Nat) (level strategy : Int32) :
    GzCallSafe i (.gzsetparams (some (.in_gzstate_x i)) level strategy) := by
  sorry

/-- `gzclose_w`: refuses a reader; otherwise `gz_zero` and `gz_comp(Z_FINISH)` (their failures included),
`deflateEnd` (part 3 of the deflate sequence goal) for a compressing writer, frees `out`, `in`, the message, the
path and the record, and closes the descriptor, which is released whatever `close` returns (M4). Also after a
broken deflate stream (observation O-1: it frees and returns `Z_STREAM_ERROR`). -/
theorem gzclose_w_step (i : Nat) : GzCloseSafe i (.gzclose_w (some (.in_gzstate_x i))) := by
  sorry

end ZlibF.Spec.Public.GzSkeleton
