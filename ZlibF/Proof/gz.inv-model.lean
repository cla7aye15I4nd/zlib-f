import ZlibF.Spec.Public.GzControl
import ZlibF.Spec.PlatformMemory

/-!
# gz file interface, safety: the representation invariant `GzInv` and the shape of a safe call

The shared definitions of the gz safety proof (skeleton branch `skeleton/gz`, file `gz.skeleton-model.lean`),
over the OS-call oracle of `ZlibF/Zlib/gzfs.lean`:

1. `GzInv` (`GzCommon`, `GzReadInv`, `GzWriteInv`): the representation invariant of an open handle, with batch
   C's W1–W10 folded into the write part. Other modules use its interface lemmas, not the definition.
2. `GzCallSafe`: safety of one public call on a handle in `GzInv`, for every world.
3. `ReadsFinite`: the M7 premise of the termination half of the reading calls: the descriptor is non-negative and
   has a read budget below `2^61` bytes in the OS-call oracle (`Fs.readBudget`).

Corrections against the skeleton at `7d896179` (strengthenings):
- `GzCommon.next` also excludes the message block (`blkOf s.msg ≠ some b`), as `NextOk` does. Without it `x.next`
  may point into the message block, which `gz_error` frees, so `GzInv` would not survive `gz_error`.
- With no codec set up (`GzReadInv.unalloc`, W2, W8) `strm.state` is NULL, instead of "the codec owns no block".
  The weaker form let `strm.state` name a block that is not live, which a caller may then allocate, so
  `GzInv.caller` was false.
- `GzCommon.recordFree`: the codec does not own the record block, so that a write of the record (`put_scalars`,
  `gz_error`) is a rebuffer of the codec.
- `GzReadInv.posHave`: `x.pos + x.have ≤ GZ_OFF_MAX` on return (patch 0004). Without it the buffered path of
  `gzgetc` overflows `x.pos`.
- `GzReadInv.againSize`: `size = 0 → again = 0`. Without it `gzungetc` computes `out + 2·size - 1` on a NULL `out`.
- `GzReadInv.haveSkip`: `x.have ≠ 0 → skip = 0` at call boundaries; `GzInvUpToSkip` is the invariant without it, for
  the inside of reading calls. Without it `gzgetc` returns a buffered byte while a skip is pending, and moves `x.pos`
  past `GZ_OFF_MAX - skip`.
- `GzPost` has a no-grab clause: a block owned after a helper call was owned before it or was not live before it.

Patches. Some clauses (`GzCommon.pos`, `GzCommon.next`, `GzReadInv.output`) are established only for the patched
source (patch 0002, patch 0003, patch 0005, and local patches for F-1 and W7). The definitions do not depend on that;
the lemmas that need a patch say so.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

namespace GzOracle

/-- The descriptor number `j` is open. -/
def FdOpen (fs : Fs) (j : Nat) : Prop := ∃ f, fs.fds[j]? = some (some f)

end GzOracle

/-- The handle's descriptor is non-negative and has a read budget in the OS-call oracle, so every later read is cut
to it. A negative descriptor is unbudgeted (`readCap` does not cut its reads), hence the first conjunct. -/
def HasBudget (fs : Fs) (fd : Int32) : Prop := 0 ≤ fd.toInt ∧ fs.readBudget fd.toInt.toNat ≠ none

/-- **M7, the finiteness premise.** The handle's descriptor has a read budget (`HasBudget`) below `2^61` bytes: the
total the descriptor can still deliver. A premise of the termination half only, and only for the calls of
`NeedsReadBound`; `docs/deviations.md`, "Gz reading termination". A finite budget is a real requirement: an endless
source (an endless `FNAME`, or endless empty gzip members) makes one `gzread` call run forever in C. The figure `2^61`
is the model's limit, not zlib's: a loop of the model has `2^64` trips of fuel, and each round of the reading loops
takes input or ends, so a budget below `2^61` keeps them within it. -/
def ReadsFinite (fs : Fs) (fd : Int32) : Prop :=
  HasBudget fs fd ∧ (fs.readBudget fd.toInt.toNat).getD 0 < 2 ^ 61

/-- The calls whose termination needs M7: the loops of `gz_fetch` (over empty gzip members), `gz_skip` and
`gz_read` read until the input ends. `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets` reach them, `gzungetc`
through `gz_skip`. `gzdirect` (one `gz_look`, whose `gz_load` loop is bounded by the request), the write side
(M2) and `gzseek` (no reading loop: the skip is deferred) do not need it. -/
def NeedsReadBound : Call → Prop
  | .gzread _ _ _ | .gzfread _ _ _ _ | .gzgetc _ | .gzgetc_ _ | .gzgets _ _ _ | .gzungetc _ _ => True
  | _ => False

/-! ## 2. The invariant -/

/-- A pointer to the start of a live writable byte block of exactly `n` bytes (`gz_look` and `gz_init` allocate
exactly these sizes). -/
def ExactBuffer (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false ∧ a.size = n

/-- The block of a pointer into a heap block. -/
def blkOf : BPtr → Option Nat
  | .ref (.blk b) _ => some b
  | _ => none

/-- The pointer advanced by `n` bytes. -/
def padv : BPtr → Nat → BPtr
  | .null, _ => .null
  | .ref r o, n => .ref r (o + n)

/-- The pointer fields the record owns: path, message, and the buffers when they exist (`out` only for a
reader or a compressing writer). -/
def ownedPtrs (s : GzState) : List BPtr :=
  [s.path, s.msg] ++
    (if s.size ≠ 0 then s.«in» :: (if s.mode = GZ_READ ∨ s.direct = 0 then [s.out] else []) else [])

/-- The embedded stream `&state->strm`. -/
def gzStrm (i : Nat) : ZStreamRef := .in_gzstate_strm i

/-- The part of the invariant common to readers and writers. -/
structure GzCommon (h : Heap) (i : Nat) (s : GzState) : Prop where
  record : h.gzstates i = some s
  mode : s.mode = GZ_READ ∨ s.mode = GZ_WRITE
  fresh : Fresh h
  uniq : Zlib.Gzlib.Spec.Uniq h
  globals : LibraryGlobals h
  /-- needed by `StreamReachable .inflate` at each codec step -/
  fit : ZlibF.PlatformMemory.ByteObjectsFit h
  path : ∃ p, CString h s.path p ∧ MallocBuffer h s.path (p.length + 1)
  /-- W9 -/
  msg : s.msg = .null ∨ ∃ m, CString h s.msg m ∧ MallocBuffer h s.msg (m.length + 1)
  memerr : s.err = Z_MEM_ERROR → s.msg = .null
  /-- W1 (`gzbuffer` clamps to 8 and refuses a doubling overflow) -/
  want : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31
  size : s.size = 0 ∨ s.size = s.want
  /-- the owned pointer blocks are distinct, differ from the record and from the codec's blocks -/
  distinct : ((ownedPtrs s).filterMap blkOf).Nodup ∧
    (∀ p, p ∈ ownedPtrs s → ∀ b, blkOf p = some b → b ≠ i ∧ ¬ StreamOwned h (gzStrm i) b)
  /-- every owned block is live -/
  live : ∀ b, GzOwned h i s b → h.live b
  /-- positions. Relies on local patches for F-1 and W7 (`x.pos + skip` never passes `GZ_OFF_MAX`) and on patch
  0002 (R-1). Lower bound: `x.pos + x.have`, the position of the end of the buffered output, is never negative;
  `gzungetc` lowers `x.pos` by one and raises `x.have` by one. It implies `-(2·size) ≤ x.pos` for a reader
  (`GzInv.pos_lower`), since `x.have ≤ 2·size` by `GzReadInv.output`. -/
  pos : 0 ≤ s.skip.toInt ∧ s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807 ∧
    0 ≤ s.x.pos.toInt + s.x.have.toNat
  /-- With buffered output (`x.have ≠ 0`), `x.next` is inside an owned buffer other than the message with `x.have`
  bytes after it. With `x.have = 0` it says nothing: the direct path of `gz_read` (`gz_decomp` into the caller's
  buffer) leaves `x.next = next_out - have` inside the caller's buffer with `x.have = 0`, and patch 0005 only guards
  `x.next += n` with `n != 0` (regression `gz-next-caller.c`). After patch 0005 every read or advance of `x.next`
  happens with `x.have ≠ 0` (`gz_skip_have`, `gzseek64`, `gzgetc`, `gzgets`, the compare in `gzungetc`), so a stale
  or never-written `x.next` (R-3, R-4) is never used. -/
  next : s.x.have ≠ 0 → ∃ b off a, s.x.next = .ref (.blk b) off ∧ b ≠ i ∧ GzOwned h i s b ∧
    blkOf s.msg ≠ some b ∧ h.bytes b = some a ∧ off + s.x.have.toNat ≤ a.size
  nullHave : s.x.next = .null → s.x.have = 0
  /-- The codec does not own the record block. The record holds the embedded stream, so a write of the record is a
  rebuffer of the codec only when the codec's frame lets block `i` change. Each codec step must re-establish it:
  for a compressing writer it rests on the deflate fact that `window`, `prev`, `head` and `pending_buf` are never
  the record block. -/
  recordFree : ¬ StreamOwned h (gzStrm i) i

/-- The message of the embedded stream is `NULL` or a string literal of the sources (`inflateInit2_` and
`inflateReset` clear it, `inflate` sets literals). `gz_decomp` hands it to `gz_error`. Only asked with buffers: a
failed `inflateInit2` in `gz_look` sets `size = 0`. -/
def MsgLit (s : GzState) : Prop :=
  s.size ≠ 0 → s.strm.msg = .null ∨ ∃ j, j < strTable.size ∧ s.strm.msg = .ref (.str j) 0

/-- The reader part (`s.mode = GZ_READ`). The note's clause "past ≠ 0 → skip = 0" is not included: a forward
`gzseek` after a short read keeps `past` and sets `skip` (`Api.GzSeek`). -/
structure GzReadInv (h : Heap) (i : Nat) (s : GzState) : Prop where
  how : s.how = LOOK ∨ s.how = GZ_COPY ∨ s.how = GZIP
  /-- COPY is set only when `direct ≠ -1`; it may be 0: after a gzip member with trailing data, `gzclearerr` and
  another read take `gz_look`'s COPY branch with `direct = 0` (regression `gz-copy-direct.c`). -/
  copyDirect : s.how = GZ_COPY → s.direct = 0 ∨ s.direct = 1
  gzipDirect : s.how = GZIP → s.direct = 0
  direct : s.direct = -1 ∨ s.direct = 0 ∨ s.direct = 1
  junk : s.junk = -1 ∨ s.junk = 0 ∨ s.junk = 1
  flags : (s.eof = 0 ∨ s.eof = 1) ∧ (s.past = 0 ∨ s.past = 1) ∧ (s.again = 0 ∨ s.again = 1)
  /-- no codec while no buffers: `strm.state` is NULL. **To confirm**: a fresh record has `strm.state = NULL`
  only in the model; C leaves it uninitialised, and never reads it before `gz_look` writes it. -/
  unalloc : s.size = 0 → s.x.have = 0 ∧ s.strm.avail_in = 0 ∧ s.how = LOOK ∧ s.strm.state = none
  bufs : s.size ≠ 0 → ExactBuffer h s.«in» s.size.toNat ∧ ExactBuffer h s.out (2 * s.size.toNat)
  input : s.strm.avail_in = 0 ∨ ∃ a, s.strm.next_in = padv s.«in» a ∧ a + s.strm.avail_in.toNat ≤ s.size.toNat
  /-- relies on patch 0003 (R-2: `x.next` is set before a COPY load can fail) -/
  output : s.x.have ≠ 0 → ∃ c, s.x.next = padv s.out c ∧ c + s.x.have.toNat ≤ 2 * s.size.toNat
  /-- the inflate stream is in the inflate history, with no header record (`gz_look` never calls
  `inflateGetHeader`) -/
  codec : s.size ≠ 0 → StreamReachable .inflate h (gzStrm i) ∧
    ∃ z k st, (gzStrm i).get h = some z ∧ z.state = some (.inflate k) ∧ h.istates k = some st ∧ st.head = none
  /-- the end of the buffered output, `x.pos + x.have`, is a representable position. Relies on the local patch for
  F-1 (patch 0004): `gz_fetch` fills at most `GZ_OFF_MAX - x.pos` bytes when that is positive. At
  `x.pos = GZ_OFF_MAX` it loads one byte to find the end of the input, so the clause may fail inside a call; its
  callers there, `gz_read` and `gzgets`, drop that byte (`x.have = 0`, `Z_DATA_ERROR`) before they return.
  `gz_skip` never fetches there: it fetches only with `skip > 0`, and `x.pos + skip ≤ GZ_OFF_MAX`. With this clause
  the buffered paths of `gzgetc` (`x.pos++`) and `gz_skip_have` need no guard. -/
  posHave : s.x.pos.toInt + s.x.have.toNat ≤ 9223372036854775807
  /-- no stalled read without buffers: only `gz_load` sets `again`, and it runs only with buffers; `gz_reset`
  clears it. Without it `gzungetc` could skip its `size == 0` refusal after a failed `gz_look`. -/
  againSize : s.size = 0 → s.again = 0
  /-- buffered output means no pending skip: the buffered bytes are at the current position `x.pos`, as the
  buffered paths of `gzgetc` (the function and the zlib.h macro) assume. It holds at call boundaries: `gzseek64`
  empties the buffer or zeroes the offset before it sets `skip`; `gz_read`, `gzgets` and `gzungetc` run `gz_skip`
  first (it ends with `skip = 0`, or fails with `x.have = 0`); `gzdirect` follows `gz_look` with `gz_skip_have`.
  Inside a reading call `gz_look` (COPY) and `gz_fetch` (called by `gz_skip`) may leave both nonzero: their posts are
  stated over `GzInvUpToSkip`. -/
  haveSkip : s.x.have ≠ 0 → s.skip = 0
  /-- a reader that stalled at the end of its input has no pending input. Otherwise `gz_read` loops forever:
  `gz_avail` reads nothing at `eof`, and `gz_look` returns 0 in LOOK because `again && avail_in < 4`. `again` is
  set only by a stalled `gz_load`, which runs with `eof = 0`; the junk path of `gz_decomp` sets `eof` with
  `avail_in = 0`; `gzclearerr` and `gz_reset` clear `eof` or `again`; `gz_look`'s COPY branch zeroes `avail_in`. -/
  againEof : s.again ≠ 0 → s.eof ≠ 0 → s.strm.avail_in = 0
  /-- `Z_STREAM_END` is never recorded: `state->err` is written only at open (`Z_OK`) and by `gz_error`,
  and no caller passes `Z_STREAM_END`. `gz_decomp` would return 0 on a failed `gz_avail` with this code. -/
  errEnd : s.err ≠ Z_STREAM_END
  /-- COPY has no pending input: `gz_look` zeroes `avail_in` when it sets COPY, `gzseek64` zeroes it in COPY, and in
  COPY only `gz_load` into `out` reads. -/
  copyIn : s.how = GZ_COPY → s.strm.avail_in = 0
  /-- the embedded stream's message is `NULL` or a literal (`MsgLit`) -/
  msgLit : MsgLit s

/-- The writer part (`s.mode = GZ_WRITE`): batch C's W1–W10. W1 and W9 are in `GzCommon`; W10 needs no fact;
W7 is the position clause of `GzCommon` (relies on the local patch for W7). -/
structure GzWriteInv (h : Heap) (i : Nat) (s : GzState) : Prop where
  /-- the `gzgetc` macro reads `x.have` on any handle -/
  have0 : s.x.have = 0
  direct : s.direct = 0 ∨ s.direct = 1
  reset : s.reset = 0 ∨ s.reset = 1
  /-- W2: no codec while no buffers (`strm.state` NULL; **to confirm** as for the reader: C never reads it
  before `gz_init` writes it) -/
  unalloc : s.size = 0 → s.strm.state = none
  /-- W3 -/
  bufs : s.size ≠ 0 → ExactBuffer h s.«in» (2 * s.size.toNat) ∧ (s.direct = 0 → ExactBuffer h s.out s.size.toNat)
  /-- W4: `next_in` is NULL with no pending input, or points into `in` (which then exists) with its pending input
  inside. So the input of the embedded deflate stream is always a `CallerRange`, as every deflate result asks
  (`StreamBuffers`), also with no pending input. The C: `gz_init` sets `next_in = NULL` (`avail_in` is 0 from
  `gz_reset`); the writers point it into `in`, or into a caller buffer only inside `gz_write`'s large path. -/
  input : (s.strm.next_in = .null ∧ s.strm.avail_in = 0) ∨
    (s.size ≠ 0 ∧ ∃ a, s.strm.next_in = padv s.«in» a ∧ a + s.strm.avail_in.toNat ≤ s.size.toNat)
  /-- W5 -/
  output : s.direct = 0 → s.size ≠ 0 → ∃ b c, s.strm.next_out = padv s.out b ∧
    s.strm.avail_out.toNat = s.size.toNat - b ∧ s.x.next = padv s.out c ∧ c ≤ b ∧ b ≤ s.size.toNat
  /-- W6: the deflate stream is in the deflate history, with no gzip header record -/
  codec : s.direct = 0 → s.size ≠ 0 → StreamReachable .deflate h (gzStrm i) ∧
    ∃ z k d, (gzStrm i).get h = some z ∧ z.state = some (.deflate k) ∧ h.dstates k = some d ∧ d.gzhead = none
  /-- W8: a transparent writer has no codec -/
  transparent : s.direct ≠ 0 → s.strm.state = none

/-- **The gz representation invariant.** Other modules use its interface lemmas, not this definition. -/
def GzInv (h : Heap) (i : Nat) (s : GzState) : Prop :=
  GzCommon h i s ∧ (s.mode = GZ_READ → GzReadInv h i s) ∧ (s.mode = GZ_WRITE → GzWriteInv h i s)

/-! ## The shape of a safe call -/

/-- The caller regions a call may write. A zero-length read names no region: `BufferFrame` keeps the view of every
named region, and with `len = 0` the buffer may be any pointer, also one into a block the call frees
(regression `tests/verification/regressions/gz-read-empty-region.lean`). -/
def GzWriteRegions : Call → List Region
  | .gzread _ p n => if 0 < n.toNat ∧ n.toNat < 2 ^ 31 then [⟨p, n.toNat⟩] else []
  | .gzfread p size n _ =>
      if 0 < size.toNat * n.toNat ∧ size.toNat * n.toNat < 2 ^ 64 then [⟨p, size.toNat * n.toNat⟩] else []
  | .gzgets _ p n => if 1 ≤ n.toInt then [⟨p, n.toInt.toNat⟩] else []
  | .gzerror _ p => [⟨p, 4⟩]
  | _ => []

/-- The set of open descriptors is unchanged. -/
def FdsKept (fs fs' : Fs) : Prop := ∀ j, GzOracle.FdOpen fs' j ↔ GzOracle.FdOpen fs j

/-- After a non-closing call that returned: a well-formed world, the invariant, mode and descriptor kept, only
the handle's blocks and the declared caller regions written, and an exact ledger. -/
def GzStepPost (h : Heap) (i : Nat) (s : GzState) (call : Call) (fs' : Fs) (after : Heap) : Prop :=
  FileSystem fs' ∧ ∃ s', GzInv after i s' ∧ s'.mode = s.mode ∧ s'.fd = s.fd ∧
    BufferFrame h after (GzOwned h i s) (GzWriteRegions call) ∧
    LiveChange h after
      (fun b => GzOwned after i s' b ∧ ¬ h.live b)
      (fun b => GzOwned h i s b ∧ ¬ GzOwned after i s' b)

/-- **Safety of one call** on a handle in `GzInv`, for every world (every oracle): no fault other than running
out of fuel; it returns, under M7 for the calls that need it; and when it returns the open descriptors are kept
and `GzStepPost` holds. -/
def GzCallSafe (i : Nat) (call : Call) : Prop :=
  ∀ h fs s, GzInv h i s → FileSystem fs → GzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)

/-! ## Helper shapes for the internal call lemmas -/

/-- The three parts of a run in `G` that a safety lemma states: no fault but `outOfFuel`; a result under the
premise `finite` (M7 where needed, `True` otherwise); and `post` of every result. -/
def RunSafe {α : Type} (m : G α) (fs : Fs) (h : Heap) (finite : Prop) (post : α → Fs → Heap → Prop) : Prop :=
  (∀ e, m fs h = .error e → e = .outOfFuel) ∧
  (finite → ∃ a fs' after, m fs h = .ok ((a, fs'), after)) ∧
  (∀ a fs' after, m fs h = .ok ((a, fs'), after) → post a fs' after)

/-- `GzStepPost` with explicit caller regions (for the internal helpers), and no grab: every block the handle owns
after the call was owned before it, or was not live before it. The last clause lets two helper calls compose with
an exact ledger (`gz_look` then `gz_skip` in `gzungetc`; `gz_read` then a free in `gzgetc`). -/
def GzPost (h : Heap) (i : Nat) (s : GzState) (regions : List Region) (fs' : Fs) (after : Heap)
    (inv : Heap → Nat → GzState → Prop) : Prop :=
  FileSystem fs' ∧ ∃ s', inv after i s' ∧ s'.mode = s.mode ∧ s'.fd = s.fd ∧
    BufferFrame h after (GzOwned h i s) regions ∧
    LiveChange h after
      (fun b => GzOwned after i s' b ∧ ¬ h.live b)
      (fun b => GzOwned h i s b ∧ ¬ GzOwned after i s' b) ∧
    (∀ b, GzOwned after i s' b → GzOwned h i s b ∨ ¬ h.live b)

/-- The record with no buffered output (`x.have = 0`, `x.next = NULL`). -/
def clearOut (s : GzState) : GzState := { s with x := { s.x with «have» := 0, next := .null } }

/-- **The invariant up to the buffered output**, for the inside of a reading call: `GzInv` of the record with no
buffered output. `gz_decomp` and `gz_load` into the caller's buffer leave `x.next` in that buffer; `GzInv` allows
that once `x.have = 0` (`GzCommon.next`), and this is what holds before `x.have` is reset. -/
def GzInvUpToOutput (h : Heap) (i : Nat) (s : GzState) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearOut s)) i (clearOut s)

/-- The record with no pending skip. -/
def clearSkip (s : GzState) : GzState := { s with skip := 0 }

/-- **The invariant up to the pending skip**, for the inside of a reading call: `GzInv` without the clause
`GzReadInv.haveSkip`. It is `GzInv` of the record with no pending skip, plus the bounds of `GzCommon.pos` on the
skip. `gz_look` (COPY) and `gz_fetch` (from `gz_skip`) may buffer output while a skip is pending; the caller
(`gz_skip`, `gzungetc`, `gzdirect`) consumes it before it returns. -/
def GzInvUpToSkip (h : Heap) (i : Nat) (s : GzState) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearSkip s)) i (clearSkip s) ∧
    0 ≤ s.skip.toInt ∧ s.x.pos.toInt + s.skip.toInt ≤ 9223372036854775807

/-! ## Interface lemmas of `GzInv` -/

/-- The state pointer of handle `i`. -/
def gzSt (i : Nat) : GzStatePtr := some (.tab i)

/-- Interface: the common part. -/
theorem GzInv.common {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) : GzCommon h i s := And.left inv

/-- Interface: the reader part. -/
theorem GzInv.reader {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_READ) :
    GzReadInv h i s := (And.right inv).1 hm

/-- Interface: the writer part. -/
theorem GzInv.writer {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm : s.mode = GZ_WRITE) :
    GzWriteInv h i s := (And.right inv).2 hm

/-- Interface: the record determines the state. -/
theorem GzInv.state_eq {h : Heap} {i : Nat} {s t : GzState} (inv : GzInv h i s) (ht : h.gzstates i = some t) :
    s = t := by
  have hs := inv.common.record
  rw [ht] at hs
  exact (Option.some.inj hs).symm

/-- Interface: the old lower bound of the position, `-(2·size) ≤ x.pos`, follows from `GzCommon.pos` (for a writer
`x.have = 0`, for a reader `x.have ≤ 2·size`). -/
theorem GzInv.pos_lower {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) :
    -(2 * s.size.toNat : Int) ≤ s.x.pos.toInt := by
  have hlo := inv.common.pos.2.2
  have hhave : s.x.have.toNat ≤ 2 * s.size.toNat := by
    rcases inv.common.mode with hm | hm
    · by_cases hz : s.x.have = 0
      · rw [hz]; exact Nat.zero_le _
      · obtain ⟨c, _, hle⟩ := (inv.reader hm).output hz
        omega
    · rw [(inv.writer hm).have0]; exact Nat.zero_le _
  omega

/-- Interface: with `strm.state = NULL` the codec owns no block. -/
theorem noCodec_owned {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s)
    (hn : s.strm.state = none) (b : Nat) : ¬ StreamOwned h (gzStrm i) b := by
  rintro ⟨z, hz, ⟨k, st, hk, _, _⟩ | ⟨k, d, hk, _, _⟩⟩
  all_goals
    simp [ZStreamRef.get, gzStrm, hs] at hz
    subst hz
    rw [hn] at hk
    cases hk

/-! ## Decision (4): the three `Uniq` are one predicate -/

/-- `Zlib.Gzlib.Spec.Uniq` and `Zlib.Inflate.Spec.Uniq` have the same body (one object per block number over the
same seven tables), so the codec histories embed with no conversion. -/
theorem gz_uniq_iff_inflate (h : Heap) : Zlib.Gzlib.Spec.Uniq h ↔ Zlib.Inflate.Spec.Uniq h := Iff.rfl

/-- The same for `Zlib.Deflate.Spec.Uniq`. -/
theorem gz_uniq_iff_deflate (h : Heap) : Zlib.Gzlib.Spec.Uniq h ↔ Zlib.Deflate.Spec.Uniq h := Iff.rfl

end ZlibF.Spec.Public
