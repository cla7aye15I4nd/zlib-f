import ZlibF.Spec.Public.History
import ZlibF.Spec.Api.Inflate
import ZlibF.Spec.PlatformMemory
import ZlibF.Spec.Public.Queries

namespace ZlibF.Spec.Public
open C ZlibF.Spec

def advance : BPtr → Nat → BPtr
  | .null, _ => .null
  | .ref r i, n => .ref r (i + n)

def StreamAccounting (z z' : ZStream) (used produced : Nat) : Prop :=
  used ≤ z.avail_in.toNat ∧ produced ≤ z.avail_out.toNat ∧
  z'.avail_in.toNat + used = z.avail_in.toNat ∧
  z'.avail_out.toNat + produced = z.avail_out.toNat ∧
  z'.next_in = advance z.next_in used ∧ z'.next_out = advance z.next_out produced ∧
  z'.state = z.state ∧ z'.zalloc = z.zalloc ∧ z'.zfree = z.zfree ∧
  z'.opaque = z.opaque ∧ z'.reserved = z.reserved

/-- `int inflate(z_streamp strm, int flush)`.
The domain is actual init/call history, not an arbitrary hand-built decoder state.
The selected LP64 platform scope explicitly requires every live represented
byte object to have at most PTRDIFF_MAX bytes (size < 2^63), including caller
storage from non-malloc origins. See docs/deviations.md.
Includes all signed flush arguments, progress, terminal/error modes, output bounds,
counter timing on late memory failure, caller frame and ownership of a new window.
`Z_STREAM_ERROR` is characterized exactly: a NULL output pointer, NULL input with
pending input, or a decoder left in `SYNC` by a failed `inflateSync`; such a call changes
neither the stream nor the decoder state. `Z_BUF_ERROR` means no progress, or an
unfinished `Z_FINISH` call. With input and output space available, and a flush other than
`Z_BLOCK`/`Z_TREES` (which may stop at a block boundary using only held bits), a call that
does not end, request a dictionary or fail makes progress.
The sequence target states format correctness across all input/output splits. -/
def Goal.inflate : Prop :=
  ∀ h r i z s flush,
    StreamReachable .inflate h r → Zlib.Inflate.Spec.Good h r i z s →
    ZlibF.PlatformMemory.ByteObjectsFit h →
    Zlib.Inflate.Spec.DefAlloc z → StreamBuffers h r → ActiveHeader h r →
    ∃ rc after z' s' used out,
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) ∧
      Zlib.Inflate.Spec.Good after r i z' s' ∧ StreamAccounting z z' used out.length ∧
      Bytes after z.next_out out.length out ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_STREAM_ERROR ∨
       rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_OK → (used ≠ 0 ∨ out ≠ []) ∧ flush ≠ Z_FINISH) ∧
      (rc = Z_STREAM_ERROR ↔
        z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC) ∧
      (rc = Z_STREAM_ERROR → z' = z ∧ s' = s ∧ used = 0 ∧ out = []) ∧
      (rc = Z_BUF_ERROR → (used = 0 ∧ out = []) ∨ flush = Z_FINISH) ∧
      (z.avail_in ≠ 0 → z.avail_out ≠ 0 → flush ≠ Z_BLOCK → flush ≠ Z_TREES →
        rc = Z_BUF_ERROR → used ≠ 0 ∨ out ≠ []) ∧
      (rc = Z_STREAM_END → s'.mode = DONE) ∧
      (rc = Z_NEED_DICT → s'.mode = DICT) ∧
      (rc = Z_DATA_ERROR → s'.mode = BAD) ∧
      (rc = Z_MEM_ERROR → s'.mode = MEM ∧ z'.total_in = z.total_in ∧ z'.total_out = z.total_out) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        z'.total_in = z.total_in + UInt64.ofNat used ∧
        z'.total_out = z.total_out + UInt64.ofNat out.length) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ InflateOwned i s b ∨ s.head = some (.tab b))
        (⟨z.next_out, out.length⟩ :: HeaderRegions h s.head) ∧
      LiveChange h after (fun b => InflateOwned i s' b ∧ ¬ h.live b) (fun _ => False)

/-- The order of flush values that `deflate` uses to detect a repeated flush:
`RANK(f) = f * 2 - (f > 4 ? 9 : 0)` (`deflate.c`), so `Z_BLOCK` ranks between
`Z_NO_FLUSH` and `Z_PARTIAL_FLUSH`. -/
def deflateRank (flush : Int32) : Int := flush.toInt * 2 - (if 4 < flush.toInt then 9 else 0)

/-- The calls that `deflate` refuses with `Z_STREAM_ERROR` (`zlib.h`): an invalid flush value,
no output buffer, no input buffer with pending input, or a flush other than `Z_FINISH` after
the first `Z_FINISH`. -/
def DeflateRefuses (z : ZStream) (s : DeflateState) (flush : Int32) : Prop :=
  flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
  (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (s.status = FINISH_STATE ∧ flush ≠ Z_FINISH)

/-- `int deflate(z_streamp strm, int flush)`.
Preserve the live stream and its five allocations. Account for exactly the bytes accepted
and delivered, including progress on a full output buffer and clean parameter refusals.
`Z_BUF_ERROR` is characterized exactly (`zlib.h`: no progress was possible): no output space;
or no input, nothing pending and a flush that repeats or weakens the previous one, other than
`Z_FINISH`; or new input after the first `Z_FINISH`. Only in the last case can the call still
deliver pending output before it refuses. A `Z_FINISH` call with output space, no new input
after the first `Z_FINISH`, and no refusal, ends the stream or makes progress. Success keeps
`msg`; an error sets it to the error's text. `data_type` changes only from `Z_UNKNOWN` to a guess.
The sequence target states valid encoding, flush points and completion. -/
def Goal.deflate : Prop :=
  ∀ h r i z s flush,
    StreamReachable .deflate h r → Zlib.Deflate.Spec.DGood h r i z s →
    StreamBuffers h r → ActiveHeader h r →
    ∃ rc after z' s' used out,
      C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
      Zlib.Deflate.Spec.DGood after r i z' s' ∧ StreamAccounting z z' used out.length ∧
      Bytes after z.next_out out.length out ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat out.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_STREAM_ERROR ↔ DeflateRefuses z s flush) ∧
      (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
      (rc = Z_STREAM_END → flush = Z_FINISH ∧ s'.status = FINISH_STATE ∧
        z'.avail_in = 0 ∧ s'.pending = 0 ∧ s'.bi_valid = 0) ∧
      (rc = Z_BUF_ERROR → used = 0 ∧
        (out = [] ∨ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0))) ∧
      (¬ DeflateRefuses z s flush → z.avail_out = 0 → rc = Z_BUF_ERROR) ∧
      (¬ DeflateRefuses z s flush → z.avail_out ≠ 0 →
        ¬ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
        (rc = Z_BUF_ERROR ↔ z.avail_in = 0 ∧ s.pending = 0 ∧ flush ≠ Z_FINISH ∧
          deflateRank flush ≤ deflateRank s.last_flush)) ∧
      (flush = Z_FINISH → ¬ DeflateRefuses z s flush → z.avail_out ≠ 0 →
        ¬ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
        rc = Z_STREAM_END ∨ used ≠ 0 ∨ out ≠ []) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END → z'.msg = z.msg) ∧
      (rc = Z_BUF_ERROR → StaticString after z'.msg (errorText Z_BUF_ERROR.toInt)) ∧
      (rc = Z_STREAM_ERROR → 0 ≤ flush.toInt → flush.toInt ≤ 5 →
        StaticString after z'.msg (errorText Z_STREAM_ERROR.toInt)) ∧
      (z'.data_type = z.data_type ∨
        (z.data_type = Z_UNKNOWN ∧ (z'.data_type = Z_BINARY ∨ z'.data_type = Z_TEXT))) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) [⟨z.next_out, out.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc

def bound64 (n : Nat) : UInt64 := UInt64.ofNat (min n (2 ^ 64 - 1))

def WrapperLength (h : Heap) (s : DeflateState) (n : Nat) : Prop :=
  (s.wrap = 0 ∧ n = 0) ∨
  ((s.wrap = 1 ∨ s.wrap = -1) ∧ n = 6 + if s.strstart = 0 then 0 else 4) ∨
  ((s.wrap = 2 ∨ s.wrap = -2) ∧
    ((s.gzhead = none ∧ n = 18) ∨ ∃ g gh name comment,
      s.gzhead = some (.tab g) ∧ h.gzheaders g = some gh ∧
      (gh.name = .null ∧ name = [] ∨ CString h gh.name name) ∧
      (gh.comment = .null ∧ comment = [] ∨ CString h gh.comment comment) ∧
      n = 18 + (if gh.extra = .null then 0 else 2 + gh.extra_len.toNat) +
        (if gh.name = .null then 0 else name.length + 1) +
        (if gh.comment = .null then 0 else comment.length + 1) +
        (if gh.hcrc = 0 then 0 else 2)))

def deflateBoundValue (s : DeflateState) (wrapper n : Nat) : UInt64 :=
  if s.w_bits = 15 ∧ s.hash_bits = 15 then
    bound64 (n + n / 4096 + n / 16384 + n / 33554432 + 7 + wrapper)
  else if s.w_bits ≤ s.hash_bits ∧ s.level ≠ 0 then
    bound64 (n + n / 8 + n / 256 + n / 512 + 4 + wrapper)
  else bound64 (n + n / 32 + n / 128 + n / 2048 + 7 + wrapper)

def DeflateBoundContract (program : ZStreamPtr → UInt64 → M UInt64) : Prop :=
  (∀ h n, C.run (program none n) h = .ok
    (bound64 (max (n.toNat + n.toNat / 8 + n.toNat / 256 + n.toNat / 512 + 4)
      (n.toNat + n.toNat / 32 + n.toNat / 128 + n.toNat / 2048 + 7) + 18), h)) ∧
  (∀ h r i z s wrapper n,
    Zlib.Deflate.Spec.DGood h r i z s → WrapperLength h s wrapper →
    C.run (program (some r) n) h = .ok (deflateBoundValue s wrapper n.toNat, h))

/-- `z_size_t deflateBound_z(z_streamp strm, z_size_t sourceLen)`.
The mathematical bound includes the entire gzip header, with saturation instead of overflow.
The known extra-length arithmetic issue remains an implementation proof blocker. -/
def Goal.deflateBound_z : Prop := DeflateBoundContract Zlib.Deflate.deflateBound_z

/-- `uLong deflateBound(z_streamp strm, uLong sourceLen)`.
The LP64 wrapper has the same numeric range; other ABIs need a conversion contract. -/
def Goal.deflateBound : Prop := DeflateBoundContract Zlib.Deflate.deflateBound

def PendingBits (h : Heap) (s : DeflateState) (bits : List Bool) : Prop :=
  ∃ bytes, Bytes h s.pending_out s.pending.toNat bytes ∧
    bits = bytesToBits bytes ++ ((List.range s.bi_valid.toInt.toNat).map fun j =>
      decide (s.bi_buf.toNat / 2 ^ j % 2 = 1))

/-- `int deflatePrime(z_streamp strm, int bits, int value)`.
Append the requested low bits in transmission order. Compaction can occur before a buffer
error; invalid bit counts are refused before compaction. No allocation occurs. -/
def Goal.deflatePrime : Prop :=
  ∀ h r i z s count value old,
    Zlib.Deflate.Spec.DGood h r i z s → PendingBits h s old →
    ∃ rc after s', C.run (Zlib.Deflate.deflatePrime (some r) count value) h = .ok (rc, after) ∧
      Zlib.Deflate.Spec.DGood after r i z s' ∧
      (count.toInt < 0 ∨ 16 < count.toInt → rc = Z_BUF_ERROR ∧ after = h) ∧
      (0 ≤ count.toInt → count.toInt ≤ 16 →
        s'.pending_out = s'.pending_buf ∧
        if s.pending_buf_size.toNat - s.pending.toNat < (s.bi_valid.toInt.toNat + count.toInt.toNat) / 8 then
          rc = Z_BUF_ERROR ∧ PendingBits after s' old
        else rc = Z_OK ∧ PendingBits after s'
          (old ++ (List.range count.toInt.toNat).map (fun j => decide (value.toUInt32.toNat / 2 ^ j % 2 = 1)))) ∧
      Frame h after (DeflateOwned i s) ∧ LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc

/-- `int deflateParams(z_streamp strm, int level, int strategy)`.
May consume input and write output while finishing the old block. A buffer error retains
the old parameters; successful changes select the canonical tuning row for a changed level. -/
def Goal.deflateParams : Prop :=
  ∀ h r i z s level strategy,
    StreamReachable .deflate h r → Zlib.Deflate.Spec.DGood h r i z s →
    StreamBuffers h r → ActiveHeader h r →
    ∃ rc after z' s' used out,
      C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after) ∧
      Zlib.Deflate.Spec.DGood after r i z' s' ∧ StreamAccounting z z' used out.length ∧
      Bytes after z.next_out out.length out ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_STREAM_ERROR) ∧
      (rc = Z_OK → s'.level = (if level = -1 then 6 else level) ∧ s'.strategy = strategy) ∧
      (rc ≠ Z_OK → s'.level = s.level ∧ s'.strategy = s.strategy) ∧
      ((level.toInt < -1 ∨ 9 < level.toInt ∨ strategy.toInt < 0 ∨ 4 < strategy.toInt) →
        rc = Z_STREAM_ERROR ∧ after = h) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) [⟨z.next_out, out.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc

def heldSyncBytes (s : InflateState) : List UInt8 :=
  (List.range ((s.bits.toNat - s.bits.toNat % 8) / 8)).map fun j =>
    UInt8.ofNat (s.hold.toNat / 2 ^ (s.bits.toNat % 8 + 8 * j) % 256)

/-- `int inflateSync(z_streamp strm)`.
Search byte-aligned held bits before new input, retaining the partial marker match.
On success retain totals and restart at TYPE with validation disabled. -/
def Goal.inflateSync : Prop :=
  ∀ h r i z s input,
    StreamReachable .inflate h r → Zlib.Inflate.Spec.Good h r i z s →
    Zlib.Inflate.Spec.DefAlloc z → Bytes h z.next_in z.avail_in.toNat input →
    ∃ rc after z' s' used,
      C.run (Zlib.Inflate.inflateSync (some r)) h = .ok (rc, after) ∧
      Zlib.Inflate.Spec.Good after r i z' s' ∧ used ≤ input.length ∧
      z'.next_in = advance z.next_in used ∧ z'.avail_in.toNat + used = z.avail_in.toNat ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out ∧
      (if z.avail_in = 0 ∧ s.bits.toNat < 8 then rc = Z_BUF_ERROR ∧ z' = z ∧ s' = s
       else let start := if s.mode = SYNC then s.have.toNat else
              (Api.syncSearch 0 (heldSyncBytes s)).1
            let found := Api.syncSearch start input
            used = found.2 ∧
            if found.1 = 4 then rc = Z_OK ∧ s'.mode = TYPE ∧ (s'.wrap &&& 4) = 0
            else rc = Z_DATA_ERROR ∧ s'.mode = SYNC ∧ s'.have.toNat = found.1) ∧
      Frame h after (fun b => StreamRoot r b ∨ InflateOwned i s b) ∧
      LiveChange h after (fun _ => False)
        (fun b => InflateOwned i s b ∧ ¬ InflateOwned i s' b)

end ZlibF.Spec.Public
