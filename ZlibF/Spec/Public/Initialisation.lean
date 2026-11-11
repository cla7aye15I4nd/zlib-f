import ZlibF.Spec.Api.Basic
import ZlibF.Spec.Public.StreamQueries
import ZlibF.Proof.«inflate.c.base»
import ZlibF.Proof.«deflate.c.base»

namespace ZlibF.Spec.Public
open C

/-- A frame over existing allocations. New allocations are governed separately by `LiveChange`. -/
def Frame (before after : Heap) (changed : Nat → Prop) : Prop :=
  before.static = after.static ∧ before.allocOk = after.allocOk ∧ before.garbage = after.garbage ∧
  before.nextBlk ≤ after.nextBlk ∧ before.nalloc ≤ after.nalloc ∧
  ∀ b, before.live b → ¬ changed b →
    after.bytes b = before.bytes b ∧ after.words b = before.words b ∧
    after.streams b = before.streams b ∧ after.gzheaders b = before.gzheaders b ∧
    after.dstates b = before.dstates b ∧ after.istates b = before.istates b ∧
    after.gzstates b = before.gzstates b ∧ after.ro b = before.ro b

/-- An exact allocation ledger. A live allocation cannot disappear or remain unaccounted for. -/
def LiveChange (before after : Heap) (created removed : Nat → Prop) : Prop :=
  ∀ b, after.live b ↔ (before.live b ∧ ¬ removed b) ∨ created b

def StreamRoot (r : ZStreamRef) (b : Nat) : Prop :=
  match r with | .tab i | .in_gzstate_strm i => b = i

def InflateOwned (i : Nat) (s : InflateState) (b : Nat) : Prop :=
  b = i ∨ s.window = .ref (.blk b) 0

def DeflateOwned (i : Nat) (s : DeflateState) (b : Nat) : Prop :=
  b = i ∨ s.window = .ref (.blk b) 0 ∨ s.prev = .ref (.blk b) 0 ∨
  s.head = .ref (.blk b) 0 ∨ s.pending_buf = .ref (.blk b) 0

def DefaultOrNull (z : ZStream) : Prop :=
  (z.zalloc = .null ∨ z.zalloc = .fn "zcalloc") ∧
  (z.zfree = .null ∨ z.zfree = .fn "zcfree")

def preparedStream (z : ZStream) : ZStream :=
  { z with
    msg := .null
    zalloc := if z.zalloc == .null then .fn "zcalloc" else z.zalloc
    «opaque» := if z.zalloc == .null then .null else z.opaque
    zfree := if z.zfree == .null then .fn "zcfree" else z.zfree }

/-- The version check reads only the first byte; the null version is a clean error. -/
def VersionValue (h : Heap) (p : BPtr) (head : Option UInt8) : Prop :=
  (p = .null ∧ head = none) ∨ ∃ b, head = some b ∧ Bytes h p 1 [b]

def WindowAllocation (h : Heap) (p : BPtr) : Prop :=
  p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false

/-- Remove a writable byte allocation. Read-only metadata, including its table shape, is
unchanged. Callers establish WindowAllocation or the corresponding owned-message condition. -/
def dropWindow (h : Heap) : BPtr → Heap
  | .ref (.blk b) 0 => { h with bytes := upd h.bytes b none }
  | _ => h

/-- Init's successful representation includes the complete established invariant, not an
invariant supplied by the caller. The single allocation is the new state record. -/
def InflateInitial (before after : Heap) (r : ZStreamRef) (wrap : Api.Wrap) (bits : Nat) : Prop :=
  ∃ z s, Zlib.Inflate.Spec.Good after r before.nextBlk z s ∧
    z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree" ∧
    s.mode = HEAD ∧ s.window = .null ∧ s.wbits.toNat = bits ∧ s.reqbits.toNat = bits ∧
    s.wrap = (match wrap with | .raw => 0 | .zlib => 5 | .gzip => 6 | .auto => 7) ∧
    s.reqwrap = s.wrap ∧ s.wsize = 0 ∧ s.whave = 0 ∧ s.wnext = 0 ∧
    s.hold = 0 ∧ s.bits = 0 ∧ s.havedict = 0 ∧ s.head = none ∧
    z.total_in = 0 ∧ z.total_out = 0 ∧ z.msg = .null ∧
    Frame before after (StreamRoot r) ∧
    LiveChange before after (fun b => b = before.nextBlk) (fun _ => False)

/-- Allocation precedes the window-bit check in inflate init. In particular, an invalid
window configuration can return `Z_MEM_ERROR` before it returns `Z_STREAM_ERROR`.
An invalid window argument allocates the state and frees it again. The state table may then
be longer than before, with an empty entry, so that branch compares tables entry by entry. -/
def InflateInitContract (program : ZStreamPtr → BPtr → Int32 → M Int32) (wb : Int32) : Prop :=
  (∀ h p version head size, VersionValue h version head →
    (head ≠ some 49 ∨ size ≠ 112) → C.run (program p version size) h = .ok (Z_VERSION_ERROR, h)) ∧
  (∀ h version, VersionValue h version (some 49) →
    C.run (program none version 112) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z version, Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h →
    r.get h = some z → DefaultOrNull z → VersionValue h version (some 49) →
    ∃ rc after, C.run (program (some r) version 112) h = .ok (rc, after) ∧
      after.nalloc = h.nalloc + 1 ∧
      (if h.allocOk h.nalloc = false then
        rc = Z_MEM_ERROR ∧ SameObjects (r.put h (preparedStream z)) after
      else match Api.inflWbits wb.toInt with
      | none => rc = Z_STREAM_ERROR ∧
          SameObjectsUpToTableShape (r.put h { preparedStream z with state := none }) after
      | some (wrap, bits) => rc = Z_OK ∧ InflateInitial h after r wrap bits))

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
All signed window arguments and every allocation oracle are included, in source error order. -/
def Goal.inflateInit2_ : Prop :=
  ∀ wb, InflateInitContract (fun p v size => Zlib.Inflate.inflateInit2_ p wb v size) wb

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
The same version, stream, allocation, cleanup and invariant contract at window bits 15. -/
def Goal.inflateInit_ : Prop := InflateInitContract Zlib.Inflate.inflateInit_ 15

def DeflateInitial (before after : Heap) (r : ZStreamRef) (p : Api.DeflParams) : Prop :=
  ∃ z s, Zlib.Deflate.Spec.DGood after r before.nextBlk z s ∧
    z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree" ∧
    s.level.toInt = p.level ∧ s.strategy.toInt = p.strategy ∧ s.w_bits.toNat = p.wbits ∧
    s.hash_bits.toNat = p.memLevel + 7 ∧
    s.wrap = (match p.wrap with | .raw => 0 | .zlib => 1 | .gzip => 2) ∧
    s.strstart = 0 ∧ s.lookahead = 0 ∧ s.pending = 0 ∧ s.bi_valid = 0 ∧ s.gzhead = none ∧
    z.total_in = 0 ∧ z.total_out = 0 ∧ z.msg = .null ∧
    Frame before after (StreamRoot r) ∧
    LiveChange before after (DeflateOwned before.nextBlk s) (fun _ => False) ∧
    (∀ b, DeflateOwned before.nextBlk s b ↔ before.nextBlk ≤ b ∧ b < before.nextBlk + 5)

/-- Deflate validates parameters before allocating. Once the state allocation succeeds it
attempts all four buffer allocations, even when an earlier buffer allocation failed. -/
def DeflateInitContract (program : ZStreamPtr → BPtr → Int32 → M Int32)
    (level method wb mem strategy : Int32) : Prop :=
  (∀ h p version head size, VersionValue h version head →
    (head ≠ some 49 ∨ size ≠ 112) → C.run (program p version size) h = .ok (Z_VERSION_ERROR, h)) ∧
  (∀ h version, VersionValue h version (some 49) →
    C.run (program none version 112) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z version, Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h →
    r.get h = some z → DefaultOrNull z → VersionValue h version (some 49) →
    ∃ rc after, C.run (program (some r) version 112) h = .ok (rc, after) ∧
      (match Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
      | none => rc = Z_STREAM_ERROR ∧ SameObjects (r.put h (preparedStream z)) after ∧
          after.nalloc = h.nalloc
      | some p =>
        if h.allocOk h.nalloc = false then
          rc = Z_MEM_ERROR ∧ after.nalloc = h.nalloc + 1 ∧
          SameObjects (r.put h (preparedStream z)) after
        else after.nalloc = h.nalloc + 5 ∧
          if (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) then
            rc = Z_OK ∧ DeflateInitial h after r p
          else rc = Z_MEM_ERROR ∧
            (∃ z', r.get after = some z' ∧ z'.state = none) ∧
            LiveChange h after (fun _ => False) (fun _ => False) ∧
            Frame h after (StreamRoot r)))

/-- `int deflateInit2_(z_streamp strm, int level, int method, int windowBits, int memLevel,
int strategy, const char *version, int stream_size)`.
Every signed argument, source-ordered refusal, five allocations, failure cleanup and success invariant. -/
def Goal.deflateInit2_ : Prop :=
  ∀ level method wb mem strategy,
    DeflateInitContract (fun p v size => Zlib.Deflate.deflateInit2_ p level method wb mem strategy v size)
      level method wb mem strategy

/-- `int deflateInit_(z_streamp strm, int level, const char *version, int stream_size)`.
The default method, window, memory level and strategy; the level remains arbitrary. -/
def Goal.deflateInit_ : Prop :=
  ∀ level, DeflateInitContract (fun p v size => Zlib.Deflate.deflateInit_ p level v size)
    level 8 15 8 0

end ZlibF.Spec.Public
