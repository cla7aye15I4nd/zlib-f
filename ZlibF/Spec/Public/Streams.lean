import ZlibF.Spec.Public.History
import ZlibF.Spec.PlatformMemory
import ZlibF.Spec.Public.Queries
import ZlibF.Spec.Public.Bits

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

def PendingBits (h : Heap) (s : DeflateState) (bits : List Bool) : Prop :=
  ∃ bytes, Bytes h s.pending_out s.pending.toNat bytes ∧
    bits = bytesToBits bytes ++ ((List.range s.bi_valid.toInt.toNat).map fun j =>
      decide (s.bi_buf.toNat / 2 ^ j % 2 = 1))

def heldSyncBytes (s : InflateState) : List UInt8 :=
  (List.range ((s.bits.toNat - s.bits.toNat % 8) / 8)).map fun j =>
    UInt8.ofNat (s.hold.toNat / 2 ^ (s.bits.toNat % 8 + 8 * j) % 256)

end ZlibF.Spec.Public
