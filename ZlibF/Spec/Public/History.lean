import ZlibF.Spec.Public.Lifecycle
import ZlibF.Spec.PlatformMemory

namespace ZlibF.Spec.Public
open C Zlib.GzFs

inductive StreamKind where
  | inflate | deflate
  deriving DecidableEq

/-- Ownership is read from the actual state graph, not chosen by a proof. -/
def StreamOwned (h : Heap) (r : ZStreamRef) (b : Nat) : Prop :=
  ∃ z, r.get h = some z ∧
    ((∃ i s, z.state = some (.inflate i) ∧ h.istates i = some s ∧ InflateOwned i s b) ∨
     (∃ i s, z.state = some (.deflate i) ∧ h.dstates i = some s ∧ DeflateOwned i s b))

def ByteRoot : BPtr → Nat → Prop
  | .ref (.blk i) _, b | .ref (.dstate_depth i) _, b => b = i
  | _, _ => False

def CallerRange (h : Heap) (r : ZStreamRef) (p : BPtr) (n : Nat) (write : Bool) : Prop :=
  p = .null ∨ ((∃ xs, Bytes h p n xs) ∧ (write = true → Writable h p n) ∧
    ∀ b, ByteRoot p b → ¬ StreamOwned h r b)

def StreamBuffers (h : Heap) (r : ZStreamRef) : Prop :=
  ∃ z, r.get h = some z ∧
    CallerRange h r z.next_in z.avail_in.toNat false ∧
    CallerRange h r z.next_out z.avail_out.toNat true ∧
    Separate z.next_in z.avail_in.toNat z.next_out z.avail_out.toNat

def CString (h : Heap) (p : BPtr) (xs : List UInt8) : Prop :=
  Bytes h p (xs.length + 1) (xs ++ [0]) ∧ 0 ∉ xs ∧ xs.length < 2 ^ 64

def HeaderMemory (h : Heap) (r : ZStreamRef) (p : GzHeaderPtr) (writing : Bool) : Prop :=
  p = none ∨ ∃ i g, p = some (.tab i) ∧ h.gzheaders i = some g ∧
    ¬ StreamOwned h r i ∧
    (g.extra ≠ .null → CallerRange h r g.extra
      (if writing then g.extra_max.toNat else g.extra_len.toNat) writing) ∧
    (g.name ≠ .null → if writing then CallerRange h r g.name g.name_max.toNat true
      else ∃ xs, CString h g.name xs) ∧
    (g.comment ≠ .null → if writing then CallerRange h r g.comment g.comm_max.toNat true
      else ∃ xs, CString h g.comment xs)

/-- The caller's gzip header still fits the part of it that `deflate` has already written:
the extra field, and the name or comment being written, are at least as long as the part
written (`gzindex`). zlib.h asks the caller to provide the header before the first `deflate`
call and to keep it valid; shortening it while it is being written makes the real C read
past the buffer (`tests/regression/deflate-history-domain`). Nor does it set the field being
written to `NULL` part-way: `deflate` then skips that field without resetting `gzindex`, and the
next string is read from `gzindex` on, past its end (`clear.c` in the same regression). -/
def DeflateHeaderProgress (h : Heap) (s : DeflateState) : Prop :=
  ∀ i g, s.gzhead = some (.tab i) → h.gzheaders i = some g →
    (s.status = EXTRA_STATE → g.extra ≠ .null → s.gzindex.toNat ≤ g.extra_len.toNat % 2 ^ 16) ∧
    (s.status = NAME_STATE → g.name ≠ .null → ∃ xs, CString h g.name xs ∧ s.gzindex.toNat ≤ xs.length) ∧
    (s.status = COMMENT_STATE → g.comment ≠ .null →
      ∃ xs, CString h g.comment xs ∧ s.gzindex.toNat ≤ xs.length) ∧
    (s.status = EXTRA_STATE → g.extra = .null → s.gzindex = 0) ∧
    (s.status = NAME_STATE → g.name = .null → s.gzindex = 0) ∧
    (s.status = COMMENT_STATE → g.comment = .null → s.gzindex = 0)

/-- `deflate` reads the caller's gzip header only while it writes it. -/
def DeflateHeaderWriting (s : DeflateState) : Prop :=
  s.status = GZIP_STATE ∨ s.status = EXTRA_STATE ∨ s.status = NAME_STATE ∨
    s.status = COMMENT_STATE ∨ s.status = HCRC_STATE

/-- A caller byte range: a pointer and a length. -/
abbrev CallerSpan := BPtr × Nat

/-- The caller ranges of a `deflate` call that writes an attached gzip header: the input, the
output, and the record's extra field (`extra_len mod 2^16` bytes), name and comment (each through
its NUL). A pointer that is `NULL` contributes an empty range. -/
def headerSpans (z : ZStream) (g : GzHeader) (name comment : List UInt8) : List CallerSpan :=
  [(z.next_in, z.avail_in.toNat), (z.next_out, z.avail_out.toNat),
    (g.extra, if g.extra = .null then 0 else g.extra_len.toNat % 2 ^ 16),
    (g.name, if g.name = .null then 0 else name.length + 1),
    (g.comment, if g.comment = .null then 0 else comment.length + 1)]

/-- **Caller regions of a header-writing `deflate` call.** While `deflate` writes an attached gzip
header (`GZIP_STATE` .. `HCRC_STATE`), the input, the output, the extra field, the name and the
comment are pairwise separate byte ranges (they may share a block), and the extra field, the name
and the comment lie outside the storage the stream owns. The name and comment ranges run through
the NUL of the `CString` that `HeaderMemory` asks for. These regions have no reason to overlap.
Two overlaps are undefined behaviour of the real C: a name in the output range, whose NUL a flush
overwrites, and a name in `pending_buf`, whose NUL a header byte overwrites; the name loop then
reads past the buffer (`tests/regression/deflate-gzip-name-output`). zlib.h does not say whether
these layouts are permitted (docs/deviations.md). -/
def DeflateHeaderApart (h : Heap) (r : ZStreamRef) (z : ZStream) (s : DeflateState) : Prop :=
  DeflateHeaderWriting s → ∀ i g, s.gzhead = some (.tab i) → h.gzheaders i = some g →
    ∀ name comment, (g.name ≠ .null → CString h g.name name) →
      (g.comment ≠ .null → CString h g.comment comment) →
      (List.Pairwise (fun a b : CallerSpan => Separate a.1 a.2 b.1 b.2) (headerSpans z g name comment)) ∧
      (∀ p ∈ [g.extra, g.name, g.comment], ∀ b, ByteRoot p b → ¬ StreamOwned h r b)

/-- While `inflate` reads a gzip header (`HEAD` .. `HCRC`) into an attached `gz_header`
record, the record's `extra` buffer (`extra_max` bytes) is separate from the unread input,
and in `EXTRA` the record's `extra_len` is not below the length still to read. EXTRA copies
with `zmemcpy(head->extra + extra_len - length, next, n)`: on the real C an overlapping
buffer is an overlapping `memcpy`, and a caller that lowers `extra_len` inside the extra
field makes the offset wrap and the copy write past `extra_max`
(`tests/regression/inflate-gzip-extra`). zlib.h does not say whether either layout is
permitted; this domain excludes both (docs/deviations.md). -/
def InflateHeaderProgress (h : Heap) (z : ZStream) (s : InflateState) : Prop :=
  HEAD ≤ s.mode → s.mode ≤ HCRC → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
    Separate g.extra g.extra_max.toNat z.next_in z.avail_in.toNat ∧
    (s.mode = EXTRA → s.length ≤ g.extra_len)

/-- The memory a call may read through the stream's header pointers. A deflate stream's gzip
header must be live while `deflate` writes it; afterwards the caller may release it. -/
def ActiveHeader (h : Heap) (r : ZStreamRef) : Prop :=
  ∃ z, r.get h = some z ∧
    (∀ i s, z.state = some (.inflate i) → h.istates i = some s →
      HeaderMemory h r s.head true ∧ InflateHeaderProgress h z s) ∧
    (∀ i s, z.state = some (.deflate i) → h.dstates i = some s →
      (DeflateHeaderWriting s → HeaderMemory h r s.gzhead false) ∧ DeflateHeaderProgress h s ∧
        DeflateHeaderApart h r z s)

/-- `deflateBound` reads a set gzip header at any time, so it must be live. -/
def DeflateHeaderLive (h : Heap) (r : ZStreamRef) : Prop :=
  ∃ z, r.get h = some z ∧
    ∀ i s, z.state = some (.deflate i) → h.dstates i = some s → HeaderMemory h r s.gzhead false

/-- No `deflate` call has started the stream since initialization or reset: the state is
still before its zlib or gzip header. zlib.h requires `deflatePrime` "before the first
deflate() call after a deflateInit2() or deflateReset()" and `deflateSetHeader` "before the
first call of deflate()". On the real C, primed bits after symbols were recorded overwrite
the symbol buffer that shares `pending_buf`, and the next block reads outside `_dist_code`;
a `NULL` header set while the header is being written is dereferenced
(`tests/regression/deflate-history-domain`). -/
def DeflateNotStarted (h : Heap) (r : ZStreamRef) : Prop :=
  ∃ z i s, r.get h = some z ∧ z.state = some (.deflate i) ∧ h.dstates i = some s ∧
    (s.status = INIT_STATE ∨ s.status = GZIP_STATE)

/-- Caller edits may replace input and output bindings and change unowned allocations.
They preserve the stream's control fields, private state, window and registered allocations. -/
def Rebuffer (h after : Heap) (r : ZStreamRef) : Prop :=
  Fresh after ∧ Zlib.Inflate.Spec.Uniq after ∧ LibraryGlobals after ∧
  Frame h after (fun b => ¬ StreamOwned h r b) ∧
  ∃ z z', r.get h = some z ∧ r.get after = some z' ∧
    z' = { z with
      next_in := z'.next_in, avail_in := z'.avail_in
      next_out := z'.next_out, avail_out := z'.avail_out }

/-- Exactly the public operations belonging to an existing stream. A direct call of
`deflateResetKeep` is not one: zlib.h lists it among the undocumented functions, and it keeps the
window and the hash tables while dropping the lookahead, after which the hash entries of the last
two positions are stale (`docs/findings/deflate-resetkeep-stale-hash`) and the deflate invariant
does not hold (`docs/deviations.md`). `deflateReset` (`deflateResetKeep`, then `lm_init`, which
clears the hash) stays. -/
def StreamOperation (kind : StreamKind) (r : ZStreamRef) : Call → Prop
  | .inflate p _ | .inflateReset p | .inflateReset2 p _ | .inflateResetKeep p
  | .inflatePrime p _ _ | .inflateGetDictionary p _ _ | .inflateSetDictionary p _ _
  | .inflateGetHeader p _ | .inflateSync p | .inflateSyncPoint p | .inflateMark p
  | .inflateCodesUsed p | .inflateValidate p _ | .inflateUndermine p _ =>
      kind = .inflate ∧ p = some r
  | .deflate p _ | .deflateReset p | .deflateParams p _ _
  | .deflatePrime p _ _ | .deflateGetDictionary p _ _ | .deflateSetDictionary p _ _
  | .deflateSetHeader p _ | .deflateTune p _ _ _ _ | .deflatePending p _ _
  | .deflateUsed p _ | .deflateBound p _ | .deflateBound_z p _ =>
      kind = .deflate ∧ p = some r
  | _ => False

def StreamArguments (h : Heap) (r : ZStreamRef) : Call → Prop
  | .inflate _ _ | .deflate _ _ | .deflateParams _ _ _ => StreamBuffers h r ∧ ActiveHeader h r
  | .inflateSync _ => ∃ z, r.get h = some z ∧
      (z.next_in = .null → z.avail_in = 0) ∧ CallerRange h r z.next_in z.avail_in.toNat false
  | .inflateSetDictionary _ p n | .deflateSetDictionary _ p n => CallerRange h r p n.toNat false
  | .inflateGetDictionary _ p _ => ∃ z i s,
      r.get h = some z ∧ z.state = some (.inflate i) ∧ h.istates i = some s ∧
      CallerRange h r p s.whave.toNat true
  | .deflateGetDictionary _ p _ => ∃ z i s,
      r.get h = some z ∧ z.state = some (.deflate i) ∧ h.dstates i = some s ∧
      CallerRange h r p (min s.w_size.toNat (s.strstart.toNat + s.lookahead.toNat)) true
  | .inflateGetHeader _ p => HeaderMemory h r p true ∧ p ≠ none
  | .deflateSetHeader _ p => HeaderMemory h r p false ∧ DeflateNotStarted h r
  | .deflateBound _ _ | .deflateBound_z _ _ => ActiveHeader h r ∧ DeflateHeaderLive h r
  | .deflatePrime _ _ _ => DeflateNotStarted h r
  | _ => True

/-- Actual successful histories, with no specification assumed for an earlier call.
For inflate streams, every heap on which a call runs and every heap a caller edit leaves
satisfies the LP64 object-size limit `ZlibF.PlatformMemory.ByteObjectsFit` (no object exceeds
`PTRDIFF_MAX`). This is a fact of the platform, not a duty of the caller; see
docs/deviations.md. The deflate side states it once its calls are shown to keep it.
The init targets separately prove that valid, non-failing initialisation produces such a history. -/
inductive StreamReachable : StreamKind → Heap → ZStreamRef → Prop
  | inflateInit {h after r z version wb} :
      Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → r.get h = some z →
      DefaultOrNull z → VersionValue h version (some 49) →
      C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) →
      StreamReachable .inflate after r
  | deflateInit {h after r z version level method wb mem strategy} :
      Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h → r.get h = some z →
      DefaultOrNull z → VersionValue h version (some 49) →
      C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h = .ok (Z_OK, after) →
      StreamReachable .deflate after r
  | rebuffer {kind h after r} : StreamReachable kind h r → Rebuffer h after r →
      (kind = .inflate → ZlibF.PlatformMemory.ByteObjectsFit after) → StreamReachable kind after r
  | step {kind h after r call value} : StreamReachable kind h r →
      (kind = .inflate → ZlibF.PlatformMemory.ByteObjectsFit h) →
      StreamOperation kind r call → StreamArguments h r call →
      call.execute default h = .ok ((value, default), after) → StreamReachable kind after r
  | inflateCopy {h after source dest z} : StreamReachable .inflate h source →
      source ≠ dest → dest.get h = some z →
      C.run (Zlib.Inflate.inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) →
      StreamReachable .inflate after dest
  | deflateCopy {h after source dest z} : StreamReachable .deflate h source →
      source ≠ dest → dest.get h = some z →
      C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h = .ok (Z_OK, after) →
      StreamReachable .deflate after dest

structure Region where
  pointer : BPtr
  length : Nat

def Region.covers (region : Region) (r : BRef) (i : Nat) : Prop :=
  ∃ off, region.pointer = .ref r off ∧ off ≤ i ∧ i < off + region.length

/-- Restore only the caller's byte-array fields, leaving all other fields available to the frame check. -/
def restoreRegions (before after : Heap) (regions : List Region) : Heap :=
  regions.foldl (fun current region => match region.pointer with
    | .null => current
    | .ref r _ => match Space.get before r with
      | none => current
      | some a => Space.put current r a) after

def BufferFrame (before after : Heap) (changed : Nat → Prop) (regions : List Region) : Prop :=
  Frame before (restoreRegions before after regions) changed ∧
  ∀ region, region ∈ regions → ∀ r off a,
    region.pointer = .ref r off → Space.get before r = some a →
    ∃ a', Space.get after r = some a' ∧ a'.size = a.size ∧
      ∀ j, j < a.size → (¬ ∃ region', region' ∈ regions ∧ region'.covers r j) → a'[j]? = a[j]?

def HeaderRegions (h : Heap) (head : GzHeaderPtr) : List Region :=
  match head with
  | none => []
  | some (.tab i) => match h.gzheaders i with
    | none => []
    | some g => [⟨g.extra, g.extra_max.toNat⟩, ⟨g.name, g.name_max.toNat⟩, ⟨g.comment, g.comm_max.toNat⟩]

end ZlibF.Spec.Public
