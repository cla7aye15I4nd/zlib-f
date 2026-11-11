import ZlibF.Spec.Public.Lifecycle

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
past the buffer (`tests/regression/deflate-history-domain`). -/
def DeflateHeaderProgress (h : Heap) (s : DeflateState) : Prop :=
  ∀ i g, s.gzhead = some (.tab i) → h.gzheaders i = some g →
    (s.status = EXTRA_STATE → g.extra ≠ .null → s.gzindex.toNat ≤ g.extra_len.toNat % 2 ^ 16) ∧
    (s.status = NAME_STATE → g.name ≠ .null → ∃ xs, CString h g.name xs ∧ s.gzindex.toNat ≤ xs.length) ∧
    (s.status = COMMENT_STATE → g.comment ≠ .null →
      ∃ xs, CString h g.comment xs ∧ s.gzindex.toNat ≤ xs.length)

def ActiveHeader (h : Heap) (r : ZStreamRef) : Prop :=
  ∃ z, r.get h = some z ∧
    (∀ i s, z.state = some (.inflate i) → h.istates i = some s → HeaderMemory h r s.head true) ∧
    (∀ i s, z.state = some (.deflate i) → h.dstates i = some s →
      HeaderMemory h r s.gzhead false ∧ DeflateHeaderProgress h s)

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

/-- Exactly the public operations belonging to an existing stream. -/
def StreamOperation (kind : StreamKind) (r : ZStreamRef) : Call → Prop
  | .inflate p _ | .inflateReset p | .inflateReset2 p _ | .inflateResetKeep p
  | .inflatePrime p _ _ | .inflateGetDictionary p _ _ | .inflateSetDictionary p _ _
  | .inflateGetHeader p _ | .inflateSync p | .inflateSyncPoint p | .inflateMark p
  | .inflateCodesUsed p | .inflateValidate p _ | .inflateUndermine p _ =>
      kind = .inflate ∧ p = some r
  | .deflate p _ | .deflateReset p | .deflateResetKeep p | .deflateParams p _ _
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
  | .deflateBound _ _ | .deflateBound_z _ _ => ActiveHeader h r
  | .deflatePrime _ _ _ => DeflateNotStarted h r
  | _ => True

/-- Actual successful histories, with no specification assumed for an earlier call.
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
      StreamReachable kind after r
  | step {kind h after r call value} : StreamReachable kind h r →
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
