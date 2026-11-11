import ZlibF.Proof.«inflate.c.gzip-header-state»
import ZlibF.Proof.«inflate.c.block-type»

/-!
# inflate.c: a gzip header dispatch under the default relation

Lifts one dispatch from a gzip header mode (`FLAGS` .. `HCRC`) to
`DefaultStateJ`, and carries the per-call facts the gzip header modes need
(`GzipDispatchLocal`) to the next dispatch while the decoder stays in a
header mode.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Each caller region the header record names after a step is the region
it named before, or its pointer was set to `Z_NULL` (the header has no extra
field, name or comment), with the same maximum length. -/
def RegionsKept : List Region → List Region → Prop
  | [], [] => True
  | a :: after, b :: before =>
    (a = b ∨ (a.pointer = .null ∧ a.length = b.length)) ∧ RegionsKept after before
  | _, _ => False

/-- The per-call facts a dispatch in `HEAD` .. `HCRC` uses besides the
representation: the local `hbuf`, its separation from the header record's
caller regions, the header record, the `extra` buffer apart from the unread
input, and, in `EXTRA`, the extra length still the one `EXLEN` stored. -/
structure GzipDispatchLocal (c : Ctx) (h : Heap) (r : ZStreamRef) (s : InflateState) (l : IL) : Prop where
  hbuf : LocalHbuf c h
  apart : HbufApart c h s.head
  record : HeaderMemory h r s.head true
  extraApart : ExtraApart h s.head l
  extraLen : s.mode = EXTRA → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
    s.length ≤ g.extra_len

/-- WORKER STUB: batch 2 proves this statement (skeleton/inflate). -/
theorem inflate_dispatch_gzip_header_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (hbuf : LocalHbuf c h) (apart : HbufApart c h s.head)
    (record : HeaderMemory h r s.head true) (globals : LibraryGlobals h)
    (extraApart : ExtraApart h s.head l)
    (extraLen : s.mode = EXTRA → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
      s.length ≤ g.extra_len)
    (mode : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) (gzip : GzipAllowed s.wrap)
    (flags : FLAGS < s.mode → s.flags ≠ -1 ∧ s.flags ≠ 0)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataPendingInvariant state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ regs.bits.toNat ≤ 39 ∧
      after.static = h.static ∧ LocalHbuf c after ∧ HbufApart c after state.head ∧
      GzipHeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧
      GzipHeaderFootprint c r zs s h after ∧ HeaderMemory after r state.head true ∧
      RegionsKept (HeaderRegions after state.head) (HeaderRegions h s.head) ∧
      (state.mode = EXTRA → ∀ i g, state.head = some (.tab i) → after.gzheaders i = some g →
        state.length ≤ g.extra_len) ∧
      ((FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨ state.mode = TYPE ∨ state.mode = BAD) ∧
      (state.mode ≠ BAD → state.mode ≠ FLAGS → state.flags ≠ -1 ∧ state.flags ≠ 0) ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  sorry

end Zlib.Inflate.Proofs
