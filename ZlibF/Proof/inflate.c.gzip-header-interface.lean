import ZlibF.Proof.«inflate.c.gzip-header-state»

/-!
# inflate.c: the gzip header modes, interface (skeleton)

One dispatch from a gzip header mode (`FLAGS` .. `HCRC`) under the
representation invariant. Batch 2 proves `inflate_dispatch_gzip_header_rank`;
batch 4 lifts it to the default relation. The statement does not mention
`DefaultStateJ`: it fixes only the run, the representation, the caller
packet, the fields the modes write, the heap footprint (stream and state
records, the local `hbuf` array, the attached header record and the caller
regions it names) and the dispatch rank.
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

/-- One dispatch from a gzip header mode returns, keeps the representation,
the caller packet and the header record, writes only the gzip header fields
and its footprint, and either leaves or decreases the dispatch rank. A
completed header (HCRC done) is in `TYPE`; past `FLAGS` the gzip flags are read
(nonzero, since the method byte is 8). The header record's buffers may
overlap the unread input (zlib.h does not forbid it), so only the length of
the remaining input is fixed, not its bytes. -/
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
      (state.flags = s.flags ∨ (0 ≤ state.flags.toInt ∧ state.flags.toInt < 65536)) ∧
      (outcome = .error Ex.leave → regs.have_ = 0) ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  sorry

end Zlib.Inflate.Proofs
