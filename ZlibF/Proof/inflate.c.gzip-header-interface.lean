import ZlibF.Proof.«inflate.c.call-default»

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

/-- The local `unsigned char hbuf[4]` of `inflate()`: a writable four-byte array. -/
def LocalHbuf (c : Ctx) (h : Heap) : Prop :=
  ∃ b a, c.hbuf = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ a.size = 4 ∧ h.ro b = false

/-- The state fields the gzip header modes may write. -/
def GzipHeaderStateFrame (before after : InflateState) : Prop :=
  after = { before with
    mode := after.mode
    flags := after.flags
    check := after.check
    length := after.length }

/-- The heap footprint of one gzip header dispatch: the stream and state
records, the local array, the attached header record, and the caller
regions that record names; no allocation or release. -/
def GzipHeaderFootprint (c : Ctx) (r : ZStreamRef) (zs : Nat) (s : InflateState)
    (h after : Heap) : Prop :=
  BufferFrame h after
      (fun b => StreamRoot r b ∨ b = zs ∨ c.hbuf = .ref (.blk b) 0 ∨ s.head = some (.tab b))
      (HeaderRegions h s.head) ∧
    LiveChange h after (fun _ => False) (fun _ => False)

/-- One dispatch from a gzip header mode returns, keeps the representation,
the caller packet and the header record, writes only the gzip header fields
and its footprint, and either leaves or decreases the dispatch rank. A
completed header (HCRC done) is in `TYPE`; past `FLAGS` the gzip flags are read
(nonzero, since the method byte is 8). -/
theorem inflate_dispatch_gzip_header_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (hbuf : LocalHbuf c h)
    (record : HeaderMemory h r s.head true)
    (mode : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) (gzip : GzipAllowed s.wrap)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ regs.bits.toNat ≤ 39 ∧
      after.static = h.static ∧ LocalHbuf c after ∧
      GzipHeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧
      GzipHeaderFootprint c r zs s h after ∧ HeaderMemory after r state.head true ∧
      ((FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨ state.mode = TYPE ∨ state.mode = BAD) ∧
      (state.mode ≠ BAD → state.mode ≠ FLAGS → state.flags ≠ -1 ∧ state.flags ≠ 0) ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  sorry

end Zlib.Inflate.Proofs
