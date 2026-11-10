import ZlibF.Proof.«inflate.c.fast-arbitrary-ready-body»
import ZlibF.Proof.«inflate.c.token-suffix-cancel»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy
set_option autoImplicit false
/-- An actual per-body causal event retains all physical cursor, heap and
output facts, while recording only held bits and actually pulled bytes. -/
def CausalBodyResult (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (c : Zlib.Inffast.Ctx) (slow : IL) (fast : Zlib.Inffast.L) (bs dict : List UInt8)
    (L D : List Nat) (dest : BRef) (output : Array UInt8) (j bg : Nat) : Prop :=
  ∃ used result after finalSlow array,
    used ≤ 7 ∧ used ≤ bs.length ∧
    result.in_ = inputAdvance fast.in_ used ∧
    C.run (Zlib.Inffast.inflate_fast_body c fast) h = .ok (result, after) ∧
    FastInputPacket after finalSlow (bs.drop used) result ∧ DispatchBuffers after r finalSlow (bs.drop used) ∧
    Space.get after dest = some array ∧
    ((∃ made, made ≤ 258 ∧ after = Space.put h dest array ∧ result.out = .ref dest (j + made) ∧ DefaultStateJ after r zs z s ∧
        Token.Step L D dict (writtenBytes output j (j - bg)) (natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (bs.take used))
          (natBits finalSlow.bits.toNat finalSlow.hold.toNat) (writtenBytes array (j + made) ((j - bg) + made)) false) ∨
     (after = setI h zs {s with mode := TYPE} ∧ result.broke = true ∧
        result.out = .ref dest j ∧ array = output ∧ DefaultStateJ after r zs z {s with mode := TYPE} ∧
        Token.Step L D dict (writtenBytes output j (j - bg)) (natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (bs.take used))
          (natBits finalSlow.bits.toNat finalSlow.hold.toNat) (writtenBytes output j (j - bg)) true) ∨
     (∃ i, after = badHeap h r zs z s i ∧ result.broke = true ∧ result.out = .ref dest j ∧ array = output ∧
        DefaultStateJ after r zs {z with msg := .ref (.str i) 0} {s with mode := BAD}))

/-- Exact used-byte accounting cancels every untouched input byte from the
accepted token. The caller may replace those untouched bytes on rebuffer. -/
theorem BodyResult.held
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {slow : IL} {fast : Zlib.Inffast.L} {bs dict : List UInt8}
    {L D : List Nat} {dest : BRef} {output : Array UInt8} {j bg : Nat}
    (result : BodyResult h r zs z s c slow fast bs dict L D dest output j bg)
    (lengths : Acceptable .litLen L) (distances : Acceptable .dist D) :
    CausalBodyResult h r zs z s c slow fast bs dict L D dest output j bg := by
  obtain ⟨used, regs, after, finalSlow, array, usedBound, raw, cursor, actual, packet, buffers, get, event⟩ := result
  refine ⟨used, regs, after, finalSlow, array, usedBound, raw, cursor, actual, packet, buffers, get, ?_⟩
  rcases event with ⟨made, madeBound, heap, out, current, token⟩ | eob | bad
  · exact Or.inl ⟨made, madeBound, heap, out, current,
      SlowReverseToken.token_step_held_raw_prefix lengths distances token⟩
  · obtain ⟨heap, broke, out, same, current, token⟩ := eob
    exact Or.inr (Or.inl ⟨heap, broke, out, same, current,
      SlowReverseToken.token_step_held_raw_prefix lengths distances token⟩)
  · exact Or.inr (Or.inr bad)

/-- Whole actual generic body classification, with untouched caller input
removed from the semantic event. No valid-source hypothesis is added. -/
theorem fast_body_arbitrary_causal
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref dref : CodeRef} {codes dcodes : Array Code}
    {offset root extent doff droot dextent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs dict : List UInt8}
    (packet : FastInputPacket h slow bs fast) (buffers : DispatchBuffers h r slow bs)
    (margin : 6 ≤ slow.have_.toNat) (bits : slow.bits.toNat ≤ 30)
    (lptr : c.lcode = .ref ref offset) (lsafe : LenTableSafe codes offset root)
    (lmask : c.lmask.toUInt64.toNat = 2 ^ root - 1)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (inv : Inv LENS codes offset root extent L)
    (flags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS codes offset root)
    (stable : StableQuery LENS codes offset root)
    (dptr : c.dcode = .ref dref doff) (dget : Space.get h dref = some dcodes)
    (dsafe : DistTableSafe dcodes doff droot) (dmask : c.dmask.toUInt64.toNat = 2 ^ droot - 1)
    (dinv : Inv DISTS dcodes doff droot dextent D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS dcodes doff droot)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (whave : c.whave.toNat ≤ c.wsize.toNat) (wnext : c.wnext.toNat ≤ c.wsize.toNat) (wsize : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output saved : Array UInt8} {oo bg j woff : Nat}
    (outPtr : fast.out = .ref dest j) (put : slow.put = .ref dest oo) (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (size : oo + slow.left.toNat ≤ output.size) (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt fast.out c.end_) h = .ok (true, h))
    (windowData : c.whave ≠ 0 → ∃ window, window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat) :
    CausalBodyResult h r zs z s c slow fast bs dict L D dest output j bg := by
  have actual := fast_body_arbitrary_current packet buffers margin bits lptr lsafe lmask invariant get inv flags stable
    dptr dget dsafe dmask dinv dflags streamPtr statePtr mode left avail whave wnext wsize outPtr put begPtr endPtr
    outputGet write size current beginLe span guard windowData dictionary dictCount
  exact actual.held inv.acceptable dinv.acceptable

theorem ready_body_arbitrary_causal
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L} {L D : List Nat} {dict : List UInt8}
    (ready : FastLoopReady ctx h q)
    (lmeaning : ∃ used, Inv LENS ctx.codes ctx.baseOff ctx.rootWidth used L)
    (lstable : StableQuery LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (lflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (dmeaning : ∃ used, Inv DISTS ctx.distCodes ctx.distOff ctx.distWidth used D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (saved : Array UInt8) (woff : Nat)
    (windowData : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + ctx.c.wsize.toNat ≤ saved.size)
    (dictionary : MatchHistory.saved saved ctx.c.wsize.toNat ctx.c.wnext.toNat ctx.c.whave.toNat woff = dict)
    (dictCount : dict.length = ctx.c.whave.toNat) :
    ∃ slow bs output off j,
      FastInputPacket h slow bs q ∧ DispatchBuffers h ctx.r slow bs ∧
      slow.next = .ref ctx.inputRef off ∧ slow.put = .ref ctx.dest ctx.oo ∧ q.out = .ref ctx.dest j ∧
      Space.get h ctx.dest = some output ∧
      CausalBodyResult h ctx.r ctx.zs ctx.z ctx.s ctx.c slow q bs dict L D ctx.dest output j ctx.bg := by
  obtain ⟨slow, bs, output, off, j, packet, buffers, next, put, out, get, result⟩ :=
    ready_body_arbitrary ready lmeaning lstable lflags dmeaning dflags saved woff windowData dictionary dictCount
  exact ⟨slow, bs, output, off, j, packet, buffers, next, put, out, get,
    result.held lmeaning.choose_spec.acceptable dmeaning.choose_spec.acceptable⟩

#print axioms BodyResult.held
#print axioms fast_body_arbitrary_causal
#print axioms ready_body_arbitrary_causal
end Zlib.Inflate.Proofs.FastArbitraryBody
