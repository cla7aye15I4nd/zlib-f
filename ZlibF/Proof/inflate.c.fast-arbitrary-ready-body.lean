import ZlibF.Proof.«inflate.c.fast-arbitrary-body-current»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

/-- The existing actual safety-loop ready state consumes constructor table
facts and the physical saved history. The logical token and emitted bytes
are conclusions for arbitrary current input, not a ready-state premise. -/
theorem ready_body_arbitrary
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
      BodyResult h ctx.r ctx.zs ctx.z ctx.s ctx.c slow q bs dict L D ctx.dest output j ctx.bg := by
  rcases ready with ⟨slow, bs, output, off, j, packet, invariant, buffers, codesGet, distGet, bits,
    leftEq, _outEq, put, next, _last, margin, out, get, write, size, current, beginLe, span, guard⟩
  obtain ⟨lextent, linv⟩ := lmeaning
  obtain ⟨dextent, dinv⟩ := dmeaning
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest (ctx.oo + slow.left.toNat - 257) := by rw [leftEq]; exact ctx.endPtr
  have whave : ctx.c.whave.toNat ≤ ctx.c.wsize.toNat := by rw [ctx.whaveEq, ctx.wsizeEq]; exact invariant.good.inv.win.hv
  have wnext : ctx.c.wnext.toNat ≤ ctx.c.wsize.toNat := by
    rw [ctx.wnextEq, ctx.wsizeEq]
    rcases invariant.good.inv.win.wn with valid | ⟨zero, nextZero⟩ <;> omega
  have wsize : ctx.c.wsize.toNat ≤ 32768 := by
    rw [ctx.wsizeEq]
    rcases invariant.good.inv.win.ws with zero | full
    · omega
    · rw [invariant.window] at full
      change ctx.s.wsize.toNat = 32768 at full
      omega
  have event := fast_body_arbitrary_current packet buffers margin bits ctx.lcodePtr ctx.lenSafe ctx.lenMask
    invariant codesGet linv lflags lstable ctx.dcodePtr distGet ctx.distSafe ctx.distMask dinv dflags
    ctx.streamPtr ctx.statePtr ctx.mode left avail whave wnext wsize out put ctx.begPtr endPtr get write size
    current beginLe span guard windowData dictionary dictCount
  exact ⟨slow, bs, output, off, j, packet, buffers, next, put, out, get, event⟩

#print axioms ready_body_arbitrary
end Zlib.Inflate.Proofs.FastArbitraryBody
