import ZlibF.Proof.«inflate.c.payload-packet-unique»
import ZlibF.Spec.InflateFastTableFlags

import ZlibF.Proof.«inflate.c.fast-view-loop-ready-invariant»
import ZlibF.Proof.«inflate.c.fast-view-loop-broke-entry»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeTableInvariant
set_option autoImplicit false

/-- A real safety-loop state with a synchronized independent block parser.
The table and saved-ring fields are internal representation facts. -/
inductive FastSemanticReady (ctx : FastLoopContext)
    (L D : List Nat) (dict : List UInt8)
    (tail : List Bool) (target : List UInt8)
    (h : Heap) (q : Zlib.Inffast.L) : Prop where
  | intro
      (slow : IL)
      (bs : List UInt8)
      (output : Array UInt8)
      (off : Nat)
      (k : Nat)
      (packet : FastInputPacket h slow bs q)
      (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
      (buffers : DispatchBuffers h ctx.r slow bs)
      (codesGet : Space.get h ctx.codeRef = some ctx.codes)
      (distGet : Space.get h ctx.distRef = some ctx.distCodes)
      (bitsBound : slow.bits.toNat ≤ 30)
      (leftEq : slow.left = ctx.leftTotal)
      (outEq : slow.out_ = ctx.outTotal)
      (putPtr : slow.put = .ref ctx.dest ctx.oo)
      (nextPtr : slow.next = .ref ctx.inputRef off)
      (lastPtr : ctx.c.last = .ref ctx.inputRef (off + slow.have_.toNat - 5))
      (inputMargin : 6 ≤ slow.have_.toNat)
      (outPtr : q.out = .ref ctx.dest k)
      (outputGet : Space.get h ctx.dest = some output)
      (outputWrite : Space.ro h ctx.dest = false)
      (outputSize : ctx.oo + slow.left.toNat ≤ output.size)
      (current : ctx.oo ≤ k)
      (beginLe : ctx.bg ≤ k)
      (span : k - ctx.bg < 2 ^ 32)
      (guard : C.run (Ptr.lt q.out ctx.c.end_) h = .ok (true, h))
      (lenMeaning : ∃ used, Inv LENS ctx.codes ctx.baseOff ctx.rootWidth used L)
      (distMeaning : ∃ used, Inv DISTS ctx.distCodes ctx.distOff ctx.distWidth used D)
      (distFlags : FastTableFlags.QueryCompatible DISTS ctx.distCodes ctx.distOff ctx.distWidth)
      (saved : Array UInt8)
      (woff : Nat)
      (windowView : 0 < ctx.c.whave.toNat → ∃ window,
    window ≠ ctx.dest ∧ ctx.c.window = .ref window woff ∧
    Space.get h window = some saved ∧
    woff + ctx.c.wsize.toNat ≤ saved.size)
      (dictionary : MatchHistory.saved saved ctx.c.wsize.toNat ctx.c.wnext.toNat
    ctx.c.whave.toNat woff = dict)
      (dictCount : dict.length = ctx.c.whave.toNat)
      (history : List UInt8)
      (written : ZlibF.Math.LZ77Copy.writtenBytes output k (k - ctx.bg) = history)
      (historyCount : history.length = k - ctx.bg)
      (input : List Bool)
      (lengthSource : input = stream slow bs)
      (parsed : Symbols L D dict history input tail target)

/-- Forgetting parser meaning leaves the already proved actual safety ready state. -/
theorem FastSemanticReady.toSafety
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastSemanticReady ctx L D dict tail target h q) :
    FastLoopReady ctx h q := by
  rcases ready with ⟨slow, bs, output, off, k, packet, invariant, buffers, codesGet, distGet, bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin, outPtr, outputGet, outputWrite, outputSize, current, beginLe, span, guard, lenMeaning, distMeaning, distFlags, saved, woff, windowView, dictionary, dictCount, history, written, historyCount, input, lengthSource, parsed⟩
  exact ⟨slow, bs, output, off, k, packet, invariant, buffers, codesGet, distGet, bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin, outPtr, outputGet, outputWrite, outputSize, current, beginLe, span, guard⟩

#print axioms FastSemanticReady.toSafety
end Zlib.Inflate.Proofs
