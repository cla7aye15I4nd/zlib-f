import ZlibF.Proof.«inflate.c.payload-body-future-cursor»
import ZlibF.Proof.«inflate.c.payload-same-used-bridge»
import ZlibF.Proof.«inflate.c.fast-view-body-condition-heap-bits-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec
open Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness Zlib.Inftrees.Spec.DecodeTableInvariant
open Zlib.Inftrees.Spec.Subtable
set_option autoImplicit false
set_option maxRecDepth 8192

theorem FastInputPacket.fast_body_symbols_future_safety_aligned
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8} {rawTail : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rawTail) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rawTail))
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth tableUsed : Nat} {lens : List Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (meaning : Inv LENS codes baseOff rootWidth tableUsed lens)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth distUsed : Nat} {D : List Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMeaning : Inv DISTS distCodes distOff distWidth distUsed D)
    (distFlags : FastTableFlags.QueryCompatible DISTS distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {saved : Array UInt8} {woff : Nat}
    (windowView : 0 < c.whave.toNat → ∃ window,
      window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    {dict history target : List UInt8} {input tail future : List Bool}
    (lengthSource : input = stream slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rawTail))
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat
      c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat)
    (written : ZlibF.Math.LZ77Copy.writtenBytes output j (j - bg) = history)
    (historyCount : history.length = j - bg)
    (parsed : Symbols lens D dict history (input ++ future) tail target)
    (streamPtr : c.strm = some r)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {inputRef : BRef} {inputOff : Nat}
    (nextPtr : slow.next = .ref inputRef inputOff)
    (lastPtr : c.last = .ref inputRef
      (inputOff + slow.have_.toNat - 5)) :
    ∃ usedSem usedSafety result after semanticSlow safetySlow,
      ∃ (array : Array UInt8) (made : Nat) (next : List UInt8)
        (done : Bool),
      usedSem ≤ 7 ∧ usedSem ≤
        (first :: second :: third :: fourth :: fifth :: sixth :: rawTail).length ∧
      usedSafety ≤ 6 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      FastInputPacket after semanticSlow
        ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop usedSem)
        result ∧
      FastInputPacket after safetySlow
        ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop usedSafety)
        result ∧
      result.in_ = inputAdvance l.in_ usedSem ∧
      Space.get after dest = some array ∧
      Token.Step lens D dict history input
        (stream semanticSlow
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop usedSem))
        next done ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (j + made) ((j - bg) + made) = next ∧
      (done = false → result.out = .ref dest (j + made)) ∧
      (done = true → after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧ made = 0) ∧
      (done = true →
        stream semanticSlow
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop usedSem) ++ future = tail ∧
        next = target) ∧
      (done = false → Symbols lens D dict next
        (stream semanticSlow
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop usedSem) ++ future)
        tail target) ∧
      (result.broke = false → ∃ finalOutput : Array UInt8,
        after = Space.put h dest finalOutput) ∧
      (result.broke = false →
        usedSem = usedSafety ∧
        stream semanticSlow
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop usedSem) =
        stream safetySlow
          ((first :: second :: third :: fourth :: fifth :: sixth :: rawTail).drop usedSafety)) := by
  obtain ⟨usedSem, semResult, semAfter, array, semanticSlow,
    made, next, done, semBound, semRaw, semRun, semPacket,
    semGet, token, bytes, out, terminal, endSource,
    continuation, semCursor⟩ :=
    packet.fast_body_of_symbols_future_cursor invariant buffers statePtr mode
      lcodePtr codesGet safe meaning mask bitsBound dcodePtr distGet
      distSafe distMeaning distFlags distMask left avail outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize current beginLe
      span guard whaveBound wnextBound wsizeBound windowView lengthSource
      dictionary dictCount written historyCount parsed
  obtain ⟨usedSafety, consumed, safetySlow, result, after, zNext, sNext,
    safetyBound, consumedBound, safetyRun, safetyPacket, finalJ,
    finalBuffers, sizes, source, rank, finalFrame, heapFrame,
    keepGoing, condRun, continuing, finalBits⟩ :=
    packet.fast_body_condition_heap_bits_default_state
      invariant buffers streamPtr statePtr mode whaveEq wsizeEq
      wnextEq windowEq lcodePtr codesGet safe mask dcodePtr distGet
      distSafe distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe span
      guard nextPtr lastPtr
  have same : (semResult, semAfter) = (result, after) :=
    Except.ok.inj (semRun.symm.trans safetyRun)
  cases same
  refine ⟨usedSem, usedSafety, semResult, semAfter, semanticSlow,
    safetySlow, array, made, next, done, semBound, semRaw, safetyBound,
    safetyRun, semPacket, safetyPacket, semCursor, semGet, token, bytes, out,
    terminal, endSource, continuation, (fun normal => let ⟨a, eq, _, _⟩ := heapFrame normal; ⟨a, eq⟩), ?_⟩
  intro normal
  obtain ⟨_, _, _, safetyCursor, _, _⟩ := finalFrame normal
  have count : usedSem = usedSafety :=
    packet.same_used_of_actual_cursor safetyPacket nextPtr semCursor safetyCursor
  exact ⟨count, semPacket.same_stream_of_same_result safetyPacket count⟩

#print axioms FastInputPacket.fast_body_symbols_future_safety_aligned
end Zlib.Inflate.Proofs
