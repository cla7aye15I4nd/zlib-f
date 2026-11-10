import ZlibF.Proof.«inflate.c.header-actual-code-tail-observation»
import ZlibF.Math.InflateHuffmanBodyContext
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Causal source prefix assembled from actual count/alphabet reads and
ordinary partial-reader Trace outputs. It asserts no complete CodeLens,
Header, Symbols or valid future. The history driver produces these fields
from actual TABLE/LENLENS/CODELENS events. -/
structure HeaderSourcePrefix (s : InflateState) (l : IL) (bs : List UInt8) (alphabet : List Nat) where
  bodyInput : List Bool
  r1 : List Bool
  r2 : List Bool
  r3 : List Bool
  codeInput : List Bool
  consumed : List Bool
  hlit : Nat
  hdist : Nat
  hclen : Nat
  first : readBits 5 bodyInput = some (hlit, r1)
  second : readBits 5 r1 = some (hdist, r2)
  third : readBits 4 r2 = some (hclen, r3)
  counts : DynamicCountsOK hlit hdist
  literalCount : s.nlen.toNat = hlit + 257
  distanceCount : s.ndist.toNat = hdist + 1
  alphabetRead : readCodeLenLens (hclen + 4) r3 = some (alphabet, codeInput)
  acceptable : Acceptable .codeLength alphabet
  source : codeInput = consumed ++ stream l bs
  trace : ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat) [] consumed (actualLengthPrefix s)

/-- Accepted actual reading and construction produce the independent
whole header from the accumulated source prefix. Successful branch
witnesses are outputs of the automatic classifiers, not caller contracts. -/
theorem accepted_header_from_source_prefix
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (prefixData : HeaderSourcePrefix s l bs alphabet)
    (observation : CodeReadObservation c h r zs z s l bs alphabet)
    (normal : observation.outcome = .ok ()) (code : observation.state.mode = CODELENS)
    (ready : TailReady c observation.heap r zs observation.streamZ observation.state observation.regs (bs.drop observation.used)) :
    Header 2 prefixData.bodyInput
      ((actualLengthPrefix observation.state).take observation.state.nlen.toNat)
      ((actualLengthPrefix observation.state).drop observation.state.nlen.toNat)
      (stream observation.regs (bs.drop observation.used)) := by
  have full := observation.full.1
  obtain ⟨state0, _used0, get0, _bound0, _B0, _shape, _bits, frame, _size, _have, _values, _modes, _done⟩ := full
  have stateEq : state0 = observation.state := Option.some.inj (get0.symm.trans observation.origin.good.live.hs)
  have savedLit : observation.state.nlen = s.nlen := by rw [← stateEq, frame]
  have savedDist : observation.state.ndist = s.ndist := by rw [← stateEq, frame]
  have complete : observation.state.«have».toNat = observation.state.nlen.toNat + observation.state.ndist.toNat := by
    rcases observation.complete normal with bad | done
    · rw [code] at bad; cases bad
    · exact done
  have current : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs)
      (stream observation.regs (bs.drop observation.used)) (actualLengthPrefix observation.state) := by
    rcases observation.grammar normal code with empty | parsed
    · obtain ⟨_zeroAlphabet, zeros, _badSource⟩ := empty
      have eob := ready.eob
      rw [zeros] at eob
      have lower : 256 < observation.state.nlen.toNat := by rw [savedLit, prefixData.literalCount]; omega
      have haveLower : 256 < observation.state.«have».toNat := by omega
      simp [HasEndOfBlock, List.take_replicate, List.getD_eq_getElem?_getD, Nat.lt_min, lower, haveLower] at eob
    · exact parsed
  have parsed := prefixData.trace _ _ _ current
  rw [← prefixData.source, prefixData.literalCount, prefixData.distanceCount] at parsed
  have literalEq : observation.state.nlen.toNat = prefixData.hlit + 257 := by rw [savedLit]; exact prefixData.literalCount
  obtain ⟨validL, validD⟩ := ready.accepted_lengths complete
  have header := Header.dynamic prefixData.first prefixData.second prefixData.third prefixData.counts prefixData.alphabetRead prefixData.acceptable parsed
    (by simpa only [literalEq] using ready.eob)
    (by simpa only [literalEq] using validL)
    (by simpa only [literalEq] using validD)
  simpa only [← literalEq] using header

#print axioms accepted_header_from_source_prefix
end Zlib.Inflate.Proofs.ActualHeader
