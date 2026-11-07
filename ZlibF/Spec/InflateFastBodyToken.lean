import ZlibF.Spec.Format.Token
import ZlibF.Spec.InflateFastLengthTrace
import ZlibF.Spec.InflateFastDistanceResult

/-!
# Actual fast-body output refines an independent token

This local result covers every input, including invalid symbols and
too-far matches. It consumes only the current token. No valid completion
of all pulled lookahead is assumed.
-/

namespace Zlib.Inffast.Spec.BodyToken
open C Zlib.Inffast Zlib.Inffast.Proofs ZlibF.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec
open ZlibF.Math.LZ77Copy

/-- Data facts about the same actual arrays used by the fast decoder.
Actual construction and installation must establish these fields; no
translated function contract is stored here. -/
structure Tables (e : Env) (L D : List Nat) : Prop where
  lengthTable : ∃ used,
    DecodeTableInvariant.Inv LENS e.LCA e.ol e.s0.lenbits.toNat used L
  distanceTable : ∃ used,
    DecodeTableInvariant.Inv DISTS e.DCA e.od e.s0.distbits.toNat used D
  lengthStable : DecodeTableStability.StableQuery LENS e.LCA e.ol e.s0.lenbits.toNat
  distanceStable : DecodeTableStability.StableQuery DISTS e.DCA e.od e.s0.distbits.toNat
  lengthFlags : FastTableFlags.QueryCompatible LENS e.LCA e.ol e.s0.lenbits.toNat
  distanceFlags : FastTableFlags.QueryCompatible DISTS e.DCA e.od e.s0.distbits.toNat

/-- The actual distance call reached after length extras and refill.
Its physical entry state is retained so that the proved distance result
can be applied. The run equation is a conclusion, never a hypothesis
standing in for a callee's correctness theorem. -/
def DistanceEntry (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (beforeRefill output len : Nat)
    (l' : Zlib.Inffast.L) (after : Heap) : Prop :=
  ∃ (entry : Zlib.Inffast.L) (input : Nat),
    beforeRefill ≤ input ∧ input ≤ beforeRefill + 2 ∧
    LS e entry input output ∧ entry.broke = false ∧ entry.len.toNat = len ∧
    15 ≤ entry.bits.toNat ∧
    (input + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (input + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ entry.bits.toNat)) ∧
    Sg e entry.hold.toNat entry.bits.toNat input = source ∧
    C.run (dolenDist c entry) (e.heap bytes msg mode) = .ok (l', after)

/-- The source length tail retains its extra-bit read and the actual
distance-entry cut point. The old `RefillPost` alone loses that cut point
on errors and cannot justify applying a distance execution theorem. -/
def LengthTail (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (input output : Nat) (entry : Code)
    (l' : Zlib.Inffast.L) (after : Heap) : Prop :=
  ∃ input' extra rest,
    input ≤ input' ∧ input' ≤ input + 1 ∧
    readBits (entry.op &&& 15).toNat source = some (extra, rest) ∧
    DistanceEntry e c bytes msg mode rest input' output (entry.val.toNat + extra) l' after

/-- Strengthen the source result without changing the already proved
length trace or the public target. Only a length-base branch needs the
additional actual distance-entry equation. -/
def EndWithDistanceEntry (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (input output : Nat) (entry : Code)
    (l' : Zlib.Inffast.L) (after : Heap) : Prop :=
  LengthTrace.End e bytes msg mode source input output entry l' after ∧
  (entry.op ≠ 0 ∧ entry.op &&& 16 ≠ 0 →
    LengthTail e c bytes msg mode source input output entry l' after)

/-- The actual body emits exactly one independently decoded token, ends
the block, or rejects that token without output. The full old safety
postcondition and actual heap result are retained. Source-origin and the
across-call history invariant connect these local inputs to public runs.
This is the existing internal physical domain, not the public API goal. -/
def Goal.actual_body_refines_token : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : Zlib.Inffast.L) (input output : Nat) (L D : List Nat),
    StepPre e c bytes l input output → Tables e L D →
    ∃ (l' : Zlib.Inffast.L) (after : Heap) (input' output' : Nat)
      (result : Array UInt8) (resultMsg : BPtr) (resultMode : UInt32),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      StepPost e bytes msg mode input output l' after ∧
      LS e l' input' output' ∧ result.size = bytes.size ∧
      after = e.heap result resultMsg resultMode ∧
      let history := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
        e.s0.whave.toNat e.woff
      let current := writtenBytes bytes output (output - e.bg)
      let produced := writtenBytes result output' (output' - e.bg)
      let source := Sg e l.hold.toNat l.bits.toNat input
      let rest := Sg e l'.hold.toNat l'.bits.toNat input'
      ((l'.broke = false ∧ Token.Step L D history current source rest produced false) ∨
       (l'.broke = true ∧ resultMode = TYPE ∧
         Token.Step L D history current source rest produced true) ∨
       (l'.broke = true ∧ resultMode = BAD ∧ produced = current ∧
         Token.Rejected L D history current source))

end Zlib.Inffast.Spec.BodyToken
