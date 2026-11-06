import ZlibF.Spec.InflateFastDistanceSemantics
import ZlibF.Spec.InflateFastMatchHistory
import ZlibF.Spec.InflateFast

/-!
# Independent symbol and copy meaning of the actual distance block

All input is retained. A rejected symbol, a too-far match and a successful
match have distinct results. The saved history is the actual window data;
its provenance from earlier public calls remains a separate obligation.
-/

namespace Zlib.Inffast.Spec.DistanceResult
open C Zlib.Inffast Zlib.Inffast.Proofs ZlibF.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec
open ZlibF.Math.LZ77Copy

/-- Physical copying after the distance extras have been consumed. Both
branches preserve the exact remaining input, including a too-far error. -/
def CopyOutcome (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (output len distance : Nat) (l' : L) (after : Heap) : Prop :=
  let history := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
    e.s0.whave.toNat e.woff
  let current := writtenBytes bytes output (output - e.bg)
  if history.length + current.length < distance then
    ∃ input' errorMsg,
      l'.broke = true ∧ LS e l' input' output ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source ∧
      after = e.heap bytes errorMsg BAD
  else
    ∃ input',
      let result := matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg output
        distance len bytes
      l'.broke = false ∧ LS e l' input' (output + len) ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source ∧
      after = e.heap result msg mode ∧
      writtenBytes result (output + len) (output - e.bg + len) =
        copyBack history distance len current

/-- Physical leaf dispatch, before relating the selected entry to an
independent symbol. This is a result to prove about the actual source,
not a callee contract assumed by the distance-block goal. -/
def PhysicalOutcome (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (source : List Bool) (output len : Nat) (entry : Code) (consumed : Nat)
    (l' : L) (after : Heap) : Prop :=
  (entry.op &&& 16 = 0 ∧
    ∃ input' errorMsg,
      l'.broke = true ∧ LS e l' input' output ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source.drop consumed ∧
      after = e.heap bytes errorMsg BAD) ∨
  (entry.op &&& 16 ≠ 0 ∧
    ∃ extra rest,
      readBits (entry.op &&& 15).toNat (source.drop consumed) = some (extra, rest) ∧
      CopyOutcome e bytes msg mode rest output len (entry.val.toNat + extra) l' after)

/-- The complete distance result, including the exact remaining source
bits on both errors. A successful copy equals independent bytewise LZ77
copying on the actual saved window and current output. -/
def Outcome (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (input output : Nat) (lens : List Nat) (entry : Code) (consumed : Nat)
    (l' : L) (after : Heap) : Prop :=
  let source := Sg e l.hold.toNat l.bits.toNat input
  let history := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
    e.s0.whave.toNat e.woff
  let current := writtenBytes bytes output (output - e.bg)
  (entry.op &&& 16 = 0 ∧
    (∀ more : List Bool,
      ¬ ∃ (symbol : Nat) (rest : List Bool),
        decodeSym lens (source ++ more) = some (symbol, rest) ∧ symbol ≤ 29) ∧
    ∃ input' errorMsg,
      l'.broke = true ∧ LS e l' input' output ∧
      Sg e l'.hold.toNat l'.bits.toNat input' = source.drop consumed ∧
      after = e.heap bytes errorMsg BAD) ∨
  (entry.op &&& 16 ≠ 0 ∧
    ∃ symbol extra codeRest rest,
      symbol ≤ 29 ∧ DecodeSemantics.SymbolEntry DISTS symbol entry ∧
      consumed = lens.getD symbol 0 ∧
      decodeSym lens source = some (symbol, codeRest) ∧
      readBits (distExtras.getD symbol 0) codeRest = some (extra, rest) ∧
      let distance := distBases.getD symbol 0 + extra
      if history.length + current.length < distance then
        ∃ input' errorMsg,
          l'.broke = true ∧ LS e l' input' output ∧
          Sg e l'.hold.toNat l'.bits.toNat input' = rest ∧
          after = e.heap bytes errorMsg BAD
      else
        ∃ input',
          let result := matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg output
            distance l.len.toNat bytes
          l'.broke = false ∧ LS e l' input' (output + l.len.toNat) ∧
          Sg e l'.hold.toNat l'.bits.toNat input' = rest ∧
          after = e.heap result msg mode ∧
          writtenBytes result (output + l.len.toNat) (output - e.bg + l.len.toNat) =
            copyBack history distance l.len.toNat current)

/-- Every actual distance-block exit retains the old execution result and
has its independent symbol/copy meaning. Internal table data facts must
still be established by actual construction. No callee contract or input
validity is a hypothesis. The physical domain is the existing distance
block's safety domain, not a restriction added to the public API. -/
def Goal.actual_distance_refines_lz77 : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (input output tableUsed : Nat) (lens : List Nat),
    CtxOK e c → LS e l input output →
    e.o0 + e.sm0.avail_out.toNat ≤ bytes.size →
    output + 258 ≤ e.o0 + e.sm0.avail_out.toNat → bytes.size < 2 ^ 63 →
    l.broke = false → (3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) →
    15 ≤ l.bits.toNat →
    (input + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (input + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat)) →
    DecodeTableInvariant.Inv DISTS e.DCA e.od e.s0.distbits.toNat tableUsed lens →
    DecodeTableStability.StableQuery DISTS e.DCA e.od e.s0.distbits.toNat →
    FastTableFlags.QueryCompatible DISTS e.DCA e.od e.s0.distbits.toNat →
    ∃ (l' : L) (after : Heap) (entry : Code) (consumed : Nat),
      C.run (dolenDist c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      consumed ≤ 15 ∧
      DistLook e l.hold.toNat (l.hold.toNat % 2 ^ e.s0.distbits.toNat) entry consumed ∧
      DistEnd e bytes msg mode
        ((Sg e l.hold.toNat l.bits.toNat input).drop consumed)
        input output l.len.toNat entry l' after ∧
      Outcome e bytes msg mode l input output lens entry consumed l' after

end Zlib.Inffast.Spec.DistanceResult
