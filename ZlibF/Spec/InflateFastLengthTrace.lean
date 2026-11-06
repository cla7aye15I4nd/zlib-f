import ZlibF.Spec.InflateFastLengthSemantics

/-!
# Actual fast-body result tied to its selected length-table leaf

The old body postcondition does not identify which literal/length entry
was selected. This obligation retains that selection and its actual
effects, including the length extras and the existing distance result.
-/

namespace Zlib.Inffast.Spec.LengthTrace
open C Zlib.Inffast Zlib.Inffast.Proofs ZlibF.Spec

/-- The two actual pre-lookup pulls, when needed, expressed with the
existing register-update function. No output or table storage changes. -/
def ready (e : Env) (l : L) (input : Nat) : L × Nat :=
  if l.bits < 15 then
    let first := pullL l (e.IN.getD input 0) (.ref (.blk e.ib) (input + 1))
    (pullL first (e.IN.getD (input + 1) 0) (.ref (.blk e.ib) (input + 2)), input + 2)
  else (l, input)

/-- The source branches after dropping the selected literal/length code.
The length branch retains actual extra-bit reading, refill and distance
lookup/copy results. Symbol meaning is supplied by the separate format
bridge, and saved-window provenance remains an enclosing invariant. -/
def End (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (remaining : List Bool) (input output : Nat) (entry : Code)
    (l' : L) (after : Heap) : Prop :=
  ¬ LenLink entry ∧ l'.againL = false ∧
  ((entry.op = 0 ∧ l'.broke = false ∧ LS e l' input (output + 1) ∧
      Sg e l'.hold.toNat l'.bits.toNat input = remaining ∧
      after = e.heap (bytes.set! output entry.val.toUInt8) msg mode) ∨
   (entry.op ≠ 0 ∧ entry.op &&& 16 ≠ 0 ∧
      ∃ input' extra rest,
        input ≤ input' ∧ input' ≤ input + 1 ∧
        readBits (entry.op &&& 15).toNat remaining = some (extra, rest) ∧
        RefillPost e bytes msg mode rest input' output (entry.val.toNat + extra) l' after) ∨
   (entry.op ≠ 0 ∧ entry.op &&& 16 = 0 ∧ entry.op &&& 64 ≠ 0 ∧
      entry.op &&& 32 ≠ 0 ∧ l'.broke = true ∧ LS e l' input output ∧
      Sg e l'.hold.toNat l'.bits.toNat input = remaining ∧
      after = e.heap bytes msg TYPE) ∨
   (entry.op ≠ 0 ∧ entry.op &&& 16 = 0 ∧ entry.op &&& 64 ≠ 0 ∧
      entry.op &&& 32 = 0 ∧ l'.broke = true ∧ LS e l' input output ∧
      Sg e l'.hold.toNat l'.bits.toNat input = remaining ∧
      ∃ errorMsg, after = e.heap bytes errorMsg BAD))

/-- The actual whole body returns its original safety result and the
selected leaf's exact effects. All source exits are retained. No body or
callee contract is a hypothesis, and no format-validity assumption hides
an invalid-code exit. These are the existing internal fast-body bounds. -/
def Goal.actual_body_retains_selected_length : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (input output : Nat),
    StepPre e c bytes l input output →
    let prepared := ready e l input
    ∃ (l' : L) (after : Heap),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      StepPost e bytes msg mode input output l' after ∧
      Sg e prepared.1.hold.toNat prepared.1.bits.toNat prepared.2 =
        Sg e l.hold.toNat l.bits.toNat input ∧
      ∃ entry consumed,
        consumed ≤ 15 ∧
        LengthSemantics.Look e prepared.1.hold.toNat
          (prepared.1.hold.toNat % 2 ^ e.s0.lenbits.toNat) entry consumed ∧
        End e bytes msg mode
          ((Sg e prepared.1.hold.toNat prepared.1.bits.toNat prepared.2).drop consumed)
          prepared.2 output entry l' after

end Zlib.Inffast.Spec.LengthTrace
