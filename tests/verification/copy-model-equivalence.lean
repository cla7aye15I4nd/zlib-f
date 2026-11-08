/-!
Pointwise regression certificate for the copy-model implementation refactor.
The same file checks against the earlier model and the explicit recursor.
All copy counts, source offsets, destination offsets and arrays are quantified.
The earlier snapshot was checked separately before changing its implementation.
-/
import ZlibF.Math.InflateMatchCopy
import ZlibF.Proof.«inflate.c.fast-view-copy»

namespace ZlibF.Math.InflateMatchCopy
set_option autoImplicit false

/-- A direct natural-number recursor with the same forward-copy equations. -/
def copyRec (same : Bool) (saved : Array UInt8) (count : Nat) :
    Nat → Nat → Array UInt8 → Array UInt8 :=
  Nat.rec (motive := fun _ => Nat → Nat → Array UInt8 → Array UInt8)
    (fun _ _ output => output)
    (fun _ loop sourceOffset dest output =>
      let source := if same then output else saved
      loop (sourceOffset + 1) (dest + 1)
        (output.set! dest (source.getD sourceOffset 0))) count

/-- Pointwise agreement with the explicit forward-copy recursor. -/
theorem original_copy_eq_rec (same : Bool) (saved : Array UInt8) :
    ∀ count sourceOffset dest output,
      copy same saved count sourceOffset dest output =
        copyRec same saved count sourceOffset dest output
  | 0, _, _, _ => rfl
  | count + 1, sourceOffset, dest, output => by
    simpa only [copy, copyRec] using
      original_copy_eq_rec same saved count (sourceOffset + 1) (dest + 1)
        (output.set! dest ((if same then output else saved).getD sourceOffset 0))

#print axioms original_copy_eq_rec
end ZlibF.Math.InflateMatchCopy

namespace Zlib.Inflate.Proofs
set_option autoImplicit false

theorem original_other_alias (saved : Array UInt8) (sourceOff : Nat)
    (output : Array UInt8) (j count : Nat) :
    copyOtherBytes saved sourceOff output j count =
      Zlib.Inffast.Proofs.blitN saved count sourceOff j output :=
  copyOtherBytes_eq_blitN count saved sourceOff output j

theorem original_same_alias (output : Array UInt8) (sourceOff j count : Nat) :
    copySameBytes output sourceOff j count =
      Zlib.Inffast.Proofs.cpyN count sourceOff j output :=
  copySameBytes_eq_cpyN count output sourceOff j

#print axioms original_other_alias
#print axioms original_same_alias
end Zlib.Inflate.Proofs
