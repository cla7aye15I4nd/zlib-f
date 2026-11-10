import ZlibF.Proof.«inflate.c.fast-causal-loop-word-run»
namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- Exact content, not only length, identifies the grammar's committed
word with the actual input bytes retained as consumed after fast rollback. -/
theorem WordSource.rollback_prefix
    {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    {observation : Observation p h q} (source : WordSource observation)
    (smallEntry : p.entry.bits.toNat < 8) :
    natBits p.entry.bits.toNat p.entry.hold.toNat ++
        bytesBits (p.input.take (observation.pulled - q.bits.toNat / 8)) =
      observation.word ++ natBits (q.bits.toNat % 8) (q.hold.toNat % 2 ^ (q.bits.toNat % 8)) := by
  have remaining := (observation.origin.rollback smallEntry).2.1
  unfold WordSource at source
  rw [← remaining] at source
  have split : natBits p.entry.bits.toNat p.entry.hold.toNat ++ bytesBits p.input =
      (natBits p.entry.bits.toNat p.entry.hold.toNat ++
          bytesBits (p.input.take (observation.pulled - q.bits.toNat / 8))) ++
        bytesBits (p.input.drop (observation.pulled - q.bits.toNat / 8)) := by
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
  rw [split, ← List.append_assoc] at source
  exact List.append_cancel_right source

/-- Actual LOAD scalar/accounting observations turn rollback content into
the precise held-only public-call input prefix, with the same grammar word. -/
theorem WordSource.loaded_prefix
    {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    {observation : Observation p h q} {loaded : IL} {used : Nat}
    (source : WordSource observation) (smallEntry : p.entry.bits.toNat < 8)
    (count : used = observation.pulled - q.bits.toNat / 8)
    (bits : loaded.bits.toNat = q.bits.toNat % 8)
    (hold : loaded.hold.toNat = q.hold.toNat % 2 ^ (q.bits.toNat % 8)) :
    natBits p.entry.bits.toNat p.entry.hold.toNat ++ bytesBits (p.input.take used) =
      observation.word ++ natBits loaded.bits.toNat loaded.hold.toNat := by
  rw [count, bits, hold]
  exact source.rollback_prefix smallEntry

end Zlib.Inflate.Proofs.FastCommittedLoop
