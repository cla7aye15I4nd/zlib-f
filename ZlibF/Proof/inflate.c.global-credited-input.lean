import ZlibF.Proof.«inflate.c.default-history»
import ZlibF.Spec.Public.Sequences
import ZlibF.Proof.«inflate.c.main.macros»
namespace Zlib.Inflate.Proofs.CausalInput
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Only input bytes actually credited by public calls enter this source
ledger. Unconsumed caller buffer contents remain free to be replaced. -/
def Credited (input : List UInt8) (committed : List Bool) (bits : UInt32) (hold : UInt64) : Prop :=
  bytesBits input = committed ++ natBits bits.toNat hold.toNat

theorem Credited.initial (hold : UInt64) : Credited [] [] 0 hold := by
  simp only [Credited, bytesBits_nil, UInt32.toNat_zero, natBits, List.nil_append]

/-- Compose one actual held/pulled/consumed source equation with the prior
public input ledger. Input used-counts must come from actual source
accounting, including fast suffix rollback. -/
theorem Credited.append
    {input raw : List UInt8} {prior word : List Bool} {bits nextBits : UInt32} {hold nextHold : UInt64}
    {used : Nat} (before : Credited input prior bits hold)
    (source : natBits bits.toNat hold.toNat ++ bytesBits (raw.take used) =
      word ++ natBits nextBits.toNat nextHold.toNat) :
    Credited (input ++ raw.take used) (prior ++ word) nextBits nextHold := by
  unfold Credited at before ⊢
  rw [bytesBits_append, before, List.append_assoc, source, List.append_assoc]

/-- Public saved-state observation carrying exact consumed input content.
This is a proof-side data-epoch projection, never a history constructor. -/
structure AtPublic (h : Heap) (r : ZStreamRef) (log : DataLog) (committed : List Bool) where
  zs : Nat
  z : ZStream
  state : InflateState
  good : Good h r zs z state
  source : Credited log.input committed state.bits state.hold

/-- Actual caller rebuffering preserves every private decoder scalar and
therefore the exact credited input equation, regardless of new buffers. -/
theorem AtPublic.rebuffer
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {committed : List Bool}
    (before : AtPublic h r log committed) (edit : Rebuffer h after r) :
    Nonempty (AtPublic after r log committed) := by
  obtain ⟨stream, _fields, good⟩ := rebuffer_inflate_good before.good edit
  exact ⟨before.zs, stream, before.state, good, before.source⟩

end Zlib.Inflate.Proofs.CausalInput
