import ZlibF.Proof.«inflate.c.whole-slow-token-phases»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs FunctionalEpoch SlowReverseToken SlowRejectedToken
set_option autoImplicit false

 theorem CallFacts.slow_count
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (facts : CallFacts c entryHeap h r zs entryZ z s l base raw) (active : s.mode < CHECK) :
    l.out_.toNat - l.left.toNat = facts.emitted.length := by
  rw [facts.outputStart active]
  have count := facts.leftCount
  omega

 theorem CallFacts.slow_history_view
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (facts : CallFacts c entryHeap h r zs entryZ z s l base raw) (active : s.mode < CHECK) :
    ∀ dest off array, l.put = .ref dest off → Space.get h dest = some array →
      ZlibF.Math.LZ77Copy.writtenBytes array off (l.out_.toNat - l.left.toNat) = facts.emitted := by
  intro dest off array pointer get
  rw [facts.slow_count active]
  exact facts.physical dest off array pointer get

 theorem CallFacts.slow_representation
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {L D : List Nat}
    (epoch : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (wrapper : Wrapper base.dictionary) (tables : TableBinding h s L D) (active : s.mode < CHECK) :
    PayloadRepresentation h r zs z s l (raw.drop epoch.used) L D (wrapper.dictionary ++ base.output) := by
  let cut := epoch
  have representation : PayloadRepresentation h r zs z s l (raw.drop cut.used) L D (base.dictionary ++ base.output) :=
    ⟨cut.origin, cut.buffers, cut.bits, tables.1, cut.window active⟩
  by_cases flagged : wrapper.flg.toNat / 32 % 2 = 1
  · have trimmed := representation.trim_dictionary
    simpa only [Wrapper.dictionary, flagged, ↓reduceIte] using trimmed
  · have plain : wrapper.flg.toNat / 32 % 2 = 0 := by
      have bounded := Nat.mod_lt (wrapper.flg.toNat / 32) (by decide : 0 < 2)
      omega
    have empty : base.dictionary = [] := wrapper.plainEmpty plain
    simpa only [Wrapper.dictionary, flagged, ↓reduceIte, empty] using representation

 theorem CallFacts.slow_payload_view
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {L D : List Nat}
    (epoch : CallFacts c entryHeap h r zs entryZ z s l base raw)
    (wrapper : Wrapper base.dictionary) (tables : TableBinding h s L D) (mode : DataTableMode s.mode) :
    PayloadView h r zs z s l (raw.drop epoch.used)
      ((wrapper.dictionary ++ base.output).drop ((wrapper.dictionary ++ base.output).length - 32768))
      epoch.emitted L D ∧ QueriesStable h s := by
  have active : s.mode < CHECK := by
    rcases mode with start | len | le | dist | de | matching | lit <;>
      first | rw [start]; decide | rw [len]; decide | rw [le]; decide | rw [dist]; decide |
        rw [de]; decide | rw [matching]; decide | rw [lit]; decide
  have representation := epoch.slow_representation wrapper tables active
  obtain ⟨origin, buffers, _bits, installed, dictionary⟩ := representation
  have safe := origin.tables mode
  refine ⟨⟨origin.good, safe, CurrentTables.of_installed safe installed, ?_, buffers, ?_, epoch.slow_history_view active, ?_⟩,
    QueriesStable.of_installed installed⟩
  · rw [origin.toDefaultStateJ.window] at dictionary
    exact dictionary
  · rw [origin.pending.sane]
    decide
  · exact (epoch.slow_count active).symm

#print axioms CallFacts.slow_count
#print axioms CallFacts.slow_history_view
#print axioms CallFacts.slow_representation
#print axioms CallFacts.slow_payload_view
end Zlib.Inflate.Proofs.WholeEpoch
