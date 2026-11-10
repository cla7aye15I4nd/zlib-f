import ZlibF.Proof.«inftrees.c.query-take-source»
import ZlibF.Proof.«inflate.c.fast-arbitrary-body-causal»
namespace Zlib.Inftrees.Proofs.QueryTakeSource
open C Zlib.Inftrees ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

/-- Actual constructor/fixed prefix replication restricts the fitted query
to precisely its consumed word. Suffix stability then rejects every
completion, without crediting any looked-ahead but undropped held bit. -/
theorem rejected_consumed_word
    {type : UInt32} {ca : Array Code} {offset root extent : Nat} {alphabet : List Nat}
    (inv : Inv type ca offset root extent alphabet)
    (stable : StableQuery type ca offset root) (takeQuery : QueryTake type ca offset root)
    {inp : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead type ca offset root (Zlib.Inftrees.Spec.DecodeShort.padded inp) = some (entry, consumed))
    (fit : consumed ≤ inp.length) (rejected : ¬ LeafAccepted type entry) :
    (inp.take consumed).length = consumed ∧
      ∀ future : List Bool, ¬ ∃ symbol rest,
        decodeSym alphabet (inp.take consumed ++ future) = some (symbol, rest) ∧ ValidSymbol type symbol := by
  have wordLength : (inp.take consumed).length = consumed := by
    simp only [List.length_take, Nat.min_eq_left fit]
  have shortQuery := takeQuery inp entry consumed query fit
  exact ⟨wordLength, short_rejected_leaf_stays_invalid type ca offset root extent alphabet inv stable
    (inp.take consumed) entry consumed shortQuery (by rw [wordLength]; exact Nat.le_refl _) rejected⟩

#print axioms rejected_consumed_word
end Zlib.Inftrees.Proofs.QueryTakeSource

namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees Zlib.Inffast.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

/-- Real zero/two pulls credit exactly these bytes into held bits. The
physical raw-used index, rather than equality of byte values, selects them. -/
theorem BodyLengthCut.held_raw_source
    {h : Heap} {r : ZStreamRef} {c : Zlib.Inffast.Ctx} {ref : CodeRef}
    {codes : Array Code} {offset root : Nat} {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs) :
    natBits cut.preparedSlow.bits.toNat cut.preparedSlow.hold.toNat =
      natBits slow.bits.toNat slow.hold.toNat ++ bytesBits (bs.take cut.used) := by
  have source := cut.source
  change natBits cut.preparedSlow.bits.toNat cut.preparedSlow.hold.toNat ++ bytesBits (bs.drop cut.used) =
    natBits slow.bits.toNat slow.hold.toNat ++ bytesBits bs at source
  have split : bytesBits bs = bytesBits (bs.take cut.used) ++ bytesBits (bs.drop cut.used) := by
    rw [← bytesBits_append, List.take_append_drop]
  rw [split, ← List.append_assoc] at source
  exact List.append_cancel_right source

/-- Any produced leaf drop with its actual unread byte slice determines
exactly the undropped held suffix. No unread caller byte is fixed. -/
theorem BodyLengthCut.dropped_held_source
    {h : Heap} {r : ZStreamRef} {c : Zlib.Inffast.Ctx} {ref : CodeRef}
    {codes : Array Code} {offset root : Nat} {slow finalSlow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (source : stream finalSlow (bs.drop cut.used) = (stream slow bs).drop
      (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat)) :
    natBits finalSlow.bits.toNat finalSlow.hold.toNat =
      (natBits cut.preparedSlow.bits.toNat cut.preparedSlow.hold.toNat).drop
        (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) := by
  have fit : cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat ≤
      (natBits cut.preparedSlow.bits.toNat cut.preparedSlow.hold.toNat).length := by
    rw [natBits_length]
    have := cut.selection.width
    have := cut.held
    omega
  rw [← cut.source] at source
  change natBits finalSlow.bits.toNat finalSlow.hold.toNat ++ bytesBits (bs.drop cut.used) =
    (natBits cut.preparedSlow.bits.toNat cut.preparedSlow.hold.toNat ++ bytesBits (bs.drop cut.used)).drop _ at source
  rw [List.drop_append_of_le_length fit] at source
  exact List.append_cancel_right source

#print axioms BodyLengthCut.held_raw_source
#print axioms BodyLengthCut.dropped_held_source
end Zlib.Inflate.Proofs.FastArbitraryBody
