import ZlibF.Proof.«inflate.c.fast-arbitrary-body-length-cut»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The actual source-selected fitted leaf yields independent decoding on
the original current input. Padding has supplied no consumed bit. -/
theorem BodyLengthCut.accepted_meaning
    {h : Heap} {r : ZStreamRef} {c : Zlib.Inffast.Ctx} {ref : CodeRef}
    {codes : Array Code} {offset root extent : Nat} {L : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (inv : Inv LENS codes offset root extent L)
    (accepted : LeafAccepted LENS (codes.getD cut.selection.index default)) :
    ∃ symbol, ValidSymbol LENS symbol ∧ SymbolEntry LENS symbol (codes.getD cut.selection.index default) ∧
      cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat = L.getD symbol 0 ∧
      decodeSym L (stream slow bs) = some (symbol, (stream slow bs).drop
        (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat)) := by
  have fit : cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat ≤
      (bitsOfNat cut.preparedSlow.hold.toNat cut.preparedSlow.bits.toNat).length := by
    rw [bitsOfNat_length]
    have := cut.selection.width
    have := cut.held
    omega
  obtain ⟨symbol, valid, fields, width, _decoded, extended⟩ := inv.short _ _ _ cut.selection.query fit accepted
  have source : bitsOfNat cut.preparedSlow.hold.toNat cut.preparedSlow.bits.toNat ++ bytesBits (bs.drop cut.used) = stream slow bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using cut.source
  have decoded := extended (bytesBits (bs.drop cut.used))
  have rest : (bitsOfNat cut.preparedSlow.hold.toNat cut.preparedSlow.bits.toNat).drop
      (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) ++ bytesBits (bs.drop cut.used) =
      (stream slow bs).drop (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) := by
    rw [← source, List.drop_append_of_le_length fit]
  rw [source, rest] at decoded
  exact ⟨symbol, valid, fields, width, decoded⟩

/-- Rejected fitted root/subtable entries remain invalid on every unread
suffix. This theorem does not posit a future valid token. -/
theorem BodyLengthCut.rejected_meaning
    {h : Heap} {r : ZStreamRef} {c : Zlib.Inffast.Ctx} {ref : CodeRef}
    {codes : Array Code} {offset root extent : Nat} {L : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (inv : Inv LENS codes offset root extent L) (stable : StableQuery LENS codes offset root)
    (rejected : ¬ LeafAccepted LENS (codes.getD cut.selection.index default)) :
    ∀ more : List Bool, ¬ ∃ symbol rest,
      decodeSym L (stream slow bs ++ more) = some (symbol, rest) ∧ ValidSymbol LENS symbol := by
  have fit : cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat ≤
      (bitsOfNat cut.preparedSlow.hold.toNat cut.preparedSlow.bits.toNat).length := by
    rw [bitsOfNat_length]
    have := cut.selection.width
    have := cut.held
    omega
  have invalid := Zlib.Inftrees.Proofs.short_rejected_leaf_stays_invalid LENS codes offset root extent L inv stable
    _ _ _ cut.selection.query fit rejected
  intro more
  have extended := invalid (bytesBits (bs.drop cut.used) ++ more)
  have source : bitsOfNat cut.preparedSlow.hold.toNat cut.preparedSlow.bits.toNat ++ bytesBits (bs.drop cut.used) = stream slow bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using cut.source
  simpa only [← List.append_assoc, source] using extended

/-- Actual root bits already consumed by the first pass and actual leaf
bits compose to the exact original code residual. -/
theorem BodyLengthCut.leaf_rest
    {h : Heap} {r : ZStreamRef} {c : Zlib.Inffast.Ctx} {ref : CodeRef}
    {codes : Array Code} {offset root : Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs) :
    (stream cut.selection.slow (bs.drop cut.used)).drop (codes.getD cut.selection.index default).bits.toNat =
      (stream slow bs).drop (cut.selection.skipped + (codes.getD cut.selection.index default).bits.toNat) := by
  rw [cut.selection.source, cut.source, List.drop_drop]

/-- The actual raw cursor is retained independently of byte values. -/
theorem BodyLengthCut.selected_cursor
    {h : Heap} {r : ZStreamRef} {c : Zlib.Inffast.Ctx} {ref : CodeRef}
    {codes : Array Code} {offset root : Nat} {slow : IL} {fast : Zlib.Inffast.L} {bs : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs) :
    cut.selection.fast.in_ = inputAdvance fast.in_ cut.used := by
  rw [cut.selection.packet.cursor, cut.selection.slowFields.1, cut.cursor, cut.initialCursor]

#print axioms BodyLengthCut.accepted_meaning
#print axioms BodyLengthCut.rejected_meaning
#print axioms BodyLengthCut.leaf_rest
#print axioms BodyLengthCut.selected_cursor
end Zlib.Inflate.Proofs.FastArbitraryBody
