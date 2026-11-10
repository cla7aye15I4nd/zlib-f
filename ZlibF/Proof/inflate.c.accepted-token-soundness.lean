import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»
import ZlibF.Proof.«inffast.c.dist»
import ZlibF.Proof.Format.Token

namespace Zlib.Inflate.Proofs.AcceptedToken
open C Zlib.Inftrees ZlibF.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant
set_option autoImplicit false

/-- A fitted actual table query determines a symbol on the current source.
The unread suffix is arbitrary. No independent valid future is assumed. -/
theorem accepted_query
    {type : UInt32} {ca : Array Code} {offset root extent : Nat} {alphabet : List Nat}
    (inv : Inv type ca offset root extent alphabet)
    {held : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead type ca offset root
      (Zlib.Inftrees.Spec.DecodeShort.padded held) = some (entry, consumed))
    (fitted : consumed ≤ held.length) (accepted : LeafAccepted type entry)
    (unread : List Bool) :
    ∃ symbol, ValidSymbol type symbol ∧ SymbolEntry type symbol entry ∧
      consumed = alphabet.getD symbol 0 ∧
      decodeSym alphabet (held ++ unread) = some (symbol, held.drop consumed ++ unread) := by
  obtain ⟨symbol, valid, fields, width, _decoded, extended⟩ :=
    inv.short held entry consumed query fitted accepted
  exact ⟨symbol, valid, fields, width, extended unread⟩

private theorem length_fields {symbol : Nat} {entry : Code}
    (lower : 257 ≤ symbol) (upper : symbol ≤ 285)
    (fields : SymbolEntry LENS symbol entry) :
    entry.op &&& 16 ≠ 0 ∧
    (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
    entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
  have finite : ∀ n : Fin 29, lengthExtras.getD n.val 0 ≤ 5 := by decide +kernel
  have bound : lengthExtras.getD (symbol - 257) 0 ≤ 5 := finite ⟨symbol - 257, by omega⟩
  have exactFields : entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
    simpa only [SymbolEntry, ite_true, ite_eq_right (show ¬ symbol < 256 by omega),
      ite_eq_right (show symbol ≠ 256 by omega), ite_eq_left upper] using fields
  have masks : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 21 →
      op &&& 16 ≠ 0 ∧ (op &&& 15).toNat = op.toNat - 16 := by
    apply Zlib.Inffast.Proofs.u8_forall
    decide +kernel
  have shape := masks entry.op (by omega) (by omega)
  exact ⟨shape.1, by rw [shape.2, exactFields.1]; omega, exactFields.2⟩

theorem literal_symbol {symbol : Nat} {entry : Code}
    (valid : ValidSymbol LENS symbol) (fields : SymbolEntry LENS symbol entry)
    (literal : entry.op = 0) : symbol < 256 ∧ entry.val.toNat = symbol := by
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  by_cases small : symbol < 256
  · exact ⟨small, (by simpa only [SymbolEntry, ite_true, ite_eq_left small] using fields :
      entry.op = 0 ∧ entry.val.toNat = symbol).2⟩
  · by_cases ending : symbol = 256
    · subst symbol
      have eob : entry.op = 96 ∧ entry.val = 0 := by simpa [SymbolEntry] using fields
      simp [literal] at eob
    · have base := (length_fields (by omega) upper fields).1
      simp [literal] at base

theorem base_symbol {symbol : Nat} {entry : Code}
    (valid : ValidSymbol LENS symbol) (fields : SymbolEntry LENS symbol entry)
    (base : entry.op &&& 16 ≠ 0) :
    257 ≤ symbol ∧ symbol ≤ 285 ∧
      (entry.op &&& 15).toNat = lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0 := by
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  have lower : 257 ≤ symbol := by
    by_cases small : symbol < 256
    · have ordinary : entry.op = 0 ∧ entry.val.toNat = symbol := by
        simpa only [SymbolEntry, ite_true, ite_eq_left small] using fields
      simp [ordinary.1] at base
    · by_cases ending : symbol = 256
      · subst symbol
        have eob : entry.op = 96 ∧ entry.val = 0 := by simpa [SymbolEntry] using fields
        exact False.elim (base (by rw [eob.1]; decide +kernel))
      · omega
  exact ⟨lower, upper, (length_fields lower upper fields).2⟩

theorem eob_symbol {symbol : Nat} {entry : Code}
    (valid : ValidSymbol LENS symbol) (fields : SymbolEntry LENS symbol entry)
    (nonzero : entry.op ≠ 0) (noBase : entry.op &&& 16 = 0) : symbol = 256 := by
  have upper : symbol ≤ 285 := by simpa [ValidSymbol] using valid
  by_cases small : symbol < 256
  · have ordinary : entry.op = 0 ∧ entry.val.toNat = symbol := by
      simpa only [SymbolEntry, ite_true, ite_eq_left small] using fields
    exact False.elim (nonzero ordinary.1)
  · by_cases ending : symbol = 256
    · exact ending
    · exact False.elim ((length_fields (by omega) upper fields).1 noBase)

theorem distance_fields {symbol : Nat} {entry : Code}
    (valid : ValidSymbol DISTS symbol) (fields : SymbolEntry DISTS symbol entry) :
    symbol ≤ 29 ∧ (entry.op &&& 15).toNat = distExtras.getD symbol 0 ∧
      entry.val.toNat = distBases.getD symbol 0 := by
  have upper : symbol ≤ 29 := by
    simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using valid
  have exactFields : entry.op.toNat = 16 + distExtras.getD symbol 0 ∧
      entry.val.toNat = distBases.getD symbol 0 := by
    simpa only [SymbolEntry, show DISTS ≠ LENS by decide, ite_false,
      ite_eq_left upper] using fields
  have finite : ∀ n : Fin 30, distExtras.getD n.val 0 ≤ 13 := by decide +kernel
  have bound : distExtras.getD symbol 0 ≤ 13 := finite ⟨symbol, by omega⟩
  have masks : ∀ op : UInt8, 16 ≤ op.toNat → op.toNat ≤ 29 →
      (op &&& 15).toNat = op.toNat - 16 := by
    apply Zlib.Inffast.Proofs.u8_forall
    decide +kernel
  refine ⟨upper, ?_, exactFields.2⟩
  rw [masks entry.op (by omega) (by omega), exactFields.1]
  omega

/-- An actual accepted literal yields the original token relation, even if
the unread source is malformed. The output byte is the actual leaf value. -/
theorem literal_step
    {ca : Array Code} {offset root extent : Nat} {L D : List Nat}
    (inv : Inv LENS ca offset root extent L)
    {held : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead LENS ca offset root
      (Zlib.Inftrees.Spec.DecodeShort.padded held) = some (entry, consumed))
    (fitted : consumed ≤ held.length) (literal : entry.op = 0)
    (unread : List Bool) (dictionary history : List UInt8) :
    Token.Step L D dictionary history (held ++ unread) (held.drop consumed ++ unread)
      (history ++ [entry.val.toNat.toUInt8]) false := by
  have accepted : LeafAccepted LENS entry := by simp [LeafAccepted, literal]
  obtain ⟨symbol, valid, fields, _width, decoded⟩ :=
    accepted_query inv query fitted accepted unread
  obtain ⟨small, value⟩ := literal_symbol valid fields literal
  rw [value]
  exact .literal decoded small

/-- An actual accepted nonliteral nonbase leaf closes the independent
block. This does not ask for a Symbols derivation of any future suffix. -/
theorem eob_step
    {ca : Array Code} {offset root extent : Nat} {L D : List Nat}
    (inv : Inv LENS ca offset root extent L)
    {held : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead LENS ca offset root
      (Zlib.Inftrees.Spec.DecodeShort.padded held) = some (entry, consumed))
    (fitted : consumed ≤ held.length) (accepted : LeafAccepted LENS entry)
    (nonzero : entry.op ≠ 0) (noBase : entry.op &&& 16 = 0)
    (unread : List Bool) (dictionary history : List UInt8) :
    Token.Step L D dictionary history (held ++ unread) (held.drop consumed ++ unread) history true := by
  obtain ⟨symbol, valid, fields, _width, decoded⟩ :=
    accepted_query inv query fitted accepted unread
  have ending := eob_symbol valid fields nonzero noBase
  subst symbol
  exact .eob decoded

/-- Accepted length and distance queries plus their actual extra-bit reads
justify a complete copy on arbitrary input. The only distance premise is
the real decoder's bound against available dictionary and output. -/
theorem copy_step
    {lca dca : Array Code} {lo lr le doff dr de : Nat} {L D : List Nat}
    (linv : Inv LENS lca lo lr le L) (dinv : Inv DISTS dca doff dr de D)
    {held unread distanceHeld distanceUnread r2 r4 : List Bool}
    {lenEntry distEntry : Code} {lenUsed distUsed lx dx : Nat}
    (lenQuery : tableRead LENS lca lo lr
      (Zlib.Inftrees.Spec.DecodeShort.padded held) = some (lenEntry, lenUsed))
    (lenFitted : lenUsed ≤ held.length) (lenAccepted : LeafAccepted LENS lenEntry)
    (base : lenEntry.op &&& 16 ≠ 0)
    (lengthRead : readBits (lenEntry.op &&& 15).toNat (held.drop lenUsed ++ unread) = some (lx, r2))
    (distanceSource : r2 = distanceHeld ++ distanceUnread)
    (distQuery : tableRead DISTS dca doff dr
      (Zlib.Inftrees.Spec.DecodeShort.padded distanceHeld) = some (distEntry, distUsed))
    (distFitted : distUsed ≤ distanceHeld.length) (distAccepted : LeafAccepted DISTS distEntry)
    (distanceRead : readBits (distEntry.op &&& 15).toNat
      (distanceHeld.drop distUsed ++ distanceUnread) = some (dx, r4))
    (dictionary history : List UInt8)
    (fits : distEntry.val.toNat + dx ≤ (dictionary ++ history).length) :
    Token.Step L D dictionary history (held ++ unread) r4
      (copyBack dictionary (distEntry.val.toNat + dx) (lenEntry.val.toNat + lx) history) false := by
  obtain ⟨symbol, valid, fields, _width, decoded⟩ :=
    accepted_query linv lenQuery lenFitted lenAccepted unread
  obtain ⟨lower, upper, lengthBits, lengthBase⟩ := base_symbol valid fields base
  obtain ⟨dsymbol, dvalid, dfields, _dwidth, ddecoded⟩ :=
    accepted_query dinv distQuery distFitted distAccepted distanceUnread
  obtain ⟨dupper, distanceBits, distanceBase⟩ := distance_fields dvalid dfields
  rw [← distanceSource] at ddecoded
  rw [lengthBits] at lengthRead
  rw [distanceBits] at distanceRead
  rw [distanceBase] at fits
  rw [distanceBase, lengthBase]
  exact .copy decoded lower upper lengthRead ddecoded dupper distanceRead fits

#print axioms accepted_query
#print axioms literal_symbol
#print axioms base_symbol
#print axioms eob_symbol
#print axioms distance_fields
#print axioms literal_step
#print axioms eob_step
#print axioms copy_step
end Zlib.Inflate.Proofs.AcceptedToken
