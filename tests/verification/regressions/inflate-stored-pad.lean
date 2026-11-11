import ZlibF.Proof.«inflate.c.meaning»

open ZlibF.Spec Zlib.Inflate.Proofs

/-! `inflate_STORED` drops the padding to the byte boundary (`BYTEBITS`) before
it waits for `LEN` and `NLEN`. A raw inflate (windowBits -15) of a stream whose
stored block header ends at bit 32805 stopped with 32808 bits consumed and the
mode `STORED`, as recorded by `tests/goals/inflate-meaning-body`. Before
`storedPad` the grammar had no position there. The smallest such position: a
final stored block at the start of the data, its three header bits, and the
five pad bits. -/
namespace StoredPadRegression

/-- The header and its pad are a parse position of a stored block. -/
theorem stored_after_pad :
    DeflateParsed [] ([true, false, false] ++ List.replicate 5 false) ⟨[], true, .storedHeader⟩ := by
  have header : DeflateParsed [] ([] ++ [true, false, false]) ⟨[], true, .storedHeader⟩ :=
    DeflateParsed.storedStart DeflateParsed.start
  exact DeflateParsed.storedPad header (by decide)

end StoredPadRegression

#print axioms StoredPadRegression.stored_after_pad
