import ZlibF.Proof.«inftrees.c.code-length-meaning»

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
set_option autoImplicit false

/-- The code-length alphabet is retained independently of the mutable lens
array. CODELENS overwrites that array while still reading the installed table.
This is a property of table contents, not a contract for a called program. -/
structure CodeLengthMeaning (ca : Array Code) (offset root : Nat) (alphabet : List Nat) : Prop where
  safe : CodeLengthTableSafe ca offset root
  acceptable : Acceptable .codeLength alphabet
  forward : ∀ (inp rest : List Bool) (symbol : Nat),
    decodeSym alphabet inp = some (symbol, rest) →
    ∃ value suffix entry,
      readBits root (DecodeShort.padded inp) = some (value, suffix) ∧
      ca[offset + value]? = some entry ∧ entry.op = 0 ∧ entry.val.toNat = symbol ∧
      entry.bits.toNat = alphabet.getD symbol 0 ∧
      entry.bits.toNat ≤ inp.length ∧ rest = inp.drop entry.bits.toNat
  sound : ∀ (inp lookahead : List Bool) (cell : Nat) (entry : Code),
    readBits root (DecodeShort.padded inp) = some (cell, lookahead) →
    ca[offset + cell]? = some entry → entry.op = 0 → entry.bits.toNat ≤ inp.length →
    ∃ symbol, symbol < 19 ∧ entry.val.toNat = symbol ∧
      entry.bits.toNat = alphabet.getD symbol 0 ∧
      decodeSym alphabet inp = some (symbol, inp.drop entry.bits.toNat)

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)` for CODES.
The actual constructor establishes the persistent content property from its
original precondition. Both directions refer to one actual returned array. -/
theorem inflate_table_establishes_code_length_meaning
    {h : Heap} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h CODES rl ol codes rc oc bits rw ow) :
    ∃ result after,
      C.run (inflate_table CODES (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      Result h rw rc ow oc (capOf CODES) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        CodeLengthMeaning ca oc result.2.2.toNat (lensOf pre.f codes.toNat)) := by
  obtain ⟨result, after, run, frame, forward⟩ := inflate_table_codes_format_short_forward pre
  obtain ⟨result2, after2, run2, _frame2, sound⟩ := inflate_table_codes_format_short_sound pre
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  obtain ⟨result3, after3, run3, _frame3, ret, _content⟩ :=
    inflate_table_content h CODES rl ol codes rc oc bits rw ow pre
  have same := Except.ok.inj (run3.symm.trans run)
  cases same
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  obtain ⟨ca, get, safety, readForward⟩ := forward success
  obtain ⟨otherArray, otherGet, _otherSafety, readSound⟩ := sound success
  have arrays : otherArray = ca := Option.some.inj (otherGet.symm.trans get)
  subst otherArray
  exact ⟨ca, get, safety, (acc_iff CODES pre.f codes.toNat pre.hf15).mp (ret.1 success),
    readForward, readSound⟩

#print axioms inflate_table_establishes_code_length_meaning
end Zlib.Inftrees.Proofs
