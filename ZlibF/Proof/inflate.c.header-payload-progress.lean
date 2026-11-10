import ZlibF.Proof.«inflate.c.header-payload-lens-public»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The stored phase's exhaustive valid-source consumer uses the same
HeaderPacketProgress outcome as HEAD, TYPE and TABLE. All actual partial waits
and completed payload-table continuations are derived, not assumed. -/
theorem Meaning.lens_header_packet_progress
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (scope : HeaderDataTrace.PlatformScope history) (before : Meaning .lens h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ (z : ZStream) (s : InflateState) (record : CountMeta) (received : List Bool),
      r.get h = some z ∧ h.istates zs = some s ∧ View readCounts record (bytesBits log.input) received ∧
      ∀ (future codeInput payloadInput rest : List Bool) (dict prior decodedOutput : List UInt8) (alphabet decoded : List Nat),
        readCodeLenLens s.ncode.toNat ((received ++ bytesBits input) ++ future) = some (alphabet, codeInput) →
        Acceptable .codeLength alphabet → CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) [] codeInput payloadInput decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        Symbols (decoded.take s.nlen.toNat) (decoded.drop s.nlen.toNat) dict prior payloadInput rest decodedOutput →
        HeaderPacketProgress h after r zs log input output used flush rc future rest dict prior decodedOutput := by
  obtain ⟨z, state, record, received, getZ, getS, view, consume⟩ := before.lens_public_packet_exhaustive scope observed accepted
  refine ⟨z, state, record, received, getZ, getS, view, ?_⟩
  intro future codeInput payloadInput rest dict prior decodedOutput alphabet decoded read validAlphabet parsed eob validL validD symbols
  rcases consume future codeInput payloadInput rest dict prior decodedOutput alphabet decoded read validAlphabet parsed eob validL validD symbols with waitLens | waitCode | payload
  · exact Or.inr (Or.inr (Or.inr (Or.inl waitLens)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl waitCode))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr payload))))

/-- The stored phase's exhaustive valid-source consumer uses the same
HeaderPacketProgress outcome as HEAD, TYPE and TABLE. All actual partial waits
and completed payload-table continuations are derived, not assumed. -/
theorem Meaning.code_header_packet_progress
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (scope : HeaderDataTrace.PlatformScope history) (before : Meaning .code h r zs log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0)) :
    ∃ (z : ZStream) (s : InflateState) (record : AlphabetMeta) (received : List Bool),
      r.get h = some z ∧ h.istates zs = some s ∧
      View readAlphabet record (bytesBits log.input) received ∧
      ∀ (future payloadInput rest : List Bool) (dict prior decodedOutput : List UInt8) (decoded : List Nat),
        CodeLens record.alphabet (s.nlen.toNat + s.ndist.toNat) [] ((received ++ bytesBits input) ++ future) payloadInput decoded →
        HasEndOfBlock (decoded.take s.nlen.toNat) → Acceptable .litLen (decoded.take s.nlen.toNat) →
        Acceptable .dist (decoded.drop s.nlen.toNat) →
        Symbols (decoded.take s.nlen.toNat) (decoded.drop s.nlen.toNat) dict prior payloadInput rest decodedOutput →
        HeaderPacketProgress h after r zs log input output used flush rc future rest dict prior decodedOutput := by
  obtain ⟨z, state, record, received, getZ, getS, view, consume⟩ := before.code_public_packet_exhaustive scope observed accepted
  refine ⟨z, state, record, received, getZ, getS, view, ?_⟩
  intro future payloadInput rest dict prior decodedOutput decoded parsed eob validL validD symbols
  rcases consume future payloadInput rest dict prior decodedOutput decoded parsed eob validL validD symbols with waitCode | payload
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl waitCode))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr payload))))

#print axioms Meaning.lens_header_packet_progress
#print axioms Meaning.code_header_packet_progress
end Zlib.Inflate.Proofs.HeaderPhaseView
