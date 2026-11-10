import ZlibF.Proof.«inflate.c.later-early-waits»
namespace Zlib.Inflate.Proofs.LaterHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue Zlib.Inflate.Proofs.HeaderPhaseView
open ZlibF.Math.InflateHuffmanBodyContext
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Every current TABLE prefix is classified, including repeated count,
alphabet and code-length exhaustion. The independent premise is header
syntax alone and asserts no payload Symbols or completion. -/
theorem table_header_exhaustive
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {future payload : List Bool} {L D : List Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TABLE) (incoming : l.bits.toNat ≤ 39) (allocator : DefAlloc z)
    (credit : AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (header : Header 2 (stream l bs ++ future) L D payload) :
    Nonempty (EarlyHeaderWait c h r zs z s l bs credited history) ∨
    Nonempty (GeneralCodeWait c h r zs z s l bs future payload L D credited history) ∨
    Nonempty (GeneralPayloadPacket c h callHeap r zs z s l bs future payload L D credited history) := by
  by_cases short : (stream l bs).length < 14
  · exact Or.inl (table_short_wait E origin buffers mode allocator credit dictionary short)
  have available : 14 ≤ (stream l bs).length := by omega
  obtain ⟨pulled, tableUsed, pull, bound, B, early⟩ := table_lens_short_wait E origin buffers mode allocator credit dictionary available header
  by_cases shortAlphabet : (stream (tableRegs pulled) (bs.drop tableUsed)).length < 3 * (tableCounts s pulled.hold).ncode.toNat
  · exact Or.inl (early shortAlphabet)
  obtain ⟨pulled0, tableUsed0, pull0, bound0, B0, entry⟩ := table_code_entry E origin buffers mode available header
  rw [pull] at pull0
  cases pull0
  have same : tableUsed0 = tableUsed := by
    have a := B0.have_eq
    have b := B.have_eq
    simp only [List.length_drop] at a b
    omega
  subst tableUsed0
  obtain ⟨e⟩ := entry (by omega)
  exact Or.inr (e.wait_or_payload E origin allocator credit dictionary incoming main)

theorem GeneralPayloadPacket.bits39
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future payload : List Bool} {L D : List Nat} {credited history : List UInt8}
    (p : GeneralPayloadPacket c h callHeap r zs z s l bs future payload L D credited history) : p.boundary.regs.bits.toNat ≤ 39 := by
  have := p.boundary.bits
  have := p.entry.bits
  have := p.incoming
  omega

/-- The actual completed tag source gives current-input BFINAL/BTYPE
reads, even when a valid-header argument originally carried future bits. -/
theorem DynamicBlockEntry.current_tag
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {future payload : List Bool} {L D : List Nat} {final : Nat}
    (e : DynamicBlockEntry c h r zs z s l bs future payload L D credited history final) :
    ∃ middle,
      readBits 1 (stream l bs) = some (final, middle) ∧
      readBits 2 middle = some (2, stream e.regs (bs.drop e.used)) := by
  have firstWord := ZlibF.Math.CodeLengthPrefix.read_word e.first
  have secondWord := ZlibF.Math.CodeLengthPrefix.read_word e.second
  have sourceWord : stream l bs ++ future =
      (bitsOfNat final 1 ++ bitsOfNat 2 2 ++ stream e.regs (bs.drop e.used)) ++ future := by
    rw [firstWord.2, secondWord.2, ← e.source]
    simp only [List.append_assoc]
  have source : stream l bs = bitsOfNat final 1 ++ (bitsOfNat 2 2 ++ stream e.regs (bs.drop e.used)) := by
    have cancel := List.append_inj_left' sourceWord rfl
    simpa only [List.append_assoc] using cancel
  refine ⟨bitsOfNat 2 2 ++ stream e.regs (bs.drop e.used), ?_, ?_⟩
  · rw [source]
    simpa only [Nat.mod_eq_of_lt e.finalBound, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
      readBits_bitsOfNat 1 1 final (bitsOfNat 2 2 ++ stream e.regs (bs.drop e.used)) (Nat.le_refl _)
  · simpa only [Nat.sub_self, bitsOfNat_zero, List.nil_append] using
      readBits_bitsOfNat 2 2 2 (stream e.regs (bs.drop e.used)) (Nat.le_refl _)

/-- The original actual TYPE loop is preserved through all dynamic header
cases. On completion its current Header and exact parsed BFINAL stay
attached to the payload packet, rather than being dropped by the join. -/
theorem DynamicBlockEntry.header_exhaustive
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {future payload : List Bool} {L D : List Nat} {final : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (buffers : DispatchBuffers h r l bs)
    (incoming : l.bits.toNat ≤ 39)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (e : DynamicBlockEntry c h r zs z s l bs future payload L D credited history final) :
    Nonempty (EarlyHeaderWait c (setI h zs e.state) r zs z e.state e.regs (bs.drop e.used) credited history) ∨
    Nonempty (GeneralCodeWait c (setI h zs e.state) r zs z e.state e.regs (bs.drop e.used) future payload L D credited history) ∨
    ∃ p : GeneralPayloadPacket c (setI h zs e.state) callHeap r zs z e.state e.regs (bs.drop e.used) future payload L D credited history,
      p.boundary.state.last.toInt = (final : Int) := by
  have currentE : Env c (setI h zs e.state) r zs z e.state := ⟨E.strm, E.st, e.origin.good.live.hz, e.origin.good.live.hs⟩
  have actualMain := e.main_cut E origin buffers incoming main
  rcases table_header_exhaustive currentE e.origin e.buffers e.mode e.bits e.allocator e.credit e.dictionary actualMain e.header with early | code | ready
  · exact Or.inl early
  · exact Or.inr (Or.inl code)
  · obtain ⟨p⟩ := ready
    exact Or.inr (Or.inr ⟨p, by rw [p.last, e.last]; exact final_flag_toInt e.finalBound⟩)

#print axioms table_header_exhaustive
#print axioms GeneralPayloadPacket.bits39
#print axioms DynamicBlockEntry.current_tag
#print axioms DynamicBlockEntry.header_exhaustive
end Zlib.Inflate.Proofs.LaterHeader
