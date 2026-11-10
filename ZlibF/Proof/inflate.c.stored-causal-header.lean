import ZlibF.Proof.«inflate.c.stored-generic-phase»
import ZlibF.Proof.«inflate.c.global-credited-input»

namespace Zlib.Inflate.Proofs.StoredCausal
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.StoredHistory Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.StoredGeneric Zlib.Inflate.Proofs.CausalInput
set_option autoImplicit false

/-- Only the real pulled byte prefix contributes to the header source.
Unconsumed caller bytes cancel out of the actual macro's stream equation. -/
theorem header_held_source_slice
    {l current : IL} {bs : List UInt8} {used : Nat}
    (source : stream current (bs.drop used) = (stream l bs).drop ((stream l bs).length % 8)) :
    let raw := natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)
    raw.drop (raw.length % 8) = natBits current.bits.toNat current.hold.toNat ∧
    raw = raw.take (raw.length % 8) ++ natBits current.bits.toNat current.hold.toNat ∧
    (raw.take (raw.length % 8)).length < 8 := by
  dsimp only
  let raw := natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)
  have split : stream l bs = raw ++ bytesBits (bs.drop used) := by
    dsimp only [raw]
    unfold stream
    rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
  have modulo : (raw ++ bytesBits (bs.drop used)).length % 8 = raw.length % 8 := by
    rw [List.length_append, bytesBits_length]
    omega
  rw [split, modulo, List.drop_append_of_le_length (Nat.mod_le _ _)] at source
  change natBits current.bits.toNat current.hold.toNat ++ bytesBits (bs.drop used) =
    raw.drop (raw.length % 8) ++ bytesBits (bs.drop used) at source
  have aligned := (List.append_cancel_right source).symm
  refine ⟨aligned, ?_, ?_⟩
  · rw [← aligned, List.take_append_drop]
  · rw [List.length_take]
    have small := Nat.mod_lt raw.length (by decide : 0 < 8)
    omega

/-- The actual 32-bit held word, viewed without unread caller bytes,
exposes the exact independent LEN/NLEN reads and the literal C guard. -/
theorem held_header_fields
    {h : Heap} {l : IL} {bs : List UInt8}
    (B : BitInv h l bs) (bits : l.bits.toNat = 32) :
    ∃ len nlen middle,
      readBits 16 (natBits l.bits.toNat l.hold.toNat) = some (len, middle) ∧
      readBits 16 middle = some (nlen, []) ∧
      (l.hold.toUInt32 &&& 0xffff).toNat = len ∧ len < 65536 ∧ nlen < 65536 ∧
      ((((l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64))) = false) ↔
        nlen = 65535 - len) := by
  let held : IL := {l with have_ := 0}
  have heldInv : BitInv h held [] := ⟨rfl, Or.inl rfl, B.hold_lt⟩
  obtain ⟨len, nlen, middle, first, second, low, small, high, accepted⟩ :=
    stored_header_word_fields heldInv bits
  refine ⟨len, nlen, middle, ?_, ?_, low, small, high, accepted⟩
  · simpa only [stream, bytesBits_nil, List.append_nil] using first
  · simpa only [bytesBits_nil] using second

/-- A completed actual accepted header word, independent of any future
payload. It records exactly the two source reads and complement check. -/
def HeaderWord (word : List Bool) (len : Nat) : Prop :=
  word.length = 32 ∧ len < 65536 ∧ ∃ nlen middle,
    readBits 16 word = some (len, middle) ∧ readBits 16 middle = some (nlen, []) ∧
    nlen = 65535 - len

/-- Actual arbitrary STORED header execution: exhausted read, checked BAD,
or accepted LEN/NLEN and the true COPY_ source cut. No Body, valid future,
expected payload bytes or successful callee result is assumed. Credited
input contains only actually pulled bytes and the exact held remainder. -/
theorem arbitrary_header_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs input : List UInt8} {committed : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (packet : DispatchBuffers h r l bs) (mode : s.mode = STORED) (bits : l.bits.toNat ≤ 39)
    (credited : Credited input committed l.bits l.hold) :
    ∃ outcome current used,
      runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((outcome, current), h) ∧
      used ≤ bs.length ∧ BitInv h current (bs.drop used) ∧ current.bits.toNat % 8 = 0 ∧
      let raw := natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used)
      let padding := raw.take (raw.length % 8)
      padding.length < 8 ∧ raw = padding ++ natBits current.bits.toNat current.hold.toNat ∧
      Credited (input ++ bs.take used) (committed ++ padding) current.bits current.hold ∧
      ((outcome = .error Ex.leave ∧
        runX (inflate_STORED c) l h = .ok ((.error Ex.leave, current), h)) ∨
       (outcome = .ok () ∧ current.bits.toNat = 32 ∧
        ∃ len nlen middle,
          readBits 16 (natBits current.bits.toNat current.hold.toNat) = some (len, middle) ∧
          readBits 16 middle = some (nlen, []) ∧ len < 65536 ∧ nlen < 65536 ∧
          ((nlen ≠ 65535 - len ∧ ∃ i,
            strTable[i]? = some "invalid stored block lengths" ∧
            runX (inflate_STORED c) l h = .ok ((.ok (), current), badHeap h r zs z s i)) ∨
           (nlen = 65535 - len ∧
            let ready := {s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_}
            let after := setI h zs ready
            let regs := {current with hold := 0, bits := 0}
            HeaderWord (natBits current.bits.toNat current.hold.toNat) len ∧
            ready.length.toNat = len ∧ DefaultOriginState after r zs z ready ∧
            DispatchBuffers after r regs (bs.drop used) ∧
            Credited (input ++ bs.take used) (committed ++ raw) regs.bits regs.hold ∧
            runX (inflate_STORED c) l h =
              runX (if c.flush == Z_TREES then (throw Ex.leave : X Unit) else inflate_COPY_ c) regs after)))) := by
  obtain ⟨outcome, current, used, macroRun, usedBound, inv, source, waiting, normal⟩ :=
    stored_STORED_header_prefix E origin packet mode bits
  obtain ⟨_aligned, slice, paddingBound⟩ := header_held_source_slice source
  have credit := credited.append slice
  have currentAligned : current.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length _aligned
    simp only [List.length_drop, natBits_length] at lengths
    omega
  have kinds : outcome = .ok () ∨ outcome = .error Ex.leave := by
    obtain ⟨aligned, _, _⟩ := BYTEBITS_inv packet.bits
    obtain ⟨value, regs, count, pull, _, _, _, _, _, _, _, _, _, allowed, _⟩ :=
      NEEDBITS_run_cursor aligned 32 (by decide)
    have actual : runX (do BYTEBITS; NEEDBITS 32) l h = .ok ((value, regs), h) := by
      rw [runX_bind, BYTEBITS_run]; exact pull
    have eq : outcome = value := congrArg (fun p => p.1.1) (Except.ok.inj (macroRun.symm.trans actual))
    rw [eq]; exact allowed
  refine ⟨outcome, current, used, macroRun, usedBound, inv, currentAligned, paddingBound, slice, credit, ?_⟩
  rcases kinds with completed | leave
  · have completedInfo := normal completed
    obtain ⟨word32, len0, nlen0, middle0, _first0, _second0, _small0, _high0, accepted0, enter⟩ := completedInfo
    obtain ⟨len, nlen, middle, first, second, low, small, high, accepted⟩ := held_header_fields inv word32
    refine Or.inr ⟨completed, word32, len, nlen, middle, first, second, small, high, ?_⟩
    by_cases complement : nlen = 65535 - len
    · have pass := accepted.mpr complement
      obtain ⟨currentJ, currentPacket, length0, sourceCut⟩ := enter (accepted0.mp pass)
      have wordCert : HeaderWord (natBits current.bits.toNat current.hold.toNat) len :=
        ⟨by rw [natBits_length, word32], small, nlen, middle, first, second, complement⟩
      have fullCredit : Credited (input ++ bs.take used)
          (committed ++ (natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used))) 0 0 := by
        apply credited.append
        simp only [UInt32.toNat_zero, natBits, List.append_nil]
      exact Or.inr ⟨complement, wordCert, low, currentJ, currentPacket, fullCredit, sourceCut⟩
    · have bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true := by
        cases value : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64)))
        · exact False.elim (complement (accepted.mp value))
        · rfl
      have pull := macroRun
      rw [completed, runX_bind, BYTEBITS_run] at pull
      exact Or.inl ⟨complement, inflate_STORED_bad E l current pull bad⟩
  · exact Or.inl ⟨leave, waiting leave⟩

#print axioms header_held_source_slice
#print axioms held_header_fields
#print axioms arbitrary_header_classifier
end Zlib.Inflate.Proofs.StoredCausal
