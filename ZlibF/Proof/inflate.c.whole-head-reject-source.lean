import ZlibF.Proof.«inflate.c.whole-header-guard-arithmetic»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- An invalid actual two-byte prefix cannot be repaired by unread bytes. -/
theorem invalid_header_rejects {log : DataLog} {cmf flg : UInt8}
    (bytes : log.input = [cmf, flg]) (invalid : ¬ Zlib.HeaderOK cmf flg) : Rejects log := by
  intro future output decoded
  obtain ⟨a, b, pre, suffix, source, valid, _plain, _dict⟩ := decoded
  rw [bytes] at source
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at source
  obtain ⟨rfl, rfl, _⟩ := source
  exact invalid valid

structure HeadBadSource (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (l : IL) (bs : List UInt8) (log : DataLog)
    (event : ByteWordRead h l bs log.input [] 16) where
  regs : IL
  message : Nat
  committed : List Bool
  actual : runX (inflate_dispatch c) l h = .ok ((.ok (), regs), badHeap h r zs z s message)
  frame : HeadRegFrame event.regs regs
  inv : BitInv h regs (bs.drop event.used)
  bits : regs.bits.toNat ≤ 16
  credited : CausalInput.Credited (log.input ++ bs.take event.used) committed regs.bits regs.hold
  rejects : Rejects (readLog log bs event.used)

/-- The actual complete default HEAD branches are accepted or real BAD;
all rejected branches retain their exact held-bit credit, including DROP4. -/
theorem head_normal_source_classification
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {log : DataLog} {cmf flg : UInt8}
    (E : Env c h r zs z s) (origins : WrapperOrigins s) (headerNone : s.head = none)
    (mode : s.mode = HEAD) (event : ByteWordRead h l bs log.input [] 16)
    (normal : event.outcome = .ok ()) (bytes : log.input ++ bs.take event.used = [cmf, flg])
    (word : event.regs.hold.toNat = cmf.toNat + 256 * flg.toNat) :
    Zlib.HeaderOK cmf flg ∨ Nonempty (HeadBadSource c h r zs z s l bs log event) := by
  obtain ⟨headerEq, methodEq, windowEq⟩ := header_guard_arithmetic origins.wrapped word
  have width : event.regs.bits.toNat = 16 := event.normal normal
  have sourceCut := (inflate_dispatch_HEAD E l mode).trans
    (head_read_source_cut E origins.wrapped headerNone (by simpa only [normal] using event.actual))
  have rejected (regs : IL) (i : Nat) (committed : List Bool)
      (actual : runX (headDefaultCheck c s event.regs) event.regs h = .ok ((.ok (), regs), badHeap h r zs z s i))
      (frame : HeadRegFrame event.regs regs) (inv : BitInv h regs (bs.drop event.used))
      (bits : regs.bits.toNat ≤ 16)
      (credit : CausalInput.Credited (log.input ++ bs.take event.used) committed regs.bits regs.hold)
      (invalid : ¬ Zlib.HeaderOK cmf flg) : Nonempty (HeadBadSource c h r zs z s l bs log event) :=
    ⟨⟨regs, i, committed, sourceCut.trans actual, frame, inv, bits, credit, invalid_header_rejects bytes invalid⟩⟩
  by_cases header : headHeaderRejected s event.regs = true
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_header E event.regs header
    right
    exact rejected event.regs i [] actual rfl event.inv (by omega) event.credited (fun valid => by
      have pass := (valid_header_guards valid origins.wrapped word).1
      rw [header] at pass; cases pass)
  have headerFalse : headHeaderRejected s event.regs = false := by cases eq : headHeaderRejected s event.regs <;> simp_all
  by_cases method : headMethodRejected event.regs = true
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_method E event.regs headerFalse method
    right
    exact rejected event.regs i [] actual rfl event.inv (by omega) event.credited (fun valid => by
      have pass := (valid_header_guards valid origins.wrapped word).2.1
      rw [method] at pass; cases pass)
  have methodFalse : headMethodRejected event.regs = false := by cases eq : headMethodRejected event.regs <;> simp_all
  by_cases window : 15 < (headWindowRegs event.regs).len.toNat
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_window E event.regs headerFalse methodFalse window
    obtain ⟨inv, _source, count⟩ := DROPBITS_inv event.inv 4 (by change 4 ≤ event.regs.bits.toNat; omega) (by decide)
    have held : natBits event.regs.bits.toNat event.regs.hold.toNat =
        natBits 4 event.regs.hold.toNat ++ natBits (headWindowRegs event.regs).bits.toNat (headWindowRegs event.regs).hold.toNat := by
      have split := natBits_add 4 12 event.regs.hold.toNat
      simpa only [headWindowRegs, width, count, shr64_toNat event.regs.hold 4 (by decide), UInt32.toNat_ofNat, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] using split
    have credit : CausalInput.Credited (log.input ++ bs.take event.used) (natBits 4 event.regs.hold.toNat)
        (headWindowRegs event.regs).bits (headWindowRegs event.regs).hold := by
      change bytesBits _ = _ ++ _
      have beforeCredit := event.credited
      change bytesBits _ = [] ++ _ at beforeCredit
      have beforeCredit0 : bytesBits (log.input ++ bs.take event.used) = natBits event.regs.bits.toNat event.regs.hold.toNat := by
        simpa only [List.nil_append] using beforeCredit
      exact beforeCredit0.trans held
    right
    exact rejected (headWindowRegs event.regs) i (natBits 4 event.regs.hold.toNat) actual rfl
      ⟨inv.have_eq, inv.next, inv.hold_lt⟩ (by change (event.regs.bits-4).toNat ≤ 16; rw [count]; omega) credit
      (fun valid => by have pass := (valid_header_guards valid origins.wrapped word).2.2.1; omega)
  · left
    rw [headerEq] at headerFalse
    rw [methodEq] at methodFalse
    rw [windowEq] at window
    have checksum : (cmf.toNat * 256 + flg.toNat) % 31 = 0 := by simpa using headerFalse
    have method : cmf.toNat % 16 = 8 := by simpa using methodFalse
    exact ⟨method, by omega, checksum⟩

#print axioms invalid_header_rejects
#print axioms head_normal_source_classification
end Zlib.Inflate.Proofs.WholeWrapper
