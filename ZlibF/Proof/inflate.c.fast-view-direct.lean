import ZlibF.Proof.«inflate.c.fast-view-do-loop»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The direct-output branch of the actual translated `copyMatch` call. Its
distance points into already produced output, so the copy can overlap its
source and must read the output array afresh at every byte. -/
theorem FastInputPacket.copyMatch_direct_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (direct : ¬ l.dist > l.op)
    (distance : l.dist.toNat ≤ j)
    (length : 3 ≤ l.len.toNat)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result = { l with
        from_ := .ref dest (j - l.dist.toNat + l.len.toNat),
        out := .ref dest (j + l.len.toNat),
        len := UInt32.ofNat (l.len.toNat % 3) } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.cpyN l.len.toNat
          (j - l.dist.toNat) j output) ∧
      Space.ro after dest = false := by
  let sourceStart := j - l.dist.toNat
  let copied : Zlib.Inffast.L := { l with
    from_ := .ref dest sourceStart }
  have subRun : OkOn h (Zlib.Inffast.subn l.out l.dist)
      (.ref dest sourceStart) := by
    rw [outPtr]
    exact Zlib.Inffast.Proofs.subn_ok outputGet distance
      (by omega)
  have packetCopied : FastInputPacket h slow bs copied :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, after, tailRun, resultPacket,
      tailEq, tailBytes, tailWrite⟩ :=
    packetCopied.tailD_view (n := l.len.toNat) rfl length
      separate left (by rfl) outputGet
      (by dsimp [sourceStart]; omega)
      (by simpa only [copied] using outPtr)
      outputPtr outputGet outputWrite outputSize outputRoom
  have bytes : Space.get after dest = some
      (Zlib.Inffast.Proofs.cpyN l.len.toNat sourceStart j output) := by
    simpa using tailBytes
  have exactResult : result = { l with
      from_ := .ref dest (j - l.dist.toNat + l.len.toNat),
      out := .ref dest (j + l.len.toNat),
      len := UInt32.ofNat (l.len.toNat % 3) } := by
    rw [tailEq]
  have run : Zlib.Inffast.copyMatch c l h =
      .ok (result, after) := by
    unfold Zlib.Inffast.copyMatch
    simp only [direct, ite_false]
    rw [bind_ok subRun]
    change Zlib.Inffast.Proofs.tailD copied h =
      .ok (result, after)
    exact tailRun
  exact ⟨result, after, run, resultPacket, exactResult,
    bytes, tailWrite⟩

end Zlib.Inflate.Proofs
