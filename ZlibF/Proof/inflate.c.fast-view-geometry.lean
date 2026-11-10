import ZlibF.Proof.«inflate.c.fast-view-window-data»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast-loop output guard reserves enough space for every
decoded match, whose length is at most 258 bytes. -/
theorem fast_output_room_of_guard
    {h : Heap} {slow : IL} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx} {dest : BRef}
    {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (avail : 258 ≤ slow.left.toNat)
    (length : l.len.toNat ≤ 258)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    j ≤ output.size ∧
      (oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat) := by
  have endBound : oo + slow.left.toNat - 257 ≤ output.size := by omega
  have currentBound : j ≤ output.size := by
    by_cases inside : j ≤ output.size
    · exact inside
    · rw [outPtr, endPtr] at guard
      simp [C.run, Ptr.lt, outputGet, inside] at guard
  have run := Ptr.lt_ok (r := dest) (a := output)
    outputGet currentBound endBound
  rw [outPtr, endPtr] at guard
  change (Ptr.lt (.ref dest j)
    (.ref dest (oo + slow.left.toNat - 257))) h = .ok (true, h) at guard
  rw [run] at guard
  have strict : j < oo + slow.left.toNat - 257 := by
    simpa using guard
  exact ⟨currentBound, current, by omega⟩

/-- The public output counter bounds the pointer difference from the
beginning of this call at every live fast-loop output guard. -/
theorem fast_begin_span_of_guard
    {h : Heap} {slow : IL} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx} {dest : BRef}
    {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (avail : 258 ≤ slow.left.toNat)
    (length : l.len.toNat ≤ 258)
    (count : slow.left.toNat ≤ slow.out_.toNat)
    (made : slow.out_.toNat - slow.left.toNat ≤ oo)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let bg := oo - (slow.out_.toNat - slow.left.toNat)
    bg ≤ j ∧ j - bg < 2 ^ 32 := by
  have geometry := fast_output_room_of_guard outPtr endPtr
    outputGet outputSize current avail length guard
  have width := UInt32.toNat_lt slow.out_
  dsimp only
  omega

/-- The `out - beg` pointer difference used by the translated distance
branch counts bytes produced since the beginning of this call. -/
theorem fast_produced_of_diff
    {h : Heap} {dest : BRef} {output : Array UInt8}
    {bg j : Nat} {d : Int64} {l : Zlib.Inffast.L}
    (outputGet : Space.get h dest = some output)
    (currentBound : j ≤ output.size)
    (beginBound : bg ≤ output.size)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (diff : C.run (Ptr.diff (.ref dest j) (.ref dest bg)) h =
      .ok (d, h))
    (opEq : l.op = d.toUInt64.toUInt32) :
    l.op.toNat = j - bg ∧ l.op.toNat ≤ j := by
  have intEq : (j : Int) - (bg : Int) = ((j - bg : Nat) : Int) := by
    omega
  have run := Ptr.diff_ok (r := dest) (a := output)
    outputGet currentBound beginBound
    (by omega : -(2 ^ 63 : Int) ≤ (j : Int) - (bg : Int) ∧
      (j : Int) - (bg : Int) < 2 ^ 63)
  change (Ptr.diff (.ref dest j) (.ref dest bg)) h =
    .ok (d, h) at diff
  rw [run] at diff
  have dEq : d = Int64.ofInt ((j : Int) - (bg : Int)) := by
    injection diff with eq
    exact congrArg Prod.fst eq.symm
  rw [intEq] at dEq
  have produced : l.op.toNat = j - bg := by
    rw [opEq, dEq]
    exact Zlib.Inffast.Proofs.i64_toU32 _ span
  exact ⟨produced, by omega⟩

/-- The translated distance-copy suffix uses the real pointer difference
and then executes `copyMatch` on the general caller byte view. -/
theorem FastInputPacket.copy_match_after_diff
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (good : Good h r zs z s)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (sane : s.sane ≠ 0)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (range : CallerRange h r slow.put slow.left.toNat true)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ =
      .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let atCopy : Zlib.Inffast.L :=
      { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }
    ∃ result after,
      C.run (do
        let d ← Ptr.diff l.out c.beg
        Zlib.Inffast.copyMatch c { l with op := d.toUInt64.toUInt32 }) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.againD = atCopy.againD ∧
      result.againL = atCopy.againL ∧
      ((result.broke = true ∧
        ∃ i, after = setI
          (r.put h { z with msg := .ref (.str i) 0 }) zs
          { s with mode := BAD } ∧
          Space.get after dest = some output ∧
          Space.ro after dest = false) ∨
       (result.broke = atCopy.broke ∧
        ∃ array,
          result.out = .ref dest (j + l.len.toNat) ∧
          Space.get after dest = some array ∧
          array.size = output.size ∧
          Space.ro after dest = false)) := by
  have geometry := fast_output_room_of_guard outPtr endPtr
    outputGet outputSize current avail length.2 guard
  have currentBound : j ≤ output.size := geometry.1
  have outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat := geometry.2
  have beginBound : bg ≤ output.size := by omega
  have diffRun : C.run (Ptr.diff l.out c.beg) h =
      .ok (Int64.ofInt ((j - bg : Nat) : Int), h) := by
    rw [outPtr, begPtr]
    have run := Ptr.diff_ok (r := dest) (a := output)
      outputGet currentBound beginBound
      (by omega : -(2 ^ 63 : Int) ≤ (j : Int) - (bg : Int) ∧
        (j : Int) - (bg : Int) < 2 ^ 63)
    have intEq : (j : Int) - (bg : Int) = ((j - bg : Nat) : Int) := by
      omega
    change (Ptr.diff (.ref dest j) (.ref dest bg)) h =
      .ok (Int64.ofInt ((j : Int) - (bg : Int)), h) at run
    simpa only [C.run, intEq] using run
  let atCopy : Zlib.Inffast.L :=
    { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }
  have produced : atCopy.op.toNat ≤ j := by
    exact (fast_produced_of_diff (l := atCopy) outputGet
      currentBound beginBound beginLe span
      (by simpa only [outPtr, begPtr] using diffRun) rfl).2
  have copyPacket : FastInputPacket h slow bs atCopy :=
    packet.with_op _
  have copyLength : 3 ≤ atCopy.len.toNat := by
    simpa only [atCopy] using length.1
  obtain ⟨result, after, copyRun, packetAfter, againD,
    againL, outcome⟩ :=
    copyPacket.copyMatch_view_of_good good streamPtr statePtr
      whaveEq wsizeEq wnextEq windowEq sane separate left
      copyLength range outPtr outputPtr outputGet outputWrite
      outputSize outputRoom produced
  refine ⟨result, after, ?_, packetAfter, againD,
    againL, ?_⟩
  · change (do
      let d ← Ptr.diff l.out c.beg
      Zlib.Inffast.copyMatch c { l with op := d.toUInt64.toUInt32 }) h =
        .ok (result, after)
    rw [bind_ok (by simpa only [C.run] using diffRun)]
    exact copyRun
  · simpa only [atCopy] using outcome

end Zlib.Inflate.Proofs
