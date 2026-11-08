import ZlibF.Proof.«inflate.c.fast-view-geometry»
import ZlibF.Proof.«inflate.c.default-byte-view»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A same-size replacement of a caller byte view has the public frame
whenever bytes outside the caller's writable interval are unchanged. -/
theorem output_view_buffer_frame
    {h : Heap} {pointer : BPtr} {dest : BRef}
    {old updated : Array UInt8} {oo count : Nat}
    (outputPtr : pointer = .ref dest oo)
    (outputGet : Space.get h dest = some old)
    (outputWrite : Space.ro h dest = false)
    (size : updated.size = old.size)
    (outside : ∀ k, k < oo ∨ oo + count ≤ k →
      updated[k]? = old[k]?) :
    BufferFrame h (Space.put h dest updated)
      (fun _ => False) [⟨pointer, count⟩] := by
  have restored : restoreRegions h (Space.put h dest updated)
      [⟨pointer, count⟩] = h := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil,
      outputPtr, outputGet]
    rw [byte_view_put_put outputGet outputWrite]
    exact byte_view_put_self outputGet outputWrite
  constructor
  · rw [restored]
    simp [Frame]
  · intro region member ref off array ptr get
    have regionEq : region = ⟨pointer, count⟩ := by
      simpa using member
    subst region
    rw [outputPtr] at ptr
    cases ptr
    have arrayEq : array = old :=
      Option.some.inj (get.symm.trans outputGet)
    subst array
    refine ⟨updated, byte_view_get_put outputGet outputWrite _,
      size, ?_⟩
    intro k _ notCovered
    apply outside
    by_cases lower : k < oo
    · exact Or.inl lower
    · by_cases upper : oo + count ≤ k
      · exact Or.inr upper
      · have covered : ∃ region' : Region,
            region' ∈ [⟨pointer, count⟩] ∧
            region'.covers dest k := by
          refine ⟨⟨pointer, count⟩, by simp, ?_⟩
          change ∃ start, pointer = .ref dest start ∧
            start ≤ k ∧ k < start + count
          exact ⟨oo, outputPtr, by omega, by omega⟩
        exact False.elim (notCovered covered)

/-- One actual fast match-copy byte preserves the default reachable-state
invariant, even when caller input and output occupy disjoint slices of one
byte object. The exact heap update is retained for loop composition. -/
theorem FastInputPacket.copy1_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {source dest : BRef} {saved output : Array UInt8}
    {sourceOff oo j : Nat}
    (fromPtr : l.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceBound : sourceOff < saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat) :
    let updated := output.set! j saved[sourceOff]
    let after := Space.put h dest updated
    let next : Zlib.Inffast.L := { l with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    C.run (Zlib.Inffast.copy1 l) h = .ok (next, after) ∧
      FastInputPacket after slow bs next ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      Space.get after dest = some updated ∧
      (∀ k, k < j ∨ j + 1 ≤ k → updated[k]? = output[k]?) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  have executed := packet.copy1_view buffers.separate left fromPtr
    sourceGet sourceBound outPtr outputPtr outputGet outputWrite
    outputSize inside
  have privateWindow := callerRange_private_window invariant.good
    buffers.output.range outputPtr
  have updatedSize : (output.set! j saved[sourceOff]).size =
      output.size := by simp
  have current := invariant.byte_view_put outputGet outputWrite
    privateWindow _ updatedSize
  have sizes := byte_view_sizes_put outputGet outputWrite _ updatedSize
  have readonly : ∀ ref : BRef,
      Space.ro (Space.put h dest (output.set! j saved[sourceOff])) ref =
        Space.ro h ref := by
    intro ref
    exact byte_view_ro_write h dest _ ref
  have inputRange := callerRange_capacity invariant.good current.good
    rfl sizes readonly buffers.input
  have outputRange := callerRange_capacity invariant.good current.good
    rfl sizes readonly buffers.output.range
  have nextBuffers : DispatchBuffers
      (Space.put h dest (output.set! j saved[sourceOff]))
      r slow bs :=
    ⟨inputRange,
      ⟨outputRange, buffers.output.nonnull,
        buffers.output.count, buffers.output.produced⟩,
      buffers.separate, executed.2.source⟩
  have outsideByte : ∀ k,
      k < j ∨ j + 1 ≤ k →
        (output.set! j saved[sourceOff])[k]? = output[k]? := by
    intro k outside
    have different : j ≠ k := by omega
    simp [Array.set!, different]
  have outsideRange : ∀ k,
      k < oo ∨ oo + slow.left.toNat ≤ k →
        (output.set! j saved[sourceOff])[k]? = output[k]? := by
    intro k outside
    apply outsideByte
    omega
  exact ⟨executed.1, executed.2, current, nextBuffers,
    sizes, byte_view_get_put outputGet outputWrite _, outsideByte,
    output_view_buffer_frame outputPtr outputGet outputWrite
      updatedSize outsideRange⟩

end Zlib.Inflate.Proofs
