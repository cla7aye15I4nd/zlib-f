import ZlibF.Proof.«inflate.c.local-fast-parser-dolen-literal-invariant»
import ZlibF.Proof.«inflate.c.local-fast-parser-pull»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-loop-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-bad-data-invariant»
import ZlibF.Proof.«inflate.c.local-fast-copy-literal-write-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- A leaf that clears `againL` terminates the actual length-code loop
after its first translated pass. -/
theorem dolen_loop_one
    {h after : Heap} {l result : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    (run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, after))
    (againL : result.againL = false) :
    C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) l) h =
      .ok (result, after) := by
  apply Zlib.Inffast.Proofs.cdoWhile_one run
  simp only [againL, C.run, pure]

/-- A root literal leaf executes the actual one-pass `dolen` loop,
including its output byte and caller buffer frame. -/
theorem FastInputPacket.dolen_root_literal_loop_local_state
    {h : Heap} {cutoff : Nat} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ slowNext result after,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.againL = false ∧
      FastInputPacket after slowNext bs result ∧
      LocalStateJ after cutoff r zs z s ∧
      DispatchBuffers after r slowNext bs ∧
      ByteViewSizes h after ∧
      stream slowNext bs =
        (stream slow bs).drop lenCodes[index].bits.toNat ∧
      Space.get after dest = some
        (output.set! j lenCodes[index].val.toUInt8) ∧
      Space.ro after dest = false ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let entry : Code := lenCodes[index]
  let count : UInt32 := entry.bits.toUInt32
  let slowNext : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let result : Zlib.Inffast.L := { l with
    againL := false,
    op := entry.op.toUInt32,
    hold := l.hold >>> count.toUInt64,
    bits := l.bits - count,
    out := .ref dest (j + 1) }
  let after := Space.put h dest
    (output.set! j entry.val.toUInt8)
  obtain ⟨run, noAgain, nextPacket, nextState,
    nextBuffers, sizes, source, outputAfter,
    writable, frame⟩ :=
    (Zlib.Inflate.Local.FastInputPacket.dolen_literal_local_state packet) invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal
      left avail outPtr outputPtr endPtr outputGet
      outputWrite outputSize current guard
  have loopRun := dolen_loop_one run noAgain
  exact ⟨slowNext, result, after, loopRun, noAgain,
    nextPacket, nextState, nextBuffers, sizes,
    source, outputAfter, writable, frame⟩

end Zlib.Inflate.Local
