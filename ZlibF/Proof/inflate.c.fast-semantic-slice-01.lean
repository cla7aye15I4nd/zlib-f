import ZlibF.Proof.«inftrees.c.decode.short»
import ZlibF.Proof.«inflate.c.fast-view-dolen-literal-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-direct»
import ZlibF.Math.LZ77Copy
import ZlibF.Proof.«inflate.c.fast-view-body-refill-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-literal-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-invalid-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-cases»
import ZlibF.Math.InflateFastMatchHistory
import ZlibF.Proof.«inflate.c.code-length-repeat-meaning»
import ZlibF.Spec.InflateDecodeTableInvariant
import ZlibF.Spec.InflateFastTableFlags
import ZlibF.Spec.Format.Token

set_option autoImplicit false
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open ZlibF.Spec

/-- A proof-side relation across one token. The same unread byte list is
represented by both heaps even when an output store changes their common
underlying byte object. The bit registers may advance. -/
structure SliceEnv (before after : Heap) (entry final : IL)
    (unread : List UInt8) : Prop where
  beforeBits : BitInv before entry unread
  afterBits : BitInv after final unread
  sameCursor : final.next = entry.next
  sameCount : final.have_ = entry.have_

/-- A nonempty `BitInv` represents the exact unread input slice, without
requiring an entire object to stay equal. -/
theorem BitInv.input_slice_of_nonempty
    {h : Heap} {l : IL} {bs : List UInt8}
    (inv : BitInv h l bs) (nonempty : bs ≠ []) :
    Bytes h l.next l.have_.toNat bs := by
  rcases inv.next with empty | ⟨ref, array, off, pointer, get, bound, contents⟩
  · exact False.elim (nonempty empty)
  · exact Or.inr ⟨ref, off, array, pointer, get,
      by rw [inv.have_eq]; exact bound,
      by rw [inv.have_eq]; exact contents⟩

theorem SliceEnv.input_slices
    {before after : Heap} {entry final : IL}
    {unread : List UInt8}
    (env : SliceEnv before after entry final unread)
    (nonempty : unread ≠ []) :
    Bytes before entry.next entry.have_.toNat unread ∧
      Bytes after final.next final.have_.toNat unread :=
  ⟨env.beforeBits.input_slice_of_nonempty nonempty,
    env.afterBits.input_slice_of_nonempty nonempty⟩

/-- A real translated literal branch on a shared caller byte object. Its
terminal heap still represents the same unread input slice, and the byte
written by the source is one independent literal token when the selected
table cell has the promised format meaning. -/
theorem literal_same_object_token
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
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
    {dest : BRef} {output : Array UInt8} {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    (value : lenCodes[index].val.toNat = symbol) :
    let entry := lenCodes[index]
    let width : UInt32 := entry.bits.toUInt32
    let slowNext : IL := { slow with
      hold := slow.hold >>> width.toUInt64,
      bits := slow.bits - width }
    let result : Zlib.Inffast.L := { l with
      againL := false, op := entry.op.toUInt32,
      hold := l.hold >>> width.toUInt64,
      bits := l.bits - width,
      out := .ref dest (j + 1) }
    let after := Space.put h dest (output.set! j entry.val.toUInt8)
    C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      SliceEnv h after slow slowNext bs ∧
      (bs ≠ [] → Bytes after (.ref dest readOff) slow.have_.toNat bs) ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history (stream slow bs)
        (stream slowNext bs) (history ++ [entry.val.toUInt8]) false := by
  obtain ⟨run, _, finalPacket, _, finalBuffers, _, streamDrop, _, _, _⟩ :=
    packet.dolen_literal_default_state invariant buffers herePtr lenGet
      indexBound codeFits codeWidth literal left avail outPtr outputPtr
      endPtr outputGet outputWrite outputSize current guard
  refine ⟨run, ?_, ?_, finalBuffers, ?_⟩
  · exact ⟨packet.source, finalPacket.source, rfl, rfl⟩
  · intro nonempty
    have slice := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [sharedInput] using slice
  · have byte : lenCodes[index].val.toUInt8 = symbol.toUInt8 := by
      apply UInt8.toNat_inj.mp
      simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
      rw [value]
    rw [streamDrop, byte]
    exact ZlibF.Spec.Token.Step.literal decoded small

#print axioms BitInv.input_slice_of_nonempty
#print axioms SliceEnv.input_slices
#print axioms literal_same_object_token
end Zlib.Inflate.Proofs


namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open ZlibF.Spec

/-- The no-refill root-literal branch of the actual complete fast body.
The table lookup is pointer arithmetic on the actual code array; all
input and output views may use the same byte reference. -/
theorem literal_same_object_body_no_pull
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    {lenRef : CodeRef} {lenCodes : Array Code}
    {baseOff index : Nat}
    (rootPtr : c.lcode = .ref lenRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (literal : lenCodes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L (stream slow bs) =
      some (symbol, (stream slow bs).drop lenCodes[index].bits.toNat))
    (small : symbol < 256)
    (value : lenCodes[index].val.toNat = symbol) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j lenCodes[index].val.toUInt8) ∧
      SliceEnv h after slow slowNext bs ∧
      (bs ≠ [] → Bytes after (.ref dest readOff) slow.have_.toNat bs) ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history (stream slow bs)
        (stream slowNext bs)
        (history ++ [lenCodes[index].val.toUInt8]) false := by
  let selected : Zlib.Inffast.L :=
    { l with here := .ref lenRef index }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have selectedOut : selected.out = .ref dest j := outPtr
  have selectedGuard : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := guard
  have literalResult := literal_same_object_token
    (L := L) (D := D) (dict := dict) (history := history) selectedPacket
    invariant buffers (by rfl) lenGet indexBound codeFits codeWidth
    literal left avail selectedOut outputPtr sharedInput endPtr
    outputGet outputWrite outputSize current selectedGuard
    decoded small value
  dsimp only at literalResult
  obtain ⟨dolenRun, slice, read, finalBuffers, token⟩ := literalResult
  have loopRun := dolen_loop_one dolenRun (by rfl)
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref lenRef index), h) := by
    rw [rootPtr, indexEq]
    exact Ptr.add_nat_ok lenGet (by omega)
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [held, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    rfl
  exact ⟨_, _, _, bodyPrefix.trans loopRun, rfl, rfl,
    slice, read, finalBuffers, token⟩

#print axioms literal_same_object_body_no_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open ZlibF.Spec

/-- The no-refill invalid root length-code branch of the actual fast body.
The independent rejection condition is a table-content fact; the actual
BAD transition and retained same-object input slice come from source. -/
theorem invalid_same_object_body_no_pull
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff index : Nat}
    (rootPtr : c.lcode = .ref codeRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (notEnd : (codes[index].op.toUInt32 &&& 32 != 0) = false)
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {L D : List Nat} {dict history : List UInt8}
    (noValid : ∀ more : List Bool,
      ¬ ∃ (symbol : Nat) (rest : List Bool),
        decodeSym L (stream slow bs ++ more) =
          some (symbol, rest) ∧ symbol ≤ 285) :
    ∃ i after result slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = badHeap h r zs z s i ∧
      result.broke = true ∧
      result.out = l.out ∧
      SliceEnv h after slow slowNext bs ∧
      (bs ≠ [] → Bytes after (.ref dest readOff) slow.have_.toNat bs) ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Rejected L D dict history (stream slow bs) := by
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef index }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨i, after, result, slowNext, dolenRun, heapEq,
    broke, noAgain, inputFrame, outputFrame, finalPacket,
    _, finalBuffers, _, _⟩ :=
    selectedPacket.dolen_invalid_leaf_default_state
      invariant buffers streamPtr statePtr (by rfl)
      codesGet codeIndex codeBits codeWidth nonzero
      notBase notLink notEnd
  have cursorEq : slowNext.next = slow.next := by
    rw [← finalPacket.cursor, inputFrame]
    exact selectedPacket.cursor
  have countEq : slowNext.have_ = slow.have_ := by
    apply UInt32.toNat_inj.mp
    rw [finalPacket.source.have_eq, packet.source.have_eq]
  have slice : SliceEnv h after slow slowNext bs :=
    ⟨packet.source, finalPacket.source, cursorEq, countEq⟩
  have read : bs ≠ [] →
      Bytes after (.ref dest readOff) slow.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [cursorEq, countEq, sharedInput] using actual
  have loopRun := dolen_loop_one dolenRun noAgain
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref codeRef index), h) := by
    rw [rootPtr, indexEq]
    exact Ptr.add_nat_ok codesGet (by omega)
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [held, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    rfl
  exact ⟨i, after, result, slowNext,
    bodyPrefix.trans loopRun, heapEq, broke,
    outputFrame, slice, read, finalBuffers,
    ZlibF.Spec.Token.Rejected.length noValid⟩

#print axioms invalid_same_object_body_no_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open ZlibF.Spec ZlibF.Math.LZ77Copy

/-- The actual direct-output match copies exactly the independent LZ77
history suffix. Overlapping source/output bytes and a separate unread
input interval in the same object are both admitted. -/
theorem direct_match_same_object_copyback
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef}
    (packet : FastInputPacket h slow bs l)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {dest : BRef} {output : Array UInt8}
    {oo bg j readOff : Nat}
    (direct : ¬ l.dist > l.op)
    (positive : 0 < l.dist.toNat)
    (withinOutput : l.dist.toNat ≤ j - bg)
    (length : 3 ≤ l.len.toNat)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (beginLe : bg ≤ j)
    {dict : List UInt8} :
    ∃ result after array,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      result.out = .ref dest (j + l.len.toNat) ∧
      Space.get after dest = some array ∧
      SliceEnv h after slow slow bs ∧
      (bs ≠ [] → Bytes after (.ref dest readOff) slow.have_.toNat bs) ∧
      writtenBytes array (j + l.len.toNat)
        (j - bg + l.len.toNat) =
        copyBack dict l.dist.toNat l.len.toNat
          (writtenBytes output j (j - bg)) := by
  have distance : l.dist.toNat ≤ j := by omega
  obtain ⟨result, after, run, finalPacket, resultEq,
    outputAfter, _⟩ := packet.copyMatch_direct_view
      buffers.separate left direct distance length outPtr
      outputPtr outputGet outputWrite outputSize outputRoom
  have finalSlice : SliceEnv h after slow slow bs :=
    ⟨packet.source, finalPacket.source, rfl, rfl⟩
  have finalRead : bs ≠ [] →
      Bytes after (.ref dest readOff) slow.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [sharedInput] using actual
  have copied :
      writtenBytes
        (Zlib.Inffast.Proofs.cpyN l.len.toNat
          (j - l.dist.toNat) j output)
        (j + l.len.toNat) (j - bg + l.len.toNat) =
        copyBack dict l.dist.toNat l.len.toNat
          (writtenBytes output j (j - bg)) := by
    exact output_copy_refines_lz77 dict output j (j - bg)
      l.dist.toNat l.len.toNat (by omega) positive
      withinOutput (by omega)
  refine ⟨result, after, _, run, ?_, outputAfter,
    finalSlice, finalRead, copied⟩
  rw [resultEq]

#print axioms direct_match_same_object_copyback
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec

/-- The actual two pulls and root-table pointer addition are one source
prefix. It consumes exactly two caller bytes, retains the output cursor,
and carries the public byte packet into the selected root entry. -/
theorem FastInputPacket.two_pull_root_prefix
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1) :
    ∃ (slowNext : IL) (fastNext selected : Zlib.Inffast.L)
      (rootSlice : Nat),
      C.run (do
        let one ← Zlib.Inffast.pull l
        let two ← Zlib.Inffast.pull one
        let here ← c.lcode.add
          (two.hold &&& c.lmask.toUInt64).toNat
        pure { two with here }) h = .ok (selected, h) ∧
      selected = { fastNext with
        here := .ref codeRef (baseOff + rootSlice) } ∧
      FastInputPacket h slowNext
        (third :: fourth :: fifth :: sixth :: rest) selected ∧
      DispatchBuffers h r slowNext
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DefaultStateJ h r zs z s ∧
      stream slowNext (third :: fourth :: fifth :: sixth :: rest) =
        stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: rest) ∧
      selected.out = l.out ∧
      fastNext.hold =
        (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
          (second.toUInt64 <<< (l.bits + 8).toUInt64) ∧
      slowNext.put = slow.put ∧ slowNext.left = slow.left ∧
      slowNext.next = inputAdvance slow.next 2 ∧
      slowNext.bits.toNat = slow.bits.toNat + 16 ∧
      16 ≤ slowNext.bits.toNat ∧ slowNext.bits.toNat ≤ 30 ∧
      rootSlice = (fastNext.hold &&& c.lmask.toUInt64).toNat ∧
      rootSlice < 2 ^ rootWidth := by
  obtain ⟨next1, fast1, slow1, pull1, next1Eq,
    slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
    packet.pull_default_state invariant buffers (by omega)
  have small1 : slow1.bits.toNat ≤ 22 := by
    rw [slow1Eq]
    change (slow.bits + 8).toNat ≤ 22
    rw [u32_add8 slow.bits (by omega)]
    omega
  obtain ⟨next2, fast2, slow2, pull2, next2Eq,
    slow2Eq, fast2Eq, packet2, _, buffers2, stream2⟩ :=
    packet1.pull_default_state invariant buffers1 small1
  have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
    rw [slow1Eq]
    exact u32_add8 slow.bits (by omega)
  have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by
    rw [slow2Eq]
    exact u32_add8 slow1.bits (by omega)
  let rootSlice := (fast2.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { fast2 with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨rootBound, addRun, selectedPacket⟩ :=
    packet2.fast_body_root_lookup lcodePtr codesGet safe mask
  have prefixRun : C.run (do
      let one ← Zlib.Inffast.pull l
      let two ← Zlib.Inffast.pull one
      let here ← c.lcode.add
        (two.hold &&& c.lmask.toUInt64).toNat
      pure { two with here }) h = .ok (selected, h) := by
    change (Zlib.Inffast.pull l >>= fun one =>
      Zlib.Inffast.pull one >>= fun two =>
        c.lcode.add (two.hold &&& c.lmask.toUInt64).toNat >>= fun here =>
          pure { two with here }) h = .ok (selected, h)
    change Zlib.Inffast.pull l h = .ok (fast1, h) at pull1
    change Zlib.Inffast.pull fast1 h = .ok (fast2, h) at pull2
    change (c.lcode.add rootSlice) h =
      .ok (.ref codeRef (baseOff + rootSlice), h) at addRun
    simp only [bind_app, pull1, pull2, pure_app]
    dsimp only [rootSlice] at addRun
    rw [addRun]
  have outFrame : selected.out = l.out := by
    simp only [selected, fast2Eq, fast1Eq,
      Zlib.Inffast.Proofs.pullL]
  have holdFrame : fast2.hold =
      (l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64) := by
    simp only [fast2Eq, fast1Eq,
      Zlib.Inffast.Proofs.pullL]
  have putFrame : slow2.put = slow.put := by
    simp only [slow2Eq, slow1Eq, pulled]
  have leftFrame : slow2.left = slow.left := by
    simp only [slow2Eq, slow1Eq, pulled]
  have nextFrame : slow2.next = inputAdvance slow.next 2 := by
    have firstNext : slow1.next = inputAdvance slow.next 1 := by
      rw [slow1Eq, next1Eq]
      rfl
    rw [slow2Eq, pulled, next2Eq, firstNext,
      inputAdvance_add]
  exact ⟨slow2, fast2, selected, rootSlice, prefixRun,
    rfl, selectedPacket, buffers2, invariant,
    stream2.trans stream1, outFrame, holdFrame, putFrame,
    leftFrame, nextFrame, by omega, by omega, by omega,
    rfl,
    rootBound⟩

#print axioms FastInputPacket.two_pull_root_prefix
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

private theorem payload_bind_assoc {α β γ : Type}
    (m : C.M α) (f : α → C.M β) (g : β → C.M γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := by
  funext heap
  simp only [bind_app]
  cases m heap <;> rfl

private theorem payload_pure_bind {α β : Type}
    (x : α) (f : α → C.M β) :
    (pure x : C.M α) >>= f = f x := by
  funext heap
  rfl

/-- The translated fast body's two-pull root literal branch emits one
independent literal token and preserves its remaining same-object input
slice. The Huffman meaning of the selected table cell is the separate
representation fact supplied by table construction. -/
theorem literal_same_object_body_two_pull
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (literal : codes[index].op = 0)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} {symbol : Nat}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat))
    (smallSymbol : symbol < 256)
    (value : codes[index].val.toNat = symbol) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest (j + 1) ∧
      after = Space.put h dest
        (output.set! j codes[index].val.toUInt8) ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      slowPrefix.next = inputAdvance slow.next 2 ∧
      (Bytes after (.ref dest (readOff + 2))
        slowPrefix.have_.toNat
        (third :: fourth :: fifth :: sixth :: rest)) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        (history ++ [codes[index].val.toUInt8]) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    nextFrame, bitsFrame, _, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have selectedOut : selected.out = .ref dest j :=
    outFrame.trans outPtr
  have put2 : slow2.put = .ref dest oo :=
    putFrame.trans outputPtr
  have left2 : slow2.left ≠ 0 := by
    rw [leftFrame]
    exact left
  have avail2 : 258 ≤ slow2.left.toNat := by
    rw [leftFrame]
    exact avail
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    rw [leftFrame]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftFrame]
    exact outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    rw [selectedOut]
    simpa only [outPtr] using guard
  have shared2 : slow2.next = .ref dest (readOff + 2) := by
    rw [nextFrame, sharedInput]
    rfl
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (symbol,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have literalResult := literal_same_object_token
    (L := L) (D := D) (dict := dict) (history := history)
    selectedPacket invariant buffers2 selectedHere codesGet
    indexBound codeFits2 codeWidth literal left2 avail2
    selectedOut put2 shared2 end2 outputGet outputWrite
    size2 current guard2 decoded2 smallSymbol value
  dsimp only at literalResult
  obtain ⟨dolenRun, slice, read, finalBuffers, token⟩ := literalResult
  have loopRun := dolen_loop_one dolenRun (by rfl)
  let prefixM : C.M Zlib.Inffast.L := do
    let one ← Zlib.Inffast.pull l
    let two ← Zlib.Inffast.pull one
    let here ← c.lcode.add
      (two.hold &&& c.lmask.toUInt64).toNat
    pure { two with here }
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (prefixM >>= fun current =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current)) current) h := by
    unfold Zlib.Inffast.inflate_fast_body
    have needsPull : l.bits < 15 := by
      rw [packet.bits]
      exact UInt32.lt_iff_toNat_lt.mpr small
    simp only [needsPull, ite_true]
    simp only [prefixM, C.run, payload_bind_assoc,
      payload_pure_bind]
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    rw [bodyPrefix]
    change (prefixM >>= fun current =>
      cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) current) h = _
    change prefixM h = .ok (selected, h) at prefixRun
    rw [bind_app, prefixRun]
    rfl
  have finalRun := bodyRun.trans loopRun
  refine ⟨slow2, _, _, _, finalRun, ?_, ?_,
    slice, nextFrame, ?_, finalBuffers, ?_⟩
  · rfl
  · rfl
  · exact read (by simp)
  · rw [source2] at token
    exact token

#print axioms literal_same_object_body_two_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public

/-- Source control-flow composition for the two-pull fast body. Both run
equations are supplied by source proofs at use sites. -/
private theorem body_from_two_pull_root
    {h after : Heap} {l selected result : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    (needsPull : l.bits < 15)
    (prefixRun : C.run (do
      let one ← Zlib.Inffast.pull l
      let two ← Zlib.Inffast.pull one
      let here ← c.lcode.add
        (two.hold &&& c.lmask.toUInt64).toNat
      pure { two with here }) h = .ok (selected, h))
    (loopRun : C.run (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) selected) h =
      .ok (result, after)) :
    C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
  let prefixM : C.M Zlib.Inffast.L := do
    let one ← Zlib.Inffast.pull l
    let two ← Zlib.Inffast.pull one
    let here ← c.lcode.add
      (two.hold &&& c.lmask.toUInt64).toNat
    pure { two with here }
  have same : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (prefixM >>= fun current =>
        cdoWhile (Zlib.Inffast.dolen c)
          (fun current => pure (current.againL, current)) current) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [needsPull, ite_true]
    simp only [prefixM, C.run, payload_bind_assoc,
      payload_pure_bind]
  rw [same]
  change (prefixM >>= fun current =>
    cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current)) current) h = _
  change prefixM h = .ok (selected, h) at prefixRun
  rw [bind_app, prefixRun]
  exact loopRun

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A selected root end code after the actual two-pull prefix enters TYPE
without changing output bytes. The retained unread slice may share its
object with the caller output interval. -/
theorem eob_same_object_body_two_pull
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {L D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym L
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat)) :
    ∃ slowPrefix slowFinal result after,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      slowPrefix.next = inputAdvance slow.next 2 ∧
      Bytes after (.ref dest (readOff + 2))
        slowPrefix.have_.toNat
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
        (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
        history true := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, _, _, nextFrame, bitsFrame,
    _, _, rootSliceEq, _⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  obtain ⟨result, slowFinal, dolenRun, broke, noAgain,
    inputFrame, outputFrame, finalPacket, _, finalBuffers,
    _, sourceDrop⟩ :=
    selectedPacket.dolen_end_leaf_default_state
      invariant buffers2 statePtr mode selectedHere codesGet
      indexBound codeFits2 codeWidth nonzero notBase
      notLink endCode
  have cursorEq : slowFinal.next = slow2.next := by
    rw [← finalPacket.cursor, inputFrame]
    exact selectedPacket.cursor
  have countEq : slowFinal.have_ = slow2.have_ := by
    apply UInt32.toNat_inj.mp
    rw [finalPacket.source.have_eq, selectedPacket.source.have_eq]
  have slice : SliceEnv h (setI h zs { s with mode := TYPE })
      slow2 slowFinal (third :: fourth :: fifth :: sixth :: rest) :=
    ⟨selectedPacket.source, finalPacket.source,
      cursorEq, countEq⟩
  have shared2 : slow2.next = .ref dest (readOff + 2) := by
    rw [nextFrame, sharedInput]
    rfl
  have read : Bytes (setI h zs { s with mode := TYPE })
      (.ref dest (readOff + 2)) slow2.have_.toNat
      (third :: fourth :: fifth :: sixth :: rest) := by
    have actual := finalPacket.source.input_slice_of_nonempty
      (by simp : third :: fourth :: fifth :: sixth :: rest ≠ [])
    simpa only [cursorEq, countEq, shared2] using actual
  have loopRun := dolen_loop_one dolenRun noAgain
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have decoded2 : decodeSym L
      (stream slow2 (third :: fourth :: fifth :: sixth :: rest)) =
      some (256,
        (stream slow2 (third :: fourth :: fifth :: sixth :: rest)).drop
          codes[index].bits.toNat) := by
    rw [source2]
    exact decoded
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨slow2, slowFinal, result,
    setI h zs { s with mode := TYPE }, bodyRun, rfl,
    broke, outputFrame.trans outFrame, slice, nextFrame,
    read, finalBuffers, token⟩

#print axioms eob_same_object_body_two_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A selected invalid root code after two actual input pulls enters BAD
without writing output. The format rejection fact comes from the table
content invariant, while the BAD transition is proved from translated C. -/
theorem invalid_same_object_body_two_pull
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth index : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (indexEq : index = baseOff +
      ((((l.hold + (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat))
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat + 16)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (notEnd : (codes[index].op.toUInt32 &&& 32 != 0) = false)
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {L D : List Nat} {dict history : List UInt8}
    (noValid : ∀ more : List Bool,
      ¬ ∃ (symbol : Nat) (restBits : List Bool),
        decodeSym L
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest) ++ more) =
          some (symbol, restBits) ∧ symbol ≤ 285) :
    ∃ slowPrefix slowFinal result after i,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = badHeap h r zs z s i ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slowPrefix slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      slowPrefix.next = inputAdvance slow.next 2 ∧
      Bytes after (.ref dest (readOff + 2))
        slowPrefix.have_.toNat
        (third :: fourth :: fifth :: sixth :: rest) ∧
      DispatchBuffers after r slowFinal
        (third :: fourth :: fifth :: sixth :: rest) ∧
      ZlibF.Spec.Token.Rejected L D dict history
        (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, _,
    outFrame, holdFrame, _, _, nextFrame, bitsFrame,
    _, _, rootSliceEq, _⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have rootEq : index = baseOff + rootSlice := by
    rw [indexEq, ← holdFrame, ← rootSliceEq]
  have selectedHere : selected.here = .ref codeRef index := by
    rw [selectedEq, rootEq]
  have codeFits2 : codes[index].bits.toNat ≤ slow2.bits.toNat := by
    rw [bitsFrame]
    exact codeFits
  obtain ⟨i, after, result, slowFinal, dolenRun, heapEq,
    broke, noAgain, inputFrame, outputFrame, finalPacket,
    _, finalBuffers, _, _⟩ :=
    selectedPacket.dolen_invalid_leaf_default_state
      invariant buffers2 streamPtr statePtr selectedHere
      codesGet indexBound codeFits2 codeWidth nonzero
      notBase notLink notEnd
  have cursorEq : slowFinal.next = slow2.next := by
    rw [← finalPacket.cursor, inputFrame]
    exact selectedPacket.cursor
  have countEq : slowFinal.have_ = slow2.have_ := by
    apply UInt32.toNat_inj.mp
    rw [finalPacket.source.have_eq, selectedPacket.source.have_eq]
  have slice : SliceEnv h after slow2 slowFinal
      (third :: fourth :: fifth :: sixth :: rest) :=
    ⟨selectedPacket.source, finalPacket.source,
      cursorEq, countEq⟩
  have shared2 : slow2.next = .ref dest (readOff + 2) := by
    rw [nextFrame, sharedInput]
    rfl
  have read : Bytes after (.ref dest (readOff + 2))
      slow2.have_.toNat
      (third :: fourth :: fifth :: sixth :: rest) := by
    have actual := finalPacket.source.input_slice_of_nonempty
      (by simp : third :: fourth :: fifth :: sixth :: rest ≠ [])
    simpa only [cursorEq, countEq, shared2] using actual
  have loopRun := dolen_loop_one dolenRun noAgain
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  exact ⟨slow2, slowFinal, result, after, i,
    bodyRun, heapEq, broke, outputFrame.trans outFrame,
    slice, nextFrame, read, finalBuffers,
    ZlibF.Spec.Token.Rejected.length noValid⟩

#print axioms invalid_same_object_body_two_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The actual two-pass linked literal branch leaves a semantic cut at the
selected second-level cell. When that cell is a literal with constructor
meaning, the complete fast body writes its byte and refines one token. -/
theorem linked_literal_same_object_body_two_pull
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8}
    {oo j readOff : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (sharedInput : slow.next = .ref dest readOff)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected : Zlib.Inffast.L)
      (rootSlice : Nat) (linked : Zlib.Inffast.L)
      (slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slowPrefix.next = .ref dest (readOff + 2) ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      ∀ symbol : Nat,
        target.op = 0 →
        decodeSym L
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
          some (symbol,
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
              (rootEntry.bits.toNat + target.bits.toNat)) →
        symbol < 256 → target.val.toNat = symbol →
        ∃ (result : Zlib.Inffast.L) (after : Heap)
          (slowFinal : IL),
          C.run (Zlib.Inffast.inflate_fast_body c l) h =
            .ok (result, after) ∧
          Space.get after dest = some
            (output.set! j target.val.toUInt8) ∧
          FastInputPacket after slowFinal
            (third :: fourth :: fifth :: sixth :: rest) result ∧
          DispatchBuffers after r slowFinal
            (third :: fourth :: fifth :: sixth :: rest) ∧
          Bytes after slowFinal.next slowFinal.have_.toNat
            (third :: fourth :: fifth :: sixth :: rest) ∧
          ZlibF.Spec.Token.Step L D dict history
            (stream slow
              (first :: second :: third :: fourth :: fifth :: sixth :: rest))
            (stream slowFinal
              (third :: fourth :: fifth :: sixth :: rest))
            (history ++ [target.val.toUInt8]) false := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    outFrame, holdFrame, putFrame, leftFrame,
    nextFrame, _, held2, _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  have out2 : selected.out = .ref dest j :=
    outFrame.trans outPtr
  have put2 : slow2.put = .ref dest oo :=
    putFrame.trans outputPtr
  have left2 : slow2.left ≠ 0 := by
    rw [leftFrame]
    exact left
  have avail2 : 258 ≤ slow2.left.toNat := by
    rw [leftFrame]
    exact avail
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    rw [leftFrame]
    exact endPtr
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    rw [leftFrame]
    exact outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    rw [out2]
    simpa only [outPtr] using guard
  obtain ⟨linked, slice, slowLink, linkRun, againL,
    _, _, _, _, linkedSource, finish⟩ :=
    selectedPacket.dolen_linked_literal_default_state
      invariant buffers2 herePtr lcodePtr codesGet safe
      rootBound link (by omega) left2 avail2 out2 put2 end2
      outputGet outputWrite size2 current guard2
  refine ⟨slow2, selected, rootSlice, linked, slice,
    linkRun, againL, ?_, ?_⟩
  · rw [nextFrame, sharedInput]
    rfl
  dsimp only
  intro symbol literal decoded smallSymbol value
  obtain ⟨result, slowFinal, after, _, loopRun, _,
    finalPacket, _, finalBuffers, _, outputAfter,
    _, _, sourceDrop⟩ := finish literal
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have byte : (codes.getD
      (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
        default).val.toUInt8 = symbol.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt8.toNat_ofNat']
    rw [value]
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      (history ++ [(codes.getD
        (baseOff + (codes.getD (baseOff + rootSlice) default).val.toNat + slice)
          default).val.toUInt8]) false := by
    rw [sourceDrop, source2, byte]
    exact ZlibF.Spec.Token.Step.literal decoded smallSymbol
  have read := finalPacket.source.input_slice_of_nonempty
    (by simp : third :: fourth :: fifth :: sixth :: rest ≠ [])
  exact ⟨result, after, slowFinal, bodyRun, outputAfter,
    finalPacket, finalBuffers, read, token⟩

#print axioms linked_literal_same_object_body_two_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A linked end-of-block leaf selected after two actual pulls enters TYPE
and refines the independent end token. The conditional records the actual
second-level index selected by the first translated `dolen` pass. -/
theorem linked_eob_same_object_body_two_pull
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {L D : List Nat} {dict history : List UInt8} :
    ∃ (slowPrefix : IL) (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slowPrefix.next = .ref dest (readOff + 2) ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
      decodeSym L
        (stream slow
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
        some (256,
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)).drop
            (rootEntry.bits.toNat + target.bits.toNat)) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = setI h zs { s with mode := TYPE } ∧
        result.broke = true ∧
        FastInputPacket after slowFinal
          (third :: fourth :: fifth :: sixth :: rest) result ∧
        DispatchBuffers after r slowFinal
          (third :: fourth :: fifth :: sixth :: rest) ∧
        Bytes after slowFinal.next slowFinal.have_.toNat
          (third :: fourth :: fifth :: sixth :: rest) ∧
        ZlibF.Spec.Token.Step L D dict history
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest))
          (stream slowFinal
            (third :: fourth :: fifth :: sixth :: rest))
          history true := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    _, holdFrame, _, _, nextFrame, _, held2,
    _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  obtain ⟨linked, slice, linkRun, againL, _, _, finish⟩ :=
    selectedPacket.dolen_linked_end_default_state
      invariant buffers2 statePtr mode herePtr lcodePtr
      codesGet safe rootBound link (by omega)
  refine ⟨slow2, selected, linked, rootSlice, slice,
    linkRun, againL, ?_, ?_⟩
  · rw [nextFrame, sharedInput]
    rfl
  dsimp only
  intro selectedEnd decoded
  obtain ⟨result, slowFinal, _, loopRun, broke,
    _, finalPacket, _, finalBuffers, _, sourceDrop⟩ :=
    finish selectedEnd
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have read := finalPacket.source.input_slice_of_nonempty
    (by simp : third :: fourth :: fifth :: sixth :: rest ≠ [])
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest))
      (stream slowFinal (third :: fourth :: fifth :: sixth :: rest))
      history true := by
    rw [sourceDrop, source2]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨result, setI h zs { s with mode := TYPE },
    slowFinal, bodyRun, rfl, broke, finalPacket,
    finalBuffers, read, token⟩

#print axioms linked_eob_same_object_body_two_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- A selected invalid second-level length leaf runs the actual two-pull
body to BAD. The rejection predicate is a table-content meaning fact;
input and output may name disjoint intervals of the same byte object. -/
theorem linked_invalid_same_object_body_two_pull
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (small : slow.bits.toNat < 15)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (mask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (rootLink : ∀ k, k < 2 ^ rootWidth →
      (k = (((l.hold +
        (first.toUInt64 <<< l.bits.toUInt64)) +
        (second.toUInt64 <<< (l.bits + 8).toUInt64)) &&&
          c.lmask.toUInt64).toNat) →
      LenLink (codes.getD (baseOff + k) default))
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {L D : List Nat} {dict history : List UInt8}
    (noValid : ∀ more : List Bool,
      ¬ ∃ (symbol : Nat) (restBits : List Bool),
        decodeSym L
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest) ++ more) =
          some (symbol, restBits) ∧ symbol ≤ 285) :
    ∃ (slowPrefix : IL) (selected linked : Zlib.Inffast.L)
      (rootSlice slice : Nat),
      C.run (Zlib.Inffast.dolen c selected) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slowPrefix.next = .ref dest (readOff + 2) ∧
      let rootEntry := codes.getD (baseOff + rootSlice) default
      let target := codes.getD
        (baseOff + rootEntry.val.toNat + slice) default
      (target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = false) →
      ∃ (result : Zlib.Inffast.L) (after : Heap)
        (slowFinal : IL) (i : Nat),
        C.run (Zlib.Inffast.inflate_fast_body c l) h =
          .ok (result, after) ∧
        after = badHeap h r zs z s i ∧
        result.broke = true ∧
        FastInputPacket after slowFinal
          (third :: fourth :: fifth :: sixth :: rest) result ∧
        DispatchBuffers after r slowFinal
          (third :: fourth :: fifth :: sixth :: rest) ∧
        Bytes after slowFinal.next slowFinal.have_.toNat
          (third :: fourth :: fifth :: sixth :: rest) ∧
        ZlibF.Spec.Token.Rejected L D dict history
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)) := by
  obtain ⟨slow2, fast2, selected, rootSlice, prefixRun,
    selectedEq, selectedPacket, buffers2, _, source2,
    _, holdFrame, _, _, nextFrame, _, held2,
    _, rootSliceEq, rootBound⟩ :=
    packet.two_pull_root_prefix invariant buffers small
      lcodePtr codesGet safe mask
  have link : LenLink (codes.getD (baseOff + rootSlice) default) := by
    apply rootLink rootSlice rootBound
    rw [rootSliceEq, holdFrame]
  have herePtr : selected.here =
      .ref codeRef (baseOff + rootSlice) := by
    rw [selectedEq]
  obtain ⟨linked, slice, linkRun, againL, _, _, finish⟩ :=
    selectedPacket.dolen_linked_invalid_default_state
      invariant buffers2 streamPtr statePtr herePtr lcodePtr
      codesGet safe rootBound link (by omega)
  refine ⟨slow2, selected, linked, rootSlice, slice,
    linkRun, againL, ?_, ?_⟩
  · rw [nextFrame, sharedInput]
    rfl
  dsimp only
  intro selectedInvalid
  obtain ⟨i, result, slowFinal, after, _, loopRun,
    heapEq, broke, _, finalPacket, _, finalBuffers,
    _, sourceDrop⟩ := finish selectedInvalid
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun := body_from_two_pull_root needsPull prefixRun loopRun
  have read := finalPacket.source.input_slice_of_nonempty
    (by simp : third :: fourth :: fifth :: sixth :: rest ≠ [])
  have rejected : ZlibF.Spec.Token.Rejected L D dict history
      (stream slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)) :=
    ZlibF.Spec.Token.Rejected.length noValid
  exact ⟨result, after, slowFinal, i,
    bodyRun, heapEq, broke, finalPacket,
    finalBuffers, read, rejected⟩

#print axioms linked_invalid_same_object_body_two_pull
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec ZlibF.Spec

/-- The actual no-refill root end code leaves the block, with the same
unread input slice even when its reference aliases the output object. -/
theorem eob_same_object_body_no_pull
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (held : ¬ l.bits < 15)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff index : Nat}
    (rootPtr : c.lcode = .ref codeRef baseOff)
    (indexEq : index = baseOff + (l.hold &&& c.lmask.toUInt64).toNat)
    (codesGet : Space.get h codeRef = some codes)
    (indexBound : index < codes.size)
    (codeFits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {dest : BRef} {readOff : Nat}
    (sharedInput : slow.next = .ref dest readOff)
    {L D : List Nat} {dict history : List UInt8}
    (decoded : decodeSym L (stream slow bs) =
      some (256, (stream slow bs).drop codes[index].bits.toNat)) :
    ∃ result after slowNext,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      after = setI h zs { s with mode := TYPE } ∧
      result.broke = true ∧ result.out = l.out ∧
      SliceEnv h after slow slowNext bs ∧
      (bs ≠ [] → Bytes after (.ref dest readOff)
        slow.have_.toNat bs) ∧
      DispatchBuffers after r slowNext bs ∧
      ZlibF.Spec.Token.Step L D dict history
        (stream slow bs) (stream slowNext bs) history true := by
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef index }
  have selectedPacket : FastInputPacket h slow bs selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, slowNext, dolenRun, broke,
    noAgain, inputFrame, outputFrame, finalPacket, _,
    finalBuffers, _, sourceDrop⟩ :=
    selectedPacket.dolen_end_leaf_default_state
      invariant buffers statePtr mode (by rfl) codesGet
      indexBound codeFits codeWidth nonzero notBase notLink endCode
  have addRun : C.run
      (c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat) h =
      .ok ((.ref codeRef index), h) := by
    rw [rootPtr, indexEq]
    exact Ptr.add_nat_ok codesGet (by omega)
  have bodyPrefix : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) selected) h := by
    unfold Zlib.Inffast.inflate_fast_body
    simp only [held, ite_false]
    unfold C.run at addRun ⊢
    simp only [bind_app, addRun]
    rfl
  have loopRun := dolen_loop_one dolenRun noAgain
  have slice : SliceEnv h
      (setI h zs { s with mode := TYPE }) slow slowNext bs := by
    refine ⟨packet.source, finalPacket.source, ?_, ?_⟩
    · rw [← finalPacket.cursor]
      rw [inputFrame]
      exact selectedPacket.cursor
    · apply UInt32.toNat_inj.mp
      rw [finalPacket.source.have_eq, packet.source.have_eq]
  have read : bs ≠ [] → Bytes
      (setI h zs { s with mode := TYPE })
      (.ref dest readOff) slow.have_.toNat bs := by
    intro nonempty
    have actual := finalPacket.source.input_slice_of_nonempty nonempty
    simpa only [slice.sameCursor, slice.sameCount, sharedInput] using actual
  have token : ZlibF.Spec.Token.Step L D dict history
      (stream slow bs) (stream slowNext bs) history true := by
    rw [sourceDrop]
    exact ZlibF.Spec.Token.Step.eob decoded
  exact ⟨result, _, slowNext, bodyPrefix.trans loopRun,
    rfl, broke, outputFrame, slice, read,
    finalBuffers, token⟩

#print axioms eob_same_object_body_no_pull
end Zlib.Inflate.Proofs
