import ZlibF.Proof.«inflate.c.fast-view-diff-invariant»
import ZlibF.Proof.«inflate.c.fast-view-drop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-base-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-root-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-leaf-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-dist-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-refill-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-extra-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-len-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-loop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-terminals-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-refill-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-one-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-leaf-one-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-linked-leaf-one-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dodist-loop-one-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-dist-one-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-refill-three-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-extra-three-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-len-four-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-four-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-base-four-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-linked-base-four-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-link-complete-four-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-four-byte-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-pull-branch-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The translated match body retains a bounded output cursor on the
invalid-distance break as well as on a successful copy. -/
theorem FastInputPacket.copyMatch_view_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (good : Good h r zs z s)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (sane : s.sane ≠ 0)
    (separate : Separate slow.next slow.have_.toNat slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (length : 3 ≤ l.len.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op → ¬ l.dist - l.op > c.whave →
      ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
        window ≠ dest ∧ c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size) :
    ∃ result after array next,
      C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ j + l.len.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases windowBranch : l.dist > l.op
  · by_cases invalidBack : l.dist - l.op > c.whave
    · obtain ⟨i, after, run, heapEq, _, bytes, _⟩ :=
        packet.copyMatch_invalid_view good streamPtr statePtr sane
          windowBranch invalidBack outputGet outputWrite
      refine ⟨{ l with op := l.dist - l.op, broke := true },
        after, output, j, run, ?_, by omega, by omega, bytes, rfl⟩
      simpa only [outPtr]
    · obtain ⟨result, after, array, run, _, out, _, _, _, bytes, size, _⟩ :=
        packet.copyMatch_valid_view separate left length
          whaveBound wnextBound wsizeBound outPtr outputPtr
          outputGet outputWrite outputSize outputRoom produced
          (fun _ => invalidBack) windowData
      exact ⟨result, after, array, j + l.len.toNat,
        run, out, by omega, by omega, bytes, size⟩
  · obtain ⟨result, after, array, run, _, out, _, _, _, bytes, size, _⟩ :=
      packet.copyMatch_valid_view separate left length
        whaveBound wnextBound wsizeBound outPtr outputPtr
        outputGet outputWrite outputSize outputRoom produced
        (fun h => False.elim (windowBranch h)) windowData
    exact ⟨result, after, array, j + l.len.toNat,
      run, out, by omega, by omega, bytes, size⟩

/-- The pointer-difference and match-copy suffix keeps the output cursor
inside the original call range even when the distance is invalid. -/
theorem FastInputPacket.copy_match_after_diff_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (do
        let d ← Ptr.diff l.out c.beg
        Zlib.Inffast.copyMatch c { l with op := d.toUInt64.toUInt32 }) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
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
      outputGet currentBound beginBound (by omega)
    have intEq : (j : Int) - (bg : Int) = ((j - bg : Nat) : Int) := by omega
    change (Ptr.diff (.ref dest j) (.ref dest bg)) h =
      .ok (Int64.ofInt ((j : Int) - (bg : Int)), h) at run
    simpa only [C.run, intEq] using run
  let atCopy : Zlib.Inffast.L :=
    { l with op := (Int64.ofInt ((j - bg : Nat) : Int)).toUInt64.toUInt32 }
  have produced : atCopy.op.toNat ≤ j :=
    (fast_produced_of_diff (l := atCopy) outputGet currentBound
      beginBound beginLe span
      (by simpa only [outPtr, begPtr] using diffRun) rfl).2
  have copyPacket : FastInputPacket h slow bs atCopy := packet.with_op _
  have sane : s.sane ≠ 0 := by
    rw [invariant.pending.sane]
    decide
  have whaveBound : c.whave.toNat ≤ c.wsize.toNat := by
    rw [whaveEq, wsizeEq]
    exact invariant.good.inv.win.hv
  have wnextBound : c.wnext.toNat ≤ c.wsize.toNat := by
    rw [wnextEq, wsizeEq]
    rcases invariant.good.inv.win.wn with lt | zero <;> omega
  have wsizeBound : c.wsize.toNat ≤ 32768 := by
    rw [wsizeEq]
    have pow := Nat.pow_le_pow_right
      (by decide : 0 < 2) invariant.good.inv.win.wbits
    rcases invariant.good.inv.win.ws with zero | size <;> omega
  have windowData := fast_window_data_of_caller (l := atCopy)
    invariant.good buffers.output.range outputPtr
    whaveEq wsizeEq windowEq
  obtain ⟨result, after, array, next, copyRun, out,
    lower, upper, bytes, size⟩ :=
    copyPacket.copyMatch_view_output_bound invariant.good
      streamPtr statePtr sane buffers.separate left length.1
      whaveBound wnextBound wsizeBound outPtr outputPtr
      outputGet outputWrite outputSize outputRoom produced
      windowData
  have lenEq : atCopy.len = l.len := rfl
  rw [lenEq] at upper
  refine ⟨result, after, array, next, ?_, out, lower,
    by omega, bytes, size⟩
  change (do
    let d ← Ptr.diff l.out c.beg
    Zlib.Inffast.copyMatch c { l with op := d.toUInt64.toUInt32 }) h =
      .ok (result, after)
  rw [bind_ok (by simpa only [C.run] using diffRun)]
  exact copyRun

/-- The extra-distance-bit suffix preserves an output cursor for both
successful copies and invalid-distance breaks. -/
theorem FastInputPacket.distCont_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (extraBits : l.op.toNat ≤ slow.bits.toNat)
    (extraSmall : l.op.toNat < 32)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.distCont c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let distance : UInt32 :=
    l.dist + (l.hold.toUInt32 &&& ((1 : UInt32) <<< l.op) - 1)
  let distanceLocal : Zlib.Inffast.L := { l with dist := distance }
  have distancePacket : FastInputPacket h slow bs distanceLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := distancePacket.drop_bits_default_state
    buffers l.op extraBits (by omega)
  let slowNext : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let fastNext : Zlib.Inffast.L := { distanceLocal with
    hold := distanceLocal.hold >>> l.op.toUInt64,
    bits := distanceLocal.bits - l.op }
  have nextPacket : FastInputPacket h slowNext bs fastNext := dropped.1
  have nextBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  have nextOut : fastNext.out = .ref dest j := outPtr
  have nextLength : 3 ≤ fastNext.len.toNat ∧ fastNext.len.toNat ≤ 258 := length
  have nextGuard : C.run (Ptr.lt fastNext.out c.end_) h = .ok (true, h) := guard
  obtain ⟨result, after, array, next, copyRun, out,
    lower, upper, bytes, size⟩ :=
    nextPacket.copy_match_after_diff_output_bound invariant
      nextBuffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq left avail nextLength nextOut
      outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span nextGuard
  have shlRun : C.run (Zlib.Inffast.shl32 1 l.op) h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok extraSmall
  have shrRun : C.run (Zlib.Inffast.shr64 l.hold l.op.toUInt64) h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  have run : C.run (Zlib.Inffast.Proofs.distCont c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.distCont c l) h = _
    change Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) at shlRun
    change Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) at shrRun
    unfold Zlib.Inffast.Proofs.distCont
    rw [bind_ok shlRun, bind_ok shrRun]
    simpa only [C.run, fastNext, distanceLocal, distance] using copyRun
  exact ⟨result, after, array, next, run, out, lower, upper, bytes, size⟩


theorem FastInputPacket.dodistBase_output_bound
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (extraBound : l.op.toNat ≤ 13)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dodistBase c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases needsFirst : l.bits < l.op
  · have small0 : slow.bits.toNat ≤ 22 := by
      have selected := UInt32.lt_iff_toNat_lt.mp needsFirst
      rw [packet.bits] at selected
      omega
    obtain ⟨next1, fast1, slow1, pull1, next1Eq,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small0
    have len1 : fast1.len = l.len := by rw [fast1Eq]; rfl
    have op1 : fast1.op = l.op := by rw [fast1Eq]; rfl
    have out1 : fast1.out = .ref dest j := by rw [fast1Eq]; exact outPtr
    have put1 : slow1.put = .ref dest oo := by rw [slow1Eq]; exact outputPtr
    have end1 : c.end_ = .ref dest
        (oo + slow1.left.toNat - 257) := by
      simpa only [slow1Eq, pulled] using endPtr
    have left1 : slow1.left ≠ 0 := by simpa only [slow1Eq, pulled] using left
    have avail1 : 258 ≤ slow1.left.toNat := by
      simpa only [slow1Eq, pulled] using avail
    have size1 : oo + slow1.left.toNat ≤ output.size := by
      simpa only [slow1Eq, pulled] using outputSize
    have guard1 : C.run (Ptr.lt fast1.out c.end_) h = .ok (true, h) := by
      simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL] using guard
    by_cases needsSecond : fast1.bits < fast1.op
    · have small1 : slow1.bits.toNat ≤ 22 := by
        have selected := UInt32.lt_iff_toNat_lt.mp needsSecond
        rw [packet1.bits, op1] at selected
        omega
      obtain ⟨next2, fast2, slow2, pull2, next2Eq,
        slow2Eq, fast2Eq, packet2, _, buffers2, stream2⟩ :=
        packet1.pull_default_state invariant buffers1 small1
      have len2 : fast2.len = l.len := by
        simpa only [fast2Eq, Zlib.Inffast.Proofs.pullL] using len1
      have op2 : fast2.op = l.op := by
        simpa only [fast2Eq, Zlib.Inffast.Proofs.pullL] using op1
      have out2 : fast2.out = .ref dest j := by rw [fast2Eq]; exact out1
      have put2 : slow2.put = .ref dest oo := by rw [slow2Eq]; exact put1
      have end2 : c.end_ = .ref dest
          (oo + slow2.left.toNat - 257) := by
        simpa only [slow2Eq, pulled] using end1
      have left2 : slow2.left ≠ 0 := by
        simpa only [slow2Eq, pulled] using left1
      have avail2 : 258 ≤ slow2.left.toNat := by
        simpa only [slow2Eq, pulled] using avail1
      have size2 : oo + slow2.left.toNat ≤ output.size := by
        simpa only [slow2Eq, pulled] using size1
      have guard2 : C.run (Ptr.lt fast2.out c.end_) h =
          .ok (true, h) := by
        simpa only [fast2Eq, Zlib.Inffast.Proofs.pullL] using guard1
      have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
        rw [slow1Eq]
        exact u32_add8 slow.bits (by omega)
      have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by
        rw [slow2Eq]
        exact u32_add8 slow1.bits (by omega)
      have fits2 : fast2.op.toNat ≤ slow2.bits.toNat := by
        rw [op2, bits2, bits1]
        omega
      have fastLength2 : 3 ≤ fast2.len.toNat ∧
          fast2.len.toNat ≤ 258 := by rw [len2]; exact length
      obtain ⟨result, after, array, next, contRun, out, lower, upper, bytes, size⟩ :=
        packet2.distCont_output_bound invariant buffers2 streamPtr statePtr
          whaveEq wsizeEq wnextEq windowEq fits2
          (by rw [op2]; omega) left2 avail2 fastLength2
          out2 put2 begPtr end2 outputGet outputWrite size2
          current beginLe span guard2
      have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after) := by
        change (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after)
        unfold Zlib.Inffast.Proofs.dodistBase
        simp only [needsFirst, ite_true]
        rw [bind_ok (by simpa only [C.run] using pull1)]
        simp only [needsSecond, ite_true]
        rw [bind_ok (by simpa only [C.run] using pull2)]
        exact contRun
      have lenEq : fast2.len = l.len := len2
      have upper' : next ≤ oo + slow.left.toNat := by
        simpa only [slow2Eq, slow1Eq, pulled] using upper
      exact ⟨result, after, array, next, run, out, lower, upper', bytes, size⟩
    · have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
        have notLess : ¬ slow1.bits.toNat < fast1.op.toNat := by
          intro hlt
          exact needsSecond (UInt32.lt_iff_toNat_lt.mpr
            (by rw [packet1.bits]; exact hlt))
        omega
      have fastLength1 : 3 ≤ fast1.len.toNat ∧
          fast1.len.toNat ≤ 258 := by rw [len1]; exact length
      obtain ⟨result, after, array, next, contRun, out, lower, upper, bytes, size⟩ :=
        packet1.distCont_output_bound invariant buffers1 streamPtr statePtr
          whaveEq wsizeEq wnextEq windowEq fits1
          (by rw [op1]; omega) left1 avail1 fastLength1
          out1 put1 begPtr end1 outputGet outputWrite size1
          current beginLe span guard1
      have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after) := by
        change (Zlib.Inffast.Proofs.dodistBase c l) h =
          .ok (result, after)
        unfold Zlib.Inffast.Proofs.dodistBase
        simp only [needsFirst, ite_true]
        rw [bind_ok (by simpa only [C.run] using pull1)]
        simp only [needsSecond, ite_false]
        exact contRun
      have upper' : next ≤ oo + slow.left.toNat := by
        simpa only [slow1Eq, pulled] using upper
      exact ⟨result, after, array, next, run, out, lower, upper', bytes, size⟩
  · have fits0 : l.op.toNat ≤ slow.bits.toNat := by
      have notLess : ¬ slow.bits.toNat < l.op.toNat := by
        intro hlt
        exact needsFirst (UInt32.lt_iff_toNat_lt.mpr
          (by rw [packet.bits]; exact hlt))
      omega
    obtain ⟨result, after, array, next, contRun, out, lower, upper, bytes, size⟩ :=
      packet.distCont_output_bound invariant buffers streamPtr statePtr
        whaveEq wsizeEq wnextEq windowEq fits0
        (by omega) left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe
        span guard
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after)
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_false]
      exact contRun
    exact ⟨result, after, array, next, run, out, lower, upper, bytes, size⟩


theorem FastInputPacket.dodist_base_leaf_output_bound
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true)
    (extraBound : (codes[index].op.toUInt32 &&& 15).toNat ≤ 13)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againD := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: second :: rest) firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeBits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeWidth
    omega
  have dropped := firstPacket.drop_bits_default_state buffers
    count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: second :: rest) afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: second :: rest) := dropped.2.1
  have codeStream : stream slowCode (first :: second :: rest) =
      (stream slow (first :: second :: rest)).drop
        entry.bits.toNat := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32] using dropped.2.2.1
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    dist := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: second :: rest) baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeLeft : slowCode.left ≠ 0 := left
  have codeAvail : 258 ≤ slowCode.left.toNat := avail
  have codeSize : oo + slowCode.left.toNat ≤ output.size := outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  have baseExtra : baseLocal.op.toNat ≤ 13 := extraBound
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat ≤ 258 := length
  have baseEntry : (entry.op.toUInt32 &&& 16 != 0) = true := by
    simpa only [entry] using base
  obtain ⟨result, after, array, next, baseRun, out, lower, upper, bytes, size⟩ :=
    basePacket.dodistBase_output_bound invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      baseExtra codeLeft codeAvail baseLength baseOut codePut
      begPtr codeEnd outputGet outputWrite codeSize current
      beginLe span baseGuard
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have run : C.run (Zlib.Inffast.dodist c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.dodist c l) h = .ok (result, after)
    rw [Zlib.Inffast.Proofs.dodist_eq_base]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [baseEntry, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode, firstLocal,
      count, entry] using baseRun
  exact ⟨result, after, array, next, run, out,
    lower, upper, bytes, size⟩


theorem FastInputPacket.dodist_root_output_bound
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootBits rootIndex : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootIndex))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootBits)
    (root : rootIndex < 2 ^ rootBits)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  have cases := dist_table_root_cases safe root
  dsimp only at cases ⊢
  obtain ⟨indexBound, codeWidth, classified⟩ := cases
  have entryEq : codes.getD (baseOff + rootIndex) default =
      codes[baseOff + rootIndex] := by
    simp [Array.getD_eq_getD_getElem?, indexBound]
  rw [entryEq] at codeWidth classified
  let entry : Code := codes[baseOff + rootIndex]
  have bitsFit : entry.bits.toNat ≤ slow.bits.toNat := by
    simpa only [entry] using
      (show codes[baseOff + rootIndex].bits.toNat ≤
        slow.bits.toNat by omega)
  have cursorBound : j ≤ oo + slow.left.toNat := by
    have geometry := fast_output_room_of_guard outPtr endPtr
      outputGet outputSize current avail length.2 guard
    omega
  rcases classified with baseClass | linkClass | invalidClass
  · have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simpa only [entry, bne_iff_ne] using baseClass.1
    have extras : (entry.op.toUInt32 &&& 15).toNat ≤ 13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      simpa only [entry] using baseClass.2.1
    obtain ⟨result, after, array, next, run, out,
      lower, upper, bytes, size⟩ :=
      packet.dodist_base_leaf_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet indexBound bitsFit codeWidth baseBool
        extras left avail length outPtr outputPtr begPtr endPtr
        outputGet outputWrite outputSize current beginLe span guard
    exact ⟨result, after, array, next, run, out,
      lower, upper, bytes, size⟩
  · have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp only [entry, linkClass.1, bne_self_eq_false]
    have linkBool : (entry.op.toUInt32 &&& 64 == 0) = true := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp only [entry, linkClass.2.1, beq_self_eq_true]
    obtain ⟨result, slowNext, slice, run, sliceBound,
      here, againD, _, out, _, packetAfter, _, buffersAfter, source⟩ :=
      packet.dodist_link_default_state invariant buffers
        herePtr dcodePtr codesGet indexBound bitsFit codeWidth
        notBase linkBool linkClass.2.2.2.1
        linkClass.2.2.2.2
    exact ⟨result, h, output, j, run,
      out.trans outPtr, Nat.le_refl _, cursorBound, outputGet, rfl⟩
  · have notBase : (entry.op.toUInt32 &&& 16 != 0) = false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp only [entry, invalidClass.1, bne_self_eq_false]
    have notLink : (entry.op.toUInt32 &&& 64 == 0) = false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [entry, invalidClass.2]
    obtain ⟨i, after, result, slowNext, run, heapEq,
      broke, againD, _, out, packetAfter, stateAfter,
      buffersAfter, sizes, source⟩ :=
      packet.dodist_invalid_leaf_default_state invariant buffers
        streamPtr statePtr herePtr codesGet indexBound bitsFit
        codeWidth notBase notLink
    obtain ⟨afterArray, afterGet, afterSize⟩ :=
      sizes.view outputGet
    exact ⟨result, after, afterArray, j, run,
      out.trans outPtr, Nat.le_refl _, cursorBound,
      afterGet, afterSize⟩


theorem FastInputPacket.dodist_linked_leaf_output_bound
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : DistLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ linked result after array next,
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dodist c linked) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : DistLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨rootWidthBound, _, opWidth,
    subtable, _⟩
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨linked, slice, firstRun, sliceBound, here,
    againD, _, linkedOut, linkedLen, linkedPacket, _,
    linkedBuffers, source⟩ :=
    packet.dodist_link_default_state_exact invariant buffers
      herePtr dcodePtr codesGet rootBound rootFits
      rootWidthBound notBase linkBool opWidth
      subtable
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have target := dist_table_link_target safe root link
    (by simpa only [rootEq] using sliceBound)
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
      default =
      codes[baseOff +
        (codes[baseOff + rootSlice].val.toNat + slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetLeaf : DistLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq] using target.2.1
  have targetBits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit held rootFits targetLeaf.1
      (by simpa only [slowLink] using source)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    omega
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using here
  have targetOut : linked.out = .ref dest j := linkedOut.trans outPtr
  have targetLen : 3 ≤ linked.len.toNat ∧
      linked.len.toNat ≤ 258 := by
    simpa only [linkedLen] using length
  have targetGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut] using guard
  rcases targetLeaf.2 with baseClass | invalidClass
  · have baseBool :
        (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
          true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [baseClass.1]
    have extraBound :
        (codes[targetIndex].op.toUInt32 &&& 15).toNat ≤
          13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      exact baseClass.2.1
    obtain ⟨result, after, array, next, secondRun, out, lower, upper, bytes, size⟩ :=
      linkedPacket.dodist_base_leaf_output_bound invariant
        linkedBuffers streamPtr statePtr whaveEq wsizeEq
        wnextEq windowEq targetHere codesGet targetBound
        targetBits targetWidth baseBool extraBound
        (by simpa only [slowLink] using left)
        (by simpa only [slowLink] using avail)
        targetLen targetOut
        (by simpa only [slowLink] using outputPtr)
        begPtr (by simpa only [slowLink] using endPtr)
        outputGet outputWrite
        (by simpa only [slowLink] using outputSize)
        current beginLe span targetGuard
    exact ⟨linked, result, after, array, next, firstRun, secondRun, out,
      lower, by simpa only [slowLink] using upper, bytes, size⟩
  · have notBaseLeaf :
        (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [invalidClass.1]
    have notLinkLeaf :
        (codes[targetIndex].op.toUInt32 &&& 64 == 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [invalidClass.2]
    obtain ⟨i, after, result, slowNext, secondRun, heapEq,
      broke, noAgain, _, out, finalPacket, finalState,
      finalBuffers, sizes, secondSource⟩ :=
      linkedPacket.dodist_invalid_leaf_default_state
        invariant linkedBuffers streamPtr statePtr targetHere
        codesGet targetBound targetBits targetWidth
        notBaseLeaf notLinkLeaf
    obtain ⟨afterArray, afterGet, afterSize⟩ :=
      sizes.view outputGet
    have cursorBound : j ≤ oo + slow.left.toNat := by
      have geometry := fast_output_room_of_guard outPtr endPtr
        outputGet outputSize current avail length.2 guard
      omega
    exact ⟨linked, result, after, afterArray, j, firstRun, secondRun,
      out.trans (linkedOut.trans outPtr), Nat.le_refl _,
      cursorBound, afterGet, afterSize⟩


theorem FastInputPacket.dodist_loop_output_bound
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  have rootCases := dist_table_root_cases safe root
  dsimp only at rootCases
  obtain ⟨rootBound, rootWidthBound, classes⟩ := rootCases
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  rw [rootEq] at rootWidthBound classes
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have rootLoad : Ptr.load l.here h =
      .ok (codes[baseOff + rootSlice], h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet rootBound
  rcases classes with baseClass | linkClass | invalidClass
  · have baseBool :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [baseClass.1]
    have extras :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 15).toNat ≤
          13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      exact baseClass.2.1
    obtain ⟨result, after, array, next, run, out,
      lower, upper, bytes, size⟩ :=
      packet.dodist_base_leaf_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound rootFits rootWidthBound
        baseBool extras left avail length outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    have noAgain := Zlib.Inffast.Proofs.dodist_base_againD_false
      rootLoad rootWidthBound baseBool run
    have cond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L))) run cond
    exact ⟨result, after, array, next, loop, out,
      lower, upper, bytes, size⟩
  · have rootLink : DistLink
        (codes.getD (baseOff + rootSlice) default) := by
      rw [rootEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    obtain ⟨linked, slice, firstRun, againD,
      sliceBound, here, leaf, used, slowNext,
      result, after, usedBound, secondRun,
      finalPacket, finalBuffers, sizes, outcome⟩ :=
      packet.dodist_linked_leaf_default_state invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    let targetIndex : Nat := baseOff +
      codes[baseOff + rootSlice].val.toNat + slice
    have targetBound : targetIndex < codes.size := by
      have bound := linkClass.2.2.2.2
      have sliceLimit : slice <
          2 ^ codes[baseOff + rootSlice].op.toNat := by
        simpa only [rootEq] using sliceBound
      omega
    have targetEq : codes.getD targetIndex default =
        codes[targetIndex] := by
      simp [Array.getD_eq_getD_getElem?, targetBound]
    have targetEqNorm : codes.getD
        (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
        default =
        codes[baseOff +
          (codes[baseOff + rootSlice].val.toNat + slice)] := by
      simpa only [targetIndex, Nat.add_assoc] using targetEq
    have targetLeaf : DistLeaf
        codes[baseOff + rootSlice].bits.toNat
        codes[targetIndex] := by
      simpa only [rootEq, targetIndex, targetEq] using leaf
    have targetHere : linked.here = .ref codeRef targetIndex := by
      simpa only [rootEq, targetIndex] using here
    have targetLoad : Ptr.load linked.here h =
        .ok (codes[targetIndex], h) := by
      rw [targetHere]
      exact Ptr.load_ok codesGet targetBound
    have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
      omega
    have noAgain : result.againD = false := by
      rcases targetLeaf.2 with base | invalid
      · have baseBool :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
              true := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [base.1]
        exact Zlib.Inffast.Proofs.dodist_base_againD_false
          targetLoad targetWidth baseBool secondRun
      · have notBase :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
              false := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [invalid.1]
        have notLink :
            (codes[targetIndex].op.toUInt32 &&& 64 == 0) =
              false := by
          rw [Zlib.Inffast.Proofs.mask64]
          simp [invalid.2]
        exact Zlib.Inffast.Proofs.dodist_invalid_againD_false
          targetLoad targetWidth notBase notLink secondRun
    have condFirst :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          linked h = .ok ((true, linked), h) := by
      simp [againD]
    have condSecond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L)))
      firstRun condFirst secondRun condSecond
    obtain ⟨linked2, result2, after2, array, next,
      firstRun2, secondRun2, out, lower, upper,
      bytes, size⟩ :=
      packet.dodist_linked_leaf_output_bound invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    have sameFirst : (linked, h) = (linked2, h) :=
      Except.ok.inj (firstRun.symm.trans firstRun2)
    have linkedEq : linked = linked2 :=
      congrArg Prod.fst sameFirst
    subst linked2
    have sameSecond : (result, after) =
        (result2, after2) :=
      Except.ok.inj (secondRun.symm.trans secondRun2)
    cases sameSecond
    exact ⟨result, after, array, next, loop, out,
      lower, upper, bytes, size⟩
  · have notBase :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [invalidClass.1]
    have notLink :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [invalidClass.2]
    obtain ⟨i, after, result, slowNext, run, heapEq,
      broke, noAgain, _, out, finalPacket, finalState,
      finalBuffers, sizes, source⟩ :=
      packet.dodist_invalid_leaf_default_state invariant
        buffers streamPtr statePtr herePtr codesGet
        rootBound rootFits rootWidthBound notBase notLink
    have cond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L))) run cond
    obtain ⟨afterArray, afterGet, afterSize⟩ :=
      sizes.view outputGet
    have cursorBound : j ≤ oo + slow.left.toNat := by
      have geometry := fast_output_room_of_guard outPtr endPtr
        outputGet outputSize current avail length.2 guard
      omega
    exact ⟨result, after, afterArray, j, loop,
      out.trans outPtr, Nat.le_refl _, cursorBound,
      afterGet, afterSize⟩


theorem FastInputPacket.dolenDist_output_bound
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let idx : Nat := (l.hold &&& c.dmask.toUInt64).toNat
  have idxEq : idx = l.hold.toNat % 2 ^ rootWidth := by
    exact Zlib.Inffast.Proofs.u64_and_mask mask
  have idxBound : idx < 2 ^ rootWidth := by
    rw [idxEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.dcode idx) h =
      .ok (.ref codeRef (baseOff + idx), h) := by
    rw [dcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + idx) }
  have selectedPacket : FastInputPacket h slow
      (first :: second :: rest) selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, after, array, next, loopRun, out, lower, upper, bytes, size⟩ :=
    selectedPacket.dodist_loop_output_bound invariant
      buffers streamPtr statePtr whaveEq wsizeEq wnextEq
      windowEq (by rfl) dcodePtr codesGet safe idxBound
      held left avail length outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have run : C.run (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenDist
    change Ptr.add c.dcode idx h =
      .ok (.ref codeRef (baseOff + idx), h) at addRun
    rw [bind_ok addRun]
    simpa [C.run, selected] using loopRun
  exact ⟨result, after, array, next, run, out,
    lower, upper, bytes, size⟩


theorem FastInputPacket.dolenRefill_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenRefill c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases needsPull : l.bits < 15
  · have small0 : slow.bits.toNat ≤ 22 := by
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next1, fast1, slow1, pull1, _,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small0
    have small1 : slow1.bits.toNat ≤ 22 := by
      rw [slow1Eq]
      change (slow.bits + 8).toNat ≤ 22
      rw [u32_add8 slow.bits (by omega)]
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next2, fast2, slow2, pull2, _,
      slow2Eq, fast2Eq, packet2, _, buffers2, stream2⟩ :=
      packet1.pull_default_state invariant buffers1 small1
    have held2 : 15 ≤ slow2.bits.toNat := by
      rw [slow2Eq, slow1Eq]
      change ((slow.bits + 8) + 8).toNat ≥ 15
      rw [u32_add8 (slow.bits + 8) (by
          have bound : (slow.bits + 8).toNat ≤ 22 := by
            simpa only [slow1Eq, pulled] using small1
          omega),
        u32_add8 slow.bits (by omega)]
      omega
    have left2 : slow2.left ≠ 0 := by
      simpa only [slow2Eq, slow1Eq, pulled] using left
    have avail2 : 258 ≤ slow2.left.toNat := by
      simpa only [slow2Eq, slow1Eq, pulled] using avail
    have length2 : 3 ≤ fast2.len.toNat ∧
        fast2.len.toNat ≤ 258 := by
      simpa only [fast2Eq, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using length
    have out2 : fast2.out = .ref dest j := by
      simpa only [fast2Eq, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using outPtr
    have put2 : slow2.put = .ref dest oo := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputPtr
    have end2 : c.end_ = .ref dest
        (oo + slow2.left.toNat - 257) := by
      simpa only [slow2Eq, slow1Eq, pulled] using endPtr
    have size2 : oo + slow2.left.toNat ≤ output.size := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputSize
    have guard2 : C.run (Ptr.lt fast2.out c.end_) h =
        .ok (true, h) := by
      simpa only [fast2Eq, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using guard
    obtain ⟨result, after, array, next, distRun, out, lower, upper, bytes, size⟩ :=
      packet2.dolenDist_output_bound invariant buffers2
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask held2 left2 avail2
        length2 out2 put2 begPtr end2 outputGet outputWrite
        size2 current beginLe span guard2
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_true]
      change (Zlib.Inffast.pull l >>= fun q =>
        Zlib.Inffast.pull q >>= fun q' =>
        Zlib.Inffast.Proofs.dolenDist c q') h =
          .ok (result, after)
      change (Zlib.Inffast.pull l) h =
        .ok (fast1, h) at pull1
      change (Zlib.Inffast.pull fast1) h =
        .ok (fast2, h) at pull2
      change (Zlib.Inffast.Proofs.dolenDist c fast2) h =
        .ok (result, after) at distRun
      simp only [bind_app, pull1, pull2, distRun]
    have upper' : next ≤ oo + slow.left.toNat := by
      simpa only [slow2Eq, slow1Eq, pulled] using upper
    exact ⟨result, after, array, next, run, out, lower,
      upper', bytes, size⟩
  · have held : 15 ≤ slow.bits.toNat := by
      have h : ¬ l.bits.toNat < 15 := by
        intro less
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
      rw [packet.bits] at h
      omega
    obtain ⟨result, after, array, next, distRun, out, lower, upper, bytes, size⟩ :=
      packet.dolenDist_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask held left avail length
        outPtr outputPtr begPtr endPtr outputGet outputWrite
        outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_false]
      exact distRun
    exact ⟨result, after, array, next, run, out,
      lower, upper, bytes, size⟩


theorem FastInputPacket.dolenExt_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (extraFits : l.op.toNat ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenExt c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let extra : Nat := l.hold.toNat % 2 ^ l.op.toNat
  have opSmall : l.op.toNat < 32 := by omega
  have low := Zlib.Inffast.Proofs.hold_low32
    (x := l.hold) (k := l.op) opSmall
  have extraBound : extra < 2 ^ l.op.toNat := by
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have lenSum : l.len.toNat + extra ≤ 258 := by omega
  let delta : UInt32 := l.hold.toUInt32 &&&
    (((1 : UInt32) <<< l.op) - 1)
  have deltaEq : delta.toNat = extra := by
    simpa only [delta, extra] using low
  have lenValue : (l.len + delta).toNat =
      l.len.toNat + extra := by
    rw [Zlib.Inffast.Proofs.u32_toNat_add
      (by rw [deltaEq]; omega), deltaEq]
  have shlRun : Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok opSmall
  have shrRun : Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  let afterLen : Zlib.Inffast.L := { l with len := l.len + delta }
  have afterLenPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) afterLen :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have within : l.op.toNat ≤ slow.bits.toNat := extraFits
  have dropped := afterLenPacket.drop_bits_default_state buffers
    l.op within (by omega)
  let slowDrop : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let fastDrop : Zlib.Inffast.L := { afterLen with
    hold := afterLen.hold >>> l.op.toUInt64,
    bits := afterLen.bits - l.op }
  have dropPacket : FastInputPacket h slowDrop
      (first :: second :: third :: fourth :: rest) fastDrop :=
    dropped.1
  have dropBuffers : DispatchBuffers h r slowDrop
      (first :: second :: third :: fourth :: rest) :=
    dropped.2.1
  have dropStream : stream slowDrop
      (first :: second :: third :: fourth :: rest) =
      (stream slow
        (first :: second :: third :: fourth :: rest)).drop
          l.op.toNat := dropped.2.2.1
  have dropBits : slowDrop.bits.toNat =
      slow.bits.toNat - l.op.toNat := dropped.2.2.2
  have dropBound : slowDrop.bits.toNat ≤ 30 := by omega
  have dropLength : 3 ≤ fastDrop.len.toNat ∧
      fastDrop.len.toNat ≤ 258 := by
    simpa only [fastDrop, afterLen, lenValue] using
      (show 3 ≤ l.len.toNat + extra ∧
        l.len.toNat + extra ≤ 258 by omega)
  have dropOut : fastDrop.out = .ref dest j := outPtr
  have dropPut : slowDrop.put = .ref dest oo := outputPtr
  have dropEnd : c.end_ = .ref dest
      (oo + slowDrop.left.toNat - 257) := endPtr
  have dropSize : oo + slowDrop.left.toNat ≤ output.size :=
    outputSize
  have dropGuard : C.run (Ptr.lt fastDrop.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨result, after, array, next, refillRun, out, lower, upper, bytes, size⟩ :=
    dropPacket.dolenRefill_output_bound invariant dropBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask dropBound left avail
      dropLength dropOut dropPut begPtr dropEnd outputGet
      outputWrite dropSize current beginLe span dropGuard
  have run : C.run (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenExt
    rw [bind_ok shlRun]
    rw [bind_ok shrRun]
    simpa only [fastDrop, afterLen, delta, C.run] using refillRun
  exact ⟨result, after, array, next, run, out,
    lower, upper, bytes, size⟩


theorem FastInputPacket.dolenLen_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases hasExtra : l.op != 0
  · by_cases needsPull : l.bits < l.op
    · have small : slow.bits.toNat ≤ 22 := by
        have less := UInt32.lt_iff_toNat_lt.mp needsPull
        rw [packet.bits] at less
        omega
      obtain ⟨next1, fast1, slow1, pullRun, _,
        slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
        packet.pull_default_state invariant buffers small
      have opEq : fast1.op = l.op := by
        rw [fast1Eq]
        rfl
      have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
        rw [opEq, slow1Eq]
        change l.op.toNat ≤ (slow.bits + 8).toNat
        rw [u32_add8 slow.bits (by omega)]
        omega
      have bound1 : slow1.bits.toNat ≤ 30 := by
        rw [slow1Eq]
        change (slow.bits + 8).toNat ≤ 30
        rw [u32_add8 slow.bits (by omega)]
        omega
      have width1 : fast1.op.toNat ≤ 5 := by
        rw [opEq]
        exact extraWidth
      have length1 : 3 ≤ fast1.len.toNat ∧
          fast1.len.toNat + 2 ^ fast1.op.toNat ≤ 259 := by
        simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
          using length
      have out1 : fast1.out = .ref dest j := by
        simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
          using outPtr
      have put1 : slow1.put = .ref dest oo := by
        simpa only [slow1Eq, pulled] using outputPtr
      have end1 : c.end_ = .ref dest
          (oo + slow1.left.toNat - 257) := by
        simpa only [slow1Eq, pulled] using endPtr
      have size1 : oo + slow1.left.toNat ≤ output.size := by
        simpa only [slow1Eq, pulled] using outputSize
      have guard1 : C.run (Ptr.lt fast1.out c.end_) h =
          .ok (true, h) := by
        simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
          using guard
      obtain ⟨result, after, array, next, extRun, out, lower, upper, bytes, size⟩ :=
        packet1.dolenExt_output_bound invariant buffers1
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask width1 fits1 bound1
          (by simpa only [slow1Eq, pulled] using left)
          (by simpa only [slow1Eq, pulled] using avail)
          length1 out1 put1 begPtr end1 outputGet outputWrite
          size1 current beginLe span guard1
      have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after) := by
        change (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after)
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, needsPull, ite_true]
        change (Zlib.Inffast.pull l >>= fun q =>
          Zlib.Inffast.Proofs.dolenExt c q) h =
            .ok (result, after)
        change (Zlib.Inffast.pull l) h =
          .ok (fast1, h) at pullRun
        change (Zlib.Inffast.Proofs.dolenExt c fast1) h =
          .ok (result, after) at extRun
        simp only [bind_app, pullRun, extRun]
      have upper' : next ≤ oo + slow.left.toNat := by
        simpa only [slow1Eq, pulled] using upper
      exact ⟨result, after, array, next, run, out,
        lower, upper', bytes, size⟩
    · have fits : l.op.toNat ≤ slow.bits.toNat := by
        have noLess : ¬ l.op.toNat > l.bits.toNat := by
          intro h
          exact needsPull (UInt32.lt_iff_toNat_lt.mpr h)
        rw [packet.bits] at noLess
        omega
      obtain ⟨result, after, array, next, extRun, out, lower, upper, bytes, size⟩ :=
        packet.dolenExt_output_bound invariant buffers
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask extraWidth fits bitsBound
          left avail length outPtr outputPtr begPtr endPtr
          outputGet outputWrite outputSize current beginLe
          span guard
      have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after) := by
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, needsPull, ite_true, ite_false]
        exact extRun
      exact ⟨result, after, array, next, run, out,
        lower, upper, bytes, size⟩
  · have opZero : l.op = 0 := by
      simpa using hasExtra
    have length0 : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258 := by
      rw [opZero] at length
      simp only [UInt32.toNat_zero, Nat.pow_zero] at length
      omega
    obtain ⟨result, after, array, next, refillRun, out, lower, upper, bytes, size⟩ :=
      packet.dolenRefill_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask bitsBound left avail
        length0 outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenLen
      simp only [hasExtra, ite_false]
      exact refillRun
    exact ⟨result, after, array, next, run, out,
      lower, upper, bytes, size⟩


theorem FastInputPacket.dolen_base_leaf_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let entry : Code := lenCodes[index]
  have load : Ptr.load l.here h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok lenGet indexBound
  let count : UInt32 := entry.bits.toUInt32
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
      using codeFits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
        using codeWidth
    omega
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest)
      firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := firstPacket.drop_bits_default_state
    buffers count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: fifth :: rest)
      afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: second :: third :: fourth :: fifth :: rest) :=
    dropped.2.1
  have codeStream : stream slowCode
      (first :: second :: third :: fourth :: fifth :: rest) =
      List.drop entry.bits.toNat
        (stream slow
          (first :: second :: third :: fourth :: fifth :: rest)) := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32]
      using dropped.2.2.1
  have codeBound : slowCode.bits.toNat ≤ 30 := by
    have remaining : slowCode.bits.toNat =
        slow.bits.toNat - count.toNat := dropped.2.2.2
    omega
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    len := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: fifth :: rest)
      baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [baseLocal, entry] using extraWidth
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simp only [baseLocal, Zlib.Inffast.Proofs.toNat32]
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [entry, UInt16.toNat_toUInt32] using lengthBase
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeSize : oo + slowCode.left.toNat ≤ output.size :=
    outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨result, after, array, next, lenRun, out, lower, upper, bytes, size⟩ :=
    basePacket.dolenLen_output_bound invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr distGet distSafe distMask baseWidth codeBound
      left avail baseLength baseOut codePut begPtr codeEnd
      outputGet outputWrite codeSize current beginLe span
      baseGuard
  have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
    rw [Zlib.Inffast.Proofs.mask16]
    simpa only [entry, bne_iff_ne] using base
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzero : entry.op.toUInt32 ≠ 0 := by
      intro zero
      rw [zero] at baseBool
      simp at baseBool
    simp [nonzero]
  have shiftRun : Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.dolen c l) h = .ok (result, after)
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, baseBool,
      Bool.false_eq_true, ite_false, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode,
      firstLocal, count, entry] using lenRun
  exact ⟨result, after, array, next, run, out,
    lower, upper, bytes, size⟩

#print axioms FastInputPacket.dolen_base_leaf_output_bound
theorem FastInputPacket.dolen_root_literal_loop_output_bound
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
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
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
  obtain ⟨run, noAgain, _, _, _, _, _, finalGet, _, _⟩ :=
    packet.dolen_literal_default_state invariant buffers
      herePtr lenGet indexBound codeFits codeWidth literal
      left avail outPtr outputPtr endPtr outputGet
      outputWrite outputSize current guard
  have loopRun := dolen_loop_one run noAgain
  have inside : j + 1 ≤ oo + slow.left.toNat := by
    let one : Zlib.Inffast.L := { l with len := 1 }
    have oneGuard : C.run (Ptr.lt one.out c.end_) h =
        .ok (true, h) := guard
    have oneRoom := fast_output_room_of_guard
      (l := one) (slow := slow) outPtr endPtr outputGet
      outputSize current avail (by simp [one]) oneGuard
    have room := oneRoom.2.2
    change j + 1 ≤ oo + slow.left.toNat at room
    exact room
  have jsize : j < output.size := by omega
  have arraySize : (output.set! j entry.val.toUInt8).size =
      output.size := by simp [Array.size_set!]
  exact ⟨result, after, output.set! j entry.val.toUInt8,
    j + 1, loopRun, rfl, by omega, inside,
    finalGet, arraySize⟩

theorem FastInputPacket.dolen_root_base_loop_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨result, after, array, next, run, out, lower,
    upper, bytes, size⟩ :=
    packet.dolen_base_leaf_output_bound invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth
      base extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  obtain ⟨extra, used, consumed, slowNext, result₂, after₂,
    _, _, _, oldRun, noAgain₂, _, _, _, _, _, _⟩ :=
    packet.dolen_base_leaf_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth
      base extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have resultEq : result₂ = result := by
    rw [run] at oldRun
    exact (Prod.mk.inj (Except.ok.inj oldRun)).1.symm
  have noAgain : result.againL = false := by
    rw [resultEq] at noAgain₂
    exact noAgain₂
  exact ⟨result, after, array, next,
    dolen_loop_one run noAgain, out, lower, upper,
    bytes, size⟩

theorem FastInputPacket.dolen_root_end_loop_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (endCode : (codes[index].op.toUInt32 &&& 32 != 0) = true)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (cursorBound : j ≤ oo + slow.left.toNat) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨result, slowNext, run, _, noAgain, _, outEq,
    _, _, _, _, _⟩ :=
    packet.dolen_end_leaf_default_state invariant buffers
      statePtr mode herePtr codesGet codeIndex codeBits
      codeWidth nonzero notBase notLink endCode
  have afterGet : Space.get (setI h zs { s with mode := TYPE }) dest =
      some output := by
    rw [byte_view_get_setI]
    exact outputGet
  exact ⟨result, setI h zs { s with mode := TYPE }, output,
    j, dolen_loop_one run noAgain,
    outEq.trans outPtr, Nat.le_refl _,
    cursorBound, afterGet, rfl⟩

theorem FastInputPacket.dolen_root_invalid_loop_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (nonzero : codes[index].op ≠ 0)
    (notBase : (codes[index].op.toUInt32 &&& 16 != 0) = false)
    (notLink : (codes[index].op.toUInt32 &&& 64 == 0) = false)
    (notEnd : (codes[index].op.toUInt32 &&& 32 != 0) = false)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (cursorBound : j ≤ oo + slow.left.toNat) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨i, after, result, slowNext, run, heapEq,
    _, noAgain, _, outEq, _, _, _, _, _⟩ :=
    packet.dolen_invalid_leaf_default_state invariant
      buffers streamPtr statePtr herePtr codesGet
      codeIndex codeBits codeWidth nonzero notBase
      notLink notEnd
  have afterGet : Space.get after dest = some output := by
    rw [heapEq]
    dsimp [badHeap]
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact outputGet
  exact ⟨result, after, output, j,
    dolen_loop_one run noAgain, outEq.trans outPtr,
    Nat.le_refl _, cursorBound, afterGet, rfl⟩

theorem FastInputPacket.dolen_root_nonlink_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (notLinkRoot : ¬ LenLink
      (codes.getD (baseOff + rootSlice) default))
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨indexBound, classes⟩ :=
    len_table_root_source_cases safe root
  let entry : Code := codes.getD (baseOff + rootSlice) default
  have entryEq : entry = codes[baseOff + rootSlice] := by
    simp only [entry]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have cursorBound : j ≤ oo + slow.left.toNat := by
    let one : Zlib.Inffast.L := { l with len := 1 }
    have oneGuard : C.run (Ptr.lt one.out c.end_) h =
        .ok (true, h) := guard
    have oneRoom := fast_output_room_of_guard
      (l := one) (slow := slow) outPtr endPtr outputGet
      outputSize current avail (by simp [one]) oneGuard
    have room := oneRoom.2.2
    change j + 1 ≤ oo + slow.left.toNat at room
    omega
  rcases classes with ⟨link, _⟩ |
    ⟨_, width, literal | base | terminal | invalid⟩
  · exact False.elim (notLinkRoot link)
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have literalCode : codes[baseOff + rootSlice].op = 0 := by
      simpa only [← entryEq] using literal
    exact packet.dolen_root_literal_loop_output_bound
      invariant buffers herePtr codesGet indexBound
      codeFits codeWidth literalCode left avail outPtr
      outputPtr endPtr outputGet outputWrite outputSize
      current guard
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have baseCode : codes[baseOff + rootSlice].op &&& 16 ≠ 0 ∧
        (codes[baseOff + rootSlice].op &&& 15).toNat ≤ 5 ∧
        3 ≤ codes[baseOff + rootSlice].val.toNat ∧
        codes[baseOff + rootSlice].val.toNat +
          2 ^ (codes[baseOff + rootSlice].op &&& 15).toNat ≤
          259 := by simpa only [← entryEq] using base
    exact packet.dolen_root_base_loop_output_bound
      invariant buffers streamPtr statePtr whaveEq
      wsizeEq wnextEq windowEq herePtr codesGet
      indexBound codeFits codeWidth baseCode.1
      baseCode.2.1 ⟨baseCode.2.2.1, baseCode.2.2.2⟩
      dcodePtr distGet distSafe distMask bitsBound
      left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe
      span guard
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have terminalCode : codes[baseOff + rootSlice].op ≠ 0 ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 32 != 0) =
          true := by simpa only [← entryEq] using terminal
    exact packet.dolen_root_end_loop_output_bound
      invariant buffers statePtr mode herePtr codesGet
      indexBound codeFits codeWidth terminalCode.1
      terminalCode.2.1 terminalCode.2.2.1
      terminalCode.2.2.2 outPtr outputPtr outputGet
      outputSize cursorBound
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have invalidCode : codes[baseOff + rootSlice].op ≠ 0 ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 32 != 0) =
          false := by simpa only [← entryEq] using invalid
    exact packet.dolen_root_invalid_loop_output_bound
      invariant buffers streamPtr statePtr herePtr
      codesGet indexBound codeFits codeWidth
      invalidCode.1 invalidCode.2.1
      invalidCode.2.2.1 invalidCode.2.2.2
      outPtr outputPtr outputGet outputSize cursorBound


/-- Composition of a linked length pass and a terminal leaf preserves
all output evidence, including a terminal break. -/
theorem dolen_two_pass_output_bound
    {h after : Heap} {l linked result : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {dest : BRef} {array : Array UInt8}
    {j next bound size : Nat}
    (first : C.run (Zlib.Inffast.dolen c l) h =
      .ok (linked, h))
    (again : linked.againL = true)
    (second : C.run (Zlib.Inffast.dolen c linked) h =
      .ok (result, after))
    (done : result.againL = false)
    (out : result.out = .ref dest next)
    (lower : j ≤ next)
    (upper : next ≤ bound)
    (bytes : Space.get after dest = some array)
    (arraySize : array.size = size) :
    ∃ final heap output finish,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (final, heap) ∧
      final.out = .ref dest finish ∧
      j ≤ finish ∧ finish ≤ bound ∧
      Space.get heap dest = some output ∧
      output.size = size := by
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two first
      (by simp only [again, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      second
      (by simp only [done, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  exact ⟨result, after, array, next, loopRun,
    out, lower, upper, bytes, arraySize⟩

theorem FastInputPacket.dolen_linked_base_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      ((let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
        target.op &&& 16 ≠ 0 ∧
        (target.op &&& 15).toNat ≤ 5 ∧
        3 ≤ target.val.toNat ∧
        target.val.toNat +
          2 ^ (target.op &&& 15).toNat ≤ 259) →
        ∃ result after array next,
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.out = .ref dest next ∧
          j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
          Space.get after dest = some array ∧
          array.size = output.size) := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨rootWidthBound, _, opWidth,
    subtable, _⟩
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.2.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨linked, slice, firstRun, sliceBound, linkedHere,
    againL, _, linkedOutEq, _, linkedPacket, _,
    linkedBuffers, linkedSource⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits
      rootWidthBound rootLink.1 notBase linkBool opWidth
      subtable
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have target := len_table_link_target safe root link
    (by simpa only [rootEq] using sliceBound)
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
      default =
      codes[baseOff +
        (codes[baseOff + rootSlice].val.toNat + slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using linkedHere
  have targetLeaf : LenLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq]
      using target.2.1
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit held rootFits targetLeaf.1
      (by simpa only [slowLink] using linkedSource)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have width := targetLeaf.1
    omega
  have linkedOut : linked.out = .ref dest j :=
    linkedOutEq.trans outPtr
  let rootCount : UInt32 :=
    codes[baseOff + rootSlice].bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := rootCount }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest)
      firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have rootCountFits : rootCount.toNat ≤ slow.bits.toNat := by
    simpa only [rootCount, Zlib.Inffast.Proofs.toNat32]
      using rootFits
  have rootCountSmall : rootCount.toNat < 64 := by
    have width : rootCount.toNat ≤ 15 := by
      simpa only [rootCount, Zlib.Inffast.Proofs.toNat32]
        using rootWidthBound
    omega
  have dropped := firstPacket.drop_bits_default_state
    buffers rootCount rootCountFits rootCountSmall
  have linkedBitsBound : slowLink.bits.toNat ≤ 30 := by
    have remaining : slowLink.bits.toNat =
        slow.bits.toNat - rootCount.toNat := by
      simpa only [slowLink, rootCount] using dropped.2.2.2
    omega
  have linkedPut : slowLink.put = .ref dest oo := outputPtr
  have linkedEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have linkedSize : oo + slowLink.left.toNat ≤ output.size :=
    outputSize
  have linkedGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut, outPtr] using guard
  refine ⟨linked, slice, firstRun, againL,
    by simpa only [rootEq] using sliceBound,
    by simpa only [rootEq, targetIndex] using linkedHere,
    ?_⟩
  intro selectedBase
  have base : codes[targetIndex].op &&& 16 ≠ 0 ∧
      (codes[targetIndex].op &&& 15).toNat ≤ 5 ∧
      3 ≤ codes[targetIndex].val.toNat ∧
      codes[targetIndex].val.toNat +
        2 ^ (codes[targetIndex].op &&& 15).toNat ≤ 259 := by
    simpa only [rootEq, targetIndex, targetEq]
      using selectedBase
  obtain ⟨result, after, array, next, secondRun,
    out, lower, upper, bytes, size⟩ :=
    linkedPacket.dolen_base_leaf_output_bound invariant
      linkedBuffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq targetHere codesGet targetBound
      targetFits targetWidth base.1 base.2.1
      ⟨base.2.2.1, base.2.2.2⟩
      dcodePtr distGet distSafe distMask linkedBitsBound
      (by simpa only [slowLink] using left)
      (by simpa only [slowLink] using avail)
      linkedOut linkedPut begPtr linkedEnd outputGet
      outputWrite linkedSize current beginLe span linkedGuard
  obtain ⟨_, _, _, _, result₂, after₂, _, _, _,
    oldRun, noAgain₂, _, _, _, _, _, _⟩ :=
    linkedPacket.dolen_base_leaf_default_state invariant
      linkedBuffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq targetHere codesGet targetBound
      targetFits targetWidth base.1 base.2.1
      ⟨base.2.2.1, base.2.2.2⟩
      dcodePtr distGet distSafe distMask linkedBitsBound
      (by simpa only [slowLink] using left)
      (by simpa only [slowLink] using avail)
      linkedOut linkedPut begPtr linkedEnd outputGet
      outputWrite linkedSize current beginLe span linkedGuard
  have resultEq : result₂ = result := by
    rw [secondRun] at oldRun
    exact (Prod.mk.inj (Except.ok.inj oldRun)).1.symm
  have noAgain : result.againL = false := by
    rw [resultEq] at noAgain₂
    exact noAgain₂
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  exact ⟨result, after, array, next, loopRun, out,
    lower, by simpa only [slowLink] using upper,
    bytes, size⟩

theorem FastInputPacket.dolen_linked_literal_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
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
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      ((codes.getD (baseOff + rootEntry.val.toNat + slice)
        default).op = 0 →
        ∃ result after array next,
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.out = .ref dest next ∧
          j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
          Space.get after dest = some array ∧
          array.size = output.size) := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨rootWidthBound, _, opWidth,
    subtable, _⟩
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.2.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨linked, slice, firstRun, sliceBound, linkedHere,
    againL, _, linkedOutEq, _, linkedPacket, _,
    linkedBuffers, linkedSource⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits
      rootWidthBound rootLink.1 notBase linkBool opWidth
      subtable
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have linkedOut : linked.out = .ref dest j :=
    linkedOutEq.trans outPtr
  have target := len_table_link_target safe root link
    (by simpa only [rootEq] using sliceBound)
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
      default =
      codes[baseOff +
        (codes[baseOff + rootSlice].val.toNat + slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using linkedHere
  have targetLeaf : LenLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq]
      using target.2.1
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit held rootFits targetLeaf.1
      (by simpa only [slowLink] using linkedSource)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have width := targetLeaf.1
    omega
  have linkedPut : slowLink.put = .ref dest oo := outputPtr
  have linkedEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have linkedSize : oo + slowLink.left.toNat ≤ output.size :=
    outputSize
  have linkedGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut, outPtr] using guard
  refine ⟨linked, slice, firstRun, againL,
    by simpa only [rootEq] using sliceBound,
    by simpa only [rootEq, targetIndex] using linkedHere,
    ?_⟩
  intro literal
  have targetLiteral : codes[targetIndex].op = 0 := by
    simpa only [rootEq, targetIndex, targetEq]
      using literal
  let count : UInt32 := codes[targetIndex].bits.toUInt32
  let slowFinal : IL := { slowLink with
    hold := slowLink.hold >>> count.toUInt64,
    bits := slowLink.bits - count }
  let result : Zlib.Inffast.L := { linked with
    againL := false,
    op := codes[targetIndex].op.toUInt32,
    hold := linked.hold >>> count.toUInt64,
    bits := linked.bits - count,
    out := .ref dest (j + 1) }
  let after := Space.put h dest
    (output.set! j codes[targetIndex].val.toUInt8)
  have second := linkedPacket.dolen_literal_default_state
    invariant linkedBuffers targetHere codesGet targetBound
    targetFits targetWidth targetLiteral
    (by simpa only [slowLink] using left)
    (by simpa only [slowLink] using avail)
    linkedOut linkedPut linkedEnd outputGet outputWrite
    linkedSize current linkedGuard
  have secondRun : C.run (Zlib.Inffast.dolen c linked) h =
      .ok (result, after) := by
    simpa only [result, after, slowFinal, count]
      using second.1
  have secondAgain : result.againL = false := by
    simpa only [result] using second.2.1
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
      .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [secondAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  have upper : j + 1 ≤ oo + slow.left.toNat := by
    let one : Zlib.Inffast.L := { l with len := 1 }
    have oneGuard : C.run (Ptr.lt one.out c.end_) h =
        .ok (true, h) := guard
    have oneRoom := fast_output_room_of_guard
      (l := one) (slow := slow) outPtr endPtr outputGet
      outputSize current avail (by simp [one]) oneGuard
    have room := oneRoom.2.2
    change j + 1 ≤ oo + slow.left.toNat at room
    exact room
  have bytes : Space.get after dest = some
      (output.set! j codes[targetIndex].val.toUInt8) := by
    simpa only [after] using second.2.2.2.2.2.2.2.1
  have arraySize : (output.set! j
      codes[targetIndex].val.toUInt8).size = output.size := by
    simp
  exact ⟨result, after,
    output.set! j codes[targetIndex].val.toUInt8,
    j + 1, loopRun, rfl, by omega, upper,
    bytes, arraySize⟩

theorem FastInputPacket.dolen_linked_end_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (cursorBound : j ≤ oo + slow.left.toNat) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      ((let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
        target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = true) →
        ∃ result after array next,
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.out = .ref dest next ∧
          j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
          Space.get after dest = some array ∧
          array.size = output.size) := by
  obtain ⟨linked, slice, slowLink, firstRun, againL,
    sliceBound, linkedHere, targetLeaf, targetBits,
    linkedPacket, _, linkedBuffers, linkedSource⟩ :=
    packet.dolen_root_link_default_state invariant buffers
      herePtr lcodePtr codesGet safe root link held
  have target := len_table_link_target safe root link sliceBound
  let targetIndex : Nat := baseOff +
    (codes.getD (baseOff + rootSlice) default).val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff +
        ((codes.getD (baseOff + rootSlice) default).val.toNat +
          slice)) default =
      codes[baseOff +
        ((codes.getD (baseOff + rootSlice) default).val.toNat +
          slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using linkedHere
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat := by
    simpa only [targetIndex, targetEq] using targetBits
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have width :
        (codes.getD targetIndex default).bits.toNat +
          (codes.getD (baseOff + rootSlice) default).bits.toNat ≤
          15 := targetLeaf.1
    rw [targetEq] at width
    omega
  refine ⟨linked, slice, firstRun, againL,
    sliceBound, linkedHere, ?_⟩
  intro selected
  have terminal : codes[targetIndex].op ≠ 0 ∧
      (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 32 != 0) = true := by
    simpa only [targetIndex, targetEq] using selected
  obtain ⟨result, slowFinal, secondRun, broke, noAgain,
    _, resultOut, finalPacket, finalState, finalBuffers,
    sizes, source⟩ :=
    linkedPacket.dolen_end_leaf_default_state invariant
      linkedBuffers statePtr mode targetHere codesGet
      targetBound targetFits targetWidth terminal.1
      terminal.2.1 terminal.2.2.1 terminal.2.2.2
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
      .ok (result, setI h zs { s with mode := TYPE }) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result))
          (setI h zs { s with mode := TYPE }) =
          .ok ((false, result),
            setI h zs { s with mode := TYPE }))
  have linkedOut :=
    packet.dolen_root_link_registers invariant buffers
      herePtr lcodePtr codesGet safe root link held firstRun
  have finalOut : result.out = .ref dest j :=
    resultOut.trans (linkedOut.1.trans outPtr)
  have afterGet : Space.get (setI h zs { s with mode := TYPE })
      dest = some output := by
    rw [byte_view_get_setI]
    exact outputGet
  exact ⟨result, setI h zs { s with mode := TYPE },
    output, j, loopRun, finalOut, Nat.le_refl _,
    cursorBound, afterGet, rfl⟩

theorem FastInputPacket.dolen_linked_invalid_output_bound
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    (held : 15 ≤ slow.bits.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (cursorBound : j ≤ oo + slow.left.toNat) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      ((let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
        target.op ≠ 0 ∧
        (target.op.toUInt32 &&& 16 != 0) = false ∧
        (target.op.toUInt32 &&& 64 == 0) = false ∧
        (target.op.toUInt32 &&& 32 != 0) = false) →
        ∃ result after array next,
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.out = .ref dest next ∧
          j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
          Space.get after dest = some array ∧
          array.size = output.size) := by
  obtain ⟨linked, slice, slowLink, firstRun, againL,
    sliceBound, linkedHere, targetLeaf, targetBits,
    linkedPacket, _, linkedBuffers, linkedSource⟩ :=
    packet.dolen_root_link_default_state invariant buffers
      herePtr lcodePtr codesGet safe root link held
  have target := len_table_link_target safe root link sliceBound
  let targetIndex : Nat := baseOff +
    (codes.getD (baseOff + rootSlice) default).val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff +
        ((codes.getD (baseOff + rootSlice) default).val.toNat +
          slice)) default =
      codes[baseOff +
        ((codes.getD (baseOff + rootSlice) default).val.toNat +
          slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using linkedHere
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat := by
    simpa only [targetIndex, targetEq] using targetBits
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have width :
        (codes.getD targetIndex default).bits.toNat +
          (codes.getD (baseOff + rootSlice) default).bits.toNat ≤
          15 := targetLeaf.1
    rw [targetEq] at width
    omega
  refine ⟨linked, slice, firstRun, againL,
    sliceBound, linkedHere, ?_⟩
  intro selected
  have invalid : codes[targetIndex].op ≠ 0 ∧
      (codes[targetIndex].op.toUInt32 &&& 16 != 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 64 == 0) = false ∧
      (codes[targetIndex].op.toUInt32 &&& 32 != 0) = false := by
    simpa only [targetIndex, targetEq] using selected
  obtain ⟨i, after, result, slowFinal, secondRun,
    heapEq, broke, noAgain, _, resultOut, finalPacket,
    finalState, finalBuffers, sizes, source⟩ :=
    linkedPacket.dolen_invalid_leaf_default_state
      invariant linkedBuffers streamPtr statePtr
      targetHere codesGet targetBound targetFits targetWidth
      invalid.1 invalid.2.1 invalid.2.2.1
      invalid.2.2.2
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
      .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  have linkedOut :=
    packet.dolen_root_link_registers invariant buffers
      herePtr lcodePtr codesGet safe root link held firstRun
  have finalOut : result.out = .ref dest j :=
    resultOut.trans (linkedOut.1.trans outPtr)
  have afterGet : Space.get after dest = some output := by
    rw [heapEq]
    dsimp [badHeap]
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact outputGet
  exact ⟨result, after, output, j, loopRun,
    finalOut, Nat.le_refl _, cursorBound,
    afterGet, rfl⟩

theorem FastInputPacket.dolen_link_complete_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨linked, slice, slowLink, firstRun, _,
    sliceBound, here, leaf, _, _, _, _, _⟩ :=
    packet.dolen_root_link_default_state invariant buffers
      herePtr lcodePtr codesGet safe root link held
  obtain ⟨_, targetLeaf, classes⟩ :=
    len_table_link_source_cases safe root link sliceBound
  let rootEntry : Code :=
    codes.getD (baseOff + rootSlice) default
  let target : Code := codes.getD
    (baseOff + rootEntry.val.toNat + slice) default
  have total : rootEntry.bits.toNat + target.bits.toNat ≤ 15 := by
    have bound : target.bits.toNat + rootEntry.bits.toNat ≤ 15 :=
      targetLeaf.1
    omega
  have cursorBound : j ≤ oo + slow.left.toNat := by
    let one : Zlib.Inffast.L := { l with len := 1 }
    have oneGuard : C.run (Ptr.lt one.out c.end_) h =
        .ok (true, h) := guard
    have oneRoom := fast_output_room_of_guard
      (l := one) (slow := slow) outPtr endPtr outputGet
      outputSize current avail (by simp [one]) oneGuard
    have room := oneRoom.2.2
    change j + 1 ≤ oo + slow.left.toNat at room
    omega
  rcases classes with literal | base | terminal | invalid
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_literal_output_bound invariant
        buffers herePtr lcodePtr codesGet safe root link held
        left avail outPtr outputPtr endPtr outputGet
        outputWrite outputSize current guard
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
          default).op = 0 := by
      simpa only [unique.2] using literal
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_base_output_bound invariant
        buffers streamPtr statePtr whaveEq wsizeEq
        wnextEq windowEq herePtr lcodePtr codesGet
        safe root link dcodePtr distGet distSafe distMask
        held bitsBound left avail outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op &&& 16 ≠ 0 ∧
          (target₂.op &&& 15).toNat ≤ 5 ∧
          3 ≤ target₂.val.toNat ∧
          target₂.val.toNat +
            2 ^ (target₂.op &&& 15).toNat ≤ 259 := by
      simpa only [unique.2] using base
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_end_output_bound invariant
        buffers statePtr mode herePtr lcodePtr codesGet
        safe root link held outPtr outputGet cursorBound
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op ≠ 0 ∧
          (target₂.op.toUInt32 &&& 16 != 0) = false ∧
          (target₂.op.toUInt32 &&& 64 == 0) = false ∧
          (target₂.op.toUInt32 &&& 32 != 0) = true := by
      simpa only [unique.2] using terminal
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_invalid_output_bound invariant
        buffers streamPtr statePtr herePtr lcodePtr
        codesGet safe root link held outPtr outputGet cursorBound
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op ≠ 0 ∧
          (target₂.op.toUInt32 &&& 16 != 0) = false ∧
          (target₂.op.toUInt32 &&& 64 == 0) = false ∧
          (target₂.op.toUInt32 &&& 32 != 0) = false := by
      simpa only [unique.2] using invalid
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩

theorem FastInputPacket.dolen_root_complete_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth fifth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨indexBound, classes⟩ :=
    len_table_root_source_cases safe root
  rcases classes with ⟨link, _⟩ | ⟨notLink, width, classes⟩
  · exact packet.dolen_link_complete_output_bound
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq herePtr lcodePtr codesGet
      safe root link dcodePtr distGet distSafe distMask
      held bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  · exact packet.dolen_root_nonlink_output_bound
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq herePtr lcodePtr codesGet
      safe root notLink dcodePtr distGet distSafe distMask
      held bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard

theorem FastInputPacket.fast_body_no_pull_output_bound
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
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 15 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe lenMask
  obtain ⟨result, after, array, next, loopRun,
    out, lower, upper, bytes, size⟩ :=
    selectedPacket.dolen_root_complete_output_bound
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq rfl lcodePtr codesGet
      safe root dcodePtr distGet distSafe distMask held
      bitsBound left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have noPull : ¬ l.bits < 15 := by
    intro less
    have below : slow.bits.toNat < 15 := by
      rw [← packet.bits]
      simpa using UInt32.lt_iff_toNat_lt.mp less
    omega
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.inflate_fast_body
    simp only [noPull, ite_false]
    change (Ptr.add c.lcode rootSlice >>= fun here =>
      cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current))
        { l with here }) h = .ok (result, after)
    change Ptr.add c.lcode rootSlice h =
      .ok (.ref codeRef (baseOff + rootSlice), h) at addRun
    rw [bind_ok addRun]
    exact loopRun
  exact ⟨result, after, array, next, bodyRun,
    out, lower, upper, bytes, size⟩

theorem FastInputPacket.dodistBase_one_byte_output_bound
    {h : Heap} {slow : IL} {first : UInt8} {rest : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (held : 5 ≤ slow.bits.toNat)
    (extraBound : l.op.toNat ≤ 13)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases needsFirst : l.bits < l.op
  · have small : slow.bits.toNat ≤ 22 := by
      have less := UInt32.lt_iff_toNat_lt.mp needsFirst
      rw [packet.bits] at less
      omega
    obtain ⟨next1, fast1, slow1, pull1, _,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small
    have op1 : fast1.op = l.op := by rw [fast1Eq]; rfl
    have len1 : fast1.len = l.len := by rw [fast1Eq]; rfl
    have out1 : fast1.out = .ref dest j := by
      rw [fast1Eq]
      exact outPtr
    have put1 : slow1.put = .ref dest oo := by
      rw [slow1Eq]
      exact outputPtr
    have end1 : c.end_ = .ref dest
        (oo + slow1.left.toNat - 257) := by
      simpa only [slow1Eq, pulled] using endPtr
    have left1 : slow1.left ≠ 0 := by
      simpa only [slow1Eq, pulled] using left
    have avail1 : 258 ≤ slow1.left.toNat := by
      simpa only [slow1Eq, pulled] using avail
    have size1 : oo + slow1.left.toNat ≤ output.size := by
      simpa only [slow1Eq, pulled] using outputSize
    have guard1 : C.run (Ptr.lt fast1.out c.end_) h =
        .ok (true, h) := by
      simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL] using guard
    have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
      rw [slow1Eq]
      exact u32_add8 slow.bits (by omega)
    have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
      rw [op1, bits1]
      omega
    have noSecond : ¬ fast1.bits < fast1.op := by
      intro hlt
      have less := UInt32.lt_iff_toNat_lt.mp hlt
      rw [packet1.bits, op1, bits1] at less
      omega
    obtain ⟨result, after, array, next, contRun,
      out, lower, upper, bytes, size⟩ :=
      packet1.distCont_output_bound invariant buffers1 streamPtr
        statePtr whaveEq wsizeEq wnextEq windowEq fits1
        (by rw [op1]; omega) left1 avail1
        (by rw [len1]; exact length) out1 put1 begPtr end1
        outputGet outputWrite size1 current beginLe span guard1
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after)
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_true]
      rw [bind_ok (by simpa only [C.run] using pull1)]
      simp only [noSecond, ite_false]
      exact contRun
    exact ⟨result, after, array, next, run, out,
      lower, by simpa only [slow1Eq, pulled] using upper,
      bytes, size⟩
  · have fits0 : l.op.toNat ≤ slow.bits.toNat := by
      have notLess : ¬ slow.bits.toNat < l.op.toNat := by
        intro hlt
        exact needsFirst (UInt32.lt_iff_toNat_lt.mpr
          (by rw [packet.bits]; exact hlt))
      omega
    obtain ⟨result, after, array, next, contRun,
      out, lower, upper, bytes, size⟩ :=
      packet.distCont_output_bound invariant buffers streamPtr
        statePtr whaveEq wsizeEq wnextEq windowEq fits0
        (by omega) left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current beginLe
        span guard
    have run : C.run (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after) := by
      change (Zlib.Inffast.Proofs.dodistBase c l) h =
        .ok (result, after)
      unfold Zlib.Inffast.Proofs.dodistBase
      simp only [needsFirst, ite_false]
      exact contRun
    exact ⟨result, after, array, next, run,
      out, lower, upper, bytes, size⟩

theorem FastInputPacket.dodist_base_leaf_one_byte_output_bound
    {h : Heap} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code} {index : Nat}
    (herePtr : l.here = .ref codeRef index)
    (codesGet : Space.get h codeRef = some codes)
    (codeIndex : index < codes.size)
    (codeBits : codes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : codes[index].bits.toNat ≤ 15)
    (held : 5 + codes[index].bits.toNat ≤ slow.bits.toNat)
    (base : (codes[index].op.toUInt32 &&& 16 != 0) = true)
    (extraBound : (codes[index].op.toUInt32 &&& 15).toNat ≤ 13)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.dodist c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let entry : Code := codes[index]
  have load : C.run (Ptr.load l.here) h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet codeIndex
  let count : UInt32 := entry.bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againD := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: rest) firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeBits
  have countSmall : count.toNat < 64 := by
    have width : count.toNat ≤ 15 := by
      simpa only [count, entry, Zlib.Inffast.Proofs.toNat32] using codeWidth
    omega
  have dropped := firstPacket.drop_bits_default_state buffers
    count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: rest) afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: rest) := dropped.2.1
  have codeHeld : 5 ≤ slowCode.bits.toNat := by
    have bitsAfter : slowCode.bits.toNat =
        slow.bits.toNat - count.toNat := dropped.2.2.2
    have codeSmall : count.toNat = codes[index].bits.toNat := by
      rfl
    omega
  have codeStream : stream slowCode (first :: rest) =
      (stream slow (first :: rest)).drop
        entry.bits.toNat := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32] using dropped.2.2.1
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    dist := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: rest) baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeLeft : slowCode.left ≠ 0 := left
  have codeAvail : 258 ≤ slowCode.left.toNat := avail
  have codeSize : oo + slowCode.left.toNat ≤ output.size := outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  have baseExtra : baseLocal.op.toNat ≤ 13 := extraBound
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat ≤ 258 := length
  have baseEntry : (entry.op.toUInt32 &&& 16 != 0) = true := by
    simpa only [entry] using base
  obtain ⟨result, after, array, next, baseRun,
    out, lower, upper, bytes, size⟩ :=
    basePacket.dodistBase_one_byte_output_bound invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      codeHeld baseExtra codeLeft codeAvail baseLength baseOut codePut
      begPtr codeEnd outputGet outputWrite codeSize current
      beginLe span baseGuard
  have shiftRun : C.run
      (Zlib.Inffast.shr64 l.hold count.toUInt64) h =
        .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have run : C.run (Zlib.Inffast.dodist c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.dodist c l) h = .ok (result, after)
    rw [Zlib.Inffast.Proofs.dodist_eq_base]
    change Ptr.load l.here h = .ok (entry, h) at load
    change Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) at shiftRun
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [baseEntry, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode, firstLocal,
      count, entry] using baseRun
  exact ⟨result, after, array, next, run, out,
    lower, upper, bytes, size⟩

theorem FastInputPacket.dodist_linked_leaf_one_byte_output_bound
    {h : Heap} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : DistLink (codes.getD (baseOff + rootSlice) default))
    (held : 20 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ linked result after array next,
      C.run (Zlib.Inffast.dodist c l) h = .ok (linked, h) ∧
      C.run (Zlib.Inffast.dodist c linked) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : DistLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨rootWidthBound, _, opWidth,
    subtable, _⟩
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨linked, slice, firstRun, sliceBound, here,
    againD, _, linkedOut, linkedLen, linkedPacket, _,
    linkedBuffers, source⟩ :=
    packet.dodist_link_default_state_exact invariant buffers
      herePtr dcodePtr codesGet rootBound rootFits
      rootWidthBound notBase linkBool opWidth
      subtable
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have target := dist_table_link_target safe root link
    (by simpa only [rootEq] using sliceBound)
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
      default =
      codes[baseOff +
        (codes[baseOff + rootSlice].val.toNat + slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetLeaf : DistLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq] using target.2.1
  have targetBits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit (by omega) rootFits targetLeaf.1
      (by simpa only [slowLink] using source)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    omega
  have targetHeld : 5 + codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat := by
    have rootWidthNat :
        codes[baseOff + rootSlice].bits.toUInt32.toNat =
          codes[baseOff + rootSlice].bits.toNat := by
      rfl
    have slowLinkBits : slowLink.bits.toNat =
        slow.bits.toNat - codes[baseOff + rootSlice].bits.toNat := by
      simp only [slowLink]
      rw [UInt32.toNat_sub_of_le _ _
        (UInt32.le_iff_toNat_le.mpr (by
          rw [rootWidthNat]
          exact rootFits))]
      rw [rootWidthNat]
    have total := targetLeaf.1
    omega
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using here
  have targetOut : linked.out = .ref dest j := linkedOut.trans outPtr
  have targetLen : 3 ≤ linked.len.toNat ∧
      linked.len.toNat ≤ 258 := by
    simpa only [linkedLen] using length
  have targetGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut] using guard
  have cursorBound : j ≤ oo + slow.left.toNat := by
    have room := fast_output_room_of_guard outPtr endPtr
      outputGet outputSize current avail length.2 guard
    omega
  rcases targetLeaf.2 with baseClass | invalidClass
  · have baseBool :
        (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
          true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [baseClass.1]
    have extraBound :
        (codes[targetIndex].op.toUInt32 &&& 15).toNat ≤
          13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      exact baseClass.2.1
    obtain ⟨result, after, array, next, secondRun,
      out, lower, upper, bytes, size⟩ :=
      linkedPacket.dodist_base_leaf_one_byte_output_bound invariant
        linkedBuffers streamPtr statePtr whaveEq wsizeEq
        wnextEq windowEq targetHere codesGet targetBound
        targetBits targetWidth targetHeld baseBool extraBound
        (by simpa only [slowLink] using left)
        (by simpa only [slowLink] using avail)
        targetLen targetOut
        (by simpa only [slowLink] using outputPtr)
        begPtr (by simpa only [slowLink] using endPtr)
        outputGet outputWrite
        (by simpa only [slowLink] using outputSize)
        current beginLe span targetGuard
    exact ⟨linked, result, after, array, next,
      firstRun, secondRun, out, lower,
      by simpa only [slowLink] using upper,
      bytes, size⟩
  · have notBaseLeaf :
        (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [invalidClass.1]
    have notLinkLeaf :
        (codes[targetIndex].op.toUInt32 &&& 64 == 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [invalidClass.2]
    obtain ⟨i, after, result, slowNext, secondRun, heapEq,
      broke, noAgain, _, out, finalPacket, finalState,
      finalBuffers, sizes, secondSource⟩ :=
      linkedPacket.dodist_invalid_leaf_default_state
        invariant linkedBuffers streamPtr statePtr targetHere
        codesGet targetBound targetBits targetWidth
        notBaseLeaf notLinkLeaf
    obtain ⟨array, bytes, size⟩ := sizes.view outputGet
    exact ⟨linked, result, after, array, j,
      firstRun, secondRun, out.trans targetOut,
      Nat.le_refl _, cursorBound, bytes, size⟩

theorem FastInputPacket.dodist_loop_one_byte_output_bound
    {h : Heap} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (held : 20 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dodist c)
        (fun q => pure (q.againD, q)) l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  have rootCases := dist_table_root_cases safe root
  dsimp only at rootCases
  obtain ⟨rootBound, rootWidthBound, classes⟩ := rootCases
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  rw [rootEq] at rootWidthBound classes
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have rootLoad : Ptr.load l.here h =
      .ok (codes[baseOff + rootSlice], h) := by
    rw [herePtr]
    exact Ptr.load_ok codesGet rootBound
  rcases classes with baseClass | linkClass | invalidClass
  · have baseBool :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          true := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [baseClass.1]
    have extras :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 15).toNat ≤
          13 := by
      rw [Zlib.Inffast.Proofs.mask15]
      exact baseClass.2.1
    obtain ⟨result, after, array, next, run, out,
      lower, upper, bytes, size⟩ :=
      packet.dodist_base_leaf_one_byte_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        herePtr codesGet rootBound rootFits rootWidthBound
        (by omega : 5 + codes[baseOff + rootSlice].bits.toNat ≤
          slow.bits.toNat) baseBool extras left avail length outPtr outputPtr
        begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    have noAgain := Zlib.Inffast.Proofs.dodist_base_againD_false
      rootLoad rootWidthBound baseBool run
    have cond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L))) run cond
    exact ⟨result, after, array, next, loop, out,
      lower, upper, bytes, size⟩
  · have rootLink : DistLink
        (codes.getD (baseOff + rootSlice) default) := by
      rw [rootEq]
      exact ⟨linkClass.1, linkClass.2.1⟩
    obtain ⟨linked, slice, firstRun, againD,
      sliceBound, here, leaf, used, slowNext,
      result, after, usedBound, secondRun,
      finalPacket, finalBuffers, sizes, outcome⟩ :=
      packet.dodist_linked_leaf_one_byte_default_state invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    let targetIndex : Nat := baseOff +
      codes[baseOff + rootSlice].val.toNat + slice
    have targetBound : targetIndex < codes.size := by
      have bound := linkClass.2.2.2.2
      have sliceLimit : slice <
          2 ^ codes[baseOff + rootSlice].op.toNat := by
        simpa only [rootEq] using sliceBound
      omega
    have targetEq : codes.getD targetIndex default =
        codes[targetIndex] := by
      simp [Array.getD_eq_getD_getElem?, targetBound]
    have targetEqNorm : codes.getD
        (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
        default =
        codes[baseOff +
          (codes[baseOff + rootSlice].val.toNat + slice)] := by
      simpa only [targetIndex, Nat.add_assoc] using targetEq
    have targetLeaf : DistLeaf
        codes[baseOff + rootSlice].bits.toNat
        codes[targetIndex] := by
      simpa only [rootEq, targetIndex, targetEq] using leaf
    have targetHere : linked.here = .ref codeRef targetIndex := by
      simpa only [rootEq, targetIndex] using here
    have targetLoad : Ptr.load linked.here h =
        .ok (codes[targetIndex], h) := by
      rw [targetHere]
      exact Ptr.load_ok codesGet targetBound
    have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
      omega
    have noAgain : result.againD = false := by
      rcases targetLeaf.2 with base | invalid
      · have baseBool :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
              true := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [base.1]
        exact Zlib.Inffast.Proofs.dodist_base_againD_false
          targetLoad targetWidth baseBool secondRun
      · have notBase :
            (codes[targetIndex].op.toUInt32 &&& 16 != 0) =
              false := by
          rw [Zlib.Inffast.Proofs.mask16]
          simp [invalid.1]
        have notLink :
            (codes[targetIndex].op.toUInt32 &&& 64 == 0) =
              false := by
          rw [Zlib.Inffast.Proofs.mask64]
          simp [invalid.2]
        exact Zlib.Inffast.Proofs.dodist_invalid_againD_false
          targetLoad targetWidth notBase notLink secondRun
    have condFirst :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          linked h = .ok ((true, linked), h) := by
      simp [againD]
    have condSecond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_two
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L)))
      firstRun condFirst secondRun condSecond
    obtain ⟨linked2, result2, after2, array, next,
      firstRun2, secondRun2, out, lower, upper,
      bytes, size⟩ :=
      packet.dodist_linked_leaf_one_byte_output_bound invariant
        buffers streamPtr statePtr whaveEq wsizeEq wnextEq
        windowEq herePtr dcodePtr codesGet safe root rootLink
        held left avail length outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    have sameFirst : (linked, h) = (linked2, h) :=
      Except.ok.inj (firstRun.symm.trans firstRun2)
    have linkedEq : linked = linked2 :=
      congrArg Prod.fst sameFirst
    subst linked2
    have sameSecond : (result, after) =
        (result2, after2) :=
      Except.ok.inj (secondRun.symm.trans secondRun2)
    cases sameSecond
    exact ⟨result, after, array, next, loop, out,
      lower, upper, bytes, size⟩
  · have notBase :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask16]
      simp [invalidClass.1]
    have notLink :
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
          false := by
      rw [Zlib.Inffast.Proofs.mask64]
      simp [invalidClass.2]
    obtain ⟨i, after, result, slowNext, run, heapEq,
      broke, noAgain, _, out, finalPacket, finalState,
      finalBuffers, sizes, source⟩ :=
      packet.dodist_invalid_leaf_default_state invariant
        buffers streamPtr statePtr herePtr codesGet
        rootBound rootFits rootWidthBound notBase notLink
    have cond :
        (fun q : Zlib.Inffast.L =>
          (pure (q.againD, q) : M (Bool × Zlib.Inffast.L)))
          result after = .ok ((false, result), after) := by
      simp [noAgain]
    have loop := Zlib.Inffast.Proofs.cdoWhile_one
      (body := Zlib.Inffast.dodist c)
      (cond := fun q => (pure (q.againD, q) :
        M (Bool × Zlib.Inffast.L))) run cond
    obtain ⟨afterArray, afterGet, afterSize⟩ :=
      sizes.view outputGet
    have cursorBound : j ≤ oo + slow.left.toNat := by
      have geometry := fast_output_room_of_guard outPtr endPtr
        outputGet outputSize current avail length.2 guard
      omega
    exact ⟨result, after, afterArray, j, loop,
      out.trans outPtr, Nat.le_refl _, cursorBound,
      afterGet, afterSize⟩

theorem FastInputPacket.dolenDist_one_byte_output_bound
    {h : Heap} {slow : IL} {first : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (held : 20 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenDist c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let idx : Nat := (l.hold &&& c.dmask.toUInt64).toNat
  have idxEq : idx = l.hold.toNat % 2 ^ rootWidth := by
    exact Zlib.Inffast.Proofs.u64_and_mask mask
  have idxBound : idx < 2 ^ rootWidth := by
    rw [idxEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.dcode idx) h =
      .ok (.ref codeRef (baseOff + idx), h) := by
    rw [dcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + idx) }
  have selectedPacket : FastInputPacket h slow
      (first :: rest) selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, after, array, next, loopRun, out, lower, upper, bytes, size⟩ :=
    selectedPacket.dodist_loop_one_byte_output_bound invariant
      buffers streamPtr statePtr whaveEq wsizeEq wnextEq
      windowEq (by rfl) dcodePtr codesGet safe idxBound
      held left avail length outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have run : C.run (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenDist
    change Ptr.add c.dcode idx h =
      .ok (.ref codeRef (baseOff + idx), h) at addRun
    rw [bind_ok addRun]
    simpa [C.run, selected] using loopRun
  exact ⟨result, after, array, next, run, out,
    lower, upper, bytes, size⟩

theorem FastInputPacket.dolenRefill_three_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (held : 4 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases needsPull : l.bits < 15
  · have small0 : slow.bits.toNat ≤ 22 := by
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next1, fast1, slow1, pull1, _,
      slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
      packet.pull_default_state invariant buffers small0
    have small1 : slow1.bits.toNat ≤ 22 := by
      rw [slow1Eq]
      change (slow.bits + 8).toNat ≤ 22
      rw [u32_add8 slow.bits (by omega)]
      have bitsSmall : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp needsPull
      omega
    obtain ⟨next2, fast2, slow2, pull2, _,
      slow2Eq, fast2Eq, packet2, _, buffers2, stream2⟩ :=
      packet1.pull_default_state invariant buffers1 small1
    have held2 : 20 ≤ slow2.bits.toNat := by
      rw [slow2Eq, slow1Eq]
      change ((slow.bits + 8) + 8).toNat ≥ 20
      rw [u32_add8 (slow.bits + 8) (by
          have bound : (slow.bits + 8).toNat ≤ 22 := by
            simpa only [slow1Eq, pulled] using small1
          omega),
        u32_add8 slow.bits (by omega)]
      omega
    have left2 : slow2.left ≠ 0 := by
      simpa only [slow2Eq, slow1Eq, pulled] using left
    have avail2 : 258 ≤ slow2.left.toNat := by
      simpa only [slow2Eq, slow1Eq, pulled] using avail
    have length2 : 3 ≤ fast2.len.toNat ∧
        fast2.len.toNat ≤ 258 := by
      simpa only [fast2Eq, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using length
    have out2 : fast2.out = .ref dest j := by
      simpa only [fast2Eq, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using outPtr
    have put2 : slow2.put = .ref dest oo := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputPtr
    have end2 : c.end_ = .ref dest
        (oo + slow2.left.toNat - 257) := by
      simpa only [slow2Eq, slow1Eq, pulled] using endPtr
    have size2 : oo + slow2.left.toNat ≤ output.size := by
      simpa only [slow2Eq, slow1Eq, pulled] using outputSize
    have guard2 : C.run (Ptr.lt fast2.out c.end_) h =
        .ok (true, h) := by
      simpa only [fast2Eq, fast1Eq,
        Zlib.Inffast.Proofs.pullL] using guard
    obtain ⟨result, after, array, next, distRun,
      out, lower, upper, bytes, size⟩ :=
      packet2.dolenDist_one_byte_output_bound invariant buffers2
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask held2 left2 avail2
        length2 out2 put2 begPtr end2 outputGet outputWrite
        size2 current beginLe span guard2
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_true]
      change (Zlib.Inffast.pull l >>= fun q =>
        Zlib.Inffast.pull q >>= fun q' =>
        Zlib.Inffast.Proofs.dolenDist c q') h =
          .ok (result, after)
      change (Zlib.Inffast.pull l) h =
        .ok (fast1, h) at pull1
      change (Zlib.Inffast.pull fast1) h =
        .ok (fast2, h) at pull2
      change (Zlib.Inffast.Proofs.dolenDist c fast2) h =
        .ok (result, after) at distRun
      simp only [bind_app, pull1, pull2, distRun]
    exact ⟨result, after, array, next, run, out,
      lower, by simpa only [slow2Eq, slow1Eq, pulled] using upper,
      bytes, size⟩
  · have held : 15 ≤ slow.bits.toNat := by
      have h : ¬ l.bits.toNat < 15 := by
        intro less
        exact needsPull (UInt32.lt_iff_toNat_lt.mpr less)
      rw [packet.bits] at h
      omega
    obtain ⟨result, after, array, next, distRun,
      out, lower, upper, bytes, size⟩ :=
      packet.dolenDist_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask held left avail length
        outPtr outputPtr begPtr endPtr outputGet outputWrite
        outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenRefill c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenRefill
      simp only [needsPull, ite_false]
      exact distRun
    exact ⟨result, after, array, next, run,
      out, lower, upper, bytes, size⟩

theorem FastInputPacket.dolenExt_three_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (extraFits : l.op.toNat ≤ slow.bits.toNat)
    (held : 4 + l.op.toNat ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenExt c l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let extra : Nat := l.hold.toNat % 2 ^ l.op.toNat
  have opSmall : l.op.toNat < 32 := by omega
  have low := Zlib.Inffast.Proofs.hold_low32
    (x := l.hold) (k := l.op) opSmall
  have extraBound : extra < 2 ^ l.op.toNat := by
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have lenSum : l.len.toNat + extra ≤ 258 := by omega
  let delta : UInt32 := l.hold.toUInt32 &&&
    (((1 : UInt32) <<< l.op) - 1)
  have deltaEq : delta.toNat = extra := by
    simpa only [delta, extra] using low
  have lenValue : (l.len + delta).toNat =
      l.len.toNat + extra := by
    rw [Zlib.Inffast.Proofs.u32_toNat_add
      (by rw [deltaEq]; omega), deltaEq]
  have shlRun : Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok opSmall
  have shrRun : Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  let afterLen : Zlib.Inffast.L := { l with len := l.len + delta }
  have afterLenPacket : FastInputPacket h slow
      (first :: second :: third :: rest) afterLen :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have within : l.op.toNat ≤ slow.bits.toNat := extraFits
  have dropped := afterLenPacket.drop_bits_default_state buffers
    l.op within (by omega)
  let slowDrop : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let fastDrop : Zlib.Inffast.L := { afterLen with
    hold := afterLen.hold >>> l.op.toUInt64,
    bits := afterLen.bits - l.op }
  have dropPacket : FastInputPacket h slowDrop
      (first :: second :: third :: rest) fastDrop :=
    dropped.1
  have dropBuffers : DispatchBuffers h r slowDrop
      (first :: second :: third :: rest) :=
    dropped.2.1
  have dropStream : stream slowDrop
      (first :: second :: third :: rest) =
      (stream slow
        (first :: second :: third :: rest)).drop
          l.op.toNat := dropped.2.2.1
  have dropBits : slowDrop.bits.toNat =
      slow.bits.toNat - l.op.toNat := dropped.2.2.2
  have dropBound : slowDrop.bits.toNat ≤ 30 := by omega
  have dropHeld : 4 ≤ slowDrop.bits.toNat := by omega
  have dropLength : 3 ≤ fastDrop.len.toNat ∧
      fastDrop.len.toNat ≤ 258 := by
    simpa only [fastDrop, afterLen, lenValue] using
      (show 3 ≤ l.len.toNat + extra ∧
        l.len.toNat + extra ≤ 258 by omega)
  have dropOut : fastDrop.out = .ref dest j := outPtr
  have dropPut : slowDrop.put = .ref dest oo := outputPtr
  have dropEnd : c.end_ = .ref dest
      (oo + slowDrop.left.toNat - 257) := endPtr
  have dropSize : oo + slowDrop.left.toNat ≤ output.size :=
    outputSize
  have dropGuard : C.run (Ptr.lt fastDrop.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨result, after, array, next, refillRun,
    out, lower, upper, bytes, size⟩ :=
    dropPacket.dolenRefill_three_byte_output_bound invariant dropBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask dropBound dropHeld left avail
      dropLength dropOut dropPut begPtr dropEnd outputGet
      outputWrite dropSize current beginLe span dropGuard
  have run : C.run (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenExt
    rw [bind_ok shlRun]
    rw [bind_ok shrRun]
    simpa only [fastDrop, afterLen, delta, C.run] using refillRun
  exact ⟨result, after, array, next, run,
    out, lower, upper, bytes, size⟩

theorem FastInputPacket.dolenLen_four_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (bitsBound : slow.bits.toNat ≤ 30)
    (held : 1 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases hasExtra : l.op != 0
  · by_cases needsPull : l.bits < l.op
    · have small : slow.bits.toNat ≤ 22 := by
        have less := UInt32.lt_iff_toNat_lt.mp needsPull
        rw [packet.bits] at less
        omega
      obtain ⟨next1, fast1, slow1, pullRun, _,
        slow1Eq, fast1Eq, packet1, _, buffers1, stream1⟩ :=
        packet.pull_default_state invariant buffers small
      have opEq : fast1.op = l.op := by
        rw [fast1Eq]
        rfl
      have fits1 : fast1.op.toNat ≤ slow1.bits.toNat := by
        rw [opEq, slow1Eq]
        change l.op.toNat ≤ (slow.bits + 8).toNat
        rw [u32_add8 slow.bits (by omega)]
        omega
      have bound1 : slow1.bits.toNat ≤ 30 := by
        rw [slow1Eq]
        change (slow.bits + 8).toNat ≤ 30
        rw [u32_add8 slow.bits (by omega)]
        omega
      have held1 : 4 + fast1.op.toNat ≤ slow1.bits.toNat := by
        rw [opEq, slow1Eq]
        change 4 + l.op.toNat ≤ (slow.bits + 8).toNat
        rw [u32_add8 slow.bits (by omega)]
        omega
      have width1 : fast1.op.toNat ≤ 5 := by
        rw [opEq]
        exact extraWidth
      have length1 : 3 ≤ fast1.len.toNat ∧
          fast1.len.toNat + 2 ^ fast1.op.toNat ≤ 259 := by
        simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
          using length
      have out1 : fast1.out = .ref dest j := by
        simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
          using outPtr
      have put1 : slow1.put = .ref dest oo := by
        simpa only [slow1Eq, pulled] using outputPtr
      have end1 : c.end_ = .ref dest
          (oo + slow1.left.toNat - 257) := by
        simpa only [slow1Eq, pulled] using endPtr
      have size1 : oo + slow1.left.toNat ≤ output.size := by
        simpa only [slow1Eq, pulled] using outputSize
      have guard1 : C.run (Ptr.lt fast1.out c.end_) h =
          .ok (true, h) := by
        simpa only [fast1Eq, Zlib.Inffast.Proofs.pullL]
          using guard
      obtain ⟨result, after, array, next, extRun,
        out, lower, upper, bytes, size⟩ :=
        packet1.dolenExt_three_byte_output_bound invariant buffers1
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask width1 fits1 held1 bound1
          (by simpa only [slow1Eq, pulled] using left)
          (by simpa only [slow1Eq, pulled] using avail)
          length1 out1 put1 begPtr end1 outputGet outputWrite
          size1 current beginLe span guard1
      have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after) := by
        change (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after)
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, needsPull, ite_true]
        change (Zlib.Inffast.pull l >>= fun q =>
          Zlib.Inffast.Proofs.dolenExt c q) h =
            .ok (result, after)
        change (Zlib.Inffast.pull l) h =
          .ok (fast1, h) at pullRun
        change (Zlib.Inffast.Proofs.dolenExt c fast1) h =
          .ok (result, after) at extRun
        simp only [bind_app, pullRun, extRun]
      exact ⟨result, after, array, next, run, out,
        lower, by simpa only [slow1Eq, pulled] using upper,
        bytes, size⟩
    · have fits : l.op.toNat ≤ slow.bits.toNat := by
        have noLess : ¬ l.op.toNat > l.bits.toNat := by
          intro h
          exact needsPull (UInt32.lt_iff_toNat_lt.mpr h)
        rw [packet.bits] at noLess
        omega
      obtain ⟨result, after, array, next, extRun,
        out, lower, upper, bytes, size⟩ :=
        packet.dolenExt_output_bound invariant buffers
          streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
          dcodePtr codesGet safe mask extraWidth fits bitsBound
          left avail length outPtr outputPtr begPtr endPtr
          outputGet outputWrite outputSize current beginLe
          span guard
      have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
          .ok (result, after) := by
        unfold Zlib.Inffast.Proofs.dolenLen
        simp only [hasExtra, needsPull, ite_true, ite_false]
        exact extRun
      exact ⟨result, after, array, next, run,
        out, lower, upper, bytes, size⟩
  · have opZero : l.op = 0 := by
      simpa using hasExtra
    have length0 : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258 := by
      rw [opZero] at length
      simp only [UInt32.toNat_zero, Nat.pow_zero] at length
      omega
    obtain ⟨result, after, array, next, refillRun,
      out, lower, upper, bytes, size⟩ :=
      packet.dolenRefill_output_bound invariant buffers
        streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
        dcodePtr codesGet safe mask bitsBound left avail
        length0 outPtr outputPtr begPtr endPtr outputGet
        outputWrite outputSize current beginLe span guard
    have run : C.run (Zlib.Inffast.Proofs.dolenLen c l) h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.dolenLen
      simp only [hasExtra, ite_false]
      exact refillRun
    exact ⟨result, after, array, next, run,
      out, lower, upper, bytes, size⟩

theorem FastInputPacket.dolen_base_leaf_four_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (held : 1 + lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.dolen c l) h = .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  let entry : Code := lenCodes[index]
  have load : Ptr.load l.here h = .ok (entry, h) := by
    rw [herePtr]
    exact Ptr.load_ok lenGet indexBound
  let count : UInt32 := entry.bits.toUInt32
  have countFits : count.toNat ≤ slow.bits.toNat := by
    simpa only [count, entry, Zlib.Inffast.Proofs.toNat32]
      using codeFits
  have countSmall : count.toNat < 64 := by
    have countNat : count.toNat =
        lenCodes[index].bits.toNat := rfl
    omega
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := count }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest)
      firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := firstPacket.drop_bits_default_state
    buffers count countFits countSmall
  let slowCode : IL := { slow with
    hold := slow.hold >>> count.toUInt64,
    bits := slow.bits - count }
  let afterCode : Zlib.Inffast.L := { firstLocal with
    hold := firstLocal.hold >>> count.toUInt64,
    bits := firstLocal.bits - count }
  have codePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: rest)
      afterCode := dropped.1
  have codeBuffers : DispatchBuffers h r slowCode
      (first :: second :: third :: fourth :: rest) :=
    dropped.2.1
  have codeStream : stream slowCode
      (first :: second :: third :: fourth :: rest) =
      List.drop entry.bits.toNat
        (stream slow
          (first :: second :: third :: fourth :: rest)) := by
    simpa only [count, Zlib.Inffast.Proofs.toNat32]
      using dropped.2.2.1
  have codeHeld : 1 ≤ slowCode.bits.toNat := by
    have remaining : slowCode.bits.toNat =
        slow.bits.toNat - count.toNat := dropped.2.2.2
    have countNat : count.toNat =
        lenCodes[index].bits.toNat := rfl
    omega
  have codeBound : slowCode.bits.toNat ≤ 30 := by
    have remaining : slowCode.bits.toNat =
        slow.bits.toNat - count.toNat := dropped.2.2.2
    omega
  let baseLocal : Zlib.Inffast.L := { afterCode with
    op := entry.op.toUInt32 &&& 15,
    len := entry.val.toUInt32 }
  have basePacket : FastInputPacket h slowCode
      (first :: second :: third :: fourth :: rest)
      baseLocal :=
    ⟨codePacket.source, codePacket.cursor,
      codePacket.hold, codePacket.bits⟩
  have baseWidth : baseLocal.op.toNat ≤ 5 := by
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [baseLocal, entry] using extraWidth
  have baseLength : 3 ≤ baseLocal.len.toNat ∧
      baseLocal.len.toNat + 2 ^ baseLocal.op.toNat ≤ 259 := by
    simp only [baseLocal, Zlib.Inffast.Proofs.toNat32]
    rw [Zlib.Inffast.Proofs.mask15]
    simpa only [entry, UInt16.toNat_toUInt32] using lengthBase
  have baseOut : baseLocal.out = .ref dest j := outPtr
  have codePut : slowCode.put = .ref dest oo := outputPtr
  have codeEnd : c.end_ = .ref dest
      (oo + slowCode.left.toNat - 257) := endPtr
  have codeSize : oo + slowCode.left.toNat ≤ output.size :=
    outputSize
  have baseGuard : C.run (Ptr.lt baseLocal.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨result, after, array, next, lenRun,
    out, lower, upper, bytes, size⟩ :=
    basePacket.dolenLen_four_byte_output_bound invariant codeBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr distGet distSafe distMask baseWidth codeBound codeHeld
      left avail baseLength baseOut codePut begPtr codeEnd
      outputGet outputWrite codeSize current beginLe span
      baseGuard
  have baseBool : (entry.op.toUInt32 &&& 16 != 0) = true := by
    rw [Zlib.Inffast.Proofs.mask16]
    simpa only [entry, bne_iff_ne] using base
  have notLiteral : (entry.op.toUInt32 == 0) = false := by
    have nonzero : entry.op.toUInt32 ≠ 0 := by
      intro zero
      rw [zero] at baseBool
      simp at baseBool
    simp [nonzero]
  have shiftRun : Zlib.Inffast.shr64 l.hold count.toUInt64 h =
      .ok (l.hold >>> count.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    exact countSmall
  have run : C.run (Zlib.Inffast.dolen c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.dolen c l) h = .ok (result, after)
    rw [Zlib.Inffast.Proofs.dolen_eq_len]
    rw [bind_ok load]
    rw [bind_ok shiftRun]
    rw [bind_ok load]
    simp only [notLiteral, baseBool,
      Bool.false_eq_true, ite_false, ite_true]
    rw [bind_ok load]
    simpa only [C.run, baseLocal, afterCode,
      firstLocal, count, entry] using lenRun
  exact ⟨result, after, array, next, run,
    out, lower, upper, bytes, size⟩

theorem FastInputPacket.dolen_root_base_loop_four_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {lenRef : CodeRef} {lenCodes : Array Code} {index : Nat}
    (herePtr : l.here = .ref lenRef index)
    (lenGet : Space.get h lenRef = some lenCodes)
    (indexBound : index < lenCodes.size)
    (codeFits : lenCodes[index].bits.toNat ≤ slow.bits.toNat)
    (codeWidth : lenCodes[index].bits.toNat ≤ 15)
    (base : lenCodes[index].op &&& 16 ≠ 0)
    (extraWidth : (lenCodes[index].op &&& 15).toNat ≤ 5)
    (lengthBase : 3 ≤ lenCodes[index].val.toNat ∧
      lenCodes[index].val.toNat +
        2 ^ (lenCodes[index].op &&& 15).toNat ≤ 259)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (held : 16 ≤ slow.bits.toNat)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨result, after, array, next, run, out, lower,
    upper, bytes, size⟩ :=
    packet.dolen_base_leaf_four_byte_output_bound invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth
      (by omega) base extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  obtain ⟨_, _, _, _, result₂, after₂,
    _, _, _, oldRun, noAgain₂, _, _, _, _, _, _⟩ :=
    packet.dolen_base_leaf_four_byte_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      herePtr lenGet indexBound codeFits codeWidth
      (by omega) base extraWidth lengthBase dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have resultEq : result₂ = result := by
    rw [run] at oldRun
    exact (Prod.mk.inj (Except.ok.inj oldRun)).1.symm
  have noAgain : result.againL = false := by
    rw [resultEq] at noAgain₂
    exact noAgain₂
  exact ⟨result, after, array, next,
    dolen_loop_one run noAgain, out, lower, upper,
    bytes, size⟩

theorem FastInputPacket.dolen_linked_base_four_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 16 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    let rootEntry := codes.getD (baseOff + rootSlice) default
    ∃ linked slice,
      C.run (Zlib.Inffast.dolen c l) h = .ok (linked, h) ∧
      linked.againL = true ∧
      slice < 2 ^ rootEntry.op.toNat ∧
      linked.here = .ref codeRef
        (baseOff + rootEntry.val.toNat + slice) ∧
      ((let target := codes.getD
          (baseOff + rootEntry.val.toNat + slice) default
        target.op &&& 16 ≠ 0 ∧
        (target.op &&& 15).toNat ≤ 5 ∧
        3 ≤ target.val.toNat ∧
        target.val.toNat +
          2 ^ (target.op &&& 15).toNat ≤ 259) →
        ∃ result after array next,
          C.run (cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current)) l) h =
            .ok (result, after) ∧
          result.out = .ref dest next ∧
          j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
          Space.get after dest = some array ∧
          array.size = output.size) := by
  have rootBound : baseOff + rootSlice < codes.size := by
    rcases safe with ⟨_, rootSize, _⟩
    omega
  have rootEq : codes.getD (baseOff + rootSlice) default =
      codes[baseOff + rootSlice] := by
    simp [Array.getD_eq_getD_getElem?, rootBound]
  have rootLink : LenLink codes[baseOff + rootSlice] := by
    simpa only [rootEq] using link
  have selected := safe.2.2 rootSlice root
  rw [rootEq, if_pos rootLink] at selected
  rcases selected with ⟨rootWidthBound, _, opWidth,
    subtable, _⟩
  have rootFits : codes[baseOff + rootSlice].bits.toNat ≤
      slow.bits.toNat := by omega
  have notBase :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
        false := by
    rw [Zlib.Inffast.Proofs.mask16]
    simp [rootLink.2.1]
  have linkBool :
      (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
        true := by
    rw [Zlib.Inffast.Proofs.mask64]
    simp [rootLink.2]
  obtain ⟨linked, slice, firstRun, sliceBound, linkedHere,
    againL, _, linkedOutEq, _, linkedPacket, _,
    linkedBuffers, linkedSource⟩ :=
    packet.dolen_link_default_state_exact invariant buffers
      herePtr lcodePtr codesGet rootBound rootFits
      rootWidthBound rootLink.1 notBase linkBool opWidth
      subtable
  let slowLink : IL := { slow with
    hold := slow.hold >>>
      codes[baseOff + rootSlice].bits.toUInt32.toUInt64,
    bits := slow.bits -
      codes[baseOff + rootSlice].bits.toUInt32 }
  have target := len_table_link_target safe root link
    (by simpa only [rootEq] using sliceBound)
  let targetIndex : Nat := baseOff +
    codes[baseOff + rootSlice].val.toNat + slice
  have targetBound : targetIndex < codes.size := by
    simpa only [rootEq, targetIndex] using target.1
  have targetEq : codes.getD targetIndex default =
      codes[targetIndex] := by
    simp [Array.getD_eq_getD_getElem?, targetBound]
  have targetEqNorm : codes.getD
      (baseOff + (codes[baseOff + rootSlice].val.toNat + slice))
      default =
      codes[baseOff +
        (codes[baseOff + rootSlice].val.toNat + slice)] := by
    simpa only [targetIndex, Nat.add_assoc] using targetEq
  have targetHere : linked.here = .ref codeRef targetIndex := by
    simpa only [targetIndex] using linkedHere
  have targetLeaf : LenLeaf
      codes[baseOff + rootSlice].bits.toNat
      codes[targetIndex] := by
    simpa only [rootEq, targetIndex, targetEq]
      using target.2.1
  have targetFits : codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat :=
    linked_distance_leaf_bits_fit (by omega) rootFits targetLeaf.1
      (by simpa only [slowLink] using linkedSource)
  have targetWidth : codes[targetIndex].bits.toNat ≤ 15 := by
    have width := targetLeaf.1
    omega
  have linkedOut : linked.out = .ref dest j :=
    linkedOutEq.trans outPtr
  let rootCount : UInt32 :=
    codes[baseOff + rootSlice].bits.toUInt32
  let firstLocal : Zlib.Inffast.L :=
    { l with againL := false, op := rootCount }
  have firstPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest)
      firstLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have rootCountFits : rootCount.toNat ≤ slow.bits.toNat := by
    simpa only [rootCount, Zlib.Inffast.Proofs.toNat32]
      using rootFits
  have rootCountSmall : rootCount.toNat < 64 := by
    have width : rootCount.toNat ≤ 15 := by
      simpa only [rootCount, Zlib.Inffast.Proofs.toNat32]
        using rootWidthBound
    omega
  have dropped := firstPacket.drop_bits_default_state
    buffers rootCount rootCountFits rootCountSmall
  have linkedBitsBound : slowLink.bits.toNat ≤ 30 := by
    have remaining : slowLink.bits.toNat =
        slow.bits.toNat - rootCount.toNat := by
      simpa only [slowLink, rootCount] using dropped.2.2.2
    omega
  have targetHeld : 1 + codes[targetIndex].bits.toNat ≤
      slowLink.bits.toNat := by
    have remaining : slowLink.bits.toNat =
        slow.bits.toNat - rootCount.toNat := by
      simpa only [slowLink, rootCount] using dropped.2.2.2
    have countNat : rootCount.toNat =
        codes[baseOff + rootSlice].bits.toNat := rfl
    have total := targetLeaf.1
    omega
  have linkedPut : slowLink.put = .ref dest oo := outputPtr
  have linkedEnd : c.end_ = .ref dest
      (oo + slowLink.left.toNat - 257) := endPtr
  have linkedSize : oo + slowLink.left.toNat ≤ output.size :=
    outputSize
  have linkedGuard : C.run (Ptr.lt linked.out c.end_) h =
      .ok (true, h) := by
    simpa only [linkedOut, outPtr] using guard
  refine ⟨linked, slice, firstRun, againL,
    by simpa only [rootEq] using sliceBound,
    by simpa only [rootEq, targetIndex] using linkedHere,
    ?_⟩
  intro selectedBase
  have base : codes[targetIndex].op &&& 16 ≠ 0 ∧
      (codes[targetIndex].op &&& 15).toNat ≤ 5 ∧
      3 ≤ codes[targetIndex].val.toNat ∧
      codes[targetIndex].val.toNat +
        2 ^ (codes[targetIndex].op &&& 15).toNat ≤ 259 := by
    simpa only [rootEq, targetIndex, targetEq]
      using selectedBase
  obtain ⟨result, after, array, next, secondRun,
    out, lower, upper, bytes, size⟩ :=
    linkedPacket.dolen_base_leaf_four_byte_output_bound invariant
      linkedBuffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq targetHere codesGet targetBound
      targetFits targetWidth targetHeld base.1 base.2.1
      ⟨base.2.2.1, base.2.2.2⟩
      dcodePtr distGet distSafe distMask linkedBitsBound
      (by simpa only [slowLink] using left)
      (by simpa only [slowLink] using avail)
      linkedOut linkedPut begPtr linkedEnd outputGet
      outputWrite linkedSize current beginLe span linkedGuard
  obtain ⟨_, _, _, _, result₂, after₂, _, _, _,
    oldRun, noAgain₂, _, _, _, _, _, _⟩ :=
    linkedPacket.dolen_base_leaf_four_byte_default_state invariant
      linkedBuffers streamPtr statePtr whaveEq wsizeEq
      wnextEq windowEq targetHere codesGet targetBound
      targetFits targetWidth targetHeld base.1 base.2.1
      ⟨base.2.2.1, base.2.2.2⟩
      dcodePtr distGet distSafe distMask linkedBitsBound
      (by simpa only [slowLink] using left)
      (by simpa only [slowLink] using avail)
      linkedOut linkedPut begPtr linkedEnd outputGet
      outputWrite linkedSize current beginLe span linkedGuard
  have resultEq : result₂ = result := by
    rw [secondRun] at oldRun
    exact (Prod.mk.inj (Except.ok.inj oldRun)).1.symm
  have noAgain : result.againL = false := by
    rw [resultEq] at noAgain₂
    exact noAgain₂
  have loopRun : C.run
      (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) := by
    apply Zlib.Inffast.Proofs.cdoWhile_two firstRun
      (by simp only [againL, C.run, pure] :
        C.run (pure (linked.againL, linked)) h =
          .ok ((true, linked), h))
      secondRun
      (by simp only [noAgain, C.run, pure] :
        C.run (pure (result.againL, result)) after =
          .ok ((false, result), after))
  exact ⟨result, after, array, next, loopRun, out,
    lower, by simpa only [slowLink] using upper,
    bytes, size⟩

theorem FastInputPacket.dolen_link_complete_four_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (link : LenLink (codes.getD (baseOff + rootSlice) default))
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 16 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨linked, slice, slowLink, firstRun, _,
    sliceBound, here, leaf, _, _, _, _, _⟩ :=
    packet.dolen_root_link_default_state invariant buffers
      herePtr lcodePtr codesGet safe root link (by omega)
  obtain ⟨_, targetLeaf, classes⟩ :=
    len_table_link_source_cases safe root link sliceBound
  let rootEntry : Code :=
    codes.getD (baseOff + rootSlice) default
  let target : Code := codes.getD
    (baseOff + rootEntry.val.toNat + slice) default
  have total : rootEntry.bits.toNat + target.bits.toNat ≤ 15 := by
    have bound : target.bits.toNat + rootEntry.bits.toNat ≤ 15 :=
      targetLeaf.1
    omega
  have cursorBound : j ≤ oo + slow.left.toNat := by
    let one : Zlib.Inffast.L := { l with len := 1 }
    have oneGuard : C.run (Ptr.lt one.out c.end_) h =
        .ok (true, h) := guard
    have oneRoom := fast_output_room_of_guard
      (l := one) (slow := slow) outPtr endPtr outputGet
      outputSize current avail (by simp [one]) oneGuard
    have room := oneRoom.2.2
    change j + 1 ≤ oo + slow.left.toNat at room
    omega
  rcases classes with literal | base | terminal | invalid
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_literal_output_bound invariant
        buffers herePtr lcodePtr codesGet safe root link (by omega)
        left avail outPtr outputPtr endPtr outputGet
        outputWrite outputSize current guard
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        (codes.getD (baseOff + rootEntry.val.toNat + slice₂)
          default).op = 0 := by
      simpa only [unique.2] using literal
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_base_four_byte_output_bound invariant
        buffers streamPtr statePtr whaveEq wsizeEq
        wnextEq windowEq herePtr lcodePtr codesGet
        safe root link dcodePtr distGet distSafe distMask
        held bitsBound left avail outPtr outputPtr begPtr
        endPtr outputGet outputWrite outputSize current
        beginLe span guard
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op &&& 16 ≠ 0 ∧
          (target₂.op &&& 15).toNat ≤ 5 ∧
          3 ≤ target₂.val.toNat ∧
          target₂.val.toNat +
            2 ^ (target₂.op &&& 15).toNat ≤ 259 := by
      simpa only [unique.2] using base
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_end_output_bound invariant
        buffers statePtr mode herePtr lcodePtr codesGet
        safe root link (by omega) outPtr outputGet cursorBound
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op ≠ 0 ∧
          (target₂.op.toUInt32 &&& 16 != 0) = false ∧
          (target₂.op.toUInt32 &&& 64 == 0) = false ∧
          (target₂.op.toUInt32 &&& 32 != 0) = true := by
      simpa only [unique.2] using terminal
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩
  · obtain ⟨linked₂, slice₂, run₂, _, _, here₂,
      selected⟩ :=
      packet.dolen_linked_invalid_output_bound invariant
        buffers streamPtr statePtr herePtr lcodePtr
        codesGet safe root link (by omega) outPtr outputGet cursorBound
    have unique := dolen_link_slice_unique firstRun run₂
      here here₂
    have selected₂ :
        let target₂ := codes.getD
          (baseOff + rootEntry.val.toNat + slice₂) default
        target₂.op ≠ 0 ∧
          (target₂.op.toUInt32 &&& 16 != 0) = false ∧
          (target₂.op.toUInt32 &&& 64 == 0) = false ∧
          (target₂.op.toUInt32 &&& 32 != 0) = false := by
      simpa only [unique.2] using invalid
    obtain ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩ := selected selected₂
    exact ⟨result, after, array, next, loopRun,
      out, lower, upper, bytes, size⟩
theorem FastInputPacket.dolen_root_nonlink_four_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    (notLinkRoot : ¬ LenLink
      (codes.getD (baseOff + rootSlice) default))
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 16 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨indexBound, classes⟩ :=
    len_table_root_source_cases safe root
  let entry : Code := codes.getD (baseOff + rootSlice) default
  have entryEq : entry = codes[baseOff + rootSlice] := by
    simp only [entry]
    simp [Array.getD_eq_getD_getElem?, indexBound]
  have cursorBound : j ≤ oo + slow.left.toNat := by
    let one : Zlib.Inffast.L := { l with len := 1 }
    have oneGuard : C.run (Ptr.lt one.out c.end_) h =
        .ok (true, h) := guard
    have oneRoom := fast_output_room_of_guard
      (l := one) (slow := slow) outPtr endPtr outputGet
      outputSize current avail (by simp [one]) oneGuard
    have room := oneRoom.2.2
    change j + 1 ≤ oo + slow.left.toNat at room
    omega
  rcases classes with ⟨link, _⟩ |
    ⟨_, width, literal | base | terminal | invalid⟩
  · exact False.elim (notLinkRoot link)
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have literalCode : codes[baseOff + rootSlice].op = 0 := by
      simpa only [← entryEq] using literal
    exact packet.dolen_root_literal_loop_output_bound
      invariant buffers herePtr codesGet indexBound
      codeFits codeWidth literalCode left avail outPtr
      outputPtr endPtr outputGet outputWrite outputSize
      current guard
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have baseCode : codes[baseOff + rootSlice].op &&& 16 ≠ 0 ∧
        (codes[baseOff + rootSlice].op &&& 15).toNat ≤ 5 ∧
        3 ≤ codes[baseOff + rootSlice].val.toNat ∧
        codes[baseOff + rootSlice].val.toNat +
          2 ^ (codes[baseOff + rootSlice].op &&& 15).toNat ≤
          259 := by simpa only [← entryEq] using base
    exact packet.dolen_root_base_loop_four_byte_output_bound
      invariant buffers streamPtr statePtr whaveEq
      wsizeEq wnextEq windowEq herePtr codesGet
      indexBound codeFits codeWidth baseCode.1
      baseCode.2.1 ⟨baseCode.2.2.1, baseCode.2.2.2⟩
      dcodePtr distGet distSafe distMask bitsBound held
      left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe
      span guard
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have terminalCode : codes[baseOff + rootSlice].op ≠ 0 ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 32 != 0) =
          true := by simpa only [← entryEq] using terminal
    exact packet.dolen_root_end_loop_output_bound
      invariant buffers statePtr mode herePtr codesGet
      indexBound codeFits codeWidth terminalCode.1
      terminalCode.2.1 terminalCode.2.2.1
      terminalCode.2.2.2 outPtr outputPtr outputGet
      outputSize cursorBound
  · have codeFits : codes[baseOff + rootSlice].bits.toNat ≤
        slow.bits.toNat := by
      have selectedWidth : codes[baseOff + rootSlice].bits.toNat ≤
          15 := by simpa only [← entryEq] using width
      omega
    have codeWidth : codes[baseOff + rootSlice].bits.toNat ≤
        15 := by simpa only [← entryEq] using width
    have invalidCode : codes[baseOff + rootSlice].op ≠ 0 ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 16 != 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 64 == 0) =
          false ∧
        (codes[baseOff + rootSlice].op.toUInt32 &&& 32 != 0) =
          false := by simpa only [← entryEq] using invalid
    exact packet.dolen_root_invalid_loop_output_bound
      invariant buffers streamPtr statePtr herePtr
      codesGet indexBound codeFits codeWidth
      invalidCode.1 invalidCode.2.1
      invalidCode.2.2.1 invalidCode.2.2.2
      outPtr outputPtr outputGet outputSize cursorBound

theorem FastInputPacket.dolen_root_complete_four_byte_output_bound
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth rootSlice : Nat}
    (herePtr : l.here = .ref codeRef (baseOff + rootSlice))
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (root : rootSlice < 2 ^ rootWidth)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (held : 16 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (cdoWhile (Zlib.Inffast.dolen c)
        (fun current => pure (current.againL, current)) l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨indexBound, classes⟩ :=
    len_table_root_source_cases safe root
  rcases classes with ⟨link, _⟩ | ⟨notLink, width, classes⟩
  · exact packet.dolen_link_complete_four_byte_output_bound
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq herePtr lcodePtr codesGet
      safe root link dcodePtr distGet distSafe distMask
      held bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
  · exact packet.dolen_root_nonlink_four_byte_output_bound
      invariant buffers streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq herePtr lcodePtr codesGet
      safe root notLink dcodePtr distGet distSafe distMask
      held bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard
theorem FastInputPacket.fast_body_pull_output_bound
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
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (small : slow.bits.toNat < 15)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  obtain ⟨next1, fast1, slow1, pull1, _, slow1Eq,
    fast1Eq, packet1, _, buffers1, stream1⟩ :=
    packet.pull_default_state invariant buffers (by omega)
  have small1 : slow1.bits.toNat ≤ 22 := by
    rw [slow1Eq]
    change (slow.bits + 8).toNat ≤ 22
    rw [u32_add8 slow.bits (by omega)]
    omega
  obtain ⟨next2, fast2, slow2, pull2, _, slow2Eq,
    fast2Eq, packet2, _, buffers2, stream2⟩ :=
    packet1.pull_default_state invariant buffers1 small1
  have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
    rw [slow1Eq]
    exact u32_add8 slow.bits (by omega)
  have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by
    rw [slow2Eq]
    exact u32_add8 slow1.bits (by omega)
  have held2 : 16 ≤ slow2.bits.toNat := by omega
  have bitsBound2 : slow2.bits.toNat ≤ 30 := by omega
  let rootSlice := (fast2.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { fast2 with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet2.fast_body_root_lookup lcodePtr codesGet safe lenMask
  have out2 : selected.out = .ref dest j := by
    simp only [selected, fast2Eq, fast1Eq,
      Zlib.Inffast.Proofs.pullL]
    exact outPtr
  have put2 : slow2.put = .ref dest oo := by
    simpa only [slow2Eq, slow1Eq, pulled] using outputPtr
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    simpa only [slow2Eq, slow1Eq, pulled] using endPtr
  have left2 : slow2.left ≠ 0 := by
    simpa only [slow2Eq, slow1Eq, pulled] using left
  have avail2 : 258 ≤ slow2.left.toNat := by
    simpa only [slow2Eq, slow1Eq, pulled] using avail
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    simpa only [slow2Eq, slow1Eq, pulled] using outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    simpa only [out2, outPtr] using guard
  obtain ⟨result, after, array, next, loopRun,
    out, lower, upper, bytes, size⟩ :=
    selectedPacket.dolen_root_complete_four_byte_output_bound
      invariant buffers2 streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq rfl lcodePtr codesGet
      safe root dcodePtr distGet distSafe distMask held2
      bitsBound2 left2 avail2 out2 put2 begPtr end2
      outputGet outputWrite size2 current beginLe span guard2
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.inflate_fast_body
    simp only [needsPull, ite_true]
    change (Zlib.Inffast.pull l >>= fun q =>
      Zlib.Inffast.pull q >>= fun q' =>
        Ptr.add c.lcode
          (q'.hold &&& c.lmask.toUInt64).toNat >>= fun here =>
          cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current))
            { q' with here }) h = .ok (result, after)
    change Zlib.Inffast.pull l h = .ok (fast1, h) at pull1
    change Zlib.Inffast.pull fast1 h = .ok (fast2, h) at pull2
    change Ptr.add c.lcode rootSlice h =
      .ok (.ref codeRef (baseOff + rootSlice), h) at addRun
    change (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current))
      selected) h = .ok (result, after) at loopRun
    simp only [bind_app, pull1, pull2, addRun, loopRun,
      rootSlice, selected]
  exact ⟨result, after, array, next, bodyRun,
    out, lower,
    by simpa only [slow2Eq, slow1Eq, pulled] using upper,
    bytes, size⟩

theorem FastInputPacket.fast_body_output_bound
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
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after array next,
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size := by
  by_cases small : slow.bits.toNat < 15
  · exact packet.fast_body_pull_output_bound invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq
      windowEq lcodePtr codesGet safe lenMask dcodePtr
      distGet distSafe distMask small left avail outPtr
      outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
  · exact packet.fast_body_no_pull_output_bound invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq
      windowEq lcodePtr codesGet safe lenMask dcodePtr
      distGet distSafe distMask (by omega) bitsBound
      left avail outPtr outputPtr begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard

#print axioms FastInputPacket.fast_body_output_bound
end Zlib.Inflate.Proofs
