import ZlibF.Proof.«inflate.c.installed-payload-tables»
import ZlibF.Proof.«inflate.c.payload-future-loop-account»
import ZlibF.Proof.«inflate.c.fast-view-prelude-ready-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec Zlib.Inftrees ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Actual source prelude into the future-aware semantic loop for an
initial zero-window payload. Semantic tables come from actual header
construction; no full block in the current buffer is required. -/
theorem fastEntryPrefix_future_zero_window
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : DataTableMode s.mode)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    {L D : List Nat} {future tail : List Bool} {target : List UInt8}
    (semanticTables : FunctionalEpoch.InstalledTables h s L D)
    (distanceFlags : ∀ (ref : CodeRef) (offset : Nat) (codes : Array Code),
      s.distcode = .ref ref offset → Space.get h ref = some codes →
      Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS codes offset s.distbits.toNat)
    (zeroWindow : s.wsize = 0) (noOutput : slow.out_ = slow.left)
    (parsed : ZlibF.Spec.Symbols L D [] [] (stream slow bs ++ future) tail target)
    (fast : (slow.have_ >= 6 && slow.left >= 258 &&
      slow.bits < 8) = true) :
    ∃ (ctx : FastLoopContext) (q : Zlib.Inffast.L),
      C.run (fastEntryPrefix (some r) slow.out_) h =
        .ok ((ctx.c, q), h) ∧
      ctx.r = r ∧ ctx.zs = zs ∧ ctx.z = z ∧ ctx.s = s ∧
      ctx.rootWidth = s.lenbits.toNat ∧ ctx.distWidth = s.distbits.toNat ∧
      ctx.c.lcode = s.lencode ∧ ctx.c.dcode = s.distcode ∧
      q.broke = false ∧ FastFutureReady ctx L D [] future tail target h q := by
  obtain ⟨ir, dest, io, oo, nextPtr, putPtr, prefixRun⟩ :=
    fastEntryPrefix_run invariant.good invariant.platform
      buffers (invariant.tables mode) inputCursor inputCount
      outputCursor outputCount stateHold stateBits fast
  obtain ⟨lr, lo, lc, lptr, lget, lsafe⟩ :=
    (invariant.tables mode).lengthTable
  obtain ⟨dr, doff, dc, dptr, dget, dsafe⟩ :=
    (invariant.tables mode).distanceTable
  have margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧
      slow.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq]
      using fast
  have inputMargin : 6 ≤ slow.have_.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.1
  have outputMargin : 258 ≤ slow.left.toNat := by
    simpa [UInt32.le_iff_toNat_le] using margins.1.2
  have bitsBound : slow.bits.toNat ≤ 30 := by
    have small : slow.bits.toNat < 8 := by
      simpa [UInt32.lt_iff_toNat_lt] using margins.2
    omega
  let bg := oo - (slow.out_.toNat - slow.left.toNat)
  let c0 : Zlib.Inffast.Ctx := {
    strm := some r, state := some (.tab zs),
    last := .ref ir (io + slow.have_.toNat - 5),
    beg := .ref dest bg,
    end_ := .ref dest (oo + slow.left.toNat - 257),
    wsize := s.wsize, whave := s.whave,
    wnext := s.wnext, window := s.window,
    lcode := s.lencode, dcode := s.distcode,
    lmask := ((1 : UInt32) <<< s.lenbits) - 1,
    dmask := ((1 : UInt32) <<< s.distbits) - 1 }
  let q0 : Zlib.Inffast.L := {
    in_ := slow.next, out := slow.put,
    hold := slow.hold, bits := slow.bits,
    here := default, op := 0, len := 0, dist := 0,
    from_ := default, broke := false,
    againL := false, againD := false }
  let ctx : FastLoopContext := {
    c := c0, r, zs, z, s,
    codeRef := lr, codes := lc, baseOff := lo,
    rootWidth := s.lenbits.toNat,
    distRef := dr, distCodes := dc, distOff := doff,
    distWidth := s.distbits.toNat,
    dest, inputRef := ir, oo, bg,
    leftTotal := slow.left, outTotal := slow.out_,
    streamPtr := rfl, statePtr := rfl, mode,
    whaveEq := rfl, wsizeEq := rfl, wnextEq := rfl,
    windowEq := rfl,
    lcodePtr := lptr, lenSafe := lsafe,
    lenMask := by
      change ((((1 : UInt32) <<< s.lenbits) - 1).toUInt64.toNat) =
        2 ^ s.lenbits.toNat - 1
      rw [UInt32.toNat_toUInt64]
      exact Zlib.Inffast.Proofs.u32_shl1_sub1 (by
        have width := lsafe.1
        omega),
    dcodePtr := dptr, distSafe := dsafe,
    distMask := by
      change ((((1 : UInt32) <<< s.distbits) - 1).toUInt64.toNat) =
        2 ^ s.distbits.toNat - 1
      rw [UInt32.toNat_toUInt64]
      exact Zlib.Inffast.Proofs.u32_shl1_sub1 (by
        have width := dsafe.1
        omega),
    leftNonzero := by
      intro zero
      rw [zero] at outputMargin
      simp at outputMargin,
    avail := outputMargin,
    begPtr := rfl, endPtr := rfl,
    count := buffers.output.count,
    made := buffers.output.produced dest oo putPtr,
    beginEq := rfl }
  have packet : FastInputPacket h slow bs q0 :=
    ⟨buffers.bits, rfl, rfl, rfl⟩
  have ready : FastLoopReady ctx h q0 :=
    FastLoopReady.initial packet invariant buffers lget
      dget rfl rfl putPtr nextPtr rfl inputMargin
      bitsBound rfl
  have lengthMeaning : ∃ used, Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS lc lo s.lenbits.toNat used L := by
    obtain ⟨ref, offset, array, used, pointer, get, meaning, _stable⟩ := semanticTables.1
    have pointers := pointer.symm.trans lptr
    cases pointers
    have same : array = lc := Option.some.inj (get.symm.trans lget)
    subst array
    exact ⟨used, meaning⟩
  have distanceMeaning : ∃ used, Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS dc doff s.distbits.toNat used D := by
    obtain ⟨ref, offset, array, used, pointer, get, meaning, _stable⟩ := semanticTables.2
    have pointers := pointer.symm.trans dptr
    cases pointers
    have same : array = dc := Option.some.inj (get.symm.trans dget)
    subst array
    exact ⟨used, meaning⟩
  have flags := distanceFlags dr doff dc dptr dget
  have zeroHave : s.whave = 0 := by
    apply UInt32.toNat_inj.mp
    have bound := invariant.good.inv.win.hv
    rw [zeroWindow] at bound
    change s.whave.toNat = 0
    simpa using Nat.eq_zero_of_le_zero bound
  rcases ready with ⟨slow1, bs1, output1, off1, k1, packet1, invariant1, buffers1,
    codesGet1, distGet1, bitsBound1, leftEq1, outEq1, putPtr1, nextPtr1, lastPtr1,
    inputMargin1, outPtr1, outputGet1, outputWrite1, outputSize1, current1,
    beginLe1, span1, guard1⟩
  have currentOut : k1 = oo := by
    have same : (.ref dest k1 : BPtr) = .ref dest oo := outPtr1.symm.trans putPtr
    exact (Ptr.ref.inj same).2
  subst k1
  have currentOff : off1 = io := by
    have same : (.ref ir off1 : BPtr) = .ref ir io :=
      nextPtr1.symm.trans (packet1.cursor.symm.trans nextPtr)
    exact (Ptr.ref.inj same).2
  subst off1
  have lastOffsets : io + slow1.have_.toNat - 5 = io + slow.have_.toNat - 5 :=
    (Ptr.ref.inj lastPtr1.symm).2
  have lengthEq : bs.length = bs1.length := by
    have oldCount := buffers.bits.have_eq
    have newCount := packet1.source.have_eq
    omega
  have nonempty : bs ≠ [] := by
    intro empty
    have count := buffers.bits.have_eq
    rw [empty] at count
    simp only [List.length_nil] at count
    omega
  have sameBytes := packet.unread_unique_of_length packet1 nonempty lengthEq
  have sameBits : slow1.bits = slow.bits := packet1.bits.symm.trans packet.bits
  have sameHold : slow1.hold = slow.hold := packet1.hold.symm.trans packet.hold
  have sameStream : stream slow1 bs1 = stream slow bs := by
    rw [← sameBytes]
    simp only [stream, sameBits, sameHold]
  have zeroSpan : oo - ctx.bg = 0 := by
    change oo - (oo - (slow.out_.toNat - slow.left.toNat)) = 0
    rw [noOutput, Nat.sub_self, Nat.sub_zero, Nat.sub_self]
  have emptyWritten : ZlibF.Math.LZ77Copy.writtenBytes output1 oo (oo - ctx.bg) = [] := by
    rw [zeroSpan]
    simp only [ZlibF.Math.LZ77Copy.writtenBytes, List.take_zero]
  have semantic : FastFutureReady ctx L D [] future tail target h q0 := by
    refine .intro slow1 bs1 output1 io oo packet1 invariant1 buffers1 codesGet1 distGet1
      bitsBound1 leftEq1 outEq1 putPtr1 nextPtr1 lastPtr1 inputMargin1 outPtr1 outputGet1
      outputWrite1 outputSize1 current1 beginLe1 span1 guard1 lengthMeaning distanceMeaning flags
      #[] 0 ?_ ?_ ?_ [] emptyWritten ?_ (stream slow1 bs1) rfl ?_
    · intro positive
      change 0 < s.whave.toNat at positive
      rw [zeroHave] at positive
      cases positive
    · change Zlib.Inffast.Spec.MatchHistory.saved #[] s.wsize.toNat s.wnext.toNat s.whave.toNat 0 = []
      rw [zeroHave]
      rfl
    · change [].length = s.whave.toNat
      rw [zeroHave]
      rfl
    · exact zeroSpan.symm
    · rwa [sameStream]
  exact ⟨ctx, q0, prefixRun, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, semantic⟩

#print axioms fastEntryPrefix_future_zero_window
end Zlib.Inflate.Proofs
