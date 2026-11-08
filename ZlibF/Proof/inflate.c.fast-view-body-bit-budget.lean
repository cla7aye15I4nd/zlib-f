import ZlibF.Proof.«inflate.c.fast-view-dolen-root-loop-bit-budget»
import ZlibF.Proof.«inflate.c.fast-view-body-post-cursor»
import ZlibF.Proof.«inffast.c.dist-two-pull-ledger»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The translated fast body, after its initial two pulls, charges all held bits to the same at-most-six-byte input cursor. -/
theorem FastInputPacket.fast_body_pull_bit_budget
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
    ∃ result after pulled,
      pulled ≤ 6 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  obtain ⟨next1, fast1, slow1, pull1, next1Eq, slow1Eq,
    fast1Eq, packet1, _, buffers1, _⟩ :=
    packet.pull_default_state invariant buffers (by omega)
  have small1 : slow1.bits.toNat ≤ 22 := by
    rw [slow1Eq]
    change (slow.bits + 8).toNat ≤ 22
    rw [u32_add8 slow.bits (by omega)]
    omega
  obtain ⟨next2, fast2, slow2, pull2, next2Eq, slow2Eq,
    fast2Eq, packet2, _, buffers2, _⟩ :=
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
  obtain ⟨result, after, cursorPulled, cursorBound,
    loopRun, cursor, budget⟩ :=
    selectedPacket.dolen_root_loop_four_byte_bit_budget
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
  refine ⟨result, after, 2 + cursorPulled, by omega,
    bodyRun, ?_, ?_⟩
  · rw [cursor]
    simp only [fast2Eq, fast1Eq,
      Zlib.Inffast.Proofs.pullL]
    rw [next2Eq, inputAdvance_add]
    rw [slow1Eq]
    simp only [pulled]
    rw [next1Eq, ← packet.cursor, inputAdvance_add]
    congr 1
    omega
  · have selectedBits : selected.bits.toNat = l.bits.toNat + 16 := by
      change fast2.bits.toNat = l.bits.toNat + 16
      rw [packet2.bits, packet.bits]
      omega
    rw [selectedBits] at budget
    omega


#print axioms FastInputPacket.fast_body_pull_bit_budget
/-- The no-refill fast body spends at most five bytes, with the same count bounding its final bits. -/
theorem FastInputPacket.fast_body_no_pull_bit_budget
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
    ∃ result after pulled,
      pulled ≤ 5 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  let rootSlice := (l.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet.fast_body_root_lookup lcodePtr codesGet safe lenMask
  obtain ⟨result, after, pulled, bound, loopRun,
    cursor, budget⟩ :=
    selectedPacket.dolen_root_loop_bit_budget invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      rfl lcodePtr codesGet safe root dcodePtr distGet
      distSafe distMask held bitsBound left avail outPtr
      outputPtr begPtr endPtr outputGet outputWrite outputSize
      current beginLe span guard
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
  exact ⟨result, after, pulled, bound, bodyRun,
    by simpa only [selected] using cursor,
    by simpa only [selected] using budget⟩

#print axioms FastInputPacket.fast_body_no_pull_bit_budget
/-- The actual fast body charges its final bits to the same at-most-six-byte physical input cursor. -/
theorem FastInputPacket.fast_body_input_bit_budget
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
    ∃ result after pulled,
      pulled ≤ 6 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled ∧
      result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  by_cases small : slow.bits.toNat < 15
  · exact packet.fast_body_pull_bit_budget invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet distSafe
      distMask small left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  · have held : 15 ≤ slow.bits.toNat := by omega
    obtain ⟨result, after, pulled, bound, run, cursor, bits⟩ :=
      packet.fast_body_no_pull_bit_budget invariant buffers
        streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
        lcodePtr codesGet safe lenMask dcodePtr distGet
        distSafe distMask held bitsBound left avail outPtr
        outputPtr begPtr endPtr outputGet outputWrite outputSize
        current beginLe span guard
    exact ⟨result, after, pulled, by omega, run, cursor, bits⟩

#print axioms FastInputPacket.fast_body_input_bit_budget
/-- The public body packet and the bit budget use the same physical cursor count, including broken returns. -/
theorem FastInputPacket.fast_body_view_post_with_bit_budget
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
    ∃ used consumed slowFinal result after zNext sNext array next,
      used ≤ 6 ∧ consumed ≤ 63 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h = .ok (result, after) ∧
      FastInputPacket after slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) result ∧
      DefaultStateJ after r zs zNext sNext ∧
      DispatchBuffers after r slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) ∧
      ByteViewSizes h after ∧
      stream slowFinal
        (List.drop used
          (first :: second :: third :: fourth :: fifth :: sixth :: rest)) =
        List.drop consumed
          (stream slow
            (first :: second :: third :: fourth :: fifth :: sixth :: rest)) ∧
      result.in_ = slowFinal.next ∧
      result.bits = slowFinal.bits ∧
      slowFinal.bits.toNat ≤ slow.bits.toNat + 8 * used ∧
      result.out = .ref dest next ∧
      j ≤ next ∧ next ≤ oo + slow.left.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      ∃ pulled, pulled ≤ 6 ∧ result.in_ = inputAdvance l.in_ pulled ∧
        result.bits.toNat ≤ l.bits.toNat + 8 * pulled := by
  obtain ⟨used, consumed, slowFinal, result, after, zNext, sNext,
      array, next, usedBound, consumedBound, bodyRun, finalPacket,
      finalInvariant, finalBuffers, sizes, trace, resultCursor,
      resultBits, oldBudget, outputOut, lower, upper, bytes, size,
      cursorPulled, cursorBound, cursor⟩ :=
    packet.fast_body_view_post_with_cursor invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe
      span guard
  obtain ⟨budgetResult, budgetAfter, budgetPulled,
      budgetBound, budgetRun, budgetCursor, budgetBits⟩ :=
    packet.fast_body_input_bit_budget invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet distSafe
      distMask bitsBound left avail outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe
      span guard
  have same : (result, after) = (budgetResult, budgetAfter) :=
    Except.ok.inj (bodyRun.symm.trans budgetRun)
  have resultEq : result = budgetResult := congrArg Prod.fst same
  subst budgetResult
  obtain ⟨inputRef, inputArray, inputOff, inputPtr, _, _, _⟩ :=
    packet.source.next.resolve_left (by simp)
  have initialPtr : l.in_ = .ref inputRef inputOff :=
    packet.cursor.trans inputPtr
  have countEq : cursorPulled = budgetPulled :=
    Zlib.Inffast.Proofs.input_count_eq_of_cursor
      (by simpa only [initialPtr] using cursor)
      (by simpa only [initialPtr] using budgetCursor)
  have finalBudget : result.bits.toNat ≤
      l.bits.toNat + 8 * cursorPulled := by
    rw [countEq]
    exact budgetBits
  exact ⟨used, consumed, slowFinal, result, after, zNext, sNext,
    array, next, usedBound, consumedBound, bodyRun, finalPacket,
    finalInvariant, finalBuffers, sizes, trace, resultCursor,
    resultBits, oldBudget, outputOut, lower, upper, bytes, size,
    ⟨cursorPulled, cursorBound, cursor, finalBudget⟩⟩

#print axioms FastInputPacket.fast_body_view_post_with_bit_budget
end Zlib.Inflate.Proofs
