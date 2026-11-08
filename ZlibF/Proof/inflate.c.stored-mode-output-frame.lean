import ZlibF.Proof.«inflate.c.header-output-frame»
import ZlibF.Proof.«inflate.c.stored-dispatch»
import ZlibF.Proof.«inflate.c.stored-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual COPY_ mode store precedes the same COPY execution whose
exact produced prefix is already proved. -/
theorem inflate_COPY_start_frame_of_run {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_COPY_ c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  let state := { s with mode := COPY }
  let heap := setI h zs state
  have current : Good heap r zs z state := good.decode_update (by rfl)
    (by change HEAD ≤ COPY ∧ COPY ≤ SYNC; decide)
  have env1 : Env c heap r zs z state := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have packet : DispatchBuffers heap r l bs := buffers.byte_views good current rfl
    (byte_view_get_setI h zs state) (byte_view_ro_setI h zs state)
  have original := run
  rw [inflate_COPY__eq E l] at run
  have frame := inflate_COPY_frame_of_run env1 current packet run count
  obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  have ro : after.ro = h.ro := congrArg Prod.fst
    (fastMemoryMetaFrameX_inflate_COPY_ r c E.strm l h outcome regs after original)
  have writable : Space.ro after dest = false := by rw [byte_view_ro_of_ro_eq ro]; exact write
  rw [pointer] at frame ⊢
  have frame' : BufferFrame (setI (r.put h z) zs state) after
      (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
    simpa only [ZStreamRef.put_self E.hz] using frame
  exact metadata_then_output_buffer_frame E.hz E.hs get write frame' writable

/-- The stored-block header performs no output writes. Its real COPY_
continuation supplies exactly the output interval recorded by left. -/
theorem inflate_STORED_frame_of_run {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    {outcome : Except Ex Unit} {made : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (buffers : DispatchBuffers h r l bs)
    (run : runX (inflate_STORED c) l h = .ok ((outcome, regs), after))
    (count : regs.left.toNat + made = l.left.toNat) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv buffers.bits
  obtain ⟨result, current, used, pull, usedBound, bits, _, _, shape,
    _, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor aligned 32 (by decide)
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have put : current.put = l.put := by rw [shape]; rfl
  have left : current.left = l.left := by rw [shape]; rfl
  obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  rcases kinds with normal | wait
  · rw [normal] at pull
    by_cases bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨i, _, actual⟩ := inflate_STORED_bad E l current pull bad
      have same := Except.ok.inj (actual.symm.trans run)
      cases same
      have zero : made = 0 := by rw [left] at count; omega
      subst made
      exact (badHeap_buffer_frame E.hz E.hs i [⟨l.put, 0⟩]).1
    · let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let heap0 := setI h zs ready
      let first := { current with hold := 0, bits := 0 }
      have good0 : Good heap0 r zs z ready := good.decode_update (by rfl)
        (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
      have env0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have inv0 : BitInv heap0 first (bs.drop used) := (INITBITS_inv bits).1.decode_update zs ready
      have packet : DispatchBuffers heap0 r first (bs.drop used) :=
        buffers.consume good good0 rfl (fun ref => byte_view_get_setI h zs ready ref)
          (fun ref => byte_view_ro_setI h zs ready ref)
          (by dsimp only [first]; rw [shape]; rfl) cursor usedBound inv0
      have cut := inflate_STORED_ok E l current pull bad
      by_cases trees : c.flush = Z_TREES
      · have actual : runX (inflate_STORED c) l h = .ok ((.error Ex.leave, first), heap0) := by
          rw [cut]
          simp only [trees, beq_self_eq_true, ↓reduceIte]
          rfl
        have heapEq : after = heap0 := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
        have nextLeft : regs.left = current.left :=
          congrArg (fun pair => pair.1.2.left) (Except.ok.inj (run.symm.trans actual))
        have zero : made = 0 := by rw [nextLeft, left] at count; omega
        subst made
        rw [heapEq]
        have frame := (fastWriteback_heap_frame E.hz E.hs z ready [⟨l.put, 0⟩]).1
        simpa only [ZStreamRef.put_self E.hz] using frame
      · have source : runX (inflate_STORED c) l h = runX (inflate_COPY_ c) first heap0 := by
          rw [cut]
          simp only [beq_iff_eq, trees, ↓reduceIte]
          rfl
        have actual : runX (inflate_COPY_ c) first heap0 = .ok ((outcome, regs), after) := source.symm.trans run
        have count0 : regs.left.toNat + made = first.left.toNat := by change _ = current.left.toNat; rw [left]; exact count
        have frame := inflate_COPY_start_frame_of_run env0 good0 packet actual count0
        have ro : after.ro = h.ro := congrArg Prod.fst
          (fastMemoryMetaFrameX_inflate_STORED r c E.strm l h outcome regs after run)
        have writable : Space.ro after dest = false := by rw [byte_view_ro_of_ro_eq ro]; exact write
        change BufferFrame heap0 after _ [⟨current.put, made⟩] at frame
        rw [put, pointer] at frame
        have frame' : BufferFrame (setI (r.put h z) zs ready) after
            (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
          simpa only [ZStreamRef.put_self E.hz] using frame
        rw [pointer]
        exact metadata_then_output_buffer_frame E.hz E.hs get write frame' writable
  · have actual := inflate_STORED_wait (c := c) l current h Ex.leave (by rwa [wait] at pull)
    have same := Except.ok.inj (actual.symm.trans run)
    cases same
    have zero : made = 0 := by rw [left] at count; omega
    subst made
    exact bufferFrame_live_refl E.hz E.hs [⟨l.put, 0⟩]

/-- Every stored-block switch case uses the same exact produced count
for caller accounting and its public output frame. -/
theorem inflate_dispatch_stored_exact_frame
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state made,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨outcome, regs, after, stream, state, _, made, _, run, current, _, _, _, _, _, _, put, count, _⟩ :=
    inflate_dispatch_stored_state_rank E invariant buffers mode incoming
  refine ⟨outcome, regs, after, stream, state, made, run, current.good, count, put, ?_⟩
  rcases mode with stored | start | copying
  · exact inflate_STORED_frame_of_run E invariant.good buffers
      ((inflate_dispatch_STORED E l stored).symm.trans run) count
  · exact inflate_COPY_start_frame_of_run E invariant.good buffers
      ((inflate_dispatch_COPY_start E l start).symm.trans run) count
  · exact inflate_COPY_frame_of_run E invariant.good buffers
      ((inflate_dispatch_COPY E l copying).symm.trans run) count

#print axioms inflate_COPY_start_frame_of_run
#print axioms inflate_STORED_frame_of_run
#print axioms inflate_dispatch_stored_exact_frame
end Zlib.Inflate.Proofs
