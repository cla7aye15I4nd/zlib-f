import ZlibF.Proof.«inflate.c.stored-views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual stored-block header and COPY fall-through retain one common
relation. Header exhaustion, a bad complement, Z_TREES and partial copying
are included. No separate-allocation premise is added to caller buffers. -/
theorem inflate_STORED_boundary_budget_modes {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) ∧ after.static = h.static ∧ Shape h after ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
      (outcome = .ok () → state.mode = COPY ∨ state.mode = TYPE ∨ state.mode = BAD) := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv buffers.bits
  have alignCount := UInt32.toNat_sub_of_le l.bits (l.bits &&& 7)
    (UInt32.le_iff_toNat_le.mpr (and7_le l))
  have alignedLe : (bytebits l).bits.toNat ≤ l.bits.toNat := by
    change (l.bits - (l.bits &&& 7)).toNat ≤ _
    rw [alignCount]
    omega
  have alignedBound : (bytebits l).bits.toNat ≤ 39 := by
    change (l.bits - (l.bits &&& 7)).toNat ≤ _
    rw [alignCount]
    omega
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, bitCount, shape,
    bitBound, _, _, _, kinds, cursor⟩ := NEEDBITS_run_cursor aligned 32 (by decide)
  have symbolShape : SymbolRegShape l current := by rw [shape]; rfl
  have next : current.next = inputAdvance l.next used := cursor
  have haveCount : current.have_.toNat + used = l.have_.toNat := by
    rw [bitInv.have_eq, buffers.bits.have_eq, List.length_drop]
    omega
  have put : current.put = l.put := by rw [shape]; rfl
  have left : current.left = l.left := by rw [shape]; rfl
  have bounded : current.bits.toNat ≤ 39 := by
    change current.bits.toNat ≤ max (bytebits l).bits.toNat 39 at bitBound
    omega
  have packet := buffers.consume good good rfl (fun _ => rfl) (fun _ => rfl)
    symbolShape next usedBound bitInv
  rcases kinds with normal | wait
  · rw [normal] at pull
    by_cases bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨i, _, run⟩ := inflate_STORED_bad E l current pull bad
      obtain ⟨currentGood, tables, nextPending, nextPacket, sizes, static⟩ :=
        head_bad_packet good pending packet bitInv (by rfl) i
      exact ⟨.ok (), current, badHeap h r zs z s i, { z with msg := .ref (.str i) 0 },
        { s with mode := BAD }, used, 0, usedBound, run, currentGood, tables, nextPending,
        nextPacket, sizes, by rfl, next, haveCount, by rw [put, inputAdvance_zero],
        by rw [left]; rfl, bounded, Or.inl rfl, static,
        (shape_put good.live.hz { z with msg := .ref (.str i) 0 }).trans
          (shape_setI (by rw [ZStreamRef.put_istates]; exact good.live.hs) { s with mode := BAD }),
        by omega,
        fun _ => Or.inr (Or.inr rfl)⟩
    · let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let heap0 := setI h zs ready
      let first := { current with hold := 0, bits := 0 }
      have frame : DecodeStateFrame s ready := by rfl
      have good0 : Good heap0 r zs z ready := good.decode_update frame
        (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
      have E0 : Env c heap0 r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have pending0 : DataPendingInvariant ready := by
        apply dataPendingInvariant_idle (s := ready) (by exact pending.sane)
        change COPY_ ≠ LENEXT ∧ COPY_ ≠ DIST ∧ COPY_ ≠ DISTEXT ∧ COPY_ ≠ MATCH
        decide
      have inv0 : BitInv heap0 first (bs.drop used) :=
        (INITBITS_inv bitInv).1.decode_update zs ready
      have packet0 : DispatchBuffers heap0 r first (bs.drop used) :=
        buffers.consume good good0 rfl (fun ref => byte_view_get_setI h zs ready ref)
          (fun ref => byte_view_ro_setI h zs ready ref) (by dsimp only [first]; rw [shape]; rfl) next usedBound inv0
      have sourceCut := inflate_STORED_ok E l current pull bad
      by_cases trees : c.flush = Z_TREES
      · have run : runX (inflate_STORED c) l h = .ok ((.error Ex.leave, first), heap0) := by
          rw [sourceCut]
          simp only [trees, beq_self_eq_true, ↓reduceIte]
          rfl
        exact ⟨.error Ex.leave, first, heap0, z, ready, used, 0, usedBound, run, good0,
          dataTableInvariant_inactive (by change ¬ DataTableMode COPY_; unfold DataTableMode; decide),
          pending0, packet0, byte_view_sizes_setI h zs ready, frame, next, haveCount,
          by rw [inputAdvance_zero]; exact put, by change current.left.toNat + 0 = l.left.toNat; rw [left]; rfl, by change 0 ≤ 39; decide, Or.inr rfl, rfl, shape_setI good.live.hs ready,
          by change 0 ≤ _; omega, fun impossible => by cases impossible⟩
      · have sourceRun : runX (inflate_STORED c) l h = runX (inflate_COPY_ c) first heap0 := by
          rw [sourceCut]
          simp only [beq_iff_eq, trees, ↓reduceIte]
          rfl
        obtain ⟨exit, regs, after, state, made, madeBound, run, currentGood, tables, nextPending,
          nextPacket, sizes, stateFrame, nextCursor, inputCount, putCursor, outputCount,
          bits, _, exits, static, heapShape⟩ := inflate_COPY_start_boundary_frame E0 good0 pending0 packet0 rfl
        have exitKinds : exit = .ok () ∨ exit = .error Ex.leave := by
          rcases exits with wait | done | copied
          · exact Or.inr wait.1
          · exact Or.inl done.1
          · exact Or.inl copied.1
        have normalModes : exit = .ok () → state.mode = COPY ∨ state.mode = TYPE ∨ state.mode = BAD := by
          intro normal
          rcases exits with wait | done | copied
          · have impossible := wait.1.symm.trans normal
            cases impossible
          · exact Or.inr (Or.inl done.2.2)
          · exact Or.inl copied.2.2.1
        have totalBound : used + made ≤ bs.length := by rw [List.length_drop] at madeBound; omega
        refine ⟨exit, regs, after, z, state, used + made, made, totalBound, sourceRun.trans run,
          currentGood, tables, nextPending, ?_, (byte_view_sizes_setI h zs ready).trans sizes,
          frame.trans stateFrame, ?_, ?_, ?_, ?_, ?_, exitKinds, static, (shape_setI good.live.hs ready).trans heapShape,
          by rw [bits]; change 0 ≤ _; omega, normalModes⟩
        · simpa only [List.drop_drop] using nextPacket
        · rw [nextCursor]
          change inputAdvance current.next made = _
          rw [next, inputAdvance_add]
        · change regs.have_.toNat + made = current.have_.toNat at inputCount
          omega
        · rw [putCursor]
          change inputAdvance current.put made = _
          rw [put]
        · change regs.left.toNat + made = current.left.toNat at outputCount
          rwa [left] at outputCount
        · rw [bits]
          change 0 ≤ 39
          decide
  · have run := inflate_STORED_wait (c := c) l current h Ex.leave (by rwa [wait] at pull)
    exact ⟨.error Ex.leave, current, h, z, s, used, 0, usedBound, run, good,
      dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide), pending, packet,
      ByteViewSizes.refl h, by rfl, next, haveCount, by rw [put, inputAdvance_zero],
      by rw [left]; rfl, bounded, Or.inr rfl, rfl, Shape.refl h,
      by omega,
      fun impossible => by cases impossible⟩

/-- Projection retaining the original complete STORED heap frame. -/
theorem inflate_STORED_boundary_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) ∧ after.static = h.static ∧ Shape h after := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds, static, shape, _, _⟩ :=
    inflate_STORED_boundary_budget_modes E good pending buffers mode incoming
  exact ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds, static, shape⟩

/-- Projection retaining the original complete STORED boundary. -/
theorem inflate_STORED_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_STORED c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) := by
  obtain ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds, _, _⟩ :=
    inflate_STORED_boundary_frame E good pending buffers mode incoming
  exact ⟨outcome, regs, after, stream, state, used, made, bound, run, current, tables,
    nextPending, packet, sizes, frame, next, count, put, left, bits, kinds⟩

/-- The actual switch selects the stored-block mode. -/
theorem inflate_dispatch_STORED {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = STORED) :
    runX (inflate_dispatch c) l h = runX (inflate_STORED c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY]

/-- The actual switch selects the stored-block mode. -/
theorem inflate_dispatch_COPY_start {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = COPY_) :
    runX (inflate_dispatch c) l h = runX (inflate_COPY_ c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY]

/-- The actual switch selects the stored-block mode. -/
theorem inflate_dispatch_COPY {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = COPY) :
    runX (inflate_dispatch c) l h = runX (inflate_COPY c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY]

/-- All three stored-block modes compose through the actual dispatch switch. -/
theorem inflate_dispatch_stored_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) (incoming : l.bits.toNat ≤ 39) :
    ∃ (outcome : Except Ex Unit) (regs : IL) (after : Heap) (stream : ZStream)
      (state : InflateState) (used made : Nat), used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧ DecodeStateFrame s state ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.bits.toNat ≤ 39 ∧ (outcome = .ok () ∨ outcome = .error Ex.leave) ∧ after.static = h.static ∧ Shape h after := by
  rcases mode with stored | start | copy
  · rw [inflate_dispatch_STORED E l stored]
    exact inflate_STORED_boundary_frame E good pending buffers stored incoming
  · obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, bits, _, exits, static, shape⟩ :=
      inflate_COPY_start_boundary_frame E good pending buffers start
    have kinds : outcome = .ok () ∨ outcome = .error Ex.leave := by
      rcases exits with wait | done | copied
      · exact Or.inr wait.1
      · exact Or.inl done.1
      · exact Or.inl copied.1
    exact ⟨outcome, regs, after, z, state, made, made, bound,
      (inflate_dispatch_COPY_start E l start).trans run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, by rw [bits]; exact incoming, kinds, static, shape⟩
  · obtain ⟨outcome, regs, after, state, made, bound, run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, bits, _, exits, static, shape⟩ :=
      inflate_COPY_boundary_frame E good pending buffers copy
    have kinds : outcome = .ok () ∨ outcome = .error Ex.leave := by
      rcases exits with wait | done | copied
      · exact Or.inr wait.1
      · exact Or.inl done.1
      · exact Or.inl copied.1
    exact ⟨outcome, regs, after, z, state, made, made, bound,
      (inflate_dispatch_COPY E l copy).trans run, current, tables, nextPending,
      packet, sizes, frame, next, count, put, left, by rw [bits]; exact incoming, kinds, static, shape⟩

end Zlib.Inflate.Proofs
