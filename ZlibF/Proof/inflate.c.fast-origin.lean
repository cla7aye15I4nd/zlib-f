import ZlibF.Proof.«inflate.c.fast-progress»
import ZlibF.Proof.«inffast.c.progress-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual fast LEN branch obeys the source-bit budget after
rollback and LOAD. This includes TYPE/BAD exits where output need not grow.
The existing distinct-raw-buffer entry scope is explicit. -/
theorem inflate_LEN_fast_raw_bit_budget_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after, runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * (l.have_.toNat - regs.have_.toNat) := by
  obtain ⟨entry, heapEq, strmEq, startEq, refEq, idEq, streamEq, stateEq, _, _, _, _⟩ :=
    inflate_fast_raw_entry E good fit tables buffers pending input output different fast
  obtain ⟨heap1, call, _, _, origin⟩ := Zlib.Inffast.Proofs.inflate_fast_safe_progress_origin entry.toEnv
  change C.run (Zlib.Inffast.inflate_fast entry.strm entry.start) entry.h0 = .ok ((), heap1) at call
  have execution : Zlib.Inffast.inflate_fast c.strm l.out_
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) = .ok ((), heap1) := by
    simpa only [C.run, heapEq, strmEq, startEq] using call
  have cut : runX (inflate_LEN c) l h = runX (inflateAfterFast c) l heap1 := by
    unfold inflate_LEN
    rw [runX_bind, runX_get]
    simp only [fast, ↓reduceIte]
    rw [runX_bind, RESTORE_pending_run E]
    simp only []
    rw [runX_bind, runX_lift_ok execution]
    rfl
  obtain ⟨state1, stream1, input1, used, stateGet, streamGet, ptr, count, inv⟩ := origin
  have origin' : Zlib.Inffast.Spec.CallOrigin.HasOrigin entry.toEnv heap1 :=
    ⟨state1, stream1, input1, used, stateGet, streamGet, ptr, count, inv⟩
  have budget := origin'.bit_budget stateGet streamGet
  change state1.bits.toNat ≤ entry.s0.bits.toNat + 8 * (entry.sm0.avail_in.toNat - stream1.avail_in.toNat) at budget
  rw [stateEq, streamEq] at budget
  change state1.bits.toNat ≤ l.bits.toNat + 8 * (l.have_.toNat - stream1.avail_in.toNat) at budget
  change heap1.istates entry.stid = some state1 at stateGet
  change entry.r.get heap1 = some stream1 at streamGet
  rw [idEq] at stateGet
  rw [refEq] at streamGet
  have E1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, streamGet, stateGet⟩
  rw [cut, inflateAfterFast_run E1]
  exact ⟨_, _, rfl, budget⟩

/-- The same actual fast mode retains the common packet, output progress and source-bit budget together. -/
theorem inflate_LEN_fast_raw_buffers_budget_progress {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ used made regs after stream state, used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat < 8 ∧ (state.mode = TYPE ∨ state.mode = BAD ∨ 0 < made) ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨used, made, regs, after, stream, state, bound, run, current, data, nextPending,
    packet, sizes, next, haveCount, put, left, bits, progress⟩ :=
    inflate_LEN_fast_raw_buffers_progress E good fit tables buffers pending input output different fast
  obtain ⟨regs2, after2, budgetRun, budget⟩ :=
    inflate_LEN_fast_raw_bit_budget_run E good fit tables buffers pending input output different fast
  obtain ⟨localEq, heapEq⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans budgetRun))
  have regsEq : regs2 = regs := (congrArg Prod.snd localEq).symm
  subst regs2
  subst after2
  have usedCount : l.have_.toNat - regs.have_.toNat = used := by omega
  rw [usedCount] at budget
  exact ⟨used, made, regs, after, stream, state, bound, run, current, data, nextPending,
    packet, sizes, next, haveCount, put, left, bits, progress, budget⟩

/-- LEN_ normalization retains the common fast budget and progress result. -/
theorem inflate_LEN_start_fast_raw_buffers_budget_progress {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ used made regs after stream state, used ≤ bs.length ∧
      runX (inflate_LEN_ c) l h = .ok ((.ok (), regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat < 8 ∧ (state.mode = TYPE ∨ state.mode = BAD ∨ 0 < made) ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  let state0 := { s with mode := LEN }
  let heap0 := setI h zs state0
  have good0 : Good heap0 r zs z state0 := good.decode_update (by rfl)
    (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have env0 : Env c heap0 r zs z state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have tables0 : DataTablesSafe heap0 state0 := tables.decode_update good.live.hs (by rfl)
  have pending0 : DataPendingInvariant state0 := by
    apply dataPendingInvariant_idle (s := state0) pending.sane
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have packet0 := buffers.byte_views good good0 rfl (fun ref => byte_view_get_setI h zs state0 ref)
    (fun ref => byte_view_ro_setI h zs state0 ref)
  have sizes0 := byte_view_sizes_setI h zs state0
  have fit0 := sizes0.platform fit
  obtain ⟨used, made, regs, after, stream, state, usedBound, run, nextGood, nextTables,
    nextPending, nextPacket, sizes, next, haveCount, put, left, bitCount, progress, budget⟩ :=
    inflate_LEN_fast_raw_buffers_budget_progress env0 good0 fit0 tables0 packet0 pending0 input output different fast
  refine ⟨used, made, regs, after, stream, state, usedBound, ?_, nextGood, nextTables,
    nextPending, nextPacket, sizes0.trans sizes, next, haveCount, put, left, bitCount, progress, budget⟩
  unfold inflate_LEN_
  rw [runX_bind, runX_setMode E]
  exact run

end Zlib.Inflate.Proofs
