import ZlibF.Proof.«inflate.c.fast-view-exact-frame-bridge»
import ZlibF.Proof.«inflate.c.fast-view-full-view-frame»
import ZlibF.Proof.«inflate.c.literal-step»
import ZlibF.Proof.«inflate.c.match-output»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A concrete byte-view replacement with unchanged extent and unchanged
cells outside one interval has precisely that public output frame. -/
theorem byte_view_segment_buffer_frame
    {h : Heap} {dest : BRef} {old array : Array UInt8} {off made : Nat}
    (get : Space.get h dest = some old) (write : Space.ro h dest = false)
    (size : array.size = old.size)
    (outside : ∀ j, j < off ∨ off + made ≤ j → array[j]? = old[j]?) :
    BufferFrame h (Space.put h dest array) (fun _ => False) [⟨.ref dest off, made⟩] := by
  have broad := byte_view_full_buffer_frame get write size
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil] using broad.1
  · intro region member ref index before pointer beforeGet
    have same : region = ⟨.ref dest off, made⟩ := by simpa only [List.mem_singleton] using member
    subst region
    cases pointer
    have sameArray : before = old := Option.some.inj (beforeGet.symm.trans get)
    subst before
    refine ⟨array, byte_view_get_put get write array, size, ?_⟩
    intro j bound untouched
    apply outside
    by_cases lower : j < off
    · exact Or.inl lower
    · by_cases upper : off + made ≤ j
      · exact Or.inr upper
      · exact False.elim (untouched ⟨⟨.ref dest off, made⟩, by simp,
          off, rfl, by change off ≤ j; omega, by change j < off + made; omega⟩)

/-- A slow output write followed by the actual private-state store changes
only the produced output interval and the stream's private record. -/
theorem output_state_segment_buffer_frame
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {dest : BRef} {old array : Array UInt8} {off made : Nat}
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (get : Space.get h dest = some old) (write : Space.ro h dest = false)
    (size : array.size = old.size) (state : InflateState)
    (outside : ∀ j, j < off ∨ off + made ≤ j → array[j]? = old[j]?) :
    BufferFrame h (setI (Space.put h dest array) zs state)
      (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
  have first := bufferFrame_weaken (wider := fun b => StreamRoot r b ∨ b = zs)
    (fun _ impossible => False.elim impossible) (byte_view_segment_buffer_frame get write size outside)
  have hz1 : r.get (Space.put h dest array) = some z := by rw [byte_view_put_stream]; exact hz
  have hs1 : (Space.put h dest array).istates zs = some s := by rw [byte_view_put_istates]; exact hs
  have second := (fastWriteback_heap_frame hz1 hs1 z state [⟨.ref dest off, made⟩]).1
  rw [ZStreamRef.put_self hz1] at second
  exact BufferFrame.singleton_trans first second (byte_view_put_shape get write array) get
    (by rw [byte_view_ro_write]; exact write)
    (by rw [byte_view_ro_setI, byte_view_ro_write]; exact write)

/-- Every actual slow literal emits one byte or leaves because output is
full. Both paths have an exact frame using their actual produced count. -/
theorem inflate_LIT_exact_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) :
    ∃ outcome regs after state made,
      runX (inflate_LIT c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs z state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  by_cases empty : l.left = 0
  · obtain ⟨dest, array, off, put, get, write, _⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    exact ⟨.error Ex.leave, l, h, s, 0, inflate_LIT_full c l h empty, good, by omega,
      (inputAdvance_zero l.put).symm, by rw [put]; exact BufferFrame.singleton_refl get write⟩
  · obtain ⟨dest, array, off, put, get, write, room, _, _, unowned⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    have positive : 0 < l.left.toNat := by
      have nonzero : l.left.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
      omega
    let state := { s with mode := LEN }
    let after := setI (Space.put h dest (array.set! off s.length.toUInt8)) zs state
    have frame : BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, 1⟩] := by
      rw [put]
      apply output_state_segment_buffer_frame E.hz E.hs get write (by simp) state
      intro j outside
      have ne : off ≠ j := by omega
      simp [Array.set!, ne]
    have nextGood : Good after r zs z state :=
      (good.byte_view_put get write unowned _).decode_update (by rfl)
        (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
    refine ⟨.ok (), { l with put := .ref dest (off + 1), left := l.left - 1 },
      after, state, 1, inflate_LIT_view_run E empty put get write (by omega), nextGood, ?_, ?_, frame⟩
    · change (l.left - 1).toNat + 1 = l.left.toNat
      rw [UInt32.toNat_sub_of_le _ _ (by exact positive)]
      have one : (1 : UInt32).toNat = 1 := rfl
      rw [one]
      omega
    · change Ptr.ref dest (off + 1) = inputAdvance l.put 1
      rw [put]
      rfl

/-- The actual forward-copy array preserves every optional cell outside
its destination interval, including overlapping growing-output reads. -/
theorem slow_match_copy_outside (same : Bool) (saved : Array UInt8) :
    ∀ count sourceOff dest output j, j < dest ∨ dest + count ≤ j →
      (ZlibF.Math.InflateMatchCopy.copy same saved count sourceOff dest output)[j]? = output[j]?
  | 0, _, _, _, _, _ => rfl
  | count + 1, sourceOff, dest, output, j, outside => by
      rw [ZlibF.Math.InflateMatchCopy.copy_succ,
        slow_match_copy_outside same saved count (sourceOff + 1) (dest + 1) _ j (by omega)]
      have different : dest ≠ j := by omega
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]

/-- The complete actual slow MATCH writes precisely its produced output
prefix. Exhaustion and invalid-distance returns write no output bytes. -/
theorem inflate_MATCH_exact_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = MATCH) (length : 0 < s.length.toNat) (offset : 0 < s.offset.toNat)
    (sane : s.sane ≠ 0) :
    ∃ outcome regs after stream state made,
      runX (inflate_MATCH c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨dest, array, off, put, get, write, room, count, produced, privateWindow⟩ :=
    callerRange_slow_output good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  by_cases empty : l.left = 0
  · refine ⟨.error Ex.leave, l, h, z, s, 0, inflate_MATCH_wait c h l empty, good,
      by omega, (inputAdvance_zero l.put).symm, ?_⟩
    rw [put]
    exact BufferFrame.singleton_refl get write
  · obtain ⟨outcome, regs, after, stream, state, run, current, _, _, _, kinds⟩ :=
      inflate_MATCH_boundary_ranges E good tables buffers.bits put get write mode length offset sane
        room count produced privateWindow (buffers.bits.output_positions put empty buffers.separate)
    rcases kinds with ⟨wait, regsEq, heapEq, stateEq⟩ | ⟨ok, bad, regsEq, i, msg, heapEq⟩ |
      ⟨ok, copy, source, sourceOff, saved, positive, copyLeft, copyLength, regsEq,
        heapEq, stateEq, lengthEq, modes, decreases⟩
    · subst outcome regs after state
      refine ⟨.error Ex.leave, l, h, stream, s, 0, run, current,
        by omega, (inputAdvance_zero l.put).symm, ?_⟩
      rw [put]
      exact BufferFrame.singleton_refl get write
    · subst outcome regs
      refine ⟨.ok (), l, after, stream, state, 0, run, current,
        by omega, (inputAdvance_zero l.put).symm, ?_⟩
      rw [heapEq]
      exact (badHeap_buffer_frame E.hz E.hs i [⟨l.put, 0⟩]).1
    · subst outcome
      refine ⟨.ok (), regs, after, stream, state, copy.toNat, run, current, ?_, ?_, ?_⟩
      · rw [regsEq]
        change (l.left - copy).toNat + copy.toNat = l.left.toNat
        rw [UInt32.toNat_sub_of_le _ _ copyLeft]
        omega
      · rw [regsEq]
        change Ptr.ref dest (off + copy.toNat) = inputAdvance l.put copy.toNat
        rw [put]
        rfl
      · rw [heapEq, put]
        exact output_state_segment_buffer_frame E.hz E.hs get write
          (ZlibF.Math.InflateMatchCopy.copy_size ..) state (slow_match_copy_outside (decide (source = dest)) saved copy.toNat sourceOff off array)

#print axioms inflate_LIT_exact_frame
#print axioms inflate_MATCH_exact_frame
end Zlib.Inflate.Proofs
