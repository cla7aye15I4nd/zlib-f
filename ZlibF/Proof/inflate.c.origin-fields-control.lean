import ZlibF.Proof.«inflate.c.origin-fields-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The real block selector either keeps both pointers or installs the
paired fixed tables. Its source writes retain the header flag. -/
theorem typedoTail_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s)
    (actual : runX (typedoTail c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
  have observe {heap : Heap} {state : InflateState} {exit : Except Ex Unit} {result : IL}
      (source : runX (typedoTail c) l h = .ok ((exit, result), heap))
      (get : heap.istates zs = some state) (flags : state.flags = s.flags)
      (pointers : BlockHeaderPointers s state) :
      ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
    have same : after = heap := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨state, by rw [same]; exact get, flags, pointers⟩
  have bound : l.hold.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have cases : l.hold.toNat % 4 = 0 ∨ l.hold.toNat % 4 = 1 ∨
      l.hold.toNat % 4 = 2 ∨ l.hold.toNat % 4 = 3 := by omega
  rcases cases with stored | fixed | dynamic | bad
  · exact observe (typedoTail_stored E l stored) (setI_istates_same ..) rfl (Or.inl ⟨rfl, rfl⟩)
  · by_cases trees : c.flush = Z_TREES
    · exact observe (typedoTail_fixed_trees E l fixed trees) (setI_istates_same ..) rfl (Or.inr ⟨rfl, rfl⟩)
    · exact observe (typedoTail_fixed E l fixed trees) (setI_istates_same ..) rfl (Or.inr ⟨rfl, rfl⟩)
  · exact observe (typedoTail_table E l dynamic) (setI_istates_same ..) rfl (Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨index, _message, source⟩ := typedoTail_bad E l bad
    exact observe (state := { s with mode := BAD }) source (by simp [badHeap]) rfl (Or.inl ⟨rfl, rfl⟩)

/-- The complete source block-header path has the same origin alternatives
on input exhaustion, all four block types and the final-block boundary. -/
theorem inflate_TYPEDO_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (buffers : DispatchBuffers h r l bs)
    (actual : runX (inflate_TYPEDO c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
  by_cases last : s.last = 0
  · obtain ⟨decision, current, _used, pull, _usedBound, _bitInv, _, _, _, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor buffers.bits 3 (by decide)
    rcases kinds with normal | wait
    · rw [normal] at pull
      let middle := { s with last := u2i (current.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) }
      let first := { current with hold := current.hold >>> (1 : UInt32).toUInt64, bits := current.bits - 1 }
      have nextEnv : Env c (setI h zs middle) r zs z middle :=
        ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using E.hz, setI_istates_same ..⟩
      rw [inflate_TYPEDO_head E l current last pull] at actual
      obtain ⟨state, get, flags, pointers⟩ := typedoTail_origin_record (l := first) nextEnv actual
      exact ⟨state, get, flags, pointers⟩
    · have source := inflate_TYPEDO_wait E l current last Ex.leave (by rwa [wait] at pull)
      have same : after = h := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
      exact ⟨s, by rw [same]; exact E.hs, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have source := inflate_TYPEDO_last E l last
    have same : after = setI h zs { s with mode := CHECK } :=
      congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨{ s with mode := CHECK }, by rw [same]; exact setI_istates_same ..,
      rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- TYPE's documented early returns retain the old pointer origins; its
remaining source is the already observed complete block-header path. -/
theorem inflate_TYPE_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (buffers : DispatchBuffers h r l bs)
    (actual : runX (inflate_TYPE c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
  by_cases stop : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
  · have source := inflate_TYPE_leave c l h stop
    have same : after = h := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    exact ⟨s, by rw [same]; exact E.hs, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have proceed : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
      ⟨fun equal => stop (Or.inl equal), fun equal => stop (Or.inr equal)⟩
    rw [inflate_TYPE_go c l h proceed] at actual
    exact inflate_TYPEDO_origin_record E buffers actual

/-- The real dispatcher preserves origins in both block-header modes. -/
theorem inflate_dispatch_type_origin_record {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (buffers : DispatchBuffers h r l bs)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO)
    (actual : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    ∃ state, after.istates zs = some state ∧ state.flags = s.flags ∧ BlockHeaderPointers s state := by
  rw [inflate_dispatch_block_type E l mode] at actual
  by_cases type : s.mode = TYPE
  · rw [if_pos type] at actual
    exact inflate_TYPE_origin_record E buffers actual
  · rw [if_neg type] at actual
    exact inflate_TYPEDO_origin_record E buffers actual

/-- Actual block-header origin alternatives upgrade the matching real J
result. Neither table safety nor a callee contract is supplied as a new
public premise. -/
theorem DefaultOriginState.of_pointer_alternatives {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : DefaultOriginState h r zs z s)
    (current : DefaultStateJ after r zs stream state) (flags : state.flags = s.flags)
    (pointers : BlockHeaderPointers s state) : DefaultOriginState after r zs stream state := by
  rcases pointers with retained | fixed
  · exact before.of_fields current flags retained.1 retained.2
  · exact ⟨current, before.flagsOrigin.of_flags flags, Or.inr fixed⟩

#print axioms typedoTail_origin_record
#print axioms inflate_dispatch_type_origin_record
end Zlib.Inflate.Proofs
