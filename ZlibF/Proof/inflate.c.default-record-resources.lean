import ZlibF.Proof.«inflate.c.origin-history-calls»
import ZlibF.Spec.Public.Sequences
import ZlibF.Proof.«inflate.c.slow-output-exact-frame»
import ZlibF.Proof.«inflate.c.construction-record-read-tail»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An actual record-only update with the same owned window satisfies the
exact public memory and ownership clauses for any declared call regions. -/
theorem default_record_public_resources {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (before : Good h r zs z s)
    (current : Good after r zs stream state)
    (frame : RecordFrame r (some (.tab zs)) h after) (window : state.window = s.window)
    (call : Call) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
      (StreamWriteRegions h r call) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  have owned : ∀ b, StreamOwned after r b ↔ StreamOwned h r b := by
    intro b
    rw [current.streamOwned_iff, before.streamOwned_iff]
    simp only [InflateOwned, window]
  refine ⟨?_, ?_⟩
  · apply inflate_buffer_frame_mono (frame.buffer (StreamWriteRegions h r call))
    intro b changed
    rcases changed with root | stateRoot
    · exact Or.inl root
    · exact Or.inr (Or.inl ((before.streamOwned_iff b).mpr (Or.inl stateRoot)))
  · intro b
    have ownerLive : StreamOwned h r b → h.live b := fun owner =>
      good_inflate_owned_live before ((before.streamOwned_iff b).mp owner)
    dsimp only
    rw [owned, frame.2.2.1.live b]
    simp only [and_not_self, not_false_eq_true, and_true]
    constructor
    · exact Or.inl
    · rintro (old | ⟨owner, fresh⟩)
      · exact old
      · exact False.elim (fresh (ownerLive owner))

/-- Ordinary reset-keep has only its actual stream/state record writes. -/
theorem inflateResetKeep_default_public_resources
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (before : DefaultOriginState h r zs z s) (current : DefaultOriginState after r zs stream state)
    (run : C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after)) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflateResetKeep (some r)) b)
      (StreamWriteRegions h r (.inflateResetKeep (some r))) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨computed, actual, heap, next, _⟩ := inflateResetKeep_default_state before.toDefaultStateJ
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have sameState : state = resetKeepState zs s := Option.some.inj (current.good.live.hs.symm.trans next.good.live.hs)
  subst state
  rw [heap] at current ⊢
  exact default_record_public_resources before.good current.good
    (RecordFrame.stream_state before.good.live.hz before.good.live.hs _ _) rfl _

/-- The selected default reset has no window-width change and frees nothing. -/
theorem inflateReset_default_public_resources
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (current : DefaultOriginState after r zs stream state)
    (run : C.run (inflateReset (some r)) h = .ok (Z_OK, after)) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflateReset (some r)) b)
      (StreamWriteRegions h r (.inflateReset (some r))) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨computed, actual, heap, next, _⟩ := inflateReset_safe before.good allocator.2
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have sameState : state = resetKeepState zs (resetPre s) :=
    Option.some.inj (current.good.live.hs.symm.trans next.live.hs)
  subst state
  have bits : s.wbits = s.reqbits := before.window.trans before.requestedBits.symm
  have heapEq : resetHeap h s = h := by simp [resetHeap, bits]
  rw [heap, heapEq] at current ⊢
  exact default_record_public_resources before.good current.good
    (RecordFrame.stream_state before.good.live.hz before.good.live.hs _ _)
    (by simp [resetKeepState, resetPre, bits]) _

/-- Only the registered fifteen-bit Reset2 call is selected here. -/
theorem inflateReset2_15_default_public_resources
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (current : DefaultOriginState after r zs stream state)
    (run : C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after)) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflateReset2 (some r) 15) b)
      (StreamWriteRegions h r (.inflateReset2 (some r) 15)) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨code, computed, actual, result⟩ := inflateReset2_safe before.good allocator.2 15
  have params : reset2Params 15 = some (5, 15) := by decide
  rw [params] at result
  obtain ⟨rfl, heap, next, _⟩ := result
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have sameState : state = resetKeepState zs (resetPre (reset2Pre 5 15 s)) :=
    Option.some.inj (current.good.live.hs.symm.trans next.live.hs)
  subst state
  have bit15 : i2u (15 : Int32) = (15 : UInt32) := by decide
  have heapEq : reset2Heap h 15 s = h := by simp [reset2Heap, before.window, bit15]
  rw [heap, heapEq] at current ⊢
  exact default_record_public_resources before.good current.good
    (RecordFrame.stream_state before.good.live.hz before.good.live.hs _ _)
    (by simp [resetKeepState, resetPre, reset2Pre, before.window, bit15]) _

/-- All signed prime requests either leave the heap unchanged or write
only the existing state record, retaining its window field. -/
theorem inflatePrime_default_record_image
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {rc : Int32}
    (before : Good h r zs z s) (bits value : Int32)
    (run : C.run (inflatePrime (some r) bits value) h = .ok (rc, after)) :
    after = h ∨ ∃ state, after = setI h zs state ∧ state.window = s.window := by
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec before bits value
  by_cases equal : bits = 0
  · exact Or.inl (congrArg Prod.snd (Except.ok.inj ((zero equal).symm.trans run))).symm
  by_cases negative : bits < 0
  · exact Or.inr ⟨_, (congrArg Prod.snd (Except.ok.inj ((clear negative).1.symm.trans run))).symm, rfl⟩
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    simp only [Int32.toInt_zero] at negative ⊢
    have nonzero : bits.toInt ≠ 0 := fun zero => equal (Int32.toInt_inj.mp zero)
    omega
  by_cases wide : 16 < bits.toInt
  · exact Or.inl (congrArg Prod.snd (Except.ok.inj ((reject positive (Or.inl wide)).symm.trans run))).symm
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact Or.inl (congrArg Prod.snd (Except.ok.inj ((reject positive (Or.inr full)).symm.trans run))).symm
  · exact Or.inr ⟨_, (congrArg Prod.snd
      (Except.ok.inj ((insert positive (by omega) (by omega)).1.symm.trans run))).symm, rfl⟩

/-- Prime's exact memory clause is derived from the actual branch images. -/
theorem inflatePrime_default_public_resources
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState} {rc : Int32}
    (before : DefaultOriginState h r zs z s) (bits value : Int32)
    (current : DefaultOriginState after r zs z state)
    (run : C.run (inflatePrime (some r) bits value) h = .ok (rc, after)) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflatePrime (some r) bits value) b)
      (StreamWriteRegions h r (.inflatePrime (some r) bits value)) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  rcases inflatePrime_default_record_image before.good bits value run with same | ⟨state', heap, window⟩
  · subst after
    have sameState : state = s := Option.some.inj (current.good.live.hs.symm.trans before.good.live.hs)
    subst state
    exact default_record_public_resources before.good before.good (RecordFrame.refl _ _ _) rfl _
  · subst after
    have sameState : state = state' := Option.some.inj (current.good.live.hs.symm.trans (setI_istates_same _ _ _))
    subst state
    exact default_record_public_resources before.good current.good
      (RecordFrame.setI r zs before.good.live.hs state') window _

/-- Validation's actual state update retains every byte view and window. -/
theorem inflateValidate_default_public_resources
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    (before : DefaultOriginState h r zs z s) (check : Int32)
    (current : DefaultOriginState after r zs z state)
    (run : C.run (inflateValidate (some r) check) h = .ok (Z_OK, after)) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflateValidate (some r) check) b)
      (StreamWriteRegions h r (.inflateValidate (some r) check)) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨computed, state', actual, heap, stateEq, next⟩ :=
    inflateValidate_default_state before.toDefaultStateJ check
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have sameState : state = state' := Option.some.inj (current.good.live.hs.symm.trans next.good.live.hs)
  subst state
  rw [heap] at current ⊢
  exact default_record_public_resources before.good current.good
    (RecordFrame.setI r zs before.good.live.hs state') (by rw [stateEq]; rfl) _

/-- The real getter copies its chronological window bytes into the caller's
admitted range and satisfies the exact public frame and ownership ledger. -/
theorem inflateGetDictionary_default_public_contract
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (before : DefaultOriginState h r zs z s) (dest : BPtr) (dl : Option UInt32)
    (range : CallerRange h r dest s.whave.toNat true) :
    ∃ after, C.run (inflateGetDictionary (some r) dest dl) h =
      .ok ((Z_OK, dl.map (fun _ => s.whave)), after) ∧
      DefaultOriginState after r zs z s ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
          StreamHeaderRecord h r (.inflateGetDictionary (some r) dest dl) b)
        (StreamWriteRegions h r (.inflateGetDictionary (some r) dest dl)) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  have good := before.good
  by_cases empty : dest = .null ∨ s.whave = 0
  · have actual : C.run (inflateGetDictionary (some r) dest dl) h =
        .ok ((Z_OK, dl.map (fun _ => s.whave)), h) := by
      unfold C.run inflateGetDictionary
      rcases empty with null | zero
      · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
          good.live.hz, good.live.zst, castI, good.live.hs, null]
      · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
          good.live.hz, good.live.zst, castI, good.live.hs, zero]
    have resources := default_record_public_resources good good
      (RecordFrame.refl r (some (.tab zs)) h) rfl (.inflateGetDictionary (some r) dest dl)
    exact ⟨h, actual, before, resources⟩
  have nonnull : dest ≠ .null := fun null => empty (Or.inl null)
  have positive : s.whave ≠ 0 := fun zero => empty (Or.inr zero)
  have positiveNat : 0 < s.whave.toNat := by
    have : s.whave.toNat ≠ 0 := fun zero => positive (UInt32.toNat_inj.mp (by simpa using zero))
    omega
  obtain ⟨w, a, window, bytes, _write, size⟩ :
      ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
        h.ro w = false ∧ a.size = 2 ^ s.wbits.toNat := by
    rcases good.inv.win.block with null | block
    · have := good.inv.win.nullws null
      have := good.inv.win.hv
      simp_all
    · exact block
  have windowSize : s.wsize.toNat = a.size := by
    rcases good.inv.win.ws with zero | full
    · have := good.inv.win.hv
      omega
    · omega
  have bounded : s.whave.toNat ≤ a.size := by
    have := good.inv.win.hv
    omega
  have chronological : s.wnext.toNat ≤ s.whave.toNat := by
    rcases Nat.lt_or_ge s.whave.toNat s.wsize.toNat with growing | full
    · have := good.inv.win.eq growing
      omega
    · have := good.inv.win.wn
      have := good.inv.win.hv
      omega
  have writable : Writable h dest s.whave.toNat := by
    rcases range with null | ⟨_read, write⟩
    · exact False.elim (nonnull null)
    · exact write.1 rfl
  rcases writable with ⟨null, _⟩ | ⟨ref, off, old, pointer, get, write, room⟩
  · exact False.elim (nonnull null)
  have separate := callerRange_private_window good range pointer
  have actual := inflateGetDictionary_copy_general (dl := dl) good.live window bytes get write
    (separate w window) positive chronological bounded room
  let replacement := getDictBytes old a off s.wnext.toNat s.whave.toNat
  have size : replacement.size = old.size := by simp [replacement, getDictBytes, size_copyRange]
  have current : DefaultOriginState (Space.put h ref replacement) r zs z s :=
    ⟨before.toDefaultStateJ.byte_view_put get write separate replacement size,
      before.flagsOrigin, before.tableOrigin⟩
  have outside : ∀ j, j < off ∨ off + s.whave.toNat ≤ j → replacement[j]? = old[j]? := by
    intro j outside
    have firstFit : off + (s.whave.toNat - s.wnext.toNat) ≤ old.size := by omega
    have secondFit : off + s.whave.toNat - s.wnext.toNat + s.wnext.toNat ≤
        (copyRange old a off s.wnext.toNat (s.whave.toNat - s.wnext.toNat)).size := by
      rw [size_copyRange]
      omega
    dsimp only [replacement]
    unfold getDictBytes
    rw [Zlib.Deflate.Engine.Proofs.getElem?_copyRange _ _ _ _ _ _ secondFit,
      Zlib.Deflate.Engine.Proofs.getElem?_copyRange _ _ _ _ _ _ firstFit]
    have firstOutside : ¬ (off ≤ j ∧ j < off + (s.whave.toNat - s.wnext.toNat)) := by omega
    have secondOutside : ¬ (off + s.whave.toNat - s.wnext.toNat ≤ j ∧
        j < off + s.whave.toNat - s.wnext.toNat + s.wnext.toNat) := by omega
    simp only [firstOutside, secondOutside, ↓reduceIte]
  have narrow := byte_view_segment_buffer_frame get write size outside
  have publicBound : s.whave.toNat ≤ 32768 := by
    have := good.inv.win.hv
    have : s.wsize.toNat = 0 ∨ s.wsize.toNat = 32768 := by
      rcases good.inv.win.ws with zero | full
      · exact Or.inl zero
      · exact Or.inr (by rw [full, before.window]; decide)
    omega
  have broad := BufferFrame.singleton_widen narrow (Nat.le_refl off)
    (by omega : off + s.whave.toNat ≤ off + 32768)
  have frame : BufferFrame h (Space.put h ref replacement)
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
        StreamHeaderRecord h r (.inflateGetDictionary (some r) dest dl) b)
      (StreamWriteRegions h r (.inflateGetDictionary (some r) dest dl)) := by
    rw [StreamWriteRegions, pointer]
    exact inflate_buffer_frame_mono broad (fun _ impossible => False.elim impossible)
  have shape := byte_view_put_shape get write replacement
  have owned : ∀ b, StreamOwned (Space.put h ref replacement) r b ↔ StreamOwned h r b := by
    intro b
    rw [current.good.streamOwned_iff, good.streamOwned_iff]
  have ledger : LiveChange h (Space.put h ref replacement)
      (fun b => StreamOwned (Space.put h ref replacement) r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned (Space.put h ref replacement) r b) := by
    intro b
    have ownerLive : StreamOwned h r b → h.live b := fun owner =>
      good_inflate_owned_live good ((good.streamOwned_iff b).mp owner)
    dsimp only
    rw [owned, shape.live b]
    simp only [and_not_self, not_false_eq_true, and_true]
    constructor
    · exact Or.inl
    · rintro (old | ⟨owner, fresh⟩)
      · exact old
      · exact False.elim (fresh (ownerLive owner))
  refine ⟨Space.put h ref replacement, ?_, current, frame, ledger⟩
  simpa only [C.run, pointer] using actual

#print axioms default_record_public_resources
#print axioms inflateResetKeep_default_public_resources
#print axioms inflateReset_default_public_resources
#print axioms inflateReset2_15_default_public_resources
#print axioms inflatePrime_default_record_image
#print axioms inflatePrime_default_public_resources
#print axioms inflateValidate_default_public_resources
#print axioms inflateGetDictionary_default_public_contract
end Zlib.Inflate.Proofs
