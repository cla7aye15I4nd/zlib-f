import ZlibF.Proof.«inflate.c.origin-fields-memory-contract»
import ZlibF.Proof.«inflate.c.dictionary-install-origin»
import ZlibF.Proof.«inflate.c.default-readonly-controls»
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

/-- Facts of the heap after Reset2's optional window free, before its record writes. -/
theorem reset2Heap_fields (h : Heap) (wb : Int32) (s : InflateState) :
    (reset2Heap h wb s).static = h.static ∧ (reset2Heap h wb s).allocOk = h.allocOk ∧
    (reset2Heap h wb s).garbage = h.garbage ∧ (reset2Heap h wb s).nextBlk = h.nextBlk ∧
    (reset2Heap h wb s).nalloc = h.nalloc ∧ (reset2Heap h wb s).streams = h.streams ∧
    (reset2Heap h wb s).istates = h.istates ∧ (reset2Heap h wb s).words = h.words ∧
    (reset2Heap h wb s).gzheaders = h.gzheaders ∧ (reset2Heap h wb s).dstates = h.dstates ∧
    (reset2Heap h wb s).gzstates = h.gzstates ∧ (reset2Heap h wb s).ro = h.ro ∧
    ∀ b, ¬ WinBlk s b → (reset2Heap h wb s).bytes b = h.bytes b := by
  unfold reset2Heap
  split
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (unfold freeWin; split <;> rfl)
    intro b other
    unfold freeWin
    split
    · rename_i w same
      have different : b ≠ w := by
        intro equal
        subst equal
        exact other same
      exact upd_ne _ _ _ _ different
    · rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Reset2 may free the current window. Its exact public memory and
ownership clauses follow from the actual heap and the freed-window
ownership fact of the translated call. -/
theorem reset2_public_resources {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {wb : Int32}
    (before : Good h r zs z s) (current : Good after r zs stream state)
    (heap : after = setI (r.put (reset2Heap h wb s) stream) zs state)
    (owns : ∀ S, h.Owns S → after.Owns (fun b => S b ∧ ¬ (s.wbits ≠ i2u wb ∧ WinBlk s b)))
    (window : state.window = if s.wbits ≠ i2u wb then .null else s.window)
    (call : Call) (regions : StreamWriteRegions h r call = []) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
      (StreamWriteRegions h r call) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨static, allocOk, garbage, nextBlk, nalloc, streams, istates, words, gzheaders,
    dstates, gzstates, ro, bytes⟩ := reset2Heap_fields h wb s
  have hzH : r.get (reset2Heap h wb s) = some z := by
    cases r <;> simp only [ZStreamRef.get, streams, gzstates] <;> exact before.live.hz
  have hsH : (reset2Heap h wb s).istates zs = some s := by rw [istates]; exact before.live.hs
  have record : RecordFrame r (some (.tab zs)) (reset2Heap h wb s) after := by
    rw [heap]
    exact RecordFrame.stream_state hzH hsH stream state
  have liveAll := owns h.live (fun _ => Iff.rfl)
  have disjoint : ∀ b, WinBlk s b → b ≠ zs := by
    intro b win same
    subst same
    rcases before.inv.win.block with null | ⟨w, a, pointer, get, _, _⟩
    · rw [win] at null
      cases null
    · rw [win] at pointer
      cases pointer
      have unique := before.uniq b
      simp only [get, before.live.hs, cnt_some] at unique
      omega
  have key : ∀ b, (s.wbits ≠ i2u wb ∧ WinBlk s b) ↔
      (StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
    intro b
    rw [before.streamOwned_iff, current.streamOwned_iff]
    unfold InflateOwned
    by_cases changes : s.wbits ≠ i2u wb
    · rw [if_pos changes] at window
      rw [window]
      constructor
      · rintro ⟨_, win⟩
        refine ⟨Or.inr win, ?_⟩
        rintro (same | absurdNull)
        · exact disjoint b win same
        · cases absurdNull
      · rintro ⟨owner, notAfter⟩
        refine ⟨changes, ?_⟩
        rcases owner with same | win
        · exact False.elim (notAfter (Or.inl same))
        · exact win
    · rw [if_neg changes] at window
      rw [window]
      constructor
      · rintro ⟨different, _⟩
        exact False.elim (changes different)
      · rintro ⟨owner, notAfter⟩
        exact False.elim (notAfter owner)
  have ownedAfter : ∀ b, StreamOwned after r b → StreamOwned h r b := by
    intro b owner
    rcases (current.streamOwned_iff b).mp owner with same | win
    · exact (before.streamOwned_iff b).mpr (Or.inl same)
    · by_cases changes : s.wbits ≠ i2u wb
      · rw [if_pos changes] at window
        rw [window] at win
        cases win
      · rw [if_neg changes] at window
        exact (before.streamOwned_iff b).mpr (Or.inr (window ▸ win))
  rw [regions]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change Frame h after _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact static.symm.trans record.1.1
    · exact allocOk.symm.trans record.1.2.1
    · exact garbage.symm.trans record.1.2.2.1
    · exact nextBlk ▸ record.1.2.2.2.1
    · exact nalloc ▸ record.1.2.2.2.2.1
    · intro b live unchanged
      have notRoot : ¬ StreamRoot r b := fun root => unchanged (Or.inl root)
      have notOwned : ¬ InflateOwned zs s b := fun owner =>
        unchanged (Or.inr (Or.inl ((before.streamOwned_iff b).mpr owner)))
      have notState : b ≠ zs := fun same => notOwned (Or.inl same)
      have notWindow : ¬ WinBlk s b := fun win => notOwned (Or.inr win)
      have liveH : (reset2Heap h wb s).live b := by
        unfold Heap.live at live ⊢
        rw [bytes b notWindow, words, streams, gzheaders, dstates, istates, gzstates]
        exact live
      have other : ¬ (StreamRoot r b ∨ DecoderRecordRoot (some (.tab zs)) b) := by
        rintro (root | same)
        · exact notRoot root
        · exact notState same
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := record.1.2.2.2.2.2 b liveH other
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact e1.trans (bytes b notWindow)
      · rw [e2, words]
      · rw [e3, streams]
      · rw [e4, gzheaders]
      · rw [e5, dstates]
      · rw [e6, istates]
      · rw [e7, gzstates]
      · rw [e8, ro]
  · intro region member
    cases member
  · intro b
    dsimp only
    rw [liveAll b]
    dsimp only
    rw [key b]
    have noCreate : ¬ (StreamOwned after r b ∧ ¬ h.live b) := fun ⟨owner, notLive⟩ =>
      notLive (good_inflate_owned_live before ((before.streamOwned_iff b).mp (ownedAfter b owner)))
    exact ⟨Or.inl, fun result => result.elim id (fun created => absurd created noCreate)⟩

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
      before.tableOrigin⟩
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
    have : s.wsize.toNat ≤ 32768 := by
      rcases good.inv.win.ws with zero | full
      · omega
      · rw [full]
        exact Nat.pow_le_pow_right (by decide) before.toDefaultDecodeJ.wbits_small
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
#print axioms inflatePrime_default_record_image
#print axioms inflatePrime_default_public_resources
#print axioms inflateValidate_default_public_resources
#print axioms inflateGetDictionary_default_public_contract
end Zlib.Inflate.Proofs
