import ZlibF.Proof.«inflate.c.copy-invariant»
import ZlibF.Spec.Public.Sequences
import ZlibF.Proof.«inflate.c.default-record-resources»
import ZlibF.Proof.«inflate.c.default-setdict-resources»
import ZlibF.Proof.«inflate.c.default-history-public-contract»

/-!
# inflate.c: frames and ledgers of the stream operations

The safety part of `Goal.inflate_sequence` for one call: from the general
invariant, the call returns, writes only the stream's records, its own
memory and the caller regions it is given, and changes the allocation
ledger exactly by the stream's own window.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One stream operation returns with an exact frame and ledger. -/
def InflateCallSafe (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h : Heap) (i : Nat) (z : ZStream) (s : InflateState),
    InflateInv h r i z s → StreamArguments h r call →
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b)

theorem inflateSyncPoint_call_safe (r : ZStreamRef) :
    InflateCallSafe r (.inflateSyncPoint (some r)) := by
  intro h i z s current _
  have run := inflateSyncPoint_spec current.good.live
  exact ⟨_, h, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateMark_call_safe (r : ZStreamRef) : InflateCallSafe r (.inflateMark (some r)) := by
  intro h i z s current _
  obtain ⟨value, run, _⟩ := inflateMark_spec current.good.live
  exact ⟨value, h, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateCodesUsed_call_safe (r : ZStreamRef) :
    InflateCallSafe r (.inflateCodesUsed (some r)) := by
  intro h i z s current _
  obtain ⟨offset, _, _, run⟩ := inflateCodesUsed_spec current.good
  exact ⟨_, h, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateUndermine_call_safe (r : ZStreamRef) (subvert : Int32) :
    InflateCallSafe r (.inflateUndermine (some r) subvert) := by
  intro h i z s current _
  obtain ⟨written, run, heap, _⟩ := inflateUndermine_safe current.good subvert
  have state : { s with sane := 1 } = s := by rw [← current.pending.sane]
  have unchanged : written = h := by rw [heap, state, tcSetI_same current.good.live.hs]
  subst unchanged
  exact ⟨_, written, heapCall_of_actual_run run default,
    default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩

theorem inflateValidate_call_safe (r : ZStreamRef) (check : Int32) :
    InflateCallSafe r (.inflateValidate (some r) check) := by
  intro h i z s current _
  obtain ⟨written, run, heap, good, _⟩ := inflateValidate_safe current.good check
  subst heap
  exact ⟨_, _, heapCall_of_actual_run run default,
    default_record_public_resources current.good good
      (RecordFrame.setI r i current.good.live.hs _) rfl _⟩

theorem inflatePrime_call_safe (r : ZStreamRef) (bits word : Int32) :
    InflateCallSafe r (.inflatePrime (some r) bits word) := by
  intro h i z s current _
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec current.good bits word
  have unchanged : ∀ {rc : Int32}, C.run (inflatePrime (some r) bits word) h = .ok (rc, h) →
      ∃ result after, (Call.inflatePrime (some r) bits word).execute default h =
          .ok ((result, default), after) ∧
        BufferFrame h after
          (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
            StreamHeaderRecord h r (.inflatePrime (some r) bits word) b)
          (StreamWriteRegions h r (.inflatePrime (some r) bits word)) ∧
        LiveChange h after
          (fun b => StreamOwned after r b ∧ ¬ h.live b)
          (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
    intro rc run
    exact ⟨rc, h, heapCall_of_actual_run run default,
      default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩
  by_cases equal : bits = 0
  · exact unchanged (zero equal)
  by_cases negative : bits < 0
  · obtain ⟨run, good⟩ := clear negative
    exact ⟨_, _, heapCall_of_actual_run run default,
      default_record_public_resources current.good good
        (RecordFrame.setI r i current.good.live.hs _) rfl _⟩
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    simp only [Int32.toInt_zero] at negative ⊢
    have nonzero : bits.toInt ≠ 0 := fun zero => equal (Int32.toInt_inj.mp zero)
    omega
  by_cases wide : 16 < bits.toInt
  · exact unchanged (reject positive (Or.inl wide))
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact unchanged (reject positive (Or.inr full))
  obtain ⟨run, good⟩ := insert positive (by omega) (by omega)
  exact ⟨_, _, heapCall_of_actual_run run default,
    default_record_public_resources current.good good
      (RecordFrame.setI r i current.good.live.hs _) rfl _⟩

theorem inflateResetKeep_call_safe (r : ZStreamRef) :
    InflateCallSafe r (.inflateResetKeep (some r)) := by
  intro h i z s current _
  obtain ⟨written, run, heap, good, _⟩ := inflateResetKeep_safe current.good
  subst heap
  exact ⟨_, _, heapCall_of_actual_run run default,
    default_record_public_resources current.good good
      (RecordFrame.stream_state current.good.live.hz current.good.live.hs _ _) rfl _⟩

theorem inflateReset2_call_safe (r : ZStreamRef) (wb : Int32) :
    InflateCallSafe r (.inflateReset2 (some r) wb) := by
  intro h i z s current _
  obtain ⟨code, written, run, result⟩ := inflateReset2_safe current.good current.alloc.2 wb
  cases params : reset2Params wb with
  | none =>
    rw [params] at result
    obtain ⟨_, same⟩ := result
    subst same
    exact ⟨code, written, heapCall_of_actual_run run default,
      default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩
  | some selected =>
    obtain ⟨wrap, width⟩ := selected
    rw [params] at result
    obtain ⟨_, heap, next, ownsFact⟩ := result
    refine ⟨code, written, heapCall_of_actual_run run default,
      reset2_public_resources current.good next heap ownsFact ?_ _ rfl⟩
    simp only [resetKeepState, resetPre, reset2Pre]
    by_cases changes : s.wbits ≠ i2u width
    · simp [changes]
    · simp only [ne_eq, Decidable.not_not] at changes
      simp [changes]

#print axioms inflatePrime_call_safe
#print axioms inflateReset2_call_safe

/-- `inflateReset` frees the window exactly when the width changes. -/
theorem inflateReset_call_safe (r : ZStreamRef) : InflateCallSafe r (.inflateReset (some r)) := by
  intro h i z s current _
  obtain ⟨written, run, heap, good, ownsFact⟩ := inflateReset_safe current.good current.alloc.2
  let wb : Int32 := Int32.ofNat s.reqbits.toNat
  have width : i2u wb = s.reqbits := by
    have key : ∀ k : Nat, k < 16 → i2u (Int32.ofNat k) = UInt32.ofNat k := by decide
    have bound := current.good.inv.reqbits
    rw [key _ (by omega)]
    exact UInt32.ofNat_toNat
  have heapSame : resetHeap h s = reset2Heap h wb s := by
    simp only [resetHeap, reset2Heap, width]
  have heap2 : written = setI (r.put (reset2Heap h wb s) (resetKeepStream z (resetPre s))) i
      (resetKeepState i (resetPre s)) := by
    rw [heap, heapSame]
  have owns2 : ∀ S, h.Owns S → written.Owns
      (fun b => S b ∧ ¬ (s.wbits ≠ i2u wb ∧ WinBlk s b)) := by
    rw [width]
    exact ownsFact
  refine ⟨_, written, heapCall_of_actual_run run default,
    reset2_public_resources current.good good heap2 owns2 ?_ _ rfl⟩
  rw [width]
  simp only [resetKeepState, resetPre]
  by_cases changes : s.wbits ≠ s.reqbits
  · simp [changes]
  · simp only [ne_eq, Decidable.not_not] at changes
    simp [changes]

/-- `inflateGetHeader` refuses without gzip, and otherwise writes only the
state record and the caller's header record. -/
theorem inflateGetHeader_call_safe (r : ZStreamRef) (head : GzHeaderPtr) :
    InflateCallSafe r (.inflateGetHeader (some r) head) := by
  intro h i z s current arguments
  obtain ⟨memory, present⟩ := arguments
  by_cases nogzip : s.wrap &&& 2 = 0
  · have run := inflateGetHeader_nogzip current.good.live head nogzip
    exact ⟨_, h, heapCall_of_actual_run run default,
      default_record_public_resources current.good current.good (RecordFrame.refl _ _ _) rfl _⟩
  rcases memory with none | ⟨b, gh, pointer, get, _⟩
  · exact absurd none present
  subst pointer
  obtain ⟨written, run, heap, good, _, live⟩ :=
    inflateGetHeader_ok current.good (g := .tab b) get nogzip
  have owned : ∀ c, StreamOwned written r c ↔ StreamOwned h r c := by
    intro c
    rw [good.streamOwned_iff, current.good.streamOwned_iff]
    simp only [InflateOwned, getHeaderState]
  have putEq : written = { setI h i (getHeaderState (some (.tab b)) s) with
      gzheaders := upd h.gzheaders b (some { gh with done := 0 }) } := by
    rw [heap]
    have kept : (setI h i (getHeaderState (some (.tab b)) s)).gzheaders b = some gh := get
    simp only [GzHeaderRef.put, kept]
    rfl
  refine ⟨_, written, heapCall_of_actual_run run default, ⟨?_, ?_⟩, ?_⟩
  · change Frame h written _
    rw [putEq]
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro c _ outside
    have notState : c ≠ i := by
      intro same
      subst same
      exact outside (Or.inr (Or.inl ((current.good.streamOwned_iff c).mpr (Or.inl rfl))))
    have notHeader : c ≠ b := by
      intro same
      subst same
      exact outside (Or.inr (Or.inr (Or.inl rfl)))
    exact ⟨rfl, rfl, rfl, upd_ne _ _ _ _ notHeader, rfl,
      setI_istates_ne h i c _ notState, rfl, rfl⟩
  · intro region member
    simp [StreamWriteRegions] at member
  · intro c
    have ownerLive : StreamOwned h r c → h.live c := fun owner =>
      good_inflate_owned_live current.good ((current.good.streamOwned_iff c).mp owner)
    dsimp only
    rw [owned, live c]
    simp only [and_not_self, not_false_eq_true, and_true]
    constructor
    · exact Or.inl
    · rintro (old | ⟨owner, fresh⟩)
      · exact old
      · exact False.elim (fresh (ownerLive owner))

#print axioms inflateReset_call_safe
#print axioms inflateGetHeader_call_safe

/-- `inflateGetDictionary` writes only the caller range it is given. -/
theorem inflateGetDictionary_call_safe (r : ZStreamRef) (dest : BPtr) (dl : Option UInt32) :
    InflateCallSafe r (.inflateGetDictionary (some r) dest dl) := by
  intro h zs z s current arguments
  obtain ⟨stream, index, state, streamGet, pointer, stateGet, range⟩ := arguments
  have sameStream : stream = z := Option.some.inj (streamGet.symm.trans current.good.live.hz)
  subst stream
  have sameIndex : index = zs := by
    rw [current.good.live.zst] at pointer
    cases pointer
    rfl
  subst index
  have sameState : state = s := Option.some.inj (stateGet.symm.trans current.good.live.hs)
  subst state
  have before := current
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
    exact ⟨_, h, heapCall_of_actual_run actual default, resources⟩
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
  have currentGood : Good (Space.put h ref replacement) r zs z s :=
    good.byte_view_put get write separate replacement
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
        exact Nat.pow_le_pow_right (by decide) good.inv.win.wbits
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
    rw [currentGood.streamOwned_iff, good.streamOwned_iff]
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
  have run : C.run (inflateGetDictionary (some r) dest dl) h =
      .ok ((Z_OK, dl.map (fun _ => s.whave)), Space.put h ref replacement) := by
    simpa only [C.run, pointer] using actual
  exact ⟨_, _, heapCall_of_actual_run run default, frame, ledger⟩

#print axioms inflateGetDictionary_call_safe

/-- The setter neither relinquishes its existing window nor changes its
state block. This observes the actual translated branches. -/
theorem inflateSetDictionary_owned_retained_good {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z z' : ZStream} {s state : InflateState} {source : BPtr} {len : UInt32} {rc : Int32}
    (good : Good h r zs z s) (allocator : DefAlloc z)
    (range : CallerRange h r source len.toNat false)
    (current : Good after r zs z' state)
    (run : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after)) :
    ∀ b, InflateOwned zs s b → InflateOwned zs state b := by
  have unchanged (same : after = h) : ∀ b, InflateOwned zs s b → InflateOwned zs state b := by
    have stateEq : state = s := Option.some.inj (current.live.hs.symm.trans (same ▸ good.live.hs))
    simpa only [stateEq] using (fun b (owned : InflateOwned zs s b) => owned)
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · have actual := inflateSetDictionary_refused_any good.live source len refused
    exact unchanged (congrArg Prod.snd (Except.ok.inj (run.symm.trans actual)))
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      apply Classical.byContradiction
      intro wrong
      exact refused (Or.inr ⟨raw, wrong⟩)
  obtain ⟨xs, readable⟩ := range.resolve_left nonnull |>.1
  rcases readable with null | ⟨ref, off, array, pointer, get, room, _⟩
  · exact (nonnull null.1).elim
  subst source
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · have actual := inflateSetDictionary_dataerr_any good.live get room mismatch.1 mismatch.2
    exact unchanged (congrArg Prod.snd (Except.ok.inj (run.symm.trans actual)))
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    apply Classical.byContradiction
    intro wrong
    exact mismatch ⟨dict, wrong⟩
  have unowned := callerRange_private_window good range rfl
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with null | ⟨w, bytes, window, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, _frame, _source, _codes, outcome⟩ :=
    updatewindow_decoder_boundary good allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room unowned
  have actual := inflateSetDictionary_window_cut good.live get room allowed checked windowRun good1.live.hs
  rcases outcome with success | ⟨failure, _null, sameState, _heap⟩
  · subst wr
    simp only [ite_true] at actual
    have heapEq := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    dsimp only at heapEq
    have stateEq : state = { state1 with havedict := 1 } := by
      apply Option.some.inj
      rw [← current.live.hs, heapEq]
      simp [setI]
    have retained := updatewindow_owned_retained good get room separate windowRun good1.live.hs
    simpa only [stateEq, InflateOwned] using retained
  · subst wr
    subst state1
    simp only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] at actual
    have heapEq := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    dsimp only at heapEq
    have stateEq : state = { s with mode := MEM } := by
      apply Option.some.inj
      rw [← current.live.hs, heapEq]
      simp [setI]
    simpa only [stateEq, InflateOwned] using (fun b (owned : InflateOwned zs s b) => owned)

/-- `inflateSetDictionary` changes only its records and may install a window. -/
theorem inflateSetDictionary_call_safe (r : ZStreamRef) (source : BPtr) (len : UInt32) :
    InflateCallSafe r (.inflateSetDictionary (some r) source len) := by
  intro h zs z s current range
  obtain ⟨old, dictionary⟩ := good_dictionary_view current.good
  have bytes : ∃ xs, source ≠ .null → Bytes h source len.toNat xs := by
    rcases range with null | ⟨⟨xs, readable⟩, _⟩
    · exact ⟨[], fun nonnull => (nonnull null).elim⟩
    · exact ⟨xs, fun _ => readable⟩
  obtain ⟨xs, readable⟩ := bytes
  have separate : Separate source len.toNat s.window (2 ^ s.wbits.toNat) := by
    cases source with
    | null => simp [Separate]
    | ref ref off =>
      have unowned := callerRange_private_window current.good range rfl
      rcases current.good.inv.win.block with null | ⟨w, array, window, _⟩
      · simp [Separate, null]
      · simp [Separate, window, unowned w window]
  have wide : (s.wrap = 0 ∨ s.mode = DICT) → 8 ≤ s.wbits.toNat := by
    intro allowed
    rcases current.config.window with range | ⟨zero, _, early⟩
    · exact range.1
    · rcases allowed with raw | dict
      · exact absurd zero (current.config.raw raw)
      · rw [dict] at early
        rcases early with e | e | e <;> exact absurd e (by decide)
  obtain ⟨rc, after, run, _reject, _content, frame, post, _beforeGet, postGet, live⟩ :=
    ZlibF.Spec.Public.Proofs.inflateSetDictionary_public h r zs z s source len xs old current.good
      current.alloc.1 dictionary readable separate wide
  have actual := heapCall_of_actual_run run default
  obtain ⟨z', state, next⟩ :=
    inflateSetDictionary_preserves r source len h after zs z s rc current range actual
  have stateEq : post = state := Option.some.inj (postGet.symm.trans next.good.live.hs)
  subst post
  have retained := inflateSetDictionary_owned_retained_good current.good current.alloc range
    next.good run
  refine ⟨rc, after, actual, ⟨?_, ?_⟩, ?_⟩
  · simpa only [StreamWriteRegions, restoreRegions, List.foldl_nil] using
      (show Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
          StreamHeaderRecord h r (.inflateSetDictionary (some r) source len) b) from by
        rcases frame with ⟨static, oracle, garbage, nextBlk, allocs, outside⟩
        refine ⟨static, oracle, garbage, nextBlk, allocs, ?_⟩
        intro b alive unchanged
        apply outside b alive
        intro changed
        apply unchanged
        rcases changed with root | owned
        · exact Or.inl root
        · exact Or.inr (Or.inl ((current.good.streamOwned_iff b).mpr owned)))
  · simp only [StreamWriteRegions, List.not_mem_nil, false_implies, implies_true]
  · intro b
    dsimp only
    rw [next.good.streamOwned_iff, current.good.streamOwned_iff]
    have notRemoved : ¬ (InflateOwned zs s b ∧ ¬ InflateOwned zs state b) := by
      rintro ⟨old, absent⟩
      exact absent (retained b old)
    simpa only [LiveChange, notRemoved, not_false_eq_true, and_true] using live b

#print axioms inflateSetDictionary_call_safe

/-- `inflateEnd` releases everything the stream owns and leaves no state. -/
theorem inflateEnd_invariant {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) :
    ∃ rc after z', C.run (Zlib.Inflate.inflateEnd (some r)) h = .ok (rc, after) ∧
      rc = Z_OK ∧ r.get after = some z' ∧ z'.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r) := by
  obtain ⟨after, run, streamGet, ledger, frame, _, _⟩ :=
    ZlibF.Spec.Public.InflateEndProof.inflate_end_public h r i z s current.good current.alloc.2
  refine ⟨Z_OK, after, {z with state := none}, run, rfl, streamGet, rfl, ?_, ?_⟩
  · exact inflate_frame_mono frame (fun b changed => changed.elim Or.inl
      (fun owned => Or.inr ((current.good.streamOwned_iff b).mpr owned)))
  · intro b
    simpa only [current.good.streamOwned_iff b] using ledger b

#print axioms inflateEnd_invariant

end Zlib.Inflate.Proofs
