import ZlibF.Proof.«inflate.c.window-pointer-run»
import ZlibF.Proof.«inflate.c.default-local-output-frame»
import ZlibF.Proof.«inflate.c.window-public-ring»
import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.window-state-frame»
import ZlibF.Spec.InflateFastMatchHistory
import ZlibF.Proof.«inflate.c.leave-default-public-accounting»
import ZlibF.Proof.«inflate.c.leave-output-footprint»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»
import ZlibF.Proof.«inflate.c.default-state»

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The fast copier and public dictionary use the same chronological ring. -/
theorem saved_zero_eq_ring (a : Array UInt8) (ws wn wh : Nat) :
    Zlib.Inffast.Spec.MatchHistory.saved a ws wn wh 0 = ringList a ws wn wh := by
  simp only [Zlib.Inffast.Spec.MatchHistory.saved, ringList, Nat.zero_add,
    Array.getElem!_eq_getD]
  rfl

/-- Trimming old history first does not change the retained suffix after append. -/
theorem retained_append {α : Type} (history incoming : List α) (capacity : Nat) :
    ((history.drop (history.length - capacity) ++ incoming).drop
      ((history.drop (history.length - capacity) ++ incoming).length - capacity)) =
      (history ++ incoming).drop ((history ++ incoming).length - capacity) := by
  by_cases hshort : history.length ≤ capacity
  · simp only [Nat.sub_eq_zero_of_le hshort, List.drop_zero]
  · simp only [List.length_append, List.length_drop, List.drop_append, List.drop_drop]
    have first : history.length - capacity +
        (history.length - (history.length - capacity) + incoming.length - capacity) =
        history.length + incoming.length - capacity := by omega
    have second : history.length - (history.length - capacity) + incoming.length - capacity -
        (history.length - (history.length - capacity)) =
        history.length + incoming.length - capacity - history.length := by omega
    rw [first, second]

/-- The public predicate exposes exactly the saved bytes used by fast matches. -/
theorem dictionary_eq_saved {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {w : Nat} {a : Array UInt8} {history : List UInt8}
    (good : Good h r zs z s) (window : s.window = .ref (.blk w) 0)
    (get : h.bytes w = some a) (size : a.size = 2 ^ s.wbits.toNat) :
    InflateDictionary h s history ↔
      history = Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat s.whave.toNat 0 := by
  rw [saved_zero_eq_ring]
  exact inflateDictionary_eq_ring good window get size

/-- A null initial window represents empty history regardless of fresh integer contents. -/
theorem null_dictionary_empty {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (good : Good h r zs z s) (window : s.window = .null) :
    InflateDictionary h s [] := by
  have size : s.wsize = 0 := good.inv.win.nullws window
  have count : s.whave = 0 := by
    apply UInt32.toNat_inj.mp
    have bound := good.inv.win.hv
    rw [size] at bound
    simpa using Nat.eq_zero_of_le_zero bound
  exact Or.inl ⟨count, rfl⟩

/-- A real update keeps the suffix of complete history. The source is an
actual public byte view; genuine allocation failure stays explicit. -/
theorem updatewindow_history_suffix
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {source : BRef} {off : Nat} {copy : UInt32} {history incoming : List UInt8}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (input : Bytes h (.ref source off) copy.toNat incoming)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat)))
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat)) :
    ∃ rc after state,
      C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (rc, after) ∧
      Good after r zs z state ∧
      ((rc = 0 ∧ InflateDictionary after state
        ((history ++ incoming).drop ((history ++ incoming).length - 2 ^ s.wbits.toNat))) ∨
       (rc = 1 ∧ s.window = .null ∧ h.allocOk h.nalloc = false ∧
        after = setI { h with nalloc := h.nalloc + 1 } zs s ∧ state = s)) := by
  rcases input with ⟨impossible, _, _⟩ | ⟨ref, index, array, pointer, get, fit, values⟩
  · cases impossible
  · cases pointer
    obtain ⟨rc, after, state, run, current, result⟩ :=
      updatewindow_dictionary_public good allocator get fit values stored separate
    refine ⟨rc, after, state, run, current, ?_⟩
    rcases result with ⟨success, dictionary⟩ | failure
    · exact Or.inl ⟨success, by simpa only [retained_append] using dictionary⟩
    · exact Or.inr failure

#print axioms saved_zero_eq_ring
#print axioms retained_append
#print axioms dictionary_eq_saved
#print axioms null_dictionary_empty
#print axioms updatewindow_history_suffix
/-- Actual default initialization establishes an empty chronological window. -/
theorem default_init_window_history
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultStateJ after r h.nextBlk z s ∧ DefAlloc z ∧ s.window = .null ∧
      InflateDictionary after s [] ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, current, reachable⟩ :=
    inflate_default_state_initial h r version domain platform allocation
  obtain ⟨z0, s0, good0, alloc, free, _mode, window, _rest⟩ := initial
  have sameZ : z0 = z := Option.some.inj (good0.live.hz.symm.trans current.good.live.hz)
  have sameS : s0 = s := Option.some.inj (good0.live.hs.symm.trans current.good.live.hs)
  subst z0
  subst s0
  exact ⟨after, z, s, run, current, ⟨alloc, free⟩, window,
    null_dictionary_empty current.good window, reachable⟩

/-- The content producer and the non-window frame describe the same actual run. -/
theorem updatewindow_history_suffix_framed
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {source : BRef} {off : Nat} {copy : UInt32} {history incoming : List UInt8}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (input : Bytes h (.ref source off) copy.toNat incoming)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat)))
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat)) :
    ∃ rc after state,
      C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (rc, after) ∧
      Good after r zs z state ∧ WindowStateFrame s state ∧ state.wbits = s.wbits ∧
      ((rc = 0 ∧ InflateDictionary after state
        ((history ++ incoming).drop ((history ++ incoming).length - 2 ^ state.wbits.toNat))) ∨
       (rc = 1 ∧ s.window = .null ∧ h.allocOk h.nalloc = false ∧
        after = setI { h with nalloc := h.nalloc + 1 } zs s ∧ state = s)) := by
  obtain ⟨rc, after, state, run, current, result⟩ :=
    updatewindow_history_suffix good allocator input stored separate
  rcases result with ⟨success, dictionary⟩ | failure
  · subst rc
    rcases input with ⟨impossible, _, _⟩ | ⟨ref, index, array, pointer, get, fit, _values⟩
    · cases impossible
    · cases pointer
      have frame := updatewindow_state_frame_public good allocator get fit separate run current.live.hs
      have bits : state.wbits = s.wbits := by rw [frame]
      exact ⟨0, after, state, run, current, frame, bits,
        Or.inl ⟨rfl, by simpa only [bits] using dictionary⟩⟩
  · have frame : WindowStateFrame s state := by rw [failure.2.2.2.2]; rfl
    have bits : state.wbits = s.wbits := by rw [frame]
    exact ⟨rc, after, state, run, current, frame, bits, Or.inr failure⟩

#print axioms default_init_window_history
#print axioms updatewindow_history_suffix_framed
/-- With the allocation oracle available, the actual update produces the
concrete saved ring used by generic fast matches, plus its real ownership
accounting. No backing-array or post-content fact is a caller assumption. -/
theorem updatewindow_history_suffix_saved
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {source : BRef} {off : Nat} {copy : UInt32} {history incoming : List UInt8}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (allocation : h.allocOk h.nalloc = true)
    (input : Bytes h (.ref source off) copy.toNat incoming)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat)))
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat)) :
    ∃ after state w a,
      C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (0, after) ∧
      Good after r zs z state ∧ WindowStateFrame s state ∧ state.wbits = s.wbits ∧
      state.window = .ref (.blk w) 0 ∧ after.bytes w = some a ∧ after.ro w = false ∧
      a.size = 2 ^ state.wbits.toNat ∧
      Zlib.Inffast.Spec.MatchHistory.saved a state.wsize.toNat state.wnext.toNat state.whave.toNat 0 =
        (history ++ incoming).drop ((history ++ incoming).length - 2 ^ state.wbits.toNat) ∧
      (∀ owned, h.Owns owned → after.Owns
        (fun b => owned b ∨ (s.window = .null ∧ b = h.nextBlk))) := by
  obtain ⟨rc, after, state, run, current, frame, bits, result⟩ :=
    updatewindow_history_suffix_framed good allocator input stored separate
  rcases result with ⟨code, dictionary⟩ | failure
  · subst rc
    rcases input with ⟨impossible, _, _⟩ | ⟨ref, index, array, pointer, get, fit, _values⟩
    · cases impossible
    · cases pointer
      obtain ⟨rc0, heap0, state0, run0, current0, result0⟩ :=
        updatewindow_safe_public (copy := copy) (eo := off + copy.toNat)
          good allocator get (by omega) fit (by simpa using separate)
      have same : ((0 : Int32), after) = (rc0, heap0) := Except.ok.inj (run.symm.trans run0)
      cases same
      have sameState : state0 = state :=
        Option.some.inj (current0.live.hs.symm.trans current.live.hs)
      subst state0
      rcases result0 with ⟨_code, nonnull, ownership⟩ | ⟨impossible, _rest⟩
      · rcases current.inv.win.block with null | ⟨w, a, window, getWindow, readonly, size⟩
        · exact False.elim (nonnull null)
        · have meaning := (dictionary_eq_saved current window getWindow size).mp dictionary
          exact ⟨after, state, w, a, run, current, frame, bits, window,
            getWindow, readonly, size, meaning.symm, ownership⟩
      · exact False.elim ((by decide : (0 : Int32) ≠ 1) impossible)
  · have bad := failure.2.2.1
    rw [allocation] at bad
    cases bad

#print axioms updatewindow_history_suffix_saved
/-- Equal window fields and equal readable views transport chronological history. -/
theorem dictionary_transport {h after : Heap} {s state : InflateState} {history : List UInt8}
    (stored : InflateDictionary h s history)
    (window : state.window = s.window) (size : state.wsize = s.wsize)
    (haveCount : state.whave = s.whave) (next : state.wnext = s.wnext)
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) :
    InflateDictionary after state history := by
  rcases stored with ⟨zero, empty⟩ | ⟨ref, off, array, pointer, get, bound, values⟩
  · exact Or.inl ⟨by rw [haveCount]; exact zero, empty⟩
  · exact Or.inr ⟨ref, off, array, by rw [window]; exact pointer,
      by rw [views]; exact get, by rw [size]; exact bound,
      by simpa only [haveCount, next] using values⟩

/-- Actual metadata/checksum/return execution does not change saved history. -/
theorem leaveFinalize_history
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} {history : List UInt8}
    (E : Env c h r zs current s) (good : Good h r zs current s)
    (output : LeaveOutputView h l) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (stored : InflateDictionary h s history) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ LeaveMetadataFrame s state ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
      InflateDictionary after state history := by
  obtain ⟨rc, after, stream, state, run, currentGood, frame, views, _ret, _codes, _statics⟩ :=
    leaveFinalize_all_wrappers_safe E good output statics cursor count
  refine ⟨rc, after, stream, state, run, currentGood, frame, views, ?_⟩
  exact dictionary_transport stored (by rw [frame]) (by rw [frame])
    (by rw [frame]) (by rw [frame]) views

#print axioms dictionary_transport
#print axioms leaveFinalize_history
/-- The actual window branch appends exactly its observed produced bytes.
The allocation-failure branch retains those bytes and reports MEM explicitly. -/
theorem leaveWithWindow_history
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {history : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ rc after stream state base emitted,
      leaveWithWindow c l z h = .ok (rc, after) ∧ Good after r zs stream state ∧
      inputAdvance base (l.out_ - l.left).toNat = l.put ∧
      emitted.length = (l.out_ - l.left).toNat ∧
      Bytes h base (l.out_ - l.left).toNat emitted ∧
      Bytes after base (l.out_ - l.left).toNat emitted ∧ state.wbits = s.wbits ∧
      ((state.mode = s.mode ∧ InflateDictionary after state
        ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat))) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  obtain ⟨ref, array, off, put, get, _write, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = (l.out_ - l.left).toNat := by rw [count]
  have natAmount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [natAmount]; exact produced
  have bound : off ≤ array.size := by omega
  let base : BPtr := .ref ref (off - (l.out_ - z.avail_out).toNat)
  let emitted := (array.toList.drop (off - (l.out_ - z.avail_out).toNat)).take
    (l.out_ - z.avail_out).toNat
  have beforeBytes : Bytes h base (l.out_ - z.avail_out).toNat emitted :=
    Or.inr ⟨ref, _, array, rfl, get, by omega, rfl⟩
  have emittedCount : emitted.length = (l.out_ - z.avail_out).toNat := by
    simp only [emitted, List.length_take, List.length_drop, Array.length_toList]
    omega
  have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off := by omega
  have advance : inputAdvance base (l.out_ - l.left).toNat = l.put := by
    rw [← amount]
    simp only [base, inputAdvance, endpoint, put]
  have sep : Separate base (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with null | ⟨w, a, window, _, _, _⟩
    · simp [Separate, null]
    · simp [base, Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, _codes, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  obtain ⟨histRc, histHeap, histState, histRun, histGood, histResult⟩ :=
    updatewindow_history_suffix good allocator beforeBytes stored sep
  have histRun0 : updatewindow (some r) (.ref ref off) (l.out_ - z.avail_out) h =
      .ok (histRc, histHeap) := by simpa only [C.run, endpoint, base] using histRun
  have same : (wr, heap1) = (histRc, histHeap) := Except.ok.inj (windowRun.symm.trans histRun0)
  cases same
  have sameState : histState = state1 := Option.some.inj (histGood.live.hs.symm.trans good1.live.hs)
  subst histState
  rcases outcome with success | failure
  · subst wr
    have dictionary : InflateDictionary heap1 state1
        ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ s.wbits.toNat)) := by
      rcases histResult with ⟨_, dictionary⟩ | ⟨impossible, _⟩
      · exact dictionary
      · exact False.elim ((by decide : (0 : Int32) ≠ 1) impossible)
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, array, put, sourceView, by rw [count] at start; exact start, bound⟩
    have publicFrame := updatewindow_frame_public (copy := l.out_ - z.avail_out)
      (off := off - (l.out_ - z.avail_out).toNat) good allocator get (by omega) sep
      (by simpa only [C.run, endpoint, base] using windowRun)
    have static1 : heap1.static = h.static := publicFrame.1.symm
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, static1] using statics
    obtain ⟨rc, after, stream, state, finish, finalGood, finalFrame, views, finalDictionary⟩ :=
      leaveFinalize_history (z := z) env1 good1 view statics1 cursor count dictionary
    have bits : state.wbits = s.wbits := by rw [finalFrame, windowFrame]
    have bytes : Bytes after base (l.out_ - z.avail_out).toNat emitted :=
      Or.inr ⟨ref, _, array, rfl, by rw [views]; exact sourceView, by omega, rfl⟩
    refine ⟨rc, after, stream, state, base, emitted, ?_, finalGood, advance,
      by simpa only [amount] using emittedCount,
      by simpa only [amount] using beforeBytes, by simpa only [amount] using bytes,
      bits, Or.inl ⟨?_, ?_⟩⟩
    · unfold leaveWithWindow
      rw [bind_app, E.strm, cursor, put, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finish
    · rw [finalFrame, windowFrame]
    · simpa only [bits] using finalDictionary
  · obtain ⟨eqrc, _null, stateEq, _heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have finalGood : Good (setI heap1 zs state) r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have bytes : Bytes (setI heap1 zs state) base (l.out_ - z.avail_out).toNat emitted :=
      Or.inr ⟨ref, _, array, rfl, by rw [byte_view_get_setI]; exact sourceView, by omega, rfl⟩
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, base, emitted, ?_, finalGood,
      advance, by simpa only [amount] using emittedCount,
      by simpa only [amount] using beforeBytes, by simpa only [amount] using bytes,
      rfl, Or.inr ⟨rfl, rfl⟩⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl

#print axioms leaveWithWindow_history

/-- Byte observations depend only on the actual readable views. -/
theorem bytes_transport {h after : Heap} {pointer : BPtr} {count : Nat}
    {values : List UInt8} (observed : Bytes h pointer count values)
    (views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) :
    Bytes after pointer count values := by
  rcases observed with null | ⟨ref, off, array, pointer, get, bound, values⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, off, array, pointer, by rw [views]; exact get, bound, values⟩

/-- A successful actual leave has a concrete observation of its new output,
including the no-window and allocation-failure paths. -/
theorem inflate_leave_observed_output
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (bits : l.bits.toNat ≤ 39) (run : inflate_leave c l h = .ok (rc, after)) :
    ∃ base emitted, inputAdvance base (l.out_ - l.left).toNat = l.put ∧
      emitted.length = (l.out_ - l.left).toNat ∧
      Bytes h base (l.out_ - l.left).toNat emitted ∧
      Bytes after base (l.out_ - l.left).toNat emitted := by
  obtain ⟨ref, array, off, put, get, _write, room, leftCount, produced, _unowned⟩ :=
    callerRange_slow_output invariant.good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  have amount : (l.out_ - l.left).toNat = l.out_.toNat - l.left.toNat :=
    UInt32.toNat_sub_of_le _ _ leftCount
  have start : (l.out_ - l.left).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ array.size := by omega
  let base : BPtr := .ref ref (off - (l.out_ - l.left).toNat)
  let emitted := (array.toList.drop (off - (l.out_ - l.left).toNat)).take
    (l.out_ - l.left).toNat
  have endpoint : off - (l.out_ - l.left).toNat + (l.out_ - l.left).toNat = off := by omega
  have afterView := (inflate_leave_output_view_unchanged E invariant allocator buffers bits run put get).2.1
  refine ⟨base, emitted, ?_, ?_, ?_, ?_⟩
  · simp only [base, inputAdvance, endpoint, put]
  · simp only [emitted, List.length_take, List.length_drop, Array.length_toList]
    omega
  · exact Or.inr ⟨ref, _, array, rfl, get, by omega, rfl⟩
  · exact Or.inr ⟨ref, _, array, rfl, afterView, by omega, rfl⟩

/-- On active decoder returns the actual inf_leave source saves exactly the
old chronological history followed by the observed output. A terminal
FINISH exit may skip its unnecessary first window allocation. -/
theorem inflate_leave_history_active
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {history : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (active : s.mode < CHECK)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ rc after stream state base emitted,
      inflate_leave c l h = .ok (rc, after) ∧ Good after r zs stream state ∧
      inputAdvance base (l.out_ - l.left).toNat = l.put ∧
      emitted.length = (l.out_ - l.left).toNat ∧
      Bytes h base (l.out_ - l.left).toNat emitted ∧
      Bytes after base (l.out_ - l.left).toNat emitted ∧
      (state.mode < CHECK → InflateDictionary after state
        ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat))) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have current := invariant.restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    have static0 : heap0.static = h.static := by
      simp only [heap0, setI, ZStreamRef.put_static]
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [static0, invariant.globals]
    exact ⟨rfl, rfl⟩
  have stored0 : InflateDictionary heap0 state0
      (history.drop (history.length - 2 ^ state0.wbits.toNat)) :=
    dictionary_transport stored rfl rfl rfl rfl views0
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, base, emitted, run, good, advance, count,
      beforeBytes, afterBytes, _wbits, outcome⟩ :=
      leaveWithWindow_history env0 current.good allocator.1 output0 statics0 rfl rfl stored0
    refine ⟨rc, after, stream, state, base, emitted, ?_, good, advance, count,
      bytes_transport beforeBytes (fun ref => (views0 ref).symm), afterBytes, ?_⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
      exact run
    · intro stillActive
      rcases outcome with ⟨_mode, dictionary⟩ | ⟨_rc, mem⟩
      · exact dictionary
      · rw [mem] at stillActive
        exact False.elim ((by decide : ¬ MEM < CHECK) stillActive)
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) with
      | false => rfl
      | true => exact False.elim (update eq)
    have modeBound : s.mode < BAD := by
      change s.mode.toNat < 16209
      change s.mode.toNat < 16206 at active
      omega
    have noOutput : l.out_ = l.left := by
      by_cases equal : l.out_ = l.left
      · exact equal
      · have yes : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
            (s.mode < CHECK || c.flush != Z_FINISH))) = true := by
          simp [equal, active, modeBound]
        rw [yes] at skip
        cases skip
    obtain ⟨rc, after, stream, state, run, good, frame, views, dictionary⟩ :=
      leaveFinalize_history (z := stream0) env0 current.good
        (leaveOutputView_of_cursor current.good output0) statics0 rfl rfl stored0
    refine ⟨rc, after, stream, state, l.put, [], ?_, good, ?_, ?_, ?_, ?_, ?_⟩
    · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
      exact run
    · simp only [noOutput, UInt32.sub_self, UInt32.toNat_zero, inputAdvance_zero]
    · simp only [noOutput, UInt32.sub_self, UInt32.toNat_zero, List.length_nil]
    · rw [noOutput, UInt32.sub_self, UInt32.toNat_zero]
      obtain ⟨ref, off, array, pointer, get, _start, bound⟩ :=
        leaveOutputView_of_cursor invariant.good buffers.output
      exact Or.inr ⟨ref, off, array, pointer, get, by omega, by simp⟩
    · rw [noOutput, UInt32.sub_self, UInt32.toNat_zero]
      obtain ⟨ref, off, array, pointer, get, _start, bound⟩ :=
        leaveOutputView_of_cursor current.good output0
      exact Or.inr ⟨ref, off, array, pointer, by rw [views]; exact get, by omega, by simp⟩
    · intro _stillActive
      have wbits : state.wbits = state0.wbits := by rw [frame]
      simpa only [List.append_nil, wbits] using dictionary

#print axioms bytes_transport
#print axioms inflate_leave_observed_output
#print axioms inflate_leave_history_active

/-- The next-call history representation is an internal guarded invariant.
Its concrete output bytes and the complete default safety invariant are
produced by the same actual leave execution. -/
theorem inflate_leave_history
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {history : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (stored : s.mode < CHECK →
      InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) (lowOut : s.mode ≤ DICT → l.out_ = l.left) :
    ∃ rc after stream state base emitted,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
      stream.next_out = l.put ∧ stream.avail_out = l.left ∧
      inputAdvance base (l.out_ - l.left).toNat = stream.next_out ∧
      emitted.length = (l.out_ - l.left).toNat ∧
      Bytes h base (l.out_ - l.left).toNat emitted ∧
      Bytes after base (l.out_ - l.left).toNat emitted ∧
      (state.mode < CHECK → InflateDictionary after state
        ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat))) := by
  obtain ⟨rc, after, stream, state, run, final, finalAllocator,
    nextIn, haveIn, nextOut, leftOut, outcome⟩ :=
    inflate_leave_default_public_accounting E invariant allocator buffers bits lowOut
  by_cases active : s.mode < CHECK
  · obtain ⟨otherRc, otherHeap, otherStream, otherState, base, emitted, otherRun,
      otherGood, advance, count, beforeBytes, afterBytes, dictionary⟩ :=
      inflate_leave_history_active E invariant allocator buffers bits active (stored active)
    have same : (rc, after) = (otherRc, otherHeap) :=
      Except.ok.inj (run.symm.trans otherRun)
    cases same
    have streamSame : otherStream = stream :=
      Option.some.inj (otherGood.live.hz.symm.trans final.good.live.hz)
    have stateSame : otherState = state :=
      Option.some.inj (otherGood.live.hs.symm.trans final.good.live.hs)
    subst otherStream
    subst otherState
    exact ⟨rc, after, stream, state, base, emitted, run, final, finalAllocator,
      nextIn, haveIn, nextOut, leftOut, by rw [nextOut]; exact advance,
      count, beforeBytes, afterBytes, dictionary⟩
  · obtain ⟨base, emitted, advance, count, beforeBytes, afterBytes⟩ :=
      inflate_leave_observed_output E invariant allocator buffers bits run
    refine ⟨rc, after, stream, state, base, emitted, run, final, finalAllocator,
      nextIn, haveIn, nextOut, leftOut, by rw [nextOut]; exact advance,
      count, beforeBytes, afterBytes, ?_⟩
    intro nextActive
    rcases outcome with ⟨_, _, mode⟩ | ⟨_, mem, _⟩
    · rw [mode] at nextActive
      exact False.elim (active nextActive)
    · rw [mem] at nextActive
      exact False.elim ((by decide : ¬ MEM < CHECK) nextActive)

/-- A chronological dictionary has the exact fast-match saved view whenever
the real window exists. The lazy unallocated alternative represents only
an empty dictionary and has whave zero. -/
theorem dictionary_saved_or_lazy
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} (good : Good h r zs z s)
    (stored : InflateDictionary h s history) :
    (s.window = .null ∧ s.whave = 0 ∧ history = []) ∨
    ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧
      a.size = 2 ^ s.wbits.toNat ∧
      Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat s.whave.toNat 0 = history := by
  rcases good.inv.win.block with null | ⟨w, a, window, get, readonly, size⟩
  · rcases stored with ⟨zero, empty⟩ | ⟨ref, off, array, pointer, _⟩
    · exact Or.inl ⟨null, zero, empty⟩
    · rw [null] at pointer
      cases pointer
  · exact Or.inr ⟨w, a, window, get, readonly, size,
      ((dictionary_eq_saved good window get size).mp stored).symm⟩

/-- The actual public leave produces the saved dictionary interface consumed
by fast match proofs. The old relation is a ghost invariant, and observed
output and any physical backing are conclusions rather than assumptions. -/
theorem inflate_leave_history_saved
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {history : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (stored : s.mode < CHECK →
      InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) (lowOut : s.mode ≤ DICT → l.out_ = l.left) :
    ∃ rc after stream state base emitted,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      inputAdvance base (l.out_ - l.left).toNat = stream.next_out ∧
      emitted.length = (l.out_ - l.left).toNat ∧
      Bytes h base (l.out_ - l.left).toNat emitted ∧
      Bytes after base (l.out_ - l.left).toNat emitted ∧
      (state.mode < CHECK →
        (state.window = .null ∧ state.whave = 0 ∧
          (history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat) = []) ∨
        ∃ w a, state.window = .ref (.blk w) 0 ∧ after.bytes w = some a ∧
          after.ro w = false ∧ a.size = 2 ^ state.wbits.toNat ∧
          Zlib.Inffast.Spec.MatchHistory.saved a state.wsize.toNat state.wnext.toNat state.whave.toNat 0 =
            (history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat)) := by
  obtain ⟨rc, after, stream, state, base, emitted, run, final, finalAllocator,
    _nextIn, _haveIn, _nextOut, _leftOut, advance, count, beforeBytes, afterBytes, dictionary⟩ :=
    inflate_leave_history E invariant allocator buffers bits stored lowOut
  exact ⟨rc, after, stream, state, base, emitted, run, final, finalAllocator,
    advance, count, beforeBytes, afterBytes, fun active =>
      dictionary_saved_or_lazy final.good (dictionary active)⟩

#print axioms inflate_leave_history
#print axioms dictionary_saved_or_lazy
#print axioms inflate_leave_history_saved

/-- The actual public caller-edit relation retains the owned chronological
window while allowing arbitrary replacement of caller byte buffers. -/
theorem rebuffer_dictionary
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} (good : Good h r zs z s) (edit : Rebuffer h after r)
    (stored : InflateDictionary h s history) : InflateDictionary after s history := by
  obtain ⟨stream, _fields, current⟩ := rebuffer_inflate_good good edit
  rcases good.inv.win.block with null | ⟨w, a, window, get, readonly, size⟩
  · rcases stored with empty | ⟨ref, off, array, pointer, _⟩
    · exact Or.inl empty
    · rw [null] at pointer
      cases pointer
  · have kept := rebuffer_inflate_owned good edit (Or.inr window)
    have nextGet : after.bytes w = some a := kept.1.trans get
    exact (dictionary_eq_saved current window nextGet size).mpr
      ((dictionary_eq_saved good window get size).mp stored)

/-- Buffer replacement preserves the guarded ghost history and the full
default relation, without any requirement on caller byte contents. -/
theorem rebuffer_default_history
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after)
    (stored : s.mode < CHECK →
      InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ stream, DefaultStateJ after r zs stream s ∧ DefAlloc stream ∧
      (s.mode < CHECK → InflateDictionary after s
        (history.drop (history.length - 2 ^ s.wbits.toNat))) := by
  obtain ⟨stream, current⟩ := rebuffer_default_state invariant edit platform
  obtain ⟨otherStream, fields, otherGood⟩ := rebuffer_inflate_good invariant.good edit
  have same : otherStream = stream :=
    Option.some.inj (otherGood.live.hz.symm.trans current.good.live.hz)
  subst otherStream
  have finalAllocator : DefAlloc stream := by
    rw [fields]
    exact allocator
  exact ⟨stream, current, finalAllocator,
    fun active => rebuffer_dictionary invariant.good edit (stored active)⟩

/-- A true leave followed by any legal rebuffer produces the ghost suffix
for the next decoder call. The ghost grows by the observed actual output,
and its initialization is provided by default_init_window_history above. -/
theorem inflate_leave_rebuffer_history
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {history : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (stored : s.mode < CHECK →
      InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) (lowOut : s.mode ≤ DICT → l.out_ = l.left) :
    ∃ rc after stream state base emitted,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      inputAdvance base (l.out_ - l.left).toNat = stream.next_out ∧
      emitted.length = (l.out_ - l.left).toNat ∧
      Bytes h base (l.out_ - l.left).toNat emitted ∧
      Bytes after base (l.out_ - l.left).toNat emitted ∧
      (state.mode < CHECK → InflateDictionary after state
        ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat))) ∧
      (∀ nextHeap, Rebuffer after nextHeap r →
        ZlibF.PlatformMemory.ByteObjectsFit nextHeap →
        ∃ nextStream, DefaultStateJ nextHeap r zs nextStream state ∧ DefAlloc nextStream ∧
          (state.mode < CHECK → InflateDictionary nextHeap state
            ((history ++ emitted).drop ((history ++ emitted).length - 2 ^ state.wbits.toNat)))) := by
  obtain ⟨rc, after, stream, state, base, emitted, run, final, finalAllocator,
    _nextIn, _haveIn, _nextOut, _leftOut, advance, count, beforeBytes, afterBytes, dictionary⟩ :=
    inflate_leave_history E invariant allocator buffers bits stored lowOut
  exact ⟨rc, after, stream, state, base, emitted, run, final, finalAllocator,
    advance, count, beforeBytes, afterBytes, dictionary,
    fun _nextHeap edit platform => rebuffer_default_history final finalAllocator edit platform dictionary⟩

#print axioms rebuffer_dictionary
#print axioms rebuffer_default_history
#print axioms inflate_leave_rebuffer_history
end Zlib.Inflate.Proofs.WindowHistory

namespace Zlib.Inflate.Proofs.WindowCounts
set_option maxHeartbeats 2000000
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An observer for the three saved-window counters; no implementation semantics are changed. -/
abbrev counts (s : InflateState) : UInt32 × UInt32 × UInt32 := (s.wsize, s.whave, s.wnext)


open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual pointer graph used to identify decoder-owned windows. -/
def decoderWindows (h : Heap) (b : Nat) : Option (UInt32 × UInt32 × UInt32) := (h.istates b).map counts

/-- Every existing decoder retains its saved-window counter. This is a source
observer, independent of safety, allocation shape and output contents. -/
def WindowFrame (_r : ZStreamRef) (_owner : InflateStatePtr) (before after : Heap) : Prop :=
  decoderWindows after = decoderWindows before

theorem WindowFrame.refl (r : ZStreamRef) (owner : InflateStatePtr) (h : Heap) : WindowFrame r owner h h := rfl

theorem WindowFrame.trans {r : ZStreamRef} {owner : InflateStatePtr} {first second third : Heap}
    (left : WindowFrame r owner first second) (right : WindowFrame r owner second third) :
    WindowFrame r owner first third := Eq.trans right left

def WindowFrameM {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : M α) : Prop :=
  ∀ h value after, program h = .ok (value, after) → WindowFrame r owner h after

def WindowFrameX {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (program : X α) : Prop :=
  ∀ l h outcome regs after, runX program l h = .ok ((outcome, regs), after) → WindowFrame r owner h after

theorem windowFrameM_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : WindowFrameM r owner (pure value) := by
  intro h result after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameM_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : M α} {next : α → M β}
    (hf : WindowFrameM r owner first) (hn : ∀ value, WindowFrameM r owner (next value)) : WindowFrameM r owner (first >>= next) := by
  intro h result after run
  rw [bind_app] at run
  cases firstRun : first h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    rw [firstRun] at run
    exact (hf h value middle firstRun).trans (hn value middle result after run)


theorem windowFrameX_pure {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (value : α) : WindowFrameX r owner (pure value) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_bind {α β : Type} {r : ZStreamRef} {owner : InflateStatePtr} {first : X α} {next : α → X β}
    (hf : WindowFrameX r owner first) (hn : ∀ value, WindowFrameX r owner (next value)) : WindowFrameX r owner (first >>= next) := by
  intro l h outcome regs after run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    cases decision with
    | error exit =>
      cases run
      exact hf _ _ _ _ _ firstRun
    | ok value =>
      exact (hf l h (.ok value) middleRegs middleHeap firstRun).trans
        (hn value middleRegs middleHeap outcome regs after run)


theorem windowFrameX_lift {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : M α}
    (frame : WindowFrameM r owner program) : WindowFrameX r owner (monadLift program : X α) := by
  intro l h outcome regs after run
  rw [runX_lift] at run
  cases source : program h with
  | error fault =>
    simp only [source] at run
    cases run
  | ok pair =>
    obtain ⟨value, middle⟩ := pair
    simp only [source] at run
    cases run
    exact frame _ _ _ source

/-- The same record frame composes through an actual terminating C loop. -/

theorem windowFrameM_cwhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ state, WindowFrameM r owner (cond state)) (hb : ∀ state, WindowFrameM r owner (body state))
    (state : σ) : WindowFrameM r owner (cwhile cond body state) := by
  have key : ∀ n state, WindowFrameM r owner (cwhile.go cond body n state) := by
    intro n
    induction n with
    | zero =>
      intro state h value after run
      simp only [cwhile.go] at run
      cases run
    | succ n ih =>
      intro state h value after run
      simp only [cwhile.go, bind_app] at run
      cases condition : cond state h with
      | error fault => rw [condition] at run; cases run
      | ok pair =>
        obtain ⟨⟨test, middle⟩, heap1⟩ := pair
        rw [condition] at run
        have first := hc state h (test, middle) heap1 condition
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
          cases run
          exact first
        | true =>
          simp only [ite_true, bind_app] at run
          cases executed : body middle heap1 with
          | error fault => rw [executed] at run; cases run
          | ok pair =>
            obtain ⟨next, heap2⟩ := pair
            rw [executed] at run
            exact first.trans ((hb middle heap1 next heap2 executed).trans (ih next heap2 value after run))
  exact key fuel state

/-- An X program's successful-run frame is also its underlying C frame. -/

theorem windowFrameM_runX {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {program : X α}
    (frame : WindowFrameX r owner program) (l : IL) : WindowFrameM r owner (runX program l) := by
  intro h result after run
  obtain ⟨outcome, regs⟩ := result
  exact frame l h outcome regs after run

/-- Local-register reads and writes leave every decoder saved-window counter unchanged. -/

theorem windowFrameX_get (r : ZStreamRef) (owner : InflateStatePtr) : WindowFrameX r owner (get : X IL) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_set (r : ZStreamRef) (owner : InflateStatePtr) (l : IL) : WindowFrameX r owner (set l : X Unit) := by
  intro before h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_modify (r : ZStreamRef) (owner : InflateStatePtr) (update : IL → IL) : WindowFrameX r owner (modify update : X Unit) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h


theorem windowFrameX_throw {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (exit : Ex) : WindowFrameX r owner (throw exit : X α) := by
  intro l h outcome regs after run
  cases run
  exact WindowFrame.refl r owner h

/-- The actual X loop wrapper retains a window-pointer frame whenever its
condition and body do, including direct returns and leave exceptions. -/

theorem windowFrameX_xwhileBrk {r : ZStreamRef} {owner : InflateStatePtr} {cond body : X Bool}
    (hc : WindowFrameX r owner cond) (hb : WindowFrameX r owner body) : WindowFrameX r owner (xwhileBrk cond body) := by
  intro l h outcome regs after run
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (result, next) ← runX cond current.1
      pure (match result with
        | .ok value => (value, (next, Stop.go))
        | .error exit => (false, (next, Stop.ex exit)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (result, next) ← runX body current.1
    pure (match result with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error exit => (next, Stop.ex exit))
  have condFrame : ∀ current, WindowFrameM r owner (loopCond current) := by
    intro ⟨current, stop⟩
    cases stop with
    | go => exact windowFrameM_bind (windowFrameM_runX hc current) (fun _ => windowFrameM_pure r owner _)
    | brk => exact windowFrameM_pure r owner _
    | ex exit => exact windowFrameM_pure r owner _
  have bodyFrame : ∀ current, WindowFrameM r owner (loopBody current) := by
    intro ⟨current, stop⟩
    exact windowFrameM_bind (windowFrameM_runX hb current) (fun _ => windowFrameM_pure r owner _)
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : WindowFrameM r owner program :=
    windowFrameM_bind (windowFrameM_cwhile condFrame bodyFrame (l, Stop.go)) (fun _ => windowFrameM_pure r owner _)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h (outcome, regs) after run


theorem windowFrameX_xwhile {r : ZStreamRef} {owner : InflateStatePtr} {cond : X Bool} {body : X Unit}
    (hc : WindowFrameX r owner cond) (hb : WindowFrameX r owner body) : WindowFrameX r owner (xwhile cond body) :=
  windowFrameX_xwhileBrk hc (windowFrameX_bind hb (fun _ => windowFrameX_pure r owner false))


theorem windowFrameX_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : X α}
    (hy : WindowFrameX r owner yes) (hn : WindowFrameX r owner no) : WindowFrameX r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn




open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! Successful primitive reads retain every decoder saved-window counter. -/

variable {R T : Type} [Space Heap R T]

theorem windowFrameM_ub {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : WindowFrameM r owner (ub message : M α) := by
  intro h value after run
  cases run

theorem windowFrameM_ite {α : Type} {r : ZStreamRef} {owner : InflateStatePtr} {test : Prop} [Decidable test] {yes no : M α}
    (hy : WindowFrameM r owner yes) (hn : WindowFrameM r owner no) : WindowFrameM r owner (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn


theorem windowFrameM_ptr_add (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (offset : Int) : WindowFrameM r owner (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_load (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) : WindowFrameM r owner (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_index (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (index : Int) : WindowFrameM r owner (Ptr.index p index : M T) :=
  windowFrameM_bind (windowFrameM_ptr_add r owner p index) (fun next => windowFrameM_ptr_load r owner next)

theorem windowFrameM_ptr_diff [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : WindowFrameM r owner (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_lt [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : WindowFrameM r owner (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ptr_le [DecidableEq R] (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) : WindowFrameM r owner (p.le q) :=
  windowFrameM_bind (windowFrameM_ptr_lt r owner q p) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_ldS (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : WindowFrameM r owner (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      exact WindowFrame.refl r owner h

theorem windowFrameM_ldZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) : WindowFrameM r owner (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    exact WindowFrame.refl r owner h

theorem windowFrameM_rdS {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (field : InflateState → α) :
    WindowFrameM r owner (rdS pointer field) :=
  windowFrameM_bind (windowFrameM_ldS r owner pointer) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_rdZ {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (field : ZStream → α) :
    WindowFrameM r owner (rdZ pointer field) :=
  windowFrameM_bind (windowFrameM_ldZ r owner pointer) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (shl32 value shift) := by
  unfold shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_cdoWhile {σ : Type} {r : ZStreamRef} {owner : InflateStatePtr} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ state, WindowFrameM r owner (body state)) (hc : ∀ state, WindowFrameM r owner (cond state))
    (state : σ) : WindowFrameM r owner (cdoWhile body cond state) := by
  have key : ∀ n state, WindowFrameM r owner (cdoWhile.go body cond n state) := by
    intro n
    induction n with
    | zero =>
      intro state h value after run
      simp only [cdoWhile.go] at run
      cases run
    | succ n ih =>
      intro state h value after run
      simp only [cdoWhile.go, bind_app] at run
      cases executed : body state h with
      | error fault => rw [executed] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        rw [executed] at run
        have first := hb state h middle heap1 executed
        simp only [] at run
        cases condition : cond middle heap1 with
        | error fault => rw [condition] at run; cases run
        | ok pair =>
          obtain ⟨⟨test, next⟩, heap2⟩ := pair
          rw [condition] at run
          have second := hc middle heap1 (test, next) heap2 condition
          cases test with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
            cases run
            exact first.trans second
          | true =>
            simp only [ite_true] at run
            exact first.trans (second.trans (ih next heap2 value after run))
  exact key fuel state

theorem windowFrameM_list_forIn {α β : Type} (r : ZStreamRef) (owner : InflateStatePtr) (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, WindowFrameM r owner (body value membership state))
    (initial : β) : WindowFrameM r owner (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact windowFrameM_pure r owner _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine windowFrameM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact windowFrameM_pure r owner _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

theorem windowFrameM_castI (r : ZStreamRef) (owner : InflateStatePtr) (state : Option StateRef) : WindowFrameM r owner (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_strLit (r : ZStreamRef) (owner : InflateStatePtr) (message : String) : WindowFrameM r owner (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_ldHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) : WindowFrameM r owner (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> exact WindowFrame.refl r owner h)

theorem windowFrameM_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (shr32 value shift) := by
  unfold shr32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : WindowFrameM r owner (shl64 value shift) := by
  unfold shl64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value : UInt64) (shift : UInt32) : WindowFrameM r owner (shr64 value shift) := by
  unfold shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_chkI32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (chkI32 value) := by
  unfold chkI32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_chkI64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (chkI64 value) := by
  unfold chkI64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_hcrcOn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) : WindowFrameM r owner (hcrcOn pointer) :=
  windowFrameM_bind (windowFrameM_ldS r owner pointer) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameX_xdoWhile {r : ZStreamRef} {owner : InflateStatePtr} {body : X Unit} {cond : X Bool}
    (hb : WindowFrameX r owner body) (hc : WindowFrameX r owner cond) : WindowFrameX r owner (xdoWhile body cond) :=
  windowFrameX_bind hb (fun _ => windowFrameX_xwhile hc hb)

theorem windowFrameX_xloopBrk {r : ZStreamRef} {owner : InflateStatePtr} {body : X Bool} (frame : WindowFrameX r owner body) :
    WindowFrameX r owner (xloopBrk body) := windowFrameX_xwhileBrk (windowFrameX_pure r owner true) frame

theorem windowFrameM_orderAt (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt32) : WindowFrameM r owner (orderAt index) := by
  unfold orderAt
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem decoderWindows_setI {h : Heap} {zs : Nat} {old state : InflateState}
    (get : h.istates zs = some old) (window : (counts state) = (counts old)) :
    decoderWindows (setI h zs state) = decoderWindows h := by
  funext b
  by_cases same : b = zs
  · subst b
    simp only [decoderWindows, setI_istates_same, get, Option.map_some, window]
  · simp only [decoderWindows, setI_istates_ne h zs b state same]

theorem decoderWindows_byte_put (h : Heap) (ref : BRef) (array : Array UInt8) :
    decoderWindows (Space.put h ref array) = decoderWindows h := by
  cases ref <;> simp only [Space.put]
  all_goals repeat' first | rfl | split

theorem decoderWindows_word_put (h : Heap) (ref : WRef) (array : Array UInt16) :
    decoderWindows (Space.put h ref array) = decoderWindows h := by
  cases ref with
  | blk b => rfl
  | dstate_bl_count b => cases get : h.dstates b <;> simp only [Space.put, get] <;> rfl
  | istate_lens b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderWindows_setI (state := { state with lens := array }) get rfl
  | istate_work b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderWindows_setI (state := { state with work := array }) get rfl

theorem decoderWindows_code_put (h : Heap) (ref : CodeRef) (array : Array Code) :
    decoderWindows (Space.put h ref array) = decoderWindows h := by
  cases ref with
  | st_lenfix => rfl
  | st_distfix => rfl
  | istate_codes b =>
    cases get : h.istates b with
    | none => simp only [Space.put, get]
    | some state =>
      simp only [Space.put, get]
      exact decoderWindows_setI (state := { state with codes := array }) get rfl

/-- A state-field store preserves every decoder window whenever its
actual field update preserves the previous pointer. -/
theorem windowFrameM_wrS (r : ZStreamRef) (owner : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ s, (counts (update s)) = (counts s)) :
    WindowFrameM r owner (wrS owner update) := by
  intro h value after run
  cases owner with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [wrI_eq] at run
      cases get : h.istates zs with
      | none => rw [get] at run; cases run
      | some state =>
        rw [get] at run
        cases run
        exact decoderWindows_setI get (window state)

theorem windowFrameM_wrZ (r : ZStreamRef) (owner : InflateStatePtr) (update : ZStream → ZStream) :
    WindowFrameM r owner (wrZ (some r) update) := by
  intro h value after run
  rw [wrZ_eq] at run
  cases get : r.get h with
  | none => rw [get] at run; cases run
  | some stream =>
    rw [get] at run
    cases run
    funext b
    simp only [decoderWindows, ZStreamRef.put_istates]

section pointers
variable {R T : Type} [Space Heap R T]

theorem windowFrameM_ptr_store (r : ZStreamRef) (owner : InflateStatePtr) (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), decoderWindows (Space.put h ref array) = decoderWindows h) :
    WindowFrameM r owner (p.store value) := by
  intro h result after run
  cases p with
  | null => cases run
  | ref ref off =>
    cases get : Space.get h ref with
    | none => simp only [Ptr.store, get] at run; cases run
    | some array =>
      simp only [Ptr.store, get] at run
      split at run
      · cases run
      · split at run
        · rw [Space.modify_eq h ref array _ get] at run
          cases run
          exact writes h ref _
        · cases run
end pointers

theorem windowFrameM_store8 (r : ZStreamRef) (owner : InflateStatePtr) (p : BPtr) (value : UInt8) :
    WindowFrameM r owner (store8 p value) := windowFrameM_ptr_store r owner p value decoderWindows_byte_put

theorem windowFrameM_store16 (r : ZStreamRef) (owner : InflateStatePtr) (p : WPtr) (value : UInt16) :
    WindowFrameM r owner (p.store value) := windowFrameM_ptr_store r owner p value decoderWindows_word_put

theorem windowFrameM_storeCode (r : ZStreamRef) (owner : InflateStatePtr) (p : CodePtr) (value : Code) :
    WindowFrameM r owner (p.store value) := windowFrameM_ptr_store r owner p value decoderWindows_code_put

/-- Every successful actual memcpy changes a byte view, which cannot
change a decoder window field. -/
theorem windowFrameM_memcpyB (r : ZStreamRef) (owner : InflateStatePtr) (destination source : BPtr) (count : Nat) :
    WindowFrameM r owner (memcpyB destination source count) := by
  intro h value after run
  cases destination with
  | null => cases run
  | ref dest off =>
    cases source with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first | cases run | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      repeat' first | split at run | (cases run <;> exact decoderWindows_byte_put h dest _)



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-! These source proofs establish the window-pointer frame for every successful
checksum execution. Fault freedom and checksum meaning are proved separately. -/

theorem windowFrameM_adler_do1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) (index : Int) :
    WindowFrameM r owner (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact windowFrameM_bind (windowFrameM_ptr_index r owner _ _) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_adler_do16 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    WindowFrameM r owner (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact windowFrameM_adler_do1 r owner _ _
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_adler_step (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    WindowFrameM r owner (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ => windowFrameM_pure r owner _))

theorem windowFrameM_adler32_z (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    WindowFrameM r owner (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact windowFrameM_adler_do16 r owner _
    | with_reducible exact windowFrameM_adler_step r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_adler32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (Zlib.Adler32.adler32 seed buffer length) := windowFrameM_adler32_z r owner seed buffer length.toUInt64

theorem windowFrameM_crc_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Crc32.shr64 value shift) := by
  unfold Zlib.Crc32.shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_crc_table (r : ZStreamRef) (owner : InflateStatePtr) (index : UInt64) : WindowFrameM r owner (Zlib.Crc32.crcTab index) :=
  windowFrameM_ptr_index r owner _ _

theorem windowFrameM_crc_idx1 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array α) (index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.idx1 table index) := by
  unfold Zlib.Crc32.idx1
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_crc_idx2 {α : Type} (r : ZStreamRef) (owner : InflateStatePtr) (table : Array (Array α)) (row index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.idx2 table row index) := by
  unfold Zlib.Crc32.idx2
  split
  · split
    · exact windowFrameM_pure r owner _
    · exact windowFrameM_ub r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_crc_address (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : WindowFrameM r owner (Zlib.Crc32.addrOf buffer) := by
  intro h value after run
  cases run
  exact WindowFrame.refl r owner h

theorem windowFrameM_crc_loadWord (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) : WindowFrameM r owner (Zlib.Crc32.loadWord buffer) := by
  unfold Zlib.Crc32.loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  refine windowFrameM_bind (windowFrameM_list_forIn r owner _ _ ?_ _) (fun _ => windowFrameM_pure r owner _)
  intro index membership state
  exact windowFrameM_bind (windowFrameM_ptr_index r owner _ _) (fun _ => windowFrameM_pure r owner _)

theorem windowFrameM_crc_word (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc_word word) := by
  unfold Zlib.Crc32.crc_word
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_word_big (r : ZStreamRef) (owner : InflateStatePtr) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc_word_big word) := by
  unfold Zlib.Crc32.crc_word_big
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_wordAt (r : ZStreamRef) (owner : InflateStatePtr) (buffer : BPtr) (index : Nat) :
    WindowFrameM r owner (Zlib.Crc32.wordAt buffer index) := by
  unfold Zlib.Crc32.wordAt
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_braid (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.braidTab index word) := by
  unfold Zlib.Crc32.braidTab
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_braid_big (r : ZStreamRef) (owner : InflateStatePtr) (index : Int32) (word : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.braidBigTab index word) := by
  unfold Zlib.Crc32.braidBigTab
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_block_little (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BL) :
    WindowFrameM r owner (Zlib.Crc32.blockLittle state) := by
  unfold Zlib.Crc32.blockLittle
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_block_big (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Crc32.BB) :
    WindowFrameM r owner (Zlib.Crc32.blockBig state) := by
  unfold Zlib.Crc32.blockBig
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_byte (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) :
    WindowFrameM r owner (Zlib.Crc32.crcByte seed buffer) := by
  unfold Zlib.Crc32.crcByte
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_crc_block_big r owner _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc_whole (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    WindowFrameM r owner (Zlib.Crc32.crc32_z seed buffer length) := by
  unfold Zlib.Crc32.crc32_z
  repeat' first
    | with_reducible exact windowFrameM_crc_shr64 r owner _ _
    | with_reducible exact windowFrameM_crc_table r owner _
    | with_reducible exact windowFrameM_crc_idx1 r owner _ _
    | with_reducible exact windowFrameM_crc_idx2 r owner _ _ _
    | with_reducible exact windowFrameM_crc_address r owner _
    | with_reducible exact windowFrameM_crc_loadWord r owner _
    | with_reducible exact windowFrameM_crc_word r owner _
    | with_reducible exact windowFrameM_crc_word_big r owner _
    | with_reducible exact windowFrameM_crc_wordAt r owner _ _
    | with_reducible exact windowFrameM_crc_braid r owner _ _
    | with_reducible exact windowFrameM_crc_braid_big r owner _ _
    | with_reducible exact windowFrameM_crc_block_little r owner _
    | with_reducible exact windowFrameM_crc_block_big r owner _
    | with_reducible exact windowFrameM_crc_byte r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

theorem windowFrameM_crc32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (Zlib.Crc32.crc32 seed buffer length) := windowFrameM_crc_whole r owner seed buffer length.toUInt64



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! The actual bit, lookup and metadata macros retain the window-pointer frame.
Every called primitive and checksum has a proved translated-body frame. -/

theorem windowFrameM_setMode (r : ZStreamRef) (owner : InflateStatePtr) (mode : UInt32) :
    WindowFrameM r owner (setMode owner mode) := windowFrameM_wrS r owner _ (fun _ => rfl)

theorem windowFrameM_setMsg (r : ZStreamRef) (owner : InflateStatePtr) (message : String) :
    WindowFrameM r owner (setMsg (some r) message) := by
  unfold setMsg
  exact windowFrameM_bind (windowFrameM_strLit r owner message) (fun _ => windowFrameM_wrZ r owner _)

theorem windowFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    WindowFrameM r context.st (badMode context message) := by
  unfold badMode
  rw [root]
  exact windowFrameM_bind (windowFrameM_setMsg r context.st message) (fun _ => windowFrameM_setMode r context.st _)

theorem windowFrameM_inflate_fixed (r : ZStreamRef) (owner : InflateStatePtr) :
    WindowFrameM r owner (Zlib.Inftrees.inflate_fixed owner) := by
  intro h value after run
  cases owner with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [Zlib.Inftrees.inflate_fixed, bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [Zlib.Inftrees.inflate_fixed, bind_app, ldI_eq, stI_eq, get,
          Option.isSome_some, ↓reduceIte, setI_istates_same, setI_setI] at run
        cases run
        exact decoderWindows_setI get rfl

theorem windowFrameX_RESTORE (r : ZStreamRef) (owner : InflateStatePtr) :
    WindowFrameX r owner (RESTORE (some r) owner) := by
  unfold RESTORE
  repeat' first
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible exact windowFrameM_wrS r owner _ (fun _ => rfl)
    | with_reducible apply windowFrameX_lift
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

theorem windowFrameM_UPDATE_CHECK (r : ZStreamRef) (owner : InflateStatePtr) (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    WindowFrameM r owner (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine windowFrameM_bind (windowFrameM_rdS r owner _ _) (fun flags => ?_)
  exact windowFrameM_ite (windowFrameM_crc32 r owner _ _ _) (windowFrameM_adler32 r owner _ _ _)

theorem windowFrameX_LOAD (r : ZStreamRef) (owner : InflateStatePtr) (strm : ZStreamPtr) (state : InflateStatePtr) : WindowFrameX r owner (LOAD strm state) := by
  unfold LOAD
  repeat' first
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_INITBITS (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (INITBITS) := by
  unfold INITBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_PULLBYTE (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (PULLBYTE) := by
  unfold PULLBYTE
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_NEEDBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (NEEDBITS count) := by
  unfold NEEDBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_BITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (BITS count) := by
  unfold BITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_DROPBITS (r : ZStreamRef) (owner : InflateStatePtr) (count : UInt32) : WindowFrameX r owner (DROPBITS count) := by
  unfold DROPBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_BYTEBITS (r : ZStreamRef) (owner : InflateStatePtr)  : WindowFrameX r owner (BYTEBITS) := by
  unfold BYTEBITS
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_lookup1 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : WindowFrameX r owner (lookup1 context distance) := by
  unfold lookup1
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_CRC4 r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

theorem windowFrameX_lookup2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) (distance : Bool) : WindowFrameX r owner (lookup2 context distance) := by
  unfold lookup2
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner _
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_CRC4 r owner _
    | with_reducible exact windowFrameX_lookup1 r owner _ _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A concrete load followed by its window-preserving state store retains
the global counter observation, before entering its actual remaining program. -/
theorem windowFrameM_ldS_update {α : Type} (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (next : InflateState → M α)
    (window : ∀ state, (counts (update state)) = (counts state))
    (tailFrame : ∀ state, WindowFrameM r owner (next state)) :
    WindowFrameM r owner (do
      let state ← ldInflateState pointer
      stInflateState pointer (update state)
      next state) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [bind_app, ldI_eq, stI_eq, get, Option.isSome_some, ↓reduceIte] at run
        exact (show WindowFrame r owner h (setI h zs (update state)) from
          decoderWindows_setI get (window state)).trans
          (tailFrame state _ value after run)

theorem windowFrameM_ldS_store (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, (counts (update state)) = (counts state)) :
    WindowFrameM r owner (do
      let state ← ldInflateState pointer
      stInflateState pointer (update state)) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      cases get : h.istates zs with
      | none => simp only [bind_app, ldI_eq, get] at run; cases run
      | some state =>
        simp only [bind_app, ldI_eq, stI_eq, get, Option.isSome_some, ↓reduceIte] at run
        cases run
        exact decoderWindows_setI get (window state)

theorem windowFrameM_wrS_any (r : ZStreamRef) (owner pointer : InflateStatePtr)
    (update : InflateState → InflateState) (window : ∀ state, (counts (update state)) = (counts state)) :
    WindowFrameM r owner (wrS pointer update) := windowFrameM_wrS r pointer update window

theorem windowFrameM_stZ (r : ZStreamRef) (owner : InflateStatePtr) (pointer : ZStreamPtr) (stream : ZStream) :
    WindowFrameM r owner (stZStream pointer stream) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some root =>
    rw [stZ_eq] at run
    split at run
    · cases run
      funext b
      simp only [decoderWindows, ZStreamRef.put_istates]
    · cases run



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem windowFrameM_table_chk32 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shr32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_shl1i32 (r : ZStreamRef) (owner : InflateStatePtr) (shift : UInt32) : WindowFrameM r owner (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_geta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) : WindowFrameM r owner (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact windowFrameM_pure r owner _
  · exact windowFrameM_ub r owner _

theorem windowFrameM_table_seta (r : ZStreamRef) (owner : InflateStatePtr) (array : Array UInt16) (index : Nat) (value : UInt16) :
    WindowFrameM r owner (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_table_storeCode (r : ZStreamRef) (owner : InflateStatePtr) (pointer : CodePtr) (index : Nat) (value : Code) :
    WindowFrameM r owner (Zlib.Inftrees.storeCode pointer index value) :=
  windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun next => windowFrameM_storeCode r owner next value)

/-- Every successful actual constructor step preserves every decoder saved-window counter. Bounds, termination and table meaning are separate proved
obligations, rather than contracts assumed by this frame proof. -/
theorem windowFrameM_table_buildStep (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    WindowFrameM r owner (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  repeat' first
    | with_reducible exact windowFrameM_table_chk32 r owner _
    | with_reducible exact windowFrameM_table_shl32 r owner _ _
    | with_reducible exact windowFrameM_table_shr32 r owner _ _
    | with_reducible exact windowFrameM_table_shl1i32 r owner _
    | with_reducible exact windowFrameM_table_geta r owner _ _
    | with_reducible exact windowFrameM_table_seta r owner _ _ _
    | with_reducible exact windowFrameM_table_storeCode r owner _ _ _
    | with_reducible exact windowFrameM_store16 r owner _ _
    | with_reducible exact windowFrameM_storeCode r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- The complete actual dynamic-table constructor preserves fixed stream
fields across all alphabets, partial writes and rejection returns. -/
theorem windowFrameM_inflate_table (r : ZStreamRef) (owner : InflateStatePtr) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    WindowFrameM r owner (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  repeat' first
    | with_reducible exact windowFrameM_table_buildStep r owner _ _
    | with_reducible exact windowFrameM_table_chk32 r owner _
    | with_reducible exact windowFrameM_table_shl32 r owner _ _
    | with_reducible exact windowFrameM_table_shr32 r owner _ _
    | with_reducible exact windowFrameM_table_shl1i32 r owner _
    | with_reducible exact windowFrameM_table_geta r owner _ _
    | with_reducible exact windowFrameM_table_seta r owner _ _ _
    | with_reducible exact windowFrameM_table_storeCode r owner _ _ _
    | with_reducible exact windowFrameM_store16 r owner _ _
    | with_reducible exact windowFrameM_storeCode r owner _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem windowFrameM_fast_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : WindowFrameM r owner (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : WindowFrameM r owner (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_chk64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : WindowFrameM r owner (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact windowFrameM_ite (windowFrameM_pure r owner _) (windowFrameM_ub r owner _)

theorem windowFrameM_fast_subn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : BPtr) (count : UInt32) : WindowFrameM r owner (Zlib.Inffast.subn pointer count) :=
  windowFrameM_ptr_add r owner _ _

theorem windowFrameM_fast_pull (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ =>
      windowFrameM_bind (windowFrameM_fast_shl64 r owner _ _) (fun _ => windowFrameM_pure r owner _)))

theorem windowFrameM_fast_copy1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact windowFrameM_bind (windowFrameM_ptr_load r owner _) (fun _ =>
    windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ =>
      windowFrameM_bind (windowFrameM_store8 r owner _ _) (fun _ =>
        windowFrameM_bind (windowFrameM_ptr_add r owner _ _) (fun _ => windowFrameM_pure r owner _))))

theorem windowFrameM_fast_copyOp (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : WindowFrameM r owner (Zlib.Inffast.copyOp state) :=
  windowFrameM_cdoWhile (windowFrameM_fast_copy1 r owner) (fun _ => windowFrameM_pure r owner _) state

/-- Actual fast-decoder diagnostics retain the decoder saved-window counters. -/
theorem windowFrameM_fast_badData (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : WindowFrameM r owner (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  repeat' first
    | with_reducible exact windowFrameM_strLit r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_stZ r owner _ _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_bind ?_ (fun _ => ?_)

/-- Successful actual fast copyMatch execution preserves decoder saved-window counters. -/
theorem windowFrameM_fast_copyMatch (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves decoder saved-window counters. -/
theorem windowFrameM_fast_dodist (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves decoder saved-window counters. -/
theorem windowFrameM_fast_dolen (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_fast_dodist r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves decoder saved-window counters. -/
theorem windowFrameM_fast_body (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    WindowFrameM r owner (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact windowFrameM_fast_badData r owner _ root _
    | with_reducible exact windowFrameM_fast_copyOp r owner _
    | with_reducible exact windowFrameM_fast_copy1 r owner _
    | with_reducible exact windowFrameM_fast_pull r owner _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_shl64 r owner _ _
    | with_reducible exact windowFrameM_fast_shr64 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact windowFrameM_fast_dodist r owner _ root _
    | with_reducible exact windowFrameM_fast_dolen r owner _ root _
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible (refine windowFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves decoder saved-window counters, through its actual record writes, on every successful run. -/
theorem windowFrameM_inflate_fast (r : ZStreamRef) (owner : InflateStatePtr) (start : UInt32) :
    WindowFrameM r owner (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact windowFrameM_fast_body r owner _ rfl _
    | with_reducible exact windowFrameM_fast_subn r owner _ _
    | with_reducible exact windowFrameM_fast_shl32 r owner _ _
    | with_reducible exact windowFrameM_fast_chk64 r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine windowFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact windowFrameM_castI r owner _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_ptr_diff r owner _ _
    | with_reducible exact windowFrameM_ptr_lt r owner _ _
    | with_reducible exact windowFrameM_pure r owner _
    | with_reducible exact windowFrameM_ub r owner _
    | with_reducible exact windowFrameM_stZ r owner _ _
    | with_reducible (refine windowFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply windowFrameM_ite
    | with_reducible (refine windowFrameM_bind ?_ (fun _ => ?_))
    | rfl



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A header record write cannot change an inflate state pointer. -/
theorem windowFrameM_stHeader (r : ZStreamRef) (owner : InflateStatePtr) (pointer : GzHeaderPtr) (header : GzHeader) :
    WindowFrameM r owner (stGzHeader pointer header) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab id =>
      simp only [stGzHeader, GzHeaderRef.get, GzHeaderRef.isRo, Bool.false_eq_true, ↓reduceIte] at run
      cases get : h.gzheaders id with
      | none => rw [get] at run; cases run
      | some old =>
        rw [get] at run
        cases run
        simp only [WindowFrame, GzHeaderRef.put, get]
        rfl

theorem windowFrameX_CRC2 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : WindowFrameX r owner (CRC2 context) := by
  unfold CRC2
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl

/-- The actual CRC4 source macro preserves decoder saved-window counters. -/
theorem windowFrameX_CRC4 (r : ZStreamRef) (owner : InflateStatePtr) (context : Ctx) : WindowFrameX r owner (CRC4 context) := by
  unfold CRC4
  repeat' first
    | with_reducible exact windowFrameX_LOAD r owner _ _
    | with_reducible exact windowFrameX_RESTORE r owner
    | with_reducible exact windowFrameX_INITBITS r owner
    | with_reducible exact windowFrameX_PULLBYTE r owner
    | with_reducible exact windowFrameX_NEEDBITS r owner _
    | with_reducible exact windowFrameX_BITS r owner _
    | with_reducible exact windowFrameX_DROPBITS r owner _
    | with_reducible exact windowFrameX_BYTEBITS r owner
    | with_reducible exact windowFrameX_CRC2 r owner _
    | with_reducible exact windowFrameX_pure r owner _
    | with_reducible exact windowFrameX_get r owner
    | with_reducible exact windowFrameX_set r owner _
    | with_reducible exact windowFrameX_modify r owner _
    | with_reducible exact windowFrameX_throw r owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_ldS r owner _
    | with_reducible exact windowFrameM_ldZ r owner _
    | with_reducible exact windowFrameM_rdS r owner _ _
    | with_reducible exact windowFrameM_rdZ r owner _ _
    | with_reducible exact windowFrameM_wrS_any r owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_store8 r owner _ _
    | with_reducible exact windowFrameM_crc32 r owner _ _ _
    | with_reducible exact windowFrameM_ptr_load r owner _
    | with_reducible exact windowFrameM_ptr_index r owner _ _
    | with_reducible exact windowFrameM_ptr_add r owner _ _
    | with_reducible exact windowFrameM_shl32 r owner _ _
    | with_reducible exact windowFrameM_shr32 r owner _ _
    | with_reducible exact windowFrameM_shl64 r owner _ _
    | with_reducible exact windowFrameM_shr64 r owner _ _
    | with_reducible exact windowFrameM_wrZ r owner _
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xloopBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl



open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Compose proved source frames through the monadic mode syntax. Each
mode supplies its actual continuation as a checked local theorem. -/
macro "window_pointer_frame_mode " r:term:max "," owner:term:max "," root:term:max : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact windowFrameX_LOAD $r $owner _ _
    | with_reducible exact windowFrameX_RESTORE $r $owner
    | with_reducible exact windowFrameX_INITBITS $r $owner
    | with_reducible exact windowFrameX_PULLBYTE $r $owner
    | with_reducible exact windowFrameX_NEEDBITS $r $owner _
    | with_reducible exact windowFrameX_BITS $r $owner _
    | with_reducible exact windowFrameX_DROPBITS $r $owner _
    | with_reducible exact windowFrameX_BYTEBITS $r $owner
    | with_reducible exact windowFrameX_CRC2 $r $owner _
    | with_reducible exact windowFrameX_CRC4 $r $owner _
    | with_reducible exact windowFrameX_lookup1 $r $owner _ _
    | with_reducible exact windowFrameX_lookup2 $r $owner _ _
    | with_reducible exact windowFrameX_pure $r $owner _
    | with_reducible exact windowFrameX_get $r $owner
    | with_reducible exact windowFrameX_set $r $owner _
    | with_reducible exact windowFrameX_modify $r $owner _
    | with_reducible exact windowFrameX_throw $r $owner _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_inflate_table $r $owner _ _ _ _ _ _
    | with_reducible exact windowFrameM_inflate_fixed $r $owner
    | with_reducible exact windowFrameM_inflate_fast $r $owner _
    | with_reducible exact windowFrameM_UPDATE_CHECK $r $owner _ _ _ _
    | with_reducible exact windowFrameM_crc32 $r $owner _ _ _
    | with_reducible exact windowFrameM_adler32 $r $owner _ _ _
    | with_reducible exact windowFrameM_ldHeader $r $owner _
    | with_reducible exact windowFrameM_stHeader $r $owner _ _
    | with_reducible exact windowFrameM_ldS $r $owner _
    | with_reducible exact windowFrameM_ldZ $r $owner _
    | with_reducible exact windowFrameM_rdS $r $owner _ _
    | with_reducible exact windowFrameM_rdZ $r $owner _ _
    | with_reducible exact windowFrameM_wrS_any $r $owner _ _ (fun _ => rfl)
    | with_reducible exact windowFrameM_setMode $r $owner _
    | with_reducible exact windowFrameM_setMsg $r $owner _
    | with_reducible exact windowFrameM_badMode $r _ $root _
    | with_reducible exact windowFrameM_hcrcOn $r $owner _
    | with_reducible exact windowFrameM_orderAt $r $owner _
    | with_reducible exact windowFrameM_store8 $r $owner _ _
    | with_reducible exact windowFrameM_store16 $r $owner _ _
    | with_reducible exact windowFrameM_storeCode $r $owner _ _
    | with_reducible exact windowFrameM_memcpyB $r $owner _ _ _
    | with_reducible exact windowFrameM_ptr_load $r $owner _
    | with_reducible exact windowFrameM_ptr_index $r $owner _ _
    | with_reducible exact windowFrameM_ptr_add $r $owner _ _
    | with_reducible exact windowFrameM_ptr_diff $r $owner _ _
    | with_reducible exact windowFrameM_shl32 $r $owner _ _
    | with_reducible exact windowFrameM_shr32 $r $owner _ _
    | with_reducible exact windowFrameM_shl64 $r $owner _ _
    | with_reducible exact windowFrameM_shr64 $r $owner _ _
    | with_reducible exact windowFrameM_chkI32 $r $owner _
    | with_reducible exact windowFrameM_chkI64 $r $owner _
    | with_reducible exact windowFrameM_wrZ $r $owner _
    | with_reducible apply windowFrameX_xdoWhile
    | with_reducible apply windowFrameX_xwhile
    | with_reducible apply windowFrameX_xwhileBrk
    | with_reducible apply windowFrameX_ite
    | with_reducible (refine windowFrameX_bind ?_ (fun _ => ?_))
    | rfl
    | split)

/-- The actual DONE mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DONE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DONE context) := by
  unfold inflate_DONE
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual LENGTH mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  try rw [root]
  have continuation0 := windowFrameX_inflate_DONE r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual CHECK mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_CHECK (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_CHECK context) := by
  unfold inflate_CHECK
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENGTH r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LIT mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LIT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LIT context) := by
  unfold inflate_LIT
  try rw [root]
  window_pointer_frame_mode r, context.st, root

set_option maxHeartbeats 800000 in
/-- The actual MATCH mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_MATCH (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_MATCH context) := by
  unfold inflate_MATCH
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual DISTEXT mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  try rw [root]
  have continuation0 := windowFrameX_inflate_MATCH r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DIST mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DIST (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DIST context) := by
  unfold inflate_DIST
  try rw [root]
  have continuation0 := windowFrameX_inflate_DISTEXT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LENEXT mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  try rw [root]
  have continuation0 := windowFrameX_inflate_DIST r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LEN mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LEN context) := by
  unfold inflate_LEN
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENEXT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LEN_ mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LEN_ context) := by
  unfold inflate_LEN_
  try rw [root]
  have continuation0 := windowFrameX_inflate_LEN r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual CODELENS mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  try rw [root]
  have continuation0 := windowFrameX_inflate_LEN_ r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual LENLENS mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  try rw [root]
  have continuation0 := windowFrameX_inflate_CODELENS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TABLE mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TABLE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TABLE context) := by
  unfold inflate_TABLE
  try rw [root]
  have continuation0 := windowFrameX_inflate_LENLENS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual COPY mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COPY (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COPY context) := by
  unfold inflate_COPY
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual COPY_ mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COPY_ context) := by
  unfold inflate_COPY_
  try rw [root]
  have continuation0 := windowFrameX_inflate_COPY r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual STORED mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_STORED (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_STORED context) := by
  unfold inflate_STORED
  try rw [root]
  have continuation0 := windowFrameX_inflate_COPY_ r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TYPEDO mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual TYPE mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TYPE (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TYPE context) := by
  unfold inflate_TYPE
  try rw [root]
  have continuation0 := windowFrameX_inflate_TYPEDO r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DICT mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DICT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DICT context) := by
  unfold inflate_DICT
  try rw [root]
  have continuation0 := windowFrameX_inflate_TYPE r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual DICTID mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_DICTID context) := by
  unfold inflate_DICTID
  rw [root]
  refine windowFrameX_bind (windowFrameX_NEEDBITS r context.st 32) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_get r context.st) (fun registers => ?_)
  refine windowFrameX_bind (windowFrameX_lift
    (windowFrameM_wrS_any r context.st context.st
      (fun state => { state with check := ZSWAP32 registers.hold }) (fun _ => rfl))) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_lift (windowFrameM_wrZ r context.st
    (fun stream => { stream with adler := ZSWAP32 registers.hold }))) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_INITBITS r context.st) (fun _ => ?_)
  refine windowFrameX_bind (windowFrameX_lift (windowFrameM_setMode r context.st DICT)) (fun _ => ?_)
  exact windowFrameX_inflate_DICT r context root

/-- The actual HCRC mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_HCRC context) := by
  unfold inflate_HCRC
  try rw [root]
  window_pointer_frame_mode r, context.st, root

/-- The actual COMMENT mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  try rw [root]
  have continuation0 := windowFrameX_inflate_HCRC r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual NAME mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_NAME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_NAME context) := by
  unfold inflate_NAME
  try rw [root]
  have continuation0 := windowFrameX_inflate_COMMENT r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual EXTRA mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  try rw [root]
  have continuation0 := windowFrameX_inflate_NAME r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual EXLEN mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  try rw [root]
  have continuation0 := windowFrameX_inflate_EXTRA r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual OS mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_OS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_OS context) := by
  unfold inflate_OS
  try rw [root]
  have continuation0 := windowFrameX_inflate_EXLEN r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual TIME mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_TIME (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_TIME context) := by
  unfold inflate_TIME
  try rw [root]
  have continuation0 := windowFrameX_inflate_OS r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual FLAGS mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  try rw [root]
  have continuation0 := windowFrameX_inflate_TIME r context root
  window_pointer_frame_mode r, context.st, root

/-- The actual HEAD mode preserves decoder saved-window counters on every successful
run, including its source fallthrough and explicit control exits. -/
theorem windowFrameX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) :
    WindowFrameX r context.st (inflate_HEAD context) := by
  unfold inflate_HEAD
  try rw [root]
  window_pointer_frame_mode r, context.st, root



open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dispatcher retains decoder saved-window counters for every selected
mode, including error returns and configurations outside the default route. -/
theorem windowFrameX_inflate_dispatch (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : WindowFrameX r context.st (inflate_dispatch context) := by
  unfold inflate_dispatch
  refine windowFrameX_bind (windowFrameX_lift (windowFrameM_rdS r context.st _ _)) (fun mode => ?_)
  repeat' first
    | with_reducible exact windowFrameX_inflate_HEAD r context root
    | with_reducible exact windowFrameX_inflate_FLAGS r context root
    | with_reducible exact windowFrameX_inflate_TIME r context root
    | with_reducible exact windowFrameX_inflate_OS r context root
    | with_reducible exact windowFrameX_inflate_EXLEN r context root
    | with_reducible exact windowFrameX_inflate_EXTRA r context root
    | with_reducible exact windowFrameX_inflate_NAME r context root
    | with_reducible exact windowFrameX_inflate_COMMENT r context root
    | with_reducible exact windowFrameX_inflate_HCRC r context root
    | with_reducible exact windowFrameX_inflate_DICTID r context root
    | with_reducible exact windowFrameX_inflate_DICT r context root
    | with_reducible exact windowFrameX_inflate_TYPE r context root
    | with_reducible exact windowFrameX_inflate_TYPEDO r context root
    | with_reducible exact windowFrameX_inflate_STORED r context root
    | with_reducible exact windowFrameX_inflate_COPY_ r context root
    | with_reducible exact windowFrameX_inflate_COPY r context root
    | with_reducible exact windowFrameX_inflate_TABLE r context root
    | with_reducible exact windowFrameX_inflate_LENLENS r context root
    | with_reducible exact windowFrameX_inflate_CODELENS r context root
    | with_reducible exact windowFrameX_inflate_LEN_ r context root
    | with_reducible exact windowFrameX_inflate_LEN r context root
    | with_reducible exact windowFrameX_inflate_LENEXT r context root
    | with_reducible exact windowFrameX_inflate_DIST r context root
    | with_reducible exact windowFrameX_inflate_DISTEXT r context root
    | with_reducible exact windowFrameX_inflate_MATCH r context root
    | with_reducible exact windowFrameX_inflate_LIT r context root
    | with_reducible exact windowFrameX_inflate_CHECK r context root
    | with_reducible exact windowFrameX_inflate_LENGTH r context root
    | with_reducible exact windowFrameX_inflate_DONE r context root
    | with_reducible exact windowFrameX_throw r context.st _
    | with_reducible exact windowFrameX_modify r context.st _
    | with_reducible exact windowFrameX_pure r context.st _
    | with_reducible apply windowFrameX_ite
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

/-- The actual entry normalization, LOAD and complete mode loop preserve
the exact decoder saved-window counters. Every callee frame is proved
about its translated body. -/
theorem windowFrameX_inflate_run (r : ZStreamRef) (context : Ctx)
    (root : context.strm = some r) : WindowFrameX r context.st (inflate_run context) := by
  unfold inflate_run
  repeat' first
    | with_reducible exact windowFrameX_inflate_dispatch r context root
    | with_reducible exact windowFrameX_LOAD r context.st _ _
    | with_reducible exact windowFrameX_modify r context.st _
    | with_reducible exact windowFrameX_pure r context.st _
    | with_reducible apply windowFrameX_lift
    | with_reducible exact windowFrameM_rdS r context.st _ _
    | with_reducible exact windowFrameM_setMode r context.st _
    | with_reducible apply windowFrameX_ite
    | with_reducible apply windowFrameX_xwhile
    | with_reducible refine windowFrameX_bind ?_ (fun _ => ?_)

/-- The window used after the actual complete mode loop is precisely its
incoming pointer. Allocation shape alone is not used to infer ownership. -/
theorem inflate_run_window_unchanged {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (root : c.strm = some r) (before : h.istates zs = some s) (get : after.istates zs = some state)
    (run : runX (inflate_run c) l h = .ok ((outcome, regs), after)) : (counts state) = (counts s) := by
  have fixed := windowFrameX_inflate_run r c root l h outcome regs after run
  have selected := congrFun fixed zs
  change (after.istates zs).map counts = (h.istates zs).map counts at selected
  rw [get, before] at selected
  exact Option.some.inj selected

#print axioms inflate_run_window_unchanged

end Zlib.Inflate.Proofs.WindowCounts


namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete source run retains all three saved-window counts,
including direct returns and every header, slow and fast payload case. -/
theorem inflate_run_window_counters
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (root : c.strm = some r) (before : h.istates zs = some s)
    (get : after.istates zs = some state)
    (run : runX (inflate_run c) l h = .ok ((outcome, regs), after)) :
    state.wsize = s.wsize ∧ state.whave = s.whave ∧ state.wnext = s.wnext := by
  have equal := WindowCounts.inflate_run_window_unchanged root before get run
  exact ⟨congrArg Prod.fst equal, congrArg (fun x => x.2.1) equal,
    congrArg (fun x => x.2.2) equal⟩

/-- The real complete run can write caller output but cannot alter its
separate owned saved-window byte array. The exact output frame is derived
from the translated run theorem rather than required as a callee premise. -/
theorem inflate_run_window_contents
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s)) (facts : CallFrameFacts c h r zs z s)
    (run : runX (inflate_run c) IL.init h = .ok ((outcome, regs), after)) :
    ∀ w a, s.window = .ref (.blk w) 0 → h.bytes w = some a → after.bytes w = some a := by
  obtain ⟨bs, exit, otherRegs, otherHeap, stream, state, used, made, _bound,
    source, _current, ⟨_, _, _packet⟩, _, _bits, _sizes, _next, _inputCount, _put, _left, _metadata, _head,
    frame⟩ := inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid local_ facts
  have same : ((Except.error exit, otherRegs), otherHeap) = ((outcome, regs), after) :=
    Except.ok.inj (source.symm.trans run)
  cases same
  intro w a window windowGet
  exact BufferFrame.view_kept frame (fun root => facts.window_root window root.head_length)
    (Or.inl ⟨w, rfl, facts.window w window⟩) windowGet

/-- A previously established chronological saved history survives the
actual complete mode loop, through its real output writes. This is the
producer needed before applying inflate_leave_history. -/
theorem inflate_run_history_preserved
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {regs : IL} {outcome : Except Ex Unit}
    {history : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((outcome, regs), after))
    (current : DefaultStateJ after r zs stream state)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    InflateDictionary after state (history.drop (history.length - 2 ^ state.wbits.toNat)) := by
  have windowEq := Zlib.Inflate.Proofs.inflate_run_window_unchanged E.strm E.hs current.good.live.hs run
  obtain ⟨sizeEq, haveEq, nextEq⟩ :=
    inflate_run_window_counters E.strm E.hs current.good.live.hs run
  rcases invariant.good.inv.win.block with null | ⟨w, a, window, get, _readonly, size⟩
  · rcases stored with ⟨zero, empty⟩ | ⟨ref, off, array, pointer, _⟩
    · have nil : history = [] := by
        have positive : 0 < 2 ^ s.wbits.toNat := Nat.two_pow_pos _
        have length := congrArg List.length empty
        simp only [List.length_drop, List.length_nil] at length
        exact List.length_eq_zero_iff.mp (by omega)
      subst nil
      exact Or.inl ⟨haveEq.trans zero, by simp⟩
    · rw [null] at pointer
      cases pointer
  · have nextGet := inflate_run_window_contents E invariant buffers nonnull inputValid local_ run w a window get
    have pointer : state.window = .ref (.blk w) 0 := windowEq.trans window
    have bitsEq : state.wbits = s.wbits := by
      rcases current.good.inv.win.block with absent | ⟨w', a', window', get', _, size'⟩
      · rw [pointer] at absent
        cases absent
      · rw [pointer] at window'
        cases window'
        rw [nextGet] at get'
        cases get'
        have powers : 2 ^ state.wbits.toNat = 2 ^ s.wbits.toNat := size'.symm.trans size
        apply UInt32.toNat_inj.mp
        rcases Nat.lt_trichotomy state.wbits.toNat s.wbits.toNat with less | equal | greater
        · have := Nat.pow_lt_pow_right (by decide : 1 < 2) less
          omega
        · exact equal
        · have := Nat.pow_lt_pow_right (by decide : 1 < 2) greater
          omega
    apply (dictionary_eq_saved current.good pointer nextGet (by rw [bitsEq]; exact size)).mpr
    simpa only [bitsEq, sizeEq, haveEq, nextEq] using
      ((dictionary_eq_saved invariant.good window get size).mp stored)

/-- Starting from the ghost old-history clause, actual source execution
supplies the unchanged physical saved ring at the complete loop boundary.
No physical array, counter frame or post-history premise is requested. -/
theorem inflate_run_history_saved
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {history : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ (bs : List UInt8), ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      regs.bits.toNat ≤ 39 ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat ∧
      state.window = s.window ∧ state.wsize = s.wsize ∧ state.whave = s.whave ∧ state.wnext = s.wnext ∧
      InflateDictionary after state (history.drop (history.length - 2 ^ state.wbits.toNat)) ∧
      ((state.window = .null ∧ state.whave = 0 ∧
          history.drop (history.length - 2 ^ state.wbits.toNat) = []) ∨
        ∃ w a, state.window = .ref (.blk w) 0 ∧ after.bytes w = some a ∧ after.ro w = false ∧
          a.size = 2 ^ state.wbits.toNat ∧
          Zlib.Inffast.Spec.MatchHistory.saved a state.wsize.toNat state.wnext.toNat state.whave.toNat 0 =
            history.drop (history.length - 2 ^ state.wbits.toNat)) := by
  obtain ⟨bs, exit, regs, after, stream, state, used, made, bound,
    run, current, packet, _, bits, _sizes, next, inputCount, put, left⟩ :=
    inflate_run_default_view E invariant buffers nonnull inputValid local_
  have dictionary := inflate_run_history_preserved E invariant buffers nonnull inputValid local_ run current stored
  obtain ⟨sizeEq, haveEq, nextEq⟩ :=
    inflate_run_window_counters E.strm E.hs current.good.live.hs run
  exact ⟨bs, exit, regs, after, stream, state, used, made, bound, run, current, packet,
    bits, next, inputCount, put, left,
    Zlib.Inflate.Proofs.inflate_run_window_unchanged E.strm E.hs current.good.live.hs run,
    sizeEq, haveEq, nextEq, dictionary, dictionary_saved_or_lazy current.good dictionary⟩

#print axioms inflate_run_window_counters
#print axioms inflate_run_window_contents
#print axioms inflate_run_history_preserved
#print axioms inflate_run_history_saved
end Zlib.Inflate.Proofs.WindowHistory
