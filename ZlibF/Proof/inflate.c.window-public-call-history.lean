import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.window-physical-history»
import ZlibF.Proof.«inflate.c.need-dict-sourcecut»
import ZlibF.Proof.«inflate.c.wrapper-output-credit»
import ZlibF.Spec.Public.Sequences

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem bytes_unique {h : Heap} {p : BPtr} {n : Nat} {xs ys : List UInt8}
    (one : Bytes h p n xs) (two : Bytes h p n ys) : xs = ys := by
  rcases one with ⟨null, _zero, empty⟩ | ⟨ref, off, array, pointer, get, _bound, values⟩
  · rcases two with ⟨_null, _zero, empty2⟩ | ⟨_ref, _off, _array, pointer, _⟩
    · exact empty.trans empty2.symm
    · rw [null] at pointer
      cases pointer
  · cases pointer
    rcases two with ⟨null, _⟩ | ⟨ref2, off2, array2, pointer, get2, _bound2, values2⟩
    · cases null
    · cases pointer
      have same : array = array2 := Option.some.inj (get.symm.trans get2)
      subst array2
      exact values.trans values2.symm

theorem inputAdvance_injective {p q : BPtr} {count : Nat}
    (equal : inputAdvance p count = inputAdvance q count) : p = q := by
  cases p with
  | null => cases q with
    | null => rfl
    | ref ref off => cases equal
  | ref ref off => cases q with
    | null => cases equal
    | ref ref2 off2 =>
      obtain ⟨sameRef, sameOff⟩ := Ptr.ref.inj equal
      have same : off = off2 := Nat.add_right_cancel sameOff
      cases sameRef
      cases same
      rfl

theorem dictionary_syncAlloc
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} (invariant : DefaultStateJ h r zs z s)
    (stored : InflateDictionary h s history) : InflateDictionary (syncAlloc h) s history := by
  rcases invariant.good.inv.win.block with null | ⟨w, a, window, get, _readonly, size⟩
  · rcases stored with empty | ⟨ref, off, array, pointer, _⟩
    · exact Or.inl empty
    · rw [null] at pointer
      cases pointer
  · have current := default_state_syncAlloc invariant
    have nextGet := (byte_view_syncAlloc (ref := .blk w) invariant.good.fresh get).1
    exact (dictionary_eq_saved current.good window nextGet size).mpr
      ((dictionary_eq_saved invariant.good window get size).mp stored)

theorem dictionary_free_local
    {h : Heap} {r : ZStreamRef} {zs block : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} {array : Array UInt8} (invariant : DefaultStateJ h r zs z s)
    (localGet : h.bytes block = some array) (localSize : array.size = 4)
    (stored : InflateDictionary h s history) :
    InflateDictionary (freeWin h (.ref (.blk block) 0)) s history := by
  rcases invariant.good.inv.win.block with null | ⟨w, a, window, get, _readonly, size⟩
  · rcases stored with empty | ⟨ref, off, bytes, pointer, _⟩
    · exact Or.inl empty
    · rw [null] at pointer
      cases pointer
  · have other : block ≠ w := by
      intro equal
      subst w
      rcases invariant.local_width with bits | none
      · exact default_local_not_window invariant.good localGet localSize bits window
      · rw [none] at window
        cases window
    have kept := freeWin_bytes_ne h (.ref (.blk block) 0) (b := w)
      (by intro w2 pointer; cases pointer; exact other)
    have current := invariant.free_local localGet localSize
    exact (dictionary_eq_saved current.good window (kept.1.trans get) size).mpr
      ((dictionary_eq_saved invariant.good window get size).mp stored)

theorem leave_active_origin
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after))
    (get : after.istates zs = some state) (active : state.mode < CHECK) (lowOut : s.mode ≤ DICT → l.out_ = l.left) : s.mode < CHECK := by
  obtain ⟨otherRc, otherHeap, stream, current, source, final, _alloc, _next, _have, _put, _left, outcome⟩ :=
    inflate_leave_default_public_accounting E invariant allocator buffers bits lowOut
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have stateEq : current = state := Option.some.inj (final.good.live.hs.symm.trans get)
  subst current
  rcases outcome with ⟨_code, _fields, mode⟩ | ⟨_code, mem, _fields⟩
  · simpa only [mode] using active
  · rw [mem] at active
    exact False.elim ((by decide : ¬ MEM < CHECK) active)

#print axioms bytes_unique
#print axioms inputAdvance_injective
#print axioms dictionary_syncAlloc
#print axioms dictionary_free_local
#print axioms leave_active_origin

/-- On the actual ordinary-leave source cut, chronological history grows
by exactly the output observed from the original caller buffer. The
whole loop establishes the old dictionary and the unre-based output base. -/
theorem local_leave_history_observed
    {c : Ctx} {h loopHeap after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {regs : IL} {rc : Int32}
    {history output : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (loop : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), loopHeap))
    (leave : inflate_leave c regs loopHeap = .ok (rc, after))
    (finalGood : Good after r zs stream state)
    (observed : Bytes after z.next_out (z.avail_out.toNat - stream.avail_out.toNat) output)
    (stored : s.mode < CHECK → InflateDictionary h s
      (history.drop (history.length - 2 ^ s.wbits.toNat)))
    (active : state.mode < CHECK) :
    InflateDictionary after state
      ((history ++ output).drop ((history ++ output).length - 2 ^ state.wbits.toNat)) := by
  obtain ⟨bs, exit, otherRegs, otherHeap, loopZ, loopS, used, made, _bound,
    source, current, ⟨_, _, packet⟩, _, bits, _sizes, _next, _count, put, left, _metadata, _frame⟩ :=
    inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid local_
  have same := Except.ok.inj (source.symm.trans loop)
  cases same
  have loopEnv : Env c loopHeap r zs loopZ loopS :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have fixed := streamFrameX_inflate_run r c E.strm IL.init h (.error Ex.leave) regs loopHeap loop
  have loopAllocator := fixed.allocator E.hz current.good.live.hz allocator
  have oldDictionary : loopS.mode < CHECK → InflateDictionary loopHeap loopS
      (history.drop (history.length - 2 ^ loopS.wbits.toNat)) := by
    intro loopActive
    have origin := ActiveSourceCut.run_active_base E invariant buffers nonnull inputValid local_ loop
      current.good.live.hs loopActive
    exact inflate_run_history_preserved E invariant buffers nonnull inputValid local_ loop current (stored origin.1)
  obtain ⟨otherRc, otherAfter, finalZ, finalS, base, emitted, actual, final, _alloc,
    _nextIn, _haveIn, nextOut, leftOut, advance, _length, _beforeBytes, afterBytes, dictionary⟩ :=
    inflate_leave_history loopEnv current loopAllocator packet bits oldDictionary
      (inflate_run_default_low_out E invariant buffers nonnull inputValid local_ loop current.good.live.hs)
  have sameLeave := Except.ok.inj (actual.symm.trans leave)
  cases sameLeave
  have sameZ : finalZ = stream := Option.some.inj (final.good.live.hz.symm.trans finalGood.live.hz)
  have sameS : finalS = state := Option.some.inj (final.good.live.hs.symm.trans finalGood.live.hs)
  subst finalZ finalS
  have loopActive := leave_active_origin loopEnv current loopAllocator packet bits leave finalGood.live.hs active
    (inflate_run_default_low_out E invariant buffers nonnull inputValid local_ loop current.good.live.hs)
  have baseEq := (ActiveSourceCut.run_active_base E invariant buffers nonnull inputValid local_ loop
    current.good.live.hs loopActive).2
  have amount : (regs.out_ - regs.left).toNat = z.avail_out.toNat - stream.avail_out.toNat := by
    rw [baseEq, leftOut]
    exact UInt32.toNat_sub_of_le _ _ (by rw [← baseEq]; exact packet.output.count)
  have madeEq : made = (regs.out_ - regs.left).toNat := by
    rw [amount, leftOut]
    omega
  have endpoint : inputAdvance base (regs.out_ - regs.left).toNat =
      inputAdvance z.next_out (regs.out_ - regs.left).toNat := by
    rw [advance, nextOut, put, madeEq]
  have baseSame := inputAdvance_injective endpoint
  subst base
  have valuesSame : emitted = output := bytes_unique (by simpa only [amount] using afterBytes) observed
  simpa only [valuesSame] using dictionary active

#print axioms local_leave_history_observed

theorem bytes_zero {h : Heap} {p : BPtr} {values : List UInt8}
    (observed : Bytes h p 0 values) : values = [] := by
  rcases observed with ⟨_, _, empty⟩ | ⟨_, _, _, _, _, _, values⟩
  · exact empty
  · simpa only [List.take_zero] using values

/-- A direct dictionary request produces zero actual output and retains
the old physical history on the same complete mode-loop execution. -/
theorem local_need_dictionary_history_observed
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {regs : IL}
    {history output : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret Z_NEED_DICT), regs), after))
    (finalGood : Good after r zs stream state)
    (observed : Bytes after z.next_out (z.avail_out.toNat - stream.avail_out.toNat) output)
    (stored : s.mode < CHECK → InflateDictionary h s
      (history.drop (history.length - 2 ^ s.wbits.toNat)))
    (active : state.mode < CHECK) :
    output = [] ∧ InflateDictionary after state
      ((history ++ output).drop ((history ++ output).length - 2 ^ state.wbits.toNat)) := by
  obtain ⟨bs, exit, otherRegs, otherHeap, loopZ, loopS, _used, _made, _bound,
    source, current, ⟨_, _, _packet⟩, _, _bits, _sizes, _next, _count, _put, _left, _metadata, _frame⟩ :=
    inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid local_
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have sameZ : loopZ = stream := Option.some.inj (current.good.live.hz.symm.trans finalGood.live.hz)
  have sameS : loopS = state := Option.some.inj (current.good.live.hs.symm.trans finalGood.live.hs)
  subst loopZ loopS
  have origin := ActiveSourceCut.run_active_base E invariant buffers nonnull inputValid local_ run finalGood.live.hs active
  have dictionary := inflate_run_history_preserved E invariant buffers nonnull inputValid local_ run current (stored origin.1)
  have left := (ActiveSourceCut.run_need_dict_produces_zero E invariant buffers nonnull inputValid local_ run).2
  have publicLeft := inflate_run_direct_output_left E invariant buffers nonnull inputValid local_ run finalGood.live.hz
  have empty : output = [] := bytes_zero (by simpa only [publicLeft, left, Nat.sub_self] using observed)
  exact ⟨empty, by simpa only [empty, List.append_nil] using dictionary⟩

/-- Every real returning body preserves the guarded physical history,
with the actual caller-observed output appended. Direct MEM/SYNC cannot
have an active result; NEED_DICT is handled by its proved zero output. -/
theorem local_body_history_observed
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {rc : Int32}
    {history output : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (rc, after))
    (finalGood : Good after r zs stream state)
    (observed : Bytes after z.next_out (z.avail_out.toNat - stream.avail_out.toNat) output)
    (stored : s.mode < CHECK → InflateDictionary h s
      (history.drop (history.length - 2 ^ s.wbits.toNat)))
    (active : state.mode < CHECK) :
    InflateDictionary after state
      ((history ++ output).drop ((history ++ output).length - 2 ^ state.wbits.toNat)) := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, _used, _made, _bound,
    run, current, ⟨_, _, _packet⟩, _, _bits, _sizes, _next, _count, _put, _left, _metadata, _frame⟩ :=
    inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid local_
  rw [bind_app, run] at body
  cases exit with
  | leave =>
    change inflate_leave c regs loopHeap = .ok (rc, after) at body
    exact local_leave_history_observed E invariant allocator buffers nonnull inputValid local_ run body
      finalGood observed stored active
  | ret value =>
    change Except.ok (value, loopHeap) = Except.ok (rc, after) at body
    cases body
    have allowed := inflate_run_direct_codes run
    rcases allowed with needed | memory | refused
    · exact (local_need_dictionary_history_observed E invariant buffers nonnull inputValid local_
        (by simpa only [needed] using run) finalGood observed stored active).2
    · obtain ⟨returned, get, _needMode, memoryMode, _rest⟩ :=
        inflate_run_return_modes E invariant buffers nonnull inputValid local_ run
      have same : returned = state := Option.some.inj (get.symm.trans finalGood.live.hs)
      have mode : state.mode = MEM := by simpa only [same] using memoryMode (congrArg Ex.ret memory)
      rw [mode] at active
      exact False.elim ((by decide : ¬ MEM < CHECK) active)
    · obtain ⟨_original, _bindings, returned, get, modes⟩ :=
        inflate_run_terminal_direct E invariant buffers nonnull inputValid local_ run (Or.inr refused)
      have same : returned = state := Option.some.inj (get.symm.trans finalGood.live.hs)
      rcases modes with ⟨_mem, impossible⟩ | ⟨mode, _code⟩
      · exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_MEM_ERROR) (refused.symm.trans impossible))
      · rw [same] at mode
        rw [mode] at active
        exact False.elim ((by decide : ¬ SYNC < CHECK) active)

#print axioms bytes_zero
#print axioms local_need_dictionary_history_observed
#print axioms local_body_history_observed

theorem old_byte_view_free_new {initial bodyHeap : Heap} {ref : BRef} {array : Array UInt8}
    (fresh : Fresh initial) (get : Space.get initial ref = some array) :
    (Space.get (freeWin bodyHeap (syncBuf initial)) ref : Option (Array UInt8)) =
      Space.get bodyHeap ref := by
  cases ref with
  | blk block =>
    have other : block ≠ initial.nextBlk := by
      intro equal
      subst block
      have absent := (fresh_dead fresh (Nat.le_refl initial.nextBlk)).1
      change initial.bytes initial.nextBlk = some array at get
      rw [get] at absent
      cases absent
    exact (freeWin_bytes_ne bodyHeap (syncBuf initial)
      (by intro w pointer; cases pointer; exact Ne.symm other)).1
  | dstate_depth block => rfl
  | str value => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

theorem bytes_free_new_back
    {initial bodyHeap : Heap} {p : BPtr} {capacity count : Nat} {output : List UInt8}
    (fresh : Fresh initial) (writable : Writable initial p capacity)
    (observed : Bytes (freeWin bodyHeap (syncBuf initial)) p count output) :
    Bytes bodyHeap p count output := by
  rcases writable with ⟨null, _zero⟩ | ⟨ref, off, array, pointer, get, _readonly, _room⟩
  · rcases observed with empty | ⟨ref, off, array, pointer, _⟩
    · exact Or.inl empty
    · rw [null] at pointer
      cases pointer
  · cases pointer
    rcases observed with ⟨null, _⟩ | ⟨ref2, off2, array2, pointer, get2, room, values⟩
    · cases null
    · cases pointer
      exact Or.inr ⟨ref, off, array2, rfl,
        by rw [old_byte_view_free_new fresh get] at get2; exact get2, room, values⟩

/-- The actual public allocation/body/free path retains chronological
window history on every active result, using its observed output bytes.
The incoming history is a ghost state clause established by initialization. -/
theorem public_history_observed
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {flush rc : Int32} {history output : List UInt8}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z)
    (actual : C.run (inflate (some r) flush) h = .ok (rc, after))
    (finalGood : Good after r zs stream state)
    (observed : Bytes after z.next_out (z.avail_out.toNat - stream.avail_out.toNat) output)
    (stored : s.mode < CHECK → InflateDictionary h s
      (history.drop (history.length - 2 ^ s.wbits.toNat)))
    (active : state.mode < CHECK) :
    InflateDictionary after state
      ((history ++ output).drop ((history ++ output).length - 2 ^ state.wbits.toNat)) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local invariant.good.fresh entry flush
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
  · have source : C.run (inflate (some r) flush) h =
        .ok (Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h)) := by
      unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    have final := allocated.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
    have sameZ : z = stream := Option.some.inj (final.good.live.hz.symm.trans finalGood.live.hz)
    have sameS : s = state := Option.some.inj (final.good.live.hs.symm.trans finalGood.live.hs)
    subst stream state
    have empty : output = [] := bytes_zero (by simpa only [Nat.sub_self] using observed)
    have dictionary := dictionary_free_local allocated (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn]) (dictionary_syncAlloc invariant (stored active))
    simpa only [empty, List.append_nil, syncBuf] using dictionary
  · have nonnull : z.next_out ≠ .null := by
      intro null
      exact rejected (by simp [null])
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have packet := streamBuffers_syncAlloc invariant.good.fresh buffers
    obtain ⟨code, bodyHeap, bodyZ, bodyS, bytes, bodyRun, current, _bodyAllocator,
      localGet, localSize, _localRo⟩ :=
      inflate_default_view_local_state_return env allocated allocator packet nonnull inputValid local_
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    obtain ⟨publicZ, publicS, publicRun, final, _finalAllocator, _freed, bodyGetZ, bodyGetS⟩ :=
      WrapperGlue.inflate_public_close_body invariant allocator buffers nonnull inputValid bodyRun
    have same := Except.ok.inj (publicRun.symm.trans actual)
    cases same
    have sameZ : bodyZ = publicZ := Option.some.inj (current.good.live.hz.symm.trans bodyGetZ)
    have sameS : bodyS = publicS := Option.some.inj (current.good.live.hs.symm.trans bodyGetS)
    subst bodyZ bodyS
    have sameZ : publicZ = stream := Option.some.inj (final.good.live.hz.symm.trans finalGood.live.hz)
    have sameS : publicS = state := Option.some.inj (final.good.live.hs.symm.trans finalGood.live.hs)
    subst publicZ publicS
    have range : CallerRange h r z.next_out z.avail_out.toNat true := by
      obtain ⟨candidate, get, _input, output, _separate⟩ := buffers
      have same : candidate = z := Option.some.inj (get.symm.trans invariant.good.live.hz)
      simpa only [same] using output
    have writable : Writable h z.next_out z.avail_out.toNat := by
      rcases range with null | ⟨_read, write, _outside⟩
      · exact False.elim (nonnull null)
      · exact write rfl
    have bodyObserved := bytes_free_new_back invariant.good.fresh writable observed
    have dictionary := local_body_history_observed env allocated allocator packet nonnull inputValid local_
      bodyRun current.good bodyObserved (fun oldActive => dictionary_syncAlloc invariant (stored oldActive)) active
    exact dictionary_free_local current localGet localSize dictionary

#print axioms old_byte_view_free_new
#print axioms bytes_free_new_back
#print axioms public_history_observed

/-- Closed public producer: actual output observation, full initialized
state, allocator and chronological history belong to one actual run. -/
theorem public_history_producer
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z) (flush : Int32)
    (stored : s.mode < CHECK → InflateDictionary h s
      (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ rc after stream state used output,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      StreamAccounting z stream used output.length ∧ Bytes after z.next_out output.length output ∧
      (state.mode < CHECK → InflateDictionary after state
        ((history ++ output).drop ((history ++ output).length - 2 ^ state.wbits.toNat))) := by
  obtain ⟨rc, after, stream, state, used, output, run, final, alloc, _freed, account, observed, _frame⟩ :=
    inflate_default_view_public_output_bytes invariant allocator buffers entry flush
  have amount : z.avail_out.toNat - stream.avail_out.toNat = output.length := by
    have count := account.2.2.2.1
    omega
  refine ⟨rc, after, stream, state, used, output, run, final, alloc, account, observed, ?_⟩
  exact public_history_observed invariant allocator buffers entry run final.good
    (by simpa only [amount] using observed) stored

/-- A DataStep records actual source execution and bytes, so determinism
identifies its observation with the public producer. No output meaning or
callee specification is an induction hypothesis. -/
theorem dataStep_history
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush rc : Int32} {input output history : List UInt8} {used : Nat}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (entry : EntryHeaderFacts h r s z)
    (step : DataStep .inflate h after r flush rc input output used)
    (stored : s.mode < CHECK → InflateDictionary h s
      (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ stream state, DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      (state.mode < CHECK → InflateDictionary after state
        ((history ++ output).drop ((history ++ output).length - 2 ^ state.wbits.toNat))) := by
  obtain ⟨beforeZ, afterZ, beforeGet, afterGet, buffers, _header, _inputBytes,
    _used, observed, actual⟩ := step
  have sameBefore : beforeZ = z := Option.some.inj (beforeGet.symm.trans invariant.good.live.hz)
  subst beforeZ
  obtain ⟨code, heap, stream, state, _used, emitted, run, final, alloc, account, bytes, dictionary⟩ :=
    public_history_producer invariant allocator buffers entry flush stored
  have same := Except.ok.inj (run.symm.trans actual)
  cases same
  have sameAfter : afterZ = stream := Option.some.inj (afterGet.symm.trans final.good.live.hz)
  subst afterZ
  have amount : z.avail_out.toNat - stream.avail_out.toNat = emitted.length := by
    have count := account.2.2.2.1
    omega
  have sameValues : emitted = output := bytes_unique bytes (by simpa only [amount] using observed)
  exact ⟨stream, state, final, alloc, by simpa only [sameValues] using dictionary⟩

#print axioms public_history_producer
#print axioms dataStep_history
end Zlib.Inflate.Proofs.WindowHistory
