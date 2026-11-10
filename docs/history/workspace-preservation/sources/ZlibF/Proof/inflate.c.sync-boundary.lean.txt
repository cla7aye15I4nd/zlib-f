import ZlibF.Proof.«inflate.c.default-state»
import ZlibF.Proof.«inflate.c.default-getdict-history»
import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«inflate.c.reset2-default-state»
import ZlibF.Proof.«inflate.c.prime-default-state»
import ZlibF.Proof.«inflate.c.default-control-history»
import ZlibF.Proof.«inflate.c.default-setdict-history»
import ZlibF.Proof.«inflate.c.sync4»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem syncSt_one : SyncSt 1 [0] := by
  have step := syncStep_spec syncSt_zero (0 : UInt8)
  rcases step with ended | continued
  · have unequal : syncStep 0 0 ≠ 4 := by decide
    exact False.elim (unequal ended.1)
  · have value : syncStep 0 0 = 1 := by decide
    rw [value] at continued
    simpa using continued.2

private theorem syncSt_two : SyncSt 2 [0, 0] := by
  have step := syncStep_spec syncSt_one (0 : UInt8)
  rcases step with ended | continued
  · have unequal : syncStep 1 0 ≠ 4 := by decide
    exact False.elim (unequal ended.1)
  · have value : syncStep 1 0 = 2 := by decide
    rw [value] at continued
    simpa using continued.2

private theorem syncSt_three : SyncSt 3 [0, 0, 255] := by
  have step := syncStep_spec syncSt_two (255 : UInt8)
  rcases step with ended | continued
  · have unequal : syncStep 2 255 ≠ 4 := by decide
    exact False.elim (unequal ended.1)
  · have value : syncStep 2 255 = 3 := by decide
    rw [value] at continued
    simpa using continued.2

/-- Each legal search-state value has a concrete byte history satisfying
the existing `SyncAt` relation. This is enough for safety of a resumed
search; format refinement will retain the actual bytes separately. -/
theorem syncAt_exists_of_bounded {got : UInt32} (bound : got.toNat ≤ 4) :
    ∃ seen, SyncAt got seen := by
  have cases : got.toNat = 0 ∨ got.toNat = 1 ∨ got.toNat = 2 ∨
      got.toNat = 3 ∨ got.toNat = 4 := by omega
  rcases cases with zero | one | two | three | four
  · have eq : got = 0 := UInt32.toNat_inj.mp (by simpa using zero)
    subst got
    exact ⟨[], Or.inl syncSt_zero⟩
  · have eq : got = 1 := UInt32.toNat_inj.mp (by simpa using one)
    subst got
    exact ⟨[0], Or.inl syncSt_one⟩
  · have eq : got = 2 := UInt32.toNat_inj.mp (by simpa using two)
    subst got
    exact ⟨[0, 0], Or.inl syncSt_two⟩
  · have eq : got = 3 := UInt32.toNat_inj.mp (by simpa using three)
    subst got
    exact ⟨[0, 0, 255], Or.inl syncSt_three⟩
  · have eq : got = 4 := UInt32.toNat_inj.mp (by simpa using four)
    subst got
    exact ⟨syncPat, Or.inr ⟨rfl, by decide⟩⟩

/-- The translated scanner returns a legal successor search count from
every bounded starting count and an actual readable input block. -/
theorem syncsearch_at_count_bound {h : Heap} {p : BPtr} {len : UInt32}
    {bs : List UInt8} (input : SyncIn h p len bs)
    {g : UInt32} (bound : g.toNat ≤ 4) :
    ∃ N G, syncsearch g p len h = .ok ((N, G), h) ∧
      N.toNat ≤ len.toNat ∧ G.toNat ≤ 4 := by
  obtain ⟨w, atSpec⟩ := syncAt_exists_of_bounded bound
  obtain ⟨N, G, run, used, _, rest⟩ := syncsearch_at input atSpec
  by_cases done : G = 4
  · exact ⟨N, G, run, used, by simpa [done]⟩
  · have st := (rest done).2
    exact ⟨N, G, run, used, Nat.le_of_lt st.1⟩

/-- For an actual raw byte block, the public readable caller range supplies
the existing sync scanner's `SyncIn` packet without an extra byte premise. -/
theorem syncIn_of_callerRange_blk {h : Heap} {r : ZStreamRef} {b off : Nat}
    {len : UInt32} (range : CallerRange h r (.ref (.blk b) off) len.toNat false) :
    ∃ bytes, SyncIn h (.ref (.blk b) off) len bytes := by
  rcases range with impossible | ⟨⟨bytes, readable⟩, _, _⟩
  · cases impossible
  rcases readable with impossible | ⟨ref, start, array, pointer, get, fit, contents⟩
  · cases impossible.1
  cases pointer
  exact ⟨bytes, Or.inl ⟨b, array, off, rfl, by simpa [Space.get] using get,
    fit, by simpa [syncBytes] using contents⟩⟩

/-- The decoder relation extended with the bounded state of the actual
four-byte synchronization search. -/
structure DefaultSyncJ (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) : Prop extends DefaultStateJ h r zs z s where
  searchBound : s.mode = SYNC → s.«have».toNat ≤ 4

theorem DefaultSyncJ.syncAt {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultSyncJ h r zs z s)
    (mode : s.mode = SYNC) : ∃ seen, SyncAt s.«have» seen :=
  syncAt_exists_of_bounded (invariant.searchBound mode)

/-- The actual default initializer establishes the synchronization bound:
its decoder starts at HEAD. -/
theorem inflate_default_sync_initial (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      DefaultSyncJ after r h.nextBlk z s ∧ StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, current, reachable⟩ :=
    inflate_default_state_initial h r version domain platform allocation
  obtain ⟨_, s0, good0, _, _, head, _⟩ := initial
  have same : s = s0 := Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have headS : s.mode = HEAD := by simpa [same] using head
  exact ⟨after, z, s, run, ⟨current, by intro mode; rw [headS] at mode; cases mode⟩,
    reachable⟩

/-- Caller replacement of public buffers leaves the search state unchanged. -/
theorem rebuffer_default_sync {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultSyncJ h r zs z s)
    (edit : Rebuffer h after r) (platform : ZlibF.PlatformMemory.ByteObjectsFit after) :
    ∃ stream, DefaultSyncJ after r zs stream s := by
  obtain ⟨stream, current⟩ := rebuffer_default_state invariant.toDefaultStateJ edit platform
  exact ⟨stream, ⟨current, invariant.searchBound⟩⟩

/-- Dictionary reads may change caller bytes, but retain the search-state
record and the checked reachable-history transition. -/
theorem inflateGetDictionary_default_sync_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultSyncJ h r zs z s) (dest : BPtr) (dl : Option UInt32)
    (arguments : StreamArguments h r (.inflateGetDictionary (some r) dest dl)) :
    ∃ value after, C.run (inflateGetDictionary (some r) dest dl) h = .ok (value, after) ∧
      DefaultSyncJ after r zs z s ∧ StreamReachable .inflate after r := by
  obtain ⟨value, after, run, current, next⟩ :=
    inflateGetDictionary_default_history reachable invariant.toDefaultStateJ dest dl arguments
  exact ⟨value, after, run, ⟨current, invariant.searchBound⟩, next⟩

/-- Validation toggles wrapper checking without changing the search count
or mode; its actual call retains the bounded search relation. -/
theorem inflateValidate_default_sync_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultSyncJ h r zs z s) (check : Int32) :
    ∃ after state, C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      DefaultSyncJ after r zs z state ∧ StreamReachable .inflate after r := by
  obtain ⟨after, state, run, _, stateEq, current⟩ :=
    inflateValidate_default_state invariant.toDefaultStateJ check
  have bound : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    rw [stateEq]
    simpa [validateState] using invariant.searchBound
  have executed : (Call.inflateValidate (some r) check).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateValidate (some r) check h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateValidate (some r) check) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateValidate (some r) check) := trivial
  exact ⟨after, state, run, ⟨current, bound⟩,
    StreamReachable.step reachable operation arguments executed⟩

/-- Reset-keep leaves the existing window but returns to HEAD, so its
actual execution clears the synchronization-bound obligation. -/
theorem inflateResetKeep_default_sync_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultSyncJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      DefaultSyncJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator⟩ :=
    inflateResetKeep_default_state invariant.toDefaultStateJ allocator
  obtain ⟨after0, run0, _, good0, _⟩ := inflateResetKeep_safe invariant.good
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0
  have sameState : state = resetKeepState zs s :=
    Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have head : state.mode = HEAD := by rw [sameState]; simp [resetKeepState]
  have bound : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro mode
    rw [head] at mode
    cases mode
  have executed : (Call.inflateResetKeep (some r)).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateResetKeep (some r) h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateResetKeep (some r)) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateResetKeep (some r)) := trivial
  exact ⟨after, stream, state, run, ⟨current, bound⟩, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

/-- Ordinary reset returns to HEAD and re-establishes the search bound on
the same checked reachable-history transition. -/
theorem inflateReset_default_sync_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultSyncJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset (some r)) h = .ok (Z_OK, after) ∧
      DefaultSyncJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator⟩ :=
    inflateReset_default_state invariant.toDefaultStateJ allocator
  obtain ⟨after0, run0, _, good0, _⟩ := inflateReset_safe invariant.good allocator.2
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0
  have sameState : state = resetKeepState zs (resetPre s) :=
    Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have head : state.mode = HEAD := by rw [sameState]; simp [resetKeepState]
  have bound : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro mode
    rw [head] at mode
    cases mode
  have executed : (Call.inflateReset (some r)).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateReset (some r) h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateReset (some r)) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateReset (some r)) := trivial
  exact ⟨after, stream, state, run, ⟨current, bound⟩, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

/-- Reset2 at the default window parameter also returns to HEAD while
retaining the platform and decoder relation. -/
theorem inflateReset2_15_default_sync_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultSyncJ h r zs z s) (allocator : DefAlloc z) :
    ∃ after stream state, C.run (inflateReset2 (some r) 15) h = .ok (Z_OK, after) ∧
      DefaultSyncJ after r zs stream state ∧ DefAlloc stream ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, stream, state, run, current, finalAllocator⟩ :=
    inflateReset2_15_default_state invariant.toDefaultStateJ allocator
  obtain ⟨_, after0, run0, result⟩ := inflateReset2_safe invariant.good allocator.2 15
  have params : reset2Params 15 = some (5, 15) := by decide
  rw [params] at result
  obtain ⟨_, _, good0, _⟩ := result
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  rw [← sameHeap] at good0
  have sameState : state = resetKeepState zs (resetPre (reset2Pre 5 15 s)) :=
    Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have head : state.mode = HEAD := by rw [sameState]; simp [resetKeepState]
  have bound : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    intro mode
    rw [head] at mode
    cases mode
  have executed : (Call.inflateReset2 (some r) 15).execute default h =
      .ok ((Z_OK, default), after) := by
    change inflateReset2 (some r) 15 h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateReset2 (some r) 15) := by
    simp [StreamOperation]
  have arguments : StreamArguments h r (.inflateReset2 (some r) 15) := trivial
  exact ⟨after, stream, state, run, ⟨current, bound⟩, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

/-- Priming only changes held bits, so it retains the bounded search state
through every accepted, refused and clearing call. -/
theorem inflatePrime_default_sync_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultSyncJ h r zs z s) (allocator : DefAlloc z)
    (bits value : Int32) :
    ∃ rc after state, C.run (inflatePrime (some r) bits value) h = .ok (rc, after) ∧
      DefaultSyncJ after r zs z state ∧ DefAlloc z ∧
      StreamReachable .inflate after r := by
  obtain ⟨rc, after, state, run, current, finalAllocator, next⟩ :=
    inflatePrime_default_history reachable invariant.toDefaultStateJ allocator bits value
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec invariant.good bits value
  have bound : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    by_cases eq0 : bits = 0
    · have same : state = s := by
        have run0 := zero eq0
        have eq := Except.ok.inj (run.symm.trans run0)
        have heapEq : after = h := congrArg Prod.snd eq
        subst after
        exact Option.some.inj (current.good.live.hs.symm.trans invariant.good.live.hs)
      simpa [same] using invariant.searchBound
    · by_cases neg : bits < 0
      · obtain ⟨run0, good0⟩ := clear neg
        have heapEq : after = setI h zs { s with hold := 0, bits := 0 } :=
          congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
        rw [heapEq] at current
        have same : state = { s with hold := 0, bits := 0 } :=
          Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
        simpa [same] using invariant.searchBound
      · have pos : 0 < bits := by
          rw [Int32.lt_iff_toInt_lt] at neg ⊢
          change ¬ bits.toInt < 0 at neg
          change 0 < bits.toInt
          have notZero : bits.toInt ≠ 0 := by
            intro eq
            apply eq0
            exact Int32.toInt_inj.mp eq
          omega
        by_cases wide : 16 < bits.toInt
        · have run0 := reject pos (Or.inl wide)
          have heapEq : after = h :=
            congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
          subst after
          have same : state = s :=
            Option.some.inj (current.good.live.hs.symm.trans invariant.good.live.hs)
          simpa [same] using invariant.searchBound
        · by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
          · have run0 := reject pos (Or.inr full)
            have heapEq : after = h :=
              congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
            subst after
            have same : state = s :=
              Option.some.inj (current.good.live.hs.symm.trans invariant.good.live.hs)
            simpa [same] using invariant.searchBound
          · obtain ⟨run0, good0⟩ := insert pos (by omega) (by omega)
            have heapEq : after = setI h zs (primeState bits value s) :=
              congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
            rw [heapEq] at current
            have same : state = primeState bits value s :=
              Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
            simpa [same, primeState] using invariant.searchBound
  exact ⟨rc, after, state, run, ⟨current, bound⟩, finalAllocator, next⟩

/-- The actual window update leaves the SYNC search count intact, including
the allocation-failure return. -/
theorem updatewindow_default_sync_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {off : Nat} {source : BRef}
    {bytes : Array UInt8} {copy : UInt32}
    (invariant : DefaultSyncJ h r zs z s) (allocator : DefAlloc z)
    (get : Space.get h source = some bytes) (fit : off + copy.toNat ≤ bytes.size)
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat)) :
    ∃ rc after state,
      C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (rc, after) ∧
      DefaultSyncJ after r zs z state ∧ (rc = 0 ∨ rc = 1) := by
  obtain ⟨rc, after, state, run, current, outcome⟩ :=
    updatewindow_default_state invariant.toDefaultStateJ allocator get fit separate
  have sep : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      s.window (2 ^ s.wbits.toNat) := by simpa using separate
  obtain ⟨rc0, after0, state0, run0, good0, cases⟩ :=
    updatewindow_safe_public invariant.good allocator.1 get (by omega) fit sep
  have sameHeap : after = after0 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans run0))
  have sameState : state = state0 := by
    rw [← sameHeap] at good0
    exact Option.some.inj (current.good.live.hs.symm.trans good0.live.hs)
  have bound : state.mode = SYNC → state.«have».toNat ≤ 4 := by
    rw [sameState]
    rcases cases with ⟨zero, _⟩ | ⟨one, window, failed, heapEq, stateEq⟩
    · have frame := updatewindow_state_frame_public invariant.good allocator.1 get fit separate
        (by simpa only [zero] using run0) good0.live.hs
      rw [frame]
      simpa using invariant.searchBound
    · rw [stateEq]
      exact invariant.searchBound
  exact ⟨rc, after, state, run, ⟨current, bound⟩, outcome⟩

/-- Recording a dictionary leaves the SYNC search fields unchanged. -/
theorem DefaultSyncJ.set_havedict {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultSyncJ h r zs z s) :
    DefaultSyncJ (setI h zs { s with havedict := 1 }) r zs z
      { s with havedict := 1 } := by
  exact ⟨invariant.toDefaultStateJ.set_havedict,
    by simpa using invariant.searchBound⟩

/-- A failed window allocation enters MEM and therefore has no pending
SYNC search count. -/
theorem DefaultSyncJ.mem_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} (invariant : DefaultSyncJ h r zs z s)
    (good : Good after r zs stream { s with mode := MEM })
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after)
    (static : after.static = h.static) :
    DefaultSyncJ after r zs stream { s with mode := MEM } := by
  refine ⟨invariant.toDefaultStateJ.mem_update good platform static, ?_⟩
  intro mode
  have distinct : MEM ≠ SYNC := by decide
  exact False.elim (distinct (by simpa using mode))

/-- The accepted dictionary path retains the bounded search state after
the actual window copy, including its allocation failure. -/
theorem inflateSetDictionary_accepted_default_sync_state {H : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {st : InflateState} {off : Nat} {source : BRef}
    {D : Array UInt8} {L : UInt32}
    (invariant : DefaultSyncJ H r zs z st) (allocator : DefAlloc z)
    (hD : Space.get H source = some D) (hfit : off + L.toNat ≤ D.size)
    (hsep : Separate (.ref source off) L.toNat st.window (2 ^ st.wbits.toNat))
    (hwrap : st.wrap = 0 ∨ st.mode = DICT)
    (hadler : st.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg D off L.toNat)).toUInt64 = st.check) :
    ∃ rc after state,
      C.run (inflateSetDictionary (some r) (.ref source off) L) H = .ok (rc, after) ∧
      DefaultSyncJ after r zs z state ∧ DefAlloc z ∧
      (rc = Z_OK ∨ rc = Z_MEM_ERROR) := by
  have hG := invariant.good
  have hL := hG.live
  obtain ⟨v0, H1, st1, hr1, current, _⟩ :=
    updatewindow_default_sync_state invariant allocator hD hfit hsep
  have hadd' : Ptr.add (Ptr.ref source off) (L.toNat : Int) H =
      .ok (Ptr.ref source (off + L.toNat), H) := Ptr.add_nat_ok hD hfit
  have hnn : (Ptr.ref source off == (Ptr.null : BPtr)) = false := by simp
  have hr1' : updatewindow (some r) (Ptr.ref source (off + L.toNat)) L H =
      .ok (v0, H1) := hr1
  have hrun : inflateSetDictionary (some r) (.ref source off) L H =
      (if v0 = 0 then .ok (Z_OK, setI H1 zs { st1 with havedict := 1 })
       else .ok (Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM })) := by
    have hs1 : H1.istates zs = some st1 := current.good.live.hs
    unfold inflateSetDictionary
    simp only [bind_app, stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, hnn,
      bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
    by_cases hm : st.mode = DICT
    · have hra := adler32_dict_any hD L hfit
      have hck := hadler hm
      have hmb : (st.mode == DICT) = true := by simpa using hm
      simp only [hmb, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', ite_true,
        Bool.false_eq_true, ite_false, Bool.and_false, hmb, hm, beq_self_eq_true]
      simp only [bind_app, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1',
        Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true,
          bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
    · have hw0 : st.wrap = 0 := by rcases hwrap with h | h; exact h; exact absurd h hm
      have hmb : (st.mode == DICT) = false := by simpa using hm
      simp only [hmb, hw0, hadd', hr1', bne_self_eq_false, Bool.false_and,
        Bool.false_eq_true, ite_false, Bool.and_false]
      simp only [bind_app, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true,
          bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
  by_cases zero : v0 = 0
  · exact ⟨Z_OK, _, _, by rw [C.run, hrun, if_pos zero], current.set_havedict,
      allocator, Or.inl rfl⟩
  · have good := good_state (st' := { st1 with mode := MEM }) current.good rfl mode_mem
      (current.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl current.good.inv.bits
        rfl rfl rfl)
    exact ⟨Z_MEM_ERROR, _, _, by rw [C.run, hrun, if_neg zero],
      current.mem_update good (current.platform.with_istates _) rfl,
      allocator, Or.inr rfl⟩

/-- All admissible dictionary outcomes preserve the bounded search state
and extend the actual public call history. -/
theorem inflateSetDictionary_default_sync_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultSyncJ h r zs z s) (allocator : DefAlloc z)
    (source : BPtr) (n : UInt32)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) source n)) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      DefaultSyncJ after r zs z state ∧ DefAlloc z ∧
      StreamReachable .inflate after r := by
  have range : CallerRange h r source n.toNat false := arguments
  obtain ⟨xs, readable⟩ : ∃ xs, source ≠ .null → Bytes h source n.toNat xs := by
    rcases range with null | ⟨⟨xs, bytes⟩, _, _⟩
    · exact ⟨[], by intro nonnull; exact False.elim (nonnull null)⟩
    · exact ⟨xs, by intro _; exact bytes⟩
  have separate := callerRange_dictionary_window_separate invariant.good range
  have result : ∃ rc after state,
      C.run (inflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      DefaultSyncJ after r zs z state ∧ DefAlloc z := by
    by_cases null : source = .null
    · exact ⟨Z_STREAM_ERROR, h, s,
        inflateSetDictionary_refused_any invariant.good.live source n (Or.inl null),
        invariant, allocator⟩
    by_cases permitted : s.wrap = 0 ∨ s.mode = DICT
    · rcases readable null with impossible | ⟨ref, off, array, pointer, get, fit, value⟩
      · exact False.elim (null impossible.1)
      subst source
      by_cases wrong : s.mode = DICT ∧
          (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 ≠ s.check
      · exact ⟨Z_DATA_ERROR, h, s,
          inflateSetDictionary_dataerr_any invariant.good.live get fit wrong.1 wrong.2,
          invariant, allocator⟩
      · have accepted : s.mode = DICT →
            (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 = s.check := by
          intro mode
          by_cases equal : (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 = s.check
          · exact equal
          · exact False.elim (wrong ⟨mode, equal⟩)
        obtain ⟨rc, after, state, run, current, finalAllocator, _⟩ :=
          inflateSetDictionary_accepted_default_sync_state invariant allocator get fit separate
            permitted accepted
        exact ⟨rc, after, state, run, current, finalAllocator⟩
    · have refused : s.wrap ≠ 0 ∧ s.mode ≠ DICT := by
        constructor
        · exact fun equal => permitted (Or.inl equal)
        · exact fun equal => permitted (Or.inr equal)
      exact ⟨Z_STREAM_ERROR, h, s,
        inflateSetDictionary_refused_any invariant.good.live source n (Or.inr refused),
        invariant, allocator⟩
  obtain ⟨rc, after, state, run, current, finalAllocator⟩ := result
  have executed : (Call.inflateSetDictionary (some r) source n).execute default h =
      .ok ((rc, default), after) := by
    change inflateSetDictionary (some r) source n h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateSetDictionary (some r) source n) := by
    simp [StreamOperation]
  exact ⟨rc, after, state, run, current, finalAllocator,
    StreamReachable.step reachable operation arguments executed⟩

end Zlib.Inflate.Proofs
