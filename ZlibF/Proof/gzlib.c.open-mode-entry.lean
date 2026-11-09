import ZlibF.Proof.«gzlib.c.open-mode-supplied»

/-!
# gzlib.c: arbitrary successful mode entry with a supplied descriptor

The caller mode and private path are actual CStrings. All initialization, mode
loop, guards, allocation, formatting and I/O belong to one real source run.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Math.GzModeParser

/-- Successful public mode parsing excludes the source's freeing '+' action. -/
theorem parsedMode_no_plus (bs : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (level : Int) (strategy : Nat) (direct : Int)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct)) :
    (43 : UInt8) ∉ bs := by
  intro hb
  have he := gzMode_plus bs hb
  change ZlibF.Spec.Public.parsedMode bs = none at he
  rw [hp] at he
  contradiction

/-- The real initialized mode accumulator has the exact public parsed fields. -/
theorem modePrepared_parsed (h : Heap) (bs : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (level : Int) (strategy : Nat) (direct : Int)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct)) :
    let s := modePreparedRecord h bs
    s.mode = modeCode (some mode) ∧ s.level.toInt = level ∧ s.strategy.toInt = (strategy : Int) ∧
      s.direct.toInt = direct ∧ (mode = .read → s.direct ≠ 1) ∧ (mode ≠ .read → s.direct ≠ -1) := by
  have hn := parsedMode_no_plus bs mode level strategy direct hp
  have hr := modeFold_rep bs {state := openFrontRecord h, flags := 0, exclusive := 0}
    initial (modeRep_initial h) hn
  apply modeRep_finish _ _ mode level strategy direct hr
  rw [← gzMode_byte_fold]
  exact hp

/-- Exact real caller-to-result heap after both successful allocations. -/
def parsedOpenHeap (h : Heap) (bs : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (name : List UInt8) (fd : Int32) (fs : Fs) : Heap :=
  modeSuppliedHeap (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode name fd fs

def parsedOpenRecord (h : Heap) (bs : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (fd : Int32) (fs : Fs) : GzState :=
  resetRec (suppliedRecord (modeCopiedRecord (modePreparedHeap h bs) (modePreparedRecord h bs) mode) mode fd fs)

/-- Arbitrary actual caller CStrings and any successful public parsed setting
execute the full real entry, using the very same final heap as the I/O tail. -/
theorem gz_open_parsed_supplied_run (h : Heap) (fs : Fs) (path modePtr : BPtr) (fd : Int32)
    (bs name : List UInt8) (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int)
    (hf : Fresh h) (hu : Uniq h) (hc : ZlibF.Spec.Public.CString h path name)
    (hmode : ZlibF.Spec.Public.CString h modePtr bs)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct))
    (hlen : name.length ≤ 2147483647) (hfd : fd ≠ -1)
    (ha : h.allocOk h.nalloc = true) (ha1 : h.allocOk (h.nalloc + 1) = true) :
    gz_open path fd modePtr fs h =
      .ok ((some (.in_gzstate_x h.nextBlk), suppliedWorld mode fd fs), parsedOpenHeap h bs mode name fd fs) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hc
  have hn : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, _, hfront⟩ := gz_open_mode_normal_front h fs path modePtr fd bs hf hn hmode
    (parsedMode_no_plus bs mode level strategy direct hp) ha
  obtain ⟨hm, _, _, _, hr, hw⟩ := modePrepared_parsed h bs mode level strategy direct hp
  obtain ⟨hfe, hue⟩ := modePrepared_invariants h bs hf hu
  have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by simp [modePreparedHeap, setS]
  rw [hfront]
  exact openAfterMode_supplied_run _ fs h.nextBlk _ path fd ml mode name hs hm hr hw
    (modePrepared_fields h bs).2.2 hdone hfe hue (modePrepared_cstring h bs path name hc) hlen ha1 hfd

/-- The returned heap and record from the exact caller run establish the
unchanged public OpenState for arbitrary accepted parser fields. -/
theorem parsedOpenHeap_OpenState (h : Heap) (fs : Fs) (bs name : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int) (fd : Int32)
    (hf : Fresh h) (hu : Uniq h) (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct))
    (hn : 0 ∉ name) (hlen : name.length < 2 ^ 64) :
    ZlibF.Spec.Public.OpenState (parsedOpenHeap h bs mode name fd fs) h.nextBlk
      (parsedOpenRecord h bs mode fd fs) mode level strategy direct fd name := by
  obtain ⟨hm, hl, hst, hd, _, _⟩ := modePrepared_parsed h bs mode level strategy direct hp
  obtain ⟨hfe, hue⟩ := modePrepared_invariants h bs hf hu
  have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by simp [modePreparedHeap, setS]
  have hg' : ZlibF.Spec.Public.LibraryGlobals (modePreparedHeap h bs) := hg
  exact modeSuppliedHeap_OpenState _ fs h.nextBlk _ mode level strategy direct name fd hs hm
    (modePrepared_fields h bs).1 (modePrepared_fields h bs).2.1 hl hst hd hfe hue hg' hn hlen

/-- No original caller object is changed by the complete successful entry. -/
theorem parsedOpenHeap_frame (h : Heap) (fs : Fs) (bs name : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) (hf : Fresh h) (hu : Uniq h) :
    ZlibF.Spec.Public.Frame h (parsedOpenHeap h bs mode name fd fs) (fun _ => False) := by
  have hp := modePrepared_ledger h bs hf
  have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by simp [modePreparedHeap, setS]
  obtain ⟨hfe, hue⟩ := modePrepared_invariants h bs hf hu
  have ht := modeSuppliedHeap_ledger _ h.nextBlk _ mode name fd fs hfe hue hs
  obtain ⟨s₁, o₁, g₁, n₁, a₁, f₁⟩ := hp.1
  obtain ⟨s₂, o₂, g₂, n₂, a₂, f₂⟩ := ht.1
  refine ⟨s₁.trans s₂, o₁.trans o₂, g₁.trans g₂, Nat.le_trans n₁ n₂, Nat.le_trans a₁ a₂, ?_⟩
  intro b hl _
  have hbi : b ≠ h.nextBlk := fun he => hf h.nextBlk (Nat.le_refl _) (he ▸ hl)
  have hentry : (modePreparedHeap h bs).live b := (hp.2 b).2 (Or.inl ⟨hl, by simp⟩)
  obtain ⟨b₁, w₁, z₁, g₁, d₁, i₁, s₁, r₁⟩ := f₁ b hl (by simp)
  obtain ⟨b₂, w₂, z₂, g₂, d₂, i₂, s₂, r₂⟩ := f₂ b hentry hbi
  exact ⟨b₂.trans b₁, w₂.trans w₁, z₂.trans z₁, g₂.trans g₁, d₂.trans d₁,
    i₂.trans i₁, s₂.trans s₁, r₂.trans r₁⟩

/-- Exact caller-to-result allocation accounting: only handle and private path. -/
theorem parsedOpenHeap_ledger (h : Heap) (fs : Fs) (bs name : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) (hf : Fresh h) (hu : Uniq h) :
    ZlibF.Spec.Public.LiveChange h (parsedOpenHeap h bs mode name fd fs)
      (fun b => b = h.nextBlk ∨ b = h.nextBlk + 1) (fun _ => False) := by
  have hp := (modePrepared_ledger h bs hf).2
  have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by simp [modePreparedHeap, setS]
  obtain ⟨hfe, hue⟩ := modePrepared_invariants h bs hf hu
  have ht := (modeSuppliedHeap_ledger _ h.nextBlk _ mode name fd fs hfe hue hs).2
  intro b
  unfold parsedOpenHeap
  rw [ht b, hp b]
  change (((h.live b ∧ ¬ False) ∨ b = h.nextBlk) ∧ ¬ False ∨ b = h.nextBlk + 1) ↔
    (h.live b ∧ ¬ False) ∨ b = h.nextBlk ∨ b = h.nextBlk + 1
  simp [or_assoc]

/-- Inactive old buffers and unwritten pointer fields are not owned at size
zero; the real final record owns precisely the handle and private path. -/
theorem parsedOpenRecord_owned (h : Heap) (fs : Fs) (bs : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) (b : Nat) (after : Heap) :
    ZlibF.Spec.Public.GzOwned after h.nextBlk (parsedOpenRecord h bs mode fd fs) b ↔
      b = h.nextBlk ∨ b = h.nextBlk + 1 := by
  have hfields := modePrepared_fields h bs
  cases mode <;> by_cases hc : (modePreparedRecord h bs).direct = 0 <;>
    by_cases hm : (modePreparedRecord h bs).mode = GZ_READ <;>
    dsimp only [GZ_READ] at hm <;>
    simp [ZlibF.Spec.Public.GzOwned, parsedOpenRecord, suppliedRecord, modeCopiedRecord,
      checkedModeRecord, hc, resetRec, modePreparedHeap, setS, openFrontHeap,
      hfields.1, hfields.2.2, hm, GZ_WRITE, GZ_READ]
  all_goals simp only [eq_comm]

/-- A rejected public final parser result is exactly an absent mode or one
of the source's two forbidden direct combinations. -/
theorem modeRep_finish_none (s : GzState) (acc : Acc) (hr : ModeRep s acc)
    (he : finish acc = none) :
    s.mode = GZ_NONE ∨ ∃ mode : ZlibF.Spec.Api.GzMode,
      s.mode = modeCode (some mode) ∧
      ((mode = .read ∧ s.direct = 1) ∨ (mode ≠ .read ∧ s.direct = -1)) := by
  rcases acc with ⟨mo, lv, st, di, bad⟩
  rcases hr with ⟨hm, _, _, hd, hb⟩
  dsimp only at hm hd hb
  subst bad
  cases mo with
  | none => exact Or.inl hm
  | some mo =>
    right
    refine ⟨mo, hm, ?_⟩
    by_cases hread : mo = .read ∧ di = 1
    · left
      refine ⟨hread.1, ?_⟩
      apply Int32.toInt.inj
      simpa [hread.2] using hd
    · by_cases hwrite : mo ≠ .read ∧ di = -1
      · right
        refine ⟨hwrite.1, ?_⟩
        apply Int32.toInt.inj
        simpa [hwrite.2] using hd
      · simp [finish, hread, hwrite] at he

/-- Any rejected caller mode, including '+' at an arbitrary position, follows
its actual release branch before path allocation. -/
theorem gz_open_parsed_reject (h : Heap) (fs : Fs) (path modePtr : BPtr) (fd : Int32)
    (bs : List UInt8) (hf : Fresh h) (hn : path ≠ .null)
    (hc : ZlibF.Spec.Public.CString h modePtr bs)
    (hp : ZlibF.Spec.Public.parsedMode bs = none) (ha : h.allocOk h.nalloc = true) :
    gz_open path fd modePtr fs h = .ok ((none, fs), openReleased h) := by
  by_cases hplus : (43 : UInt8) ∈ bs
  · exact gz_open_mode_plus h fs path modePtr fd bs hf hn hc hplus ha
  · obtain ⟨ml, hdone, hr, hfront⟩ := gz_open_mode_normal_front h fs path modePtr fd bs hf hn hc hplus ha
    have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by simp [modePreparedHeap, setS]
    have hfin : finish (bs.foldl (fun acc b => semanticStep acc (semanticAction (sourceAction b))) initial) = none := by
      rw [← gzMode_byte_fold]
      exact hp
    rcases modeRep_finish_none _ _ hr hfin with hm | ⟨m, hm, hbad⟩
    · rw [hfront]
      simpa [modePreparedHeap, setS, openFrontHeap, openReleased, upd_upd] using
        openAfterMode_absent _ fs h.nextBlk _ path fd ml hs hm hdone
    · rw [hfront]
      simpa [modePreparedHeap, setS, openFrontHeap, openReleased, upd_upd] using
        openAfterMode_forbidden _ fs h.nextBlk _ path fd ml m hs hm hbad hdone

/-- A path-allocation refusal after any successful caller parse releases the
real initialized handle, without depending on the formatter's length bound. -/
theorem gz_open_parsed_path_failure (h : Heap) (fs : Fs) (path modePtr : BPtr) (fd : Int32)
    (bs name : List UInt8) (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int)
    (hf : Fresh h) (hc : ZlibF.Spec.Public.CString h path name)
    (hmode : ZlibF.Spec.Public.CString h modePtr bs)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct))
    (ha : h.allocOk h.nalloc = true) (hfail : h.allocOk (h.nalloc + 1) = false) :
    gz_open path fd modePtr fs h =
      .ok ((none, fs), {openReleased h with nalloc := h.nalloc + 2}) := by
  obtain ⟨r, off, a, he, _, _, _⟩ := writerCString_view h path name hc
  have hn : path ≠ .null := by simp [he]
  obtain ⟨ml, hdone, _, hfront⟩ := gz_open_mode_normal_front h fs path modePtr fd bs hf hn hmode
    (parsedMode_no_plus bs mode level strategy direct hp) ha
  obtain ⟨hm, _, _, _, hr, hw⟩ := modePrepared_parsed h bs mode level strategy direct hp
  have hs : (modePreparedHeap h bs).gzstates h.nextBlk = some (modePreparedRecord h bs) := by simp [modePreparedHeap, setS]
  rw [hfront]
  simpa [modePreparedHeap, setS, openFrontHeap, openReleased, upd_upd] using
    openAfterMode_supplied_path_failure _ fs h.nextBlk _ path fd ml mode name hs hm hr hw hdone
      (modePrepared_cstring h bs path name hc) hfail

/-- Only the actual written fields determine ownership and fd; inactive old
pointers remain arbitrary. This layout is independent of parsing success. -/
theorem parsedOpenRecord_layout (h : Heap) (fs : Fs) (bs : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (fd : Int32) :
    let s := parsedOpenRecord h bs mode fd fs
    s.path = .ref (.blk (h.nextBlk + 1)) 0 ∧ s.size = 0 ∧ s.msg = .null ∧ s.fd = fd := by
  have hfields := modePrepared_fields h bs
  cases mode <;> by_cases hc : (modePreparedRecord h bs).direct = 0 <;>
    by_cases hm : (modePreparedRecord h bs).mode = GZ_READ <;>
    dsimp only [GZ_READ] at hm <;>
    simp [parsedOpenRecord, suppliedRecord, modeCopiedRecord, checkedModeRecord, hc,
      resetRec, modePreparedHeap, setS, openFrontHeap, hfields.1, hfields.2.2, hm, GZ_WRITE, GZ_READ]

/-- The actual caller-run world satisfies the public supplied-descriptor OS
relation, including failed seeks and arbitrary parsed settings. -/
theorem parsedOpenWorld (h : Heap) (fs : Fs) (bs : List UInt8)
    (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int) (fd : Int32)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct)) (hfd : fd ≠ -1) :
    ZlibF.Spec.Public.OpenWorld h fs (suppliedWorld mode fd fs) [] bs mode (some fd) fd
      (parsedOpenRecord h bs mode fd fs).start := by
  have hm := (modePrepared_parsed h bs mode level strategy direct hp).1
  have hm' : (modeCopiedRecord (modePreparedHeap h bs) (modePreparedRecord h bs) mode).mode =
      modeCode (some mode) := by
    by_cases he : mode = .read ∧ (modePreparedRecord h bs).direct = 0 <;>
      simp [modeCopiedRecord, checkedModeRecord, he, hm]
  exact suppliedWorld_OpenWorld h fs fd _ mode bs hm' hfd

/-- Arbitrary caller mode CString, all parsed settings/flags and both allocator
outcomes, on one actual supplied-fd execution. The internal short-path premise
is satisfied by gzdopen's generated identifier, not imposed on public callers. -/
theorem gz_open_supplied_short (h : Heap) (fs : Fs) (path modePtr : BPtr) (fd : Int32)
    (bs name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hg : ZlibF.Spec.Public.LibraryGlobals h)
    (hc : ZlibF.Spec.Public.CString h path name) (hmode : ZlibF.Spec.Public.CString h modePtr bs)
    (hlen : name.length ≤ 2147483647) (hfd : fd ≠ -1) :
    ∃ file fs' after, gz_open path fd modePtr fs h = .ok ((file, fs'), after) ∧
      ZlibF.Spec.Public.Frame h after (fun _ => False) ∧
      (match file with
       | none => fs'.fds = fs.fds ∧ ZlibF.Spec.Public.LiveChange h after (fun _ => False) (fun _ => False) ∧
           (ZlibF.Spec.Public.parsedMode bs = none ∨ ZlibF.Spec.Public.AllocationFailed h after)
       | some (.in_gzstate_x i) => ∃ s mode level strategy direct,
           ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct) ∧
           ZlibF.Spec.Public.OpenState after i s mode level strategy direct fd name ∧
           ZlibF.Spec.Public.OpenWorld h fs fs' [] bs mode (some fd) fd s.start ∧
           ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.GzOwned after i s) (fun _ => False)) := by
  obtain ⟨pr, po, pa, hpp, _, _, _⟩ := writerCString_view h path name hc
  obtain ⟨mr, mo, ma, hmp, _, _, _⟩ := writerCString_view h modePtr bs hmode
  have hpn : path ≠ .null := by simp [hpp]
  have hmn : modePtr ≠ .null := by simp [hmp]
  by_cases ha : h.allocOk h.nalloc = true
  · cases hp : ZlibF.Spec.Public.parsedMode bs with
    | none =>
      obtain ⟨hframe, hledger⟩ := openReleased_frame h (Fresh.slotUsed_next hf)
      exact ⟨none, fs, openReleased h, gz_open_parsed_reject h fs path modePtr fd bs hf hpn hmode hp ha,
        hframe, rfl, hledger, Or.inl rfl⟩
    | some parsed =>
      rcases parsed with ⟨mode, level, strategy, direct⟩
      by_cases ha1 : h.allocOk (h.nalloc + 1) = true
      · let out := parsedOpenRecord h bs mode fd fs
        let after := parsedOpenHeap h bs mode name fd fs
        have ho := parsedOpenHeap_OpenState h fs bs name mode level strategy direct fd hf hu hg hp hc.2.1 hc.2.2
        refine ⟨some (.in_gzstate_x h.nextBlk), suppliedWorld mode fd fs, after,
          gz_open_parsed_supplied_run h fs path modePtr fd bs name mode level strategy direct hf hu hc hmode hp hlen hfd ha ha1,
          parsedOpenHeap_frame h fs bs name mode fd hf hu, out, mode, level, strategy, direct, rfl, ho,
          parsedOpenWorld h fs bs mode level strategy direct fd hp hfd, ?_⟩
        intro b
        change after.live b ↔ ((h.live b ∧ ¬ False) ∨ ZlibF.Spec.Public.GzOwned after h.nextBlk out b)
        rw [parsedOpenRecord_owned]
        exact parsedOpenHeap_ledger h fs bs name mode fd hf hu b
      · have he : h.allocOk (h.nalloc + 1) = false := by simpa using ha1
        obtain ⟨hframe, hledger, halloc⟩ := writerPathFailure_checks h hf he
        exact ⟨none, fs, {openReleased h with nalloc := h.nalloc + 2},
          gz_open_parsed_path_failure h fs path modePtr fd bs name mode level strategy direct hf hc hmode hp ha he,
          hframe, rfl, hledger, Or.inr halloc⟩
  · have he : h.allocOk h.nalloc = false := by simpa using ha
    obtain ⟨hframe, hledger, halloc⟩ := writerFirstFailure_checks h he
    exact ⟨none, fs, {h with nalloc := h.nalloc + 1},
      gz_open_alloc_failure h fs path fd modePtr hpn hmn he, hframe, rfl, hledger, Or.inr halloc⟩

/-- Exact real success layout, derived from the actual run rather than from a
weaker abstract ownership ledger. In particular the copied path is fresh. -/
theorem gz_open_supplied_success_layout (h : Heap) (fs : Fs) (path modePtr : BPtr) (fd : Int32)
    (bs name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hc : ZlibF.Spec.Public.CString h path name) (hmode : ZlibF.Spec.Public.CString h modePtr bs)
    (hlen : name.length ≤ 2147483647) (hfd : fd ≠ -1)
    (i : Nat) (fs' : Fs) (after : Heap) (s : GzState)
    (hrun : gz_open path fd modePtr fs h = .ok ((some (.in_gzstate_x i), fs'), after))
    (hs : after.gzstates i = some s) :
    i = h.nextBlk ∧ s.path = .ref (.blk (h.nextBlk + 1)) 0 ∧ s.size = 0 ∧ s.msg = .null := by
  obtain ⟨pr, po, pa, hpp, _, _, _⟩ := writerCString_view h path name hc
  obtain ⟨mr, mo, ma, hmp, _, _, _⟩ := writerCString_view h modePtr bs hmode
  have hpn : path ≠ .null := by simp [hpp]
  have hmn : modePtr ≠ .null := by simp [hmp]
  by_cases ha : h.allocOk h.nalloc = true
  · cases hp : ZlibF.Spec.Public.parsedMode bs with
    | none =>
      rw [gz_open_parsed_reject h fs path modePtr fd bs hf hpn hmode hp ha] at hrun
      simp at hrun
    | some parsed =>
      rcases parsed with ⟨mode, level, strategy, direct⟩
      by_cases ha1 : h.allocOk (h.nalloc + 1) = true
      · rw [gz_open_parsed_supplied_run h fs path modePtr fd bs name mode level strategy direct
          hf hu hc hmode hp hlen hfd ha ha1] at hrun
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq, GzFileRef.in_gzstate_x.injEq] at hrun
        rcases hrun with ⟨⟨hi, _⟩, hh⟩
        subst i
        rw [← hh] at hs
        have hs' : (parsedOpenHeap h bs mode name fd fs).gzstates h.nextBlk =
            some (parsedOpenRecord h bs mode fd fs) := by simp [parsedOpenHeap, modeSuppliedHeap, setS, parsedOpenRecord]
        rw [hs'] at hs
        have he := Option.some.inj hs
        subst s
        exact ⟨rfl, (parsedOpenRecord_layout h fs bs mode fd).1,
          (parsedOpenRecord_layout h fs bs mode fd).2.1, (parsedOpenRecord_layout h fs bs mode fd).2.2.1⟩
      · have he : h.allocOk (h.nalloc + 1) = false := by simpa using ha1
        rw [gz_open_parsed_path_failure h fs path modePtr fd bs name mode level strategy direct hf hc hmode hp ha he] at hrun
        simp at hrun
  · have he : h.allocOk h.nalloc = false := by simpa using ha
    rw [gz_open_alloc_failure h fs path fd modePtr hpn hmn he] at hrun
    simp at hrun

#print axioms parsedMode_no_plus
#print axioms modePrepared_parsed
#print axioms gz_open_parsed_supplied_run
#print axioms parsedOpenHeap_OpenState
#print axioms parsedOpenHeap_frame
#print axioms parsedOpenHeap_ledger
#print axioms parsedOpenRecord_owned
#print axioms modeRep_finish_none
#print axioms gz_open_parsed_reject
#print axioms gz_open_parsed_path_failure
#print axioms parsedOpenRecord_layout
#print axioms parsedOpenWorld
#print axioms gz_open_supplied_short
#print axioms gz_open_supplied_success_layout
end Zlib.Gzlib.Proofs
