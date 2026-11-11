import ZlibF.Proof.«inflate.c.head-gzip-state»
import ZlibF.Proof.«inflate.c.call-dispatch-changed»

/-!
# inflate.c: the memory footprint of `HEAD` when gzip is allowed

`HEAD` with gzip decoding allowed waits for two bytes, or stores the CRC of
the gzip magic in the local `hbuf` and the state, or marks an attached header
record as not gzip (`head->done = -1`) and checks a zlib header, writing only
the stream and the state. The header record's caller buffers keep their bytes.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The zlib header check writes only the stream and the state. -/
theorem headDefaultCheck_heap {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (wbits : HeadWindow s)
    (run : runX (headDefaultCheck c s l) l h = .ok ((outcome, regs), after)) :
    ∃ stream state, after = setI (r.put h stream) zs state := by
  have bad (out : IL) (i : Nat)
      (actual : runX (headDefaultCheck c s l) l h = .ok ((.ok (), out), badHeap h r zs z s i)) :
      ∃ stream state, after = setI (r.put h stream) zs state :=
    ⟨_, _, congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))⟩
  have good
      (actual : runX (headDefaultCheck c s l) l h = .ok ((.ok (), { headWindowRegs l with hold := 0, bits := 0 }),
        setI (r.put h { z with adler := 1 }) zs (headDefaultState s l))) :
      ∃ stream state, after = setI (r.put h stream) zs state :=
    ⟨_, _, congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))⟩
  by_cases header : headHeaderRejected s l = true
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_header E l header
    exact bad _ i actual
  have headerFalse : headHeaderRejected s l = false := by cases test : headHeaderRejected s l <;> simp_all
  by_cases method : headMethodRejected l = true
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_method E l headerFalse method
    exact bad _ i actual
  have methodFalse : headMethodRejected l = false := by cases test : headMethodRejected l <;> simp_all
  by_cases zero : s.wbits = 0
  · by_cases big : 15 < (headWindowRegs l).len.toNat
    · obtain ⟨i, actual⟩ := headDefaultCheck_bad_window_zero E l headerFalse methodFalse big
      exact bad _ i actual
    · exact good (headDefaultCheck_accept_zero E l headerFalse methodFalse zero (by omega))
  have range := wbits.resolve_right (fun e => zero e.1)
  by_cases window : s.wbits.toNat < (headWindowRegs l).len.toNat
  · obtain ⟨i, actual⟩ := headDefaultCheck_bad_window E l headerFalse methodFalse zero window
    exact bad _ i actual
  · exact good (headDefaultCheck_accept E l headerFalse methodFalse (by omega) range)

/-- Marking the attached record as not gzip is a header-record write. -/
theorem HeaderFoot.headDone {c : Ctx} {r : ZStreamRef} {zs : Nat} {regions : List Region} {h : Heap}
    (head : GzHeaderPtr) :
    HeaderFoot (CallChanged c r zs head) regions h (headDoneHeap h head) ∧
      HeaderRegions (headDoneHeap h head) head = HeaderRegions h head := by
  match head with
  | none => exact ⟨HeaderFoot.refl _ _ h, rfl⟩
  | some (.tab i) =>
    cases get : h.gzheaders i with
    | none =>
      have same : headDoneHeap h (some (.tab i)) = h := by simp [headDoneHeap, get]
      rw [same]
      exact ⟨HeaderFoot.refl _ _ h, rfl⟩
    | some g =>
      have same : headDoneHeap h (some (.tab i)) = (GzHeaderRef.tab i).put h { g with done := -1 } := by
        rw [GzHeaderRef.put_tab get]
        simp [headDoneHeap, get]
      rw [same]
      refine ⟨(HeaderFoot.refl (CallChanged c r zs (some (.tab i))) regions h).headerPut
        (Or.inr (Or.inr (Or.inr rfl))) get { g with done := -1 }, ?_⟩
      rw [GzHeaderRef.put_tab get]
      simp [HeaderRegions, upd_same, get]

/-- `HEAD` with gzip allowed changes only the call's blocks; the header
record's regions are those at entry. -/
theorem inflate_dispatch_HEAD_gzip_frame {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (gzip : GzipAllowed s.wrap)
    (local_ : GzipDispatchLocal c h r s l)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    HeaderFoot (CallChanged c r zs s.head) (HeaderRegions h s.head) h after ∧
      HeaderRegions after s.head = HeaderRegions h s.head := by
  have nonzero : s.wrap ≠ 0 := by
    intro zero
    rw [zero] at gzip
    rcases gzip with e | e | e | e <;> exact absurd e (by decide)
  have gzipBit : (s.wrap &&& 2) ≠ 0 := by
    rcases gzip with e | e | e | e <;> rw [e] <;> decide
  have exists_record : ∀ i, s.head = some (.tab i) → (h.gzheaders i).isSome := by
    intro i attached
    rcases local_.record with none | ⟨j, g, pointer, get, _⟩
    · rw [none] at attached
      cases attached
    · rw [attached] at pointer
      cases pointer
      simp [get]
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  have wrapNe : (s.wrap == 0) = false := by simpa using nonzero
  obtain ⟨pulled, current, _, pull, _, _, _, _, _, _, _, _, _, kinds, _⟩ :=
    NEEDBITS_run_cursor buffers.bits 16 (by decide)
  rcases kinds with normal | wait
  · subst normal
    have prefixRun : runX (inflate_dispatch c) l h = runX (headAfterBits c) current h := by
      rw [inflate_dispatch_HEAD E l mode, inflate_HEAD_split, runX_bind, runX_rdS E]
      simp only [wrapNe, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, pull]
    by_cases magic : current.hold = 0x8b1f
    · obtain ⟨b, a, hbufAt, bytes, size, writable⟩ := local_.hbuf
      have actual := prefixRun.trans
        (headAfterBits_gzip E current hbufAt bytes size writable statics gzipBit magic)
      have heapEq := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
      subst heapEq
      have outside : ¬ RegionRoot (HeaderRegions h s.head) (.blk b) := by
        rintro ⟨region, member, off, pointer⟩
        exact local_.apart b hbufAt region member (.blk b) off pointer rfl
      have put := (HeaderFoot.refl (CallChanged c r zs s.head) (HeaderRegions h s.head) h).privatePut
        (Or.inr (Or.inr (Or.inl hbufAt))) outside bytes (crc2Bytes a current.hold)
      have stateGet : (Space.put h (BRef.blk b) (crc2Bytes a current.hold)).istates zs = some s := E.hs
      exact ⟨put.setI (Or.inr (Or.inl rfl)) stateGet _, HeaderRegions.of_headers _ rfl⟩
    · have zlibPath : ((s.wrap &&& 2) != 0 && current.hold == 0x8b1f) = false := by
        simp [magic]
      have actual := (prefixRun.trans (headAfterBits_zlib E current zlibPath exists_record)).symm.trans run
      have doneEnv := E.headDone s.head
      obtain ⟨stream, state, heapEq⟩ := headDefaultCheck_heap doneEnv invariant.headWindow actual
      subst heapEq
      obtain ⟨doneFoot, doneRegions⟩ := HeaderFoot.headDone (c := c) (r := r) (zs := zs)
        (regions := HeaderRegions h s.head) (h := h) s.head
      have streamFoot := doneFoot.streamPut (fun _ root => Or.inl root) doneEnv.hz stream
      have stateGet : (r.put (headDoneHeap h s.head) stream).istates zs = some s := by
        simpa using doneEnv.hs
      refine ⟨streamFoot.setI (Or.inr (Or.inl rfl)) stateGet state, ?_⟩
      rw [← doneRegions]
      exact HeaderRegions.of_headers _ (by simp [setI])
  · subst wait
    have actual : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, current), h) := by
      rw [inflate_dispatch_HEAD E l mode, inflate_HEAD_split, runX_bind, runX_rdS E]
      simp only [wrapNe, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, pull]
    have heapEq := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    subst heapEq
    exact ⟨HeaderFoot.refl _ _ _, rfl⟩

#print axioms inflate_dispatch_HEAD_gzip_frame
end Zlib.Inflate.Proofs
