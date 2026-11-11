import ZlibF.Proof.«inflate.c.meaning-run»
import ZlibF.Proof.«inflate.c.meaning-check»
import ZlibF.Proof.«inflate.c.meaning-leave-window»
import ZlibF.Proof.«inflate.c.leave-checksum-general»
import ZlibF.Proof.«inflate.c.leave-window»
import ZlibF.Proof.«inflate.c.meaning-frame»

/-!
# inflate.c: `inf_leave` keeps the format meaning (`leave_meaning`)

At `inf_leave` zlib writes the registers back (`RESTORE()`), updates the
window with this call's output since the check base (`updatewindow`), adds
that output to `total` and to the running check, and selects the return
code. From `LoopMatches` at the leave, the decoder after the call matches the
stage of the input read in the call, with the output of the call appended:

* the bit buffer is the registers' (`RESTORE()`), so `HeldBits` carries over;
* a body stage gets the window of the output before the call followed by the
  call's output (`leave_window_meaning`, batch 1);
* `total` and `check` cover the whole output of the stage
  (`leaveFinalize_values`);
* a failed window allocation enters `MEM` and returns `Z_MEM_ERROR`, with the
  parse facts of the input read kept.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The counter, check and return suffix with its values -/

/-- The check after `inf_leave` adds the `out` bytes `bytes` before the cursor. -/
def leaveCheckValue (s : InflateState) (out : UInt32) (bytes : List UInt8) : UInt64 :=
  if ((s.wrap &&& 4) != 0 && out != 0) = true then inflateChecksumValue s.flags s.check bytes
  else s.check

/-- The decoder after the counter and check updates of `inf_leave`. -/
def leaveValueState (s : InflateState) (out : UInt32) (bytes : List UInt8) : InflateState :=
  { s with total := s.total + out.toUInt64, check := leaveCheckValue s out bytes }

/-- The return code `inf_leave` selects. -/
def leaveCode (c : Ctx) (l : IL) (z : ZStream) : Int32 :=
  if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
    l.ret == Z_OK) then Z_BUF_ERROR else l.ret

/-- `leaveFinalize` with its values: the decoder gets `leaveValueState` of the
bytes before the output cursor, the stream record keeps its cursors and
counts, and nothing else changes. -/
theorem leaveFinalize_values {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} {ref : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs current s) (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (bits : s.bits.toNat ≤ 39) (put : l.put = .ref ref off) (get : Space.get h ref = some array)
    (startBound : (l.out_ - l.left).toNat ≤ off) (endBound : off ≤ array.size)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ stream, leaveFinalize c l z h = .ok (leaveCode c l z, setI (r.put h stream) zs
        (leaveValueState s (l.out_ - l.left)
          ((array.toList.drop (off - (l.out_ - l.left).toNat)).take (l.out_ - l.left).toNat))) ∧
      stream.next_in = current.next_in ∧ stream.avail_in = current.avail_in ∧
      stream.next_out = current.next_out ∧ stream.avail_out = current.avail_out ∧
      stream.state = current.state := by
  let out := l.out_ - l.left
  let bytes := (array.toList.drop (off - out.toNat)).take out.toNat
  let stream1 := leaveCountStream current z l
  let state1 := leaveCountState s z l
  let heap1 := setI (r.put h stream1) zs state1
  have env1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, by simp [heap1, E.hz], by simp [heap1]⟩
  have get1 : (Space.get heap1 ref : Option (Array UInt8)) = some array := by
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact get
  have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
    simpa only [Zlib.Crc32.Proofs.StaticsOK, heap1, setI, ZStreamRef.put_static] using statics
  have outEq : l.out_ - z.avail_out = out := by rw [count]
  -- the checksum statement
  have checksum : ∃ stream2, leaveChecksum c l z heap1 = .ok ((), setI (r.put h stream2) zs
      (leaveValueState s out bytes)) ∧ stream2.next_in = current.next_in ∧
      stream2.avail_in = current.avail_in ∧ stream2.next_out = current.next_out ∧
      stream2.avail_out = current.avail_out ∧ stream2.state = current.state := by
    by_cases update : ((state1.wrap &&& 4) != 0 && out != 0) = true
    · have ptr : l.put.add (-(out.toNat : Int)) heap1 = .ok (.ref ref (off - out.toNat), heap1) := by
        rw [put]
        exact Ptr.sub_nat_ok get1 startBound endBound
      have value := UPDATE_CHECK_all_views statics1 env1.hs get1
        (by show off - (l.out_ - l.left).toNat + (l.out_ - l.left).toNat ≤ array.size; omega) state1.check
      refine ⟨{ stream1 with adler := inflateChecksumValue s.flags s.check bytes }, ?_, rfl, rfl, rfl,
        rfl, rfl⟩
      unfold leaveChecksum
      rw [E.st, E.strm]
      have update' : ((state1.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) = true := by
        rw [outEq]; exact update
      simp only [bind_app, ldI_eq, env1.hs, update', ↓reduceIte]
      rw [cursor, outEq, ptr]
      simp only []
      rw [value]
      simp only [bind_app, wrI_eq, env1.hs, wrZ_eq, ZStreamRef.get_setI, env1.hz, pure_app]
      simp only [heap1, ZStreamRef.put_setI, ZStreamRef.put_put, setI_setI]
      have upd : ((s.wrap &&& 4) != 0 && out != 0) = true := update
      simp only [leaveValueState, leaveCheckValue, upd, ↓reduceIte, state1, leaveCountState, outEq]
      rfl
    · have skip : ((state1.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) = false := by
        rw [outEq]
        cases eq : ((state1.wrap &&& 4) != 0 && out != 0) <;> simp_all
      refine ⟨stream1, ?_, rfl, rfl, rfl, rfl, rfl⟩
      unfold leaveChecksum
      rw [E.st]
      simp only [bind_app, ldI_eq, env1.hs, skip, Bool.false_eq_true, ↓reduceIte, pure_app]
      have upd : ((s.wrap &&& 4) != 0 && out != 0) = false := by
        cases eq : ((s.wrap &&& 4) != 0 && out != 0) <;> simp_all [state1, leaveCountState]
      simp only [heap1, leaveValueState, leaveCheckValue, upd, Bool.false_eq_true, ↓reduceIte,
        state1, leaveCountState, outEq]
  obtain ⟨stream2, checksumRun, n1, a1, n2, a2, st2⟩ := checksum
  have env2 : Env c (setI (r.put h stream2) zs (leaveValueState s out bytes)) r zs stream2
      (leaveValueState s out bytes) := ⟨E.strm, E.st, by simp [E.hz], by simp⟩
  obtain ⟨dt, _, finish⟩ := leaveReturn_run (l := l) (z := z) env2 bits
  refine ⟨{ stream2 with data_type := dt }, ?_, n1, a1, n2, a2, st2⟩
  rw [leaveFinalize_split, bind_app, leaveCounters_run E]
  simp only []
  rw [bind_app, checksumRun]
  simp only []
  rw [finish, ZStreamRef.put_setI, ZStreamRef.put_put]
  rfl

#print axioms leaveFinalize_values

/-! ## The whole of `inf_leave` with its values -/

/-- The window-update test of `inf_leave` on the restored decoder. -/
def leaveUpdates (c : Ctx) (l : IL) (s : InflateState) : Bool :=
  s.wsize != 0 || (l.out_ != l.left && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH))

/-- `inf_leave` from the registers `l`, with the values it writes. After
`RESTORE()` (decoder `leaveState s l`, stream `leaveStream z l`, heap `h0`):

* a failed window allocation (only when no window was allocated) enters
  `MEM` and returns `Z_MEM_ERROR`;
* otherwise the window step (skipped, or a successful `updatewindow` of the
  `out - left` bytes before the cursor) gives a decoder that differs only in
  its window fields, and the counter and check step gives `leaveValueState`
  of it with those bytes. -/
theorem inflate_leave_values {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ref : BRef} {off : Nat}
    {array : Array UInt8} {rc : Int32} {after : Heap}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (binv : BitInv h l bs) (bits : l.bits.toNat ≤ 39) (allocator : z.zalloc = .fn "zcalloc")
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (put : l.put = .ref ref off) (get : Space.get h ref = some array)
    (startBound : (l.out_ - l.left).toNat ≤ off) (endBound : off ≤ array.size)
    (unowned : ∀ w, s.window = .ref (.blk w) 0 → ref ≠ .blk w)
    (run : inflate_leave c l h = .ok (rc, after)) :
    (rc = Z_MEM_ERROR ∧ leaveUpdates c l (leaveState s l) = true ∧ s.window = .null ∧
      after.istates zs = some { leaveState s l with mode := MEM } ∧
      r.get after = some (leaveStream z l) ∧
      ∀ bref : BRef, (Space.get after bref : Option (Array UInt8)) = Space.get h bref) ∨
    ∃ heap1 s1 stream,
      ((leaveUpdates c l (leaveState s l) = false ∧ heap1 = setI (r.put h (leaveStream z l)) zs
          (leaveState s l)) ∨
        (leaveUpdates c l (leaveState s l) = true ∧
          C.run (updatewindow (some r) (.ref ref off) (l.out_ - l.left))
            (setI (r.put h (leaveStream z l)) zs (leaveState s l)) = .ok (0, heap1))) ∧
      heap1.istates zs = some s1 ∧ WindowStateFrame (leaveState s l) s1 ∧
      r.get heap1 = some (leaveStream z l) ∧ Space.get heap1 ref = some array ∧
      (∀ cref : CodeRef, (Space.get heap1 cref : Option (Array Code)) = Space.get h cref) ∧
      after = setI (r.put heap1 stream) zs (leaveValueState s1 (l.out_ - l.left)
        ((array.toList.drop (off - (l.out_ - l.left).toNat)).take (l.out_ - l.left).toNat)) ∧
      rc = leaveCode c l (leaveStream z l) ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧ stream.next_out = l.put ∧
      stream.avail_out = l.left ∧ stream.state = z.state := by
  let z0 := leaveStream z l
  let s0 := leaveState s l
  let h0 := setI (r.put h z0) zs s0
  obtain ⟨good0, _, _, _⟩ := leave_restore_invariant E good pending binv bits
  have env0 : Env c h0 r zs z0 s0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have get0 : (Space.get h0 ref : Option (Array UInt8)) = some array := by
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact get
  have codes0 : ∀ cref : CodeRef, (Space.get h0 cref : Option (Array Code)) = Space.get h cref := by
    intro cref
    have current : (r.put h z0).istates zs = some s := by simpa using E.hs
    change (Space.get (setI (r.put h z0) zs { s with hold := l.hold, bits := l.bits }) cref :
      Option (Array Code)) = _
    rw [code_views_set_bits current, code_views_put_stream]
  have statics0 : Zlib.Crc32.Proofs.StaticsOK h0 := by
    simpa only [Zlib.Crc32.Proofs.StaticsOK, h0, setI, ZStreamRef.put_static] using statics
  have bits0 : s0.bits.toNat ≤ 39 := bits
  have cutRun : leaveAfterRestore c l h0 = .ok (rc, after) := by
    rw [← inflate_leave_restore_cut E]
    exact run
  have finalize : ∀ {heap1 : Heap} {s1 : InflateState}, Env c heap1 r zs z0 s1 →
      Zlib.Crc32.Proofs.StaticsOK heap1 → s1.bits.toNat ≤ 39 →
      Space.get heap1 ref = some array → leaveFinalize c l z0 heap1 = .ok (rc, after) →
      ∃ stream, after = setI (r.put heap1 stream) zs (leaveValueState s1 (l.out_ - l.left)
        ((array.toList.drop (off - (l.out_ - l.left).toNat)).take (l.out_ - l.left).toNat)) ∧
        rc = leaveCode c l z0 ∧ stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
        stream.next_out = l.put ∧ stream.avail_out = l.left ∧ stream.state = z.state := by
    intro heap1 s1 env1 statics1 bits1 get1 finalRun
    obtain ⟨stream, values, n1, a1, n2, a2, st⟩ :=
      leaveFinalize_values (z := z0) env1 statics1 bits1 put get1 startBound endBound rfl rfl
    rw [values] at finalRun
    simp only [Except.ok.injEq, Prod.mk.injEq] at finalRun
    obtain ⟨rfl, rfl⟩ := finalRun
    exact ⟨stream, rfl, rfl, n1, a1, n2, a2, st⟩
  cases update : leaveUpdates c l s0 with
  | false =>
    have skip : (s0.wsize != 0 || (l.out_ != z0.avail_out && s0.mode < BAD &&
        (s0.mode < CHECK || c.flush != Z_FINISH))) = false := update
    rw [leaveAfterRestore_no_window env0 skip] at cutRun
    obtain ⟨stream, afterEq, rcEq, n1, a1, n2, a2, st⟩ :=
      finalize env0 statics0 bits0 get0 cutRun
    exact Or.inr ⟨h0, s0, stream, Or.inl ⟨rfl, rfl⟩, env0.hs, rfl, env0.hz, get0, codes0, afterEq,
      rcEq, n1, a1, n2, a2, st⟩
  | true =>
    have doIt : (s0.wsize != 0 || (l.out_ != z0.avail_out && s0.mode < BAD &&
        (s0.mode < CHECK || c.flush != Z_FINISH))) = true := update
    rw [leaveAfterRestore_window env0 doIt] at cutRun
    have unowned0 : ∀ w, s0.window = .ref (.blk w) 0 → ref ≠ .blk w := unowned
    have endEq : off = off - (l.out_ - l.left).toNat + (l.out_ - l.left).toNat := by omega
    obtain ⟨wrc, heap1, s1, windowRun, good1, frame, sourceView, codeViews, outcome⟩ :=
      updatewindow_decoder_boundary (eo := off) (copy := l.out_ - l.left) good0 allocator get0
        startBound endBound unowned0
    unfold leaveWithWindow at cutRun
    have target : (l.out_ - z0.avail_out) = l.out_ - l.left := rfl
    have nextOut : z0.next_out = .ref ref off := put
    rw [nextOut, target, E.strm] at cutRun
    rw [bind_app, show updatewindow (some r) (.ref ref off) (l.out_ - l.left) h0 = .ok (wrc, heap1)
      from windowRun] at cutRun
    rcases outcome with success | ⟨failure, null, stateEq, heapEq⟩
    · subst success
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at cutRun
      have env1 : Env c heap1 r zs z0 s1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
      have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
        have separate : Separate (.ref ref (off - (l.out_ - l.left).toNat)) (l.out_ - l.left).toNat
            s0.window (2 ^ s0.wbits.toNat) := by
          rcases good0.inv.win.block with isNull | ⟨w, _, isWindow, _⟩
          · simp [Separate, s0, isNull]
          · simp [Separate, s0, isWindow, unowned0 w isWindow]
        have := updatewindow_static good0 allocator get0 startBound endBound separate windowRun
        simpa only [Zlib.Crc32.Proofs.StaticsOK, this] using statics0
      have bits1 : s1.bits.toNat ≤ 39 := by rw [frame]; exact bits0
      obtain ⟨stream, afterEq, rcEq, n1, a1, n2, a2, st⟩ :=
        finalize env1 statics1 bits1 sourceView cutRun
      refine Or.inr ⟨heap1, s1, stream, Or.inr ⟨rfl, windowRun⟩, env1.hs, frame, env1.hz, sourceView,
        fun cref => (codeViews cref).trans (codes0 cref), afterEq, rcEq, n1, a1, n2, a2, st⟩
    · subst failure
      subst stateEq
      subst heapEq
      have fail : ((1 : Int32) != 0) = true := by decide
      simp only [fail, ↓reduceIte, bind_app] at cutRun
      unfold setMode at cutRun
      rw [E.st, wrI_eq] at cutRun
      rw [setI_istates_same] at cutRun
      cases cutRun
      refine Or.inl ⟨rfl, rfl, null, by simp, ?_, ?_⟩
      · rw [ZStreamRef.get_setI, ZStreamRef.get_setI, ← env0.hz]
        cases r <;> rfl
      · intro bref
        rw [byte_view_get_setI, byte_view_get_setI]
        refine Eq.trans ?_ (show (Space.get h0 bref : Option (Array UInt8)) = Space.get h bref by
          rw [byte_view_get_setI, byte_view_get_stream_put])
        cases bref <;> rfl

#print axioms inflate_leave_values

/-! ## `total` and `check` after `inf_leave` -/

open Zlib.Inflate.Proofs.MeaningCheck in
/-- `inf_leave` adds the `p` bytes `pend` after the checked output to `total`
and to the running check: the check covers the whole output. -/
theorem checkMeaning_leave {s : InflateState} {wrap : Api.Wrap} {configured : Nat}
    {dict header bodyDict checked pend whole : List UInt8} {p : UInt32}
    (cm : CheckMeaning s wrap header checked) (joined : checked ++ pend = whole)
    (len : pend.length = p.toNat) (wh : WrapHeader wrap configured dict header bodyDict)
    (flagsM : FlagsMatch s wrap header) (code : s.wrap = wrapCode wrap) :
    CheckMeaning (leaveValueState s p pend) wrap header whole := by
  refine ⟨?_, ?_⟩
  · show s.total + p.toUInt64 = _
    rw [cm.1, total_add, ← joined, List.length_append, len]
  · intro w4
    have w4' : (s.wrap &&& 4) ≠ 0 := w4
    have old := cm.2 w4'
    have wrapped : wrap ≠ .raw := by
      intro raw
      rw [code, raw] at w4'
      exact w4' (by decide)
    have kind := trailer_kind wh wrapped flagsM
    show leaveCheckValue s p pend = _
    unfold leaveCheckValue
    by_cases zero : p = 0
    · have empty : pend = [] := List.eq_nil_of_length_eq_zero (by rw [len, zero]; rfl)
      subst empty
      rw [List.append_nil] at joined
      subst joined
      have cond : ((s.wrap &&& 4) != 0 && p != 0) = false := by
        rw [zero]; simp
      rw [cond]
      exact old
    · have cond : ((s.wrap &&& 4) != 0 && p != 0) = true := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨w4', zero⟩
      rw [if_pos cond]
      rcases kind with ⟨_, flagsNZ, choice, _⟩ | ⟨flags0, choice, _⟩
      · simp only [choice, ite_true] at old ⊢
        rw [inflateChecksumValue, if_neg (show s.flags ≠ 0 from flagsNZ), old, toUInt32_toUInt64,
          MeaningChecksum.crc_continue, joined]
      · simp only [choice, ite_false] at old ⊢
        rw [inflateChecksumValue, if_pos (show s.flags = 0 from flags0), old, adlerValue_continue, joined]

#print axioms checkMeaning_leave

/-! ## The stage after `inf_leave` -/

/-- Nothing to add: `inf_leave` keeps `total` and `check`. -/
theorem leaveValueState_zero (s : InflateState) : leaveValueState s 0 [] = s := by
  cases s
  simp only [leaveValueState, leaveCheckValue, bne_self_eq_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply UInt64.toNat_inj.mp
  simp

/-- `BodyMatches` reads none of the fields `inf_leave` writes. -/
theorem BodyMatches.leave {h : Heap} {s0 s1 : InflateState} {pos : DeflatePos} {p : UInt32}
    {bytes : List UInt8} (body : BodyMatches h s0 pos) (frame : WindowStateFrame s0 s1) :
    BodyMatches h (leaveValueState s1 p bytes) pos := by
  rw [frame]
  obtain ⟨out, final, stg⟩ := pos
  cases stg <;> exact body

/-- `WindowMeaning` reads none of the fields of the counter and check step. -/
theorem WindowMeaning.leave {h h' : Heap} {s1 : InflateState} {p : UInt32} {bytes dict out : List UInt8}
    (views : ∀ bref : BRef, (Space.get h' bref : Option (Array UInt8)) = Space.get h bref)
    (window : WindowMeaning h s1 dict out) : WindowMeaning h' (leaveValueState s1 p bytes) dict out :=
  WindowMeaning.frame (s := s1) (fun r _ _ => views r) window

/-- The format meaning after `inf_leave` from a loop exit with `LoopMatches`:
the stream cursors are the registers, the call's output is in place, the
input read parses to a stage, and the decoder either entered `MEM` (window
allocation failure) or matches the stage with the call's output appended. -/
def LeaveMeaning (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (l : IL) (ret rc : Int32)
    (after : Heap) : Prop :=
  ∃ (zs : Nat) (s s' : InflateState) (z' : ZStream) (callOut : List UInt8)
    (consumed held : List Bool) (stage : WrapStage),
    c.st = some (.tab zs) ∧ after.istates zs = some s' ∧ r.get after = some z' ∧
    z'.next_in = l.next ∧ z'.avail_in = l.have_ ∧ z'.next_out = l.put ∧ z'.avail_out = l.left ∧
    l.have_.toNat ≤ l.in_.toNat ∧ l.in_.toNat = f.inp.length ∧
    l.put = inputAdvance f.start callOut.length ∧ Bytes after f.start callOut.length callOut ∧
    bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ held ∧
    WrapParsed f.wrap f.configured f.dict consumed stage ∧ stage.output = f.logOut ++ callOut ∧
    ConfigMatches s' f.wrap f.configured ∧ s'.havedict = s.havedict ∧ HeldBits s' held ∧
    ((rc = Z_MEM_ERROR ∧ s'.mode = MEM) ∨
     ((rc = ret ∨ (rc = Z_BUF_ERROR ∧ ret = Z_OK)) ∧ s'.mode = s.mode ∧
       StageMatches after s' f.wrap f.dict stage ∧ WrapMatches after s' f.wrap f.configured f.dict stage))

open Zlib.Inflate.Proofs.MeaningTrailer (body_mode_range) in
open Zlib.Inflate.Proofs.MeaningCheck (pending_bytes checked_append) in
/-- `leave_meaning`: `inf_leave` after a loop exit with `LoopMatches` (the
return register `ret` set by the exit) gives `LeaveMeaning`. The side
premises are facts of the safety proof at the exit: the stream invariant,
the pending-field invariant, the output block is not the window, at most 39
held bits, the default allocator and the CRC tables; `next_out` was checked
non-null at entry. -/
theorem leave_meaning {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {ret rc : Int32} {after : Heap}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (side : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      Good h r zs z s ∧ DataPendingInvariant s ∧
      ∀ w ref off, s.window = .ref (.blk w) 0 → l.put = .ref ref off → ref ≠ .blk w)
    (bits : l.bits.toNat ≤ 39) (allocator : z.zalloc = .fn "zcalloc")
    (statics : Zlib.Crc32.Proofs.StaticsOK h) (nonnull : f.start ≠ .null)
    (run : inflate_leave c { l with ret := ret } h = .ok (rc, after)) :
    LeaveMeaning c f r l ret rc after := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, _, config, haveLe, inLen, binv, leftLe,
    ⟨pendLe, pendBody⟩, putEq, outBytes, _, _, _, _, bitsEq, heldBits, parsed, stageM, wrapM,
    outputEq⟩ := loop
  obtain ⟨good, pendingInv, unowned⟩ := side zs s st hs
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have binv' : BitInv h { l with ret := ret } (f.inp.drop (loopRead l)) :=
    ⟨binv.have_eq, binv.next, binv.hold_lt⟩
  obtain ⟨ref, i0, a0, startEq, get, fit, contents⟩ : ∃ ref i0 a0, f.start = .ref ref i0 ∧
      Space.get h ref = some a0 ∧ i0 + callOut.length ≤ a0.size ∧
      callOut = (a0.toList.drop i0).take callOut.length := by
    rcases outBytes with ⟨null, _, _⟩ | ⟨ref, i0, a0, ptr, g, fi, cs⟩
    · exact absurd null nonnull
    · exact ⟨ref, i0, a0, ptr, g, fi, cs⟩
  have put : l.put = .ref ref (i0 + callOut.length) := by rw [putEq, startEq]; rfl
  have pNat : (l.out_ - l.left).toNat = loopPending l :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr leftLe)
  have startBound : (l.out_ - l.left).toNat ≤ i0 + callOut.length := by rw [pNat]; omega
  have pLe : (l.out_ - l.left).toNat ≤ callOut.length := by rw [pNat]; exact pendLe
  have pendEq : (a0.toList.drop (i0 + callOut.length - (l.out_ - l.left).toNat)).take
      (l.out_ - l.left).toNat = callOut.drop (callOut.length - (l.out_ - l.left).toNat) :=
    pending_bytes outBytes putEq put get pLe
  have checkedEq : (f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l) ++
      callOut.drop (callOut.length - (l.out_ - l.left).toNat) = f.logOut ++ callOut := by
    rw [pNat]; exact checked_append f.logOut callOut (loopPending l) pendLe
  have dropLen : (callOut.drop (callOut.length - (l.out_ - l.left).toNat)).length =
      (l.out_ - l.left).toNat := by
    rw [List.length_drop]; omega
  have outView : Bytes h f.start callOut.length callOut := outBytes
  have bytesAfter : ∀ heap : Heap, Space.get heap ref = some a0 →
      Bytes heap f.start callOut.length callOut :=
    fun heap g => Or.inr ⟨ref, i0, a0, startEq, g, fit, contents⟩
  have outcome := inflate_leave_values (l := { l with ret := ret }) E good pendingInv binv' bits
    allocator statics put get startBound fit (fun w isWin => unowned w ref _ isWin put) run
  rcases outcome with ⟨rcEq, _, _, hsAfter, hzAfter, viewsAfter⟩ | ⟨heap1, s1, stream, window, hs1,
    frame, hz1, get1, codes1, afterEq, rcEq, n1, a1, n2, a2, _⟩
  · -- window allocation failure: `MEM`
    obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
    refine ⟨zs, s, _, _, callOut, consumed, held, stage, st, hsAfter, hzAfter, rfl, rfl, rfl, rfl,
      haveLe, inLen, putEq, bytesAfter after (by rw [viewsAfter]; exact get), bitsEq, parsed,
      outputEq, ⟨c1, c2, c3, c4, c5, (show MEM ≠ SYNC by decide)⟩, rfl, heldBits, Or.inl ⟨rcEq, rfl⟩⟩
  · dsimp only at window rcEq n1 a1 n2 a2 afterEq
    subst afterEq
    have s0eq : leaveState s { l with ret := ret } = loopState s l := rfl
    rw [s0eq] at frame window
    obtain ⟨good0, _, _, _⟩ := leave_restore_invariant E good pendingInv binv' bits
    rw [s0eq] at good0
    have views0 : ∀ bref : BRef, (Space.get (setI (r.put h (leaveStream z { l with ret := ret })) zs
        (loopState s l)) bref : Option (Array UInt8)) = Space.get h bref := by
      intro bref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    -- the decoder after the leave, with its common facts
    generalize hp : l.out_ - l.left = p at window pNat startBound pLe pendEq checkedEq dropLen ⊢
    have hsA := setI_istates_same (r.put heap1 stream) zs (leaveValueState s1 p
      ((a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat))
    have hzA : r.get (setI (r.put heap1 stream) zs (leaveValueState s1 p
        ((a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat))) = some stream := by
      simp [hz1]
    have viewsA : ∀ bref : BRef, (Space.get (setI (r.put heap1 stream) zs (leaveValueState s1 p
        ((a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat))) bref :
        Option (Array UInt8)) = Space.get heap1 bref := by
      intro bref
      rw [byte_view_get_setI, byte_view_get_stream_put]
    have codesA : ∀ cref : CodeRef, (Space.get (setI (r.put heap1 stream) zs (leaveValueState s1 p
        ((a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat))) cref :
        Option (Array Code)) = Space.get h cref :=
      fun cref => (leave_metadata_code_views (state := leaveValueState s1 p
        ((a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat)) hs1 stream
        (show _ = _ from rfl) cref).trans (codes1 cref)
    have rcCase : rc = ret ∨ (rc = Z_BUF_ERROR ∧ ret = Z_OK) := by
      unfold leaveCode at rcEq
      split at rcEq
      · rename_i cond
        simp only [Bool.and_eq_true, beq_iff_eq] at cond
        exact Or.inr ⟨rcEq, cond.2⟩
      · exact Or.inl rcEq
    have configA : ConfigMatches s1 f.wrap f.configured := by rw [frame]; exact config
    have heldA : HeldBits s1 held := by rw [frame]; exact heldBits
    have modeA : s1.mode = s.mode := by rw [frame]; rfl
    have dictA : s1.havedict = s.havedict := by rw [frame]; rfl
    -- the window step
    have skipZero : leaveUpdates c { l with ret := ret } (loopState s l) = false →
        (loopState s l).wsize = 0 ∧ ((loopState s l).mode < CHECK → p = 0) := by
      intro skip
      refine ⟨?_, ?_⟩
      · by_cases nz : (loopState s l).wsize = 0
        · exact nz
        have yes : leaveUpdates c { l with ret := ret } (loopState s l) = true := by
          simp [leaveUpdates, nz]
        rw [yes] at skip
        cases skip
      · intro lt
        by_cases nz : p = 0
        · exact nz
        have hne : l.out_ ≠ l.left := fun e => nz (by rw [← hp, e, UInt32.sub_self])
        have hbad : (loopState s l).mode < BAD := UInt32.lt_trans lt (by decide)
        have yes : leaveUpdates c { l with ret := ret } (loopState s l) = true := by
          simp [leaveUpdates, hne, hbad, lt]
        rw [yes] at skip
        cases skip
    have skipState : leaveUpdates c { l with ret := ret } (loopState s l) = false →
        heap1 = setI (r.put h (leaveStream z { l with ret := ret })) zs (loopState s l) →
        s1 = loopState s l := by
      intro _ heapEq
      rw [heapEq, setI_istates_same] at hs1
      exact (Option.some.inj hs1).symm
    have windowStep : ∀ out0, WindowMeaning h (loopState s l) f.dict out0 →
        (p = 0 ∨ (loopState s l).mode < CHECK) →
        WindowMeaning heap1 s1 f.dict
          (out0 ++ (a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat) := by
      intro out0 w pz
      rcases window with ⟨skip, heapEq⟩ | ⟨_, wrun⟩
      · obtain ⟨wsize0, zeroOf⟩ := skipZero skip
        have p0 : p = 0 := by
          rcases pz with z0 | lt
          · exact z0
          · exact zeroOf lt
        have sEq := skipState skip heapEq
        subst sEq
        subst p0
        have empty : (a0.toList.drop (i0 + callOut.length - (0 : UInt32).toNat)).take
            (0 : UInt32).toNat = [] := by simp
        rw [empty, List.append_nil]
        exact windowMeaning_of_unset wsize0 w
      · have written : Bytes (setI (r.put h (leaveStream z { l with ret := ret })) zs (loopState s l))
            (.ref ref (i0 + callOut.length - p.toNat)) p.toNat
            ((a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat) :=
          Or.inr ⟨ref, _, a0, rfl, by rw [views0]; exact get, by omega, rfl⟩
        have wrun' : C.run (updatewindow (some r) (.ref ref (i0 + callOut.length - p.toNat + p.toNat)) p)
            (setI (r.put h (leaveStream z { l with ret := ret })) zs (loopState s l)) = .ok (0, heap1) := by
          rw [show i0 + callOut.length - p.toNat + p.toNat = i0 + callOut.length by omega]
          exact wrun
        obtain ⟨state, good', _, _, _, result⟩ := leave_window_meaning good0 allocator
          (WindowMeaning.frame (fun r' _ _ => views0 r') w) written
          (fun w isWin => unowned w ref _ isWin put) wrun'
        have sEq : state = s1 := Option.some.inj (good'.live.hs.symm.trans hs1)
        subst sEq
        rcases result with ⟨_, wm⟩ | ⟨one, _⟩
        · exact wm
        · exact absurd one (by decide)
    have fieldsA : s1.bits = l.bits ∧ s1.flags = s.flags ∧ s1.wbits = s.wbits ∧ s1.check = s.check ∧
        s1.total = s.total ∧ s1.wrap = s.wrap ∧ s1.last = s.last := by
      rw [frame]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have outLeft : p = 0 → l.out_ = l.left := by
      intro p0
      rw [p0] at pNat
      apply UInt32.toNat_inj.mp
      unfold loopPending at pNat
      simp only [UInt32.toNat_zero] at pNat
      omega
    -- with nothing to add, an update means a window of nonzero size
    have updSize : p = 0 → leaveUpdates c { l with ret := ret } (loopState s l) = true →
        (loopState s l).wsize ≠ 0 := by
      intro p0 upd wsize0
      have same : (l.out_ != l.left) = false := by rw [outLeft p0]; simp
      simp [leaveUpdates, wsize0, same] at upd
    refine ⟨zs, s, _, stream, callOut, consumed, held, stage, st, hsA, hzA, n1, a1, n2, a2, haveLe,
      inLen, putEq, bytesAfter _ (by rw [viewsA]; exact get1), bitsEq, parsed, outputEq, configA, dictA,
      heldA, Or.inr ⟨rcCase, modeA, ?_⟩⟩
    obtain ⟨wrap1, conf1, _⟩ := id configA
    cases stage with
    | header bytes =>
      have callNil : callOut = [] := (List.append_eq_nil_iff.mp (outputEq.symm)).2
      have p0 : p = 0 := by
        apply UInt32.toNat_inj.mp
        rw [callNil] at pLe
        simpa using pLe
      subst p0
      have sZ : leaveValueState s1 0 ((a0.toList.drop (i0 + callOut.length - (0 : UInt32).toNat)).take
          (0 : UInt32).toNat) = s1 := by simpa using leaveValueState_zero s1
      rw [sZ] at viewsA ⊢
      obtain ⟨hm, wm, dr⟩ := wrapM
      refine ⟨?_, ?_, ?_, dr⟩
      · show HEAD ≤ s1.mode ∧ s1.mode ≤ DICTID
        rw [modeA]; exact stageM
      · rcases window with ⟨skip, heapEq⟩ | ⟨upd, _⟩
        · rw [skipState skip heapEq]; exact hm
        · obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH⟩ := hm
          rw [frame]
          exact ⟨hA, hB, hC, hD, hE, fun nr => absurd (hF nr).2.1 (updSize rfl upd), hG, hH⟩
      · have w := windowStep [] wm (Or.inl rfl)
        simp only [List.nil_append, UInt32.toNat_zero, List.take_zero] at w
        exact WindowMeaning.frame (fun r' _ _ => viewsA r') w
    | needDict header =>
      have callNil : callOut = [] := (List.append_eq_nil_iff.mp (outputEq.symm)).2
      have p0 : p = 0 := by
        apply UInt32.toNat_inj.mp
        rw [callNil] at pLe
        simpa using pLe
      subst p0
      have sZ : leaveValueState s1 0 ((a0.toList.drop (i0 + callOut.length - (0 : UInt32).toNat)).take
          (0 : UInt32).toNat) = s1 := by simpa using leaveValueState_zero s1
      rw [sZ] at viewsA ⊢
      obtain ⟨wcheck, wflags, wbits, wwidth, wnone, wsome⟩ := wrapM
      refine ⟨by show s1.mode = DICT; rw [modeA]; exact stageM, ?_⟩
      have widthA : HeaderWidth s1 f.configured header := by rw [frame]; exact wwidth
      refine ⟨by rw [fieldsA.2.2.2.1]; exact wcheck, by rw [fieldsA.2.1]; exact wflags,
        by rw [fieldsA.1]; exact wbits, widthA, ?_, ?_⟩
      · intro hd0
        rcases window with ⟨skip, heapEq⟩ | ⟨upd, _⟩
        · rw [skipState skip heapEq] at hd0 ⊢; exact wnone hd0
        · rw [dictA] at hd0
          exact absurd (wnone hd0).1 (updSize rfl upd)
      · intro hd
        rw [dictA] at hd
        refine ⟨(wsome hd).1, ?_⟩
        have w := windowStep [] (wsome hd).2 (Or.inl rfl)
        simp only [List.nil_append, UInt32.toNat_zero, List.take_zero] at w
        exact WindowMeaning.frame (fun r' _ _ => viewsA r') w
    | body header pos =>
      have pAll : p.toNat = callOut.length := by rw [pNat]; exact pendBody header pos rfl
      have bytesAll : (a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat = callOut := by
        rw [pendEq, pAll, Nat.sub_self, List.drop_zero]
      have outEq : pos.out = f.logOut ++ callOut := outputEq
      obtain ⟨bodyM, windowM, checkM⟩ := stageM
      obtain ⟨bodyDict, _, wh, _, _⟩ := id parsed
      have lt : (loopState s l).mode < CHECK :=
        UInt32.lt_of_le_of_lt (body_mode_range bodyM).2 (by decide)
      have flagsS1 : FlagsMatch s1 f.wrap header := by rw [frame]; exact wrapM.1
      have widthS1 : HeaderWidth s1 f.configured header := by rw [frame]; exact wrapM.2.1
      refine ⟨⟨BodyMatches.leave (BodyMatches.frame codesA bodyM) frame, ?_, ?_⟩,
        flagsS1, widthS1, wrapM.2.2⟩
      · rw [outEq]
        have w := windowStep f.logOut windowM (Or.inr lt)
        rw [bytesAll] at w
        exact WindowMeaning.leave viewsA w
      · rw [outEq]
        have cm : CheckMeaning s1 f.wrap header ((f.logOut ++ callOut).take
            ((f.logOut ++ callOut).length - loopPending l)) := by rw [frame]; exact checkM
        exact checkMeaning_leave cm (by rw [pendEq]; exact checkedEq) (by rw [pendEq]; exact dropLen)
          wh flagsS1 wrap1
    | trailer header out tbytes =>
      have outEq : out = f.logOut ++ callOut := outputEq
      obtain ⟨modeT, checkM⟩ := stageM
      obtain ⟨bodyDict, _, _, wh, _⟩ := id parsed
      obtain ⟨flagsM, widthM, tm⟩ := wrapM
      have flagsS1 : FlagsMatch s1 f.wrap header := by rw [frame]; exact flagsM
      have widthS1 : HeaderWidth s1 f.configured header := by rw [frame]; exact widthM
      have cm : CheckMeaning s1 f.wrap header ((f.logOut ++ callOut).take
          ((f.logOut ++ callOut).length - loopPending l)) := by rw [frame]; exact checkM
      have newCM := checkMeaning_leave (p := p)
        (pend := (a0.toList.drop (i0 + callOut.length - p.toNat)).take p.toNat)
        (whole := f.logOut ++ callOut) cm (by rw [pendEq]; exact checkedEq)
        (by rw [pendEq]; exact dropLen) wh flagsS1 wrap1
      rw [← outEq] at newCM
      refine ⟨⟨by show s1.mode = CHECK ∨ s1.mode = LENGTH; rw [modeA]; exact modeT, newCM⟩,
        flagsS1, widthS1, ?_, ?_, ?_⟩
      · intro m
        have m' : s1.mode = CHECK := m
        rw [modeA] at m'
        exact tm.1 m'
      · intro m
        have m' : s1.mode = LENGTH := m
        rw [modeA] at m'
        obtain ⟨t1, t2, t3, _⟩ := tm.2.1 m'
        exact ⟨t1, t2, t3, newCM.1⟩
      · show s1.bits.toNat ≤ 32
        rw [fieldsA.1]; exact tm.2.2
    | done out =>
      refine ⟨by show s1.mode = DONE; rw [modeA]; exact stageM, ?_⟩
      show s1.bits = 0
      rw [fieldsA.1]; exact wrapM

#print axioms leave_meaning

/-- The format meaning after `inf_leave` from `BAD` (`Z_DATA_ERROR`): the
decoder stays in `BAD` (or enters `MEM` after a window allocation failure),
the configuration is kept, and the input read is doomed. -/
def LeaveBad (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (l : IL) (rc : Int32) (after : Heap) :
    Prop :=
  ∃ (zs : Nat) (s' : InflateState) (z' : ZStream),
    c.st = some (.tab zs) ∧ after.istates zs = some s' ∧ r.get after = some z' ∧
    z'.next_in = l.next ∧ z'.avail_in = l.have_ ∧ z'.next_out = l.put ∧ z'.avail_out = l.left ∧
    l.have_.toNat ≤ l.in_.toNat ∧ l.in_.toNat = f.inp.length ∧
    ConfigMatches s' f.wrap f.configured ∧ LoopDoomed f l ∧
    ((rc = Z_DATA_ERROR ∧ s'.mode = BAD) ∨ (rc = Z_MEM_ERROR ∧ s'.mode = MEM))

/-- `leave_meaning` for the `BAD` exit: `case BAD:` set `Z_DATA_ERROR` and left
with `LoopBad`. The output view is a fact of the safety proof (the output
cursor lies in a block, `out - left` bytes after its start). -/
theorem leave_meaning_bad {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    {rc : Int32} {after : Heap}
    (bad : LoopBad c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (side : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      Good h r zs z s ∧ DataPendingInvariant s ∧
      ∀ w ref off, s.window = .ref (.blk w) 0 → l.put = .ref ref off → ref ≠ .blk w)
    (binv : ∃ bs, BitInv h l bs) (bits : l.bits.toNat ≤ 39) (allocator : z.zalloc = .fn "zcalloc")
    (statics : Zlib.Crc32.Proofs.StaticsOK h) (output : LeaveOutputView h l)
    (run : inflate_leave c { l with ret := Z_DATA_ERROR } h = .ok (rc, after)) :
    LeaveBad c f r l rc after := by
  obtain ⟨zs, s, st, hs, mode, _, config, haveLe, inLen, doomed⟩ := bad
  obtain ⟨good, pendingInv, unowned⟩ := side zs s st hs
  obtain ⟨bs, binv⟩ := binv
  obtain ⟨ref, off, array, put, get, startBound, endBound⟩ := output
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have binv' : BitInv h { l with ret := Z_DATA_ERROR } bs := ⟨binv.have_eq, binv.next, binv.hold_lt⟩
  have outcome := inflate_leave_values (l := { l with ret := Z_DATA_ERROR }) E good pendingInv binv'
    bits allocator statics put get startBound endBound (fun w isWin => unowned w ref _ isWin put) run
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
  rcases outcome with ⟨rcEq, _, _, hsAfter, hzAfter, _⟩ | ⟨heap1, s1, stream, _, hs1, frame, _, _, _,
    afterEq, rcEq, n1, a1, n2, a2, _⟩
  · exact ⟨zs, _, _, st, hsAfter, hzAfter, rfl, rfl, rfl, rfl, haveLe, inLen,
      ⟨c1, c2, c3, c4, c5, (show MEM ≠ SYNC by decide)⟩, doomed, Or.inr ⟨rcEq, rfl⟩⟩
  · dsimp only at rcEq n1 a1 n2 a2 afterEq
    subst afterEq
    have hzA : r.get (setI (r.put heap1 stream) zs (leaveValueState s1 (l.out_ - l.left)
        ((array.toList.drop (off - (l.out_ - l.left).toNat)).take (l.out_ - l.left).toNat))) =
        some stream := by
      simp [‹r.get heap1 = some (leaveStream z { l with ret := Z_DATA_ERROR })›]
    have configA : ConfigMatches s1 f.wrap f.configured := by
      rw [frame]; exact ⟨c1, c2, c3, c4, c5, by show s.mode ≠ SYNC; rw [mode]; decide⟩
    have modeA : s1.mode = BAD := by rw [frame]; exact mode
    have rcA : rc = Z_DATA_ERROR := by
      rw [rcEq]
      unfold leaveCode
      have notOk : (Z_DATA_ERROR == Z_OK) = false := by decide
      simp [notOk]
    exact ⟨zs, _, stream, st, setI_istates_same _ _ _, hzA, n1, a1, n2, a2, haveLe, inLen, configA,
      doomed, Or.inl ⟨rcA, modeA⟩⟩

#print axioms leave_meaning_bad

end Zlib.Inflate.Proofs
