import ZlibF.Proof.«inflate.c.leave-restore»
import ZlibF.Spec.Functional.Checksums

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual counters, checksum, data-type and return suffix. The stream
value is the one read before updatewindow in inf_leave. -/
def leaveFinalize (c : Ctx) (l : IL) (z : ZStream) : M Int32 := do
  -- in -= strm->avail_in; out -= strm->avail_out;
  let in_ := l.in_ - z.avail_in
  let out_ := l.out_ - z.avail_out
  -- strm->total_in += in; strm->total_out += out; state->total += out;
  wrZ c.strm fun z => { z with total_in := z.total_in + in_.toUInt64, total_out := z.total_out + out_.toUInt64 }
  wrS c.st fun s => { s with total := s.total + out_.toUInt64 }
  -- if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, strm->next_out - out, out);
  let s ← ldInflateState c.st
  if (s.wrap &&& 4) != 0 && out_ != 0 then
    let p ← z.next_out.add (-(out_.toNat : Int))
    let v ← UPDATE_CHECK c.st s.check p out_
    wrS c.st fun s => { s with check := v }
    wrZ c.strm fun z => { z with adler := v }
  -- strm->data_type = (int)state->bits + (state->last ? 64 : 0) + (state->mode == TYPE ? 128 : 0) +
  --                   (state->mode == LEN_ || state->mode == COPY_ ? 256 : 0);
  let s ← ldInflateState c.st
  let dt ← chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) + (if s.mode == TYPE then 128 else 0) +
    (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0))
  wrZ c.strm fun z => { z with data_type := dt }
  -- if (((in == 0 && out == 0) || flush == Z_FINISH) && ret == Z_OK) ret = Z_BUF_ERROR;
  let mut ret := l.ret
  if ((in_ == 0 && out_ == 0) || c.flush == Z_FINISH) && ret == Z_OK then ret := Z_BUF_ERROR
  return ret

/-- The final data_type assignment and return selection. -/
def leaveReturn (c : Ctx) (l : IL) (z : ZStream) : M Int32 := do
  let in_ := l.in_ - z.avail_in
  let out_ := l.out_ - z.avail_out
  -- strm->data_type = (int)state->bits + (state->last ? 64 : 0) + (state->mode == TYPE ? 128 : 0) +
  --                   (state->mode == LEN_ || state->mode == COPY_ ? 256 : 0);
  let s ← ldInflateState c.st
  let dt ← chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) + (if s.mode == TYPE then 128 else 0) +
    (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0))
  wrZ c.strm fun z => { z with data_type := dt }
  -- if (((in == 0 && out == 0) || flush == Z_FINISH) && ret == Z_OK) ret = Z_BUF_ERROR;
  let mut ret := l.ret
  if ((in_ == 0 && out_ == 0) || c.flush == Z_FINISH) && ret == Z_OK then ret := Z_BUF_ERROR
  return ret

/-- The two actual counter writes. -/
def leaveCounters (c : Ctx) (l : IL) (z : ZStream) : M Unit := do
  -- in -= strm->avail_in; out -= strm->avail_out;
  let in_ := l.in_ - z.avail_in
  let out_ := l.out_ - z.avail_out
  -- strm->total_in += in; strm->total_out += out; state->total += out;
  wrZ c.strm fun z => { z with total_in := z.total_in + in_.toUInt64, total_out := z.total_out + out_.toUInt64 }
  wrS c.st fun s => { s with total := s.total + out_.toUInt64 }

/-- The actual optional output checksum update. -/
def leaveChecksum (c : Ctx) (l : IL) (z : ZStream) : M Unit := do
  let out_ := l.out_ - z.avail_out
  -- if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, strm->next_out - out, out);
  let s ← ldInflateState c.st
  if (s.wrap &&& 4) != 0 && out_ != 0 then
    let p ← z.next_out.add (-(out_.toNat : Int))
    let v ← UPDATE_CHECK c.st s.check p out_
    wrS c.st fun s => { s with check := v }
    wrZ c.strm fun z => { z with adler := v }

private theorem leave_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f >>= g) = (m >>= fun x => f x >>= g) := by
  funext h
  simp only [bind_app]
  cases m h <;> rfl

private theorem leave_ite_bind {α β : Type} (b : Bool) (yes no : M α) (f : α → M β) :
    ((if b then yes else no) >>= f) = (if b then yes >>= f else no >>= f) := by
  cases b <;> rfl

private theorem leave_pure_bind {α β : Type} (a : α) (f : α → M β) :
    (pure a >>= f) = f a := rfl

/-- Literal source decomposition; each stage below is proved by execution. -/
theorem leaveFinalize_split (c : Ctx) (l : IL) (z : ZStream) :
    leaveFinalize c l z = (do leaveCounters c l z; leaveChecksum c l z; leaveReturn c l z) := by
  unfold leaveFinalize leaveCounters leaveChecksum leaveReturn
  simp only [leave_bind_assoc, leave_ite_bind, leave_pure_bind]

/-- The source reaches this suffix directly when no window update is due. -/
theorem leaveAfterRestore_no_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (skip : (s.wsize != 0 || (l.out_ != z.avail_out && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false) :
    leaveAfterRestore c l h = leaveFinalize c l z h := by
  unfold leaveAfterRestore leaveFinalize
  rw [E.strm, E.st]
  simp only [bind_app, ldZ_eq, E.hz, ldI_eq, E.hs, skip, Bool.false_eq_true, ↓reduceIte]

/-- The cast used in data_type stays signed and bounded. -/
theorem leave_data_type_safe (s : InflateState) (bits : s.bits.toNat ≤ 39) :
    ∃ dt, chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) +
      (if s.mode == TYPE then 128 else 0) +
      (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0)) = pure dt := by
  have cast : (u2i s.bits).toInt = (s.bits.toNat : Int) := by
    unfold u2i
    rw [Int32.toInt_ofInt_of_le (by omega) (by omega)]
  refine ⟨Int32.ofInt _, chkI32_ok ?_ ?_⟩
  all_goals rw [cast]; split <;> split <;> split <;> omega

/-- The final metadata and return operations execute without a signed cast
fault. Only data_type is written; the private state is unchanged. -/
theorem leaveReturn_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (bits : s.bits.toNat ≤ 39) :
    ∃ dt, chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) +
      (if s.mode == TYPE then 128 else 0) +
      (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0)) = pure dt ∧
      leaveReturn c l z h = .ok
      ((if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret), r.put h { current with data_type := dt }) := by
  obtain ⟨dt, cast⟩ := leave_data_type_safe s bits
  refine ⟨dt, cast, ?_⟩
  unfold leaveReturn
  rw [E.st, E.strm]
  simp only [bind_app, ldI_eq, E.hs, cast, pure_app, wrZ_eq, E.hz]
  split <;> rfl

/-- The exact stream counter update. -/
def leaveCountStream (current z : ZStream) (l : IL) : ZStream :=
  { current with total_in := current.total_in + (l.in_ - z.avail_in).toUInt64, total_out := current.total_out + (l.out_ - z.avail_out).toUInt64 }

/-- The exact private output counter update. -/
def leaveCountState (s : InflateState) (z : ZStream) (l : IL) : InflateState :=
  { s with total := s.total + (l.out_ - z.avail_out).toUInt64 }

theorem leaveCounters_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s) :
    leaveCounters c l z h = .ok ((),
      setI (r.put h (leaveCountStream current z l)) zs (leaveCountState s z l)) := by
  unfold leaveCounters
  rw [E.strm, E.st]
  simp only [bind_app, wrZ_eq, E.hz, ZStreamRef.put_istates, wrI_eq, E.hs]
  rfl

/-- No counter or checksum write changes a decoder field. -/
def LeaveMetadataFrame (before after : InflateState) : Prop :=
  after = { before with total := after.total, check := after.check }

theorem LeaveMetadataFrame.trans {first second third : InflateState}
    (a : LeaveMetadataFrame first second) (b : LeaveMetadataFrame second third) :
    LeaveMetadataFrame first third := by
  unfold LeaveMetadataFrame at *
  rw [b, a]

/-- Metadata writes preserve every actual decoder-table view. -/
theorem leave_metadata_code_views {h : Heap} {r : ZStreamRef} {zs : Nat} {s state : InflateState}
    (get : h.istates zs = some s) (stream : ZStream) (frame : LeaveMetadataFrame s state) (ref : CodeRef) :
    (Space.get (setI (r.put h stream) zs state) ref : Option (Array Code)) = Space.get h ref := by
  cases ref with
  | istate_codes i =>
    by_cases same : i = zs
    · subst i
      simp only [Space.get, setI_istates_same, get, Option.map_some]
      rw [frame]
    · simp only [Space.get, setI_istates_ne _ _ _ _ same, ZStreamRef.put_istates]
  | st_lenfix => simp only [Space.get, setI, ZStreamRef.put_static]
  | st_distfix => simp only [Space.get, setI, ZStreamRef.put_static]

/-- The guarded scalar clause is unaffected by counter/checksum metadata. -/
theorem LeaveMetadataFrame.pending {s state : InflateState} (frame : LeaveMetadataFrame s state)
    (pending : DataPendingInvariant s) : DataPendingInvariant state := by
  rw [frame]
  exact ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩

/-- Table pointers, table sizes and table contents all survive metadata writes. -/
theorem LeaveMetadataFrame.tables {h after : Heap} {s state : InflateState}
    (frame : LeaveMetadataFrame s state)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (tables : DataTableInvariant h s) : DataTableInvariant after state := by
  intro active
  have oldActive : DataTableMode s.mode := by rw [frame] at active; exact active
  have safe := tables oldActive
  constructor
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.lengthTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.distanceTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩
  · exact safe.lengthLeaves_frame (by rw [frame]) (by rw [frame]) (fun ref _ _ => views ref)

/-- Only a readable produced prefix is needed after the last output write. -/
def LeaveOutputView (h : Heap) (l : IL) : Prop :=
  ∃ ref off array, l.put = .ref ref off ∧ Space.get h ref = some array ∧
    (l.out_ - l.left).toNat ≤ off ∧ off ≤ array.size

theorem leaveOutputView_of_cursor {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {l : IL} (good : Good h r zs z s) (output : OutputCursorInvariant h r l) :
    LeaveOutputView h l := by
  obtain ⟨ref, array, off, ptr, get, _, room, count, made, _⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  refine ⟨ref, off, array, ptr, get, ?_, by omega⟩
  rw [UInt32.toNat_sub_of_le _ _ count]
  exact made

theorem leaveChecksum_view_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (good : Good h r zs current s) (output : LeaveOutputView h l)
    (flags : s.flags = 0) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ after stream state, leaveChecksum c l z h = .ok ((), after) ∧
      Good after r zs stream state ∧ LeaveMetadataFrame s state ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
      after = setI (r.put h stream) zs state ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) := by
  by_cases update : ((s.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) = true
  · obtain ⟨ref, off, array, put, get, startBound, endBound⟩ := output
    have ptr : l.put.add (-((l.out_ - l.left).toNat : Int)) h =
        .ok (.ref ref (off - (l.out_ - l.left).toNat), h) := by
      rw [put]
      exact Ptr.sub_nat_ok get startBound endBound
    have checksum := UPDATE_CHECK_zlib_view E.hs flags get (by omega :
      off - (l.out_ - l.left).toNat + (l.out_ - l.left).toNat ≤ array.size) s.check
    let value := adlerValue s.check ((array.toList.drop (off - (l.out_ - l.left).toNat)).take
      (l.out_ - l.left).toNat)
    let stream := { current with adler := value }
    let state := { s with check := value }
    let after := setI (r.put h stream) zs state
    have nextGood : Good after r zs stream state := good.setZI rfl good.live.zalloc good.live.zfree
      rfl good.live.mode (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
    refine ⟨after, stream, state, ?_, nextGood, by rfl, ?_, rfl, leave_metadata_code_views E.hs stream (by rfl)⟩
    · unfold leaveChecksum
      rw [E.st, E.strm]
      simp only [bind_app, ldI_eq, E.hs, update, ↓reduceIte]
      rw [cursor, count, ptr]
      simp only []
      rw [checksum]
      simp only [bind_app, E.st, wrI_eq, E.hs, wrZ_eq, ZStreamRef.get_setI, E.hz]
      rw [ZStreamRef.put_setI]
    · intro ref
      rw [byte_view_get_setI, byte_view_get_stream_put]
  · have skip : ((s.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) = false := by
      cases eq : ((s.wrap &&& 4) != 0 && l.out_ - z.avail_out != 0) <;> simp_all
    refine ⟨h, current, s, ?_, good, by rfl, fun _ => rfl, ?_, fun _ => rfl⟩
    · unfold leaveChecksum
      rw [E.st]
      simp only [bind_app, ldI_eq, E.hs, skip, Bool.false_eq_true, ↓reduceIte, pure_app]
    · rw [ZStreamRef.put_self E.hz]
      simp only [setI, upd_self _ _ _ E.hs]

/-- The full post-window suffix executes on ordinary public output views.
The actual Adler callee is discharged above, rather than assumed here. -/
theorem leaveFinalize_view_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (good : Good h r zs current s) (output : LeaveOutputView h l)
    (flags : s.flags = 0) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ LeaveMetadataFrame s state ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
      rc = (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) := by
  let stream1 := leaveCountStream current z l
  let state1 := leaveCountState s z l
  let heap1 := setI (r.put h stream1) zs state1
  have good1 : Good heap1 r zs stream1 state1 := good.setZI rfl good.live.zalloc good.live.zfree
    rfl good.live.mode (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl good.inv.bits rfl rfl rfl)
  have env1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
  have views1 : ∀ ref : BRef, (Space.get heap1 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output1 : LeaveOutputView heap1 l := by
    obtain ⟨ref, off, array, put, get, startBound, endBound⟩ := output
    exact ⟨ref, off, array, put, by rw [views1]; exact get, startBound, endBound⟩
  obtain ⟨heap2, stream2, state2, checksum, good2, frame2, views2, heapEq2, code2⟩ :=
    leaveChecksum_view_safe env1 good1 output1 flags cursor count
  have bits2 : state2.bits.toNat ≤ 39 := by rw [frame2]; exact good.inv.bits
  have env2 : Env c heap2 r zs stream2 state2 := ⟨E.strm, E.st, good2.live.hz, good2.live.hs⟩
  obtain ⟨dt, _, finish⟩ := leaveReturn_run (l := l) (z := z) env2 bits2
  let stream3 := { stream2 with data_type := dt }
  have same : setI (r.put heap2 stream3) zs state2 = r.put heap2 stream3 := by
    exact tcSetI_same (by simpa using good2.live.hs)
  have good3 : Good (r.put heap2 stream3) r zs stream3 state2 := by
    have result := good2.setZI (z' := stream3) (st' := state2) rfl good2.live.zalloc good2.live.zfree
      rfl good2.live.mode good2.inv
    rwa [same] at result
  refine ⟨_, r.put heap2 stream3, stream3, state2, ?_, good3,
    LeaveMetadataFrame.trans (by rfl) frame2, ?_, rfl, ?_⟩
  · rw [leaveFinalize_split, bind_app, leaveCounters_run E]
    simp only []
    rw [bind_app, checksum]
    exact finish
  · intro ref
    rw [byte_view_get_stream_put, views2, views1]
  · intro ref
    rw [code_views_put_stream, code2]
    exact leave_metadata_code_views E.hs stream1 (by rfl) ref

theorem leaveFinalize_safe {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (good : Good h r zs current s) (output : OutputCursorInvariant h r l)
    (flags : s.flags = 0) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      Good after r zs stream state ∧ LeaveMetadataFrame s state ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) ∧
      rc = (if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) := by
  exact leaveFinalize_view_safe E good (leaveOutputView_of_cursor good output) flags cursor count

/-- Complete inf_leave execution when its actual window guard is false.
This includes RESTORE, counts, optional Adler output, data_type and return.
The stronger state clauses are retained for the next public call. -/
theorem inflate_leave_no_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (good : Good h r zs z s) (buffers : DispatchBuffers h r l bs)
    (tables : DataTableInvariant h s) (pending : DataPendingInvariant s)
    (bits : l.bits.toNat ≤ 39) (flags : s.flags = 0)
    (skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧ ByteViewSizes h after ∧
      rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨good0, pending0, hold0, sizes0⟩ := leave_restore_invariant E good pending buffers.bits bits
  have env0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport good good0 rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  have tables0 := leave_restore_tables (r := r) (z := z) l E.hs tables
  obtain ⟨rc, after, stream, state, run, nextGood, frame, views, ret, codeViews⟩ :=
    leaveFinalize_safe (z := stream0) env0 good0 output0 flags rfl rfl
  refine ⟨rc, after, stream, state, ?_, nextGood, frame.tables codeViews tables0,
    frame.pending pending0, ?_, ?_, ret⟩
  · rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run
  · rw [frame]
    exact hold0
  · intro ref
    rw [views]
    exact sizes0 ref

end Zlib.Inflate.Proofs
