import ZlibF.Proof.«inflate.c.pending-entry»
import ZlibF.Proof.«inflate.c.checksum-view»
import ZlibF.Proof.«inflate.c.table-prime»
import ZlibF.Proof.«inflate.c.window-compose»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual inf_leave suffix after RESTORE. The source equation below
retains the window, counters, checksum, data-type and return branches. -/
def leaveAfterRestore (c : Ctx) (l : IL) : M Int32 := do
  let z ← ldZStream c.strm
  let s ← ldInflateState c.st
  -- if (state->wsize || (out != strm->avail_out && state->mode < BAD && (state->mode < CHECK || flush != Z_FINISH)))
  --     if (updatewindow(strm, strm->next_out, out - strm->avail_out)) { state->mode = MEM; return Z_MEM_ERROR; }
  if s.wsize != 0 || (l.out_ != z.avail_out && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH)) then
    if (← updatewindow c.strm z.next_out (l.out_ - z.avail_out)) != 0 then
      setMode c.st MEM
      return Z_MEM_ERROR
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

/-- Stream fields written by RESTORE. -/
def leaveStream (z : ZStream) (l : IL) : ZStream :=
  { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }

/-- Private fields written by RESTORE. -/
def leaveState (s : InflateState) (l : IL) : InflateState := { s with hold := l.hold, bits := l.bits }

/-- The two RESTORE statements, retained as a literal source prefix. -/
def leaveRestore (c : Ctx) (l : IL) : M Unit := do
  wrZ c.strm fun z => { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }
  wrS c.st fun s => { s with hold := l.hold, bits := l.bits }

/-- The source splits at RESTORE without assuming any suffix execution. -/
theorem inflate_leave_split (c : Ctx) (l : IL) :
    inflate_leave c l = (do leaveRestore c l; leaveAfterRestore c l) := by
  funext h
  unfold inflate_leave leaveRestore leaveAfterRestore
  simp only [bind_app]
  cases first : wrZ c.strm (fun z => { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }) h with
  | error fault => simp only [first]
  | ok result =>
    obtain ⟨unit, current⟩ := result
    cases unit
    simp only [first]

/-- The actual prefix writes the exposed cursors and private bit buffer. -/
theorem leaveRestore_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) :
    leaveRestore c l h = .ok ((), setI (r.put h (leaveStream z l)) zs (leaveState s l)) := by
  unfold leaveRestore
  rw [E.strm, E.st]
  simp only [bind_app, wrZ_eq, E.hz, ZStreamRef.put_istates, wrI_eq, E.hs]
  rfl

/-- The actual inf_leave prefix reaches the same proved restored heap. -/
theorem inflate_leave_restore_cut {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) :
    inflate_leave c l h = leaveAfterRestore c l (setI (r.put h (leaveStream z l)) zs (leaveState s l)) := by
  rw [inflate_leave_split, bind_app, leaveRestore_run E]

/-- RESTORE preserves representation and pending scalar clauses. The bit
count and held-bit premises come from the actual dispatch relation. -/
theorem leave_restore_invariant {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (B : BitInv h l bs) (bits : l.bits.toNat ≤ 39) :
    Good (setI (r.put h (leaveStream z l)) zs (leaveState s l)) r zs (leaveStream z l) (leaveState s l) ∧
      DataPendingInvariant (leaveState s l) ∧
      (leaveState s l).hold.toNat < 2 ^ (leaveState s l).bits.toNat ∧
      ByteViewSizes h (setI (r.put h (leaveStream z l)) zs (leaveState s l)) := by
  have stateInv : StInv h zs (leaveState s l) :=
    good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl bits rfl rfl rfl
  have finalGood := good.setZI (z' := leaveStream z l) (st' := leaveState s l)
    rfl good.live.zalloc good.live.zfree rfl (by exact good.live.mode) stateInv
  exact ⟨finalGood, ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩, B.hold_lt,
    (byte_view_sizes_stream_put h r (leaveStream z l)).trans (byte_view_sizes_setI _ zs (leaveState s l))⟩

/-- Stream-record writes leave every decoder table byte-for-byte unchanged. -/
theorem code_views_put_stream (h : Heap) (r : ZStreamRef) (z : ZStream) (ref : CodeRef) :
    (Space.get (r.put h z) ref : Option (Array Code)) = Space.get h ref := by
  cases ref <;> cases r <;> simp only [Space.get, ZStreamRef.put] <;> split <;> rfl

/-- The guarded data tables survive RESTORE on that same heap. -/
theorem leave_restore_tables {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} (l : IL)
    (state : h.istates zs = some s) (tables : DataTableInvariant h s) :
    DataTableInvariant (setI (r.put h (leaveStream z l)) zs (leaveState s l)) (leaveState s l) := by
  intro active
  have safe := tables active
  have current : (r.put h (leaveStream z l)).istates zs = some s := by simpa using state
  constructor
  · obtain ⟨ref, off, array, ptr, get, valid⟩ := safe.lengthTable
    refine ⟨ref, off, array, ptr, ?_, valid⟩
    unfold leaveState
    rw [code_views_set_bits current, code_views_put_stream]
    exact get
  · obtain ⟨ref, off, array, ptr, get, valid⟩ := safe.distanceTable
    refine ⟨ref, off, array, ptr, ?_, valid⟩
    unfold leaveState
    rw [code_views_set_bits current, code_views_put_stream]
    exact get

end Zlib.Inflate.Proofs
