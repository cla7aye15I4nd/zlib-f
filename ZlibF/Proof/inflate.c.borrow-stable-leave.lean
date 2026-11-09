import ZlibF.Proof.«checksum.borrow-stable»
import ZlibF.Zlib.«inflate.c»

/-!
# inflate.c: actual leave path preserves the libc borrow

The observation is proved from each actual operation and successful execution,
without any public Good invariant or assumed callee contract. Faulting branches
remain faulting; this states metadata preservation on every returning branch.
-/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate

/-- All stream-reference representations retain the separate libc metadata. -/
theorem stream_put_borrow (h : Heap) (r : ZStreamRef) (z : ZStream) :
    (r.put h z).libcErrorBorrow = h.libcErrorBorrow := by
  cases r <;> simp only [ZStreamRef.put]
  all_goals split <;> rfl

theorem stable_ldZStream (p : ZStreamPtr) : StableM (ldZStream p) := by
  intro h v after hr
  unfold ldZStream at hr
  split at hr
  · contradiction
  · split at hr
    · cases hr; rfl
    · contradiction

theorem stable_stZStream (p : ZStreamPtr) (z : ZStream) : StableM (stZStream p z) := by
  intro h v after hr
  unfold stZStream at hr
  split at hr
  · contradiction
  · split at hr
    · split at hr
      · contradiction
      · cases hr; exact stream_put_borrow _ _ _
    · contradiction

theorem stable_ldInflateState (p : InflateStatePtr) : StableM (ldInflateState p) := by
  intro h v after hr
  unfold ldInflateState at hr
  split at hr
  · contradiction
  · split at hr
    · cases hr; rfl
    · contradiction

theorem stable_stInflateState (p : InflateStatePtr) (s : InflateState) : StableM (stInflateState p s) := by
  intro h v after hr
  unfold stInflateState at hr
  split at hr
  · contradiction
  · split at hr
    · split at hr
      · contradiction
      · cases hr
        rename_i r _ _
        cases r
        simp only [InflateStateRef.put]
        split <;> rfl
    · contradiction

theorem stable_castInflateState (p : Option StateRef) : StableM (castInflateState p) := by
  intro h v after hr
  unfold castInflateState at hr
  split at hr
  · cases hr; rfl
  · cases hr; rfl
  · contradiction

theorem stable_wrZ (p : ZStreamPtr) (f : ZStream → ZStream) : StableM (wrZ p f) :=
  StableM.bind (stable_ldZStream p) (fun _ => stable_stZStream _ _)

theorem stable_wrS (p : InflateStatePtr) (f : InflateState → InflateState) : StableM (wrS p f) :=
  StableM.bind (stable_ldInflateState p) (fun _ => stable_stInflateState _ _)

theorem stable_rdS {α : Type} (p : InflateStatePtr) (f : InflateState → α) : StableM (rdS p f) :=
  StableM.bind (stable_ldInflateState p) (fun _ => StableM.pure _)

theorem stable_setMode (p : InflateStatePtr) (m : UInt32) : StableM (setMode p m) := stable_wrS _ _

theorem stable_shl32 (x n : UInt32) : StableM (shl32 x n) := by
  unfold shl32
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

theorem stable_chkI32 (v : Int) : StableM (chkI32 v) := by
  unfold chkI32
  exact StableM.ite _ (StableM.pure _) (StableM.ub _)

/-- Both real default-allocation outcomes retain the borrowed text epoch. -/
theorem stable_ZALLOCB (p : ZStreamPtr) (items size : UInt32) : StableM (ZALLOCB p items size) := by
  unfold ZALLOCB
  apply StableM.bind (stable_ldZStream p)
  intro z
  split
  · exact stable_allocB _
  · exact StableM.ub _

/-- Every actual window allocation/copy branch, including malloc refusal. -/
theorem stable_updatewindow (p : ZStreamPtr) (end_ : BPtr) (copy : UInt32) :
    StableM (updatewindow p end_ copy) := by
  unfold updatewindow
  repeat' first
    | exact stable_ldZStream _
    | exact stable_castInflateState _
    | exact stable_ldInflateState _
    | exact stable_wrS _ _
    | exact stable_shl32 _ _
    | exact stable_ZALLOCB _ _ _
    | exact stable_memcpyB _ _ _
    | exact stable_ptr_add _ _
    | exact StableM.pure _
    | apply StableM.ite
    | apply StableM.bind
    | intro x
    | dsimp only

/-- Both actual checksum choices retain the metadata for arbitrary flags,
checksums, pointer representations and lengths, on every returning execution. -/
theorem stable_UPDATE_CHECK (st : InflateStatePtr) (check : UInt64) (buf : BPtr) (len : UInt32) :
    StableM (UPDATE_CHECK st check buf len) := by
  unfold UPDATE_CHECK
  apply StableM.bind (stable_rdS _ _)
  intro flags
  exact StableM.ite _ (stable_crc32 _ _ _) (stable_adler32 _ _ _)

/-- The real RESTORE macro writes only stream/state registers. Its X-state and
exception wrappers do not invalidate borrowed libc text. -/
theorem stable_RESTORE (p : ZStreamPtr) (st : InflateStatePtr) (l : IL) :
    StableM (StateT.run (ExceptT.run (RESTORE p st)) l) := by
  intro h v after hr
  let fz : ZStream → ZStream := fun z =>
    {z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_}
  let fi : InflateState → InflateState := fun s => {s with hold := l.hold, bits := l.bits}
  cases hz : wrZ p fz h with
  | error e =>
    simp [RESTORE, ExceptT.mk, ExceptT.run, StateT.run, ExceptT.bind,
      ExceptT.bindCont, ExceptT.lift, StateT.bind, StateT.lift, StateT.map,
      StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, Bind.bind, Pure.pure, Functor.map, fz, hz] at hr
  | ok pair =>
    rcases pair with ⟨u, h₁⟩
    cases u
    cases hi : wrS st fi h₁ with
    | error e =>
      simp [RESTORE, ExceptT.mk, ExceptT.run, StateT.run, ExceptT.bind,
        ExceptT.bindCont, ExceptT.lift, StateT.bind, StateT.lift, StateT.map,
        StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
        MonadLift.monadLift, Bind.bind, Pure.pure, Functor.map, fz, fi, hz, hi] at hr
    | ok pair =>
      rcases pair with ⟨u, h₂⟩
      cases u
      have h₁eq := stable_wrZ p fz h () h₁ hz
      have h₂eq := stable_wrS st fi h₁ () h₂ hi
      have hout : after = h₂ := by
        simp [RESTORE, ExceptT.mk, ExceptT.run, StateT.run, ExceptT.bind,
          ExceptT.bindCont, ExceptT.lift, StateT.bind, StateT.lift, StateT.map,
          StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
          MonadLift.monadLift, Bind.bind, Pure.pure, Functor.map, fz, fi, hz, hi] at hr
        exact hr.2.symm
      exact hout ▸ h₂eq.trans h₁eq

/-- The complete actual inf_leave continuation preserves external borrow
metadata for every context/register/heap and every successful return. This
includes real window-allocation refusal and all window/checksum/return guards.
No representation invariant or callee contract is assumed. -/
theorem stable_inflate_leave (c : Ctx) (l : IL) : StableM (inflate_leave c l) := by
  unfold inflate_leave
  repeat' first
    | with_reducible exact stable_wrZ _ _
    | with_reducible exact stable_wrS _ _
    | with_reducible exact stable_ldZStream _
    | with_reducible exact stable_ldInflateState _
    | with_reducible exact stable_updatewindow _ _ _
    | with_reducible exact stable_setMode _ _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible exact stable_UPDATE_CHECK _ _ _ _
    | with_reducible exact stable_chkI32 _
    | with_reducible exact StableM.pure _
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | with_reducible intro x
    | split
    | dsimp only

/-- Direct execution form for callers transporting a source view across the
same actual inflate_leave run. It supplies metadata equality, not a new caller
premise hidden in Frame or Good. -/
theorem inflate_leave_borrow_eq (c : Ctx) (l : IL) (h after : Heap) (rc : Int32)
    (hr : inflate_leave c l h = .ok (rc, after)) :
    after.libcErrorBorrow = h.libcErrorBorrow := stable_inflate_leave c l h rc after hr

/-- Volatile and persistent views can use the established execution equality. -/
theorem inflate_leave_borrow_stable (c : Ctx) (l : IL) (h after : Heap) (rc : Int32)
    (hr : inflate_leave c l h = .ok (rc, after)) (r : BRef) : BorrowStable h after r :=
  (stable_inflate_leave c l).view hr r

#print axioms stable_updatewindow
#print axioms stable_UPDATE_CHECK
#print axioms stable_RESTORE
#print axioms stable_inflate_leave
#print axioms inflate_leave_borrow_eq
#print axioms inflate_leave_borrow_stable
end Zlib.Inflate.BorrowProofs
