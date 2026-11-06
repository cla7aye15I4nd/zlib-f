import ZlibF.Proof.«inflate.c.main.simple»
import ZlibF.Proof.«zutil.c»

/-!
# inflate.c: access to the state and the stream from a mode

The access functions of a mode (`rdS`, `wrS`, `rdZ`, `wrZ`, `setMsg`, `setMode`, `inflate_fixed`) as `runX` rules. The
context of a mode is `Env`: the state record `s` at table entry `zs`, and the stream record `z` at `r`. The heap after
`badMode` is `badHeap`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The mode context: `c` names the stream `r` and the state entry `zs`, which hold `z` and `s` in `h`. -/
structure Env (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Prop where
  strm : c.strm = some r
  st : c.st = some (.tab zs)
  hz : r.get h = some z
  hs : h.istates zs = some s

theorem runX_rdS {c : Ctx} {h : Heap} {r zs z s} {α : Type} (E : Env c h r zs z s) (f : InflateState → α) (l : IL) :
    runX (monadLift (rdS c.st f) : X α) l h = .ok ((.ok (f s), l), h) := by
  apply runX_lift_ok
  rw [E.st, rdI_eq, E.hs]

theorem runX_ldS {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) :
    runX (monadLift (ldInflateState c.st) : X InflateState) l h = .ok ((.ok s, l), h) := by
  apply runX_lift_ok
  rw [E.st]; exact ldInflateState_tab E.hs

theorem runX_wrS {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (f : InflateState → InflateState) (l : IL) :
    runX (monadLift (wrS c.st f) : X Unit) l h = .ok ((.ok (), l), setI h zs (f s)) := by
  apply runX_lift_ok
  rw [E.st, wrI_eq, E.hs]

theorem runX_setMode {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (m : UInt32) (l : IL) :
    runX (monadLift (setMode c.st m) : X Unit) l h = .ok ((.ok (), l), setI h zs { s with mode := m }) := by
  apply runX_lift_ok
  rw [E.st]; exact setMode_tab E.hs m

/-- The heap after `strm->msg = "..."; state->mode = BAD;` for the literal at string index `i`. -/
def badHeap (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (i : Nat) : Heap :=
  setI (r.put h { z with msg := .ref (.str i) 0 }) zs { s with mode := BAD }

theorem Env.put {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (v : ZStream) :
    Env c (r.put h v) r zs v s :=
  ⟨E.strm, E.st, ZStreamRef.get_put_same E.hz v, by simpa using E.hs⟩

/-- `badMode c msg` for a literal of the sources. -/
theorem badMode_run {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) {msg : String} (hm : msg ∈ strTable) :
    ∃ i, strTable[i]? = some msg ∧ badMode c msg h = .ok ((), badHeap h r zs z s i) := by
  obtain ⟨i, hi, hi'⟩ := Zlib.Zutil.Proofs.strLit_run h msg hm
  refine ⟨i, hi', ?_⟩
  have hz : ldZStream c.strm h = .ok (z, h) := by rw [E.strm, ldZ_eq, E.hz]
  have hst : stZStream c.strm { z with msg := .ref (.str i) 0 } h = .ok ((), r.put h { z with msg := .ref (.str i) 0 }) := by
    rw [E.strm]; exact stZStream_ok E.hz (by cases r <;> rfl)
  have hE := E.put { z with msg := .ref (.str i) 0 }
  unfold badMode setMsg
  rw [bind_app]
  simp only [Zlib.Zutil.Proofs.litHeap] at hi
  simp only [bind_app, hi, hz, hst]
  have := setMode_tab (m := BAD) hE.hs
  rw [E.st]
  simpa [badHeap] using this

theorem runX_badMode {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) {msg : String} (hm : msg ∈ strTable) (l : IL) :
    ∃ i, strTable[i]? = some msg ∧ runX (monadLift (badMode c msg) : X Unit) l h = .ok ((.ok (), l), badHeap h r zs z s i) := by
  obtain ⟨i, hi, he⟩ := badMode_run E hm
  exact ⟨i, hi, runX_lift_ok he l⟩

/-- The state after `inflate_fixed`. -/
def fixedState (s : InflateState) : InflateState :=
  { s with
    lencode := Ptr.ref CodeRef.st_lenfix 0
    lenbits := 9
    distcode := Ptr.ref CodeRef.st_distfix 0
    distbits := 5 }

/-- `inflate_fixed(state)`: the static tables become the current ones. -/
theorem inflate_fixed_tab {h : Heap} {zs : Nat} {s : InflateState} (e : h.istates zs = some s) :
    Zlib.Inftrees.inflate_fixed (some (.tab zs)) h = .ok ((), setI h zs (fixedState s)) := by
  unfold Zlib.Inftrees.inflate_fixed
  simp only [bind_app, ldInflateState_tab e, stInflateState_tab e]
  simp [setI, ldInflateState_tab, stInflateState_tab, upd_upd]
  rfl

theorem runX_fixed {c : Ctx} {h : Heap} {r zs z s} (E : Env c h r zs z s) (l : IL) :
    runX (monadLift (Zlib.Inftrees.inflate_fixed c.st) : X Unit) l h = .ok ((.ok (), l), setI h zs (fixedState s)) := by
  apply runX_lift_ok
  rw [E.st]; exact inflate_fixed_tab E.hs

end Zlib.Inflate.Proofs
