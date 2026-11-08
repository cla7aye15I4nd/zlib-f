import ZlibF.Proof.«inflate.c.main.table4»
import ZlibF.Proof.«inflate.c.lookup-codes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

def clRepeatCond : X Bool := do
  let l ← get
  set { l with copy := l.copy - 1 }
  return l.copy != 0

def clRepeatBody (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) (← get).len.toUInt16
  wrS c.st fun s => { s with «have» := s.«have» + 1 }

def clRepeat (c : Ctx) : X Unit := xwhile clRepeatCond (clRepeatBody c)

def clWrite (s : InflateState) (value : UInt16) : InflateState :=
  { s with lens := s.lens.set! s.«have».toNat value, «have» := s.«have» + 1 }

theorem clRepeatCond_run (l : IL) (h : Heap) :
    runX clRepeatCond l h = .ok ((.ok (l.copy != 0), { l with copy := l.copy - 1 }), h) := rfl

theorem clRepeatBody_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (inside : s.«have».toNat < s.lens.size) :
    runX (clRepeatBody c) l h = .ok ((.ok (), l), setI h zs (clWrite s l.len.toUInt16)) := by
  have lens := WRef.get_istate_lens hs
  have add := Ptr.add_nat_ok (off := 0) (n := s.«have».toNat) lens (by omega)
  have store := Ptr.store_ok (off := s.«have».toNat) (v := l.len.toUInt16) lens (by simp) inside
  rw [WRef.put_istate_lens hs] at store
  change Ptr.store (.ref (WRef.istate_lens zs) s.«have».toNat) l.len.toUInt16 h =
    .ok ((), setI h zs { s with lens := s.lens.set! s.«have».toNat l.len.toUInt16 }) at store
  unfold OkOn at add
  simp only [Nat.zero_add] at add
  unfold clRepeatBody
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, lensP, add, store, runX_get,
    wrI_eq, setI_setI, clWrite]

/-- The actual post-decrement repeat loop writes only the initialized
length prefix, advances have exactly by copy, and terminates. Its final
failed condition decrements zero to UINT_MAX, as in the C source. -/
theorem clRepeat_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (room : s.«have».toNat + l.copy.toNat ≤ 320)
    (value : l.len.toNat ≤ 15)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15) :
    ∃ state,
      runX (clRepeat c) l h = .ok ((.ok (), { l with copy := 0xffffffff }), setI h zs state) ∧
      state = { s with lens := state.lens, «have» := state.«have» } ∧
      state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + l.copy.toNat ∧
      ∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15 := by
  let total := s.«have».toNat + l.copy.toNat
  let P : Nat → IL → Heap → Prop := fun k current heap => ∃ state,
    heap = setI h zs state ∧
    state = { s with lens := state.lens, «have» := state.«have» } ∧ state.lens.size = 320 ∧
    state.«have».toNat + k = total ∧
    (∀ j, j < state.«have».toNat → (state.lens.getD j 0).toNat ≤ 15) ∧
    current = { l with copy := current.copy } ∧ current.copy.toNat = k
  let Q : Except Ex Unit → IL → Heap → Prop := fun result current heap => ∃ state,
    result = .ok () ∧ current = { l with copy := 0xffffffff } ∧ heap = setI h zs state ∧
    state = { s with lens := state.lens, «have» := state.«have» } ∧ state.lens.size = 320 ∧
    state.«have».toNat = total ∧
    ∀ j, j < state.«have».toNat → (state.lens.getD j 0).toNat ≤ 15
  have rule := xwhileBrk_run (cond := clRepeatCond) (body := do clRepeatBody c; pure false)
    P Q ?_ ?_ (k := l.copy.toNat) (l := l) (h := h) ?_ ?_
  · obtain ⟨result, current, after, run, state, rfl, rfl, rfl, frame, sz, count, initializedState⟩ := rule
    exact ⟨state, run, frame, sz, count, initializedState⟩
  · intro k current heap inv
    obtain ⟨state, heapEq, frame, sz, count, initializedState, registers, remaining⟩ := inv
    subst heap
    have get : (setI h zs state).istates zs = some state := by simp
    have positive : current.copy ≠ 0 := by intro zero; rw [zero] at remaining; simp at remaining
    have copyCount : (current.copy - 1).toNat = k := by
      rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; simp; omega)]
      simp only [UInt32.toNat_one]
      omega
    have inside : state.«have».toNat < state.lens.size := by dsimp [total] at count; omega
    have body := clRepeatBody_run (l := { current with copy := current.copy - 1 }) hc get inside
    have countNext : (state.«have» + 1).toNat = state.«have».toNat + 1 := by
      rw [UInt32.toNat_add]
      simp only [UInt32.toNat_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have registers' : { current with copy := current.copy - 1 } =
        { l with copy := current.copy - 1 } := by rw [registers]
    refine ⟨{ current with copy := current.copy - 1 }, setI h zs state, ?_, .ok false,
      { current with copy := current.copy - 1 }, setI (setI h zs state) zs (clWrite state current.len.toUInt16), ?_, ?_⟩
    · rw [clRepeatCond_run]
      simp [positive]
    · rw [runX_bind, body]
      rfl
    · refine ⟨clWrite state current.len.toUInt16, by simp, ?_, ?_, ?_, ?_, ?_, copyCount⟩
      · unfold clWrite
        rw [frame]
      · simp only [clWrite, Array.size_set!, sz]
      · simp only [clWrite, countNext]
        omega
      · intro j bound
        have actualValue : current.len = l.len := by rw [registers]
        have storedValue : current.len.toUInt16.toNat ≤ 15 := by
          rw [actualValue, UInt32.toNat_toUInt16]
          omega
        simp only [clWrite] at bound ⊢
        rw [countNext] at bound
        rw [Zlib.Inftrees.Proofs.getD_set!]
        by_cases last : state.«have».toNat = j
        · rw [if_pos ⟨last, inside⟩]
          exact storedValue
        · rw [if_neg (fun both => last both.1)]
          exact initializedState j (by omega)
      · exact registers'
  · intro current heap inv
    obtain ⟨state, heapEq, frame, sz, count, initializedState, registers, remaining⟩ := inv
    have zero : current.copy = 0 := UInt32.toNat_inj.mp (by simpa using remaining)
    refine ⟨{ current with copy := current.copy - 1 }, heap, ?_, state, rfl, ?_, heapEq,
      frame, sz, by omega, initializedState⟩
    · rw [clRepeatCond_run]
      simp [zero]
    · rw [registers, zero]
      rfl
  · exact ⟨s, (tcSetI_same hs).symm, rfl, size, rfl, initialized, rfl, rfl⟩
  · have bound := UInt32.toNat_lt l.copy
    unfold fuel
    omega

end Zlib.Inflate.Proofs
