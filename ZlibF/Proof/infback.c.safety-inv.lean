import ZlibF.Proof.«infback.c.safety-valid»
import ZlibF.Proof.«infback.c.pull»

/-!
# infback.c: the invariant of the dispatch loop over the caller protocol, and `PULL()`

`PInv` is what holds whenever `for (;;) switch (state->mode)` of `inflateBack()` is about to
read the mode. It is stated over the caller protocol of `Goal.inflate_back_sequence_safety`,
with the protocol's observation log as ghost state: the state is valid over the caller's window,
`put`/`left` describe the unwritten tail of the window, the input registers describe the rest of
the chunk `in` returned last (all of which stays readable, outside the window, the stream record
and the state record), the protocol's invariant holds of the log, and the heap differs from the
heap at the call by a `CallbackFrame` and no change of liveness outside the call-backs' blocks.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
set_option autoImplicit false

/-- The protocol of the call-backs of a context. -/
abbrev Proto (c : BCtx) (r : ZStreamRef) (i : Nat) (window : BPtr) (n : Nat) :=
  CallbackProtocol r i window n c.inCb c.inDesc c.outCb c.outDesc

/-- The chunk `held` at `active` is readable, outside the window, the stream record and the state. -/
def ChunkOk (h : Heap) (r : ZStreamRef) (i : Nat) (window : BPtr) (n : Nat) (active : BPtr)
    (held : List UInt8) : Prop :=
  held ≠ [] → Bytes h active held.length held ∧ Separate active held.length window n ∧
    ∀ b, ByteRoot active b → b ≠ i ∧ ¬ StreamRoot r b

/-- **The invariant of the dispatch loop**, relative to the heap `h0` at the call. -/
structure PInv (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 h : Heap) (l : IL) (log : BackLog) : Prop where
  cstrm : c.strm = some r
  cst : c.st = some (.tab i)
  valid : ∃ z s, BackValid h r i z s ∧ s.window = window ∧ s.wsize.toNat = n
  winRoot : ∀ b, ByteRoot window b → b ≠ i ∧ ¬ StreamRoot r b
  put : l.put = advance window (n - l.left.toNat) ∧ l.left.toNat ≤ n
  chunk : l.have_.toNat ≤ log.held.length ∧
    (l.have_ ≠ 0 → l.next = advance log.active (log.held.length - l.have_.toNat))
  held : ChunkOk h r i window n log.active log.held
  bits : l.bits.toNat ≤ 39 ∧ l.hold.toNat < 2 ^ l.bits.toNat
  proto : pr.invariant h log
  frame : CallbackFrame pr.own h0 h r i window n
  live : ∀ b, ¬ pr.own b → (h.live b ↔ h0.live b)

/-- The rank of a mode in the measure: the modes that leave at once rank lowest. -/
def modeRank (m : UInt32) : Nat := if m == DONE || m == BAD then 0 else if m == TYPE then 1 else 2

/-- The measure of the dispatch loop: four times the input bits still readable (held, in the
chunk, and what `in` may still deliver within `inputBound`), plus the rank of the mode. -/
def backMeasure {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h : Heap) (l : IL) (log : BackLog) : Nat :=
  4 * (l.bits.toNat + 8 * l.have_.toNat + 8 * (pr.inputBound - log.supplied.length)) +
    ((h.istates i).map (fun s => modeRank s.mode)).getD 0

theorem advance_zero (p : BPtr) : advance p 0 = p := by
  cases p <;> rfl

/-- The window's views name only writable byte views of blocks outside the changed set. -/
theorem window_views {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {own : Nat → Prop}
    (writable : Writable h window n) (root : ∀ b, ByteRoot window b → b ≠ i ∧ ¬ StreamRoot r b)
    (disjoint : ∀ x, ByteRoot window x → ¬ own x) :
    RegionViews (fun x => StreamRoot r x ∨ x = i ∨ own x) [⟨window, n⟩] := by
  intro ref rootR
  obtain ⟨region, member, off, pointer⟩ := rootR
  simp only [List.mem_singleton] at member
  subst member
  change window = .ref ref off at pointer
  have outside : ∀ b, ByteRoot window b → ¬ (StreamRoot r b ∨ b = i ∨ own b) := by
    intro b rb inside
    obtain ⟨ne, nroot⟩ := root b rb
    rcases inside with x | x | x
    · exact nroot x
    · exact ne x
    · exact disjoint b rb x
  cases ref with
  | blk b => exact Or.inl ⟨b, rfl, outside b (by rw [pointer]; rfl)⟩
  | dstate_depth b => exact Or.inr ⟨b, rfl, outside b (by rw [pointer]; rfl)⟩
  | _ =>
    exfalso
    rcases writable with ⟨null, -⟩ | ⟨ref0, off0, a0, ptr0, -, ro0, -⟩
    · rw [null] at pointer; cases pointer
    · rw [ptr0] at pointer
      injection pointer with e _
      subst e
      cases ro0

/-- The liveness ledger of a call-back step. -/
theorem live_callback {h h' : Heap} {own : Nat → Prop} (frame : ExternalFrame own h h') (b : Nat)
    (notOwn : ¬ own b) : h'.live b ↔ h.live b := by
  constructor
  · intro live'
    exact Classical.byContradiction fun dead => notOwn (frame.2.2.2.1 b dead live')
  · intro live
    exact Frame.live_kept frame.1 live notOwn

/-- The mode rank of the measure reads the state record, which a call-back keeps. -/
theorem rank_frame {h h' : Heap} {own : Nat → Prop} (frame : ExternalFrame own h h') {i : Nat}
    {s : InflateState} (get : h.istates i = some s) (outside : ¬ own i) :
    (h'.istates i).map (fun s => modeRank s.mode) = (h.istates i).map (fun s => modeRank s.mode) := by
  rw [istates_frame frame.1 get outside, get]

/-- **`PULL()` on the invariant.** With input left nothing happens. With the chunk used up, `in`
is called once (the protocol's `inStep`): a non-empty chunk becomes the chunk in use, recorded in
the log; an empty one ends the call with `Z_BUF_ERROR` and `next = NULL`. The measure does not
grow: the bytes `in` hands out were counted as still deliverable. -/
theorem PULL_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog}
    (I : PInv c pr h0 h l log) :
    ∃ res l' h' log', runX (PULL c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → l'.have_ ≠ 0 ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧ l'.put = l.put ∧ l'.left = l.left ∧
        (l'.next = l.next ∨ l.have_ = 0)) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧
      backMeasure pr h' l' log' ≤ backMeasure pr h l log := by
  by_cases hz : l.have_ = 0
  · obtain ⟨k, pointer, after, bytes, run, len, ext, window', fresh, inv'⟩ := pr.inStep h log l.next I.proto
    obtain ⟨z, s, valid, win, size⟩ := I.valid
    have stateOut := pr.disjoint.1
    have rootOut := pr.disjoint.2
    have valid' : BackValid after r i z s :=
      backValid_callback valid ext stateOut rootOut (by rw [win, size]; exact window')
    have writable : Writable h window n := by
      have w := valid.2.2.2.2.2.2.2.2.2.2.1
      rw [win, size] at w; exact w
    have frame' : CallbackFrame pr.own h0 after r i window n :=
      CallbackFrame.trans I.frame (callbackFrame_of_external ext writable)
        (fun disjoint => window_views (valid.2.2.2.2.2.2.2.2.2.2.1 |> fun w => by rw [win, size] at w; exact w)
          I.winRoot disjoint)
    have live' : ∀ b, ¬ pr.own b → (after.live b ↔ h0.live b) :=
      fun b notOwn => (live_callback ext b notOwn).trans (I.live b notOwn)
    have bound := pr.bounded after _ inv'
    simp only [List.length_append] at bound
    have rank := rank_frame ext valid.2.1 stateOut
    by_cases hk : k = 0
    · subst hk
      have bytes0 : bytes = [] := List.eq_nil_of_length_eq_zero (by rw [len]; rfl)
      subst bytes0
      refine ⟨.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }, after, _,
        PULL_noinput hz run,
        { cstrm := I.cstrm, cst := I.cst, valid := ⟨z, s, valid', win, size⟩, winRoot := I.winRoot,
          put := I.put, chunk := ⟨by simp, fun e => absurd rfl e⟩, held := fun e => absurd rfl e,
          bits := I.bits, proto := inv', frame := frame', live := live' },
        fun e => (nomatch e), fun e he => by injection he with he; subst he; exact ⟨rfl, rfl⟩, ?_⟩
      unfold backMeasure
      rw [rank, hz]
      simp only [List.length_append, List.length_nil, Nat.add_zero, UInt32.toNat_zero]
      omega
    · obtain ⟨bytesB, sep, roots⟩ := fresh hk
      have kpos : k.toNat ≠ 0 := fun e => hk (UInt32.toNat_inj.mp (by rw [e]; rfl))
      refine ⟨.ok (), { l with have_ := k, next := pointer }, after, _, PULL_chunk hz hk run,
        { cstrm := I.cstrm, cst := I.cst, valid := ⟨z, s, valid', win, size⟩, winRoot := I.winRoot,
          put := I.put, chunk := ⟨by show k.toNat ≤ bytes.length; rw [len]; exact Nat.le_refl _,
            fun _ => by simp [len, advance_zero]⟩,
          held := fun _ => ⟨by rw [len]; exact bytesB, by rw [len]; exact sep, roots⟩,
          bits := I.bits, proto := inv', frame := frame', live := live' },
        fun _ => ⟨hk, rfl, rfl, rfl, rfl, Or.inr hz⟩, fun e he => (nomatch he), ?_⟩
      unfold backMeasure
      rw [rank, hz]
      simp only [UInt32.toNat_zero, List.length_append, len]
      rw [len] at bound
      omega
  · refine ⟨.ok (), l, h, log, PULL_have hz, I, fun _ => ⟨hz, rfl, rfl, rfl, rfl, Or.inl rfl⟩,
      fun e he => (nomatch he), Nat.le_refl _⟩

end Zlib.Infback.Safety
