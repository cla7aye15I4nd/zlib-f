import ZlibF.Proof.«inflate.c.completes-room-modes»
import ZlibF.Proof.«inflate.c.completes-observe-avail»
import ZlibF.Proof.«inflate.c.completes-interface»
import ZlibF.Proof.«inflate.c.ret-loop»
import ZlibF.Proof.«inflate.c.sync2»
import ZlibF.Proof.«inflate.c.invariant-bridge»
import ZlibF.Proof.«inflate.c.default-local»

/-!
# inflate.c: a call blocked with input left stopped in LIT, MATCH or COPY

`BlockedLeave` from two premises:

* `LeaveRetCodes`: a leave of the decoder loop of a call, from a decoder with the
  invariant, has `ret` in `Z_OK`, `Z_STREAM_END` or `Z_DATA_ERROR`
  (`PublicLeaveRet`). This is the conclusion of `inflate_run_leave_ret_codes`
  (`inflate.c.ret-loop`), proved there for the default configuration; the general
  form is the inflate owner's (`worker/gzip`). `leaveRetCodes_default` gives it for
  the default configuration.
* `GzipFieldLeaves` (`inflate.c.completes-room-modes`).

The loop leaves only for a `RoomCause` (`roomX_inflate_run`) or returns early with
another code; it never ends normally (`inflate_run_not_ok`). `inf_leave` returns
`Z_MEM_ERROR`, `ret`, or `Z_BUF_ERROR` for `ret == Z_OK` (`inflate_leave_ret`),
stores `have` and `left` into the stream (`inflate_leave_avail`) and keeps the
decoder's mode and length unless it returns `Z_MEM_ERROR` (`rcFrame_inflate_leave`).
A call that returns `Z_OK` or `Z_BUF_ERROR` with input left therefore left for want
of room, in `LIT`, `MATCH`, or `COPY` with bytes left.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public Zlib.Inflate.KeepProofs
set_option autoImplicit false

/-! ## The loop never ends normally -/

theorem cwhile_last {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (Q : σ → Prop)
    (hc : ∀ s h s' h', cond s h = .ok ((false, s'), h') → Q s') :
    ∀ n s h res h', cwhile.go cond body n s h = .ok (res, h') → Q res := by
  intro n
  induction n with
  | zero => intro s h res h' run; cases run
  | succ n ih =>
    intro s h res h' run
    simp only [cwhile.go, bind_app] at run
    cases condition : cond s h with
    | error fault => rw [condition] at run; cases run
    | ok pair =>
      obtain ⟨⟨test, next⟩, heap1⟩ := pair
      rw [condition] at run
      cases test with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
        cases run
        exact hc s h _ _ condition
      | true =>
        simp only [ite_true, bind_app] at run
        cases executed : body next heap1 with
        | error fault => rw [executed] at run; cases run
        | ok pair =>
          obtain ⟨next2, heap2⟩ := pair
          rw [executed] at run
          exact ih next2 heap2 res h' run

/-- `while (1)` whose body never breaks ends only with an exit. -/
theorem xwhileBrk_true_not_ok {body : X Bool}
    (nobreak : ∀ l h l' h', runX body l h = .ok ((.ok true, l'), h') → False)
    {l l' : IL} {h h' : Heap} {u : Unit}
    (run : runX (xwhileBrk (pure true) body) l h = .ok ((.ok u, l'), h')) : False := by
  unfold xwhileBrk runX at run
  simp only [ExceptT.run, ExceptT.mk, StateT.run, bind_app] at run
  generalize hcw : cwhile _ _ (l, Stop.go) h = cw at run
  cases cw with
  | error fault => cases run
  | ok pair =>
    obtain ⟨⟨regs, stop⟩, heap⟩ := pair
    have notGo : stop ≠ Stop.go := by
      have := cwhile_last (body := _) (fun st : IL × Stop => st.2 ≠ Stop.go) ?_ _ _ _ _ _ hcw
      · exact this
      · intro ⟨cur, st⟩ h0 s' h1 e
        cases st with
        | go =>
          dsimp only at e
          simp only [pure, ExceptT.pure, ExceptT.mk, StateT.pure] at e
          have e' : (Except.ok ((true, (cur, Stop.go)), h0) : Except Fault ((Bool × IL × Stop) × Heap)) =
              Except.ok ((false, s'), h1) := e
          simp at e'
        | brk => simp only [pure_app] at e; cases e; simp
        | ex x => simp only [pure_app] at e; cases e; simp
    have notBrk : stop ≠ Stop.brk := by
      have := cwhile_success_invariant (fun (st : IL × Stop) (_ : Heap) => st.2 ≠ Stop.brk) ?_ ?_
        (by simp) hcw
      · exact this
      · intro ⟨cur, st⟩ h0 test next h1 current e
        cases st with
        | go =>
          dsimp only at e
          simp only [pure, ExceptT.pure, ExceptT.mk, StateT.pure] at e
          have e' : (Except.ok ((true, (cur, Stop.go)), h0) : Except Fault ((Bool × IL × Stop) × Heap)) =
              Except.ok ((test, next), h1) := e
          simp only [Except.ok.injEq, Prod.mk.injEq] at e'
          obtain ⟨⟨_, rfl⟩, _⟩ := e'
          simp
        | brk => exact absurd rfl current
        | ex x => simp only [pure_app] at e; cases e; simp
      · intro ⟨cur, st⟩ h0 next h1 _ e
        simp only [bind_app] at e
        cases b : body cur h0 with
        | error fault => rw [b] at e; cases e
        | ok pair =>
          obtain ⟨⟨result, regs1⟩, heap1⟩ := pair
          rw [b] at e
          simp only [pure_app] at e
          cases result with
          | ok v =>
            cases v with
            | true => exact (nobreak cur h0 regs1 heap1 b).elim
            | false => cases e; simp
          | error x => cases e; simp
    cases stop with
    | go => exact notGo rfl
    | brk => exact notBrk rfl
    | ex x => simp only [pure_app] at run; cases run

/-- A run of `p >>= k` that ends normally ends with a normal run of `k`. -/
theorem xbind_ok {α β : Type} {p : X α} {k : α → X β} {l l' : IL} {h h' : Heap} {v : β}
    (run : runX (p >>= k) l h = .ok ((.ok v, l'), h')) :
    ∃ a l1 h1, runX (k a) l1 h1 = .ok ((.ok v, l'), h') := by
  rw [runX_bind] at run
  split at run
  · exact ⟨_, _, _, run⟩
  · cases run
  · cases run

/-- The decoder loop of `inflate()` never ends normally. -/
theorem inflate_run_not_ok {c : Ctx} {l l' : IL} {h h' : Heap} {u : Unit}
    (run : runX (inflate_run c) l h = .ok ((.ok u, l'), h')) : False := by
  unfold inflate_run at run
  obtain ⟨_, _, _, run⟩ := xbind_ok run
  try dsimp only at run
  split at run
  all_goals
    repeat (first | (obtain ⟨_, _, _, run⟩ := xbind_ok run; try dsimp only at run))
    unfold xwhile at run
    exact xwhileBrk_true_not_ok (fun l0 h0 l1 h1 e => by
      rw [runX_bind] at e
      split at e
      · rw [runX_pure] at e; cases e
      · cases e
      · cases e) run

/-! ## The return code of `inf_leave` -/

/-- Every successful run returns a value with `P`. -/
def RetIs (P : Int32 → Prop) (m : M Int32) : Prop := ∀ h v h', m h = .ok (v, h') → P v

theorem RetIs.pure {P : Int32 → Prop} (v : Int32) (hv : P v) : RetIs P (Pure.pure v) := by
  intro h v' h' run
  cases run
  exact hv

theorem RetIs.bind {α : Type} {P : Int32 → Prop} {m : M α} {f : α → M Int32}
    (hf : ∀ a, RetIs P (f a)) : RetIs P (m >>= f) := by
  intro h v h' run
  obtain ⟨a, h1, _, run1⟩ := KeepProofs.bind_ok run
  exact hf a h1 v h' run1

theorem RetIs.ite {P : Int32 → Prop} (p : Prop) [Decidable p] {a b : M Int32}
    (ha : p → RetIs P a) (hb : ¬ p → RetIs P b) : RetIs P (if p then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- `inf_leave` returns `Z_MEM_ERROR`, `ret`, or `Z_BUF_ERROR` when `ret == Z_OK`. -/
theorem inflate_leave_ret (c : Ctx) (l : IL) :
    RetIs (fun v => v = Z_MEM_ERROR ∨ v = l.ret ∨ (v = Z_BUF_ERROR ∧ l.ret = Z_OK))
      (inflate_leave c l) := by
  unfold inflate_leave
  repeat' first
    | exact RetIs.pure _ (Or.inl rfl)
    | exact RetIs.pure _ (Or.inr (Or.inl rfl))
    | exact RetIs.pure _ (Or.inr (Or.inr ⟨rfl, by simp_all⟩))
    | refine RetIs.ite _ (fun _ => ?_) (fun _ => ?_)
    | refine RetIs.bind (fun _ => ?_)
    | split
    | intro _

#print axioms inflate_leave_ret

/-! ## The call -/

theorem Live.syncAlloc {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (live : Live h r i z s) : Live (syncAlloc h) r i z s := by
  obtain ⟨hz, hs, zst, back, mode, za, zf⟩ := live
  refine ⟨?_, by simpa using hs, zst, back, mode, za, zf⟩
  cases r <;> simpa [ZStreamRef.get] using hz

theorem freeB_tables {p : BPtr} {h h' : Heap} {u : Unit} (run : freeB p h = .ok (u, h')) :
    h'.istates = h.istates ∧ h'.streams = h.streams ∧ h'.gzstates = h.gzstates := by
  unfold freeB at run
  repeat' first | (cases run; exact ⟨rfl, rfl, rfl⟩) | split at run | (simp at run)

/-- `BlockedLeave`, from the return codes of a loop leave and the gzip field modes. -/
theorem blocked_leave (codesOK : LeaveRetCodes) (gz : GzipFieldLeaves) : BlockedLeave := by
  intro h r i0 z0 s0 flush rc after z inv fit buffers active run hz notBlock notTrees codes left
  have live' := Live.syncAlloc inv.good.live
  unfold C.run Zlib.Inflate.inflate at run
  obtain ⟨hbuf, h1, ealloc, run1⟩ := KeepProofs.bind_ok run
  rw [allocLocalB_run h inv.good.fresh] at ealloc
  cases ealloc
  obtain ⟨res, h2, ebody, run2⟩ := KeepProofs.bind_ok run1
  obtain ⟨u, h3, efree, run3⟩ := KeepProofs.bind_ok run2
  cases run3
  have refusal : rc ≠ Z_STREAM_ERROR := by
    rcases codes with e | e <;> rw [e] <;> decide
  by_cases accepted : (z0.next_out == .null || (z0.next_in == .null && z0.avail_in != 0)) = false
  · simp only [bind_app, stateCheck_live live', bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok live'.hz, accepted, live'.zst, castI] at ebody
    have nonnull : z0.next_out ≠ .null := by
      intro e; rw [e] at accepted; simp at accepted
    have inputValid : z0.next_in = .null → z0.avail_in = 0 := by
      intro e
      rw [e] at accepted
      simp only [Bool.or_eq_false_iff, beq_iff_eq, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at accepted
      rcases accepted.2 with x | x
      · simp at x
      · exact x
    let c : Ctx := ⟨some r, some (.tab i0), syncBuf h, flush⟩
    generalize hR : (ExceptT.run (inflate_run c)).run IL.init (syncAlloc h) = R at ebody
    have erun : runX (inflate_run c) IL.init (syncAlloc h) = R := hR
    cases R with
    | error fault => cases ebody
    | ok triple =>
      obtain ⟨⟨res, regs⟩, hr⟩ := triple
      have room := roomX_inflate_run gz c IL.init (syncAlloc h) res regs hr trivial erun
      cases res with
      | ok v => exact (inflate_run_not_ok erun).elim
      | error exit =>
        cases exit with
        | ret v =>
          simp only [pure_app] at ebody
          cases ebody
          have code := room (.ret rc) rfl
          rcases codes with e | e
          · exact absurd e code.1
          · exact absurd e code.2
        | leave =>
          dsimp only at ebody
          have cause : RoomCause c.flush c.st regs hr := room .leave rfl
          have retCode := inflate_leave_ret c regs hr rc h2 ebody
          have publicRet := codesOK h r i0 z0 s0 flush regs hr inv fit buffers active nonnull inputValid erun
          have retOk : regs.ret = Z_OK := by
            rcases retCode with mem | same | ⟨_, ok⟩
            · rcases codes with e | e <;> rw [e] at mem <;> exact absurd mem (by decide)
            · rcases publicRet with p | p | p
              · exact p
              · rcases codes with e | e <;> rw [← same, e] at p <;> exact absurd p (by decide)
              · rcases codes with e | e <;> rw [← same, e] at p <;> exact absurd p (by decide)
            · exact ok
          have notMem : rc ≠ Z_MEM_ERROR := by rcases codes with e | e <;> rw [e] <;> decide
          obtain ⟨z2, get2, availIn, availOut⟩ := Avail.inflate_leave_avail r c rfl regs ebody
          obtain ⟨ist, str, gzs⟩ := freeB_tables efree
          have zSame : z2 = z := by
            have : r.get after = r.get h2 := by
              cases r <;> simp [ZStreamRef.get, str, gzs]
            rw [this, get2] at hz
            exact Option.some.inj hz
          subst zSame
          have haveNz : regs.have_ ≠ 0 := by rw [← availIn]; exact left
          rcases cause with h0 | b | tr | rn | ⟨left0, ⟨i, s, st, get, holding⟩⟩
          · exact absurd h0 haveNz
          · exact absurd b notBlock
          · exact absurd tr notTrees
          · exact absurd retOk rn
          · have sameI : i = i0 := by
              have : (some (InflateStateRef.tab i0) : InflateStatePtr) = some (.tab i) := st
              cases this
              rfl
            subst sameI
            have frame := ModeLen.rcFrame_inflate_leave r c rfl regs hr rc h2 ebody notMem
            unfold ModeLen.WindowFrame ModeLen.decoderWindows at frame
            have at_i := congrFun frame i
            rw [get] at at_i
            cases g2 : h2.istates i with
            | none => rw [g2] at at_i; cases at_i
            | some s2 =>
              rw [g2] at at_i
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at at_i
              refine ⟨by rw [availOut, left0], s2, by rw [ist]; exact g2, ?_⟩
              rw [at_i.1, at_i.2]
              exact holding
  · have refused : (z0.next_out == .null || (z0.next_in == .null && z0.avail_in != 0)) = true := by
      cases e : (z0.next_out == .null || (z0.next_in == .null && z0.avail_in != 0))
      · exact absurd e accepted
      · rfl
    simp only [bind_app, stateCheck_live live', bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok live'.hz, refused, ite_true, pure_app] at ebody
    cases ebody
    exact absurd rfl refusal

#print axioms blocked_leave

/-- `LeaveRetCodes` in the default configuration (raw or zlib wrapper), from
`inflate_run_leave_ret_codes`. -/
theorem leaveRetCodes_default {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    {flush : Int32} {regs : IL} {after : Heap}
    (inv : InflateInv h r i z s) (config : DefaultConfig s) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : StreamBuffers h r) (_active : ActiveHeader h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run ⟨some r, some (.tab i), syncBuf h, flush⟩) IL.init (syncAlloc h) =
      .ok ((.error .leave, regs), after)) :
    PublicLeaveRet regs := by
  have invariant := (inv.to_origin fit).toDefaultStateJ
  have allocated := default_state_syncAlloc invariant
  have env : Env ⟨some r, some (.tab i), syncBuf h, flush⟩ (syncAlloc h) r i z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have local_ : HeaderLocal ⟨some r, some (.tab i), syncBuf h, flush⟩ (syncAlloc h) r s (dispatchRegs z s) :=
    entry_header_local invariant.good.fresh (ActiveHeader.entry _active inv.good.live) flush
  exact inflate_run_leave_ret_codes env allocated (streamBuffers_syncAlloc invariant.good.fresh buffers)
    nonnull inputValid local_ run

#print axioms leaveRetCodes_default
end Zlib.Inflate.Proofs
