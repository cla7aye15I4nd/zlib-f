import ZlibF.Proof.«inffast.c.call-origin»
import ZlibF.Proof.«inffast.c.body-token»
import ZlibF.Proof.«inffast.c.body-token-reject»
import ZlibF.Proof.«inflate.c.meaning-fast-token»

/-!
# inffast.c: the tokens of one whole `inflate_fast` call

`actual_body_refines_token` gives one token per pass of the do-while loop of
`inflate_fast`, against the saved window and the output of the call so far,
on the remaining input of the call. `actual_body_preserves_origin` places the
remaining input of each pass in the input of the call. This file composes the
passes over the loop and through the epilogue (unused whole bytes returned,
counters written back).

The composition is generic in the fact `Q used current` that the caller keeps
about the input bits consumed so far (`used`, counted from the bits held at
entry) and the output since the call's output start (`current`): the caller
supplies `Q 0` at entry and shows that `Q` survives a token (in the decoder,
`DeflateParsed` with one more `DeflateParsed.token`).

Input and output are raw byte blocks, distinct or disjoint ranges of one
block (`Env.hsep`). The loop keeps the unread input in the output array
(`EnvG.InputFrame`): the decoder writes only in the output range.
-/

namespace Zlib.Inffast.Proofs.FastMeaning
open C Zlib.Inffast Zlib.Inffast.Proofs Zlib.Inffast.Spec ZlibF.Spec ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- The history the fast decoder copies from: the window's bytes in order. -/
def hist (e : Env) : List UInt8 :=
  MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff

/-- The output of the call so far, at `[bg, o)` of the output array. -/
def cur (e : Env) (A : Array UInt8) (o : Nat) : List UInt8 := writtenBytes A o (o - e.bg)

/-- The rest of the call's input after `used` consumed bits. -/
def src (e : Env) (used : Nat) : List Bool := (Origin.initial e).drop used

/-- An end-of-block token writes nothing. -/
theorem Token.Step.end_out {LL DD : List Nat} {dict h : List UInt8} {inp rest : List Bool}
    {out : List UInt8} (step : Token.Step LL DD dict h inp rest out true) : out = h := by
  cases step
  rfl

theorem heap_inj (e : Env) {A B : Array UInt8} {p q : BPtr} {m n : UInt32}
    (same : e.heap A p m = e.heap B q n) : A = B ∧ p = q ∧ m = n := by
  have bytes := congrArg (fun h => h.bytes e.ob) same
  simp only [e.heap_bytes_ob, Option.some.injEq] at bytes
  exact ⟨bytes, e.heap_msg_mode_eq same⟩

/-- One pass of the loop: its token, with the origin of the input before and
after it. -/
theorem body_step (e : Env) (c : Ctx) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o u : Nat) (LL DD : List Nat)
    (pre : StepPre e c A l i o) (tables : BodyToken.Tables e LL DD)
    (lenPrefix : Zlib.Inftrees.Proofs.PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat)
    (distPrefix : Zlib.Inftrees.Proofs.PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i u) :
    ∃ (l' : L) (A' : Array UInt8) (msg' : BPtr) (mode' : UInt32) (i' o' u' : Nat),
      C.run (inflate_fast_body c l) (e.heap A msg mode) = .ok (l', e.heap A' msg' mode') ∧
      LS e l' i' o' ∧ o ≤ o' ∧ o' ≤ o + 258 ∧ A'.size = A.size ∧
      Origin.Inv e l'.hold.toNat l'.bits.toNat i' u' ∧ u ≤ u' ∧ (∀ j, (j < o ∨ o' ≤ j) → A'[j]? = A[j]?) ∧
      ((l'.broke = false ∧ msg' = msg ∧ mode' = mode ∧ o < o' ∧
          Token.Step LL DD (hist e) (cur e A o) (src e u) (src e u') (cur e A' o') false) ∨
       (l'.broke = true ∧ mode' = TYPE ∧
          Token.Step LL DD (hist e) (cur e A o) (src e u) (src e u') (cur e A' o') true) ∨
       (l'.broke = true ∧ mode' = BAD ∧ cur e A' o' = cur e A o ∧
          ∀ more, Token.Rejected LL DD (hist e) (cur e A o) ((src e u).take (u' - u) ++ more))) := by
  obtain ⟨l', after, input', output', result, resultMsg, resultMode, run, post, locals, size,
    heapEq, outcome⟩ := actual_body_refines_token e c A msg mode l i o LL DD pre tables
  obtain ⟨l1, h1, run1, _, j, k, u', locals1, origin', le⟩ :=
    actual_body_preserves_origin e c A msg mode l i o u pre origin
  obtain ⟨same1, same2⟩ := Prod.mk.inj (Except.ok.inj (run1.symm.trans run))
  subst same1 same2
  have sameIn : j = input' := by
    have eq := Ptr.ref.inj (locals1.hin.symm.trans locals.hin)
    omega
  have sameOut : k = output' := by
    have eq := Ptr.ref.inj (locals1.hout.symm.trans locals.hout)
    omega
  subst sameIn sameOut
  obtain ⟨i'', o'', A'', msg'', mode'', locals2, _, _, oo, o258, _, heap2, _, frameP, cont, _⟩ :=
    post
  have sameOut2 : o'' = k := by
    have eq := Ptr.ref.inj (locals2.hout.symm.trans locals.hout)
    omega
  subst sameOut2
  obtain ⟨arr, msgEq, modeEq⟩ := heap_inj e (heap2.symm.trans heapEq)
  subst arr msgEq modeEq
  have source : Sg e l.hold.toNat l.bits.toNat i = src e u := origin.stream
  have rest : Sg e l1.hold.toNat l1.bits.toNat j = src e u' := origin'.stream
  simp only [] at outcome
  rw [source, rest] at outcome
  have runH : C.run (inflate_fast_body c l) (e.heap A msg mode) = .ok (l1, e.heap A'' msg'' mode'') :=
    heapEq ▸ run
  refine ⟨l1, A'', msg'', mode'', j, o'', u', runH, locals, oo, o258, size, origin', le, frameP, ?_⟩
  rcases outcome with ⟨stopped, step⟩ | ⟨stopped, typeMode, step⟩ | ⟨stopped, badMode, same, _⟩
  · obtain ⟨progress, msgSame, modeSame⟩ := cont stopped
    exact Or.inl ⟨stopped, msgSame, modeSame, progress, step⟩
  · exact Or.inr (Or.inl ⟨stopped, typeMode, step⟩)
  · refine Or.inr (Or.inr ⟨stopped, badMode, same, ?_⟩)
    obtain ⟨l2, h2, run2, reject⟩ := BodyTokenReject.actual_body_rejects_prefix e c A msg mode l i o
      LL DD pre tables lenPrefix distPrefix
    obtain ⟨sameL, sameH⟩ := Prod.mk.inj (Except.ok.inj (run2.symm.trans runH))
    subst sameL sameH
    obtain ⟨j2, _, k, locals2, restK, rejected⟩ :=
      reject A'' msg'' stopped (by rw [badMode])
    have sameJ : j2 = j := by
      have eq := Ptr.ref.inj (locals2.hin.symm.trans locals.hin)
      omega
    subst sameJ
    rw [source, rest] at restK
    have lengths := (BodyTokenReject.origin_length origin').1
    have drops : (src e u).drop k = (src e u).drop (u' - u) := by
      rw [← restK]
      simp only [src, List.drop_drop]
      congr 1
      omega
    have cut : (src e u).take k = (src e u).take (u' - u) :=
      BodyTokenReject.take_of_drop_eq drops (by simp only [src, List.length_drop]; omega)
    intro more
    rw [← cut]
    have r := rejected more
    rw [source] at r
    exact r

/-- What the loop ends with, for the fact `Q` kept between tokens. -/
def LoopEnd (e : Env) (LL DD : List Nat) (Q : Nat → List UInt8 → Prop) (l : L) (h : Heap) : Prop :=
  ∃ (i o : Nat) (A : Array UInt8) (msg : BPtr) (mode : UInt32) (u : Nat),
    LS e l i o ∧ o ≤ e.o0 + e.sm0.avail_out.toNat ∧ A.size = e.A0.size ∧
    h = e.heap A msg mode ∧ Origin.Inv e l.hold.toNat l.bits.toNat i u ∧ e.InputFrame A e.i0 ∧
    ((l.broke = false ∧ mode = e.s0.mode ∧ Q u (cur e A o)) ∨
     (l.broke = true ∧ mode = TYPE ∧ ∃ u0, u0 ≤ u ∧ Q u0 (cur e A o) ∧
        Token.Step LL DD (hist e) (cur e A o) (src e u0) (src e u) (cur e A o) true) ∨
     (l.broke = true ∧ mode = BAD ∧ ∃ u0, u0 ≤ u ∧ Q u0 (cur e A o) ∧
        ∀ more, Token.Rejected LL DD (hist e) (cur e A o) ((src e u0).take (u - u0) ++ more)))

/-- The do-while loop of `inflate_fast` keeps `Q` over its tokens. -/
theorem loop_tokens (e : Env) (c : Ctx) (hc : CtxOK e c) (LL DD : List Nat)
    (tables : BodyToken.Tables e LL DD)
    (lenPrefix : Zlib.Inftrees.Proofs.PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat)
    (distPrefix : Zlib.Inftrees.Proofs.PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat) (Q : Nat → List UInt8 → Prop)
    (step : ∀ u u' current next, u ≤ u' → Q u current →
      Token.Step LL DD (hist e) current (src e u) (src e u') next false → Q u' next)
    (l : L) (i o : Nat) (A : Array UInt8) (u : Nat)
    (hl : LS e l i o) (hA : A.size = e.A0.size) (hb : l.broke = false)
    (hi : i + 6 ≤ e.i0 + e.sm0.avail_in.toNat)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i u) (hfr : e.InputFrame A e.i0)
    (q : Q u (cur e A o)) :
    Wp (cdoWhile (inflate_fast_body c)
      (fun l => do
        if l.broke then pure (false, l)
        else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
        else pure (false, l)) l) (e.heap A e.sm0.msg e.s0.mode) (LoopEnd e LL DD Q) := by
  let Inv : L → Heap → Prop := fun l h => ∃ i o A u,
    LS e l i o ∧ A.size = e.A0.size ∧ h = e.heap A e.sm0.msg e.s0.mode ∧ l.broke = false ∧
    i + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o + 258 ≤ e.o0 + e.sm0.avail_out.toNat ∧
    Origin.Inv e l.hold.toNat l.bits.toNat i u ∧ e.InputFrame A e.i0 ∧ Q u (cur e A o)
  let μ : L → Nat := fun l => match l.out with
    | .null => 0
    | .ref _ k => e.o0 + e.sm0.avail_out.toNat - k
  have hμ : ∀ l i o, LS e l i o → μ l = e.o0 + e.sm0.avail_out.toNat - o := by
    intro l i o hl
    simp only [μ, hl.hout]
  refine Wp.cdoWhile Inv μ _ ?_ ⟨i, o, A, u, hl, hA, rfl, hb, hi, ho, origin, hfr, q⟩ ?_
  · intro l h hI
    obtain ⟨i, o, A, u, hl, hA, rfl, hb, hi, ho, origin, hfr, q⟩ := hI
    have pre : StepPre e c A l i o := ⟨hc, hl, hA, hi, ho, hb, hfr.mono hl.hi0⟩
    obtain ⟨l1, A', msg', mode', i', o', u', run, hl', oo, o258, size, origin', le, frameOut, outcome⟩ :=
      body_step e c A e.sm0.msg e.s0.mode l i o u LL DD pre tables lenPrefix distPrefix origin
    have hAsz : A'.size = e.A0.size := size.trans hA
    have hoend : o' ≤ e.o0 + e.sm0.avail_out.toNat := by omega
    have frame' : e.InputFrame A' e.i0 :=
      hfr.write (Nat.le_refl _) (Nat.le_refl _) hl.ho0 hoend size frameOut
    refine ⟨l1, _, run, ?_⟩
    rcases outcome with ⟨stop, msgEq, modeEq, progress, tok⟩ | ⟨stop, modeEq, tok⟩ |
        ⟨stop, modeEq, same, rejected⟩
    · subst msgEq modeEq
      have q' := step u u' _ _ le q tok
      have hcnd := fast_cond_live hc A' e.sm0.msg e.s0.mode l1 i' o' hl' hAsz hoend stop
      by_cases hroom : i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧
          o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat
      · refine Or.inr ⟨l1, _, ?_, ⟨i', o', A', u', hl', hAsz, rfl, stop, hroom.1, hroom.2,
          origin', frame', q'⟩, ?_⟩
        · simpa [stop, hroom.1, hroom.2] using hcnd
        · rw [hμ _ _ _ hl', hμ _ _ _ hl]
          omega
      · refine Or.inl ⟨l1, _, ?_, i', o', A', e.sm0.msg, e.s0.mode, u', hl', hoend, hAsz, rfl,
          origin', frame', Or.inl ⟨stop, rfl, q'⟩⟩
        have hcfalse : (decide (i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat) &&
            decide (o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        simpa [stop, hcfalse] using hcnd
    · have same := Token.Step.end_out tok
      refine Or.inl ⟨l1, _, by simp [stop], i', o', A', msg', mode', u', hl', hoend, hAsz, rfl,
        origin', frame', Or.inr (Or.inl ⟨stop, modeEq, u, le, ?_, ?_⟩)⟩
      · rw [same]; exact q
      · rw [same] at tok ⊢; exact tok
    · refine Or.inl ⟨l1, _, by simp [stop], i', o', A', msg', mode', u', hl', hoend, hAsz, rfl,
        origin', frame', Or.inr (Or.inr ⟨stop, modeEq, u, le, ?_, ?_⟩)⟩
      · rw [same]; exact q
      · rw [same]; exact rejected
  · rw [hμ _ _ _ hl]
    apply lt_fuel_of
    have := UInt32.toNat_lt e.sm0.avail_out
    have := hl.ho0
    omega

/-- The final heap of a fast call: output array `A`, message `msg`, the
state's mode, bit buffer and the stream cursors. -/
def finalHeap (e : Env) (A : Array UInt8) (msg : BPtr) (mode : UInt32) (hold : UInt64)
    (bits : UInt32) (used o : Nat) : Heap :=
  e.r.put
    { e.h0 with bytes := upd e.h0.bytes e.ob (some A), istates := upd e.h0.istates e.stid (some { e.s0 with mode, hold, bits }) }
    { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + used), next_out := .ref (.blk e.ob) o, avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - (o - e.o0)), msg }

/-- The epilogue: whole unused bytes are returned, fewer than 8 bits stay,
and the input after them is the same. -/
theorem finish_tokens (e : Env) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (usedBits : Nat) (origin : Origin.Inv e l.hold.toNat l.bits.toNat i usedBits)
    (hfr : e.InputFrame A i) :
    Wp (do
      let len := l.bits >>> 3
      let input ← subn l.in_ len
      let bits := l.bits - (len <<< 3)
      let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
      let ai : Int64 ←
        if ← Ptr.lt input (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5)) then do
          let d ← Ptr.diff (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5)) input
          chk64 (5 + d.toInt)
        else do
          let d ← Ptr.diff input (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5))
          chk64 (5 - d.toInt)
      let ao : Int64 ←
        if ← Ptr.lt l.out (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257)) then do
          let d ← Ptr.diff (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257)) l.out
          chk64 (257 + d.toInt)
        else do
          let d ← Ptr.diff l.out (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257))
          chk64 (257 - d.toInt)
      let sm ← ldZStream e.strm
      stZStream e.strm { sm with next_in := input, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
      let st ← ldInflateState (some (.tab e.stid))
      stInflateState (some (.tab e.stid)) { st with hold, bits })
      (e.heap A msg mode) (fun _ after => ∃ (hold : UInt64) (bits : UInt32) (used : Nat),
        after = finalHeap e A msg mode hold bits used o ∧ used ≤ e.sm0.avail_in.toNat ∧
        bits.toNat < 8 ∧ Origin.Inv e hold.toNat bits.toNat (e.i0 + used) usedBits ∧
        Sg e hold.toNat bits.toNat (e.i0 + used) = Sg e l.hold.toNat l.bits.toNat i) := by
  let buf := l.bits.toNat / 8
  let used := i - e.i0 - buf
  let produced := o - e.o0
  let bits := l.bits - ((l.bits >>> 3) <<< 3)
  let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  have hbuf : buf ≤ i - e.i0 := hl.buffered_le
  have hused : used + buf = i - e.i0 := by dsimp only [used]; omega
  have hui : used + buf ≤ e.sm0.avail_in.toNat := by have := hl.hi0; have := hl.hi1; omega
  have hup : produced ≤ e.sm0.avail_out.toNat := by dsimp only [produced]; have := hl.ho0; omega
  have hio : i - (l.bits >>> 3).toNat = e.i0 + used := by
    rw [bits_whole]
    change i - buf = e.i0 + used
    have := hl.hi0
    omega
  have hout : o = e.o0 + produced := by dsimp only [produced]; have := hl.ho0; omega
  have hbits : bits.toNat < 8 := by dsimp only [bits]; rw [bits_residual _ hl.hb]; omega
  have hinbuf : OkOn (e.heap A msg mode) (subn l.in_ (l.bits >>> 3))
      (.ref (BRef.blk e.ib) (e.i0 + used)) := by
    rw [hl.hin]
    have hr := subn_ok (h := e.heap A msg mode) (r := BRef.blk e.ib) (a := e.inArr A) (e.heap_bytes_in A msg mode)
      (n := l.bits >>> 3) (off := i) (by rw [bits_whole]; have := hl.hi0; omega)
      (by have := hl.hi1; have := e.hINsz; have := e.inArr_size hfr; omega)
    simpa only [hio] using hr
  refine Wp.bindO hinbuf ?_
  refine Wp.bindO (shl32_ok (x := 1) (n := bits) (by omega)) ?_
  have hu32 : e.sm0.avail_in.toNat - used < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_in; omega
  have ho32 : e.sm0.avail_out.toNat - produced < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_out; omega
  have hei : e.i0 + e.sm0.avail_in.toNat - 5 + 5 - (e.i0 + used) = e.sm0.avail_in.toNat - used := by
    have := e.hai; omega
  refine ptr_avail_wp (h := e.heap A msg mode) (r := BRef.blk e.ib) (A := e.inArr A)
    (p := e.i0 + used) (q := e.i0 + e.sm0.avail_in.toNat - 5) (k := 5)
    (e.heap_bytes_in A msg mode) (by have := e.hINsz; have := e.inArr_size hfr; omega)
    (by have := e.hINsz; have := e.inArr_size hfr; omega)
    (by rw [e.inArr_size hfr]; exact e.hINbig) (by have := e.hai; omega) (by decide) (by rw [hei]; exact hu32) ?_
  rw [hei]
  rw [hl.hout]
  have heo : e.o0 + e.sm0.avail_out.toNat - 257 + 257 - o = e.sm0.avail_out.toNat - produced := by
    have := e.hao; omega
  refine ptr_avail_wp (h := e.heap A msg mode) (r := BRef.blk e.ob) (A := A)
    (p := o) (q := e.o0 + e.sm0.avail_out.toNat - 257) (k := 257)
    (e.heap_bytes_ob A msg mode) (by rw [hAsz]; have := e.hAsz; omega) (by rw [hAsz]; have := e.hAsz; omega)
    (by rw [hAsz]; exact e.hAbig) (by have := e.hao; omega) (by decide) (by rw [heo]; exact ho32) ?_
  rw [heo]
  rw [i64_to_u32_eq _ hu32, i64_to_u32_eq _ ho32]
  refine Wp.of_eq (fast_stores_run e A msg mode (.ref (BRef.blk e.ib) (e.i0 + used)) (.ref (BRef.blk e.ob) o)
    (UInt32.ofNat (e.sm0.avail_in.toNat - used)) (UInt32.ofNat (e.sm0.avail_out.toNat - produced)) hold bits) ?_
  have rollback := actual_rollback_preserves_origin e A msg mode l i o usedBits hl origin hfr
  have sameIndex : i - l.bits.toNat / 8 = e.i0 + used := by simpa only [bits_whole] using hio
  refine ⟨hold, bits, used, by rfl, Nat.le_trans (Nat.le_add_right _ _) hui, hbits, ?_, ?_⟩
  · simpa only [sameIndex] using rollback.2.2.1
  · simpa only [sameIndex] using rollback.2.2.2

/-- The tokens of one whole fast call, on the exact final heap. -/
theorem fast_call_tokens (e : Env) (LL DD : List Nat) (tables : BodyToken.Tables e LL DD)
    (lenPrefix : Zlib.Inftrees.Proofs.PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat)
    (distPrefix : Zlib.Inftrees.Proofs.PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat)
    (Q : Nat → List UInt8 → Prop)
    (step : ∀ u u' current next, u ≤ u' → Q u current →
      Token.Step LL DD (hist e) current (src e u) (src e u') next false → Q u' next)
    (q0 : Q 0 (cur e e.A0 e.o0)) :
    ∃ (A : Array UInt8) (msg : BPtr) (mode : UInt32) (hold : UInt64) (bits : UInt32)
      (used o u : Nat),
      C.run (inflate_fast e.strm e.start) e.h0 =
        .ok ((), finalHeap e A msg mode hold bits used o) ∧
      used ≤ e.sm0.avail_in.toNat ∧ e.o0 ≤ o ∧ o ≤ e.o0 + e.sm0.avail_out.toNat ∧
      A.size = e.A0.size ∧ bits.toNat < 8 ∧ Origin.Inv e hold.toNat bits.toNat (e.i0 + used) u ∧
        e.InputFrame A e.i0 ∧
      ((mode = e.s0.mode ∧ Q u (cur e A o)) ∨
       (mode = TYPE ∧ ∃ u0, u0 ≤ u ∧ Q u0 (cur e A o) ∧
          Token.Step LL DD (hist e) (cur e A o) (src e u0) (src e u) (cur e A o) true) ∨
       (mode = BAD ∧ ∃ u0, u0 ≤ u ∧ Q u0 (cur e A o) ∧
          ∀ more, Token.Rejected LL DD (hist e) (cur e A o) ((src e u0).take (u - u0) ++ more))) := by
  have hw : Wp (inflate_fast e.strm e.start) e.h0 (fun _ after =>
      ∃ (A : Array UInt8) (msg : BPtr) (mode : UInt32) (hold : UInt64) (bits : UInt32)
        (used o u : Nat),
        after = finalHeap e A msg mode hold bits used o ∧
        used ≤ e.sm0.avail_in.toNat ∧ e.o0 ≤ o ∧ o ≤ e.o0 + e.sm0.avail_out.toNat ∧
        A.size = e.A0.size ∧ bits.toNat < 8 ∧ Origin.Inv e hold.toNat bits.toNat (e.i0 + used) u ∧
        e.InputFrame A e.i0 ∧
        ((mode = e.s0.mode ∧ Q u (cur e A o)) ∨
         (mode = TYPE ∧ ∃ u0, u0 ≤ u ∧ Q u0 (cur e A o) ∧
            Token.Step LL DD (hist e) (cur e A o) (src e u0) (src e u) (cur e A o) true) ∨
         (mode = BAD ∧ ∃ u0, u0 ≤ u ∧ Q u0 (cur e A o) ∧
            ∀ more, Token.Rejected LL DD (hist e) (cur e A o) ((src e u0).take (u - u0) ++ more)))) := by
    let c0 : Ctx := {
      strm := e.strm, state := some (.tab e.stid),
      last := .ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5),
      beg := .ref (BRef.blk e.ob) e.bg,
      end_ := .ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257),
      wsize := e.s0.wsize, whave := e.s0.whave, wnext := e.s0.wnext, window := e.s0.window,
      lcode := e.s0.lencode, dcode := e.s0.distcode,
      lmask := ((1 : UInt32) <<< e.s0.lenbits) - 1, dmask := ((1 : UInt32) <<< e.s0.distbits) - 1 }
    let l0 : L := {
      in_ := .ref (BRef.blk e.ib) e.i0, out := .ref (BRef.blk e.ob) e.o0,
      hold := e.s0.hold, bits := e.s0.bits, here := default, op := 0, len := 0, dist := 0,
      from_ := default, broke := false, againL := false, againD := false }
    have hc0 : CtxOK e c0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hl0 : LS e l0 e.i0 e.o0 := by
      dsimp only [l0]
      refine ⟨rfl, rfl, by omega, ?_, by omega, ?_, e.hhold, ?_⟩
      · have := e.hai; omega
      · change e.s0.bits.toNat ≤ 30
        have := e.hbits; omega
      · change e.s0.bits.toNat + 8 * e.i0 ≤ e.s0.bits.toNat + 8 * e.i0
        exact Nat.le_refl _
    have hlast : OkOn e.h0 (Ptr.add e.sm0.next_in (e.sm0.avail_in - 5).toNat)
        (.ref (BRef.blk e.ib) (e.i0 + e.sm0.avail_in.toNat - 5)) := by
      rw [e.hnin, u32_toNat_sub (by change 5 ≤ e.sm0.avail_in.toNat; have := e.hai; omega)]
      have hr := Ptr.add_nat_ok (h := e.h0) (r := BRef.blk e.ib) (a := e.IN)
        (off := e.i0) (n := e.sm0.avail_in.toNat - 5) e.hIN (by have := e.hINsz; omega)
      have hoff : e.i0 + (e.sm0.avail_in.toNat - 5) = e.i0 + e.sm0.avail_in.toNat - 5 := by have := e.hai; omega
      simpa [hoff] using hr
    have hbeg : OkOn e.h0 (subn e.sm0.next_out (e.start - e.sm0.avail_out))
        (.ref (BRef.blk e.ob) e.bg) := by
      rw [e.hnout]
      have hn : (e.start - e.sm0.avail_out).toNat = e.start.toNat - e.sm0.avail_out.toNat :=
        u32_toNat_sub e.hstart
      have hr := subn_ok (h := e.h0) (r := BRef.blk e.ob) (a := e.A0)
        (off := e.o0) (n := e.start - e.sm0.avail_out) e.hA0 (by rw [hn]; exact e.hbeg)
        (by have := e.hAsz; omega)
      simpa only [hn, EnvG.bg] using hr
    have hend : OkOn e.h0 (Ptr.add e.sm0.next_out (e.sm0.avail_out - 257).toNat)
        (.ref (BRef.blk e.ob) (e.o0 + e.sm0.avail_out.toNat - 257)) := by
      rw [e.hnout, u32_toNat_sub (by change 257 ≤ e.sm0.avail_out.toNat; have := e.hao; omega)]
      have hr := Ptr.add_nat_ok (h := e.h0) (r := BRef.blk e.ob) (a := e.A0)
        (off := e.o0) (n := e.sm0.avail_out.toNat - 257) e.hA0 (by have := e.hAsz; omega)
      have hoff : e.o0 + (e.sm0.avail_out.toNat - 257) = e.o0 + e.sm0.avail_out.toNat - 257 := by have := e.hao; omega
      simpa [hoff] using hr
    unfold inflate_fast
    refine Wp.bindO (x := e.sm0) (by rw [e.hstrm]; exact ldZStream_ok e.hsm) ?_
    refine Wp.bindO (x := some (InflateStateRef.tab e.stid)) (by rw [e.hstate]; exact castInflateState_ok) ?_
    refine Wp.bindO hlast ?_
    refine Wp.bindO hbeg ?_
    refine Wp.bindO hend ?_
    refine Wp.bindO (ldInflateState_tab e.hs0) ?_
    refine Wp.bindO (shl32_ok (x := 1) (n := e.s0.lenbits) (by have := e.hlt.1; omega)) ?_
    refine Wp.bindO (shl32_ok (x := 1) (n := e.s0.distbits) (by have := e.hdt.1; omega)) ?_
    rw [e.hnin, e.hnout]
    have origin0 : Origin.Inv e l0.hold.toNat l0.bits.toNat e.i0 0 := initial_origin e
    obtain ⟨l, h, hr, hpost⟩ := loop_tokens e c0 hc0 LL DD tables lenPrefix distPrefix Q step l0 e.i0 e.o0 e.A0 0
      hl0 rfl rfl (by have := e.hai; omega) (by have := e.hao; omega) origin0 (e.inputFrame_entry _) q0
    rw [e.heap_initial] at hr
    refine Wp.bindE hr ?_
    obtain ⟨i, o, A, msg, mode, u, hl, ho, hA, hh, origin, frameEnd, outcome⟩ := hpost
    rw [hh]
    refine Wp.mono (finish_tokens e A msg mode l i o hl hA ho u origin (frameEnd.mono hl.hi0)) ?_
    intro _ after ⟨hold, bits, used, heapEq, usedLe, bitsLt, origin', _⟩
    refine ⟨A, msg, mode, hold, bits, used, o, u, heapEq, usedLe, hl.ho0, ho, hA, bitsLt, origin',
      frameEnd, ?_⟩
    rcases outcome with ⟨_, modeEq, q⟩ | ⟨_, modeEq, rest⟩ | ⟨_, modeEq, rest⟩
    · exact Or.inl ⟨modeEq, q⟩
    · exact Or.inr (Or.inl ⟨modeEq, rest⟩)
    · exact Or.inr (Or.inr ⟨modeEq, rest⟩)
  obtain ⟨⟨⟩, after, hr, A, msg, mode, hold, bits, used, o, u, rfl, rest⟩ := hw
  exact ⟨A, msg, mode, hold, bits, used, o, u, hr, rest⟩

#print axioms fast_call_tokens

end Zlib.Inffast.Proofs.FastMeaning
