import ZlibF.Spec.InflateFastCallOrigin
import ZlibF.Proof.«inffast.c.body-origin»
import ZlibF.Proof.«inffast.c.origin»
import ZlibF.Proof.«inffast.c.final»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Spec.CallOrigin

private theorem loop_origin_wp (hc : CtxOK e c) (l : L) (i o : Nat) (A : Array UInt8) (msg : BPtr) (mode : UInt32) (used : Nat)
    (hl : LS e l i o) (hA : A.size = e.A0.size) (hb : l.broke = false)
    (hi : i + 6 ≤ e.i0 + e.sm0.avail_in.toNat)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used) :
    Wp (cdoWhile (inflate_fast_body c)
      (fun l => do
        if l.broke then pure (false, l)
        else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
        else pure (false, l)) l) (e.heap A msg mode)
      (fun l' h' => ∃ i' o' A' msg' mode' used',
        LS e l' i' o' ∧ o' ≤ e.o0 + e.sm0.avail_out.toNat ∧ A'.size = e.A0.size ∧
        h' = e.heap A' msg' mode' ∧
        Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  let Inv : L → Heap → Prop := fun l h => ∃ i o A msg mode cursor,
    LS e l i o ∧ A.size = e.A0.size ∧ h = e.heap A msg mode ∧ l.broke = false ∧
    i + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o + 258 ≤ e.o0 + e.sm0.avail_out.toNat ∧
    Origin.Inv e l.hold.toNat l.bits.toNat i cursor ∧ used ≤ cursor
  let μ : L → Nat := fun l => match l.out with
    | .null => 0
    | .ref _ k => e.o0 + e.sm0.avail_out.toNat - k
  have hμ : ∀ l i o, LS e l i o → μ l = e.o0 + e.sm0.avail_out.toNat - o := by
    intro l i o hl
    simp only [μ, hl.hout]
  refine Wp.cdoWhile Inv μ _ ?_
    ⟨i, o, A, msg, mode, used, hl, hA, rfl, hb, hi, ho, origin, Nat.le_refl _⟩ ?_
  · intro l h hI
    obtain ⟨i, o, A, msg, mode, cursor, hl, hA, rfl, hb, hi, ho, origin, hused⟩ := hI
    have hp : StepPre e c A l i o := ⟨hc, hl, hA, hi, ho, hb⟩
    obtain ⟨l1, h1, hr, hpost, j, k, cursor', resultLocals, resultOrigin, hcursor⟩ :=
      actual_body_preserves_origin e c A msg mode l i o cursor hp origin
    obtain ⟨i', o', A', msg', mode', hl', hii, hi6, hoo, ho258, hsz, hh,
      _, _, hcont, _⟩ := hpost
    have sameInput : j = i' := by
      have eq := Ptr.ref.inj (resultLocals.hin.symm.trans hl'.hin)
      omega
    have sameOutput : k = o' := by
      have eq := Ptr.ref.inj (resultLocals.hout.symm.trans hl'.hout)
      omega
    subst j k
    have hAsz : A'.size = e.A0.size := hsz.trans hA
    have hoend : o' ≤ e.o0 + e.sm0.avail_out.toNat := by omega
    have hused' : used ≤ cursor' := Nat.le_trans hused hcursor
    refine ⟨l1, h1, hr, ?_⟩
    cases hstop : l1.broke with
    | true =>
      refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', mode', cursor', hl',
        hoend, hAsz, hh, resultOrigin, hused'⟩
      simp [hstop]
    | false =>
      obtain ⟨progress, _, _⟩ := hcont hstop
      have hcnd := fast_cond_live hc A' msg' mode' l1 i' o' hl' hAsz hoend hstop
      by_cases hroom : i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧
          o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat
      · refine Or.inr ⟨l1, h1, ?_, ?_, ?_⟩
        · rw [hh]; simpa [hstop, hroom.1, hroom.2] using hcnd
        · exact ⟨i', o', A', msg', mode', cursor', hl', hAsz, hh, hstop,
            hroom.1, hroom.2, resultOrigin, hused'⟩
        · rw [hμ _ _ _ hl', hμ _ _ _ hl]
          omega
      · refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', mode', cursor', hl',
          hoend, hAsz, hh, resultOrigin, hused'⟩
        have hcfalse : (decide (i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat) &&
            decide (o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        rw [hh]
        simpa [hstop, hcfalse] using hcnd
  · rw [hμ _ _ _ hl]
    apply lt_fuel_of
    have := UInt32.toNat_lt e.sm0.avail_out
    have := hl.ho0
    omega

private theorem finish_origin_wp (e : Env) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (usedBits : Nat) (origin : Origin.Inv e l.hold.toNat l.bits.toNat i usedBits) :
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
      (e.heap A msg mode) (fun _ after => HasOrigin e after) := by
  let buf := l.bits.toNat / 8
  let used := i - e.i0 - buf
  let produced := o - e.o0
  let bits := l.bits - ((l.bits >>> 3) <<< 3)
  let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  have hbuf : buf ≤ i - e.i0 := hl.buffered_le
  have hsmall : buf ≤ 3 := by dsimp only [buf]; have := hl.hb; omega
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
    have hr := subn_ok (h := e.heap A msg mode) (r := BRef.blk e.ib) (a := e.IN) (e.heap_bytes_in A msg mode)
      (n := l.bits >>> 3) (off := i) (by rw [bits_whole]; have := hl.hi0; omega)
      (by have := hl.hi1; have := e.hINsz; omega)
    simpa only [hio] using hr
  refine Wp.bindO hinbuf ?_
  refine Wp.bindO (shl32_ok (x := 1) (n := bits) (by omega)) ?_
  have hu32 : e.sm0.avail_in.toNat - used < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_in; omega
  have ho32 : e.sm0.avail_out.toNat - produced < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_out; omega
  have hei : e.i0 + e.sm0.avail_in.toNat - 5 + 5 - (e.i0 + used) = e.sm0.avail_in.toNat - used := by
    have := e.hai; omega
  refine ptr_avail_wp (h := e.heap A msg mode) (r := BRef.blk e.ib) (A := e.IN)
    (p := e.i0 + used) (q := e.i0 + e.sm0.avail_in.toNat - 5) (k := 5)
    (e.heap_bytes_in A msg mode) (by have := e.hINsz; omega) (by have := e.hINsz; omega)
    e.hINbig (by have := e.hai; omega) (by decide) (by rw [hei]; exact hu32) ?_
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
  have rollback := actual_rollback_preserves_origin e A msg mode l i o usedBits hl origin
  have newOrigin : Origin.Inv e hold.toNat bits.toNat (e.i0 + used) usedBits := by
    have sameIndex : i - l.bits.toNat / 8 = e.i0 + used := by simpa only [bits_whole] using hio
    simpa only [sameIndex] using rollback.2.2.1
  let stream : ZStream := { e.sm0 with
    next_in := .ref (.blk e.ib) (e.i0 + used)
    next_out := .ref (.blk e.ob) o
    avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used)
    avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - produced)
    msg := msg }
  refine ⟨{ e.s0 with mode, hold, bits }, stream,
    e.i0 + used, usedBits, ?_, ?_, rfl, ?_, newOrigin⟩
  · rw [put_istates]
    exact upd_same _ _ _
  · exact put_get e.r _ e.sm0 _ (e.stream_get_frame _ _)
  · change (e.i0 + used) + (UInt32.ofNat (e.sm0.avail_in.toNat - used)).toNat = _
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hu32]
    omega

theorem actual_fast_preserves_origin : CallOrigin.Goal.actual_fast_preserves_origin := by
  intro e
  have hw : Wp (inflate_fast e.strm e.start) e.h0 (fun _ after => HasOrigin e after) := by
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
      simpa only [hn, Env.bg] using hr
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
    obtain ⟨l, h, hr, hpost⟩ := loop_origin_wp hc0 l0 e.i0 e.o0 e.A0 e.sm0.msg e.s0.mode 0
      hl0 rfl rfl (by have := e.hai; omega) (by have := e.hao; omega) origin0
    rw [e.heap_initial] at hr
    refine Wp.bindE hr ?_
    obtain ⟨i, o, A, msg, mode, usedBits, hl, ho, hA, hh, origin, _⟩ := hpost
    rw [hh]
    exact finish_origin_wp e A msg mode l i o hl hA ho usedBits origin
  obtain ⟨⟨⟩, after, hr, hp⟩ := hw
  obtain ⟨safeAfter, safeRun, safePost⟩ := inflate_fast_safe e
  have same : safeAfter = after := by
    have eq := safeRun.symm.trans hr
    cases eq
    rfl
  subst safeAfter
  exact ⟨after, hr, safePost, hp⟩

end Zlib.Inffast.Proofs
