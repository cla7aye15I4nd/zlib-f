import ZlibF.Proof.«inflate.c.meaning-check»
import ZlibF.Proof.«inflate.c.dictionary-dispatch»

/-!
# inflate.c: `DICTID` keeps the format meaning in the loop

Batch 2, `dictid_step`. In `DICTID` the decoder has read the two bytes of a
zlib header with `FDICT` set. `case DICTID:` either leaves for more input, or
reads the four identifier bytes, stores them as `check` (and `adler`), and
falls through to `DICT`. A wrapped header has no dictionary yet
(`HeaderMatches`), so `DICT` then returns `Z_NEED_DICT` directly, without
`inf_leave` (`NeedDictExit`): the parse stands at the dictionary request.
-/

namespace Zlib.Inflate.Proofs.MeaningDictid
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningBits Zlib.Inflate.Proofs.MeaningFields Zlib.Inflate.Proofs.MeaningTrailer
open Zlib.Inflate.Proofs.MeaningCheck
set_option autoImplicit false

/-- `DICT` without a dictionary: `RESTORE()`, the input count, and
`return Z_NEED_DICT`, from a loop state `mid` whose parse stands at the
dictionary request. The meaning after the call follows from `LoopMatches`
at `mid` (the call assembly). -/
def NeedDictExit (c : Ctx) (f : LoopFrame) (result : Except Ex Unit) (h : Heap) (l : IL) : Prop :=
  result = .error (.ret Z_NEED_DICT) ∧
  ∃ (r : ZStreamRef) (z : ZStream) (zs : Nat) (s : InflateState) (mid : Heap),
    c.strm = some r ∧ r.get mid = some z ∧ mid.istates zs = some s ∧ s.mode = DICT ∧
    s.havedict = 0 ∧ LoopMatches c f mid l ∧
    h = setI (r.put mid (dictWaitStream z l)) zs (leaveState s l)

/-- In the loop, a header mode stands for a header position. -/
theorem stage_of_header {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageM : LoopStageMatches h s f checked stage) (high : s.mode ≤ DICTID) :
    ∃ bytes, stage = .header bytes := by
  rcases stage with b | b | ⟨b, pos⟩ | ⟨header, out, bytes⟩ | out
  · exact ⟨b, rfl⟩
  · have m : s.mode = DICT := stageM
    rw [m] at high
    exact absurd high (by decide)
  · have range := body_mode_range stageM.1
    exact absurd (UInt32.le_trans range.1 high) (by decide)
  · rcases stageM.1 with m | m <;> rw [m] at high <;> exact absurd high (by decide)
  · have m : s.mode = DONE := stageM
    rw [m] at high
    exact absurd high (by decide)

/-- In `DICTID` the header stage holds any bit buffer of at most 32 bits. -/
theorem dictid_bits {h : Heap} {s : InflateState} {f : LoopFrame} {checked bytes : List UInt8}
    (stageM : LoopStageMatches h s f checked (.header bytes))
    (wrapM : WrapMatches h s f.wrap f.configured f.dict (.header bytes))
    (mode : s.mode = DICTID) (hold : UInt64) (bits : UInt32) (small : bits.toNat ≤ 32) :
    LoopStageMatches h { s with hold := hold, bits := bits } f checked (.header bytes) ∧
      WrapMatches h { s with hold := hold, bits := bits } f.wrap f.configured f.dict (.header bytes) := by
  obtain ⟨⟨rawHead, _, dictidC, _, _, wrappedC, lastTotal⟩, windowM, used⟩ := wrapM
  obtain ⟨a, b, c', _, e, g⟩ := dictidC mode
  refine ⟨stageM, ⟨rawHead, fun m => absurd (mode.symm.trans m) (by decide),
    fun _ => ⟨a, b, c', small, e, g⟩, fun m => absurd (mode.symm.trans m) (by decide), fun _ hi => ?_,
    wrappedC, lastTotal⟩, windowM, used⟩
  have hi' : s.mode ≤ HCRC := hi
  rw [mode] at hi'
  exact absurd hi' (by decide)

/-- The first two bytes of a wrapped header that is not gzip are a zlib
header's `CMF` and `FLG`. -/
theorem zlib_prefix {wrap : Api.Wrap} {configured : Nat} {dict bytes more bodyDict : List UInt8}
    (wh : WrapHeader wrap configured dict (bytes ++ more) bodyDict) (wrapped : wrap ≠ .raw)
    (two : bytes.length = 2) (notGzip : ¬ IsGzipHeader bytes) :
    (wrap = .zlib ∨ wrap = .auto) ∧ ∃ cmf flg, bytes = [cmf, flg] ∧ Zlib.HeaderOK cmf flg ∧
      Api.ZlibFits configured [cmf, flg] := by
  have takeTwo : (bytes ++ more).take 2 = bytes := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have ofZlib : ∀ window, ZlibHeader configured dict (bytes ++ more) window →
      ∃ cmf flg, bytes = [cmf, flg] ∧ Zlib.HeaderOK cmf flg ∧ Api.ZlibFits configured [cmf, flg] := by
    intro window zh
    obtain ⟨cmf, flg, ok, fits, _, shape⟩ := zh
    refine ⟨cmf, flg, ?_, ok, fits⟩
    rw [← takeTwo]
    rcases shape with ⟨_, eq⟩ | ⟨_, eq⟩ <;> rw [eq] <;> simp
  have notGz : ¬ GzipHeader (bytes ++ more) := by
    intro gh
    apply notGzip
    have magic := gzipHeader_is_gzip gh
    unfold IsGzipHeader at magic ⊢
    rw [takeTwo] at magic
    rw [List.take_of_length_le (by omega)]
    exact magic
  cases wrap with
  | raw => exact absurd rfl wrapped
  | zlib =>
    obtain ⟨window, zh, _⟩ := wh
    exact ⟨Or.inl rfl, ofZlib window zh⟩
  | gzip => exact absurd wh.1 notGz
  | auto =>
    rcases wh with ⟨window, zh, _⟩ | ⟨gh, _⟩
    · exact ⟨Or.inr rfl, ofZlib window zh⟩
    · exact absurd gh notGz

/-- `ZSWAP32` of the held identifier word is the `DICTID` field of the header. -/
theorem dictId_swap {hold : UInt64} {cmf flg a b c d : UInt8}
    (value : hold.toNat = leValue [a, b, c, d]) : ZSWAP32 hold = dictId ([cmf, flg] ++ [a, b, c, d]) := by
  apply UInt64.toNat_inj.mp
  simp only [leValue] at value
  rw [zswap_value value]
  show a.toNat * 2 ^ 24 + b.toNat * 2 ^ 16 + c.toNat * 2 ^ 8 + d.toNat =
    (UInt64.ofNat (a.toNat * 2 ^ 24 + b.toNat * 2 ^ 16 + c.toNat * 2 ^ 8 + d.toNat)).toNat
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- A write of the stream record and the state record keeps every byte view. -/
theorem sameViews_put (h : Heap) (r : ZStreamRef) (z : ZStream) (zs : Nat) (s : InflateState) :
    SameViews h (setI (r.put h z) zs s) := by
  intro ref
  rw [byte_view_get_setI, byte_view_get_stream_put, byte_view_ro_setI, byte_view_ro_stream_put]
  exact ⟨rfl, rfl⟩

/-- `case DICTID:` in the loop: it leaves for more input, or it stores the
identifier and asks for the dictionary (`NeedDictExit`). -/
theorem dictid_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (dictid : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = DICTID) :
    ∃ result l' h', runX (inflate_DICTID c) l h = .ok ((result, l'), h') ∧
      (TripOutcome c f result h' l' ∨ NeedDictExit c f result h' l') := by
  have loop0 := loop
  obtain ⟨zs, s, _, consumed0, _, stage0, st, hs, _, _, _, _, _, _, _, _, _, _, _, _, _, bitsEq0,
    heldBits0, parsed0, stageM0, wrapM0, _⟩ := loop
  have mode : s.mode = DICTID := dictid zs s st hs
  have high : (loopState s l).mode ≤ DICTID := by
    show s.mode ≤ DICTID
    rw [mode]
    decide
  have sameState : ∀ zs' s', c.st = some (.tab zs') → h.istates zs' = some s' → zs = zs' ∧ s = s' := by
    intro zs' s' st' hs'
    rw [st] at st'
    cases st'
    exact ⟨rfl, Option.some.inj (hs.symm.trans hs')⟩
  obtain ⟨bytes0, rfl⟩ := stage_of_header stageM0 high
  have bitsBound : l.bits.toNat ≤ 32 := (wrapM0.1.2.2.1 mode).2.2.2.1
  have heldAligned : l.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length bitsEq0
    rw [parsed0.1] at lengths
    simp only [List.length_append, bytesToBits_length'] at lengths
    have := heldBits0.1
    simp only [loopState] at this
    omega
  obtain ⟨result, l', j, needRun, shape, _, bitsCount, enough, leaveFacts, kinds, bitsMax, loopAt⟩ :=
    LoopMatches.needbits_at loop0 (ok := (· ≤ 32))
      (fun zs' s' checked stage st' hs' stageM' wrapM' hold bits okb => by
        obtain ⟨rfl, rfl⟩ := sameState zs' s' st' hs'
        obtain ⟨bytes, rfl⟩ := stage_of_header stageM' high
        exact dictid_bits stageM' wrapM' mode hold bits okb) 32 (by decide)
  rcases kinds with okResult | leaveResult
  · -- 32 bits held: the identifier
    subst okResult
    have bits32 : l'.bits.toNat = 32 := by
      have atLeast := enough rfl
      have n32 : (32 : UInt32).toNat = 32 := rfl
      rw [n32] at atLeast bitsMax
      omega
    have loop' := loopAt (by omega)
    obtain ⟨zs1, s1, callOut, consumed, held, stage, st1, hs1, retOk1, config1, haveLe1, inLen1,
      binv1, leftLe1, pend1, putEq1, outBytes1, writable1, sepIn1, sepWin1, sepOutIn1, bitsEq1,
      heldBits1, parsed1, stageM1, wrapM1, outputEq1⟩ := loop'
    obtain ⟨rfl, rfl⟩ := sameState zs1 s1 st1 hs1
    obtain ⟨bytes, rfl⟩ := stage_of_header stageM1 high
    obtain ⟨⟨rawHead1, _, dictidC1, _, _, wrappedC1, _⟩, _, _⟩ := wrapM1
    obtain ⟨two, notGzip, flags0, _, width1, fdict⟩ := dictidC1 mode
    have wrapped : f.wrap ≠ .raw := by
      intro raw
      have head : s.mode = HEAD := rawHead1 raw
      rw [mode] at head
      exact absurd head (by decide)
    obtain ⟨havedict0, wsize0, whave0⟩ := wrappedC1 wrapped
    obtain ⟨consumedEq, more, bodyDict, wh, _⟩ := parsed1
    obtain ⟨zlibLike, cmf, flg, rfl, ok, fits⟩ := zlib_prefix wh wrapped two notGzip
    have aligned1 : consumed.length % 8 = 0 := by
      rw [consumedEq, bytesToBits_length']
      omega
    have fieldEq := held_bytes bitsEq1 aligned1
    obtain ⟨field, fieldDef⟩ : ∃ x, x = (f.logIn ++ f.inp.take (loopRead l')).drop (consumed.length / 8) :=
      ⟨_, rfl⟩
    rw [← fieldDef] at fieldEq
    have heldLength : held.length = 32 := by
      have := heldBits1.1
      simp only [loopState] at this
      omega
    have fieldLength : field.length = 4 := by
      have := congrArg List.length fieldEq
      rw [heldLength, bytesToBits_length'] at this
      omega
    have holdValue : l'.hold.toNat = leValue field := by
      have := heldBits1.2
      simp only [loopState] at this
      rw [this]
      change heldValue held = _
      rw [fieldEq, heldValue_bytesToBits]
    obtain ⟨a, b, c', d, rfl⟩ : ∃ a b c' d, field = [a, b, c', d] := by
      match field, fieldLength with
      | [a, b, c', d], _ => exact ⟨a, b, c', d, rfl⟩
    have bitsField : bytesToBits (f.logIn ++ f.inp.take (loopRead l')) =
        bytesToBits ([cmf, flg] ++ [a, b, c', d]) := by
      rw [bitsEq1, fieldEq, consumedEq, bytesToBits_append']
    -- the request state
    have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
    have cut := inflate_DICTID_parsed_cut E l l' needRun
    have hz2 : r.get (setI (r.put h { z with adler := ZSWAP32 l'.hold }) zs
        { s with check := ZSWAP32 l'.hold, mode := DICT }) = some { z with adler := ZSWAP32 l'.hold } := by
      rw [ZStreamRef.get_setI]
      exact ZStreamRef.get_put_same hz _
    have E2 : Env c (setI (r.put h { z with adler := ZSWAP32 l'.hold }) zs
        { s with check := ZSWAP32 l'.hold, mode := DICT }) r zs { z with adler := ZSWAP32 l'.hold }
        { s with check := ZSWAP32 l'.hold, mode := DICT } := ⟨strm, st, hz2, setI_istates_same _ _ _⟩
    have wait := inflate_DICT_wait_run E2 { l' with hold := 0, bits := 0 } havedict0
    have views := sameViews_put h r { z with adler := ZSWAP32 l'.hold } zs
      { s with check := ZSWAP32 l'.hold, mode := DICT }
    have binv2 := binv1.byte_views (fun ref => (views ref).1)
    obtain ⟨c1, c2, c3, c4, c5, _⟩ := config1
    obtain ⟨w1, w2, w3⟩ := width1
    have loopMid : LoopMatches c f (setI (r.put h { z with adler := ZSWAP32 l'.hold }) zs
        { s with check := ZSWAP32 l'.hold, mode := DICT }) { l' with hold := 0, bits := 0 } := by
      refine ⟨zs, { s with check := ZSWAP32 l'.hold, mode := DICT }, callOut,
        bytesToBits ([cmf, flg] ++ [a, b, c', d]), [], .needDict ([cmf, flg] ++ [a, b, c', d]), st,
        setI_istates_same _ _ _, retOk1, ⟨c1, c2, c3, c4, c5, show DICT ≠ SYNC by decide⟩, haveLe1, inLen1,
        ⟨binv2.have_eq, binv2.next, by simp⟩, leftLe1, ⟨pend1.1, fun _ _ e => by cases e⟩, putEq1,
        views.bytes outBytes1, views.writable writable1, sepIn1, sepWin1, sepOutIn1,
        by rw [List.append_nil]; exact bitsField, ⟨rfl, rfl⟩,
        wrapParsed_needDict zlibLike ok fits fdict rfl, rfl, ?_, outputEq1⟩
      exact ⟨dictId_swap holdValue, flags0, rfl, ⟨w1, w2, fun zero => ⟨fun g => (w3 zero).1 g,
        fun ng => (w3 zero).2 ng⟩⟩, fun _ => ⟨wsize0, whave0⟩, fun ne => absurd havedict0 ne⟩
    exact ⟨_, _, _, cut.trans wait, Or.inr ⟨rfl, r, _, zs, _, _, strm, hz2, setI_istates_same _ _ _, rfl,
      havedict0, loopMid, rfl⟩⟩
  · -- the input ran out
    subst leaveResult
    refine ⟨_, _, _, inflate_DICTID_wait needRun, Or.inl (Or.inr ⟨rfl, Or.inl (loopAt ?_)⟩)⟩
    have below := (leaveFacts rfl).2
    have n32 : (32 : UInt32).toNat = 32 := rfl
    rw [n32] at below
    omega

#print axioms dictid_step

end Zlib.Inflate.Proofs.MeaningDictid
