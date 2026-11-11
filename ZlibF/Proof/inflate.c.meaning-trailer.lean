import ZlibF.Proof.«inflate.c.meaning-loop»
import ZlibF.Proof.«inflate.c.meaning-format»
import ZlibF.Proof.«inflate.c.meaning-outcome»
import ZlibF.Proof.«inflate.c.meaning-fields»
import ZlibF.Proof.«inflate.c.meaning-lit»
import ZlibF.Proof.«inflate.c.main.check»
import ZlibF.Proof.«inflate.c.meaning-dictionary»

/-!
# inflate.c: the trailer and end modes keep the format meaning in the loop

Per-mode steps of the stream side (batch 2) against `LoopMatches`
(`inflate.c.meaning-loop`). `DONE` leaves with `Z_STREAM_END` and nothing
else changed.
-/

namespace Zlib.Inflate.Proofs.MeaningTrailer
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningBits Zlib.Inflate.Proofs.MeaningFields
set_option autoImplicit false

/-- `case DONE:` sets the return register and leaves; heap and every other
register are unchanged. -/
theorem inflate_DONE_run (c : Ctx) (l : IL) (h : Heap) :
    runX (inflate_DONE c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), h) := rfl

/-- Every position inside the deflate body is represented in a body mode,
`TYPE` to `LIT`. -/
theorem body_mode_range {h : Heap} {s : InflateState} {pos : DeflatePos}
    (body : BodyMatches h s pos) : TYPE ≤ s.mode ∧ s.mode ≤ LIT := by
  obtain ⟨out, final, blockStage⟩ := pos
  cases blockStage with
  | boundary =>
    obtain ⟨mode | mode, _⟩ := body <;> rw [mode] <;> decide
  | storedHeader =>
    obtain ⟨mode, _⟩ := body
    rw [mode]; decide
  | stored remaining =>
    obtain ⟨mode | mode, _⟩ := body <;> rw [mode] <;> decide
  | dynamicHeader header =>
    obtain ⟨dynamic, _⟩ := body
    rcases MeaningLit.dynamic_mode dynamic with mode | mode | mode <;> rw [mode] <;> decide
  | codes L D pending =>
    obtain ⟨_, _, _, modes⟩ := body
    cases pending with
    | none => rcases modes with mode | mode <;> rw [mode] <;> decide
    | lengthExtra _ => obtain ⟨mode, _⟩ := modes; rw [mode]; decide
    | distance _ => obtain ⟨mode, _⟩ := modes; rw [mode]; decide
    | distanceExtra _ _ => obtain ⟨mode, _⟩ := modes; rw [mode]; decide
    | copy _ _ => obtain ⟨mode, _⟩ := modes; rw [mode]; decide
    | literal _ => obtain ⟨mode, _⟩ := modes; rw [mode]; decide
  | finished =>
    obtain ⟨mode | mode, _⟩ := body <;> rw [mode] <;> decide

/-- No position inside the deflate body is represented in `DONE`. -/
theorem body_not_done {h : Heap} {s : InflateState} {pos : DeflatePos}
    (body : BodyMatches h s pos) (done : s.mode = DONE) : False := by
  have := body_mode_range body
  rw [done] at this
  exact absurd this (by decide)

/-- In the loop, only the end stage is represented in `DONE`. -/
theorem loop_stage_done {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (done : s.mode = DONE) :
    ∃ out, stage = .done out := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨_, hi⟩ := stageFacts
    rw [done] at hi
    exact absurd hi (by decide)
  · have mode : s.mode = DICT := stageFacts
    rw [done] at mode
    exact absurd mode (by decide)
  · exact (body_not_done stageFacts.1 done).elim
  · obtain ⟨mode | mode, _⟩ := stageFacts <;> rw [done] at mode <;> exact absurd mode (by decide)
  · exact ⟨out, rfl⟩

/-- `case DONE:` in the loop: it leaves with `Z_STREAM_END`, and the loop
meaning holds for the registers with the return value reset. -/
theorem done_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} (loop : LoopMatches c f h l) :
    runX (inflate_DONE c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), h) ∧
      LoopMatches c f h { { l with ret := Z_STREAM_END } with ret := Z_OK } := by
  refine ⟨inflate_DONE_run c l h, ?_⟩
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, rest⟩ := loop
  have same : ({ { l with ret := Z_STREAM_END } with ret := Z_OK } : IL) = l := by
    cases l
    simp only at retOk ⊢
    rw [retOk]
  rw [same]
  exact ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, rest⟩

#print axioms loop_stage_done
#print axioms done_step

/-! ## `LENGTH` -/

theorem writable_setI {h : Heap} {zs : Nat} {s : InflateState} {p : BPtr} {n : Nat}
    (w : Writable h p n) : Writable (setI h zs s) p n := by
  rcases w with null | ⟨r, i, a, ptr, get, ro, fits⟩
  · exact Or.inl null
  · exact Or.inr ⟨r, i, a, ptr, by rw [byte_view_get_setI]; exact get,
      by rw [byte_view_ro_setI]; exact ro, fits⟩

/-- The bits read before a trailer position end on a byte boundary. -/
theorem trailer_aligned {wrap : Api.Wrap} {configured : Nat} {dict header out bytes : List UInt8}
    {consumed : List Bool}
    (parsed : WrapParsed wrap configured dict consumed (.trailer header out bytes)) :
    consumed.length % 8 = 0 := by
  obtain ⟨_, bits, pad, _, _, _, padLength, _, _, rfl⟩ := parsed
  simp only [List.length_append, bytesToBits_length']
  omega

/-- Held bits after an aligned position are the bits of the next input bytes. -/
theorem held_bytes {input : List UInt8} {consumed held : List Bool}
    (bits : bytesToBits input = consumed ++ held) (aligned : consumed.length % 8 = 0) :
    held = bytesToBits (input.drop (consumed.length / 8)) := by
  have := congrArg (fun l => l.drop (8 * (consumed.length / 8))) bits
  simp only [bytesToBits_drop] at this
  rw [show 8 * (consumed.length / 8) = consumed.length by omega, List.drop_left] at this
  rw [← this, bytesBits_eq_bytesToBits]

/-- In the loop, a `LENGTH` state stands for a trailer position. -/
theorem stage_of_length {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageM : LoopStageMatches h s f checked stage) (mode : s.mode = LENGTH) :
    ∃ header out bytes, stage = .trailer header out bytes := by
  rcases stage with b | b | ⟨b, pos⟩ | ⟨header, out, bytes⟩ | out
  · have hi : s.mode ≤ DICTID := stageM.2
    rw [mode] at hi; exact absurd hi (by decide)
  · have m : s.mode = DICT := stageM; rw [mode] at m; exact absurd m (by decide)
  · have range := body_mode_range stageM.1
    rw [mode] at range
    exact absurd range (by decide)
  · exact ⟨header, out, bytes, rfl⟩
  · have m : s.mode = DONE := stageM; rw [mode] at m; exact absurd m (by decide)

/-- The method byte of a gzip header is 8. -/
theorem gzipHeader_method {header : List UInt8} (gzip : GzipHeader header) : header.getD 2 0 = 8 := by
  obtain ⟨flg, mt, xfl, os, ex, nm, cm, _, _, _, _, _, rfl⟩ := gzip
  simp [Gzip.header]

/-- The header of a stage whose header starts with the gzip magic is a gzip header. -/
theorem wrapHeader_gzip {wrap : Api.Wrap} {configured : Nat} {dict header bodyDict : List UInt8}
    (wh : WrapHeader wrap configured dict header bodyDict) (isGzip : IsGzipHeader header)
    (wrapped : wrap ≠ .raw) :
    GzipHeader header ∧ WrapTrailer wrap header = fun out =>
      le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32) := by
  cases wrap with
  | raw => exact absurd rfl wrapped
  | zlib =>
    obtain ⟨window, zlib, _⟩ := wh
    exact absurd isGzip (zlibHeader_not_gzip zlib)
  | gzip => exact ⟨wh.1, rfl⟩
  | auto =>
    rcases wh with ⟨window, zlib, _⟩ | ⟨gzip, _⟩
    · exact absurd isGzip (zlibHeader_not_gzip zlib)
    · refine ⟨gzip, ?_⟩
      funext out
      simp only [WrapTrailer]
      split
      · rfl
      · contradiction

/-- The low 32 bits of a 64-bit length. -/
theorem total_mask (n : Nat) : (UInt64.ofNat n &&& 0xffffffff).toNat = n % 2 ^ 32 := by
  rw [UInt64.toNat_and, show (0xffffffff : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_ofNat']
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- `case LENGTH:` of a gzip trailer in the loop: it leaves for more input,
ends the stream when the four bytes are the length of the output modulo
`2^32`, or enters `BAD` with the input doomed. -/
theorem length_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (length : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LENGTH) :
    ∃ result l' h', runX (inflate_LENGTH c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have loop0 := loop
  obtain ⟨zs, s, _, consumed, held, stage, st, hs, retOk, config, _, _, binv, _, _, _, _, _, _, _, _,
    bitsEq0, heldBits0, parsed0, stageM0, wrapM0, _⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = LENGTH := length zs s st hs
  have sameState : ∀ zs' s', c.st = some (.tab zs') → h.istates zs' = some s' → zs = zs' ∧ s = s' := by
    intro zs' s' st' hs'
    rw [st] at st'
    cases st'
    exact ⟨rfl, Option.some.inj (hs.symm.trans hs')⟩
  obtain ⟨header0, out0, bytes0, rfl⟩ := stage_of_length stageM0 mode
  obtain ⟨flagsM0, _, ⟨_, lengthFacts0, bitsBound0⟩⟩ := wrapM0
  obtain ⟨_, wrapped, isGzip0, _⟩ := lengthFacts0 mode
  have aligned0 := trailer_aligned parsed0
  have heldAligned : l.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length bitsEq0
    simp only [List.length_append, bytesToBits_length'] at lengths
    have := heldBits0.1
    simp only [loopState] at this
    omega
  have bitsBound : l.bits.toNat ≤ 32 := bitsBound0
  have wrapNZ : s.wrap ≠ 0 := fun zero => wrapped (wrapCode_zero (config.1.symm.trans zero))
  have flagsNZ : s.flags ≠ 0 := by
    obtain ⟨_, _, _, wh, _⟩ := parsed0
    have method := gzipHeader_method (wrapHeader_gzip wh isGzip0 wrapped).1
    intro zero
    unfold FlagsMatch at flagsM0
    simp only [wrapped, ite_false] at flagsM0
    have value : s.flags.toInt = gzipFlagsWord header0 := by
      split at flagsM0
      · exact flagsM0
      · contradiction
    rw [zero] at value
    have eq : (0 : Int) = ((header0.getD 2 0).toNat : Int) + 256 * ((header0.getD 3 0).toNat : Int) := by
      simpa [gzipFlagsWord] using value
    rw [method] at eq
    simp at eq
    omega
  have wrap4 : (s.wrap &&& 4) ≠ 0 := by
    have code : s.wrap = wrapCode f.wrap := config.1
    rw [code]
    revert wrapped
    generalize f.wrap = w
    intro wrapped
    cases w with
    | raw => exact absurd rfl wrapped
    | zlib => decide
    | gzip => decide
    | auto => decide
  -- NEEDBITS(32) keeps the loop meaning while at most 32 bits are held
  obtain ⟨result, l', j, needRun, shape, readEq, bitsCount, enough, leaveFacts, kinds, bitsMax,
    loopAt⟩ := LoopMatches.needbits loop0 (ok := (· ≤ 32))
      (fun zs' s' checked stage st' hs' stageM' => by
        obtain ⟨rfl, rfl⟩ := sameState zs' s' st' hs'
        obtain ⟨header, out, bytes, rfl⟩ := stage_of_length stageM' mode
        exact bitsFree_trailer f header out bytes) 32 (by decide)
  obtain ⟨rr, l'', j', run'', _, _, _, leaveRun, okRun⟩ :=
    inflate_LENGTH_run strm st hz hs wrapNZ flagsNZ binv
  rw [needRun] at run''
  simp only [Except.ok.injEq, Prod.mk.injEq] at run''
  obtain ⟨⟨rfl, rfl⟩, _⟩ := run''
  have shapeFields : l'.ret = l.ret ∧ l'.in_ = l.in_ ∧ l'.out_ = l.out_ ∧ l'.left = l.left ∧
      l'.put = l.put := by
    rw [shape]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rcases kinds with okResult | leaveResult
  · -- 32 bits held: the ISIZE field
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
    obtain ⟨header, out, bytes, rfl⟩ := stage_of_length stageM1 mode
    obtain ⟨flagsM1, widthM1, ⟨_, lengthFacts1, _⟩⟩ := wrapM1
    obtain ⟨fourBytes, _, isGzip, totalEq⟩ := lengthFacts1 mode
    have aligned1 := trailer_aligned parsed1
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
    have ⟨_, _, _, wh1, _⟩ := parsed1
    obtain ⟨_, trailerEq⟩ := wrapHeader_gzip wh1 isGzip wrapped
    have maskEq : (s.total &&& 0xffffffff).toNat = out.length % 2 ^ 32 := by
      have : (loopState s l').total = UInt64.ofNat out.length := totalEq
      simp only [loopState] at this
      rw [this, total_mask]
    obtain ⟨_, matchRun⟩ := okRun rfl
    have bitsField : bytesToBits (f.logIn ++ f.inp.take (loopRead l')) = consumed ++ bytesToBits field := by
      rw [bitsEq1, fieldEq]
    have ⟨_, _, _, _, _, _, _, bytesPrefix, _, _⟩ := parsed1
    have crcBytes : bytes = le32 (crc32 out).toNat := by
      rw [trailerEq] at bytesPrefix
      have short : bytes <+: le32 (crc32 out).toNat :=
        List.prefix_of_prefix_length_le bytesPrefix (List.prefix_append _ _)
          (by rw [fourBytes]; simp [le32])
      exact short.eq_of_length (by rw [fourBytes]; simp [le32])
    have fieldIff : bytes ++ field <+: WrapTrailer f.wrap header out ↔
        l'.hold = s.total &&& 0xffffffff := by
      rw [trailerEq, crcBytes]
      simp only [List.prefix_append_right_inj]
      constructor
      · intro pre
        have same : field = le32 (out.length % 2 ^ 32) :=
          pre.eq_of_length (by rw [fieldLength]; rfl)
        apply UInt64.toNat_inj.mp
        rw [holdValue, maskEq, same, leValue_le32, Nat.mod_mod]
      · intro agree
        have value : leValue field = out.length % 2 ^ 32 := by
          rw [← holdValue, agree, maskEq]
        match field, fieldLength with
        | [a, b, c', d], _ =>
          rw [le32_of_value (by rw [value, Nat.mod_mod])]
          exact List.prefix_refl _
    by_cases agree : l'.hold = s.total &&& 0xffffffff
    · -- the length agrees: the stream ends
      have notBad : ¬ ((s.wrap &&& 4) ≠ 0 ∧ l'.hold ≠ (s.total &&& 0xffffffff)) :=
        fun ⟨_, ne⟩ => ne agree
      refine ⟨_, _, _, matchRun.2 notBad, Or.inr ⟨rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩⟩
      have binvSet := MeaningLit.bitInv_setI (zs := zs) (s := { s with mode := DONE }) binv1
      have parsedDone := (wrapParsed_trailer_step parsed1 (more := field) (fieldIff.mpr agree)).2
        ((fieldIff.mpr agree).eq_of_length (by
          rw [trailerEq, crcBytes]; simp [fieldLength, le32]))
      refine ⟨zs, { s with mode := DONE }, callOut, consumed ++ bytesToBits field, [], .done out,
        st1, setI_istates_same _ _ _, rfl, ?_, haveLe1, inLen1,
        ⟨binvSet.have_eq, binvSet.next, by simp⟩, leftLe1, ⟨pend1.1, fun _ _ e => by cases e⟩,
        putEq1, MeaningLit.bytes_setI outBytes1, writable_setI writable1, sepIn1, sepWin1,
        sepOutIn1, by rw [List.append_nil]; exact bitsField, ⟨rfl, rfl⟩, parsedDone, rfl, rfl,
        outputEq1⟩
      obtain ⟨a, b, c', d, e, _⟩ := config1
      exact ⟨a, b, c', d, e, show DONE ≠ SYNC by decide⟩
    · -- the length disagrees: BAD, and no valid stream continues
      obtain ⟨i, _, badRun⟩ := matchRun.1 wrap4 agree
      refine ⟨_, _, _, badRun, Or.inl ⟨rfl, Or.inr ?_⟩⟩
      refine ⟨zs, { s with mode := BAD }, st1, setI_istates_same _ _ _, rfl,
        shapeFields.1.trans retOk, ?_, haveLe1, inLen1, ?_⟩
      · obtain ⟨a, b, c', d, e, _⟩ := config1
        exact ⟨a, b, c', d, e, show BAD ≠ SYNC by decide⟩
      · intro source decoded valid _ started
        exact trailer_reject parsed1 bitsField (fun pre => agree (fieldIff.mp pre)) valid started
  · -- the input ran out
    subst leaveResult
    obtain ⟨_, _, _, leaveRun'⟩ := leaveRun rfl
    exact ⟨_, _, _, leaveRun', Or.inr ⟨rfl, Or.inl (loopAt (by
      have below := (leaveFacts rfl).2
      have n32 : (32 : UInt32).toNat = 32 := rfl
      rw [n32] at below
      omega))⟩⟩

#print axioms length_step

end Zlib.Inflate.Proofs.MeaningTrailer
