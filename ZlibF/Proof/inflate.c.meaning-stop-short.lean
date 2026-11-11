import ZlibF.Proof.«inflate.c.meaning-held-within»

/-!
# inflate.c: a starved stop is short of the end of a valid stream

The per-call parts of `StopShort` and `FailWithin` (`inflate.c.completes-interface`)
that do not need the composition of the mode steps into a whole call.

* `LoopMatches.starved_not_end`: a trip of the mode loop that leaves for want
  of input, short of the field its mode waits for (`LeaveShort`), has not
  read a whole valid stream. If it had, the held bits would be the rest of
  the stream, and the stream's parse from the stage on reads the field the
  mode waits for inside them: the block header after a boundary, the stored
  length, the dynamic header counts, code-length code lengths and items, a
  valid literal/length or distance symbol, extra bits, the trailer. A wrapper
  header is shorter than any valid stream.
* `LoopRefuted.not_comparable`: a rejection leaves the input read comparable
  with no valid stream that the offered input is comparable with, so a call
  that ends in `BAD` cannot have such a stream (the `BAD` case of
  `FailWithin`). The `MEM` case is `LoopMatches.within`
  (`inflate.c.meaning-held-within`) at the leave.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open HeldWithinBounds
set_option autoImplicit false

/-- A deflate position whose held bits are the whole rest of the deflate data
of a valid stream (and the trailer after it), with a state short of the field
its mode waits for, is impossible. -/
theorem body_starved {h : Heap} {s : InflateState} {dict : List UInt8} {dbits held T : List Bool}
    {pos : DeflatePos} {outF : List UInt8}
    (parsed : DeflateParsed dict dbits pos) (bm : BodyMatches h s pos) (sh : ShortAt h s held)
    (heldBits : HeldBits s held) (aligned : (dbits ++ held).length % 8 = 0)
    (blocks : Blocks dict [] (dbits ++ held) T outF) : False := by
  have len : held.length = s.bits.toNat := heldBits.1
  have resid := deflateParsed_resid parsed held T outF aligned blocks
  have prevResid : ∀ {c : List Bool} {p : DeflatePos} (pbits : List Bool),
      DeflateParsed dict c p → dbits = c ++ pbits → Resid dict p (pbits ++ held) T outF := by
    intro c p pbits prev e
    subst e
    exact deflateParsed_resid prev (pbits ++ held) T outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
  have boundaryCase : ∀ {out : List UInt8} {final : Bool},
      Resid dict ⟨out, final, .boundary⟩ held T outF → (s.mode = TYPE ∨ s.mode = TYPEDO) → False := by
    intro out final r m
    have := blocks_length (show Blocks dict out held T outF from r)
    have := (sh.of_type m).2
    omega
  have finishedCase : (s.mode = TYPE ∨ s.mode = TYPEDO) → s.last = 1 → False := by
    intro m last
    have := (sh.of_type m).1
    rw [last] at this
    exact absurd this (by decide)
  have storedHeaderCase : ∀ {out : List UInt8} {final : Bool},
      Resid dict ⟨out, final, .storedHeader⟩ held T outF → s.mode = STORED → False := by
    intro out final r m
    obtain ⟨r', h', body, cont⟩ := r
    have := body_stored_length body
    have := sh.of_stored m
    omega
  have storedCase : ∀ {out : List UInt8} {final : Bool} {remaining : Nat},
      Resid dict ⟨out, final, .stored remaining⟩ held T outF → (s.mode = COPY_ ∨ s.mode = COPY) →
      s.length.toNat = remaining → s.bits = 0 → False := by
    intro out final remaining r m lengthEq zero
    obtain ⟨bs, r', rd, cont⟩ := r
    have := readBytes_length _ _ _ _ rd
    have z : s.bits.toNat = 0 := by rw [zero]; rfl
    have nz := sh.of_copy m
    have : remaining ≠ 0 := by
      intro e
      apply nz
      apply UInt32.toNat_inj.mp
      rw [lengthEq, e]
      rfl
    omega
  have noneCase : ∀ {out : List UInt8} {final : Bool} {L D : List Nat},
      Resid dict ⟨out, final, .codes L D .none⟩ held T outF → (s.mode = LEN_ ∨ s.mode = LEN) →
      TableMeaning h s.lencode s.lenbits LENS L → False := by
    intro out final L D r m lenT
    obtain ⟨_, _, r', h', sy, _⟩ := r
    obtain ⟨sym, r1, d, le, _⟩ := symbols_first sy
    have := sh.of_len m L lenT sym r1 d
    omega
  have dynamicCase : ∀ {out : List UInt8} {final : Bool} {header : List Bool},
      Resid dict ⟨out, final, .dynamicHeader header⟩ held T outF → DynamicMatches h s header → False := by
    intro out final header r dm
    obtain ⟨r', h', body, _⟩ := r
    cases body with
    | dynamic f1 f2 f3 _ f4 acc cls _ _ _ _ =>
      have l1 := readBits_length _ _ _ _ f1
      have l2 := readBits_length _ _ _ _ f2
      have l3 := readBits_length _ _ _ _ f3
      have l4 := readCodeLenLens_length _ _ _ _ f4
      rw [List.length_append] at l1
      rcases dm with ⟨m, rfl, _⟩ |
        ⟨hlit, hdist, hclen, r1, r2, r3, g1, g2, g3, _, _, _, _, stage⟩
      · have := sh.of_table m
        simp only [List.length_nil] at l1
        omega
      · have e1 := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held g1
        rw [f1] at e1
        simp only [Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        have e2 := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held g2
        rw [f2] at e2
        simp only [Option.some.injEq, Prod.mk.injEq] at e2
        obtain ⟨rfl, rfl⟩ := e2
        have e3 := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held g3
        rw [f3] at e3
        simp only [Option.some.injEq, Prod.mk.injEq] at e3
        obtain ⟨rfl, rfl⟩ := e3
        rw [List.length_append] at l4
        rcases stage with ⟨m, haveLt, _, vs, rn, _⟩ |
          ⟨m, cl, r4, ref, offset, codes, rcl, ptr, get, meaning, haveLt, _, future, _, _⟩
        · have rl := readNats_length 3 _ _ _ _ rn
          have := sh.of_lenlens m
          simp only [List.length_nil] at rl
          omega
        · have e4 := ZlibF.Spec.Proofs.readCodeLenLens_append _ _ _ _ held rcl
          rw [e4] at f4
          simp only [Option.some.injEq, Prod.mk.injEq] at f4
          obtain ⟨rfl, rfl⟩ := f4
          have c2 := future held _ _ cls
          have prefixLen : (lensPrefix s).length = s.«have».toNat := by simp [lensPrefix]
          obtain ⟨sym, a1, x, a2, dsym, rb, _⟩ :=
            codeLens_item c2 (by rw [prefixLen]; exact haveLt)
          exact sh.of_codelens m ref offset codes cl ptr get meaning ⟨sym, a1, x, a2, dsym, rb⟩
  cases parsed with
  | start => exact boundaryCase resid bm.1
  | storedStart => exact storedHeaderCase resid bm.1
  | storedPad => exact storedHeaderCase resid bm.1
  | storedLength => exact storedCase resid bm.1 bm.2.1 bm.2.2.2
  | storedByte => exact storedCase resid bm.1 bm.2.1 bm.2.2.2
  | storedEnd => exact boundaryCase resid bm.1
  | storedFinal => exact finishedCase bm.1 bm.2.2.1
  | fixedHeader => exact noneCase resid bm.2.2.2.1 bm.2.1
  | dynamicStart => exact dynamicCase resid bm.1
  | dynamicBits => exact dynamicCase resid bm.1
  | dynamicDone => exact noneCase resid bm.2.2.2.1 bm.2.1
  | token => exact noneCase resid bm.2.2.2.1 bm.2.1
  | endOfBlock => exact boundaryCase resid bm.1
  | endOfFinal => exact finishedCase bm.1 bm.2.2.1
  | @partialToken consumed out final L D pending pbits prev pp =>
    have r0 := prevResid pbits prev rfl
    cases pending with
    | none =>
      have e : pbits = [] := pp
      subst e
      rw [List.nil_append] at r0
      exact noneCase r0 bm.2.2.2.1 bm.2.1
    | lengthExtra symbol =>
      obtain ⟨lo, _, dp⟩ := pp
      obtain ⟨_, _, _, mode, extraEq, _, _⟩ := bm
      obtain ⟨extL, _, r, h', sy, _⟩ := r0
      have dfull := extL _ _ _ held dp
      rw [List.nil_append] at dfull
      obtain ⟨xl, r2, dsym, r3, xd, r4, rb1, _, _, _, _⟩ := symbols_copy_of sy dfull lo
      have := readBits_length _ _ _ _ rb1
      have := sh.of_lenext mode
      omega
    | distance length =>
      obtain ⟨symbol, extra, r1, dp, lo, _, rbp, _⟩ := pp
      obtain ⟨_, _, distT, mode, _, _⟩ := bm
      obtain ⟨extL, _, r, h', sy, _⟩ := r0
      have dfull := extL _ _ _ held dp
      have rbfull := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held rbp
      rw [List.nil_append] at rbfull
      obtain ⟨xl, r2, dsym, r3, xd, r4, rb1, d2, ds, _, _⟩ := symbols_copy_of sy dfull lo
      rw [rbfull] at rb1
      simp only [Option.some.injEq, Prod.mk.injEq] at rb1
      obtain ⟨_, rfl⟩ := rb1
      have := sh.of_dist mode _ distT dsym r3 d2
      omega
    | distanceExtra length dsymbol =>
      obtain ⟨symbol, extra, r1, r2', dp, lo, _, rbp, _, dDp, _⟩ := pp
      obtain ⟨_, _, _, mode, _, extraEq, _, _⟩ := bm
      obtain ⟨extL, extD, r, h', sy, _⟩ := r0
      have dfull := extL _ _ _ held dp
      have rbfull := ZlibF.Spec.Proofs.readBits_append _ _ _ _ held rbp
      have dDfull := extD _ _ _ held dDp
      rw [List.nil_append] at dDfull
      obtain ⟨xl, r2, dsym, r3, xd, r4, rb1, d2, _, rb2, _⟩ := symbols_copy_of sy dfull lo
      rw [rbfull] at rb1
      simp only [Option.some.injEq, Prod.mk.injEq] at rb1
      obtain ⟨_, rfl⟩ := rb1
      rw [dDfull] at d2
      simp only [Option.some.injEq, Prod.mk.injEq] at d2
      obtain ⟨rfl, rfl⟩ := d2
      have := readBits_length _ _ _ _ rb2
      have := sh.of_distext mode
      omega
    | copy remaining dist => exact sh.not_match bm.2.2.2.1
    | literal byte => exact (pp : False).elim
  | partialCopy => exact sh.not_match bm.2.2.2.1
  | partialLiteral => exact sh.not_lit bm.2.2.2.1

#print axioms body_starved

/-- A trip of the mode loop that is short of the field its mode waits for has
not read a whole valid stream. -/
theorem LoopMatches.starved_not_end {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    (loop : LoopMatches c f h l) (short : LeaveShort c h l) {S decoded : List UInt8}
    (valid : Api.Layer.Decodes f.wrap f.configured f.dict S decoded)
    (whole : f.logIn ++ f.inp.take (loopRead l) = S) : False := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := MeaningBits.HeldBits.eq_natBits heldBits
  have sh : ShortAt h (loopState s l) held := by rw [heldEq]; exact short zs s st hs
  rw [whole] at bitsEq
  have len : held.length = (loopState s l).bits.toNat := heldBits.1
  have lengths := congrArg List.length bitsEq
  simp only [List.length_append, bytesToBits_length'] at lengths
  cases stage with
  | header bytes =>
    obtain ⟨rfl, more, bd, wh, _⟩ := parsed
    have range : HEAD ≤ (loopState s l).mode ∧ (loopState s l).mode ≤ DICTID := stageM
    obtain ⟨hm, _, _⟩ := wrapM
    obtain ⟨rawHead, headC, dictidC, flagsC, gzC, _⟩ := hm
    have lens := stream_length valid
    rw [bytesToBits_length'] at lengths
    have pre : bytes <+: S := bytesToBits_prefix_iff.mp ⟨held, bitsEq.symm⟩
    have preLen := pre.length_le
    have notRawOf : (loopState s l).mode ≠ HEAD → f.wrap ≠ .raw := fun ne r => ne (rawHead r)
    have gz : (loopState s l).mode ≠ HEAD → IsGzipHeader bytes → 20 ≤ S.length := fun ne g =>
      gzip_decodes_length (lens.2.2 (notRawOf ne) (head31 pre g))
    rcases header_mode_cases range with m | m | m | m | m | m | m | m | m | m
    · obtain ⟨be, _, _⟩ := headC m
      have bl : bytes.length = 0 := by rw [be]; rfl
      obtain ⟨wrapNz, small⟩ := sh.of_head m
      have notRaw : f.wrap ≠ .raw := by
        intro r
        apply wrapNz
        rw [config.1, r]
        rfl
      have := lens.2.1 notRaw
      omega
    · obtain ⟨be, _, _⟩ := flagsC m
      have bl : bytes.length = 2 := by rw [be]; rfl
      have := lens.2.1 (notRawOf (by rw [m]; decide))
      have := sh.of_flags m
      omega
    · obtain ⟨_, _, _, _, _, timeC, _⟩ := gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨be, _⟩ := timeC m
      have bl : bytes.length = 4 := by rw [be]; rfl
      have := lens.2.1 (notRawOf (by rw [m]; decide))
      have := sh.of_time m
      omega
    · obtain ⟨isG, _, _, _, _, _, osC, _⟩ := gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨_, four, fl, be⟩ := osC m
      have bl : bytes.length = 8 := by rw [be, List.length_append, fl]; rfl
      have := gz (by rw [m]; decide) isG
      have := sh.of_os m
      omega
    · obtain ⟨isG, _, _, _, _, _, _, exlenC, _⟩ := gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨_, _, six, sl, be⟩ := exlenC m
      have bl : bytes.length = 10 := by rw [be, List.length_append, sl]; rfl
      have := gz (by rw [m]; decide) isG
      have := sh.of_exlen m
      omega
    · exact sh.not_extra m
    · exact sh.not_name m
    · exact sh.not_comment m
    · obtain ⟨isG, _, _, _, _, _, _, _, _, _, _, hcrcC⟩ :=
        gzC (by rw [m]; decide) (by rw [m]; decide)
      obtain ⟨_, _, mt, xfl, os, ex, nm, cm, ⟨_, mtL, exL, nmOk, cmOk⟩, be⟩ := hcrcC m
      have g := lens.2.2 (notRawOf (by rw [m]; decide)) (head31 pre isG)
      have long := gzip_core_long (flg := bytes.getD 3 0) (xfl := xfl) (os := os) g mtL exL nmOk
        cmOk (Or.inr (be ▸ pre))
      rw [← be] at long
      have := sh.of_hcrc m
      omega
    · obtain ⟨bl, _, _, _, _⟩ := dictidC m
      have := lens.2.1 (notRawOf (by rw [m]; decide))
      have := sh.of_dictid m
      omega
  | needDict header => exact sh.not_dict stageM
  | body header pos =>
    obtain ⟨bd, dbits, wh, rfl, dparsed⟩ := parsed
    obtain ⟨rest, xAligned, blocks, _⟩ := header_split wh valid (X := dbits ++ held) (Q := [])
      (by rw [List.append_nil, bitsEq, List.append_assoc]) rfl
    exact body_starved dparsed stageM.1 sh heldBits xAligned blocks
  | trailer header out bytes =>
    obtain ⟨bd, dbits, pad, wh, dparsed, notRaw, padLength, pre, ne, rfl⟩ := parsed
    have modes : (loopState s l).mode = CHECK ∨ (loopState s l).mode = LENGTH := stageM.1
    obtain ⟨_, _, checkC, lengthC, _⟩ := wrapM
    have tl := wrapTrailer_length notRaw header out
    have pl := pre.length_le
    have neLen : bytes.length ≠ (WrapTrailer f.wrap header out).length :=
      fun e => ne (pre.eq_of_length e)
    simp only [List.length_append, bytesToBits_length'] at lengths
    obtain ⟨outEq, moreLen⟩ := finished_rest wh dparsed padLength valid
      (more := bytesToBits bytes ++ held) (Q := [])
      (by rw [List.append_nil, bitsEq]; simp only [List.append_assoc])
      (by rw [List.length_append, bytesToBits_length']; omega) rfl
    subst outEq
    rw [List.length_append, bytesToBits_length'] at moreLen
    rcases modes with m | m
    · have be := checkC m
      have bl : bytes.length = 0 := by rw [be]; rfl
      have := sh.of_check m
      simp only [List.length_nil] at moreLen
      omega
    · obtain ⟨bl, _⟩ := lengthC m
      have := sh.of_length m
      simp only [List.length_nil] at moreLen
      omega
  | done out => exact sh.not_done stageM

#print axioms LoopMatches.starved_not_end

/-- The `BAD` case of `FailWithin`, per trip: input read that is refuted is
comparable with no valid full-window stream that a longer input is comparable
with. -/
theorem LoopRefuted.not_comparable {f : LoopFrame} {l : IL} (refuted : LoopRefuted f l)
    {offered S decoded : List UInt8} (valid : Api.Layer.Decodes f.wrap f.configured f.dict S decoded)
    (full : Api.FullWindow f.wrap f.configured S)
    (read : f.logIn ++ f.inp.take (loopRead l) <+: offered) (cmp : offered <+: S ∨ S <+: offered) :
    False := by
  apply refuted S decoded valid full
  rcases cmp with p | p
  · exact Or.inl (read.trans p)
  · exact List.prefix_or_prefix_of_prefix read p

#print axioms LoopRefuted.not_comparable

end Zlib.Inflate.Proofs
