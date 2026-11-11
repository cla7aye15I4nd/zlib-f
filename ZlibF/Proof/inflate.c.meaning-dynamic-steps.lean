import ZlibF.Proof.«inflate.c.meaning-length»
import ZlibF.Proof.«inflate.c.meaning-dynamic»
import ZlibF.Proof.«inflate.c.table-fields-meaning»

/-!
# inflate.c: `TABLE`, `LENLENS` and `CODELENS` keep the format meaning

The three modes of a dynamic block header. Each step starts from
`LoopMatches` at a `.dynamicHeader` position and ends in one of four ways:
it leaves the call with the meaning kept, it goes to `BAD` and no
continuation of the input read so far is valid (`LoopDoomed`), it reaches a
new position, or it falls through to the next mode with `LoopMatches` at
that mode.

* `case TABLE` waits for 14 bits and reads `HLIT`, `HDIST`, `HCLEN`
  (`DeflateParsed.dynamicBits`). Counts beyond 286 or 30 go to `BAD`: no
  `Body.dynamic` has them (`DynamicCountsOK`). Otherwise it falls through to
  `LENLENS` with no code-length code length read.
-/

namespace Zlib.Inflate.Proofs.MeaningDynamicSteps
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningDynamic
set_option autoImplicit false

/-! ## Stages and bits -/

/-- The only stage a `TABLE`, `LENLENS` or `CODELENS` state can stand for. -/
theorem stage_of_dynamic {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ header out final hdr, stage = .body header ⟨out, final, .dynamicHeader hdr⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rcases mode with m | m | m <;> rw [m] at lo hi <;> exact absurd hi (by decide)
  · have this := stageFacts
    simp only [LoopStageMatches] at this
    rcases mode with m | m | m <;> rw [m] at this <;> exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | hdr | ⟨L, D, pending⟩ | _
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · exact ⟨header, out, final, hdr, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      all_goals (rcases mode with m | m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide))
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
  · obtain ⟨m', _⟩ := stageFacts
    rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
  · have m' : s.mode = DONE := stageFacts
    rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)

/-- The state record after a `BAD` exit has mode `BAD`. -/
theorem bad_heap_mode {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {i : Nat} (st : c.st = some (.tab zs)) :
    ∀ zs' s', c.st = some (.tab zs') → (tcBadHeap h r zs z s i).istates zs' = some s' →
      s'.mode = BAD := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  simp only [tcBadHeap, setI_istates_same, Option.some.injEq] at hs'
  rw [← hs']

/-- The state record after `setI` is the one stored. -/
theorem setI_state {c : Ctx} {h : Heap} {zs : Nat} (s2 : InflateState) (st : c.st = some (.tab zs)) :
    ∀ zs' s', c.st = some (.tab zs') → (setI h zs s2).istates zs' = some s' → s' = s2 := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  rw [setI_istates_same] at hs'
  cases hs'
  rfl

/-- The three count fields read from the low 14 held bits. -/
theorem counts_bits (v : Nat) :
    readBits 5 (natBits 14 v) = some (v % 32, natBits 9 (v / 32)) ∧
    readBits 5 (natBits 9 (v / 32)) = some (v / 32 % 32, natBits 4 (v / 32 / 32)) ∧
    readBits 4 (natBits 4 (v / 32 / 32)) = some (v / 32 / 32 % 16, []) := by
  have s14 : natBits 14 v = natBits 5 v ++ natBits 9 (v / 32) := natBits_add 5 9 v
  have s9 : natBits 9 (v / 32) = natBits 5 (v / 32) ++ natBits 4 (v / 32 / 32) :=
    natBits_add 5 4 (v / 32)
  refine ⟨?_, ?_, ?_⟩
  · rw [s14, readBits_natBits]
  · rw [s9, readBits_natBits]
  · have := readBits_natBits 4 (v / 32 / 32) []
    rwa [List.append_nil] at this

/-! ## `TABLE` -/

set_option maxHeartbeats 4000000 in
/-- `case TABLE` keeps the format meaning. Without 14 bits it leaves with all
input read (`have = 0`) and the empty header held. Otherwise it reads `HLIT`,
`HDIST` and `HCLEN`: counts beyond 286 or 30 go to `BAD` with no valid
continuation of the input; otherwise it falls through to `LENLENS`
(`have = 0`) at the position after the 14 bits. No hypothesis beyond the
stream record. -/
theorem table_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (tableMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = TABLE) :
    (∃ result l' h', runX (inflate_TABLE c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ l'.have_ = 0 ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
         LoopDoomed f l'))) ∨
    (∃ l' h', runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) l' h' ∧
      loopRead l ≤ loopRead l' ∧
      (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = LENLENS) ∧
      LoopMatches c f h' l') := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have mode : s.mode = TABLE := tableMode zs s st hs
  obtain ⟨header, out, final, hdr, rfl⟩ := stage_of_dynamic stageM (Or.inl mode)
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨dyn, last⟩, window, check⟩ := stageM
  have tab : hdr = [] ∧ l.bits.toNat < 22 := by
    rcases dyn with ⟨_, e, b⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨m, _⟩ | ⟨m, _⟩⟩
    · exact ⟨e, b⟩
    · exact absurd (mode.symm.trans m) (by decide)
    · exact absurd (mode.symm.trans m) (by decide)
  obtain ⟨rfl, bitsLt⟩ := tab
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  obtain ⟨result, l1, j, run, jle, binv1, streamEq, _, shape, bitsBound, _, enough, empty,
    kinds, nextEq⟩ := NEEDBITS_run_cursor binv 14 (by decide)
  obtain ⟨rr, l1', j', run', jle', binv1', _, leaveFacts, okFacts⟩ := inflate_TABLE_run strm st hz hs binv
  have same := Except.ok.inj (run'.symm.trans run)
  have e1 : result = rr := (congrArg (fun p => p.1.1) same).symm
  have e2 : l1 = l1' := (congrArg (fun p => p.1.2) same).symm
  subst e1 e2
  have haveOld := binv.have_eq
  have haveNew := binv1.have_eq
  have haveNew' := binv1'.have_eq
  simp only [List.length_drop, loopRead] at haveOld haveNew haveNew' jle jle'
  have e3 : j = j' := by omega
  subst e3
  have keep1 : RegsKeep l l1 := RegsKeep.of_shape shape
  have readEq : loopRead l1 = loopRead l + j := by
    simp only [loopRead, keep1.1]
    omega
  have used : l1.have_.toNat + j = l.have_.toNat := by omega
  have bits1 := bits_pull bitsEq readEq streamEq
  have binvL : BitInv h l1 (f.inp.drop (loopRead l1)) := by
    rw [readEq, ← List.drop_drop]
    exact binv1
  rcases kinds with rfl | rfl
  · -- the 14 bits are held
    obtain ⟨b14, binvT, streamT, bad, good⟩ := okFacts rfl
    have bound : l1.bits.toNat ≤ 21 := by
      change l1.bits.toNat ≤ max l.bits.toNat 21 at bitsBound
      omega
    have streamT' : stream (tableRegs l1) ((f.inp.drop (loopRead l)).drop j) =
        (stream l1 ((f.inp.drop (loopRead l)).drop j)).drop 14 := by
      rw [streamT, streamEq]
    have heldT := held_drop streamT' b14
    have countT : (tableRegs l1).bits.toNat = l1.bits.toNat - 14 := by
      have := congrArg List.length heldT
      rw [natBits_length, List.length_drop, natBits_length] at this
      exact this
    have split : natBits l1.bits.toNat l1.hold.toNat =
        natBits 14 l1.hold.toNat ++ natBits (tableRegs l1).bits.toNat (tableRegs l1).hold.toNat := by
      rw [heldT, ← natBits_take l1.bits.toNat l1.hold.toNat 14 b14, List.take_append_drop]
    have readT : loopRead (tableRegs l1) = loopRead l + j := readEq
    have bitsT : bytesToBits (f.logIn ++ f.inp.take (loopRead (tableRegs l1))) =
        (consumed ++ natBits 14 l1.hold.toNat) ++
          natBits (tableRegs l1).bits.toNat (tableRegs l1).hold.toNat := by
      rw [readT, ← readEq, bits1, split, List.append_assoc]
    have binvT' : BitInv h (tableRegs l1) (f.inp.drop (loopRead (tableRegs l1))) := by
      rw [readT, ← List.drop_drop]
      exact binvT
    obtain ⟨read1, read2, read3⟩ := counts_bits l1.hold.toNat
    obtain ⟨hlit, hdist, hclen, firstRest, secondRest, f1, f2, f3, nlenEq, ndistEq, ncodeEq⟩ :=
      tableCounts_read_fields s binv1 b14
    have streamSplit : stream l1 ((f.inp.drop (loopRead l)).drop j) =
        natBits 14 l1.hold.toNat ++ (natBits (tableRegs l1).bits.toNat (tableRegs l1).hold.toNat ++
          bytesBits ((f.inp.drop (loopRead l)).drop j)) := by
      simp only [stream, split, List.append_assoc]
    rw [streamSplit] at f1
    rw [ZlibF.Spec.Proofs.readBits_append _ _ _ _ _ read1] at f1
    simp only [Option.some.injEq, Prod.mk.injEq] at f1
    obtain ⟨rfl, rfl⟩ := f1
    rw [ZlibF.Spec.Proofs.readBits_append _ _ _ _ _ read2] at f2
    simp only [Option.some.injEq, Prod.mk.injEq] at f2
    obtain ⟨rfl, rfl⟩ := f2
    have read2' : readBits 5 (natBits 9 (l1.hold.toNat / 32)) =
        some (l1.hold.toNat / 32 % 32, natBits 4 (l1.hold.toNat / 32 / 32)) := read2
    rw [ZlibF.Spec.Proofs.readBits_append _ _ _ _ _ read3] at f3
    simp only [Option.some.injEq, Prod.mk.injEq] at f3
    obtain ⟨rfl, _⟩ := f3
    by_cases tooMany : (tableCounts s l1.hold).nlen > 286 ∨ (tableCounts s l1.hold).ndist > 30
    · -- the counts are out of range
      left
      obtain ⟨i, _, runBad⟩ := bad tooMany
      refine ⟨.ok (), tableRegs l1, _, runBad, Or.inr ⟨rfl, by rw [readT]; omega,
        bad_heap_mode st, ?_⟩⟩
      apply doomed_of_aligned (rest := natBits l1.bits.toNat l1.hold.toNat) wrapHeader deflate
      · show bytesToBits (f.logIn ++ f.inp.take (loopRead l1)) = _
        rw [bits1, consumedEq]
      · intro more tail outF _ resid
        obtain ⟨_, _, body, _⟩ := resid
        cases body with
        | dynamic r1 r2 _ counts =>
          obtain ⟨c1, c2⟩ := counts
          rw [List.nil_append, split, List.append_assoc,
            ZlibF.Spec.Proofs.readBits_append _ _ _ _ _ read1] at r1
          simp only [Option.some.injEq, Prod.mk.injEq] at r1
          obtain ⟨rfl, rfl⟩ := r1
          rw [ZlibF.Spec.Proofs.readBits_append _ _ _ _ _ read2'] at r2
          simp only [Option.some.injEq, Prod.mk.injEq] at r2
          obtain ⟨rfl, rfl⟩ := r2
          rcases tooMany with big | big
          · have := UInt32.lt_iff_toNat_lt.mp big
            rw [nlenEq] at this
            change 286 < _ at this
            omega
          · have := UInt32.lt_iff_toNat_lt.mp big
            rw [ndistEq] at this
            change 30 < _ at this
            omega
    · -- `LENLENS` follows
      right
      have runGood := good tooMany
      have countsOK : DynamicCountsOK (l1.hold.toNat % 32) (l1.hold.toNat / 32 % 32) := by
        have litBound := (not_or.mp tooMany).1
        have distBound := (not_or.mp tooMany).2
        rw [gt_iff_lt, UInt32.lt_iff_toNat_lt] at litBound distBound
        change ¬ 286 < (tableCounts s l1.hold).nlen.toNat at litBound
        change ¬ 30 < (tableCounts s l1.hold).ndist.toNat at distBound
        rw [nlenEq] at litBound
        rw [ndistEq] at distBound
        constructor <;> omega
      let s2 : InflateState := { tableCounts s l1.hold with «have» := 0, mode := LENLENS }
      have parsed2 := DeflateParsed.dynamicBits (natBits 14 l1.hold.toNat) deflate
      rw [List.nil_append] at parsed2
      have moved := loop_move (s' := s2) (l' := tableRegs l1) (j := j)
        (pos := ⟨out, final, .dynamicHeader (natBits 14 l1.hold.toNat)⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show LENLENS ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
        (keep1.trans ⟨rfl, rfl, rfl, rfl, rfl⟩) used nextEq binvT' bitsT
        (HeldBits.of_natBits (s := loopState s2 (tableRegs l1)) binvT'.hold_lt) wrapHeader
        (by rw [consumedEq, List.append_assoc]) parsed2
        ⟨Or.inr ⟨l1.hold.toNat % 32, l1.hold.toNat / 32 % 32, l1.hold.toNat / 32 / 32 % 16,
            natBits 9 (l1.hold.toNat / 32), natBits 4 (l1.hold.toNat / 32 / 32), [],
            read1, read2', read3, countsOK, nlenEq, ndistEq, ncodeEq,
            Or.inl ⟨rfl, by show (0 : UInt32).toNat < _; simp,
              by change (tableRegs l1).bits.toNat < 11; omega, [], rfl,
              fun j lt => absurd lt (by show ¬ j < (0 : UInt32).toNat; simp)⟩⟩, last⟩
        (window_transfer (s := loopState s l) (s' := loopState s2 (tableRegs l1)) rfl rfl rfl rfl
          (fun q => byte_view_get_setI h zs s2 q) window) check wrapM outputEq
      refine ⟨tableRegs l1, setI h zs s2, runGood, by rw [readT]; omega, ?_, moved⟩
      intro zs' s' st' hs'
      rw [setI_state s2 st zs' s' st' hs']
  · -- not enough input
    left
    obtain ⟨wait, _, _, runLeave⟩ := leaveFacts rfl
    have moved := loop_move (s' := s) (l' := l1) (j := j) (pos := ⟨out, final, .dynamicHeader []⟩)
      st retOk config haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep1
      used nextEq binvL bits1 (HeldBits.of_natBits (s := loopState s l1) binv1.hold_lt) wrapHeader
      consumedEq deflate
      ⟨Or.inl ⟨mode, rfl, by
        have := (empty rfl).2.2; change l1.bits.toNat < 14 at this; change l1.bits.toNat < 22; omega⟩, last⟩
      (window_transfer (s := loopState s l) (s' := loopState s l1) rfl rfl rfl rfl
        (fun q => byte_view_get_setI h zs s q) window) check wrapM outputEq
    rw [setI_self hs] at moved
    exact ⟨_, _, _, runLeave, Or.inl ⟨rfl, wait, moved⟩⟩

#print axioms table_step

end Zlib.Inflate.Proofs.MeaningDynamicSteps
