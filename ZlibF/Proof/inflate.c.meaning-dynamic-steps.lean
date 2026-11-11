import ZlibF.Proof.«inflate.c.meaning-length»
import ZlibF.Proof.«inflate.c.meaning-dynamic»
import ZlibF.Proof.«inflate.c.table-fields-meaning»
import ZlibF.Proof.«inflate.c.header-chunks»
import ZlibF.Proof.«inflate.c.lenlens-input»
import ZlibF.Proof.«inflate.c.code-length-install»
import ZlibF.Proof.«inflate.c.lenlens-code-length-meaning»

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
* `case LENLENS` reads the code-length code lengths three bits at a time
  across calls. With all of them it builds the code-length table: an
  unacceptable code goes to `BAD` (`Body.dynamic` needs
  `Acceptable .codeLength`), otherwise it falls through to `CODELENS` with
  `CodeLengthMeaning` of the table and no length read.
-/

namespace Zlib.Inflate.Proofs.MeaningDynamicSteps
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningDynamic
open Zlib.Inftrees (inflate_table)
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

/-- `ll1_run_cursor` with the bound after at least one read: a byte is
pulled only while fewer than 3 bits are held, so a read leaves at most
`max bits 10 - 3` bits. -/
theorem ll1_run_short {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hsz : s.lens.size = 320)
    (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat) (B : BitInv h l bs) :
    ∃ r l' j, runX (xwhile (llCond c) (llBody c)) l h =
        .ok ((r, l'), setI h zs (llSt s (stream l bs) (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)))) ∧
      j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = (stream l bs).drop (3 * min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3)) ∧
      TcRegShape l l' ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) < s.ncode.toNat - s.«have».toNat →
        r = .error Ex.leave ∧ l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 3) ∧
      (min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) = s.ncode.toNat - s.«have».toNat → r = .ok ()) ∧ l'.next = inputAdvance l.next j ∧
      l'.bits.toNat ≤ max l.bits.toNat 10 ∧
      (0 < min (s.ncode.toNat - s.«have».toNat) ((stream l bs).length / 3) → l'.bits.toNat + 3 ≤ max l.bits.toNat 10) := by
  obtain ⟨n, hn⟩ : ∃ n, n = s.ncode.toNat - s.«have».toNat := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = stream l bs := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = min n (S.length / 3) := ⟨_, rfl⟩
  rw [← hn, ← hS, ← hM]
  have key := xwhileBrk_run (cond := llCond c) (body := (do llBody c; pure false : X Bool))
    (fun k l1 h1 => ∃ m j, k + m = n ∧ m ≤ M ∧ j ≤ bs.length ∧ h1 = setI h zs (llSt s S m) ∧
      BitInv h l1 (bs.drop j) ∧ stream l1 (bs.drop j) = S.drop (3 * m) ∧ TcRegShape l l1 ∧ l1.next = inputAdvance l.next j ∧ l1.bits.toNat ≤ max l.bits.toNat 10 ∧
      (0 < m → l1.bits.toNat + 3 ≤ max l.bits.toNat 10))
    (fun r l1 h1 => ∃ j, j ≤ bs.length ∧ h1 = setI h zs (llSt s S M) ∧ BitInv h l1 (bs.drop j) ∧
      stream l1 (bs.drop j) = S.drop (3 * M) ∧ TcRegShape l l1 ∧
      (M < n → r = .error Ex.leave ∧ l1.have_ = 0 ∧ j = bs.length ∧ l1.bits.toNat < 3) ∧ (M = n → r = .ok ()) ∧ l1.next = inputAdvance l.next j ∧ l1.bits.toNat ≤ max l.bits.toNat 10 ∧
      (0 < M → l1.bits.toNat + 3 ≤ max l.bits.toNat 10))
    (fun k l1 h1 hP => by
      obtain ⟨m, j, hk, hmM, hj, hh1, B1, hS1, hsh1, cursor, bitBound, bitBound2⟩ := hP
      subst hh1
      have hmn : m < n := by omega
      have hb19 : s.«have».toNat + m < 19 := by omega
      have hht := llSt_have s S m (by omega)
      have ht : (setI h zs (llSt s S m)).istates zs = some (llSt s S m) := by simp
      have hszt : (llSt s S m).lens.size = 320 := by simp [llSt, lensRead_size, hsz]
      have hHt : (llSt s S m).«have».toNat < 19 := by omega
      have hcond : runX (llCond c) l1 (setI h zs (llSt s S m)) = .ok ((.ok true, l1), setI h zs (llSt s S m)) := by
        unfold llCond
        rw [hc]
        simp only [runX_bind, runX_lift, ldI_eq, ht, runX_pure]
        have : (llSt s S m).«have» < (llSt s S m).ncode := by
          rw [UInt32.lt_iff_toNat_lt, hht]
          show _ < s.ncode.toNat
          omega
        simp [this]
      obtain ⟨rr, l', jn, hrun, hjn, B', hS', hshape, hleave, hok, stepCursor, stepBits⟩ :=
        llBody_run_cursor (c := c) hc ht hszt hHt (B1.tc_setI zs _)
      have nextCursor : l'.next = inputAdvance l.next (j + jn) := by
        rw [stepCursor, cursor, inputAdvance_add]
      have nextBits : l'.bits.toNat ≤ max l.bits.toNat 10 := by omega
      have hlen := tcStream_length B1
      have hlen' := tcStream_length B'
      refine ⟨l1, setI h zs (llSt s S m), hcond, ?_⟩
      cases rr with
      | error e =>
        cases e with
        | leave =>
          obtain ⟨h1, h2, h3, hbody⟩ := hleave rfl
          refine ⟨.error Ex.leave, l', setI h zs (llSt s S m), ?_, ?_⟩
          · rw [runX_bind, hbody]
          · -- the loop stops here: `m = M`
            have hlenS : (S.drop (3 * m)).length = l'.bits.toNat := by
              rw [← hS1, ← hS', tcStream_length B', h2, List.drop_length]; simp
            simp only [List.length_drop] at hlenS
            have hmM' : m = M := by omega
            subst hmM'
            have hjl : j + jn = bs.length := by
              have : (bs.drop j).length = bs.length - j := by simp
              omega
            refine ⟨j + jn, by omega, rfl, ?_, ?_, ?_, fun _ => ⟨rfl, h1, hjl, h3⟩, (fun hh => by omega), nextCursor, nextBits, fun _ => by omega⟩
            · simpa [tcDrop_drop] using B'.tc_of_heap (h' := h) rfl rfl rfl rfl
            · rw [← hS1, ← hS']; simp [tcDrop_drop]
            · exact hsh1.trans hshape
        | ret v => exact absurd rfl (noRet_NEEDBITS 3 l1 _ _ l' _ hrun v)
      | ok u =>
        cases u
        obtain ⟨h3, hbody⟩ := hok rfl
        have hSlen : 3 ≤ (S.drop (3 * m)).length := by
          have hh : (S.drop (3 * m)).length = l'.bits.toNat + 8 * ((bs.drop j).drop jn).length := by
            rw [← hS1, ← hS']; exact tcStream_length B'
          omega
        simp only [List.length_drop] at hSlen
        have hmM1 : m + 1 ≤ M := by
          rw [hM]
          apply Nat.le_min.mpr
          constructor <;> omega
        have hgrp : grp S m = l'.hold.toNat % 8 := by
          unfold grp
          rw [← hS1, ← hS']
          simp only [stream, tcDrop_drop]
          exact grp_head _ _ _ h3
        have hbits7 : (l'.hold.toUInt32 &&& 7).toNat = grp S m := by
          rw [hgrp]
          have := BITS_toNat l' 3 (by decide)
          rw [show ((1 : UInt32) <<< (3 : UInt32) - 1) = 7 by decide] at this
          rw [this]
          rfl
        have hv : (l'.hold.toUInt32 &&& 7).toUInt16 = (grp S m).toUInt16 := by
          show UInt16.ofNat (l'.hold.toUInt32 &&& 7).toNat = UInt16.ofNat (grp S m)
          rw [hbits7]
        obtain ⟨hB3, hS3, hsub3⟩ := DROPBITS_inv B' 3 h3 (by decide)
        have hB3' : BitInv h { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 } ((bs.drop j).drop jn) := by
          have := hB3.tc_of_heap (h := setI h zs (llSt s S m)) (h' := h) rfl rfl rfl rfl
          exact this
        refine ⟨.ok false, { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 }, setI h zs (llSt s S (m + 1)), ?_, ?_⟩
        · rw [runX_bind, hbody, ← llSt_succ s S m hb19 _ hv]
          simp [runX_pure, setI_setI]
        · have hjn' : jn ≤ bs.length - j := by simpa using hjn
          refine ⟨m + 1, j + jn, by omega, hmM1, by omega, rfl, ?_, ?_, ?_, nextCursor, ?_⟩
          · simpa [tcDrop_drop] using hB3'
          · have hS3' : stream { l' with hold := l'.hold >>> 3, bits := l'.bits - 3 } ((bs.drop j).drop jn) =
                (stream l' ((bs.drop j).drop jn)).drop 3 := hS3
            rw [hS'] at hS3'
            simp only [tcDrop_drop] at hS3' ⊢
            rw [hS3', hS1, tcDrop_drop]
            congr 1
          · exact (hsh1.trans hshape).drop _ _
          · change (l'.bits - 3).toNat ≤ _ ∧ (0 < m + 1 → (l'.bits - 3).toNat + 3 ≤ _)
            rw [hsub3]
            have t3 : (3 : UInt32).toNat = 3 := rfl
            omega)
    (fun l1 h1 hP => by
      obtain ⟨m, j, hk, hmM, hj, hh1, B1, hS1, hsh1, cursor, bitBound, bitBound2⟩ := hP
      subst hh1
      have hmn : m = n := by omega
      have hMm : M = m := by omega
      have ht : (setI h zs (llSt s S m)).istates zs = some (llSt s S m) := by simp
      have hht := llSt_have s S m (by omega)
      have hcond : runX (llCond c) l1 (setI h zs (llSt s S m)) = .ok ((.ok false, l1), setI h zs (llSt s S m)) := by
        unfold llCond
        rw [hc]
        simp only [runX_bind, runX_lift, ldI_eq, ht, runX_pure]
        have : ¬ (llSt s S m).«have» < (llSt s S m).ncode := by
          rw [UInt32.lt_iff_toNat_lt, hht]
          show ¬ _ < s.ncode.toNat
          omega
        simp [this]
      refine ⟨l1, _, hcond, j, hj, by rw [hMm], B1, by rw [hMm]; exact hS1, hsh1, (fun hh => by omega), (fun _ => rfl), cursor, bitBound, by rw [hMm]; exact bitBound2⟩)
    (k := n) (l := l) (h := h)
    ⟨0, 0, by omega, by omega, by omega, by rw [llSt_zero]; exact (tcSetI_same hs).symm, by simpa using B,
      by simp [hS], TcRegShape.refl l, (inputAdvance_zero l.next).symm, by omega, fun h0 => absurd h0 (by omega)⟩ (by unfold fuel; omega)
  obtain ⟨r, l', h', hrun, j, hj, hh', B', hS', hsh, hl, hok, cursor, bits, bits2⟩ := key
  subst hh'
  exact ⟨r, l', j, hrun, hj, B', hS', hsh, hl, hok, cursor, bits, bits2⟩

/-! ## `LENLENS` -/

theorem readNats_facts {w : Nat} : ∀ {n : Nat} {inp : List Bool} {vs : List Nat} {r : List Bool},
    readNats w n inp = some (vs, r) → vs.length = n ∧ ∀ v ∈ vs, v < 2 ^ w
  | 0, inp, vs, r, read => by
    simp only [readNats, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, _⟩ := read
    simp
  | n + 1, inp, vs, r, read => by
    cases first : readBits w inp with
    | none => simp [readNats, first] at read
    | some pair =>
      obtain ⟨value, middle⟩ := pair
      cases tail : readNats w n middle with
      | none => simp [readNats, first, tail] at read
      | some pair =>
        obtain ⟨suffix, final⟩ := pair
        simp only [readNats, first, tail, Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, _⟩ := read
        obtain ⟨len, small⟩ := readNats_facts tail
        refine ⟨by simp [len], ?_⟩
        intro v member
        rcases List.mem_cons.mp member with rfl | inside
        · exact (ZlibF.Math.CodeLengthPrefix.read_word first).1
        · exact small v inside

theorem getD_of_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem clOrder_getD : ∀ i, i < 19 → clOrder.getD i 0 = orderNat i := by
  unfold clOrder orderNat order
  decide +kernel

/-- The lengths of `DynamicMatches` at `LENLENS` are the source-order fields. -/
theorem headerFields_of_matches {a : Array UInt16} {count : Nat} {vs : List Nat}
    (small : count < 19) (len : vs.length = count)
    (cells : ∀ j, j < count → (a.getD (clOrder.getD j 0) 0).toNat = vs.getD j 0) :
    headerFields a count = vs := by
  apply List.ext_getElem
  · rw [headerFields_length, len]
  · intro i h1 h2
    have inside : i < count := by rw [headerFields_length] at h1; exact h1
    have e1 := headerFields_get (a := a) inside
    rw [getD_of_lt h1] at e1
    rw [e1, ← clOrder_getD i (by omega), cells i inside, getD_of_lt h2]

/-- Bytes read after the held bits join them. -/
theorem bits_take {f : LoopFrame} {l : IL} {j : Nat} {consumed held : List Bool}
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ held) :
    bytesToBits (f.logIn ++ f.inp.take (loopRead l + j)) =
      consumed ++ (held ++ bytesBits ((f.inp.drop (loopRead l)).take j)) := by
  rw [List.take_add, ← List.append_assoc, bytesToBits_append', bitsEq, bytesBits_eq_bytesToBits,
    List.append_assoc]

theorem decodeSym_none_of_zero {lens : List Nat} (zero : ∀ k, lens.getD k 0 = 0) (inp : List Bool) :
    decodeSym lens inp = none := by
  unfold decodeSym
  rw [List.find?_eq_none.mpr (fun s _ => by
    have z := zero s
    rw [List.getD_eq_getElem?_getD] at z
    simp [z])]

theorem lensList_zero (a : Array UInt16) (n : Nat) :
    Zlib.Inftrees.Spec.lensList a 0 n = Zlib.Inftrees.Proofs.lensOf (fun k => (a.getD k 0).toNat) n := by
  simp [Zlib.Inftrees.Spec.lensList, Zlib.Inftrees.Proofs.lensOf]

/-- The `LENLENS` constructor call returns 0 on an acceptable code-length code. -/
theorem llInstall_accepts {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (lengths : Good3 s.lens 19) :
    ∃ (ret : Int32) (next : CodePtr) (root : UInt32) (work : Array UInt16) (codes : Array Code),
      runX (llInstall c) l h = .ok ((.ok ret, { l with ret := ret }),
        setI h zs { llPre zs s with next := next, lenbits := root, work := work, codes := codes }) ∧
      (Acceptable .codeLength (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) 19) →
        ret = 0) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (llPre zs s)).istates zs = some (llPre zs s) := by simp
  have lens : Space.get (setI h zs (llPre zs s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [llPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (llPre zs s)) (WRef.istate_work zs) = some s.work := by
    simpa [llPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (llPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [llPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (llPre zs s)) CODES
      (.istate_lens zs) 0 19 (.istate_codes zs) 0 7 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inl rfl, lens, work, codes, by simp, by simp,
      by simp; omega, by simp; omega,
      by simp [Zlib.Inftrees.Spec.capOf, CODES]; omega,
      (by intro k inside; have := lengths.all k (by simpa using inside); simpa using (by omega : (s.lens.getD k 0).toNat ≤ 15)),
      (by intro _; exact ⟨by decide, fun k inside => by simpa using lengths.all k (by simpa using inside), by decide⟩),
      (by intro impossible; cases impossible), (by intro impossible; cases impossible)⟩
  obtain ⟨result, after, run, frame, _⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_establishes_code_length_contents pre
  obtain ⟨result', after', run', reject, _, capacity⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_correct_ret (setI h zs (llPre zs s)) CODES
      (.istate_lens zs) 0 19 (.istate_codes zs) 0 7 (.istate_work zs) 0
      pre.la pre.wa pre.ca pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne
      pre.hla pre.hwa pre.hca pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [run] at run'
  cases run'
  obtain ⟨ret, next, root⟩ := result
  obtain ⟨work, codes, heap, _, _, _, _, retCases⟩ := frame
  have heapEq : after = setI h zs (llBadSt zs s work codes) := by
    rw [heap, put_work_codes stored]
    simp [setI_setI, llBadSt, llPre]
  refine ⟨ret, next, root, work, codes, ?_, ?_⟩
  · unfold llInstall
    rw [hc]
    have call : inflate_table CODES (.ref (WRef.istate_lens zs) 0) 19
        (.ref (CodeRef.istate_codes zs) 0) 7 (.ref (WRef.istate_work zs) 0)
        (setI h zs (llPre zs s)) = .ok ((ret, next, root), after) := run
    simp [llPre] at call
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, lensP, workP, codesP,
      call, heapEq, runX_modify, runX_pure, llBadSt, llPre, setI_setI]
  · intro acceptable
    have kind : Zlib.Inftrees.Spec.kindOf CODES = ZlibF.Spec.CodeKind.codeLength := by
      simp [Zlib.Inftrees.Spec.kindOf]
    rw [kind] at reject capacity
    have listEq : Zlib.Inftrees.Spec.lensList pre.la 0 (19 : UInt32).toNat =
        Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) 19 := lensList_zero s.lens 19
    rw [listEq] at reject capacity
    rcases retCases with ⟨zero, _⟩ | ⟨one | bad, _⟩
    · exact zero
    · exact absurd rfl (capacity one).2
    · exact absurd acceptable (reject.mp bad)

set_option maxHeartbeats 8000000 in
/-- `case LENLENS` keeps the format meaning. It reads the code-length code
lengths three bits at a time (`DeflateParsed.dynamicBits` with the fields
read). Without input it leaves (`have = 0`) with fewer than `ncode` lengths
read. With all of them it builds the code-length table: an unacceptable
code-length code goes to `BAD` with no valid continuation of the input
(`Body.dynamic` needs `Acceptable .codeLength`); otherwise it falls through to
`CODELENS` with the code-length code meaning of the table, no length read,
and fewer than 8 held bits. The empty code-length code is accepted; its
table has the cells `{64, 1, 0}`.

`wf` (the array sizes of the state record) is supplied by the safety
invariant (`Good`). -/
theorem lenlens_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (lenlensMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LENLENS)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed) :
    (∃ result l' h', runX (inflate_LENLENS c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ l'.have_ = 0 ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
         LoopDoomed f l'))) ∨
    (∃ l' h', runX (inflate_LENLENS c) l h = runX (inflate_CODELENS c) l' h' ∧
      loopRead l ≤ loopRead l' ∧
      (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = CODELENS) ∧
      LoopMatches c f h' l') := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have mode : s.mode = LENLENS := lenlensMode zs s st hs
  have wfS := wf zs s st hs
  obtain ⟨header, out, final, hdr, rfl⟩ := stage_of_dynamic stageM (Or.inr (Or.inl mode))
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨dyn, last⟩, window, check⟩ := stageM
  obtain ⟨hlit, hdist, hclen, r1, r2, r3, read1, read2, read3, counts, nlenEq, ndistEq, ncodeEq,
      haveLt, bitsLt, vs, readVs, lensVs⟩ :
      ∃ (hlit hdist hclen : Nat) (r1 r2 r3 : List Bool),
        readBits 5 hdr = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
        readBits 4 r2 = some (hclen, r3) ∧ DynamicCountsOK hlit hdist ∧
        s.nlen.toNat = hlit + 257 ∧ s.ndist.toNat = hdist + 1 ∧ s.ncode.toNat = hclen + 4 ∧
        s.«have».toNat < hclen + 4 ∧ l.bits.toNat < 11 ∧
        ∃ vs, readNats 3 s.«have».toNat r3 = some (vs, []) ∧
          ∀ j, j < s.«have».toNat → (s.lens.getD (clOrder.getD j 0) 0).toNat = vs.getD j 0 := by
    rcases dyn with ⟨m, _, _⟩ | ⟨hlit, hdist, hclen, r1, r2, r3, read1, read2, read3, counts, e1, e2, e3,
      ⟨_, a, b, vs, c', d⟩ | ⟨m, _⟩⟩
    · exact absurd (mode.symm.trans m) (by decide)
    · exact ⟨hlit, hdist, hclen, r1, r2, r3, read1, read2, read3, counts, e1, e2, e3, a, b, vs, c', d⟩
    · exact absurd (mode.symm.trans m) (by decide)
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  have hclenLt : hclen < 16 := (ZlibF.Math.CodeLengthPrefix.read_word read3).1
  have ncodeLe : s.ncode.toNat ≤ 19 := by omega
  have haveLe' : s.«have».toNat ≤ s.ncode.toNat := by omega
  obtain ⟨vsLen, vsSmall⟩ := readNats_facts readVs
  have fields0 : headerFields s.lens s.«have».toNat = vs :=
    headerFields_of_matches (by omega) vsLen lensVs
  have good0 : Good3 s.lens s.«have».toNat := by
    intro i inside
    have hi : i < vs.length := by omega
    rw [← clOrder_getD i (by omega), lensVs i inside, getD_of_lt hi]
    have := vsSmall vs[i] (List.getElem_mem hi)
    change _ < 8 at this
    omega
  have r3Eq : r3 = vs.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) := by
    simpa using readNats_word readVs
  -- the read loop
  obtain ⟨result, l1, j, runLL, jle, binv1, _, shape1, leaveF, okF, next1, _, bits1b⟩ :=
    ll1_run_short st hs wfS.1 ncodeLe haveLe' binv
  obtain ⟨result', l1', j', count, values, countEq, runLL', jle', binv1', ledger, fields, small⟩ :=
    ll1_header_consumed_input st hs wfS.1 ncodeLe haveLe' binv
  rw [← countEq] at runLL leaveF okF bits1b
  have same := Except.ok.inj (runLL'.symm.trans runLL)
  have e1 : result = result' := (congrArg (fun p => p.1.1) same).symm
  have e2 : l1 = l1' := (congrArg (fun p => p.1.2) same).symm
  subst e1 e2
  have haveOld := binv.have_eq
  have haveNew := binv1.have_eq
  have haveNew' := binv1'.have_eq
  simp only [List.length_drop, loopRead] at haveOld haveNew haveNew' jle jle'
  have e3 : j = j' := by omega
  subst e3
  let st1 := llSt s (stream l (f.inp.drop (loopRead l))) count
  have keep1 : RegsKeep l l1 := RegsKeep.of_shape shape1
  have readEq : loopRead l1 = loopRead l + j := by
    simp only [loopRead, keep1.1]
    omega
  have used : l1.have_.toNat + j = l.have_.toNat := by omega
  obtain ⟨vb, hvb⟩ : ∃ vb, vb = values.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) :=
    ⟨_, rfl⟩
  rw [← hvb] at ledger
  have bits1 : bytesToBits (f.logIn ++ f.inp.take (loopRead l1)) =
      (consumed ++ vb) ++ natBits l1.bits.toNat l1.hold.toNat := by
    rw [readEq, bits_take bitsEq, ledger]
    simp only [List.append_assoc]
  have binvL : BitInv h l1 (f.inp.drop (loopRead l1)) := by
    rw [readEq, ← List.drop_drop]
    exact binv1
  have st1Have : st1.«have».toNat = s.«have».toNat + count := llSt_have s _ count (by omega)
  have fields1 : headerFields st1.lens st1.«have».toNat = vs ++ values := by
    rw [← fields0]; exact fields
  have valuesLen : values.length = count := by
    have := congrArg List.length fields1
    rw [headerFields_length, List.length_append, vsLen] at this
    omega
  have allSmall : ∀ v ∈ vs ++ values, v < 8 := by
    intro v member
    rcases List.mem_append.mp member with a | b
    · exact vsSmall v a
    · have := small v b; omega
  have r3' : r3 ++ vb = (vs ++ values).flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) := by
    rw [r3Eq, hvb, List.flatMap_append]
  have readVs' : readNats 3 st1.«have».toNat (r3 ++ vb) = some (vs ++ values, []) := by
    have := readNats_words_append (count := 0) (future := []) (rest := []) (suffix := []) rfl
      (vs ++ values) allSmall
    rw [r3', st1Have]
    simpa [vsLen, valuesLen] using this
  have lensVs' : ∀ i, i < st1.«have».toNat →
      (st1.lens.getD (clOrder.getD i 0) 0).toNat = (vs ++ values).getD i 0 := by
    intro i inside
    rw [← fields1, headerFields_get inside, clOrder_getD i (by omega)]
  obtain ⟨read1', read2', read3'⟩ := counts_append (more := vb) read1 read2 read3
  have parsed1 := DeflateParsed.dynamicBits vb deflate
  have consumed1 : consumed ++ vb = bytesToBits header ++ (bitsP ++ vb) := by
    rw [consumedEq, List.append_assoc]
  have window1 := fun (s' : InflateState) (l' : IL) (wnd : s'.window = s.window)
      (ws : s'.wsize = s.wsize) (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
    window_transfer (s := loopState s l) (s' := loopState s' l') wnd ws wn wh
      (fun q => byte_view_get_setI h zs s' q) window
  by_cases full : count = s.ncode.toNat - s.«have».toNat
  · -- all lengths read: the code-length table
    have okRun := okF full
    have st1Full : st1.«have».toNat = s.ncode.toNat := by omega
    have size1 : st1.lens.size = 320 := by simp [st1, llSt, lensRead_size, wfS.1]
    have good1 : Good3 st1.lens st1.«have».toNat := by
      have g := lensRead_good (a := s.lens) (i0 := s.«have».toNat) (stream l (f.inp.drop (loopRead l)))
        good0 count (by omega)
      rwa [← st1Have] at g
    let st2 := lzSt st1 (19 - st1.«have».toNat)
    have lzRun := lz_run (c := c) (l := l1) st (show (setI h zs st1).istates zs = some st1 by simp)
      size1 (by omega)
    have runTail : runX (inflate_LENLENS c) l h = runX (llTail c) l1 (setI h zs st2) := by
      rw [inflate_LENLENS_eq, runX_bind, runLL, okRun]
      simp only []
      rw [runX_bind, lzRun]
      simp only [setI_setI]
      rfl
    have wf2 : st2.WellFormed := ⟨by simp [st2, lzSt, lensZero_size, size1], wfS.2.1, wfS.2.2⟩
    have good2 : Good3 st2.lens 19 := by
      have g := lensZero_good good1 (19 - st1.«have».toNat) (by omega)
      rw [show st1.«have».toNat + (19 - st1.«have».toNat) = 19 by omega] at g
      exact g
    let cl := Zlib.Inftrees.Proofs.lensOf (fun k => (st2.lens.getD k 0).toNat) 19
    have readCL : readCodeLenLens (hclen + 4) (r3 ++ vb) = some (cl, []) := by
      have g1 : Good3 st1.lens s.ncode.toNat := by rw [← st1Full]; exact good1
      have := readCodeLenLens_header_fields (a := st1.lens) (by omega) s.ncode.toNat ncodeLe g1 []
      rw [List.append_nil] at this
      rw [← ncodeEq, r3', ← fields1, st1Full, this]
      show _ = some (Zlib.Inftrees.Proofs.lensOf
        (fun k => ((lensZero st1.lens st1.«have».toNat (19 - st1.«have».toNat)).getD k 0).toNat) 19, [])
      rw [st1Full]
    have hs2 : (setI h zs st2).istates zs = some st2 := by simp
    have hz2 : r.get (setI h zs st2) = some z := by simpa using hz
    by_cases accepted : Acceptable .codeLength cl
    · -- the table is built: `CODELENS` follows
      right
      obtain ⟨ret, next, root, work, codes, runInstall, cont⟩ :=
        llTail_code_length_contents_continuation (l := l1) st hs2 wf2 good2
      obtain ⟨ret', next', root', work', codes', runInstall', accepts⟩ :=
        llInstall_accepts (l := l1) st hs2 wf2 good2
      have sameI := Except.ok.inj (runInstall.symm.trans runInstall')
      have retEq : ret = ret' := Except.ok.inj (congrArg (fun p => p.1.1) sameI)
      have zero : ret = 0 := retEq.trans (accepts accepted)
      obtain ⟨contents, runC⟩ := cont zero
      let s3 : InflateState :=
        { llPre zs st2 with next := next, lenbits := root, work := work, codes := codes, «have» := 0, mode := CODELENS }
      have bitsSmall : l1.bits.toNat < 8 := by
        have := bits1b (by omega)
        omega
      have emptyFacts : (∀ k, cl.getD k 0 = 0) →
          (∀ i, i < 2 ^ root.toNat → codes[0 + i]? = some ⟨64, 1, 0⟩) := by
        intro allZero i inside
        rcases contents.layout with ⟨rootOne, _, c0, c1⟩ | ordinary
        · rw [rootOne] at inside
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · exact c0
          · exact c1
        · exfalso
          obtain ⟨entry, get, op⟩ := ordinary 0 (Nat.two_pow_pos _)
          have safeCell := contents.safe.2.2.2 0 (Nat.two_pow_pos _)
          have getD : codes.getD (0 + 0) default = entry := by
            simp only [Array.getD_eq_getD_getElem?, get, Option.getD_some]
          dsimp only at safeCell
          rw [getD] at safeCell
          have entryBits := safeCell.2.1
          obtain ⟨rest, read⟩ := MeaningLookup.readBits_natBits_prefix (k := root.toNat) (n := 15) (v := 0)
            (by have := contents.safe.2.1; omega)
          have padded : Zlib.Inftrees.Spec.DecodeShort.padded (natBits 15 0) = natBits 15 0 := by
            rw [MeaningLookup.padded_natBits (by decide)]
          rw [← padded, Nat.zero_mod] at read
          obtain ⟨symbol, _, _, _, decoded⟩ := contents.sound (natBits 15 0) rest 0 entry read get op
            (by rw [natBits_length]; have := contents.safe.2.1; omega)
          rw [decodeSym_none_of_zero allZero] at decoded
          cases decoded
      have parsedC : DeflateParsed bodyDict (bitsP ++ vb) ⟨out, final, .dynamicHeader (hdr ++ vb)⟩ :=
        parsed1
      have moved := loop_move (s' := s3) (l' := { l1 with ret := 0 }) (j := j)
        (pos := ⟨out, final, .dynamicHeader (hdr ++ vb)⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show CODELENS ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
        ⟨keep1.1, keep1.2.1, keep1.2.2.1, keep1.2.2.2.1, by show (0 : Int32) = l.ret; rw [retOk]; rfl⟩
        used next1 ⟨binvL.have_eq, binvL.next, binvL.hold_lt⟩ bits1
        (HeldBits.of_natBits (s := loopState s3 { l1 with ret := 0 }) binvL.hold_lt) wrapHeader
        consumed1 parsedC
        ⟨Or.inr ⟨hlit, hdist, hclen, r1 ++ vb, r2 ++ vb, r3 ++ vb, read1', read2', read3', counts,
            nlenEq, ndistEq, ncodeEq,
            Or.inr ⟨rfl, cl, [], .istate_codes zs, 0, codes, readCL, rfl,
              CodeRef.get_istate_codes (setI_istates_same h zs s3), contents.toCodeLengthMeaning,
              by show (0 : UInt32).toNat < _; simp only [UInt32.toNat_zero]; omega,
              by
                have e : lensPrefix (loopState s3 { l1 with ret := 0 }) = [] := by
                  simp [lensPrefix, loopState, s3]
                rw [e]
                exact ZlibF.Math.CodeLengthPrefix.Trace.refl _ _ _,
              fun allZero => ⟨emptyFacts allZero, fun k inside =>
                absurd inside (by show ¬ k < (0 : UInt32).toNat; simp)⟩,
              Or.inl bitsSmall⟩⟩, last⟩
        (window1 s3 _ rfl rfl rfl rfl) check wrapM outputEq
      refine ⟨{ l1 with ret := 0 }, setI h zs s3, ?_, by show loopRead l ≤ loopRead l1; omega, ?_, moved⟩
      · rw [runTail, runC, setI_setI]
      · intro zs' s' st' hs'
        rw [setI_state s3 st zs' s' st' hs']
    · -- the code-length code is not acceptable
      left
      obtain ⟨ret, wa', ca', _, _, _, _, _, rejection, _, badRun⟩ :=
        llTail_run_code_length_meaning (l := l1) strm st hz2 hs2 wf2 good2
      have listEq : Zlib.Inftrees.Spec.lensList st2.lens 0 19 = cl := lensList_zero st2.lens 19
      rw [listEq] at rejection
      obtain ⟨i, _, runBad⟩ := badRun (rejection.mpr accepted)
      refine ⟨.ok (), { l1 with ret := -1 }, _, runTail.trans runBad,
        Or.inr ⟨rfl, by show loopRead l ≤ loopRead l1; omega, bad_heap_mode st, ?_⟩⟩
      apply doomed_of_aligned (rest := natBits l1.bits.toNat l1.hold.toNat) wrapHeader parsed1
      · show bytesToBits (f.logIn ++ f.inp.take (loopRead l1)) = _
        rw [bits1, consumed1]
      · intro more tail outF _ resid
        obtain ⟨_, _, body, _⟩ := resid
        cases body with
        | dynamic q1 q2 q3 _ q5 q6 =>
          obtain ⟨a1, a2, a3⟩ := counts_append (more := natBits l1.bits.toNat l1.hold.toNat ++ more)
            read1' read2' read3'
          rw [a1] at q1
          simp only [Option.some.injEq, Prod.mk.injEq] at q1
          obtain ⟨rfl, rfl⟩ := q1
          rw [a2] at q2
          simp only [Option.some.injEq, Prod.mk.injEq] at q2
          obtain ⟨rfl, rfl⟩ := q2
          rw [a3] at q3
          simp only [Option.some.injEq, Prod.mk.injEq] at q3
          obtain ⟨rfl, rfl⟩ := q3
          rw [ZlibF.Spec.Proofs.readCodeLenLens_append _ _ _ _ _ readCL] at q5
          simp only [Option.some.injEq, Prod.mk.injEq] at q5
          obtain ⟨rfl, _⟩ := q5
          exact accepted q6
  · -- waiting for input
    left
    have lt : count < s.ncode.toNat - s.«have».toNat := by omega
    obtain ⟨rleave, wait, _, small3⟩ := leaveF lt
    subst rleave
    have runL : runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, l1), setI h zs st1) := by
      rw [inflate_LENLENS_eq, runX_bind, runLL]
    have moved := loop_move (s' := st1) (l' := l1) (j := j)
      (pos := ⟨out, final, .dynamicHeader (hdr ++ vb)⟩) st retOk
      config
      haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep1
      used next1 binvL bits1
      (HeldBits.of_natBits (s := loopState st1 l1) binvL.hold_lt) wrapHeader
      consumed1 parsed1
      ⟨Or.inr ⟨hlit, hdist, hclen, r1 ++ vb, r2 ++ vb, r3 ++ vb, read1', read2', read3', counts,
          nlenEq, ndistEq, ncodeEq,
          Or.inl ⟨mode, by show st1.«have».toNat < _; omega, by show l1.bits.toNat < 11; omega,
            vs ++ values, readVs', lensVs'⟩⟩, last⟩
      (window1 st1 _ rfl rfl rfl rfl) check wrapM outputEq
    exact ⟨_, _, _, runL, Or.inl ⟨rfl, wait, moved⟩⟩

#print axioms lenlens_step

end Zlib.Inflate.Proofs.MeaningDynamicSteps
