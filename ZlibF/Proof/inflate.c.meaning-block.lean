import ZlibF.Proof.«inflate.c.meaning-copy»
import ZlibF.Proof.«inflate.c.meaning-bits»
import ZlibF.Proof.«inflate.c.meaning-stuck»
import ZlibF.Proof.«inflate.c.meaning-fixed-tables»
import ZlibF.Proof.«inflate.c.main.type»
import ZlibF.Proof.«inflate.c.main.stored2»
import ZlibF.Proof.«infback.c.pure»

/-!
# inflate.c: `TYPE`, `TYPEDO` and `STORED` keep the format meaning

`case TYPEDO` at a block boundary waits for three bits, stores the last-block
flag and dispatches on the block type: a stored block goes to `STORED`
(`DeflateParsed.storedStart`), a fixed block installs the static tables and
goes to `LEN_` (`DeflateParsed.fixedHeader`), a dynamic block goes to `TABLE`
(`DeflateParsed.dynamicStart`), and type 3 goes to `BAD`: no block of the
format has type 3, so no continuation of the input is valid. `case TYPE`
leaves for `Z_BLOCK` and `Z_TREES` and otherwise runs `case TYPEDO`.

`case STORED` drops the padding to the byte boundary (`DeflateParsed.storedPad`),
waits for `LEN` and `NLEN`, and checks the complement. A mismatch dooms the
input (`Body.stored` needs `NLEN = 65535 - LEN`). Otherwise the bit buffer is
emptied and the parse reaches the stored bytes (`DeflateParsed.storedLength`);
`case COPY_` follows unless the flush is `Z_TREES`.

The check reads the low 32 held bits and requires the bits above them to be
zero, so it needs fewer than 32 held bits on entry. `BodyMatches` at
`.storedHeader` records that bound (P11): `TYPEDO` leaves fewer than 8 bits,
and `STORED` leaves fewer than 32 when it waits for `LEN` and `NLEN`. Without
it the step is false: with 45 held bits that hold a valid `LEN`, `NLEN` and a
nonzero next byte the check fails on a valid stream.
-/

namespace Zlib.Inflate.Proofs.MeaningBlock
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
set_option autoImplicit false

/-! ## Registers and held bits -/

theorem setI_self {h : Heap} {zs : Nat} {s : InflateState} (hs : h.istates zs = some s) :
    setI h zs s = h := by
  simp [setI, upd_self _ _ _ hs]

/-- The registers a mode keeps when it only reads input and changes the bit buffer. -/
def RegsKeep (l l' : IL) : Prop :=
  l'.in_ = l.in_ ∧ l'.out_ = l.out_ ∧ l'.left = l.left ∧ l'.put = l.put ∧ l'.ret = l.ret

theorem RegsKeep.of_shape {l l' : IL}
    (shape : l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits }) :
    RegsKeep l l' := by
  rw [shape]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem RegsKeep.trans {a b c : IL} (ab : RegsKeep a b) (bc : RegsKeep b c) : RegsKeep a c :=
  ⟨bc.1.trans ab.1, bc.2.1.trans ab.2.1, bc.2.2.1.trans ab.2.2.1, bc.2.2.2.1.trans ab.2.2.2.1,
    bc.2.2.2.2.trans ab.2.2.2.2⟩

/-- Bytes pulled by `NEEDBITS` join the held bits. -/
theorem bits_pull {f : LoopFrame} {l l1 : IL} {j : Nat} {consumed : List Bool}
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) =
      consumed ++ natBits l.bits.toNat l.hold.toNat)
    (readEq : loopRead l1 = loopRead l + j)
    (streamEq : stream l1 ((f.inp.drop (loopRead l)).drop j) = stream l (f.inp.drop (loopRead l))) :
    bytesToBits (f.logIn ++ f.inp.take (loopRead l1)) =
      consumed ++ natBits l1.bits.toNat l1.hold.toNat := by
  have split : bytesBits (f.inp.drop (loopRead l)) =
      bytesBits ((f.inp.drop (loopRead l)).take j) ++ bytesBits ((f.inp.drop (loopRead l)).drop j) := by
    rw [← bytesBits_append, List.take_append_drop]
  simp only [stream] at streamEq
  rw [split, ← List.append_assoc] at streamEq
  have pulled := List.append_cancel_right streamEq
  have takeSplit : f.inp.take (loopRead l + j) =
      f.inp.take (loopRead l) ++ (f.inp.drop (loopRead l)).take j := List.take_add ..
  rw [readEq, takeSplit, ← List.append_assoc, bytesToBits_append', bitsEq, pulled,
    bytesBits_eq_bytesToBits]
  simp only [List.append_assoc]

/-- Bits dropped by `DROPBITS` or `BYTEBITS` leave the held bits. -/
theorem held_drop {l l' : IL} {bs : List UInt8} {k : Nat}
    (streamEq : stream l' bs = (stream l bs).drop k) (le : k ≤ l.bits.toNat) :
    natBits l'.bits.toNat l'.hold.toNat = (natBits l.bits.toNat l.hold.toNat).drop k := by
  simp only [stream] at streamEq
  rw [List.drop_append_of_le_length (by rw [natBits_length]; exact le)] at streamEq
  exact List.append_cancel_right streamEq

theorem natBits_three (v : Nat) :
    natBits 3 v = [v % 2 == 1, v / 2 % 2 == 1, v / 2 / 2 % 2 == 1] := rfl

theorem natToBitsLSB_eq (n v : Nat) : natToBitsLSB n v = natBits n v := by
  rw [natToBitsLSB_eq_bitsOfNat, natBits_testBit]
  rfl

theorem readBits_natBits : ∀ (k v : Nat) (r : List Bool),
    readBits k (natBits k v ++ r) = some (v % 2 ^ k, r)
  | 0, v, r => by simp [readBits, natBits, Nat.mod_one]
  | k + 1, v, r => by
    simp only [natBits, List.cons_append, readBits, readBits_natBits k (v / 2) r]
    congr 2
    have split : v % (2 * 2 ^ k) = v % 2 + 2 * (v / 2 % 2 ^ k) := Nat.mod_mul
    have bit : (v % 2 == 1) = true ↔ v % 2 = 1 := by simp
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, split]
    by_cases odd : v % 2 = 1
    · rw [if_pos (bit.mpr odd)]
      omega
    · rw [if_neg (by simpa [bit] using odd)]
      omega

/-- The registers after the three header bits of a block are dropped. -/
def typedoRegs (l : IL) : IL :=
  { ({ l with hold := l.hold >>> 1, bits := l.bits - 1 } : IL) with
    hold := ({ l with hold := l.hold >>> 1, bits := l.bits - 1 } : IL).hold >>> 2,
    bits := ({ l with hold := l.hold >>> 1, bits := l.bits - 1 } : IL).bits - 2 }

theorem typedoRegs_facts {h : Heap} {l : IL} {bs : List UInt8} (inv : BitInv h l bs)
    (three : 3 ≤ l.bits.toNat) :
    BitInv h (typedoRegs l) bs ∧ (typedoRegs l).bits.toNat = l.bits.toNat - 3 ∧
      natBits l.bits.toNat l.hold.toNat =
        natBits 3 l.hold.toNat ++ natBits (typedoRegs l).bits.toNat (typedoRegs l).hold.toNat ∧
      RegsKeep l (typedoRegs l) ∧ (typedoRegs l).next = l.next ∧ (typedoRegs l).have_ = l.have_ := by
  have d1 := DROPBITS_inv inv 1 (by show 1 ≤ l.bits.toNat; omega) (by decide)
  have e1 := held_drop d1.2.1 (by show 1 ≤ l.bits.toNat; omega)
  change natBits (l.bits - 1).toNat (l.hold >>> 1).toNat =
    (natBits l.bits.toNat l.hold.toNat).drop 1 at e1
  have c1 : (l.bits - 1).toNat = l.bits.toNat - 1 := by
    have := congrArg List.length e1
    rw [natBits_length, List.length_drop, natBits_length] at this
    exact this
  have d2 := DROPBITS_inv d1.1 2 (by show 2 ≤ (l.bits - 1).toNat; omega) (by decide)
  have e2 := held_drop d2.2.1 (by show 2 ≤ (l.bits - 1).toNat; omega)
  change natBits (typedoRegs l).bits.toNat (typedoRegs l).hold.toNat =
    (natBits (l.bits - 1).toNat (l.hold >>> 1).toNat).drop 2 at e2
  have e3 : natBits (typedoRegs l).bits.toNat (typedoRegs l).hold.toNat =
      (natBits l.bits.toNat l.hold.toNat).drop 3 := by
    rw [e2, e1]
    simp
  have c3 : (typedoRegs l).bits.toNat = l.bits.toNat - 3 := by
    have := congrArg List.length e3
    rw [natBits_length, List.length_drop, natBits_length] at this
    exact this
  refine ⟨d2.1, c3, ?_, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  rw [e3, ← natBits_take l.bits.toNat l.hold.toNat 3 three, List.take_append_drop]

/-- The last-block flag `BITS(1)` as `TYPEDO` stores it. -/
theorem last_value (l : IL) :
    u2i (l.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) =
      (if (l.hold.toNat % 2 == 1) then 1 else 0) := by
  have v : (l.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)).toNat = l.hold.toNat % 2 :=
    (BITS_toNat l 1 (by decide)).trans (by rfl)
  unfold u2i
  rw [v]
  rcases Nat.mod_two_eq_zero_or_one l.hold.toNat with e | e <;> rw [e] <;> decide

/-! ## Rebuilding the loop meaning after the bit buffer moves -/

/-- The loop meaning for new registers that only read input and change the
bit buffer, a new state with the same window, and a new parse position with
the same output. -/
theorem loop_move {c : Ctx} {f : LoopFrame} {h : Heap} {l l' : IL} {zs : Nat} {s' : InflateState}
    {callOut : List UInt8} {consumed held : List Bool} {header bodyDict : List UInt8}
    {bitsP : List Bool} {pos : DeflatePos} {j : Nat}
    (st : c.st = some (.tab zs)) (retOk : l.ret = Z_OK)
    (config : ConfigMatches (loopState s' l') f.wrap f.configured)
    (haveLe : l.have_.toNat ≤ l.in_.toNat) (inLen : l.in_.toNat = f.inp.length)
    (leftLe : l.left.toNat ≤ l.out_.toNat) (pendBase : loopPending l = callOut.length)
    (putEq : l.put = inputAdvance f.start callOut.length)
    (outBytes : Bytes h f.start callOut.length callOut)
    (writable : Writable h l.put l.left.toNat)
    (sepIn : Separate l.put l.left.toNat l.next l.have_.toNat)
    (sepWin : Separate l.put l.left.toNat s'.window s'.wsize.toNat)
    (sepOutIn : Separate f.start callOut.length l.next l.have_.toNat)
    (keep : RegsKeep l l') (used : l'.have_.toNat + j = l.have_.toNat)
    (nextEq : l'.next = inputAdvance l.next j)
    (binv : BitInv h l' (f.inp.drop (loopRead l')))
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l')) = consumed ++ held)
    (heldBits : HeldBits (loopState s' l') held)
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (consumedEq : consumed = bytesToBits header ++ bitsP)
    (parsed : DeflateParsed bodyDict bitsP pos)
    (body : BodyMatches (setI h zs s') (loopState s' l') pos)
    (window : WindowMeaning (setI h zs s') (loopState s' l') f.dict f.logOut)
    (check : CheckMeaning (loopState s' l') f.wrap header
      ((f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l)))
    (wrapM : FlagsMatch (loopState s' l') f.wrap header ∧
      HeaderWidth (loopState s' l') f.configured header)
    (outEq : pos.out = f.logOut ++ callOut) :
    LoopMatches c f (setI h zs s') l' := by
  obtain ⟨inEq, outEq', leftEq, putEq', retEq⟩ := keep
  have pendEq : loopPending l' = loopPending l := by simp only [loopPending, outEq', leftEq]
  refine ⟨zs, s', callOut, consumed, held, .body header pos, st, setI_istates_same _ _ _,
    retEq.trans retOk, config, by rw [inEq]; omega, by rw [inEq]; exact inLen, bitInv_setI binv,
    by rw [leftEq, outEq']; exact leftLe,
    ⟨by rw [pendEq]; omega, fun _ _ _ => by rw [pendEq]; exact pendBase⟩,
    by rw [putEq']; exact putEq, bytes_setI outBytes, ?_, ?_, by rw [putEq', leftEq]; exact sepWin,
    ?_, bitsEq, heldBits, ⟨bodyDict, bitsP, wrapHeader, consumedEq, parsed⟩, ⟨body, window, ?_⟩,
    wrapM, outEq⟩
  · rw [putEq', leftEq]
    rcases writable with null | ⟨r, i, a, ptr, get, ro, fits⟩
    · exact Or.inl null
    · exact Or.inr ⟨r, i, a, ptr, by rw [byte_view_get_setI]; exact get,
        by rw [byte_view_ro_setI]; exact ro, fits⟩
  · rw [putEq', leftEq, nextEq]
    have sep := separate_advance (j := j) sepIn (by omega)
    rwa [show l.have_.toNat - j = l'.have_.toNat by omega] at sep
  · rw [nextEq]
    have sep := separate_advance (j := j) sepOutIn (by omega)
    rwa [show l.have_.toNat - j = l'.have_.toNat by omega] at sep
  · rw [pendEq]
    exact check

/-! ## Stages and parses -/

/-- The only stage a `TYPE` or `TYPEDO` state before the final block can stand for. -/
theorem stage_of_boundary {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last = 0) :
    ∃ header out, stage = .body header ⟨out, false, .boundary⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rcases mode with m | m <;> rw [m] at lo hi <;> exact absurd hi (by decide)
  · have this := stageFacts
    simp only [LoopStageMatches] at this
    rcases mode with m | m <;> rw [m] at this <;> exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨_, fin, _, _⟩ := body
      subst fin
      exact ⟨header, out, rfl⟩
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m' | m' | m' <;> rcases mode with m | m <;>
        (rw [m] at m'; exact absurd m' (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
    · obtain ⟨_, _, one, _⟩ := body
      rw [last] at one
      exact absurd one (by decide)
  · obtain ⟨m', _⟩ := stageFacts
    rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
  · have m' : s.mode = DONE := stageFacts
    rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)

/-- The only stage a `STORED` state can stand for. -/
theorem stage_of_stored {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage)
    (mode : s.mode = STORED) :
    ∃ header out final, stage = .body header ⟨out, final, .storedHeader⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [mode] at lo hi
    exact absurd hi (by decide)
  · have this := stageFacts
    simp only [LoopStageMatches] at this
    rw [mode] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m', _⟩ := body
      rw [mode] at m'
      exact absurd m' (by decide)
    · exact ⟨header, out, final, rfl⟩
    · obtain ⟨m', _⟩ := body
      rw [mode] at m'
      exact absurd m' (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m' | m' | m' <;> (rw [mode] at m'; exact absurd m' (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
    · obtain ⟨m', _⟩ := body
      rw [mode] at m'
      exact absurd m' (by decide)
  · obtain ⟨m', _⟩ := stageFacts
    rw [mode] at m'
    exact absurd m' (by decide)
  · have m' : s.mode = DONE := stageFacts
    rw [mode] at m'
    exact absurd m' (by decide)

/-- No block of the format has type 3. -/
theorem body_three {dict h : List UInt8} {inp rest : List Bool} {out : List UInt8} :
    ¬ Body dict 3 h inp rest out := by
  intro b
  generalize e : (3 : Nat) = n at b
  cases b <;> exact absurd e (by decide)

/-- A position whose continuation, read on byte-aligned input, has no parse
dooms the input read so far. Like `LoopDoomed.of_stuck`, but the rest only
needs to fail on aligned continuations, as every source is. -/
theorem doomed_of_aligned {f : LoopFrame} {l : IL} {header bodyDict : List UInt8}
    {dbits rest : List Bool} {pos : DeflatePos}
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (dparsed : DeflateParsed bodyDict dbits pos)
    (bits : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = bytesToBits header ++ dbits ++ rest)
    (never : ∀ more tail outF, (dbits ++ (rest ++ more)).length % 8 = 0 →
      ¬ Resid bodyDict pos (rest ++ more) tail outF) :
    LoopDoomed f l := by
  intro source decoded valid _ started
  obtain ⟨more, tail, aligned, sourceBits, blocks, _⟩ :=
    body_on_source wrapHeader valid started bits
  have whole := bytesToBits_prefix_iff.mpr started
  rw [bits, sourceBits] at whole
  have inner : rest <+: more := by
    have := (List.prefix_append_right_inj (bytesToBits header)).mp
      (by simpa only [List.append_assoc] using whole)
    exact (List.prefix_append_right_inj dbits).mp this
  obtain ⟨more', rfl⟩ := inner
  exact never more' tail decoded (by simpa only [List.append_assoc] using aligned)
    (deflateParsed_resid dparsed (rest ++ more') tail decoded
      (by simpa only [List.append_assoc] using aligned)
      (by simpa only [List.append_assoc] using blocks))

/-- The static tables installed by `inflate_fixed` decode the fixed codes. -/
theorem fixed_tables {h : Heap} (globals : LibraryGlobals h) (zs : Nat) (s : InflateState) :
    TableMeaning (setI h zs s) (.ref .st_lenfix 0) 9 LENS fixedLitLens ∧
      TableMeaning (setI h zs s) (.ref .st_distfix 0) 5 DISTS fixedDistLens := by
  refine ⟨⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, 512, rfl, ?_, MeaningFixed.lenfix_inv,
      MeaningFixed.lenfix_stable⟩,
    ⟨.st_distfix, 0, Zlib.InffixedH.distfix, 32, rfl, ?_, MeaningFixed.distfix_inv,
      MeaningFixed.distfix_stable⟩⟩
  · change some h.static.lenfix = some Zlib.InffixedH.lenfix
    rw [globals]
    rfl
  · change some h.static.distfix = some Zlib.InffixedH.distfix
    rw [globals]
    rfl

/-! ## `TYPEDO` and `TYPE` -/

set_option maxHeartbeats 4000000 in
/-- `case TYPEDO` before the final block keeps the format meaning. Without
three bits it leaves with all input read (`have = 0`) and the boundary held.
Otherwise it reads the block header: a stored block goes to `STORED`, a fixed
block installs the static tables and goes to `LEN_` (leaving at once for
`Z_TREES`), a dynamic block goes to `TABLE`, and type 3 goes to `BAD` with no
valid continuation of the input. The static tables are those of the library
(`LibraryGlobals`). The case `last ≠ 0` (to `CHECK`) is the stream side's. -/
theorem typedo_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (globals : LibraryGlobals h)
    (boundary : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) :
    ∃ result l' h', runX (inflate_TYPEDO c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ c.flush = Z_TREES) ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  obtain ⟨mode, last⟩ := boundary zs s st hs
  obtain ⟨header, out, rfl⟩ := stage_of_boundary stageM mode last
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨_, _, _, bitsLt⟩, window, check⟩ := stageM
  have bitsLt' : l.bits.toNat < 8 := bitsLt
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  obtain ⟨result, l1, j, run, jle, binv1, streamEq, _, shape, bitsBound, _, enough, empty,
    kinds, nextEq⟩ := NEEDBITS_run_cursor binv 3 (by decide)
  have haveOld := binv.have_eq
  have haveNew := binv1.have_eq
  simp only [List.length_drop, loopRead] at haveOld haveNew jle
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
  · -- the three header bits are there
    have three : 3 ≤ l1.bits.toNat := enough rfl
    have bound : l1.bits.toNat ≤ 10 := by
      change l1.bits.toNat ≤ max l.bits.toNat 10 at bitsBound
      omega
    obtain ⟨binv2, count2, split2, keep2, next2, have2⟩ := typedoRegs_facts binv1 three
    have keep : RegsKeep l (typedoRegs l1) := keep1.trans keep2
    have read2 : loopRead (typedoRegs l1) = loopRead l + j := readEq
    have binvN : BitInv h (typedoRegs l1) (f.inp.drop (loopRead (typedoRegs l1))) := by
      rw [read2, ← List.drop_drop]
      exact binv2
    have usedN : (typedoRegs l1).have_.toNat + j = l.have_.toNat := by rw [have2]; exact used
    have nextN : (typedoRegs l1).next = inputAdvance l.next j := by rw [next2]; exact nextEq
    have bitsAll : bytesToBits (f.logIn ++ f.inp.take (loopRead (typedoRegs l1))) =
        (consumed ++ natBits 3 l1.hold.toNat) ++
          natBits (typedoRegs l1).bits.toNat (typedoRegs l1).hold.toNat := by
      rw [read2, ← readEq, bits1, split2, List.append_assoc]
    have bitsN : (typedoRegs l1).bits.toNat < 8 := by omega
    have lastEq := last_value l1
    have half : (l1.hold >>> 1).toNat = l1.hold.toNat / 2 :=
      (shr64_toNat l1.hold 1 (by decide)).trans (by rfl)
    have E1 : Env c (setI h zs { s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) })
        r zs z { s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) } :=
      ⟨strm, st, by simpa using hz, by simp⟩
    have runHead := inflate_TYPEDO_head E l l1 last run
    have window' := fun (s' : InflateState) (wnd : s'.window = s.window) (ws : s'.wsize = s.wsize)
        (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
      window_transfer (s := loopState s l) (s' := loopState s' (typedoRegs l1)) wnd ws wn wh
        (fun q => byte_view_get_setI h zs s' q) window
    have typeCases : l1.hold.toNat / 2 % 4 = 0 ∨ l1.hold.toNat / 2 % 4 = 1 ∨
        l1.hold.toNat / 2 % 4 = 2 ∨ l1.hold.toNat / 2 % 4 = 3 := by omega
    rcases typeCases with t | t | t | t
    · -- stored
      have hv : ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL).hold.toNat % 4 = 0 := by
        show (l1.hold >>> 1).toNat % 4 = 0
        rw [half]
        exact t
      have e1 : (l1.hold.toNat / 2 % 2 == 1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      have e2 : (l1.hold.toNat / 2 / 2 % 2 == 1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      have run2 := runHead.trans (typedoTail_stored E1 ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL) hv)
      rw [setI_setI] at run2
      refine ⟨.ok (), typedoRegs l1, _, run2, Or.inr ⟨rfl, by rw [read2]; omega, Or.inl ?_⟩⟩
      rw [natBits_three, e1, e2] at bitsAll
      exact loop_move (s' := { ({ s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) } : InflateState) with mode := STORED })
        (l' := typedoRegs l1) (pos := ⟨out, l1.hold.toNat % 2 == 1, .storedHeader⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show STORED ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep usedN nextN
        binvN bitsAll (HeldBits.of_natBits binv2.hold_lt) wrapHeader
        (by rw [consumedEq, List.append_assoc])
        (DeflateParsed.storedStart (final := l1.hold.toNat % 2 == 1) deflate)
        ⟨rfl, lastEq, show (typedoRegs l1).bits.toNat < 32 by omega⟩
        (window' _ rfl rfl rfl rfl) check wrapM outputEq
    · -- fixed
      have hv : ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL).hold.toNat % 4 = 1 := by
        show (l1.hold >>> 1).toNat % 4 = 1
        rw [half]
        exact t
      have e1 : (l1.hold.toNat / 2 % 2 == 1) = true := by
        simp only [beq_iff_eq]; omega
      have e2 : (l1.hold.toNat / 2 / 2 % 2 == 1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      rw [natBits_three, e1, e2] at bitsAll
      obtain ⟨lenT, distT⟩ := fixed_tables globals zs
        { fixedState { s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) } with
          mode := LEN_ }
      have moved := loop_move
        (s' := { fixedState ({ s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) } : InflateState) with mode := LEN_ })
        (l' := typedoRegs l1)
        (pos := ⟨out, l1.hold.toNat % 2 == 1, .codes fixedLitLens fixedDistLens .none⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show LEN_ ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep usedN nextN
        binvN bitsAll (HeldBits.of_natBits binv2.hold_lt) wrapHeader
        (by rw [consumedEq, List.append_assoc])
        (DeflateParsed.fixedHeader (final := l1.hold.toNat % 2 == 1) deflate)
        ⟨lastEq, lenT, distT, Or.inl rfl, Or.inl bitsN⟩
        (window' _ rfl rfl rfl rfl) check wrapM outputEq
      by_cases trees : c.flush = Z_TREES
      · have run2 := runHead.trans (typedoTail_fixed_trees E1 ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL) hv trees)
        rw [setI_setI] at run2
        exact ⟨.error Ex.leave, typedoRegs l1, _, run2, Or.inl ⟨rfl, Or.inr trees, moved⟩⟩
      · have run2 := runHead.trans (typedoTail_fixed E1 ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL) hv trees)
        rw [setI_setI] at run2
        exact ⟨.ok (), typedoRegs l1, _, run2, Or.inr ⟨rfl, by rw [read2]; omega, Or.inl moved⟩⟩
    · -- dynamic
      have hv : ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL).hold.toNat % 4 = 2 := by
        show (l1.hold >>> 1).toNat % 4 = 2
        rw [half]
        exact t
      have e1 : (l1.hold.toNat / 2 % 2 == 1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      have e2 : (l1.hold.toNat / 2 / 2 % 2 == 1) = true := by
        simp only [beq_iff_eq]; omega
      have run2 := runHead.trans (typedoTail_table E1 ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL) hv)
      rw [setI_setI] at run2
      refine ⟨.ok (), typedoRegs l1, _, run2, Or.inr ⟨rfl, by rw [read2]; omega, Or.inl ?_⟩⟩
      rw [natBits_three, e1, e2] at bitsAll
      exact loop_move (s' := { ({ s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) } : InflateState) with mode := TABLE })
        (l' := typedoRegs l1) (pos := ⟨out, l1.hold.toNat % 2 == 1, .dynamicHeader []⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show TABLE ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep usedN nextN
        binvN bitsAll (HeldBits.of_natBits binv2.hold_lt) wrapHeader
        (by rw [consumedEq, List.append_assoc])
        (DeflateParsed.dynamicStart (final := l1.hold.toNat % 2 == 1) deflate)
        ⟨Or.inl ⟨rfl, rfl, show (typedoRegs l1).bits.toNat < 22 by omega⟩, lastEq⟩
        (window' _ rfl rfl rfl rfl) check wrapM outputEq
    · -- type 3
      have hv : ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL).hold.toNat % 4 = 3 := by
        show (l1.hold >>> 1).toNat % 4 = 3
        rw [half]
        exact t
      have e1 : (l1.hold.toNat / 2 % 2 == 1) = true := by
        simp only [beq_iff_eq]; omega
      have e2 : (l1.hold.toNat / 2 / 2 % 2 == 1) = true := by
        simp only [beq_iff_eq]; omega
      obtain ⟨i, _, runBad⟩ := typedoTail_bad E1 ({ l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 } : IL) hv
      refine ⟨.ok (), typedoRegs l1, _, runHead.trans runBad,
        Or.inr ⟨rfl, by rw [read2]; omega, Or.inr ⟨?_, ?_⟩⟩⟩
      · intro zs' s' st' hs'
        rw [st] at st'
        cases st'
        simp only [badHeap, setI_istates_same, Option.some.injEq] at hs'
        rw [← hs']
      · apply LoopDoomed.of_stuck
        refine ⟨consumed, natBits l1.bits.toNat l1.hold.toNat, header, ⟨out, false, .boundary⟩,
          bits1, ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩, ?_⟩
        intro _ _ bd _ more tail outF resid
        change Blocks bd out (natBits l1.bits.toNat l1.hold.toNat ++ more) tail outF at resid
        rw [split2, natBits_three, e1, e2] at resid
        obtain ⟨_, _, body, _⟩ := blocks_header (dict := bd) (out := out)
          (b0 := l1.hold.toNat % 2 == 1) (b1 := true) (b2 := true)
          (more := natBits (typedoRegs l1).bits.toNat (typedoRegs l1).hold.toNat ++ more)
          (tail := tail) (outF := outF)
          (by simpa only [List.cons_append, List.nil_append, List.append_assoc] using resid)
        exact body_three body
  · -- not enough input
    have wait := empty rfl
    have small : l1.bits.toNat < 8 := by
      have := wait.2.2
      change l1.bits.toNat < 3 at this
      omega
    have moved := loop_move (s' := s) (l' := l1) (pos := ⟨out, false, .boundary⟩) st retOk config haveLe inLen
      leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep1 used nextEq binvL bits1
      (HeldBits.of_natBits (s := loopState s l1) binv1.hold_lt) wrapHeader consumedEq deflate
      ⟨mode, rfl, last, small⟩
      (window_transfer (s := loopState s l) (s' := loopState s l1) rfl rfl rfl rfl
        (fun q => byte_view_get_setI h zs s q) window) check wrapM
      outputEq
    rw [setI_self hs] at moved
    exact ⟨_, _, _, inflate_TYPEDO_wait E l l1 last _ run, Or.inl ⟨rfl, Or.inl wait.2.1, moved⟩⟩

#print axioms typedo_step

/-- `case TYPE` keeps the format meaning: with `flush` `Z_BLOCK` or `Z_TREES`
it leaves with nothing changed; otherwise it is `case TYPEDO` (`typedo_step`). -/
theorem type_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (globals : LibraryGlobals h)
    (boundary : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) :
    ∃ result l' h', runX (inflate_TYPE c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ c.flush = Z_BLOCK ∨ c.flush = Z_TREES) ∧
          LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
  · exact ⟨_, _, _, inflate_TYPE_leave c l h flush, Or.inl ⟨rfl, Or.inr flush, loop⟩⟩
  · have go : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
      ⟨fun e => flush (Or.inl e), fun e => flush (Or.inr e)⟩
    obtain ⟨result, l', h', run, rest⟩ := typedo_step loop strm hz globals boundary
    refine ⟨result, l', h', (inflate_TYPE_go c l h go).trans run, ?_⟩
    rcases rest with ⟨leave, cause, m⟩ | other
    · exact Or.inl ⟨leave, cause.imp_right (fun e => Or.inr e), m⟩
    · exact Or.inr other

#print axioms type_step

/-! ## `STORED` -/

set_option maxHeartbeats 4000000 in
/-- `case STORED` keeps the format meaning. It drops the padding to the byte
boundary; without 32 bits it leaves with all input read (`have = 0`) and the
parse after the padding. A length whose complement does not match goes to
`BAD` with no valid continuation of the input. Otherwise the bit buffer is
emptied, the parse reaches the stored bytes, and `case COPY_` follows
(`copy_start_step`), or the call leaves for `Z_TREES`.

`heldBound` (fewer than 32 held bits) is the `.storedHeader` bound of
`BodyMatches` (P11); `stored_step` takes it from there. The other facts are
the stream record and the window bounds, as for `COPY`. -/
theorem stored_step_bounded {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (storedMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = STORED)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (heldBound : l.bits.toNat < 32) :
    ∃ result l' h', runX (inflate_STORED c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ c.flush = Z_TREES ∨ l.left = 0) ∧
          LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = STORED := storedMode zs s st hs
  obtain ⟨header, out, final, rfl⟩ := stage_of_stored stageM mode
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨_, last, _⟩, window, check⟩ := stageM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  -- the padding
  obtain ⟨binv0, stream0, mod0⟩ := BYTEBITS_inv binv
  have held0 := held_drop stream0 (Nat.mod_le _ _)
  have bits0 : (bytebits l).bits.toNat = l.bits.toNat - l.bits.toNat % 8 := by
    have := congrArg List.length held0
    rw [natBits_length, List.length_drop, natBits_length] at this
    exact this
  have total := congrArg List.length bitsEq
  simp only [bytesToBits_length', consumedEq, List.length_append, natBits_length] at total
  have padLen : l.bits.toNat % 8 = (8 - bitsP.length % 8) % 8 := by omega
  have parsed0 := DeflateParsed.storedPad
    (pad := (natBits l.bits.toNat l.hold.toNat).take (l.bits.toNat % 8)) deflate
    (by rw [List.length_take, natBits_length]; omega)
  have bitsEq0 : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) =
      (consumed ++ (natBits l.bits.toNat l.hold.toNat).take (l.bits.toNat % 8)) ++
        natBits (bytebits l).bits.toNat (bytebits l).hold.toNat := by
    rw [held0, List.append_assoc, List.take_append_drop]
    exact bitsEq
  have consumed0 : consumed ++ (natBits l.bits.toNat l.hold.toNat).take (l.bits.toNat % 8) =
      bytesToBits header ++ (bitsP ++ (natBits l.bits.toNat l.hold.toNat).take (l.bits.toNat % 8)) := by
    rw [consumedEq, List.append_assoc]
  -- the length fields
  obtain ⟨result, l1, j, run, jle, binv1, streamEq, bitsCount, shape, bitsBound, _, enough, empty,
    kinds, nextEq⟩ := NEEDBITS_run_cursor binv0 32 (by decide)
  have haveOld := binv.have_eq
  have haveNew := binv1.have_eq
  simp only [List.length_drop, loopRead] at haveOld haveNew jle
  have keep1 : RegsKeep l l1 :=
    (show RegsKeep l (bytebits l) from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans (RegsKeep.of_shape shape)
  have readEq : loopRead l1 = loopRead l + j := by
    simp only [loopRead, keep1.1]
    omega
  have used : l1.have_.toNat + j = l.have_.toNat := by omega
  have bits1 := bits_pull (l := bytebits l) bitsEq0 readEq streamEq
  have binvL : BitInv h l1 (f.inp.drop (loopRead l1)) := by
    rw [readEq, ← List.drop_drop]
    exact binv1
  have window' := fun (s' : InflateState) (l' : IL) (wnd : s'.window = s.window)
      (ws : s'.wsize = s.wsize) (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
    window_transfer (s := loopState s l) (s' := loopState s' l') wnd ws wn wh
      (fun q => byte_view_get_setI h zs s' q) window
  rcases kinds with rfl | rfl
  · -- `LEN` and `NLEN` are held
    have b32 : 32 ≤ l1.bits.toNat := enough rfl
    have bound : l1.bits.toNat ≤ max (bytebits l).bits.toNat 39 := bitsBound
    have exact32 : l1.bits.toNat = 32 := by omega
    have holdLt : l1.hold.toNat < 2 ^ 32 := by
      have := binv1.hold_lt
      rw [exact32] at this
      exact this
    have split32 : natBits 32 l1.hold.toNat =
        natBits 16 l1.hold.toNat ++ natBits 16 (l1.hold.toNat / 2 ^ 16) := natBits_add 16 16 _
    have p16 : (2 : Nat) ^ 16 = 65536 := rfl
    have holdLt' : l1.hold.toNat < 4294967296 := holdLt
    by_cases cond : ((l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · -- the complement does not match
      obtain ⟨i, _, runBad⟩ := inflate_STORED_bad E l l1 run cond
      refine ⟨.ok (), l1, _, runBad, Or.inr ⟨rfl, by rw [readEq]; omega, Or.inr ⟨?_, ?_⟩⟩⟩
      · intro zs' s' st' hs'
        rw [st] at st'
        cases st'
        simp only [badHeap, setI_istates_same, Option.some.injEq] at hs'
        rw [← hs']
      · apply doomed_of_aligned (rest := natBits l1.bits.toNat l1.hold.toNat) wrapHeader parsed0
        · rw [bits1, consumed0]
        · intro more tail outF aligned resid
          obtain ⟨_, _, body, _⟩ := resid
          cases body with
          | stored one two comp _ =>
            have al : (natBits l1.bits.toNat l1.hold.toNat ++ more).length % 8 = 0 := by
              simp only [List.length_append, List.length_take, natBits_length] at aligned ⊢
              omega
            rw [al, List.drop_zero, exact32, split32, List.append_assoc, readBits_natBits] at one
            simp only [Option.some.injEq, Prod.mk.injEq] at one
            obtain ⟨lenEq, restEq⟩ := one
            rw [← restEq, readBits_natBits] at two
            simp only [Option.some.injEq, Prod.mk.injEq] at two
            obtain ⟨nlenEq, _⟩ := two
            rw [p16] at lenEq nlenEq
            have fine := (Zlib.Infback.Proofs.stored_check l1.hold holdLt).mpr (by omega)
            rw [fine] at cond
            exact absurd cond (by decide)
    · -- the complement matches
      have good : ((l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) = false := by
        simpa using cond
      have sum := (Zlib.Infback.Proofs.stored_check l1.hold holdLt).mp good
      have runOk := inflate_STORED_ok E l l1 run cond
      have lenNat := Zlib.Infback.Proofs.stored_len_toNat l1.hold
      have parsed2 := DeflateParsed.storedLength (pad := []) (len := l1.hold.toNat % 65536) parsed0
        (by simp only [List.length_nil, List.length_append, List.length_take, natBits_length]; omega)
        (by omega)
      have hiEq : l1.hold.toNat / 2 ^ 16 = 65535 - l1.hold.toNat % 65536 := by rw [p16]; omega
      have loEq : natBits 16 l1.hold.toNat = natToBitsLSB 16 (l1.hold.toNat % 65536) := by
        rw [natToBitsLSB_eq, ← p16, natBits_mod]
      have hiEq' : natBits 16 (l1.hold.toNat / 2 ^ 16) =
          natToBitsLSB 16 (65535 - l1.hold.toNat % 65536) := by
        rw [natToBitsLSB_eq, hiEq]
      have bits2 : bytesToBits (f.logIn ++ f.inp.take (loopRead l1)) =
          (bytesToBits header ++
            (bitsP ++ (natBits l.bits.toNat l.hold.toNat).take (l.bits.toNat % 8) ++ [] ++
              natToBitsLSB 16 (l1.hold.toNat % 65536) ++
              natToBitsLSB 16 (65535 - l1.hold.toNat % 65536))) ++ [] := by
        rw [bits1, exact32, split32, loEq, hiEq', consumedEq]
        simp only [List.append_assoc, List.append_nil]
      have binv2 : BitInv h { l1 with hold := 0, bits := 0 } (f.inp.drop (loopRead l1)) := by
        rw [readEq, ← List.drop_drop]
        exact (INITBITS_inv binv1).1
      have moved := loop_move
        (s' := { s with length := l1.hold.toUInt32 &&& 0xffff, mode := COPY_ })
        (l' := { l1 with hold := 0, bits := 0 })
        (pos := ⟨out, final, .stored (l1.hold.toNat % 65536)⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
          show COPY_ ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep1 used nextEq
        binv2 bits2 ⟨rfl, rfl⟩ wrapHeader rfl parsed2 ⟨Or.inl rfl, lenNat, last, rfl⟩
        (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
      by_cases trees : c.flush = Z_TREES
      · have run3 : runX (inflate_STORED c) l h =
            .ok ((.error Ex.leave, { l1 with hold := 0, bits := 0 }),
              setI h zs { s with length := l1.hold.toUInt32 &&& 0xffff, mode := COPY_ }) := by
          rw [runOk, if_pos (show (c.flush == Z_TREES) = true by simp [trees]), runX_throw]
        exact ⟨_, _, _, run3, Or.inl ⟨rfl, Or.inr (Or.inl trees), moved⟩⟩
      · have run3 : runX (inflate_STORED c) l h =
            runX (inflate_COPY_ c) { l1 with hold := 0, bits := 0 }
              (setI h zs { s with length := l1.hold.toUInt32 &&& 0xffff, mode := COPY_ }) := by
          rw [runOk, if_neg (show ¬ (c.flush == Z_TREES) = true by simp [trees])]
        have same : ∀ zs' s', c.st = some (.tab zs') →
            (setI h zs { s with length := l1.hold.toUInt32 &&& 0xffff, mode := COPY_ }).istates zs' =
              some s' → s' = { s with length := l1.hold.toUInt32 &&& 0xffff, mode := COPY_ } := by
          intro zs' s' st' hs'
          rw [st] at st'
          cases st'
          rw [setI_istates_same] at hs'
          cases hs'
          rfl
        obtain ⟨result, l', h', runC, rest⟩ := copy_start_step moved strm
          (by rw [ZStreamRef.get_setI]; exact hz)
          (fun zs' s' st' hs' => by rw [same zs' s' st' hs'])
          (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact bounds zs s st hs)
        refine ⟨result, l', h', run3.trans runC, ?_⟩
        rcases rest with ⟨leave, cause, m⟩ | ⟨ok, more, m⟩
        · exact Or.inl ⟨leave, cause.imp id (fun e => Or.inr (keep1.2.2.1.symm.trans e)), m⟩
        · exact Or.inr ⟨ok, Nat.le_trans (by show loopRead l ≤ loopRead l1; omega) more, Or.inl m⟩
  · -- not enough input
    have wait := empty rfl
    have moved := loop_move (s' := s) (l' := l1) (pos := ⟨out, final, .storedHeader⟩) st retOk config haveLe
      inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep1 used nextEq binvL bits1
      (HeldBits.of_natBits (s := loopState s l1) binv1.hold_lt) wrapHeader consumed0 parsed0
      ⟨mode, last, show l1.bits.toNat < 32 from wait.2.2⟩ (window' _ _ rfl rfl rfl rfl) check wrapM
      outputEq
    rw [setI_self hs] at moved
    exact ⟨_, _, _, inflate_STORED_wait (c := c) l l1 h _ run, Or.inl ⟨rfl, Or.inl wait.2.1, moved⟩⟩

#print axioms stored_step_bounded

/-- `case STORED` keeps the format meaning (`stored_step_bounded`, with the
held-bit bound of the `.storedHeader` position). -/
theorem stored_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (storedMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = STORED)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) :
    ∃ result l' h', runX (inflate_STORED c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ c.flush = Z_TREES ∨ l.left = 0) ∧
          LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  have heldBound : l.bits.toNat < 32 := by
    obtain ⟨zs, s, _, _, _, stage, st, hs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      stageM, _, _⟩ := loop
    obtain ⟨header, out, final, rfl⟩ := stage_of_stored stageM (storedMode zs s st hs)
    exact stageM.1.2.2
  exact stored_step_bounded loop strm hz storedMode bounds heldBound

#print axioms stored_step

end Zlib.Inflate.Proofs.MeaningBlock
