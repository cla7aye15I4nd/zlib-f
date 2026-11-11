import ZlibF.Proof.«inflate.c.leave-default-public-accounting»
import ZlibF.Proof.«inflate.c.leave-zero-output-memory»
import ZlibF.Proof.«inflate.c.default-public-output-bytes»
import ZlibF.Math.LZ77CopySpec
import ZlibF.Proof.«inflate.c.check-default-accounting»
import ZlibF.Math.DeflateChecksum
import ZlibF.Proof.«inflate.c.code-length-repeat-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The literal default-zlib CHECK/LENGTH/DONE path with no newly produced
output. The actual NEEDBITS result is an operational observation; callers
supply it from the closed macro proof, not a callee specification. -/
theorem inflate_CHECK_zlib_zero_output_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l current : IL}
    (E : Env c h r zs z s) (wrap : s.wrap = 5) (flags : s.flags = 0)
    (empty : l.out_ = l.left)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (outField : current.out_ = l.out_) (leftField : current.left = l.left)
    (trailer : ZSWAP32 current.hold = s.check) :
    runX (inflate_CHECK c) l h =
      .ok ((.error Ex.leave, { current with out_ := l.left, hold := 0, bits := 0, ret := Z_STREAM_END }),
        setI h zs { s with mode := DONE }) := by
  have amount : current.out_ - current.left = 0 := by rw [outField, leftField, empty]; simp
  unfold inflate_CHECK
  rw [runX_bind, runX_ldS E]
  simp only [wrap, show ((5 : Int32) != 0) = true from rfl, ↓reduceIte]
  rw [runX_bind, pull]
  simp only []
  simp [runX_bind, runX_lift, runX_modify, runX_get, amount, E.strm, E.st,
    wrZ_eq, wrI_eq, ldI_eq, E.hz, E.hs, ZStreamRef.put_self E.hz, flags, wrap,
    trailer, runX_INITBITS, setMode, inflate_LENGTH, inflate_DONE, runX_throw,
    setI_setI, setI, upd_upd, upd_self _ _ _ E.hs, outField, leftField, empty, bind_app, pure_app]

/-- The real optional leave checksum extends the independent checksum of
all earlier output by the exact new readable output slice. This includes
zero output and the translated Adler one-byte special case. -/
theorem leaveChecksum_zlib_output_append
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} {ref : BRef} {off : Nat} {array : Array UInt8}
    {before incoming : List UInt8} (E : Env c h r zs current s)
    (wrap : s.wrap = 5) (flags : s.flags = 0)
    (seed : s.check = (adler32 before).toUInt64) (streamSeed : current.adler = s.check)
    (pointer : z.next_out = .ref ref off) (get : Space.get h ref = some array)
    (start : (l.out_ - z.avail_out).toNat ≤ off) (finish : off ≤ array.size)
    (slice : (array.toList.drop (off - (l.out_ - z.avail_out).toNat)).take
      (l.out_ - z.avail_out).toNat = incoming) :
    leaveChecksum c l z h = .ok ((),
      setI (r.put h { current with adler := (adler32 (before ++ incoming)).toUInt64 }) zs
        { s with check := (adler32 (before ++ incoming)).toUInt64 }) := by
  let out := l.out_ - z.avail_out
  by_cases empty : out = 0
  · have incomingEmpty : incoming = [] := by
      rw [show (l.out_ - z.avail_out).toNat = 0 by change out.toNat = 0; rw [empty]; rfl] at slice
      simpa using slice.symm
    rw [incomingEmpty]
    have value : (adler32 (before ++ [])).toUInt64 = s.check := by simpa using seed.symm
    have streamValue : { current with adler := s.check } = current := by rw [← streamSeed]
    have stateValue : { s with check := s.check } = s := rfl
    unfold leaveChecksum
    have empty0 : l.out_ - z.avail_out = 0 := empty
    simp only [bind_app, E.st, ldI_eq, E.hs, empty0, bne_self_eq_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, pure_app]
    rw [value, streamValue, stateValue, ZStreamRef.put_self E.hz]
    congr 1
    unfold setI
    rw [upd_self _ _ _ E.hs]
  · have actualPointer : z.next_out.add (-((l.out_ - z.avail_out).toNat : Int)) h =
        .ok (.ref ref (off - (l.out_ - z.avail_out).toNat), h) := by
      rw [pointer]
      exact Ptr.sub_nat_ok get start finish
    have update := UPDATE_CHECK_zlib_view E.hs flags get (by omega :
      off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat ≤ array.size) s.check
    have value : adlerValue s.check ((array.toList.drop (off - (l.out_ - z.avail_out).toNat)).take
        (l.out_ - z.avail_out).toNat) = (adler32 (before ++ incoming)).toUInt64 := by
      rw [seed, slice]
      exact ZlibF.Math.DeflateChecksum.adler_value_append before incoming
    unfold leaveChecksum
    rw [E.st, E.strm]
    simp only [bind_app, ldI_eq, E.hs, wrap,
      show (((5 : Int32) &&& 4) != 0) = true from rfl, Bool.true_and,
      bne_iff_ne, show l.out_ - z.avail_out ≠ 0 from empty, ↓reduceIte]
    rw [if_pos (show l.out_ - z.avail_out ≠ 0 from empty), bind_app, actualPointer]
    simp only []
    rw [bind_app, update, value]
    simp only [bind_app, E.st, wrI_eq, E.hs, E.strm, wrZ_eq, ZStreamRef.get_setI, E.hz]
    rw [ZStreamRef.put_setI, wrap]

/-- Once the actual trailer pull succeeds, CHECK validates the independent
checksum of old output plus this call's nonempty output slice and follows
its real LENGTH/DONE path. All checksum callees are discharged by proof. -/
theorem inflate_CHECK_zlib_output_append_cut
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l current : IL}
    {ref : BRef} {off : Nat} {array : Array UInt8} {before incoming : List UInt8}
    (E : Env c h r zs z s) (wrap : s.wrap = 5) (flags : s.flags = 0)
    (seed : s.check = (adler32 before).toUInt64)
    (nonempty : l.out_ - l.left ≠ 0)
    (pointer : l.put = .ref ref off) (get : Space.get h ref = some array)
    (start : (l.out_ - l.left).toNat ≤ off) (finish : off ≤ array.size)
    (slice : (array.toList.drop (off - (l.out_ - l.left).toNat)).take
      (l.out_ - l.left).toNat = incoming)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (outField : current.out_ = l.out_) (leftField : current.left = l.left)
    (putField : current.put = l.put)
    (trailer : ZSWAP32 current.hold = (adler32 (before ++ incoming)).toUInt64) :
    runX (inflate_CHECK c) l h =
      .ok ((.error Ex.leave, { current with out_ := l.left, hold := 0, bits := 0, ret := Z_STREAM_END }),
        setI (r.put h { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (before ++ incoming)).toUInt64 }) zs
          { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (before ++ incoming)).toUInt64, mode := DONE }) := by
  let out := l.out_ - l.left
  let value := (adler32 (before ++ incoming)).toUInt64
  let h1 : Heap := setI (r.put h { z with total_out := z.total_out + out.toUInt64 }) zs
    { s with total := s.total + out.toUInt64 }
  have get1 : Space.get h1 ref = some array := by
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact get
  have state1 : h1.istates zs = some { s with total := s.total + out.toUInt64 } := by
    simp [h1]
  have actualPointer : l.put.add (-(out.toNat : Int)) h1 =
      .ok (.ref ref (off - out.toNat), h1) := by
    rw [pointer]
    exact Ptr.sub_nat_ok get1 start finish
  have update0 := UPDATE_CHECK_zlib_view state1 flags get1 (by dsimp only [out]; omega :
    off - out.toNat + out.toNat ≤ array.size) s.check
  have checksum : adlerValue s.check ((array.toList.drop (off - out.toNat)).take out.toNat) = value := by
    rw [seed, slice]
    exact ZlibF.Math.DeflateChecksum.adler_value_append before incoming
  have update : UPDATE_CHECK (some (.tab zs)) s.check (.ref ref (off - out.toNat)) out h1 =
      .ok (value, h1) := by
    rw [update0, checksum]
  have actualPointer2 := actualPointer
  have update2 := update
  simp [h1, out, wrap, flags] at actualPointer2 update2
  unfold inflate_CHECK inflate_LENGTH inflate_DONE
  rw [E.st]
  simp [runX_bind, runX_lift, ldI_eq, E.hs, wrap, pull, E.strm, runX_modify, runX_get,
    wrZ_eq, wrI_eq, E.hz, outField, leftField, putField, nonempty,
    show ((5 : Int32) &&& 4) ≠ 0 by decide, actualPointer2, update2,
    flags, trailer, runX_INITBITS, setMode, runX_throw, setI_setI, chkCond, h1, out, value,
    ZStreamRef.put_setI, ZStreamRef.put_put, ZStreamRef.get_put_same E.hz]

/-- Independent bit reads compose, retaining the exact little-endian value. -/
theorem wrapper_readBits_join {n m : Nat} {input middle rest : List Bool} {v w : Nat}
    (first : readBits n input = some (v, middle)) (second : readBits m middle = some (w, rest)) :
    readBits (n + m) input = some (v + 2 ^ n * w, rest) := by
  induction n generalizing input v with
  | zero =>
    simp only [readBits] at first
    cases first
    simpa using second
  | succ n ih =>
    cases input with
    | nil => simp [readBits] at first
    | cons bit input =>
      cases parse : readBits n input with
      | none => simp [readBits, parse] at first
      | some pair =>
        rcases pair with ⟨v0, next⟩
        simp only [readBits, parse] at first
        cases first
        have tail := ih parse
        rw [show n + 1 + m = (n + m) + 1 by omega, readBits, tail]
        congr 2
        simp only [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

/-- The independent reader consumes exactly one represented byte. -/
theorem wrapper_readBits_byte (byte : UInt8) (future : List Bool) :
    readBits 8 (natBits 8 byte.toNat ++ future) = some (byte.toNat, future) := by
  rw [natBits_testBit]
  change readBits 8 (Zlib.Inffast.Proofs.bitsOfNat byte.toNat 8 ++ future) = _
  simpa only [Nat.mod_eq_of_lt byte.toNat_lt, Nat.sub_self,
    Zlib.Inffast.Proofs.bitsOfNat_zero, List.nil_append] using
    Zlib.Inffast.Proofs.readBits_bitsOfNat 8 8 byte.toNat future (Nat.le_refl _)

/-- The independent 32-bit reader sees the four zlib trailer bytes in
memory order, before the translated byte swap. -/
theorem wrapper_readBits_be32 (value : Nat) (future : List Bool) :
    readBits 32 (bytesBits (be32 value) ++ future) = some
      (value / 16777216 % 256 + 256 * (value / 65536 % 256) +
        65536 * (value / 256 % 256) + 16777216 * (value % 256), future) := by
  let b0 := (value / 2 ^ 24 % 256).toUInt8
  let b1 := (value / 2 ^ 16 % 256).toUInt8
  let b2 := (value / 2 ^ 8 % 256).toUInt8
  let b3 := (value % 256).toUInt8
  have one := wrapper_readBits_byte b0 (natBits 8 b1.toNat ++ natBits 8 b2.toNat ++ natBits 8 b3.toNat ++ future)
  have two := wrapper_readBits_byte b1 (natBits 8 b2.toNat ++ natBits 8 b3.toNat ++ future)
  have three := wrapper_readBits_byte b2 (natBits 8 b3.toNat ++ future)
  have four := wrapper_readBits_byte b3 future
  have first := wrapper_readBits_join one two
  have second := wrapper_readBits_join first three
  have third := wrapper_readBits_join second four
  simpa only [be32, bytesBits_cons, bytesBits_nil, List.append_nil, List.append_assoc,
    b0, b1, b2, b3, UInt8.toNat_ofNat', Nat.mod_mod, Nat.reducePow, Nat.reduceAdd,
    Nat.mul_add, Nat.add_assoc, Nat.mul_assoc] using third

/-- The middle-byte mask is the second base-256 digit. -/
theorem wrapper_mask_middle_byte (value : Nat) :
    value &&& 65280 = value / 256 % 256 * 256 := by
  have shifted : value &&& (255 <<< 8) = ((value >>> 8) &&& 255) <<< 8 := by
    apply Nat.eq_of_testBit_eq
    intro bit
    by_cases low : 8 ≤ bit
    · have back : 8 + (bit - 8) = bit := by omega
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, low,
        decide_true, Bool.true_and, back]
    · simp only [Nat.testBit_and, Nat.testBit_shiftLeft, low, decide_false, Bool.false_and,
        Bool.and_false]
  have mask (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul, mask] using shifted

/-- A 32-bit little-endian read of the independent big-endian bytes becomes
that format word after the literal ZSWAP32 operation. -/
theorem wrapper_swap_be32 {held : UInt64} (value : UInt32)
    (wire : held.toNat % 4294967296 = value.toNat / 16777216 % 256 +
      256 * (value.toNat / 65536 % 256) + 65536 * (value.toNat / 256 % 256) +
      16777216 * (value.toNat % 256)) :
    ZSWAP32 held = value.toUInt64 := by
  have mask8 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
  have bound := value.toNat_lt
  have byte0 : held.toNat % 256 = value.toNat / 16777216 % 256 := by omega
  have byte1 : held.toNat / 256 % 256 = value.toNat / 65536 % 256 := by omega
  have digit2 (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
      (a + 256 * b + 65536 * c + 16777216 * d) / 65536 % 256 = c := by
    have low : a + 256 * b < 65536 := by omega
    rw [show a + 256 * b + 65536 * c + 16777216 * d =
      (a + 256 * b) + (c + d * 256) * 65536 by omega]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < 65536), Nat.div_eq_of_lt low, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have digit3 (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
      (a + 256 * b + 65536 * c + 16777216 * d) / 16777216 % 256 = d := by
    have low : a + 256 * b + 65536 * c < 16777216 := by omega
    rw [show a + 256 * b + 65536 * c + 16777216 * d =
      (a + 256 * b + 65536 * c) + d * 16777216 by omega]
    rw [Nat.add_mul_div_right _ _ (by decide : 0 < 16777216), Nat.div_eq_of_lt low, Nat.zero_add,
      Nat.mod_eq_of_lt hd]
  have keep2 : (held.toNat % 4294967296) / 65536 % 256 = held.toNat / 65536 % 256 := by
    change (held.toNat % (65536 * 65536)) / 65536 % 256 = _
    rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 65536)]
  have byte2 : held.toNat / 65536 % 256 = value.toNat / 256 % 256 := by
    rw [← keep2, wire]
    exact digit2 _ _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  have keep3 : (held.toNat % 4294967296) / 16777216 % 256 = held.toNat / 16777216 % 256 := by
    change (held.toNat % (16777216 * 256)) / 16777216 % 256 = _
    rw [Nat.mod_mul_right_div_self, Nat.mod_mod]
  have byte3 : held.toNat / 16777216 % 256 = value.toNat % 256 := by
    rw [← keep3, wire]
    exact digit3 _ _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  have split0 := Nat.mod_add_div value.toNat 256
  have split1 := Nat.mod_add_div (value.toNat / 256) 256
  have split2 := Nat.mod_add_div (value.toNat / 65536) 256
  have div1 : value.toNat / 256 / 256 = value.toNat / 65536 := by rw [Nat.div_div_eq_div_mul]
  have div2 : value.toNat / 65536 / 256 = value.toNat / 16777216 := by rw [Nat.div_div_eq_div_mul]
  rw [div1] at split1
  rw [div2] at split2
  have last : value.toNat / 16777216 % 256 = value.toNat / 16777216 := Nat.mod_eq_of_lt (by omega)
  apply UInt64.toNat_inj.mp
  simp only [ZSWAP32, UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_shiftLeft, UInt64.reduceToNat, UInt32.toNat_toUInt64, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, mask8, wrapper_mask_middle_byte]
  simp only [UInt64.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.div_div_eq_div_mul, Nat.reduceMul, mask8, wrapper_mask_middle_byte, Nat.shiftLeft_eq, byte0, byte1, byte2, byte3, last]
  clear wire byte0 byte1 byte2 byte3 keep2 keep3 held
  omega

/-- The actual trailer pull from an aligned, bounded held word reads the
independently encoded checksum, preserving every following bit. -/
theorem wrapper_NEEDBITS_valid_be32
    {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (small : l.bits.toNat ≤ 39) (aligned : l.bits.toNat % 8 = 0)
    (value : UInt32) (future : List Bool)
    (source : stream l bs = bytesBits (be32 value.toNat) ++ future) :
    ∃ current used, runX (NEEDBITS 32) l h = .ok ((.ok (), current), h) ∧
      used ≤ bs.length ∧ BitInv h current (bs.drop used) ∧ current.bits.toNat = 32 ∧
      current.next = inputAdvance l.next used ∧ current.out_ = l.out_ ∧
      current.left = l.left ∧ current.put = l.put ∧
      ZSWAP32 current.hold = value.toUInt64 ∧
      stream { current with hold := 0, bits := 0 } (bs.drop used) = future := by
  obtain ⟨outcome, current, used, pull, bound, inv, preserved, count, shape,
    bitBound, _identity, full, exhausted, kinds, cursor⟩ := NEEDBITS_run_cursor B 32 (by decide)
  have inputLength : 32 ≤ (stream l bs).length := by
    rw [source, List.length_append, bytesBits_length]
    simp only [be32, List.length_cons, List.length_nil]
    omega
  have normal : outcome = .ok () := by
    rcases kinds with done | waiting
    · exact done
    · obtain ⟨usedAll, _empty, short⟩ := exhausted waiting
      change current.bits.toNat < 32 at short
      have lengths := congrArg List.length preserved
      rw [usedAll, List.drop_length] at lengths
      have emptyLength : (stream current []).length = current.bits.toNat := by
        simp only [stream, bytesBits_nil, List.append_nil, natBits_length]
      rw [emptyLength] at lengths
      omega
  have full32 : 32 ≤ current.bits.toNat := full normal
  have exact32 : current.bits.toNat = 32 := by
    change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
    omega
  have actualRead := readBits_held_stream current (bs.drop used) 32 full32
  rw [preserved, source] at actualRead
  have expectedRead := wrapper_readBits_be32 value.toNat future
  have same := Option.some.inj (actualRead.symm.trans expectedRead)
  have checksum : ZSWAP32 current.hold = value.toUInt64 := wrapper_swap_be32 value (congrArg Prod.fst same)
  have futureEq : (stream current (bs.drop used)).drop 32 = future := by
    simpa only [preserved, source] using congrArg Prod.snd same
  have dropHeld : (stream current (bs.drop used)).drop 32 = bytesBits (bs.drop used) := by
    change (natBits current.bits.toNat current.hold.toNat ++ bytesBits (bs.drop used)).drop 32 = _
    rw [exact32]
    exact List.drop_left' (natBits_length _ _)
  refine ⟨current, used, ?_, bound, inv, exact32, cursor, ?_, ?_, ?_, checksum, ?_⟩
  · rwa [normal] at pull
  · rw [shape]
  · rw [shape]
  · rw [shape]
  · change bytesBits (bs.drop used) = future
    exact dropHeld.symm.trans futureEq

/-- A valid independent zlib trailer supplies the actual checksum test.
The source CHECK call returns END, rebases this call's output account,
keeps the following input bits, and records the cumulative Adler value. -/
theorem inflate_CHECK_zlib_valid_trailer
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    {ref : BRef} {off : Nat} {array : Array UInt8} {before incoming : List UInt8}
    (E : Env c h r zs z s) (wrap : s.wrap = 5) (flags : s.flags = 0)
    (seed : s.check = (adler32 before).toUInt64) (streamSeed : z.adler = s.check)
    (B : BitInv h l bs) (small : l.bits.toNat ≤ 39) (aligned : l.bits.toNat % 8 = 0)
    (pointer : l.put = .ref ref off) (get : Space.get h ref = some array)
    (start : (l.out_ - l.left).toNat ≤ off) (finish : off ≤ array.size)
    (slice : (array.toList.drop (off - (l.out_ - l.left).toNat)).take
      (l.out_ - l.left).toNat = incoming) (future : List Bool)
    (source : stream l bs = bytesBits (be32 (adler32 (before ++ incoming)).toNat) ++ future) :
    ∃ regs used,
      used ≤ bs.length ∧
      runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, regs),
        setI (r.put h { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (before ++ incoming)).toUInt64 }) zs
          { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (before ++ incoming)).toUInt64, mode := DONE }) ∧
      regs.next = inputAdvance l.next used ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.left ∧ regs.hold = 0 ∧ regs.bits = 0 ∧ regs.ret = Z_STREAM_END ∧
      stream regs (bs.drop used) = future := by
  obtain ⟨current, used, pull, bound, inv, bits, cursor, outField, leftField, putField, trailer, rest⟩ :=
    wrapper_NEEDBITS_valid_be32 B small aligned (adler32 (before ++ incoming)) future source
  let regs := { current with out_ := l.left, hold := 0, bits := 0, ret := Z_STREAM_END }
  have actual : runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, regs),
      setI (r.put h { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (before ++ incoming)).toUInt64 }) zs
        { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (before ++ incoming)).toUInt64, mode := DONE }) := by
    by_cases empty : l.out_ = l.left
    · have zero : (l.out_ - l.left).toNat = 0 := by rw [empty]; simp
      have incomingEmpty : incoming = [] := by rw [zero] at slice; simpa using slice.symm
      have expected : (adler32 (before ++ incoming)).toUInt64 = s.check := by
        rw [incomingEmpty, List.append_nil]
        exact seed.symm
      have streamEq : { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (before ++ incoming)).toUInt64 } = z := by
        simp only [empty, UInt32.sub_self, show (0 : UInt32).toUInt64 = (0 : UInt64) from rfl, UInt64.add_zero, expected]
        rw [← streamSeed]
      have stateEq : { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (before ++ incoming)).toUInt64, mode := DONE } = { s with mode := DONE } := by
        simp only [empty, UInt32.sub_self, show (0 : UInt32).toUInt64 = (0 : UInt64) from rfl, UInt64.add_zero, expected]
      rw [streamEq, stateEq, ZStreamRef.put_self E.hz]
      exact inflate_CHECK_zlib_zero_output_cut E wrap flags empty pull outField leftField (trailer.trans expected)
    · have nonempty : l.out_ - l.left ≠ 0 := by
        intro zero
        apply empty
        simpa using UInt32.sub_eq_iff_eq_add.mp zero
      exact inflate_CHECK_zlib_output_append_cut E wrap flags seed nonempty pointer get start finish
        slice pull outField leftField putField trailer
  refine ⟨regs, used, bound, actual, cursor, putField, leftField, rfl, rfl, rfl, rfl, ?_⟩
  exact rest

#print axioms inflate_CHECK_zlib_valid_trailer

#print axioms wrapper_NEEDBITS_valid_be32

#print axioms wrapper_mask_middle_byte
#print axioms wrapper_swap_be32

#print axioms wrapper_readBits_byte
#print axioms wrapper_readBits_be32

#print axioms wrapper_readBits_join

#print axioms inflate_CHECK_zlib_output_append_cut

#print axioms leaveChecksum_zlib_output_append

#print axioms inflate_CHECK_zlib_zero_output_cut
namespace WrapperGlue

/-- Ghost ledger of bytes already credited by the real checksum statements.
The current uncredited output slice is kept separate until CHECK or leave.
This describes byte observation; payload format meaning is a separate proof. -/
def AdlerCredit (z : ZStream) (s : InflateState) (credited : List UInt8) : Prop :=
  s.wrap = 5 ∧ s.flags = 0 ∧ s.check = (adler32 credited).toUInt64 ∧ z.adler = s.check

theorem head_accept_adler_base
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (wrap : s.wrap = 5)
    (header : headHeaderRejected s l = false) (method : headMethodRejected l = false)
    (window : (headWindowRegs l).len.toNat ≤ s.wbits.toNat) (wbits : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) :
    runX (headDefaultCheck c s l) l h =
      .ok ((.ok (), { headWindowRegs l with hold := 0, bits := 0 }),
        setI (r.put h { z with adler := 1 }) zs (headDefaultState s l)) ∧
    AdlerCredit { z with adler := 1 } (headDefaultState s l) [] := by
  exact ⟨headDefaultCheck_accept E l header method window wbits, wrap, rfl, rfl, rfl⟩

/-- The payload agents' independent writtenBytes is the very byte slice
read by the actual Adler callee. All readable BRef kinds are retained. -/
theorem writtenBytes_observed {h : Heap} {ref : BRef} {off count : Nat} {a : Array UInt8}
    (get : Space.get h ref = some a) (start : count ≤ off) (bound : off ≤ a.size) :
    Bytes h (.ref ref (off - count)) count (ZlibF.Math.LZ77Copy.writtenBytes a off count) := by
  exact Or.inr ⟨ref, off - count, a, rfl, get, by omega, rfl⟩

/-- RESTORE changes only cursor/bit-buffer fields, retaining the exact
credited checksum even when this call stops with partial input or output. -/
theorem adlerCredit_restore {z : ZStream} {s : InflateState} {credited : List UInt8}
    (credit : AdlerCredit z s credited) (l : IL) :
    AdlerCredit (leaveStream z l) (leaveState s l) credited := credit

/-- Successful window allocation/copy retains the checksum ledger. -/
theorem adlerCredit_window {z : ZStream} {s state : InflateState} {credited : List UInt8}
    (credit : AdlerCredit z s credited) (frame : WindowStateFrame s state) :
    AdlerCredit z state credited := by
  rw [frame]
  exact credit

/-- The full actual post-window suffix credits exactly the newly written
slice, including zero output and partial-call return codes. It preserves
all byte views and the public stream/state Adler agreement. -/
theorem leaveFinalize_adler_append
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} {ref : BRef} {off : Nat} {a : Array UInt8}
    {credited incoming : List UInt8}
    (E : Env c h r zs current s) (bits : s.bits.toNat ≤ 39)
    (credit : AdlerCredit current s credited)
    (pointer : z.next_out = .ref ref off) (get : Space.get h ref = some a)
    (start : (l.out_ - z.avail_out).toNat ≤ off) (bound : off ≤ a.size)
    (written : ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - z.avail_out).toNat = incoming) :
    ∃ dt after stream state,
      leaveFinalize c l z h = .ok
        ((if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret), after) ∧
      after = setI (r.put h stream) zs state ∧
      stream = { leaveCountStream current z l with adler := (adler32 (credited ++ incoming)).toUInt64, data_type := dt } ∧
      state = { leaveCountState s z l with check := (adler32 (credited ++ incoming)).toUInt64 } ∧
      AdlerCredit stream state (credited ++ incoming) ∧
      (∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref) := by
  let stream1 := leaveCountStream current z l
  let state1 := leaveCountState s z l
  let heap1 := setI (r.put h stream1) zs state1
  let value := (adler32 (credited ++ incoming)).toUInt64
  let stream2 := { stream1 with adler := value }
  let state2 := { state1 with check := value }
  let heap2 := setI (r.put heap1 stream2) zs state2
  have env1 : Env c heap1 r zs stream1 state1 :=
    ⟨E.strm, E.st, by simp [heap1, stream1, ZStreamRef.get_put_same E.hz], by simp [heap1]⟩
  have get1 : Space.get heap1 ref = some a := by
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact get
  have checksum := leaveChecksum_zlib_output_append (z := z) env1 credit.1 credit.2.1
    credit.2.2.1 credit.2.2.2 pointer get1 start bound written
  have get2 : r.get heap2 = some stream2 := by
    simp [heap2, stream2, ZStreamRef.get_put_same env1.hz]
  have stateGet2 : heap2.istates zs = some state2 := by simp [heap2]
  have env2 : Env c heap2 r zs stream2 state2 := ⟨E.strm, E.st, get2, stateGet2⟩
  obtain ⟨dt, _, returned⟩ := leaveReturn_run (z := z) env2 bits
  let stream3 := { stream2 with data_type := dt }
  let after := r.put heap2 stream3
  have heapEq : after = setI (r.put h stream3) zs state2 := by
    dsimp only [after, heap2]
    rw [ZStreamRef.put_setI, ZStreamRef.put_put, ZStreamRef.put_setI,
      ZStreamRef.put_put, setI_setI]
  refine ⟨dt, after, stream3, state2, ?_, heapEq, rfl, rfl, ?_, ?_⟩
  · rw [leaveFinalize_split, bind_app, leaveCounters_run E]
    simp only []
    rw [bind_app, checksum]
    exact returned
  · exact ⟨credit.1, credit.2.1, rfl, rfl⟩
  · intro view
    rw [heapEq, byte_view_get_setI, byte_view_get_stream_put]

#print axioms head_accept_adler_base
#print axioms writtenBytes_observed
#print axioms adlerCredit_restore
#print axioms adlerCredit_window
#print axioms leaveFinalize_adler_append

/-- The same exact suffix result, exposing actual record reads for the
next call rather than a second abstract checksum state. -/
theorem leaveFinalize_adler_records
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} {ref : BRef} {off : Nat} {a : Array UInt8}
    {credited incoming : List UInt8}
    (E : Env c h r zs current s) (bits : s.bits.toNat ≤ 39)
    (credit : AdlerCredit current s credited)
    (pointer : z.next_out = .ref ref off) (get : Space.get h ref = some a)
    (start : (l.out_ - z.avail_out).toNat ≤ off) (bound : off ≤ a.size)
    (written : ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - z.avail_out).toNat = incoming) :
    ∃ after stream state,
      leaveFinalize c l z h = .ok
        ((if ((l.in_ - z.avail_in == 0 && l.out_ - z.avail_out == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret), after) ∧
      r.get after = some stream ∧ after.istates zs = some state ∧
      AdlerCredit stream state (credited ++ incoming) := by
  obtain ⟨dt, after, stream, state, run, heap, _, _, credit, _⟩ :=
    leaveFinalize_adler_append E bits credit pointer get start bound written
  refine ⟨after, stream, state, run, ?_, ?_, credit⟩
  · rw [heap, ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz stream
  · rw [heap]
    simp only [setI_istates_same]

/-- Actual full inf_leave, including RESTORE and real window handling.
Ordinary returns append the just-written slice to the checksum ledger.
A genuine window-allocation failure retains the previous ledger and is
reported separately; those bytes have not yet been credited by zlib. -/
theorem inflate_leave_adler_credit
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {off : Nat} {a : Array UInt8}
    {credited incoming : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited)
    (pointer : l.put = .ref ref off) (get : Space.get h ref = some a)
    (start : (l.out_ - l.left).toNat ≤ off) (bound : off ≤ a.size)
    (written : ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat = incoming)
    (unowned : ∀ w, s.window = .ref (.blk w) 0 → ref ≠ .blk w) :
    ∃ rc after stream state,
      inflate_leave c l h = .ok (rc, after) ∧
      r.get after = some stream ∧ after.istates zs = some state ∧
      ((rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧ AdlerCredit stream state (credited ++ incoming)) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ AdlerCredit stream state credited)) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have inv0 : StInv h zs state0 :=
    good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl bits rfl rfl rfl
  have good0 : Good heap0 r zs stream0 state0 :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl good.live.mode inv0
  have env0 : Env c heap0 r zs stream0 state0 := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
  have get0 : Space.get heap0 ref = some a := by
    rw [byte_view_get_setI, byte_view_get_stream_put]
    exact get
  have credit0 := adlerCredit_restore credit l
  have ordinary : (if ((l.in_ - stream0.avail_in == 0 && l.out_ - stream0.avail_out == 0 ||
      c.flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret) =
      (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
        l.ret == Z_OK) then Z_BUF_ERROR else l.ret) := rfl
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, sourceView, _, outcome⟩ :=
      updatewindow_decoder_boundary (copy := l.out_ - l.left) good0 allocator get0 start bound unowned
    rcases outcome with success | failure
    · subst wr
      have env1 : Env c heap1 r zs stream0 state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
      have bits1 : state1.bits.toNat ≤ 39 := by rw [windowFrame]; exact bits
      obtain ⟨after, stream, state, finished, getZ, getS, credited1⟩ :=
        leaveFinalize_adler_records (z := stream0) env1 bits1
          (adlerCredit_window credit0 windowFrame) pointer sourceView start bound written
      refine ⟨_, after, stream, state, ?_, getZ, getS, Or.inl ⟨ordinary, credited1⟩⟩
      rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
      unfold leaveWithWindow
      rw [bind_app, E.strm, show stream0.next_out = .ref ref off from pointer,
        show stream0.avail_out = l.left from rfl, windowRun]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact finished
    · obtain ⟨eqrc, _, stateEq, _⟩ := failure
      subst wr
      subst state1
      let state := { state0 with mode := MEM }
      refine ⟨Z_MEM_ERROR, setI heap1 zs state, stream0, state, ?_, ?_, ?_, Or.inr ⟨rfl, rfl, credit0⟩⟩
      · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
        unfold leaveWithWindow
        rw [bind_app, E.strm, show stream0.next_out = .ref ref off from pointer,
        show stream0.avail_out = l.left from rfl, windowRun]
        simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
          setMode_tab good1.live.hs, pure_app]
        rfl
      · rw [ZStreamRef.get_setI]
        exact good1.live.hz
      · simp only [setI_istates_same]
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨after, stream, state, finished, getZ, getS, credited1⟩ :=
      leaveFinalize_adler_records (z := stream0) env0 bits credit0 pointer get0 start bound written
    refine ⟨_, after, stream, state, ?_, getZ, getS, Or.inl ⟨ordinary, credited1⟩⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact finished

#print axioms leaveFinalize_adler_records
#print axioms inflate_leave_adler_credit

/-- The original legal caller edit preserves the private state and Adler
field. Rebinding disjoint intervals in a single byte object is admitted. -/
theorem adlerCredit_rebuffer {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {credited : List UInt8}
    (good : Good h r zs z s) (edit : Rebuffer h after r) (credit : AdlerCredit z s credited) :
    ∃ stream, r.get after = some stream ∧ after.istates zs = some s ∧ AdlerCredit stream s credited := by
  obtain ⟨stream, fields, final⟩ := rebuffer_inflate_good good edit
  refine ⟨stream, final.live.hz, final.live.hs, credit.1, credit.2.1, credit.2.2.1, ?_⟩
  rw [fields]
  exact credit.2.2.2

/-- After successful CHECK has rebased its output account, actual inf_leave
returns END and retains the new cumulative checksum. It cannot credit the
same payload twice and cannot fail a fresh window allocation at this point. -/
theorem inflate_leave_after_CHECK_adler
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {credited : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (pending : DataPendingInvariant s)
    (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited) (zero : l.out_ = l.left) (ended : l.ret = Z_STREAM_END) :
    ∃ after stream state, inflate_leave c l h = .ok (Z_STREAM_END, after) ∧
      r.get after = some stream ∧ after.istates zs = some state ∧ AdlerCredit stream state credited := by
  obtain ⟨ref, a, off, ptr, get, _, room, count, made, unowned⟩ :=
    callerRange_slow_output good l packet.output.range packet.output.nonnull packet.output.count packet.output.produced
  have start : (l.out_ - l.left).toNat ≤ off := by rw [zero]; simp
  have written : ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat = [] := by
    rw [zero]
    simp [ZlibF.Math.LZ77Copy.writtenBytes]
  obtain ⟨rc, after, stream, state, run, getZ, getS, outcome⟩ :=
    inflate_leave_adler_credit E good allocator bits credit ptr get start (by omega) written unowned
  rcases outcome with ordinary | failure
  · have eqrc : rc = Z_STREAM_END := by
      simpa only [ended, show (Z_STREAM_END == Z_OK) = false from rfl,
        Bool.and_false, Bool.false_eq_true, ite_false] using ordinary.1
    exact ⟨after, stream, state, by simpa only [eqrc] using run, getZ, getS,
      by simpa only [List.append_nil] using ordinary.2⟩
  · rw [failure.1] at run
    exact False.elim (inflate_leave_zero_output_not_memory E good allocator pending packet bits
      (Or.inr (Or.inl ended)) zero run)

/-- Public allocation/body/free composition for an exact actual body run.
The body equation is a source-cut observation supplied by its execution
proof, not a callee specification. All return codes, including END, work. -/
theorem inflate_public_close_body
    {h bodyHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {rc flush : Int32}
    (initial : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (actual : (do
      let (result, regs) ← runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave ⟨some r, some (.tab zs), syncBuf h, flush⟩ regs) (syncAlloc h) = .ok (rc, bodyHeap)) :
    ∃ stream state,
      C.run (inflate (some r) flush) h = .ok (rc, freeWin bodyHeap (syncBuf h)) ∧
      DefaultStateJ (freeWin bodyHeap (syncBuf h)) r zs stream state ∧ DefAlloc stream ∧
      (freeWin bodyHeap (syncBuf h)).bytes h.nextBlk = none ∧
      r.get bodyHeap = some stream ∧ bodyHeap.istates zs = some state := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc initial
  have env : Env c (syncAlloc h) r zs z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  obtain ⟨rc0, heap1, stream, state, bytes, bodyRun, current, finalAllocator, localGet, localSize, localRo⟩ :=
    inflate_default_view_local_state_return env allocated allocator
      (streamBuffers_syncAlloc initial.good.fresh buffers) nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have same : (rc0, heap1) = (rc, bodyHeap) := Except.ok.inj (bodyRun.symm.trans actual)
  cases same
  have final := current.free_local localGet localSize
  refine ⟨stream, state, ?_, final, finalAllocator, ?_, current.good.live.hz, current.good.live.hs⟩
  · have entry : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      by_cases null : z.next_in = .null
      · simp [nonnull, null, inputValid null]
      · simp [nonnull, null]
    unfold C.run inflate
    rw [bind_app, allocLocalB_run h initial.good.fresh]
    simp only []
    rw [bind_app]
    simp only [bind_app, stateCheck_live allocated.good.live, bne_self_eq_false, Bool.false_eq_true,
      ite_false, ldZStream_ok allocated.good.live.hz, entry, allocated.good.live.zst, castI]
    rw [bind_app] at bodyRun
    unfold runX at bodyRun
    dsimp only [c] at bodyRun
    erw [bodyRun]
    simp only []
    change (do freeB (syncBuf h); pure rc) bodyHeap = .ok (rc, freeWin bodyHeap (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  · simp only [syncBuf, freeWin, upd_same]

/-- Public output observation is on the same exact successful execution.
This retains all original byte-view kinds and same-object separated ranges. -/
theorem public_actual_END_output
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {flush : Int32}
    (initial : DefaultStateJ h r zs z s) (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (actual : C.run (inflate (some r) flush) h = .ok (Z_STREAM_END, after)) :
    ∃ stream state used output,
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ after.bytes h.nextBlk = none ∧
      StreamAccounting z stream used output.length ∧ Bytes after z.next_out output.length output ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) [⟨z.next_out, output.length⟩] := by
  obtain ⟨rc, heap1, stream, state, used, output, run, final, alloc, freed, account, bytes, frame⟩ :=
    inflate_default_view_public_output_bytes initial allocator buffers flush
  have same : (rc, heap1) = (Z_STREAM_END, after) := Except.ok.inj (run.symm.trans actual)
  cases same
  exact ⟨stream, state, used, output, final, alloc, freed, account, bytes, frame⟩

#print axioms adlerCredit_rebuffer
#print axioms inflate_leave_after_CHECK_adler
#print axioms inflate_public_close_body
#print axioms public_actual_END_output

/-- DICTID stores the dictionary id in check, so the output checksum
ledger begins again at the actual DICT-ready reset, not at that id. -/
theorem dictionary_ready_adler_base
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (wrap : s.wrap = 5) (flags : s.flags = 0)
    (present : s.havedict ≠ 0) :
    runX (inflate_DICT c) l h = runX (inflate_TYPE c) l
      (setI (r.put h { z with adler := 1 }) zs { s with check := 1, mode := TYPE }) ∧
    AdlerCredit { z with adler := 1 } { s with check := 1, mode := TYPE } [] := by
  exact ⟨inflate_DICT_ready_cut E l present, wrap, flags, rfl, rfl⟩

/-- Standard literal/length/distance scalar frames retain the old credit;
the bytes written by those paths remain the uncredited current segment. -/
theorem adlerCredit_decode {z : ZStream} {s state : InflateState} {credited : List UInt8}
    (credit : AdlerCredit z s credited) (frame : DecodeStateFrame s state) :
    AdlerCredit z state credited := by
  rw [frame]
  exact credit

/-- A valid independent trailer commits the current writtenBytes segment
to the actual records and rebases the local account to zero. The earlier
credit can come from any number of preceding ordinary leaves/rebuffers. -/
theorem CHECK_adler_commit
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    {ref : BRef} {off : Nat} {a : Array UInt8} {credited incoming : List UInt8}
    (E : Env c h r zs z s) (credit : AdlerCredit z s credited)
    (B : BitInv h l bs) (small : l.bits.toNat ≤ 39) (aligned : l.bits.toNat % 8 = 0)
    (pointer : l.put = .ref ref off) (get : Space.get h ref = some a)
    (start : (l.out_ - l.left).toNat ≤ off) (bound : off ≤ a.size)
    (written : ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat = incoming)
    (future : List Bool)
    (source : stream l bs = bytesBits (be32 (adler32 (credited ++ incoming)).toNat) ++ future) :
    ∃ regs used after current state,
      used ≤ bs.length ∧ runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, regs), after) ∧
      r.get after = some current ∧ after.istates zs = some state ∧
      AdlerCredit current state (credited ++ incoming) ∧ state.mode = DONE ∧
      regs.next = inputAdvance l.next used ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = regs.left ∧ regs.hold = 0 ∧ regs.bits = 0 ∧ regs.ret = Z_STREAM_END ∧
      stream regs (bs.drop used) = future := by
  obtain ⟨regs, used, usedBound, actual, next, put, left, out, hold, bits, ret, rest⟩ :=
    inflate_CHECK_zlib_valid_trailer E credit.1 credit.2.1 credit.2.2.1 credit.2.2.2
      B small aligned pointer get start bound written future source
  let current : ZStream := { z with total_out := z.total_out + (l.out_ - l.left).toUInt64, adler := (adler32 (credited ++ incoming)).toUInt64 }
  let state : InflateState := { s with total := s.total + (l.out_ - l.left).toUInt64, check := (adler32 (credited ++ incoming)).toUInt64, mode := DONE }
  refine ⟨regs, used, setI (r.put h current) zs state, current, state, usedBound, actual,
    ?_, by simp, ⟨credit.1, credit.2.1, rfl, rfl⟩, rfl, next, put, left, out.trans left.symm,
    hold, bits, ret, rest⟩
  rw [ZStreamRef.get_setI]
  exact ZStreamRef.get_put_same E.hz current

/-- The exact body ledger survives the actual public local-object cleanup.
No total-output bytes are guessed: credit is an explicit internal record
invariant at the proven body exit, whose records are retained by free. -/
theorem inflate_public_close_body_adler
    {h bodyHeap : Heap} {r : ZStreamRef} {zs : Nat} {z current : ZStream} {s state : InflateState}
    {rc flush : Int32} {credited : List UInt8}
    (initial : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (actual : (do
      let (result, regs) ← runX (inflate_run ⟨some r, some (.tab zs), syncBuf h, flush⟩) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave ⟨some r, some (.tab zs), syncBuf h, flush⟩ regs) (syncAlloc h) = .ok (rc, bodyHeap))
    (getZ : r.get bodyHeap = some current) (getS : bodyHeap.istates zs = some state)
    (credit : AdlerCredit current state credited) :
    C.run (inflate (some r) flush) h = .ok (rc, freeWin bodyHeap (syncBuf h)) ∧
    DefaultStateJ (freeWin bodyHeap (syncBuf h)) r zs current state ∧ DefAlloc current ∧
    (freeWin bodyHeap (syncBuf h)).bytes h.nextBlk = none ∧
    AdlerCredit current state credited := by
  obtain ⟨otherZ, otherS, run, final, alloc, freed, otherGetZ, otherGetS⟩ :=
    inflate_public_close_body initial allocator buffers nonnull inputValid actual
  have sameZ : otherZ = current := Option.some.inj (otherGetZ.symm.trans getZ)
  have sameS : otherS = state := Option.some.inj (otherGetS.symm.trans getS)
  subst otherZ otherS
  exact ⟨run, final, alloc, freed, credit⟩

#print axioms dictionary_ready_adler_base
#print axioms adlerCredit_decode
#print axioms CHECK_adler_commit
#print axioms inflate_public_close_body_adler

/-- Whole actual leave connects the independent writtenBytes prefix with
the bytes observed on its returned heap, J and the public cursor bindings.
The public caller packet derives the window exclusion. The memory branch
keeps the old checksum ledger explicitly. Partial calls are included. -/
theorem inflate_leave_adler_observed
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {credited : List UInt8}
    (E : Env c h r zs z s) (initial : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (packet : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (credit : AdlerCredit z s credited) (lowOut : s.mode ≤ DICT → l.out_ = l.left) :
    ∃ rc after current state ref off a incoming,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs current state ∧ DefAlloc current ∧
      l.put = .ref ref off ∧ Space.get h ref = some a ∧ Space.get after ref = some a ∧
      incoming = ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat ∧
      incoming.length = (l.out_ - l.left).toNat ∧
      Bytes after (.ref ref (off - (l.out_ - l.left).toNat)) incoming.length incoming ∧
      current.next_out = l.put ∧ current.avail_out = l.left ∧
      ((rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧ AdlerCredit current state (credited ++ incoming)) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ AdlerCredit current state credited)) := by
  obtain ⟨ref, a, off, pointer, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output initial.good l packet.output.range packet.output.nonnull packet.output.count packet.output.produced
  have amount : (l.out_ - l.left).toNat = l.out_.toNat - l.left.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - l.left).toNat ≤ off := by rw [amount]; exact produced
  let incoming := ZlibF.Math.LZ77Copy.writtenBytes a off (l.out_ - l.left).toNat
  obtain ⟨rc, after, current, state, run, getZ, getS, outcome⟩ :=
    inflate_leave_adler_credit E initial.good allocator.1 bits credit pointer get start (by omega) rfl unowned
  have view := (inflate_leave_output_view_unchanged E initial allocator packet bits run pointer get).2.1
  obtain ⟨otherRc, otherHeap, otherZ, otherS, otherRun, final, alloc,
    _next, _have, put, left, _account⟩ :=
    inflate_leave_default_public_accounting E initial allocator packet bits lowOut
  have same : (otherRc, otherHeap) = (rc, after) := Except.ok.inj (otherRun.symm.trans run)
  cases same
  have sameZ : otherZ = current := Option.some.inj (final.good.live.hz.symm.trans getZ)
  have sameS : otherS = state := Option.some.inj (final.good.live.hs.symm.trans getS)
  subst otherZ otherS
  have length : incoming.length = (l.out_ - l.left).toNat := by
    simp only [incoming, ZlibF.Math.LZ77Copy.writtenBytes, List.length_take, List.length_drop, Array.length_toList]
    omega
  refine ⟨rc, after, current, state, ref, off, a, incoming, run, final, alloc,
    pointer, get, view, rfl, length, ?_, put, left, outcome⟩
  rw [length]
  exact writtenBytes_observed view start (by omega)

#print axioms inflate_leave_adler_observed

/-- The actual null-output entry refusal changes no checksum record. -/
theorem inflate_null_output_credit
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {credited : List UInt8}
    (initial : DefaultStateJ h r zs z s) (credit : AdlerCredit z s credited)
    (flush : Int32) (null : z.next_out = .null) :
    C.run (inflate (some r) flush) h = .ok (Z_STREAM_ERROR, tmpFreed h) ∧
    DefaultStateJ (tmpFreed h) r zs z s ∧ AdlerCredit z s credited := by
  have allocated := default_state_syncAlloc initial
  have final := allocated.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
  exact ⟨inflate_default_null_output_run initial flush null, final, credit⟩

/-- Equal physical byte observations have equal contents, including all
represented same-object slices. This is independent of payload meaning. -/
theorem wrapper_bytes_unique {h : Heap} {p : BPtr} {n : Nat} {left right : List UInt8}
    (first : Bytes h p n left) (second : Bytes h p n right) : left = right := by
  rcases first with ⟨null, zero, empty⟩ | ⟨ref, off, a, ptr, get, _, values⟩
  · rw [null] at second
    rcases second with ⟨_, _, rfl⟩ | ⟨ref, off, a, impossible, _⟩
    · exact empty
    · cases impossible
  · rcases second with ⟨null, _, _⟩ | ⟨ref1, off1, a1, ptr1, get1, _, values1⟩
    · rw [ptr] at null
      cases null
    · have eqptr := ptr.symm.trans ptr1
      cases eqptr
      have arrays : a = a1 := Option.some.inj (get.symm.trans get1)
      subst a1
      exact values.trans values1.symm

/-- The actual public/trace output observation agrees with the prefix
used by leave's Adler calculation, once the source cursor accounting
identifies its start and length. No different-object premise is present. -/
theorem writtenBytes_matches_output
    {h : Heap} {ref : BRef} {off count : Nat} {a : Array UInt8} {output : List UInt8}
    (get : Space.get h ref = some a) (start : count ≤ off) (bound : off ≤ a.size)
    (observed : Bytes h (.ref ref (off - count)) count output) :
    output = ZlibF.Math.LZ77Copy.writtenBytes a off count := by
  exact wrapper_bytes_unique observed (writtenBytes_observed get start bound)

#print axioms inflate_null_output_credit
#print axioms wrapper_bytes_unique
#print axioms writtenBytes_matches_output
end WrapperGlue
end Zlib.Inflate.Proofs
