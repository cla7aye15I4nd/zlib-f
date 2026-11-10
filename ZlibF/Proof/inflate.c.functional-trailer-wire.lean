import ZlibF.Proof.«inflate.c.functional-trailer-bad»
import ZlibF.Math.InflateDecodeBits

namespace Zlib.Inflate.Proofs.FunctionalTrailerWire
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
set_option maxRecDepth 4096

/-- Inverse of the actual zlib byte swap: accepted CHECK words determine
all four independent trailer bytes. No expected-word equality is assumed
by the final format consumer. -/
theorem swap_be32_inverse {held : UInt64} {value : UInt32}
    (accepted : ZSWAP32 held = value.toUInt64) :
    held.toNat % 4294967296 = value.toNat / 16777216 % 256 +
      256 * (value.toNat / 65536 % 256) + 65536 * (value.toNat / 256 % 256) +
      16777216 * (value.toNat % 256) := by
  have mask8 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
  have actual := congrArg UInt64.toNat accepted
  simp only [ZSWAP32, UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_shiftRight,
    UInt64.toNat_shiftLeft, UInt64.reduceToNat, UInt32.toNat_toUInt64,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, mask8, wrapper_mask_middle_byte,
    Nat.reducePow, Nat.reduceMod, Nat.div_div_eq_div_mul, Nat.reduceMul] at actual
  have vbound := value.toNat_lt
  have b0 := Nat.mod_lt held.toNat (by decide : 0 < 256)
  have b1 := Nat.mod_lt (held.toNat / 256) (by decide : 0 < 256)
  have b2 := Nat.mod_lt (held.toNat / 65536) (by decide : 0 < 256)
  have b3 := Nat.mod_lt (held.toNat / 16777216) (by decide : 0 < 256)
  have sum2 : held.toNat / 16777216 % 256 + held.toNat / 65536 % 256 * 256 < 18446744073709551616 := by omega
  have shift1 : held.toNat / 256 % 256 * 256 * 256 < 18446744073709551616 := by omega
  have shift0 : held.toNat % 256 * 16777216 < 18446744073709551616 := by omega
  have sum3 : held.toNat / 16777216 % 256 + held.toNat / 65536 % 256 * 256 +
      held.toNat / 256 % 256 * 256 * 256 < 18446744073709551616 := by omega
  have sum4 : held.toNat / 16777216 % 256 + held.toNat / 65536 % 256 * 256 +
      held.toNat / 256 % 256 * 256 * 256 + held.toNat % 256 * 16777216 < 18446744073709551616 := by omega
  simp only [Nat.mod_eq_of_lt sum2, Nat.mod_eq_of_lt shift1, Nat.mod_eq_of_lt shift0,
    Nat.mod_eq_of_lt sum3, Nat.mod_eq_of_lt sum4] at actual
  have div1 : held.toNat / 256 / 256 = held.toNat / 65536 := by rw [Nat.div_div_eq_div_mul]
  have div2 : held.toNat / 65536 / 256 = held.toNat / 16777216 := by rw [Nat.div_div_eq_div_mul]
  have div3 : held.toNat / 16777216 / 256 = held.toNat / 4294967296 := by rw [Nat.div_div_eq_div_mul]
  have vdiv1 : value.toNat / 256 / 256 = value.toNat / 65536 := by rw [Nat.div_div_eq_div_mul]
  have vdiv2 : value.toNat / 65536 / 256 = value.toNat / 16777216 := by rw [Nat.div_div_eq_div_mul]
  have vdiv3 : value.toNat / 16777216 / 256 = value.toNat / 4294967296 := by rw [Nat.div_div_eq_div_mul]
  have valueHigh : value.toNat / 4294967296 = 0 := by
    apply Nat.div_eq_of_lt
    exact value.toNat_lt
  have byte0 : held.toNat % 256 = value.toNat / 16777216 % 256 := by omega
  have byte1 : held.toNat / 256 % 256 = value.toNat / 65536 % 256 := by omega
  have byte2 : held.toNat / 65536 % 256 = value.toNat / 256 % 256 := by omega
  have byte3 : held.toNat / 16777216 % 256 = value.toNat % 256 := by omega
  omega

#print axioms swap_be32_inverse
/-- The independent bit reader retains enough information to reconstruct
its entire input, including the unconsumed suffix. -/
theorem readBits_input_unique {n value : Nat} {first second suffix : List Bool}
    (enoughFirst : n ≤ first.length) (enoughSecond : n ≤ second.length)
    (readFirst : readBits n first = some (value, suffix))
    (readSecond : readBits n second = some (value, suffix)) : first = second := by
  obtain ⟨v1, rest1, actual1, _bound1, source1⟩ :=
    ZlibF.Math.InflateDecode.read_total n first enoughFirst
  obtain ⟨v2, rest2, actual2, _bound2, source2⟩ :=
    ZlibF.Math.InflateDecode.read_total n second enoughSecond
  have same1 := Option.some.inj (actual1.symm.trans readFirst)
  have same2 := Option.some.inj (actual2.symm.trans readSecond)
  cases same1
  cases same2
  exact source1.trans source2.symm

/-- Soundness for arbitrary complete trailer input. An actual CHECK exit
forces the independent big-endian trailer of the actual observed output;
all following input bits are retained. The wire-validity equation is
produced from the source execution, never assumed as an END oracle. -/
theorem CHECK_observed_exit_wire
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l current returned : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s)
    (ledger : Zlib.Inflate.Proofs.FunctionalTrailer.OutputCredit h z s l prior emitted credited)
    (B : BitInv h l bs) (small : l.bits.toNat ≤ 39) (aligned : l.bits.toNat % 8 = 0)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h))
    (observed : runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, returned), after)) :
    ∃ used suffix, used ≤ bs.length ∧ BitInv h current (bs.drop used) ∧ current.bits.toNat = 32 ∧
      stream l bs = bytesBits (be32 (adler32 (prior ++ emitted)).toNat) ++ suffix ∧
      (stream current (bs.drop used)).drop 32 = suffix := by
  obtain ⟨outcome, pulled, used, actualPull, usedBound, inv, source, count, shape,
    bitBound, _identity, full, _wait, _kinds, _cursor⟩ := NEEDBITS_run_cursor B 32 (by decide)
  have same := Except.ok.inj (actualPull.symm.trans pull)
  cases same
  have full32 := full rfl
  change 32 ≤ current.bits.toNat at full32
  have exact32 : current.bits.toNat = 32 := by
    change current.bits.toNat ≤ max l.bits.toNat 39 at bitBound
    omega
  have accepted := Zlib.Inflate.Proofs.FunctionalTrailerReject.CHECK_observed_exit_checksum
    E ledger pull (by rw [shape]) (by rw [shape]) (by rw [shape]) observed
  have wire := swap_be32_inverse accepted
  let suffix := (stream current (bs.drop used)).drop 32
  have firstRead := readBits_held_stream current (bs.drop used) 32 full32
  change readBits 32 (stream current (bs.drop used)) = some (current.hold.toNat % 4294967296, suffix) at firstRead
  rw [wire] at firstRead
  have secondRead := wrapper_readBits_be32 (adler32 (prior ++ emitted)).toNat suffix
  have firstEnough : 32 ≤ (stream current (bs.drop used)).length := by
    simp only [stream, List.length_append, natBits_length]
    omega
  have secondEnough : 32 ≤ (bytesBits (be32 (adler32 (prior ++ emitted)).toNat) ++ suffix).length := by
    simp only [List.length_append, bytesBits_length, be32, List.length_cons, List.length_nil]
    omega
  have independent := readBits_input_unique firstEnough secondEnough firstRead secondRead
  exact ⟨used, suffix, usedBound, inv, exact32, source.symm.trans independent, rfl⟩

#print axioms readBits_input_unique
#print axioms CHECK_observed_exit_wire

/-- No complete-pull premise is needed for the actual END soundness
boundary: source NEEDBITS either waits with unchanged OK, which cannot be
this END, or yields the full independently valid trailer. -/
theorem CHECK_observed_END_wire
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l returned : IL} {bs prior emitted : List UInt8} {credited : Nat}
    (E : Env c h r zs z s)
    (ledger : Zlib.Inflate.Proofs.FunctionalTrailer.OutputCredit h z s l prior emitted credited)
    (B : BitInv h l bs) (small : l.bits.toNat ≤ 39) (aligned : l.bits.toNat % 8 = 0)
    (incoming : l.ret = Z_OK)
    (observed : runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, returned), after))
    (ended : returned.ret = Z_STREAM_END) :
    ∃ current used suffix,
      runX (NEEDBITS 32) l h = .ok ((.ok (), current), h) ∧ used ≤ bs.length ∧
      BitInv h current (bs.drop used) ∧ current.bits.toNat = 32 ∧
      stream l bs = bytesBits (be32 (adler32 (prior ++ emitted)).toNat) ++ suffix ∧
      (stream current (bs.drop used)).drop 32 = suffix := by
  obtain ⟨outcome, current, used, pull, _usedBound, _inv, _source, _count, shape,
    _bitBound, _identity, _full, _wait, kinds, _cursor⟩ := NEEDBITS_run_cursor B 32 (by decide)
  rcases kinds with normal | waiting
  · have actual : runX (NEEDBITS 32) l h = .ok ((.ok (), current), h) := by rwa [normal] at pull
    obtain ⟨used, suffix, bound, inv, bits, source, rest⟩ :=
      CHECK_observed_exit_wire E ledger B small aligned actual observed
    exact ⟨current, used, suffix, actual, bound, inv, bits, source, rest⟩
  · have waitRun := Zlib.Inflate.Proofs.FunctionalTrailer.CHECK_wait_cut E l current
      (by rw [ledger.checksum.1]; decide) (by rwa [waiting] at pull)
    have same := xrun_regs_eq waitRun observed
    have initial : current.ret = Z_OK := by rw [shape]; exact incoming
    have impossible : Z_OK = Z_STREAM_END := initial.symm.trans ((congrArg IL.ret same).trans ended)
    exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)

#print axioms CHECK_observed_END_wire

end Zlib.Inflate.Proofs.FunctionalTrailerWire
