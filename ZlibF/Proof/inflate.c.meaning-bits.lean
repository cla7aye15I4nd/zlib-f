import ZlibF.Proof.«inflate.c.meaning-loop»
import ZlibF.Proof.«inflate.c.bits-complete»
import ZlibF.Proof.«inflate.c.meaning-wrap-steps»

/-!
# inflate.c: pulling input bits keeps the loop meaning

`NEEDBITS(n)` moves whole input bytes from `next` into the bit buffer. The
parse does not move: the bytes pulled become held bits. `LoopMatches.needbits`
states this for every stage whose facts do not depend on the bit buffer
beyond `HeldBits` (`BitsFree`), such as the position after the header bits
of a stored block. The other body positions bound the held bits and are
handled by their own mode proofs.
-/

namespace Zlib.Inflate.Proofs.MeaningBits
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Held bits are the low bits of `hold` -/

/-- The number whose bits, least significant first, are `held`. -/
def heldValue (held : List Bool) : Nat :=
  (held.zipIdx.map fun (b, i) => if b then 2 ^ i else 0).sum

theorem zipIdx_sum (l : List Bool) :
    ∀ k, ((l.zipIdx k).map fun (b, i) => if b then 2 ^ i else 0).sum = 2 ^ k * heldValue l := by
  induction l with
  | nil => intro k; simp [heldValue]
  | cons b t ih =>
    intro k
    have zero := ih 1
    have succ := ih (k + 1)
    simp only [heldValue, List.zipIdx_cons, List.map_cons, List.sum_cons] at zero succ ⊢
    rw [succ, ih 1]
    cases b <;> simp [Nat.pow_succ, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm] <;>
      simp only [heldValue, Nat.mul_assoc]

theorem heldValue_cons (b : Bool) (t : List Bool) :
    heldValue (b :: t) = (if b then 1 else 0) + 2 * heldValue t := by
  have := zipIdx_sum t 1
  simp only [heldValue, List.zipIdx_cons, List.map_cons, List.sum_cons] at this ⊢
  rw [this]

theorem natBits_heldValue : ∀ held : List Bool, natBits held.length (heldValue held) = held
  | [] => rfl
  | b :: t => by
    rw [List.length_cons, heldValue_cons]
    simp only [natBits]
    have div : ((if b then 1 else 0) + 2 * heldValue t) / 2 = heldValue t := by
      cases b <;> simp <;> omega
    rw [div, natBits_heldValue t]
    cases b <;> simp

theorem heldValue_natBits : ∀ k n, heldValue (natBits k n) = n % 2 ^ k
  | 0, n => by simp [natBits, heldValue, Nat.mod_one]
  | k + 1, n => by
    simp only [natBits]
    rw [heldValue_cons, heldValue_natBits k (n / 2), Nat.pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one n with bit | bit <;> simp [bit]

theorem HeldBits.eq_natBits {s : InflateState} {held : List Bool} (bits : HeldBits s held) :
    held = natBits s.bits.toNat s.hold.toNat := by
  obtain ⟨length, value⟩ := bits
  rw [← length, value]
  exact (natBits_heldValue held).symm

theorem HeldBits.of_natBits {s : InflateState} (small : s.hold.toNat < 2 ^ s.bits.toNat) :
    HeldBits s (natBits s.bits.toNat s.hold.toNat) := by
  refine ⟨natBits_length _ _, ?_⟩
  change s.hold.toNat = heldValue _
  rw [heldValue_natBits, Nat.mod_eq_of_lt small]

/-! ## The input cursor moves forward -/

theorem separate_advance {p : BPtr} {n : Nat} {q : BPtr} {m j : Nat} (sep : Separate p n q m)
    (le : j ≤ m) : Separate p n (inputAdvance q j) (m - j) := by
  rcases sep with zero | zero | sep
  · exact Or.inl zero
  · exact Or.inr (Or.inl (by omega))
  · right; right
    cases p with
    | null => trivial
    | ref r i =>
      cases q with
      | null => trivial
      | ref s o =>
        simp only [inputAdvance] at sep ⊢
        rcases sep with ne | before | after
        · exact Or.inl ne
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))

#print axioms HeldBits.eq_natBits
#print axioms HeldBits.of_natBits

/-! ## Pulling bits -/

/-- The stage facts of `stage` survive replacing the bit buffer by one whose
size satisfies `ok`: the stage reads the bit buffer only through `HeldBits`
and a bound on its size. -/
def BitsFree (f : LoopFrame) (stage : WrapStage) (ok : Nat → Prop) : Prop :=
  ∀ (h : Heap) (s : InflateState) (checked : List UInt8) (hold : UInt64) (bits : UInt32),
    ok bits.toNat →
    LoopStageMatches h s f checked stage → WrapMatches h s f.wrap f.configured f.dict stage →
    LoopStageMatches h { s with hold := hold, bits := bits } f checked stage ∧
      WrapMatches h { s with hold := hold, bits := bits } f.wrap f.configured f.dict stage

/-- `NEEDBITS(n)` in the loop: it returns with at least `n` bits or leaves
with all input read; the parse position does not move, the `j` pulled bytes
become held bits, and the loop meaning holds for the new registers whenever
the new bit count satisfies `ok` and the stage tolerates such a bit buffer. -/
theorem LoopMatches.needbits {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    (loop : LoopMatches c f h l)
    {ok : Nat → Prop}
    (free : ∀ zs s checked stage, c.st = some (.tab zs) → h.istates zs = some s →
      LoopStageMatches h (loopState s l) f checked stage → BitsFree f stage ok)
    (n : UInt32) (small : n.toNat ≤ 32) :
    ∃ result l' j, runX (NEEDBITS n) l h = .ok ((result, l'), h) ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } ∧
      loopRead l' = loopRead l + j ∧ l'.bits.toNat = l.bits.toNat + 8 * j ∧
      (result = .ok () → n.toNat ≤ l'.bits.toNat) ∧
      (result = .error Ex.leave → l'.have_ = 0 ∧ l'.bits.toNat < n.toNat) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧
      (ok l'.bits.toNat → LoopMatches c f h l') := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  obtain ⟨result, l', j, run, jle, binv', streamEq, bitsCount, shape, bitsBound, _, enough, empty,
    kinds, nextEq⟩ := NEEDBITS_run_cursor binv n (by omega)
  have inEq : l'.in_ = l.in_ := by rw [shape]
  have outEq : l'.out_ = l.out_ := by rw [shape]
  have leftEq : l'.left = l.left := by rw [shape]
  have putEq' : l'.put = l.put := by rw [shape]
  have retEq : l'.ret = l.ret := by rw [shape]
  have haveOld := binv.have_eq
  have haveNew := binv'.have_eq
  simp only [List.length_drop, loopRead] at haveOld haveNew jle
  have readEq : loopRead l' = loopRead l + j := by
    simp only [loopRead, inEq]
    omega
  have pendEq : loopPending l' = loopPending l := by simp only [loopPending, outEq, leftEq]
  refine ⟨result, l', j, run, shape, readEq, bitsCount, enough, fun leave => ⟨?_, (empty leave).2.2⟩,
    kinds, bitsBound, fun okBits => ?_⟩
  · have := (empty leave).2.1
    exact this
  have heldEq := HeldBits.eq_natBits heldBits
  have pulled : natBits l'.bits.toNat l'.hold.toNat =
      natBits l.bits.toNat l.hold.toNat ++ bytesBits ((f.inp.drop (loopRead l)).take j) := by
    have split : bytesBits (f.inp.drop (loopRead l)) =
        bytesBits ((f.inp.drop (loopRead l)).take j) ++ bytesBits ((f.inp.drop (loopRead l)).drop j) := by
      rw [← bytesBits_append, List.take_append_drop]
    simp only [stream] at streamEq
    rw [split, ← List.append_assoc] at streamEq
    exact List.append_cancel_right streamEq
  have freeStage := free zs s _ stage st hs stageM
  have transferred := freeStage h (loopState s l) _ l'.hold l'.bits okBits stageM wrapM
  refine ⟨zs, s, callOut, consumed, natBits l'.bits.toNat l'.hold.toNat, stage, st, hs,
    retEq.trans retOk, config, by rw [inEq]; omega, by rw [inEq]; exact inLen, ?_, by rw [leftEq, outEq]; exact leftLe,
    by rw [pendEq]; exact pendLe, by rw [putEq']; exact putEq, outBytes, by rw [putEq', leftEq]; exact writable,
    ?_, by rw [putEq', leftEq]; exact sepWin, ?_, ?_, HeldBits.of_natBits binv'.hold_lt, parsed, ?_, ?_,
    outputEq⟩
  · rw [readEq, ← List.drop_drop]
    exact binv'
  · rw [putEq', leftEq, nextEq]
    have := separate_advance (j := j) sepIn (by omega)
    rwa [show l.have_.toNat - j = l'.have_.toNat by omega] at this
  · rw [nextEq]
    have := separate_advance (j := j) sepOutIn (by omega)
    rwa [show l.have_.toNat - j = l'.have_.toNat by omega] at this
  · have takeSplit : f.inp.take (loopRead l + j) =
        f.inp.take (loopRead l) ++ (f.inp.drop (loopRead l)).take j := List.take_add ..
    simp only [loopState] at heldEq
    rw [readEq, takeSplit, ← List.append_assoc, bytesToBits_append', bitsEq, heldEq, pulled,
      bytesBits_eq_bytesToBits]
    simp only [List.append_assoc]
  · rw [pendEq]
    exact transferred.1
  · exact transferred.2

/-- Positions after the header bits of a stored block read the bit buffer
only through `HeldBits`. -/
theorem bitsFree_storedHeader (f : LoopFrame) (header : List UInt8) (out : List UInt8)
    (final : Bool) (ok : Nat → Prop) : BitsFree f (.body header ⟨out, final, .storedHeader⟩) ok := by
  intro h s checked hold bits _ stageM wrapM
  exact ⟨stageM, wrapM⟩

#print axioms LoopMatches.needbits

/-- A trailer position tolerates any bit buffer of at most 32 bits. -/
theorem bitsFree_trailer (f : LoopFrame) (header out bytes : List UInt8) :
    BitsFree f (.trailer header out bytes) (· ≤ 32) := by
  intro h s checked hold bits small stageM wrapM
  obtain ⟨flags, width, check, length, _⟩ := wrapM
  exact ⟨stageM, flags, width, check, length, small⟩

#print axioms bitsFree_trailer

end Zlib.Inflate.Proofs.MeaningBits
