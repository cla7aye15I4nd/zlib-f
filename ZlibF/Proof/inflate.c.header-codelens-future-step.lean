import ZlibF.Proof.«inflate.c.header-waiting-payload-interface»
namespace Zlib.Inflate.Proofs.CodeLensFuture
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CodeLensCompletion
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Enough current bits determine the same value as any valid future
extension; the unconsumed future is never read from the current heap. -/
theorem read_current_of_future {width value : Nat} {current future rest : List Bool}
    (parsed : readBits width (current ++ future) = some (value, rest)) (available : width ≤ current.length) :
    ∃ tail, readBits width current = some (value, tail) ∧ tail ++ future = rest := by
  obtain ⟨actual, tail, read, _bound, _source⟩ := ZlibF.Math.InflateDecode.read_total width current available
  have extended := CumulativeTableBoundary.readBits_append read future
  have pair := Option.some.inj (extended.symm.trans parsed)
  have same := congrArg Prod.fst pair
  dsimp only at same
  subst actual
  exact ⟨tail, read, congrArg Prod.snd pair⟩

theorem needbits_wait_of_short {h : Heap} {l : IL} {bs : List UInt8} {width : UInt32}
    (B : BitInv h l bs) (small : width.toNat ≤ 49) (short : (stream l bs).length < width.toNat) :
    ∃ regs used, runX (NEEDBITS width) l h = .ok ((.error Ex.leave, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs := by
  obtain ⟨result, regs, used, actual, bound, inv, source, _count, _shape, _max, _same, full, _wait, kinds, _cursor⟩ := NEEDBITS_run_cursor B width small
  have leaves : result = .error Ex.leave := by
    rcases kinds with normal | leaves
    · have enough := full normal
      have sourceLength := congrArg List.length source
      have length := tcStream_length inv
      omega
    · exact leaves
  exact ⟨regs, used, by rwa [leaves] at actual, bound, inv, source⟩

/-- An actual ordinary lookup on a valid future grammar either waits or
selects that grammar's exact symbol. It tests selected-entry width, not
mandatory root-width availability. -/
theorem lookup_future
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState} {l : IL} {bs : List UInt8}
    {alphabet : List Nat} {symbol : Nat} {future rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref (.istate_codes zs) 0)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (B : BitInv h l bs) (decoded : decodeSym alphabet (stream l bs ++ future) = some (symbol, rest)) :
    (∃ regs, runX (lookup1 c false) l h = .ok ((.error Ex.leave, regs), h)) ∨
    (∃ regs used, runX (lookup1 c false) l h = .ok ((.ok (), regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs ∧
      regs.here.op = 0 ∧ regs.here.val.toNat = symbol ∧ regs.here.bits.toNat ≤ 7 ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
      rest = (stream regs (bs.drop used)).drop regs.here.bits.toNat ++ future) := by
  have get := CodeRef.get_istate_codes hs
  obtain ⟨result, regs, used, actual, _one, bound, inv, source, _shape, _bits, _lower, width, kinds, fitted, _empty, _next, _count⟩ :=
    lookup1_codes_run_cursor hc hs pointer get contents.safe B
  rcases kinds with normal | leave
  · rw [normal] at actual
    have ordinaryRoot := decoded_root_ordinary contents decoded
    obtain ⟨_heap, cell, _fields⟩ := lookup1_codes_contents hc hs pointer get contents B actual
    obtain ⟨entry, entryGet, op⟩ := ordinaryRoot _ (Nat.mod_lt _ (Nat.two_pow_pos _))
    have sameEntry : entry = regs.here := Option.some.inj (entryGet.symm.trans cell)
    have ordinary : regs.here.op = 0 := by rw [← sameEntry]; exact op
    obtain ⟨actualSymbol, _small, value, _width, actualDecode⟩ := lookup1_codes_symbol hc hs pointer get contents.toCodeLengthMeaning B actual ordinary
    have extended := ZlibF.Spec.Proofs.ext_acceptable contents.acceptable _ _ _ future actualDecode
    have pair := Option.some.inj (extended.symm.trans decoded)
    have sameSymbol : actualSymbol = symbol := congrArg Prod.fst pair
    rw [sameSymbol] at value
    have restEq := congrArg Prod.snd pair
    have root := contents.safe.2.1
    refine Or.inr ⟨regs, used, actual, bound, inv, source, ordinary, value, by omega, fitted normal, ?_⟩
    rw [source]
    exact restEq.symm
  · exact Or.inl ⟨regs, by rwa [leave] at actual⟩

#print axioms read_current_of_future
#print axioms needbits_wait_of_short
#print axioms lookup_future
end Zlib.Inflate.Proofs.CodeLensFuture

namespace Zlib.Inflate.Proofs.CodeLensFuture
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.CodeLensCompletion
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem previous_repeat_future
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {value : Nat} {future rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat) (nonempty : 1 ≤ s.«have».toNat)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7) (fitted : here.bits.toNat ≤ l.bits.toNat)
    (readExtra : readBits 2 ((stream l bs).drop here.bits.toNat ++ future) = some (value, rest))
    (room : s.«have».toNat + (3 + value) ≤ s.nlen.toNat + s.ndist.toNat) :
    (∃ regs, runX (clRepeat16 c here) l h = .ok ((.error Ex.leave, regs), h)) ∨
    (∃ regs state used currentRest,
      runX (clRepeat16 c here) l h = .ok ((.ok false, regs), setI h zs state) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧ stream regs (bs.drop used) = currentRest ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (3 + value) ((actualLengthPrefix s).getLastD 0) ∧
      currentRest ++ future = rest) := by
  by_cases enough : 2 ≤ ((stream l bs).drop here.bits.toNat).length
  · obtain ⟨currentRest, parsed, remaining⟩ := read_current_of_future readExtra enough
    obtain ⟨regs, state, used, run, _one, bound, inv, source, _frame, _size, _count, written⟩ :=
      previous_repeat_complete hr hc hz hs size nlen ndist haveBound nonempty B here width fitted parsed room
    exact Or.inr ⟨regs, state, used, currentRest, run, bound, inv, source, written, remaining⟩
  · have total : (here.bits.toUInt32 + 2).toNat = here.bits.toNat + 2 := by
      rw [UInt32.toNat_add, UInt8.toNat_toUInt32, show (2 : UInt32).toNat = 2 by decide, Nat.mod_eq_of_lt (by omega)]
    have length := tcStream_length B
    obtain ⟨regs, _used, need, _bound, _inv, _source⟩ := needbits_wait_of_short B
      (by rw [total]; omega) (by rw [total]; simp only [List.length_drop] at enough; omega)
    have drop : runX (clNeedDrop here 2) l h = .ok ((.error Ex.leave, regs), h) := by
      unfold clNeedDrop
      rw [runX_bind, need]
    refine Or.inl ⟨regs, ?_⟩
    unfold clRepeat16
    rw [runX_bind, drop]

theorem zero_repeat_future
    {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState} {l : IL} {bs : List UInt8}
    {value : Nat} {future rest : List Bool}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (B : BitInv h l bs) (here : Code) (extra base : UInt32)
    (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7) (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11)
    (fitted : here.bits.toNat ≤ l.bits.toNat)
    (readExtra : readBits extra.toNat ((stream l bs).drop here.bits.toNat ++ future) = some (value, rest))
    (room : s.«have».toNat + (base.toNat + value) ≤ s.nlen.toNat + s.ndist.toNat) :
    (∃ regs, runX (do clZeroSetup here extra base; clRepeatFinish c) l h = .ok ((.error Ex.leave, regs), h)) ∨
    (∃ regs state used currentRest,
      runX (do clZeroSetup here extra base; clRepeatFinish c) l h = .ok ((.ok false, regs), setI h zs state) ∧
      used ≤ bs.length ∧ BitInv (setI h zs state) regs (bs.drop used) ∧ stream regs (bs.drop used) = currentRest ∧
      actualLengthPrefix state = actualLengthPrefix s ++ List.replicate (base.toNat + value) 0 ∧ currentRest ++ future = rest) := by
  by_cases enough : extra.toNat ≤ ((stream l bs).drop here.bits.toNat).length
  · obtain ⟨currentRest, parsed, remaining⟩ := read_current_of_future readExtra enough
    obtain ⟨regs, state, used, run, _one, bound, inv, source, _frame, _size, _count, written⟩ :=
      zero_repeat_complete hc hs size nlen ndist haveBound B here extra base width extraBound baseLo baseHi fitted parsed room
    exact Or.inr ⟨regs, state, used, currentRest, run, bound, inv, source, written, remaining⟩
  · have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
      rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    have length := tcStream_length B
    obtain ⟨regs, _used, need, _bound, _inv, _source⟩ := needbits_wait_of_short B
      (by rw [total]; omega) (by rw [total]; simp only [List.length_drop] at enough; omega)
    have setup : runX (clZeroSetup here extra base) l h = .ok ((.error Ex.leave, regs), h) := by
      unfold clZeroSetup
      rw [runX_bind, need]
    exact Or.inl ⟨regs, by rw [runX_bind, setup]⟩

#print axioms previous_repeat_future
#print axioms zero_repeat_future
end Zlib.Inflate.Proofs.CodeLensFuture
