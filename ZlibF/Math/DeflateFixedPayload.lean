import ZlibF.Proof.«trees.c.compress-match»
import ZlibF.Math.DeflateSymbolTrace

/-! # Fixed payload bits and the independent DEFLATE symbol grammar -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees Zlib.Trees.Proofs ZlibF.Spec
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- The actual fixed literal/length words are the independent canonical
codes, including END_BLOCK and every legal length symbol. -/
theorem fixed_literal_wire (k : Nat) (bound : k < 288) :
    codeBits fixedLiteralWords k = codeOf fixedLitLens k ∧ fixedLitLens.getD k 0 ≠ 0 := by
  have table : ∀ i : Fin 288,
      codeBits fixedLiteralWords i.val = codeOf fixedLitLens i.val ∧ fixedLitLens.getD i.val 0 ≠ 0 := by
    decide +kernel
  exact table ⟨k, bound⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The actual used fixed distance words are the independent canonical codes. -/
theorem fixed_distance_wire (k : Nat) (bound : k < 30) :
    codeBits fixedDistanceWords k = codeOf fixedDistLens k ∧ fixedDistLens.getD k 0 ≠ 0 := by
  have table : ∀ i : Fin 30,
      codeBits fixedDistanceWords i.val = codeOf fixedDistLens i.val ∧ fixedDistLens.getD i.val 0 ≠ 0 := by
    decide +kernel
  exact table ⟨k, bound⟩

/-- Fixed literal/length decoding retains every trailing bit suffix. -/
theorem fixed_literal_decode (k : Nat) (bound : k < 288) (suffix : List Bool) :
    decodeSym fixedLitLens (codeBits fixedLiteralWords k ++ suffix) = some (k, suffix) := by
  obtain ⟨wire, used⟩ := fixed_literal_wire k bound
  rw [wire]
  exact format_decode_code (kind := .litLen) (by decide +kernel) k used suffix

/-- Fixed distance decoding retains every trailing bit suffix. -/
theorem fixed_distance_decode (k : Nat) (bound : k < 30) (suffix : List Bool) :
    decodeSym fixedDistLens (codeBits fixedDistanceWords k ++ suffix) = some (k, suffix) := by
  obtain ⟨wire, used⟩ := fixed_distance_wire k bound
  rw [wire]
  exact format_decode_code (kind := .dist) (by decide +kernel) k used suffix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The writer's length remainder equals the independent extra-bit field.
Taking the transmitted low bits handles the zero-width length-258 case. -/
theorem length_payload_format (lc : Nat) (bound : lc < 256) :
    let k := lcodeN lc
    let width := extra_lbits_tab[k]!.toInt.toNat
    let rem := lc - base_length_tab[k]!.toInt.toNat
    let value := rem % 2 ^ width
    natBits rem width = natBits value width ∧ value < 2 ^ width ∧
      lengthExtras.getD k 0 = width ∧ lengthBases.getD k 0 + value = lc + 3 := by
  have table : ∀ i : Fin 256,
      let k := lcodeN i.val
      let width := extra_lbits_tab[k]!.toInt.toNat
      let rem := i.val - base_length_tab[k]!.toInt.toNat
      let value := rem % 2 ^ width
      natBits rem width = natBits value width ∧ value < 2 ^ width ∧
        lengthExtras.getD k 0 = width ∧ lengthBases.getD k 0 + value = i.val + 3 := by
    decide +kernel
  exact table ⟨lc, bound⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The writer uses distance-minus-one bases; the independent format uses
actual distances. Their extra widths and base offset agree. -/
theorem distance_payload_format (k : Nat) (bound : k < 30) :
    distExtras.getD k 0 = extra_dbits_tab[k]!.toInt.toNat ∧
      distBases.getD k 0 = base_dist_tab[k]!.toInt.toNat + 1 := by
  have table : ∀ i : Fin 30,
      distExtras.getD i.val 0 = extra_dbits_tab[i.val]!.toInt.toNat ∧
        distBases.getD i.val 0 = base_dist_tab[i.val]!.toInt.toNat + 1 := by
    decide +kernel
  exact table ⟨k, bound⟩


/-- One actual fixed-payload symbol prepends the independent grammar.
The history bound is the real back-reference rule. Self-overlap remains
handled by the independent bytewise copyBack operation. -/
theorem fixed_symbol_grammar (s : Symbol) (valid : s.Valid)
    (history : List UInt8) (back : s.distance ≤ history.length)
    (suffix rest : List Bool) (out : List UInt8)
    (continuation : Symbols fixedLitLens fixedDistLens [] (expandSymbol history s) suffix rest out) :
    Symbols fixedLitLens fixedDistLens [] history
      (payloadSymBits fixedLiteralWords fixedDistanceWords (s.distance, s.value) ++ suffix) rest out := by
  by_cases zero : s.distance = 0
  · simp only [payloadSymBits, zero, ite_true]
    exact Symbols.lit (fixed_literal_decode s.value (by have := valid.2; omega) suffix) valid.2
      (by simpa only [expandSymbol, zero, ite_true] using continuation)
  · let lk := lcodeN s.value
    let le := extra_lbits_tab[lk]!.toInt.toNat
    let lr := s.value - base_length_tab[lk]!.toInt.toNat
    let lv := lr % 2 ^ le
    let dk := dcodeN (s.distance - 1)
    let de := extra_dbits_tab[dk]!.toInt.toNat
    let dr := s.distance - 1 - base_dist_tab[dk]!.toInt.toNat
    have positive : 0 < s.distance := by omega
    have lkBound : lk < 29 := (length_payload_checked_fields s.value valid.2).1
    obtain ⟨dkBound, _extraLo, _extraHi, _baseLo, baseBound, distanceFit⟩ :=
      distance_payload_fields (s.distance - 1) (by have := valid.1; omega)
    obtain ⟨lengthBits, lengthFit, lengthWidth, lengthValue⟩ := length_payload_format s.value valid.2
    obtain ⟨distanceWidth, distanceBase⟩ := distance_payload_format dk dkBound
    have distanceValue : distBases.getD dk 0 + dr = s.distance := by
      rw [distanceBase]
      dsimp only [dr, dk]
      omega
    have normalize : payloadSymBits fixedLiteralWords fixedDistanceWords (s.distance, s.value) ++ suffix =
        codeBits fixedLiteralWords (lk + 257) ++ (natBits lv le ++
          (codeBits fixedDistanceWords dk ++ (natBits dr de ++ suffix))) := by
      simp only [payloadSymBits, zero, ite_false]
      change (codeBits fixedLiteralWords (lk + 257) ++ natBits lr le ++
        codeBits fixedDistanceWords dk ++ natBits dr de) ++ suffix = _
      rw [lengthBits]
      simp only [List.append_assoc]
      rfl
    rw [normalize]
    refine Symbols.copy (s := lk + 257) (d := dk) (xl := lv) (xd := dr)
      (r1 := natBits lv le ++ (codeBits fixedDistanceWords dk ++ (natBits dr de ++ suffix)))
      (r2 := codeBits fixedDistanceWords dk ++ (natBits dr de ++ suffix))
      (r3 := natBits dr de ++ suffix) (r4 := suffix)
      (fixed_literal_decode (lk + 257) (by omega) _) (by omega) (by omega) ?_
      (fixed_distance_decode dk dkBound _) (by omega) ?_ ?_ ?_
    · rw [show lk + 257 - 257 = lk by omega, lengthWidth]
      exact readBits_natBits le lv _ lengthFit
    · rw [distanceWidth]
      exact readBits_natBits de dr _ distanceFit
    · simp only [List.nil_append]
      omega
    · rw [show lk + 257 - 257 = lk by omega, lengthValue, distanceValue]
      simpa only [expandSymbol, zero, ite_false] using continuation

/-- A real logical symbol trace prepends the independent fixed grammar
on every continuation. Both literal bytes and overlapping matches retain
their actual input meaning. -/
theorem fixed_trace_grammar {input : Nat → UInt8} {base : Nat} {xs : List Symbol}
    (trace : Trace input base xs) :
    ∀ suffix rest out,
      Symbols fixedLitLens fixedDistLens [] (inputPrefix input (base + represented xs)) suffix rest out →
      Symbols fixedLitLens fixedDistLens [] (inputPrefix input base)
        (xs.flatMap (fun s => payloadSymBits fixedLiteralWords fixedDistanceWords (s.distance, s.value)) ++ suffix) rest out := by
  induction trace with
  | empty => intro suffix rest out continuation; exact continuation
  | @snoc xs s trace meaning ih =>
    intro suffix rest out continuation
    have copied := meaning_expands meaning
    have back : s.distance ≤ (inputPrefix input (base + represented xs)).length := by
      rw [input_prefix_length]
      by_cases zero : s.distance = 0
      · omega
      · have matching := meaning.2
        rw [ite_eq_right zero] at matching
        exact matching.1
    have tail : Symbols fixedLitLens fixedDistLens [] (expandSymbol (inputPrefix input (base + represented xs)) s)
        suffix rest out := by
      rw [copied]
      simpa only [represented_snoc, Nat.add_assoc] using continuation
    have symbol := fixed_symbol_grammar s meaning.1 _ back suffix rest out tail
    have result := ih _ _ _ symbol
    simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using result

/-- The complete fixed payload, including END_BLOCK, is accepted by the
independent grammar and reproduces the exact input prefix for every suffix. -/
theorem fixed_payload_grammar {input : Nat → UInt8} {base : Nat} {xs : List Symbol}
    (trace : Trace input base xs) (suffix : List Bool) :
    Symbols fixedLitLens fixedDistLens [] (inputPrefix input base)
      ((xs.flatMap (fun s => payloadSymBits fixedLiteralWords fixedDistanceWords (s.distance, s.value)) ++
        codeBits fixedLiteralWords 256) ++ suffix) suffix (inputPrefix input (base + represented xs)) := by
  rw [List.append_assoc]
  exact fixed_trace_grammar trace _ _ _ (Symbols.eob (fixed_literal_decode 256 (by decide) suffix))

end Zlib.Trees.Proofs.Out
