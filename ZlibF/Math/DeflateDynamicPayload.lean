import ZlibF.Math.DeflateFixedPayload

/-! # Dynamic stored words refine the independent DEFLATE symbol grammar -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees Zlib.Trees.Proofs ZlibF.Spec
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Decoding facts about stored words, not contracts of translated calls.
The engine obtains them from actual canonical construction and its frame. -/
structure SymbolDecodeData (lt dt : Nat → UInt16 × UInt16) (litLens distLens : List Nat)
    (xs : List Symbol) : Prop where
  literal : ∀ s ∈ xs, ∀ suffix,
    decodeSym litLens (codeBits lt (s.literalKey lcodeN) ++ suffix) = some (s.literalKey lcodeN, suffix)
  distance : ∀ s ∈ xs, s.distance ≠ 0 → ∀ suffix,
    decodeSym distLens (codeBits dt (dcodeN (s.distance - 1)) ++ suffix) = some (dcodeN (s.distance - 1), suffix)
  end_marker : ∀ suffix, decodeSym litLens (codeBits lt 256 ++ suffix) = some (256, suffix)

/-- One actual dynamic word sequence prepends the independent grammar,
including length/distance extra bits and overlapping back references. -/
theorem dynamic_symbol_grammar (lt dt : Nat → UInt16 × UInt16) (litLens distLens : List Nat)
    (s : Symbol) (valid : s.Valid)
    (literalDecode : ∀ suffix, decodeSym litLens (codeBits lt (s.literalKey lcodeN) ++ suffix) = some (s.literalKey lcodeN, suffix))
    (distanceDecode : s.distance ≠ 0 → ∀ suffix,
      decodeSym distLens (codeBits dt (dcodeN (s.distance - 1)) ++ suffix) = some (dcodeN (s.distance - 1), suffix))
    (history : List UInt8) (back : s.distance ≤ history.length)
    (suffix rest : List Bool) (out : List UInt8)
    (continuation : Symbols litLens distLens [] (expandSymbol history s) suffix rest out) :
    Symbols litLens distLens [] history
      (payloadSymBits lt dt (s.distance, s.value) ++ suffix) rest out := by
  by_cases zero : s.distance = 0
  · simp only [payloadSymBits, zero, ite_true]
    exact Symbols.lit (by simpa only [Symbol.literalKey, zero, ite_true] using literalDecode suffix) valid.2
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
    have normalize : payloadSymBits lt dt (s.distance, s.value) ++ suffix =
        codeBits lt (lk + 257) ++ (natBits lv le ++
          (codeBits dt dk ++ (natBits dr de ++ suffix))) := by
      simp only [payloadSymBits, zero, ite_false]
      change (codeBits lt (lk + 257) ++ natBits lr le ++
        codeBits dt dk ++ natBits dr de) ++ suffix = _
      rw [lengthBits]
      simp only [List.append_assoc]
      rfl
    rw [normalize]
    refine Symbols.copy (s := lk + 257) (d := dk) (xl := lv) (xd := dr)
      (r1 := natBits lv le ++ (codeBits dt dk ++ (natBits dr de ++ suffix)))
      (r2 := codeBits dt dk ++ (natBits dr de ++ suffix))
      (r3 := natBits dr de ++ suffix) (r4 := suffix)
      (by simpa only [Symbol.literalKey, zero, ite_false] using literalDecode _) (by omega) (by omega) ?_
      (distanceDecode zero _) (by omega) ?_ ?_ ?_
    · rw [show lk + 257 - 257 = lk by omega, lengthWidth]
      exact readBits_natBits le lv _ lengthFit
    · rw [distanceWidth]
      exact readBits_natBits de dr _ distanceFit
    · simp only [List.nil_append]
      omega
    · rw [show lk + 257 - 257 = lk by omega, lengthValue, distanceValue]
      simpa only [expandSymbol, zero, ite_false] using continuation


/-- A real input trace and the actual stored-code decoding facts prepend
the independent dynamic symbol grammar on every continuation. -/
theorem dynamic_trace_grammar (lt dt : Nat → UInt16 × UInt16) (litLens distLens : List Nat)
    {input : Nat → UInt8} {base : Nat} {xs : List Symbol}
    (trace : Trace input base xs) (data : SymbolDecodeData lt dt litLens distLens xs) :
    ∀ suffix rest out,
      Symbols litLens distLens [] (inputPrefix input (base + represented xs)) suffix rest out →
      Symbols litLens distLens [] (inputPrefix input base)
        (xs.flatMap (fun s => payloadSymBits lt dt (s.distance, s.value)) ++ suffix) rest out := by
  revert data
  induction trace with
  | empty => intro data suffix rest out continuation; exact continuation
  | @snoc xs s trace meaning ih =>
    intro data suffix rest out continuation
    have earlier : SymbolDecodeData lt dt litLens distLens xs := by
      exact ⟨fun t member => data.literal t (List.mem_append_left [s] member),
        fun t member => data.distance t (List.mem_append_left [s] member), data.end_marker⟩
    have member : s ∈ xs ++ [s] := by simp
    have copied := meaning_expands meaning
    have back : s.distance ≤ (inputPrefix input (base + represented xs)).length := by
      rw [input_prefix_length]
      by_cases zero : s.distance = 0
      · omega
      · have matching := meaning.2
        rw [ite_eq_right zero] at matching
        exact matching.1
    have tail : Symbols litLens distLens [] (expandSymbol (inputPrefix input (base + represented xs)) s)
        suffix rest out := by
      rw [copied]
      simpa only [represented_snoc, Nat.add_assoc] using continuation
    have symbol := dynamic_symbol_grammar lt dt litLens distLens s meaning.1
      (data.literal s member) (data.distance s member) _ back suffix rest out tail
    have result := ih earlier _ _ _ symbol
    simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using result

/-- The entire dynamic payload, including the actual stored end marker,
decodes to the exact logical input prefix for every trailing suffix. -/
theorem dynamic_payload_grammar (lt dt : Nat → UInt16 × UInt16) (litLens distLens : List Nat)
    {input : Nat → UInt8} {base : Nat} {xs : List Symbol}
    (trace : Trace input base xs) (data : SymbolDecodeData lt dt litLens distLens xs) (suffix : List Bool) :
    Symbols litLens distLens [] (inputPrefix input base)
      ((xs.flatMap (fun s => payloadSymBits lt dt (s.distance, s.value)) ++ codeBits lt 256) ++ suffix)
      suffix (inputPrefix input (base + represented xs)) := by
  rw [List.append_assoc]
  exact dynamic_trace_grammar lt dt litLens distLens trace data _ _ _ (Symbols.eob (data.end_marker suffix))

end Zlib.Trees.Proofs.Out
