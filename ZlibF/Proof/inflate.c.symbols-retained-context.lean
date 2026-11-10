import ZlibF.Proof.«inflate.c.slow-protocol-dictionary»
import ZlibF.Proof.«inflate.c.global-token-composition»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C ZlibF.Spec Zlib.Inflate.Proofs.SlowInputFragment ZlibF.Math.LZ77History
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Move a complete logical output prefix into a retained physical
dictionary. Every format distance is at most 32768, so trimming that prior
history preserves every copied byte and the original Symbols grammar. -/
theorem symbols_retained_context
    {L D : List Nat} {dict past history output : List UInt8} {input rest : List Bool}
    (parsed : Symbols L D dict (past ++ history) input rest output) :
    ∃ target, output = past ++ target ∧
      Symbols L D ((dict ++ past).drop ((dict ++ past).length - 32768)) history input rest target := by
  have convert : ∀ (original : List UInt8) (bits tail : List Bool) (final : List UInt8),
      Symbols L D dict original bits tail final →
      ∀ current, original = past ++ current →
      ∃ target, final = past ++ target ∧
        Symbols L D ((dict ++ past).drop ((dict ++ past).length - 32768)) current bits tail target := by
    intro original bits tail final symbols
    induction symbols with
    | eob decoded =>
      intro current equality
      exact ⟨current, equality, .eob decoded⟩
    | @lit h inp r tail symbol out decoded small continuation ih =>
      intro current equality
      obtain ⟨target, final, grammar⟩ := ih (current ++ [symbol.toUInt8]) (by rw [equality, List.append_assoc])
      exact ⟨target, final, .lit decoded small grammar⟩
    | @copy h inp r1 r2 r3 r4 tail symbol distance extraLength extraDistance out decoded lower upper
        readLength decodedDistance distanceBound readDistance fits continuation ih =>
      intro current equality
      let parsedCopy : CopySyntax L D := ⟨inp, r1, r2, r3, r4, symbol, distance, extraLength, extraDistance,
        decoded, lower, upper, readLength, decodedDistance, distanceBound, readDistance⟩
      have bounds := parsedCopy.distance_bounds
      change 1 ≤ distBases.getD distance 0 + extraDistance ∧
        distBases.getD distance 0 + extraDistance ≤ 32768 at bounds
      let saved := (dict ++ past).drop ((dict ++ past).length - 32768)
      have retainedFits : distBases.getD distance 0 + extraDistance ≤ saved.length + current.length := by
        rw [equality] at fits
        dsimp only [saved]
        simp only [List.length_drop, List.length_append] at fits ⊢
        omega
      have copied := retained_history_agrees dict past current saved
        (distBases.getD distance 0 + extraDistance) (lengthBases.getD (symbol - 257) 0 + extraLength)
        (List.drop_suffix _ _) (by omega) retainedFits
      obtain ⟨target, final, grammar⟩ := ih
        (copyBack saved (distBases.getD distance 0 + extraDistance)
          (lengthBases.getD (symbol - 257) 0 + extraLength) current)
        (by rw [equality]; exact copied)
      have grammarFits : extraDistance + distBases.getD distance 0 ≤ (saved ++ current).length := by
        rw [List.length_append]
        omega
      exact ⟨target, final, .copy decoded lower upper readLength decodedDistance distanceBound readDistance
        grammarFits grammar⟩
  exact convert _ _ _ _ parsed history rfl

/-- The actual retained-window grammar also reconstructs the full logical
history. This direction does not require a complete future source or an
expected output: it is a structural implication between original grammars. -/
theorem symbols_expand_retained_context
    {L D : List Nat} {dict past history output : List UInt8} {input rest : List Bool}
    (parsed : Symbols L D ((dict ++ past).drop ((dict ++ past).length - 32768)) history input rest output) :
    Symbols L D dict (past ++ history) input rest (past ++ output) := by
  induction parsed with
  | eob decoded => exact .eob decoded
  | lit decoded small continuation ih =>
    exact .lit decoded small (by simpa only [List.append_assoc] using ih)
  | @copy h inp r1 r2 r3 r4 tail symbol distance extraLength extraDistance out decoded lower upper
      readLength decodedDistance distanceBound readDistance fits continuation ih =>
    let parsedCopy : CopySyntax L D := ⟨inp, r1, r2, r3, r4, symbol, distance, extraLength, extraDistance,
      decoded, lower, upper, readLength, decodedDistance, distanceBound, readDistance⟩
    have positive := parsedCopy.distance_bounds.1
    change 1 ≤ distBases.getD distance 0 + extraDistance at positive
    have retainedFits : distBases.getD distance 0 + extraDistance ≤
        ((dict ++ past).drop ((dict ++ past).length - 32768)).length + h.length := by
      simpa only [List.length_append, Nat.add_comm] using fits
    have copied := retained_history_agrees dict past h
      ((dict ++ past).drop ((dict ++ past).length - 32768))
      (distBases.getD distance 0 + extraDistance) (lengthBases.getD (symbol - 257) 0 + extraLength)
      (List.drop_suffix _ _) (by omega) retainedFits
    apply Symbols.copy decoded lower upper readLength decodedDistance distanceBound readDistance
    · simp only [List.length_drop, List.length_append] at fits ⊢
      omega
    · rw [copied]
      exact ih

/-- The target of the retained parser is the exact new-output suffix of
the independently decoded whole output. This is the handoff used by the
actual fast loop's writtenBytes history. -/
theorem symbols_retained_target
    {L D : List Nat} {dict past history output : List UInt8} {input rest : List Bool}
    (parsed : Symbols L D dict (past ++ history) input rest output) :
    past <+: output ∧
      Symbols L D ((dict ++ past).drop ((dict ++ past).length - 32768)) history input rest
        (output.drop past.length) := by
  obtain ⟨target, equality, grammar⟩ := symbols_retained_context parsed
  rw [equality]
  exact ⟨List.prefix_append _ _, by simpa only [List.drop_left] using grammar⟩

#print axioms symbols_retained_context
#print axioms symbols_expand_retained_context
#print axioms symbols_retained_target
end Zlib.Inflate.Proofs.FunctionalEpoch
