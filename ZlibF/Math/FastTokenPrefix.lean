import ZlibF.Proof.Format.Token
import ZlibF.Proof.«inftrees.c.decode.semantics»
import ZlibF.Math.«code-length-prefix»

namespace ZlibF.Math.FastTokenPrefix
open ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- If the independently decoded code word fits the supplied prefix,
the independent decoder already returns that same symbol there. This
requires no table or prefix-free hypothesis. -/
theorem decodeSym_restrict {L : List Nat} {available future rest : List Bool} {symbol : Nat}
    (decoded : decodeSym L (available ++ future) = some (symbol, rest))
    (fits : L.getD symbol 0 ≤ available.length) :
    decodeSym L available = some (symbol, available.drop (L.getD symbol 0)) ∧
      rest = available.drop (L.getD symbol 0) ++ future := by
  have details := Zlib.Inftrees.Proofs.decoded_symbol_prefix decoded
  have word : codeOf L symbol <+: available := List.prefix_of_prefix_length_le details.2.2.1
    (List.prefix_append available future) (by simpa only [codeOf, natToBitsMSB_length] using fits)
  unfold decodeSym at decoded ⊢
  cases found : (List.range L.length).find? (fun a => L.getD a 0 != 0 && (codeOf L a).isPrefixOf (available ++ future)) with
  | none => simp only [found] at decoded; cases decoded
  | some selected =>
    simp only [found, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨rfl, rfl⟩ := decoded
    obtain ⟨tested, earlier, later, split, excluded⟩ := List.find?_eq_some_iff_append.mp found
    have selectedTest : (L.getD selected 0 != 0 && (codeOf L selected).isPrefixOf available) = true := by
      simp only [Bool.and_eq_true, bne_iff_ne]
      exact ⟨details.2.1, List.isPrefixOf_iff_prefix.mpr word⟩
    have localFound : (List.range L.length).find? (fun a => L.getD a 0 != 0 && (codeOf L a).isPrefixOf available) = some selected := by
      apply List.find?_eq_some_iff_append.mpr
      refine ⟨selectedTest, earlier, later, split, ?_⟩
      intro a member
      have forbidden := excluded a member
      cases accepted : (L.getD a 0 != 0 && (codeOf L a).isPrefixOf available) with
      | false => rfl
      | true =>
        have acceptedFields : (L.getD a 0 != 0) = true ∧ (codeOf L a).isPrefixOf available = true := by
          simpa only [Bool.and_eq_true] using accepted
        have extended : (L.getD a 0 != 0 && (codeOf L a).isPrefixOf (available ++ future)) = true := by
          rw [Bool.and_eq_true]
          exact ⟨acceptedFields.1, List.isPrefixOf_iff_prefix.mpr
            ((List.isPrefixOf_iff_prefix.mp acceptedFields.2).trans (List.prefix_append available future))⟩
        rw [extended] at forbidden
        contradiction
    rw [localFound]
    exact ⟨rfl, List.drop_append_of_le_length fits⟩

/-- Fixed-width independent reads also restrict exactly to the supplied
prefix as soon as their whole width is present. -/
theorem readBits_restrict {n value : Nat} {available future rest : List Bool}
    (read : readBits n (available ++ future) = some (value, rest)) (fits : n ≤ available.length) :
    ∃ localRest, readBits n available = some (value, localRest) ∧ rest = localRest ++ future := by
  induction n generalizing available value rest with
  | zero =>
    simp only [readBits, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨available, rfl, rfl⟩
  | succ n ih =>
    cases available with
    | nil => simp only [List.length_nil] at fits; omega
    | cons bit available =>
      simp only [List.cons_append, readBits] at read
      cases previous : readBits n (available ++ future) with
      | none => rw [previous] at read; cases read
      | some pair =>
        obtain ⟨oldValue, oldRest⟩ := pair
        obtain ⟨localRest, localRead, suffix⟩ := ih previous (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using fits)
        rw [previous] at read
        simp only [Option.some.injEq, Prod.mk.injEq] at read
        obtain ⟨rfl, rfl⟩ := read
        refine ⟨localRest, ?_, suffix⟩
        simp only [readBits, localRead]


end ZlibF.Math.FastTokenPrefix

namespace ZlibF.Math.FastTokenPrefix
open ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

theorem read_count {n value : Nat} {input rest : List Bool}
    (read : readBits n input = some (value, rest)) :
    input.length = n + rest.length := by
  have source := (ZlibF.Math.CodeLengthPrefix.read_word read).2
  have count := congrArg List.length source
  simpa only [List.length_append, bitsOfNat_length] using count

/-- Six actual input bytes already contain every possible complete token.
The remainder of the block may still lie in a later caller buffer. -/
theorem token_restrict48
    {L D : List Nat} {dict history next : List UInt8}
    {available future rest : List Bool} {done : Bool}
    (lengthBound : ∀ i, L.getD i 0 ≤ 15)
    (distanceBound : ∀ i, D.getD i 0 ≤ 15)
    (enough : 48 ≤ available.length)
    (token : Token.Step L D dict history (available ++ future) rest next done) :
    ∃ currentRest, Token.Step L D dict history available currentRest next done ∧
      rest = currentRest ++ future := by
  cases token with
  | @literal rest symbol decoded small =>
    obtain ⟨current, suffix⟩ := decodeSym_restrict decoded (by have := lengthBound symbol; omega)
    exact ⟨_, .literal current small, suffix⟩
  | @eob rest decoded =>
    obtain ⟨current, suffix⟩ := decodeSym_restrict decoded (by have := lengthBound 256; omega)
    exact ⟨_, .eob current, suffix⟩
  | @copy r1 r2 r3 rest symbol ds le de
      decoded lower upper lengthRead distanceRead distanceSymbol distanceExtra fits =>
    have lengthWidth : lengthExtras.getD (symbol - 257) 0 ≤ 5 := by
      have finite : ∀ i : Fin 29, lengthExtras.getD i.val 0 ≤ 5 := by decide +kernel
      exact finite ⟨symbol - 257, by omega⟩
    have distanceWidth : distExtras.getD ds 0 ≤ 13 := by
      have finite : ∀ i : Fin 30, distExtras.getD i.val 0 ≤ 13 := by decide +kernel
      exact finite ⟨ds, by omega⟩
    have firstFits : L.getD symbol 0 ≤ available.length := by
      have := lengthBound symbol
      omega
    obtain ⟨currentLength, firstSuffix⟩ := decodeSym_restrict decoded firstFits
    rw [firstSuffix] at lengthRead
    have firstLength : (available.drop (L.getD symbol 0)).length ≥ 33 := by
      simp only [List.length_drop]
      have := lengthBound symbol
      omega
    obtain ⟨r2Current, currentExtra, secondSuffix⟩ := readBits_restrict lengthRead (by omega)
    have secondLength := read_count currentExtra
    rw [secondSuffix] at distanceRead
    have secondFits : D.getD ds 0 ≤ r2Current.length := by
      have := distanceBound ds
      omega
    obtain ⟨currentDistance, thirdSuffix⟩ := decodeSym_restrict distanceRead secondFits
    rw [thirdSuffix] at distanceExtra
    have thirdLength : 13 ≤ (r2Current.drop (D.getD ds 0)).length := by
      simp only [List.length_drop]
      have := distanceBound ds
      omega
    obtain ⟨currentRest, currentDistanceExtra, finalSuffix⟩ :=
      readBits_restrict distanceExtra (by omega)
    exact ⟨currentRest, .copy currentLength lower upper currentExtra currentDistance
      distanceSymbol currentDistanceExtra fits, finalSuffix⟩

#print axioms token_restrict48

theorem acceptable_width {kind : CodeKind} {lengths : List Nat}
    (acceptable : Acceptable kind lengths) (i : Nat) : lengths.getD i 0 ≤ 15 := by
  have helper : ∀ xs : List Nat, (∀ x ∈ xs, x ≤ 15) → ∀ n, xs.getD n 0 ≤ 15 := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro bounds n
      cases n with
      | zero => simpa using bounds x (by simp)
      | succ n =>
        have tail : ∀ y ∈ xs, y ≤ 15 := fun y hy => bounds y (by simp [hy])
        simpa using ih tail n
  exact helper lengths (by simpa only [maxCodeLen] using acceptable.1) i

theorem token_unique
    {L D : List Nat} {dict history first second : List UInt8}
    {input rest₁ rest₂ : List Bool} {done₁ done₂ : Bool}
    (a : Token.Step L D dict history input rest₁ first done₁)
    (b : Token.Step L D dict history input rest₂ second done₂) :
    rest₁ = rest₂ ∧ first = second ∧ done₁ = done₂ := by
  cases a <;> cases b <;> simp_all <;> omega

/-- An actual current-buffer token keeps the full block's continuation
with the same fixed future suffix. No end-of-block in this buffer is needed. -/
theorem token_align_future
    {L D : List Nat} {dict history next target : List UInt8}
    {available future rest tail : List Bool} {done : Bool}
    (lengthBound : ∀ i, L.getD i 0 ≤ 15)
    (distanceBound : ∀ i, D.getD i 0 ≤ 15)
    (enough : 48 ≤ available.length)
    (token : Token.Step L D dict history available rest next done)
    (parsed : Symbols L D dict history (available ++ future) tail target) :
    (done = true → rest ++ future = tail ∧ next = target) ∧
    (done = false → Symbols L D dict next (rest ++ future) tail target) := by
  obtain ⟨fullRest, fullNext, fullDone, first, continuation⟩ :=
    ZlibF.Spec.Token.symbols_exposes_step L D dict history _ tail target parsed
  obtain ⟨currentRest, current, suffix⟩ := token_restrict48 lengthBound distanceBound enough first
  obtain ⟨sameRest, sameNext, sameDone⟩ := token_unique token current
  subst currentRest fullNext fullDone
  rw [suffix] at continuation
  rcases continuation with ⟨ended, tailEq, targetEq⟩ | ⟨running, later⟩
  · exact ⟨fun _ => ⟨tailEq, targetEq⟩, fun impossible => by simp_all⟩
  · exact ⟨fun impossible => by simp_all, fun _ => later⟩

#print axioms acceptable_width
#print axioms token_align_future
end ZlibF.Math.FastTokenPrefix
