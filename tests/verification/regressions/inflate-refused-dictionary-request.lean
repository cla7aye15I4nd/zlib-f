import ZlibF.Runtime.Schema

open C

/-! The request clause of `ParseMeaning` said that the protocol token is set
exactly when the decoder waits for a dictionary (a `needDict` stage with
`havedict = 0`). The token is the test `rc == Z_NEED_DICT` on the last call.
A zlib stream with a preset dictionary makes `inflate` return `Z_NEED_DICT`;
a further call with a NULL `next_out` is refused with `Z_STREAM_ERROR` and
changes nothing, so the decoder still waits while the token is false; the next
accepted call returns `Z_NEED_DICT` again
(`tests/goals/inflate-meaning/refused-dictionary-request.c`). The clause is now
an implication from the token to the wait, which is the direction every use
takes. -/
namespace RefusedDictionaryRequestRegression

/-- After the refused call the token is false while the decoder still waits:
the equivalence fails and the implication holds. -/
theorem token_after_refusal (waits : Prop) (still : waits) :
    ((Z_STREAM_ERROR == Z_NEED_DICT) = true → waits) ∧
      ¬ ((Z_STREAM_ERROR == Z_NEED_DICT) = true ↔ waits) := by
  have off : (Z_STREAM_ERROR == Z_NEED_DICT) = false := by decide
  rw [off]
  exact ⟨fun bad => absurd bad (by decide), fun iff => absurd (iff.mpr still) (by decide)⟩

end RefusedDictionaryRequestRegression
