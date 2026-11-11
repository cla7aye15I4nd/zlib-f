import ZlibF.Proof.«inflate.c.meaning-accept»
import ZlibF.Proof.Format.Token

/-!
# inflate.c: output still due is before the end of the decoding (heap-free)

A parse position that holds output it has not written yet — a decoded literal
(`LIT`), a match with bytes left to copy (`MATCH`), or a stored block with bytes
left (`COPY`) — lies strictly before the end of the decoding of every valid
stream that the consumed input begins (`wrapParsed_due`). `StopsWhenBlocked`
needs this for a call that stops for want of output room.

The proof follows the stream's own parse from the position before the pending
token (`deflateParsed_resid`, `Resid.token`): the stream decodes that token,
which writes at least one byte more.
-/

namespace Zlib.Inflate.Proofs
open C ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- A stage with output not yet written. -/
def Due : BlockStage → Prop
  | .codes _ _ (.literal _) => True
  | .codes _ _ (.copy (_ + 1) _) => True
  | .stored (_ + 1) => True
  | _ => False

theorem copyBack_length_add (dict : List UInt8) (dist : Nat) :
    ∀ (n : Nat) (h : List UInt8), (copyBack dict dist n h).length = h.length + n
  | 0, _ => rfl
  | n + 1, h => by
    rw [copyBack, copyBack_length_add dict dist n]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem readBytes_length_eq :
    ∀ (n : Nat) (inp : List Bool) (bs : List UInt8) (r : List Bool),
      readBytes n inp = some (bs, r) → bs.length = n
  | 0, _, bs, r, read => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at read
    rw [← read.1]
    rfl
  | n + 1, inp, bs, r, read => by
    simp only [readBytes] at read
    cases first : readBits 8 inp with
    | none => rw [first] at read; cases read
    | some pair =>
      obtain ⟨v, r1⟩ := pair
      rw [first] at read
      simp only at read
      cases rest : readBytes n r1 with
      | none => rw [rest] at read; cases read
      | some pair' =>
        obtain ⟨bs', r'⟩ := pair'
        rw [rest] at read
        simp only [Option.some.injEq, Prod.mk.injEq] at read
        rw [← read.1, List.length_cons, readBytes_length_eq n r1 bs' r' rest]

theorem lengthBases_pos : ∀ i, i < 29 → 3 ≤ lengthBases.getD i 0 := by decide

theorem lengthBases_symbol_pos (s : Nat) (lower : 257 ≤ s) (upper : s ≤ 285) :
    3 ≤ lengthBases.getD (s - 257) 0 :=
  lengthBases_pos (s - 257) (by omega)

/-- A literal or a match writes at least one byte. -/
theorem _root_.ZlibF.Spec.Token.Step.grows {L D : List Nat} {dict out out' : List UInt8}
    {inp rest : List Bool} (step : Token.Step L D dict out inp rest out' false) :
    out.length < out'.length := by
  cases step with
  | literal => simp
  | copy _ lower upper =>
    rw [copyBack_length_add]
    have := lengthBases_symbol_pos _ lower upper
    omega

/-- On a valid stream, a deflate position with output still due is strictly
before the end of the decoding. -/
theorem deflateParsed_due {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) (due : Due pos.stage) {more tail : List Bool}
    {outF : List UInt8} (aligned : (bits ++ more).length % 8 = 0)
    (blocks : Blocks dict [] (bits ++ more) tail outF) : pos.out.length < outF.length := by
  have resid := deflateParsed_resid parsed more tail outF aligned blocks
  obtain ⟨out, final, stage⟩ := pos
  cases stage with
  | stored remaining =>
    cases remaining with
    | zero => exact absurd due (by simp [Due])
    | succ k =>
      obtain ⟨bs, r, read, cont⟩ := resid
      have written := cont.history.length_le
      have length := readBytes_length_eq _ _ _ _ read
      rw [List.length_append] at written
      change out.length < outF.length
      omega
  | codes L D p =>
    cases p with
    | literal byte =>
      cases parsed with
      | @partialLiteral consumed tokenBits _ _ _ _ _ prev step =>
        have before := deflateParsed_resid prev (tokenBits ++ more) tail outF
          (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
        have after := (Resid.output (fun _ _ _ eq => by cases eq; rfl)
          (before.token step)).length_le
        simp only [List.length_append, List.length_cons, List.length_nil] at after
        change out.length < outF.length
        omega
      | partialToken _ _ pending => exact absurd pending (by simp [PendingParsed])
    | copy remaining dist =>
      cases parsed with
      | @partialCopy consumed tokenBits out0 out' _ _ _ _ written prev step _ less _ _ _ =>
        have before := deflateParsed_resid prev (tokenBits ++ more) tail outF
          (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
        have after := (Resid.output (fun _ _ _ eq => by cases eq; rfl)
          (before.token step)).length_le
        change (out'.take (out0.length + written)).length < outF.length
        rw [List.length_take]
        omega
      | @partialToken consumed out0 _ _ _ _ pbits prev pending =>
        have before := deflateParsed_resid prev (pbits ++ more) tail outF
          (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
        obtain ⟨extL, _, r, h', symbols, cont⟩ := before
        obtain ⟨symbol, _, _, _, _, _, _, decoded, lower, _⟩ := pending
        obtain ⟨rest, next, fin, exposed, outcome⟩ :=
          ZlibF.Spec.Token.symbols_exposes_step _ _ _ _ _ _ _ symbols
        have long := extL _ _ _ more decoded
        rcases outcome with ⟨rfl, _, _⟩ | ⟨rfl, following⟩
        · cases exposed with
          | eob end256 =>
            rw [long] at end256
            cases end256
            omega
        · have grows := exposed.grows
          have reach := (following.history.trans cont.history).length_le
          dsimp only
          omega
    | _ => exact absurd due (by simp [Due])
  | boundary => exact absurd due (by simp [Due])
  | storedHeader => exact absurd due (by simp [Due])
  | dynamicHeader _ => exact absurd due (by simp [Due])
  | finished => exact absurd due (by simp [Due])

/-- On a valid stream that the input begins, a body stage with output still due
is strictly before the end of the decoding. -/
theorem wrapParsed_due {wrap : Api.Wrap} {configured : Nat}
    {dict input source decoded header : List UInt8} {consumed held : List Bool} {pos : DeflatePos}
    (parsed : WrapParsed wrap configured dict consumed (.body header pos)) (due : Due pos.stage)
    (bits : bytesToBits input = consumed ++ held)
    (valid : Api.Layer.Decodes wrap configured dict source decoded) (started : input <+: source) :
    pos.out.length < decoded.length := by
  obtain ⟨bodyDict, dbits, wrapHeader, rfl, dparsed⟩ := parsed
  obtain ⟨more, tail, aligned, _, blocks, _⟩ :=
    body_on_source wrapHeader valid started (rest := held) (by rw [bits])
  exact deflateParsed_due dparsed due aligned blocks

#print axioms deflateParsed_due
#print axioms wrapParsed_due
end Zlib.Inflate.Proofs
