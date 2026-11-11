import ZlibF.Proof.«inflate.c.sequence-safety»
import ZlibF.Proof.«inflate.c.meaning»

/-!
# inflate.c: the format part of `Goal.inflate_sequence` (skeleton)

`ParseMeaning` couples the actual decoder after a protocol-admitted data
epoch with the stream format: the decoder state is the parse position reached
by reading the consumed input under the configured format, and the delivered
output is what that position has decoded. It is established by
initialization and preserved by rebuffering, every `inflate` call and every
dictionary call; the three format clauses follow from it.

`ParseMeaning` is defined in `inflate.c.meaning`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem meaning_init {h after : Heap} {r : ZStreamRef} {version : BPtr} {wb : Int32}
    (domain : InitDomain h r version)
    (run : C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after)) :
    ParseMeaning wb r after {} false := by
  sorry

theorem meaning_rebuffer {h after : Heap} {r : ZStreamRef} {wb : Int32} {log : DataLog}
    {pending : Bool} (current : ParseMeaning wb r h log pending) (edit : Rebuffer h after r) :
    ParseMeaning wb r after log pending := by
  sorry

/-- The functional correctness of one `inflate` call: header, stored,
fixed and dynamic blocks, table meaning, slow and fast symbol decoding,
window copies and the trailer, for every input and output split. -/
theorem meaning_step {h after : Heap} {r : ZStreamRef} {wb flush rc : Int32} {log : DataLog}
    {pending : Bool} {input output : List UInt8} {used : Nat}
    (current : ParseMeaning wb r h log pending)
    (step : DataStep .inflate h after r flush rc input output used) :
    ParseMeaning wb r after
      { log with
        input := log.input ++ input.take used, output := log.output ++ output
        result := rc, finished := log.finished || rc == Z_STREAM_END }
      (rc == Z_NEED_DICT) := by
  sorry

theorem meaning_dictionary {h after : Heap} {r : ZStreamRef} {wb : Int32} {log : DataLog}
    {pending : Bool} {p : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
    (current : ParseMeaning wb r h log pending)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) p n))
    (read : Bytes h p n.toNat bytes)
    (run : C.run (inflateSetDictionary (some r) p n) h = .ok (rc, after))
    (admitted : wb.toInt < 0 ∨ rc ≠ Z_OK ∨ pending = true) :
    ParseMeaning wb r after
      { log with
        dictionary := if rc = Z_OK then
          if wb.toInt < 0 then log.dictionary ++ bytes else bytes else log.dictionary
        singleDictionary := log.singleDictionary &&
          !(rc = Z_OK && wb.toInt < 0 && (log.input != [] || log.output != [])) }
      (if wb.toInt < 0 then pending else if rc = Z_OK then false else pending) := by
  sorry

theorem meaning_of_trace {wb : Int32} {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace wb r h log pending) : ParseMeaning wb r h log pending := by
  induction trace with
  | init domain run => exact meaning_init domain run
  | caller _ edit ih => exact meaning_rebuffer ih edit
  | step _ step ih => exact meaning_step ih step
  | dictionary _ arguments read run admitted ih => exact meaning_dictionary ih arguments read run admitted

/-- A finished single-dictionary epoch consumed an accepted stream. -/
theorem meaning_accepted {wb : Int32} {wrap : ZlibF.Spec.Api.Wrap} {bits : Nat} {r : ZStreamRef}
    {h : Heap} {log : DataLog} {pending : Bool}
    (params : ZlibF.Spec.Api.inflWbits wb.toInt = some (wrap, bits))
    (current : ParseMeaning wb r h log pending)
    (single : log.singleDictionary = true) (ended : log.result = Z_STREAM_END) :
    ZlibF.Spec.Api.Layer.InflateAccepted wrap bits log.dictionary log.input log.output := by
  sorry

/-- On a prefix of a valid stream, output is a prefix of its decoding,
there is no data error, and the end is reached exactly at the stream end. -/
theorem meaning_prefix {wb : Int32} {wrap : ZlibF.Spec.Api.Wrap} {bits : Nat} {r : ZStreamRef}
    {h : Heap} {log : DataLog} {pending : Bool} {source decoded : List UInt8}
    (params : ZlibF.Spec.Api.inflWbits wb.toInt = some (wrap, bits))
    (current : ParseMeaning wb r h log pending)
    (valid : ZlibF.Spec.Api.Layer.Decodes wrap bits log.dictionary source decoded)
    (single : log.singleDictionary = true) (full : ZlibF.Spec.Api.FullWindow wrap bits source)
    (started : log.input <+: source) :
    log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
      (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded) := by
  sorry

/-- Completion: with the rest of a valid stream and enough room, the next call
finishes, or asks once for a missing zlib dictionary, or refuses a bad pointer. -/
theorem inflate_completes_proof : InflateCompletes := by
  sorry

/-- The format part of `Goal.inflate_sequence`. -/
theorem inflate_sequence_format :
    ∀ wb wrap bits r h log, ZlibF.Spec.Api.inflWbits wb.toInt = some (wrap, bits) →
      AllowedInflateProtocol wb r h log →
      (log.singleDictionary = true → log.result = Z_STREAM_END →
        ZlibF.Spec.Api.Layer.InflateAccepted wrap bits log.dictionary log.input log.output) ∧
      (∀ source decoded, ZlibF.Spec.Api.Layer.Decodes wrap bits log.dictionary source decoded →
        log.singleDictionary = true → ZlibF.Spec.Api.FullWindow wrap bits source →
        log.input <+: source →
        log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
        (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded)) := by
  intro wb wrap bits r h log params ⟨pending, trace⟩
  have current := meaning_of_trace trace
  exact ⟨fun single ended => meaning_accepted params current single ended,
    fun source decoded valid single full started =>
      meaning_prefix params current valid single full started⟩

end Zlib.Inflate.Proofs
