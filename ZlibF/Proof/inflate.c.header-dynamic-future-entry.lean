import ZlibF.Proof.«inflate.c.header-head-empty-block»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem read_dynamic_three {input middle rest : List Bool} {last : Nat}
    (first : readBits 1 input = some (last, middle)) (second : readBits 2 middle = some (2, rest)) :
    readBits 3 input = some (last + 4, rest) := by
  cases input with
  | nil => simp [readBits] at first
  | cons bit tail =>
    simp only [readBits, Option.some.injEq, Prod.mk.injEq] at first
    obtain ⟨rfl, rfl⟩ := first
    simp only [readBits, second]

/-- A valid first dynamic Body may continue in future caller buffers.
Whenever a current block byte exists, its three header bits already select
TABLE. Validity derives the literal C kind guard; no guard observation or
callee/postcondition is required as an extra premise. -/
theorem Epoch.head_dynamic_future_loop_entry
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used last : Nat} {cmf flg : UInt8} {bodyBytes : List UInt8}
    {future middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (prefixBytes : log.input ++ input = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0) (nonempty : bodyBytes ≠ [])
    (first : readBits 1 (bytesBits bodyBytes ++ future) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    ∃ currentRest, SameCallTableEntry h r zs log input flush currentRest ∧ Body dict 2 prior (currentRest ++ future) rest decoded := by
  have enough : 3 ≤ (bytesBits bodyBytes).length := by
    rw [bytesBits_length]
    have positive : 1 ≤ bodyBytes.length := by cases bodyBytes <;> simp_all
    omega
  obtain ⟨value, currentRest, parse, _bound, _source⟩ := ZlibF.Math.InflateDecode.read_total 3 (bytesBits bodyBytes) enough
  have extended := CumulativeTableBoundary.readBits_append parse future
  have expected := read_dynamic_three first second
  have pair := Option.some.inj (extended.symm.trans expected)
  have valueEq : value = last + 4 := congrArg Prod.fst pair
  have restEq : currentRest ++ future = bodyInput := congrArg Prod.snd pair
  have lastBound := (ZlibF.Math.CodeLengthPrefix.read_word first).1
  have kind : value / 2 = 2 := by omega
  exact ⟨currentRest, selected.head_dynamic_loop_entry observed flushing accepted prefixBytes valid plain parse kind, by rwa [restEq]⟩

#print axioms read_dynamic_three
#print axioms Epoch.head_dynamic_future_loop_entry
end Zlib.Inflate.Proofs.HeaderPhaseView

namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A short current wrapper prefix produces the actual next HEAD trace
constructor directly from the original observed call. -/
theorem Epoch.head_short_input {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog}
    {history : InflateDataTrace 15 r h log} {flush rc : Int32} {input output : List UInt8} {used : Nat}
    {actual : DataStep .inflate h after r flush rc input output used}
    (selected : Epoch r zs .head history) (short : log.input.length + input.length < 2) :
    Epoch r zs .head (.step history actual) := by
  have actual0 := actual
  obtain ⟨z, s, current, _allocator, _window, _empty, mode, _last, _wrap, _below, count, _word, _bound⟩ := selected.checked.2
  obtain ⟨z0, _returned, get0, _get1, _buffers, _active, bytes, _usedEq, _output, _run⟩ := actual
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have length := header_observed_bytes_length bytes
  exact .headwait (actual := actual0) selected current.good.live.hz current.good.live.hs mode (by omega)

/-- The accepted valid first dynamic header has a complete same-call
entry classification for every current input size: public HEAD wait,
public TYPE wait, or the actual private TABLE loop and unrestricted suffix.
The caller may supply the remaining bytes in future buffers. This does not
force the same call to return in a header mode after reaching TABLE. -/
theorem Epoch.head_dynamic_arbitrary_boundary
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output futureBytes bodyBytes : List UInt8} {used last : Nat} {cmf flg : UInt8}
    {middle bodyInput rest : List Bool} {dict prior decoded : List UInt8}
    (selected : Epoch r zs .head history)
    (observed : DataStep .inflate h after r flush rc input output used)
    (flushing : flush ≠ Z_BLOCK ∧ flush ≠ Z_TREES)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (allBytes : (log.input ++ input) ++ futureBytes = [cmf, flg] ++ bodyBytes)
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (first : readBits 1 (bytesBits bodyBytes) = some (last, middle))
    (second : readBits 2 middle = some (2, bodyInput))
    (body : Body dict 2 prior bodyInput rest decoded) :
    Meaning .head after r zs (credit log input output used rc) ∨
      Meaning .block after r zs (credit log input output used rc) ∨
      ∃ currentRest, SameCallTableEntry h r zs log input flush currentRest ∧
        Body dict 2 prior (currentRest ++ bytesBits futureBytes) rest decoded := by
  by_cases short : log.input.length + input.length < 2
  · exact Or.inl ((selected.head_short_input (actual := observed) short).checked.2)
  have enough : 2 ≤ (log.input ++ input).length := by simp only [List.length_append]; omega
  have headerPrefix : (log.input ++ input).take 2 = [cmf, flg] := by
    have take := congrArg (List.take 2) allBytes
    rw [List.take_append_of_le_length enough] at take
    simpa using take
  have currentPrefix : log.input ++ input = [cmf, flg] ++ (log.input ++ input).drop 2 := by
    rw [← headerPrefix, List.take_append_drop]
  have futureSplit : (log.input ++ input).drop 2 ++ futureBytes = bodyBytes := by
    have drop := congrArg (List.drop 2) allBytes
    rw [List.drop_append_of_le_length enough] at drop
    simpa using drop
  by_cases empty : (log.input ++ input).drop 2 = []
  · apply Or.inr ∘ Or.inl
    apply selected.head_empty_block observed (by simpa only [empty, List.append_nil] using currentPrefix) valid plain accepted
  · apply Or.inr ∘ Or.inr
    apply selected.head_dynamic_future_loop_entry observed flushing accepted currentPrefix valid plain empty
    · simpa only [← futureSplit, bytesBits_append] using first
    · exact second
    · exact body

#print axioms Epoch.head_short_input
#print axioms Epoch.head_dynamic_arbitrary_boundary
end Zlib.Inflate.Proofs.HeaderPhaseView
