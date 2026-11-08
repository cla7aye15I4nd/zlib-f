import ZlibF.Proof.«deflate.c.engine.fill-checksum»
import ZlibF.Proof.«deflate.c.engine.fill-history»
import ZlibF.Math.DeflateSymbolTrace

/-! # The checksum input ledger agrees with the logical compression input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateChecksum
set_option autoImplicit false

/-- The array slice is precisely its bounded pointwise byte view. -/
theorem checksum_input_array_slice (incoming : Array UInt8) (offset count : Nat)
    (fit : offset + count ≤ incoming.size) :
    (List.range count).map (fun j => bfn incoming (offset + j)) =
      (incoming.toList.drop offset).take count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take,
      List.length_drop, Array.length_toList]
    omega
  · intro j left right
    have index : j < count := by simpa only [List.length_map, List.length_range] using left
    have bound : offset + j < incoming.size := by omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, Array.getElem_toList]
    exact (getElem_bfn incoming (offset + j) bound).symm

/-- Agreement before the old endpoint and the actual new caller bytes
determine the entire next accepted input prefix. -/
theorem checksum_input_prefix_append {input extended : Nat → UInt8}
    {limit offset count : Nat} {incoming : Array UInt8}
    (agree : ∀ i, i < limit → extended i = input i)
    (added : ∀ j, j < count → extended (limit + j) = bfn incoming (offset + j))
    (fit : offset + count ≤ incoming.size) :
    inputPrefix extended (limit + count) =
      inputPrefix input limit ++ (incoming.toList.drop offset).take count := by
  unfold inputPrefix
  rw [List.range_add, List.map_append, List.map_map]
  have old : (List.range limit).map extended = (List.range limit).map input := by
    apply List.map_congr_left
    intro i member
    exact agree i (List.mem_range.mp member)
  rw [old]
  congr 1
  calc
    (List.range count).map (extended ∘ (limit + ·)) =
        (List.range count).map (fun j => bfn incoming (offset + j)) := by
      apply List.map_congr_left
      intro j member
      exact added j (List.mem_range.mp member)
    _ = _ := checksum_input_array_slice incoming offset count fit

/-- The actual refill extension function joins the same caller bytes to
the previously accepted input used by independent raw block encoding. -/
theorem checksum_extend_input_prefix (input : Nat → UInt8) (limit : Nat)
    (incoming : Array UInt8) (offset count : Nat) (fit : offset + count ≤ incoming.size) :
    inputPrefix (extendInput input limit incoming offset) (limit + count) =
      inputPrefix input limit ++ (incoming.toList.drop offset).take count := by
  apply checksum_input_prefix_append
  · intro i before
    simp only [extendInput, before, ite_true]
  · intro j _before
    simp only [extendInput, show ¬ limit + j < limit from by omega, ite_false,
      Nat.add_sub_cancel_left]
  · exact fit

/-- The real non-sliding refill's returned window fixes the exact newly
accepted logical input. Pending insertions and high-water padding are
included by the complete actual execution theorem. -/
theorem fill_window_no_slide_input_prefix {h after : Heap} {r : ZStreamRef}
    {ds origin io used : Nat} {z z' : ZStream} {d result : DeflateState}
    {input extended : Nat → UInt8} {xs : List Symbol} {ref : BRef} {incoming : Array UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (getInput : Space.get h ref = some incoming)
    (inputBound : io + z.avail_in.toNat ≤ incoming.size) (nonempty : z.avail_in ≠ 0)
    (run : fill_window (some (.tab ds)) h = .ok ((), after))
    (stateA : PendingBoundary after r ds z' result extended origin xs)
    (account : StreamAccounting z z' used 0)
    (agree : ∀ i, i < origin + fillEnd d → extended i = input i) :
    inputPrefix extended (origin + fillEnd result) =
      inputPrefix input (origin + fillEnd d) ++ (incoming.toList.drop io).take used := by
  obtain ⟨w, window, win, get, _view, _form⟩ := boundary.data
  have separate := caller_input_window_separate boundary.good buffers win pointer
  obtain ⟨other, otherD, output, otherRun, otherGood, _chains, winA, getA,
      _rangeA, _highA, _formA, fields, _insertA, _private, copiedA, _stoppedA, _frameA⟩ :=
    fill_window_pending_complete_storage boundary.good boundary.frontier boundary.insert_le
      win get boundary.range short noSlide wrap pointer getInput inputBound nonempty separate
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood getA
  have states : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans stateA.good.live.hs)
  rw [states] at winA fields copiedA
  have streams := actual_run_stream_unique otherRun run (by rw [heaps]; exact otherGood.live.hz) stateA.good.live.hz
  have countBound : (rbLen z.avail_in (fillMore d)).toNat ≤ z.avail_in.toNat := by
    rw [rbLen_nat]
    exact Nat.min_le_left _ _
  have expected := read_stream_accounting z (rbLen z.avail_in (fillMore d)) ref io
    (adlerValue z.adler ((incoming.toList.drop io).take (rbLen z.avail_in (fillMore d)).toNat)) pointer countBound
  rw [streams] at expected
  have usedEq : used = (rbLen z.avail_in (fillMore d)).toNat :=
    (stream_accounting_counts_unique account expected).1
  have counts := resume_read_counts boundary.good win get boundary.range
  have endEq : fillEnd result = fillEnd d + used := by
    rw [fields]
    change d.strstart.toNat + (d.lookahead + rbLen z.avail_in (fillMore d)).toNat = _
    rw [counts.2.1, usedEq]
    simp only [fillEnd, Nat.add_assoc]
  obtain ⟨wA, arrayA, pointerA, arrayGetA, viewA, _formAA⟩ := stateA.data
  have windowEq : wA = w := by simpa only [winA, Ptr.ref.injEq, BRef.blk.injEq, and_true] using pointerA.symm
  subst wA
  have arrayEq : arrayA = output := Option.some.inj (arrayGetA.symm.trans getA)
  subst arrayA
  have room : fillEnd d + (rbLen z.avail_in (fillMore d)).toNat ≤ window.size := by
    have extent := window_extent boundary.good win get
    have range := boundary.range
    rw [counts.1, extent.1]
    omega
  rw [endEq, ← Nat.add_assoc]
  apply checksum_input_prefix_append agree
  · intro j bound
    have inside : fillEnd d + j < fillEnd result := by omega
    have view := viewA (fillEnd d + j) inside
    rw [← Nat.add_assoc] at view
    rw [← view, copiedA _ inside]
    have copied := copy_range_inside window incoming (fillEnd d) io
      (rbLen z.avail_in (fillMore d)).toNat (fillEnd d + j) room
      (by rw [← usedEq]; omega) (by simp only [Nat.add_sub_cancel_left]; have consumed := account.1; omega)
    simpa only [Nat.add_sub_cancel_left] using copied
  · omega

/-- A readable input slice is uniquely fixed by its actual object and cursor. -/
theorem checksum_bytes_slice {h : Heap} {pointer : BPtr} {ref : BRef} {offset count : Nat}
    {incoming : Array UInt8} {copied : List UInt8}
    (cursor : pointer = .ref ref offset) (get : Space.get h ref = some incoming)
    (data : Bytes h pointer count copied) :
    copied = (incoming.toList.drop offset).take count := by
  rcases data with null | ⟨otherRef, otherOffset, array, otherCursor, otherGet, _bound, value⟩
  · rw [cursor] at null
    cases null.1
  · obtain ⟨refEq, offsetEq⟩ := Ptr.ref.inj (cursor.symm.trans otherCursor)
    subst otherRef otherOffset
    have same : array = incoming := Option.some.inj (otherGet.symm.trans get)
    subst array
    exact value

/-- The actual complete non-sliding refill preserves checksum meaning on
the same logical accepted prefix as its returned compression boundary. -/
theorem fill_window_no_slide_logical_adler {h after : Heap} {r : ZStreamRef}
    {ds origin io used : Nat} {z z' : ZStream} {d result : DeflateState}
    {input extended : Nat → UInt8} {xs : List Symbol} {ref : BRef} {incoming : Array UInt8}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) (getInput : Space.get h ref = some incoming)
    (inputBound : io + z.avail_in.toNat ≤ incoming.size) (nonempty : z.avail_in ≠ 0)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (run : fill_window (some (.tab ds)) h = .ok ((), after))
    (stateA : PendingBoundary after r ds z' result extended origin xs)
    (account : StreamAccounting z z' used 0)
    (agree : ∀ i, i < origin + fillEnd d → extended i = input i) :
    z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (origin + fillEnd result))).toUInt64 := by
  have joined := fill_window_no_slide_input_prefix boundary short noSlide wrap buffers pointer
    getInput inputBound nonempty run stateA account agree
  obtain ⟨copied, slice, _length, checksumA⟩ := fill_window_run_adler boundary short wrap buffers
    (by intro _; rw [pointer]; intro impossible; cases impossible) checksum run stateA.good.live.hz account
  have bytes := checksum_bytes_slice pointer getInput slice
  rw [bytes] at checksumA
  rw [joined]
  exact checksumA

/-- Two logical inputs represented by the same actual returned window
have the same complete accepted prefix once their earlier bytes agree.
The origin may move during a slide; the covered prefix accounts for all
positions before that window. -/
theorem pending_boundary_input_prefix_unique {h : Heap} {r : ZStreamRef}
    {ds origin earlier : Nat} {z : ZStream} {d : DeflateState}
    {one two : Nat → UInt8} {xs ys : List Symbol}
    (first : PendingBoundary h r ds z d one origin xs)
    (second : PendingBoundary h r ds z d two origin ys)
    (covered : origin ≤ earlier) (agree : ∀ i, i < earlier → one i = two i) :
    inputPrefix one (origin + fillEnd d) = inputPrefix two (origin + fillEnd d) := by
  obtain ⟨w, window, pointer, get, view, _form⟩ := first.data
  obtain ⟨w', window', pointer', get', view', _form'⟩ := second.data
  have sameWindow : w' = w := by
    simpa only [pointer, Ptr.ref.injEq, BRef.blk.injEq, and_true] using pointer'.symm
  subst w'
  have sameArray : window' = window := Option.some.inj (get'.symm.trans get)
  subst window'
  unfold inputPrefix
  apply List.map_congr_left
  intro i member
  have bound := List.mem_range.mp member
  by_cases old : i < earlier
  · exact agree i old
  · have inside : i - origin < fillEnd d := by omega
    have position : origin + (i - origin) = i := by omega
    exact (by simpa only [position] using (view (i - origin) inside).symm.trans (view' (i - origin) inside))

end Zlib.Deflate.Engine.Proofs
