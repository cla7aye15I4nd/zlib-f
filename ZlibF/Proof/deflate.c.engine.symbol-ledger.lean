import ZlibF.Math.DeflateSymbols
import ZlibF.Proof.«deflate.c.engine.symbol-initial»
import ZlibF.Proof.«deflate.c.engine.tally-match»

/-! # The actual symbol bytes and leaf frequencies describe the same block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase InitialFrequencies bumpFc dcodeN)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def symbolLengthCode (n : Nat) : Nat := Zlib.Trees.length_code_tab[n]!.toNat

def PackedSymbols (buf : Array UInt8) (base : Nat) (xs : List Symbol) : Prop :=
  ∀ i s, xs[i]? = some s →
    bfn buf (base + 3 * i) = (UInt16.ofNat s.distance).toUInt8 ∧
    bfn buf (base + 3 * i + 1) = (UInt16.ofNat s.distance >>> 8).toUInt8 ∧
    bfn buf (base + 3 * i + 2) = UInt8.ofNat s.value

/-- A ledger refers to the stored bytes and the actual leaf frequencies.
It does not constrain unused symbols or the internal tree nodes. -/
structure SymbolLedger (buf : Array UInt8) (d : DeflateState) (xs : List Symbol) : Prop where
  count : d.sym_next.toNat = 3 * xs.length
  valid : ∀ s ∈ xs, s.Valid
  packed : PackedSymbols buf d.lit_bufsize.toNat xs
  literal : ∀ k, k < 286 → (d.dyn_ltree[k]!).fc.toNat = literalFrequency symbolLengthCode xs k
  distance : ∀ k, k < 30 → (d.dyn_dtree[k]!).fc.toNat = distanceFrequency dcodeN xs k

theorem SymbolLedger.keep {buf : Array UInt8} {d result : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) (count : result.sym_next = d.sym_next)
    (offset : result.lit_bufsize = d.lit_bufsize) (literal : result.dyn_ltree = d.dyn_ltree)
    (distance : result.dyn_dtree = d.dyn_dtree) : SymbolLedger buf result xs := by
  exact ⟨by rw [count]; exact ledger.count, ledger.valid, by rw [offset]; exact ledger.packed,
    by rw [literal]; exact ledger.literal, by rw [distance]; exact ledger.distance⟩

theorem empty_symbol_ledger {buf : Array UInt8} {d : DeflateState}
    (count : d.sym_next = 0) (frequencies : InitialFrequencies d.dyn_ltree d.dyn_dtree) :
    SymbolLedger buf d [] := by
  refine ⟨by simp [count], by simp, ?_, ?_, ?_⟩
  · intro i s selected
    simp at selected
  · intro k bound
    simpa [literalFrequency, countKey] using frequencies.literal k bound
  · intro k bound
    simpa [distanceFrequency, countKey] using frequencies.distance k bound

/-- Every leaf increment fits in UInt16, including the end-marker count.
The bound follows from the real symbol capacity. -/
theorem ledger_frequency_room {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    xs.length + 2 < 65536 ∧
      (∀ k, k < 286 → (d.dyn_ltree[k]!).fc.toNat + 1 < 65536) ∧
      (∀ k, k < 30 → (d.dyn_dtree[k]!).fc.toNat + 1 < 65536) := by
  have cap := base.lit_hi
  have end_ := base.sym_end
  have count := ledger.count
  have symbols : xs.length + 2 < 65536 := by omega
  refine ⟨symbols, ?_, ?_⟩
  · intro k bound
    rw [ledger.literal k bound]
    have := literal_frequency_le symbolLengthCode xs k
    omega
  · intro k bound
    rw [ledger.distance k bound]
    have := distance_frequency_le dcodeN xs k
    omega

theorem bump_frequency_nat {a : Array CtData} {i j : Nat}
    (fit : i < a.size) (room : (a[i]!).fc.toNat + 1 < 65536) :
    ((bumpFc a i)[j]!).fc.toNat = (a[j]!).fc.toNat + if j = i then 1 else 0 := by
  unfold bumpFc
  rw [Zlib.Trees.Proofs.Out.getElem!_set!]
  by_cases same : j = i
  · subst j
    simp only [fit, and_self, ite_true]
    rw [UInt16.toNat_add]
    simp only [show (1 : UInt16).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt room
  · simp [same, Ne.symm same]

theorem packed_symbols_snoc {buf after : Array UInt8} {base : Nat} {xs : List Symbol} {s : Symbol}
    (packed : PackedSymbols buf base xs)
    (old : ∀ i, i < 3 * xs.length → bfn after (base + i) = bfn buf (base + i))
    (low : bfn after (base + 3 * xs.length) = (UInt16.ofNat s.distance).toUInt8)
    (high : bfn after (base + 3 * xs.length + 1) = (UInt16.ofNat s.distance >>> 8).toUInt8)
    (value : bfn after (base + 3 * xs.length + 2) = UInt8.ofNat s.value) :
    PackedSymbols after base (xs ++ [s]) := by
  intro i t selected
  by_cases before : i < xs.length
  · rw [List.getElem?_append_left before] at selected
    obtain ⟨lo, hi, val⟩ := packed i t selected
    refine ⟨?_, ?_, ?_⟩
    · rw [old (3 * i) (by omega), lo]
    · simpa only [Nat.add_assoc] using (old (3 * i + 1) (by omega)).trans hi
    · simpa only [Nat.add_assoc] using (old (3 * i + 2) (by omega)).trans val
  · rw [List.getElem?_append_right (by omega)] at selected
    have index : i - xs.length = 0 := by
      by_cases zero : i - xs.length = 0
      · exact zero
      · have out : 1 ≤ i - xs.length := by omega
        rw [List.getElem?_eq_none (by simpa using out)] at selected
        cases selected
    have eq : i = xs.length := by omega
    subst i
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at selected
    subst t
    exact ⟨low, high, value⟩

/-- The two inline tally implementations share the same three-byte
append geometry. Earlier symbols are unaffected by these writes. -/
theorem packed_symbols_write {buf after : Array UInt8} {base : Nat} {xs : List Symbol} {s : Symbol}
    (packed : PackedSymbols buf base xs)
    (view : ∀ i, bfn after i =
      if i = base + 3 * xs.length + 2 then UInt8.ofNat s.value
      else if i = base + 3 * xs.length + 1 then (UInt16.ofNat s.distance >>> 8).toUInt8
      else if i = base + 3 * xs.length then (UInt16.ofNat s.distance).toUInt8
      else bfn buf i) : PackedSymbols after base (xs ++ [s]) := by
  apply packed_symbols_snoc packed
  · intro i bound
    rw [view]
    simp only [if_neg (show base + i ≠ base + 3 * xs.length + 2 by omega),
      if_neg (show base + i ≠ base + 3 * xs.length + 1 by omega),
      if_neg (show base + i ≠ base + 3 * xs.length by omega)]
  · rw [view]
    simp
  · rw [view]
    simp
  · rw [view]
    simp

/-- The actual inline literal tally appends one literal to both the
packed buffer and the natural-number frequency histogram. -/
theorem ledger_literal {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) (c : UInt8) :
    SymbolLedger (literalBytes buf d c) (literalState d c) (xs ++ [⟨0, c.toNat⟩]) := by
  have cap := base.lit_hi
  have end_ := base.sym_end
  have size := base.size
  have fit : d.lit_bufsize.toNat + d.sym_next.toNat + 2 < buf.size := by omega
  have freqRoom := ledger_frequency_room base ledger room
  have cfit : c.toNat < d.dyn_ltree.size := by rw [base.wf.1]; have := c.toNat_lt; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [literal_count base room c, ledger.count]
    simp [List.length_append, Nat.mul_add]
  · intro s member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ledger.valid s member
    · exact ⟨by simp, c.toNat_lt⟩
  · apply packed_symbols_write ledger.packed
    intro i
    simpa [ledger.count] using literal_bytes_view buf d c fit i
  · intro k bound
    change ((bumpFc d.dyn_ltree c.toNat)[k]!).fc.toNat = _
    rw [bump_frequency_nat cfit (freqRoom.2.1 c.toNat (by have := c.toNat_lt; omega)),
      ledger.literal k bound, literal_frequency_snoc]
    simp [Symbol.literalKey, eq_comm]
  · intro k bound
    change (d.dyn_dtree[k]!).fc.toNat = _
    rw [ledger.distance k bound, distance_frequency_snoc]
    simp [Symbol.distanceKey]

/-- A match appends its real positive distance and length offset. The
strategy supplies the bounds before either machine narrowing occurs. -/
theorem ledger_match {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) (distance length : UInt32)
    (positive : 1 ≤ distance.toNat) (distanceBound : distance.toNat ≤ 32768)
    (lengthBound : length.toNat < 256) :
    SymbolLedger (matchBytes buf d distance.toUInt16 length.toUInt8)
      (matchSymbolState d distance length) (xs ++ [⟨distance.toNat, length.toNat⟩]) := by
  have cap := base.lit_hi
  have end_ := base.sym_end
  have size := base.size
  have fit : d.lit_bufsize.toNat + d.sym_next.toNat + 2 < buf.size := by omega
  have freqRoom := ledger_frequency_room base ledger room
  have index := match_distance_index distance positive distanceBound
  have lengthNarrow : length.toUInt8.toNat = length.toNat := by
    rw [UInt32.toNat_toUInt8]
    exact Nat.mod_eq_of_lt lengthBound
  have lengthTable : length.toNat < Zlib.Trees.length_code_tab.size := by
    rw [Zlib.Trees.Proofs.Out.length_code_tab_size]
    exact lengthBound
  have lcBound : symbolLengthCode length.toNat ≤ 28 := by
    simpa [symbolLengthCode, lengthTable] using
      Zlib.Trees.Proofs.Out.length_code_le length.toNat lengthBound
  obtain ⟨dc, _, code, dcBound⟩ := distance_code_run base.static (distance.toUInt16 - 1) index.2.2
  have dcIndex : dcodeN (distance.toNat - 1) < 30 := by
    rw [index.2.1] at code
    omega
  have nonzero : distance.toNat ≠ 0 := by omega
  have packedDistance : UInt16.ofNat distance.toNat = distance.toUInt16 := by
    apply UInt16.toNat_inj.mp
    simp
  have packedLength : UInt8.ofNat length.toNat = length.toUInt8 := by
    apply UInt8.toNat_inj.mp
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have count : (matchSymbolState d distance length).sym_next.toNat = d.sym_next.toNat + 3 :=
      literal_count base room 0
    rw [count, ledger.count]
    simp [List.length_append, Nat.mul_add]
  · intro s member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ledger.valid s member
    · exact ⟨distanceBound, lengthBound⟩
  · apply packed_symbols_write ledger.packed
    intro i
    simpa [ledger.count, packedDistance, packedLength] using
      match_bytes_view buf d distance.toUInt16 length.toUInt8 fit i
  · intro k bound
    change ((bumpFc d.dyn_ltree
      (Zlib.Trees.length_code_tab[length.toUInt8.toNat]!.toNat + 256 + 1))[k]!).fc.toNat = _
    rw [lengthNarrow]
    change ((bumpFc d.dyn_ltree (symbolLengthCode length.toNat + 256 + 1))[k]!).fc.toNat = _
    rw [bump_frequency_nat (by rw [base.wf.1]; omega) (freqRoom.2.1 _ (by omega)),
      ledger.literal k bound, literal_frequency_snoc]
    simp [Symbol.literalKey, nonzero, Nat.add_assoc, eq_comm]
  · intro k bound
    change ((bumpFc d.dyn_dtree (dcodeN (distance.toUInt16 - 1).toNat))[k]!).fc.toNat = _
    rw [index.2.1, bump_frequency_nat (by rw [base.wf.2.1]; omega) (freqRoom.2.2 _ dcIndex),
      ledger.distance k bound, distance_frequency_snoc]
    simp [Symbol.distanceKey, nonzero, eq_comm]

/-- The execution and semantic ledger concern exactly the same returned
heap, including the full-buffer flag. -/
theorem tally_literal_ledger {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) (c : UInt8) :
    tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end,
      setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)) ∧
    SymbolLedger (literalBytes buf d c) (literalState d c) (xs ++ [⟨0, c.toNat⟩]) :=
  ⟨tally_literal_run base c room, ledger_literal base ledger room c⟩

theorem tally_match_ledger {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (base : TreesBase h ds d b buf) (ledger : SymbolLedger buf d xs)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) (distance length : UInt32)
    (positive : 1 ≤ distance.toNat) (distanceBound : distance.toNat ≤ 32768)
    (lengthBound : length.toNat < 256) :
    tally_dist (some (.tab ds)) distance length h = .ok (d.sym_next + 3 == d.sym_end,
      setD (Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d distance.toUInt16 length.toUInt8)) ds
        (matchSymbolState d distance length)) ∧
    SymbolLedger (matchBytes buf d distance.toUInt16 length.toUInt8)
      (matchSymbolState d distance length) (xs ++ [⟨distance.toNat, length.toNat⟩]) :=
  ⟨tally_match_run base distance length positive distanceBound room,
    ledger_match base ledger room distance length positive distanceBound lengthBound⟩

/-- The ledger starts at the actual public default initialization. The
pending array is obtained from the returned owned storage. -/
theorem default_initialization_ledger {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : ZlibF.Spec.Public.LibraryGlobals h) (hz : r.get h = some z)
    (ha : ZlibF.Spec.Public.DefaultOrNull z) (hv : ZlibF.Spec.Public.VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf b buf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ ZlibF.Spec.Public.DeflateInitial h after r p ∧
      ZlibF.Spec.Public.StreamReachable .deflate after r ∧
      sf.pending_buf = .ref (.blk b) 0 ∧ after.bytes b = some buf ∧ SymbolLedger buf sf [] := by
  obtain ⟨after, zf, sf, run, start, initial, reachable, frequencies⟩ :=
    SymbolInit.default_initialization_frequencies hf hu hg hz ha hv params alloc
  obtain ⟨w, p0, q, b, blocks⟩ := start.good.inv.blocks
  obtain ⟨buf, get, _⟩ := blocks.ba
  exact ⟨after, zf, sf, b, buf, run, start, initial, reachable, blocks.pbuf, get,
    empty_symbol_ledger start.symbols frequencies⟩

end Zlib.Deflate.Engine.Proofs
