import ZlibF.Proof.«inflate.c.head-default-state»
import ZlibF.Proof.«inflate.c.gzip-header-state»

/-!
# inflate.c: `case HEAD` under the default relation when gzip is allowed

With `wrap & 2`, `case HEAD` either sees the gzip magic bytes and enters
`FLAGS` (writing `hbuf` and the CRC-32 of the two bytes), or marks an
attached header record as not gzip (`done = -1`) and runs the zlib header
checks on that heap. Both keep `DefaultStateJ`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The record write of `headDoneHeap`, as a `gz_header` store. -/
theorem headDoneHeap_tab {h : Heap} {i : Nat} {g : GzHeader} (get : h.gzheaders i = some g) :
    headDoneHeap h (some (.tab i)) = (GzHeaderRef.tab i).put h { g with done := -1 } := by
  simp only [headDoneHeap, get, GzHeaderRef.put_tab get]

theorem headDoneHeap_views (h : Heap) (head : GzHeaderPtr) (ref : BRef) :
    (Space.get (headDoneHeap h head) ref : Option (Array UInt8)) = Space.get h ref := by
  unfold headDoneHeap
  split
  · rfl
  · split
    · cases ref <;> rfl
    · rfl

theorem headDoneHeap_ro (h : Heap) (head : GzHeaderPtr) (ref : BRef) :
    Space.ro (headDoneHeap h head) ref = Space.ro h ref := by
  unfold headDoneHeap
  split
  · rfl
  · split
    · cases ref <;> rfl
    · rfl

theorem headDoneHeap_static (h : Heap) (head : GzHeaderPtr) :
    (headDoneHeap h head).static = h.static := by
  unfold headDoneHeap
  split
  · rfl
  · split <;> rfl

theorem headDoneHeap_good {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) (head : GzHeaderPtr) : Good (headDoneHeap h head) r zs z s := by
  cases head with
  | none => exact good
  | some ref =>
    cases ref with
    | tab i =>
      cases get : h.gzheaders i with
      | none => simp only [headDoneHeap, get]; exact good
      | some g =>
        rw [headDoneHeap_tab get]
        exact good.headerPut get _

/-- `HEAD` keeps `DefaultStateJ` across the header record's `done = -1`. -/
theorem DefaultStateJ.headDone {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (mode : s.mode = HEAD) :
    DefaultStateJ (headDoneHeap h s.head) r zs z s := by
  have sizes : ByteViewSizes h (headDoneHeap h s.head) := by
    intro ref
    rw [headDoneHeap_views]
  refine ⟨⟨headDoneHeap_good invariant.good s.head,
    dataTableInvariant_inactive (by rw [mode]; unfold DataTableMode; decide),
    invariant.pending, invariant.lengths, invariant.headerLengths, invariant.held, invariant.window,
    invariant.wrapper, invariant.header, invariant.modes, invariant.trailer, ?_,
    sizes.platform invariant.platform⟩, invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩
  change (headDoneHeap h s.head).static = _
  rw [headDoneHeap_static]
  exact invariant.globals

#print axioms DefaultStateJ.headDone

/-- The state after the gzip magic bytes is in `FLAGS` with a window width. -/
theorem headGzipState_mode (s : InflateState) (word : UInt64) : (headGzipState s word).mode = FLAGS := rfl

theorem headGzipState_width {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultDecodeJ h r zs z s) (word : UInt64) :
    8 ≤ (headGzipState s word).wbits.toNat ∧ (headGzipState s word).wbits.toNat ≤ 15 := by
  by_cases zero : s.wbits = 0
  · simp only [headGzipState, zero, ↓reduceIte]
    decide
  · simp only [headGzipState, zero, ↓reduceIte]
    exact invariant.range_of_nonzero zero

/-- After the gzip magic bytes: the representation and the default relation
hold on the heap with the two `hbuf` bytes and the new state. -/
theorem headGzip_default_state {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (mode : s.mode = HEAD) (gzip : GzipAllowed s.wrap)
    {b : Nat} {a : Array UInt8} (bytes : h.bytes b = some a) (writable : h.ro b = false) (word : UInt64) :
    let after := setI (Space.put h (BRef.blk b) (crc2Bytes a word)) zs (headGzipState s word)
    DefaultStateJ after r zs z (headGzipState s word) ∧ ByteViewSizes h after ∧
      (∀ ref : BRef, Space.ro after ref = Space.ro h ref) ∧ after.static = h.static := by
  intro after
  let state := headGzipState s word
  let h1 := Space.put h (BRef.blk b) (crc2Bytes a word)
  have good1 : Good h1 r zs z s :=
    invariant.good.byte_view_put_sized (dest := BRef.blk b) bytes writable (crc2Bytes a word)
      (crc2Bytes_size a word)
  have width := headGzipState_width invariant.toDefaultDecodeJ word
  have inv : StInv h1 zs state := by
    apply good1.inv.with_width rfl rfl rfl rfl rfl rfl rfl rfl good1.inv.bits rfl rfl rfl width.2
    by_cases zero : s.wbits = 0
    · right
      rcases invariant.window with range | ⟨_, null, _, _⟩
      · rw [zero] at range
        exact absurd range.1 (by decide)
      · exact null
    · left
      simp only [state, headGzipState, zero, ↓reduceIte]
  have good2 : Good (setI (r.put h1 z) zs state) r zs z state :=
    good1.setZI rfl good1.live.zalloc good1.live.zfree rfl (by change HEAD ≤ FLAGS ∧ FLAGS ≤ SYNC; decide) inv
  have stream1 : r.get h1 = some z := by cases r <;> exact invariant.good.live.hz
  rw [ZStreamRef.put_self stream1] at good2
  have sizes : ByteViewSizes h after := by
    intro ref
    change (Space.get (setI h1 zs state) ref : Option (Array UInt8)).map Array.size = _
    rw [byte_view_get_setI]
    cases ref with
    | blk w =>
      by_cases same : w = b
      · subst w
        simp only [h1, Space.get, Space.put, upd_same, bytes, Option.map_some, crc2Bytes_size]
      · simp only [h1, Space.get, Space.put, upd_ne _ _ _ _ same]
    | _ => rfl
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    change Space.ro (setI h1 zs state) ref = _
    rw [byte_view_ro_setI]
    cases ref <;> rfl
  have static : after.static = h.static := rfl
  refine ⟨⟨⟨good2, dataTableInvariant_inactive (by change ¬ DataTableMode FLAGS; unfold DataTableMode; decide),
    ?_, fun active => absurd active (by change FLAGS ≠ CODELENS; decide),
    fun active => absurd active (by change FLAGS ≠ LENLENS; decide), invariant.held, Or.inl width,
    invariant.wrapper, invariant.header, Or.inr (Or.inr ⟨by change FLAGS ≤ FLAGS; decide,
      by change FLAGS ≤ HCRC; decide, gzip, fun past => absurd past (by change ¬ FLAGS < FLAGS; decide)⟩),
    fun late => by rcases late with e | e <;> exact absurd e (by change FLAGS ≠ _; decide),
    by change after.static = _; rw [static]; exact invariant.globals, sizes.platform invariant.platform⟩,
    ?_, invariant.requestedWrap, ?_⟩, sizes, readonly, static⟩
  · apply dataPendingInvariant_idle (s := state) invariant.pending.sane
    change FLAGS ≠ LENEXT ∧ FLAGS ≠ DIST ∧ FLAGS ≠ DISTEXT ∧ FLAGS ≠ MATCH
    decide
  · apply invariant.requestedBits.with_width
    by_cases zero : s.wbits = 0
    · exact Or.inr zero
    · left
      simp only [state, headGzipState, zero, ↓reduceIte]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, gzip, ?_⟩))))
    intro zero
    have low := width.1
    rw [zero] at low
    exact absurd low (by decide)

#print axioms headGzip_default_state

end Zlib.Inflate.Proofs
