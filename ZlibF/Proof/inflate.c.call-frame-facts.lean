import ZlibF.Proof.«inflate.c.call-dispatch-frame»
import ZlibF.Proof.«inflate.c.entry-header»

/-!
# inflate.c: the caller facts the call frame needs

At the start of the public body (after `hbuf[4]` is declared), the output
buffer and the header record's buffers are writable views. By uniqueness of
block numbers they are not the stream, the state, the attached header record
or the fresh `hbuf`, and by the caller range they are not the saved window.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A writable byte view of the caller is a byte array or a deflate `depth`
array in a block the call does not change. -/
theorem writable_view_unchanged {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {flush : Int32} (good : Good h r zs z s) (record : HeaderMemory h r s.head true)
    {ref : BRef} {a : Array UInt8} (get : Space.get h ref = some a) (write : Space.ro h ref = false) :
    (∃ i, ref = .blk i ∧ ¬ CallChanged ⟨some r, some (.tab zs), syncBuf h, flush⟩ r zs s.head i) ∨
      (∃ i, ref = .dstate_depth i ∧ ¬ CallChanged ⟨some r, some (.tab zs), syncBuf h, flush⟩ r zs s.head i) := by
  have notHeader : ∀ i, (h.bytes i ≠ none ∨ h.dstates i ≠ none) → s.head ≠ some (.tab i) := by
    intro i present attached
    rcases record with none | ⟨j, g, pointer, headerGet, _⟩
    · rw [none] at attached
      cases attached
    · rw [attached] at pointer
      cases pointer
      have count := good.uniq i
      rw [headerGet] at count
      rcases present with e | e
      · cases x : h.bytes i with
        | none => exact e x
        | some _ => simp only [x, cnt_some] at count; omega
      · cases x : h.dstates i with
        | none => exact e x
        | some _ => simp only [x, cnt_some] at count; omega
  have notState : ∀ i, (h.bytes i ≠ none ∨ h.dstates i ≠ none) → i ≠ zs := by
    intro i present same
    subst same
    have count := good.uniq i
    rw [good.live.hs] at count
    rcases present with e | e
    · cases x : h.bytes i with
      | none => exact e x
      | some _ => simp only [x, cnt_some] at count; omega
    · cases x : h.dstates i with
      | none => exact e x
      | some _ => simp only [x, cnt_some] at count; omega
  have notLocal : ∀ i, (h.bytes i ≠ none ∨ h.dstates i ≠ none) → syncBuf h ≠ .ref (.blk i) 0 := by
    intro i present same
    change Ptr.ref (BRef.blk h.nextBlk) 0 = .ref (.blk i) 0 at same
    cases same
    have dead := fresh_dead good.fresh (Nat.le_refl h.nextBlk)
    rcases present with e | e
    · exact e dead.1
    · exact e dead.2.2.2.2.1
  cases ref with
  | blk i =>
    have present : h.bytes i ≠ none ∨ h.dstates i ≠ none := Or.inl (by
      change h.bytes i = some a at get; rw [get]; simp)
    refine Or.inl ⟨i, rfl, ?_⟩
    rintro (root | state | buf | head)
    · exact caller_byte_root_not_stream (off := 0) good get rfl root
    · exact notState i present state
    · exact notLocal i present buf
    · exact notHeader i present head
  | dstate_depth i =>
    have present : h.bytes i ≠ none ∨ h.dstates i ≠ none := Or.inr (by
      change (h.dstates i).map (·.depth) = some a at get
      intro none
      rw [none] at get
      cases get)
    refine Or.inr ⟨i, rfl, ?_⟩
    rintro (root | state | buf | head)
    · exact caller_byte_root_not_stream (off := 0) good get rfl root
    · exact notState i present state
    · exact notLocal i present buf
    · exact notHeader i present head
  | str _ => simp [Space.ro] at write
  | st_dist_code => simp [Space.ro] at write
  | st_length_code => simp [Space.ro] at write

/-- A caller range written by the call names a writable view. -/
theorem callerRange_writable_view {h : Heap} {r : ZStreamRef} {pointer : BPtr} {size : Nat}
    (range : CallerRange h r pointer size true) {ref : BRef} {off : Nat} (at_ : pointer = .ref ref off) :
    ∃ a, Space.get h ref = some a ∧ Space.ro h ref = false := by
  rcases range with null | ⟨_, writable, _⟩
  · rw [at_] at null
    cases null
  · rcases writable rfl with ⟨null, _⟩ | ⟨ref', off', a, pointer, get, ro, _⟩
    · rw [at_] at null
      cases null
    · rw [at_] at pointer
      cases pointer
      exact ⟨a, get, ro⟩

/-- Every region a public call may write is a caller range written by the call. -/
theorem call_region_range {h : Heap} {r : ZStreamRef} {z : ZStream} {head : GzHeaderPtr}
    (output : CallerRange h r z.next_out z.avail_out.toNat true) (record : HeaderMemory h r head true)
    {region : Region} (member : region ∈ (⟨z.next_out, 0⟩ :: HeaderRegions h head))
    {ref : BRef} {off : Nat} (at_ : region.pointer = .ref ref off) :
    ∃ size, CallerRange h r region.pointer size true := by
  rcases List.mem_cons.mp member with rfl | header
  · exact ⟨_, output⟩
  · have nonnull : region.pointer ≠ .null := by rw [at_]; intro e; cases e
    rcases record with none | ⟨i, g, attached, get, _, extra, name, comment⟩
    · rw [none] at header
      simp [HeaderRegions] at header
    · rw [attached] at header
      simp only [HeaderRegions, get, List.mem_cons, List.not_mem_nil, or_false] at header
      rcases header with rfl | rfl | rfl
      · exact ⟨_, extra nonnull⟩
      · have range := name nonnull
        simp only [ite_true] at range
        exact ⟨_, range⟩
      · have range := comment nonnull
        simp only [ite_true] at range
        exact ⟨_, range⟩

/-- The caller's output buffer and header record give the call frame facts at
the start of the public body. -/
theorem call_frame_facts {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (buffers : StreamBuffers h r)
    (record : HeaderMemory h r s.head true) (flush : Int32) :
    CallFrameFacts ⟨some r, some (.tab zs), syncBuf h, flush⟩ (syncAlloc h) r zs z s := by
  have output : CallerRange h r z.next_out z.avail_out.toNat true := by
    obtain ⟨candidate, get, _input, output, _separate⟩ := buffers
    have equal : candidate = z := Option.some.inj (get.symm.trans invariant.good.live.hz)
    simpa only [equal] using output
  have regionsEq : HeaderRegions (syncAlloc h) s.head = HeaderRegions h s.head :=
    HeaderRegions.of_headers _ (syncAlloc_gzheaders h)
  refine ⟨?_, ?_⟩
  · rw [regionsEq]
    rintro ref ⟨region, member, off, at_⟩
    obtain ⟨size, range⟩ := call_region_range output record member at_
    obtain ⟨a, get, write⟩ := callerRange_writable_view range at_
    exact writable_view_unchanged invariant.good record get write
  · intro w window
    rw [regionsEq]
    rcases invariant.good.inv.win.block with null | ⟨w', a, at_, get, ro, _⟩
    · rw [null] at window
      cases window
    · rw [window] at at_
      cases at_
      refine ⟨?_, ?_⟩
      · rcases writable_view_unchanged (flush := flush) invariant.good record (ref := .blk w) get ro with
          ⟨i, e, unchanged⟩ | ⟨i, e, _⟩
        · cases e
          exact unchanged
        · cases e
      · rintro ⟨region, member, off, at_⟩
        obtain ⟨size, range⟩ := call_region_range output record member at_
        exact callerRange_private_window invariant.good range at_ w window rfl

#print axioms call_frame_facts
end Zlib.Inflate.Proofs
