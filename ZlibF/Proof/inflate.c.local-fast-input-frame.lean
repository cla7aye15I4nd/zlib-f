import ZlibF.Proof.«inflate.c.local-fast-effect»
import ZlibF.Proof.«inflate.c.fast-view-caller-buffers»

/-! Actual source frames retain arbitrary caller input views using only
uniqueness at the stream roots allocated by real initialization. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The caller's byte root cannot be a newly allocated stream record.
Only uniqueness at that actual private root is used. -/
theorem caller_byte_root_not_stream {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs off b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {array : Array UInt8}
    (invariant : LocalStateJ h cutoff r zs z s) (get : Space.get h ref = some array)
    (root : ByteRoot (.ref ref off) b) : ¬ StreamRoot r b := by
  intro stream
  have age := invariant.roots.stream b stream
  have unique := invariant.good.unique b age
  have absent : h.streams b = none ∧ h.gzstates b = none := by
    cases ref with
    | blk i =>
      change b = i at root
      subst b
      change h.bytes i = some array at get
      simp only [get, cnt_some] at unique
      constructor
      · cases slot : h.streams i with
        | none => rfl
        | some value => simp only [slot, cnt_some] at unique; omega
      · cases slot : h.gzstates i with
        | none => rfl
        | some value => simp only [slot, cnt_some] at unique; omega
    | dstate_depth i =>
      change b = i at root
      subst b
      cases state : h.dstates i with
      | none => simp [Space.get, state] at get
      | some value =>
        simp only [state, cnt_some] at unique
        constructor
        · cases slot : h.streams i with
          | none => rfl
          | some value => simp only [slot, cnt_some] at unique; omega
        · cases slot : h.gzstates i with
          | none => rfl
          | some value => simp only [slot, cnt_some] at unique; omega
    | str i => cases root
    | st_dist_code => cases root
    | st_length_code => cases root
  cases r with
  | tab i =>
    change b = i at stream
    have live := invariant.good.live.hz
    simp only [ZStreamRef.get, ← stream, absent.1] at live
    contradiction
  | in_gzstate_strm i =>
    change b = i at stream
    have live := invariant.good.live.hz
    simp only [ZStreamRef.get, ← stream, absent.2, Option.map_none] at live
    contradiction

/-- Caller ownership and the good heap derive the input exclusion needed
by the fast frame consumer. No allocation-identity premise is required. -/
theorem caller_byte_root_outside
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs off count b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {array : Array UInt8}
    (invariant : LocalStateJ h cutoff r zs z s) (get : Space.get h ref = some array)
    (range : CallerRange h r (.ref ref off) count false)
    (root : ByteRoot (.ref ref off) b) :
    ¬ (StreamRoot r b ∨ InflateOwned zs s b) := by
  rcases range with null | ⟨_, _, outside⟩
  · cases null
  · rintro (stream | owned)
    · exact caller_byte_root_not_stream invariant get root stream
    · exact outside b root ((invariant.good.streamOwned_iff b).mpr owned)

/-- The permitted fast output interval leaves every byte of a disjoint
caller input range unchanged, including shared objects and empty ranges,
when its external borrow remains stable. -/
theorem caller_input_bytes_preserved
    {before after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs writeOff capacity count : Nat}
    {z : ZStream} {s : InflateState} {p : BPtr} {dest : BRef}
    {output : Array UInt8} {xs : List UInt8}
    (invariant : LocalStateJ before cutoff r zs z s)
    (range : CallerRange before r p count false)
    (outputGet : Space.get before dest = some output)
    (bytes : Bytes before p count xs)
    (separate : Separate p count (.ref dest writeOff) capacity)
    (frame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest writeOff, capacity⟩])
    (stable : ∀ {ref off input}, p = .ref ref off →
      Space.get before ref = some input → C.LibcBorrow.BorrowStable before after ref) :
    Bytes after p count xs := by
  rcases bytes with null | ⟨source, off, input, pointer, get, bound, values⟩
  · exact Or.inl null
  · subst p
    have outside := fun b root => caller_byte_root_outside invariant get range (b := b) root
    by_cases shared : source = dest
    · subst source
      rw [values]
      exact BufferFrame.same_view_separate_read frame get bound separate
    · exact Or.inr ⟨source, off, input, rfl,
        BufferFrame.other_view_get frame get outputGet outside shared (stable rfl get), bound, values⟩

/-- An actual output frame preserves the unconsumed input bytes after
cursor rollback. Existing readable-view observations establish borrow stability.
The held-bit bound is supplied for the returned registers. -/
theorem output_frame_advance_bits
    {before after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs writeOff capacity used : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8}
    {dest : BRef} {output : Array UInt8}
    (invariant : LocalStateJ before cutoff r zs z s) (B : BitInv before l bs)
    (sizes : ByteViewSizes before after)
    (range : CallerRange before r l.next l.have_.toNat false)
    (outputGet : Space.get before dest = some output)
    (separate : Separate l.next l.have_.toNat (.ref dest writeOff) capacity)
    (frame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest writeOff, capacity⟩])
    (bound : used ≤ bs.length)
    (cursor : regs.next = inputAdvance l.next used)
    (count : regs.have_.toNat + used = l.have_.toNat)
    (held : regs.hold.toNat < 2 ^ regs.bits.toNat) :
    BitInv after regs (bs.drop used) := by
  have retained : BitInv after l bs := by
    refine ⟨B.have_eq, ?_, B.hold_lt⟩
    rcases B.next with empty | ⟨ref, array, off, pointer, get, fit, content⟩
    · exact Or.inl empty
    · have read : Bytes before l.next bs.length bs :=
        Or.inr ⟨ref, off, array, pointer, get, fit, content⟩
      have range' : CallerRange before r l.next bs.length false := by
        simpa only [B.have_eq] using range
      have separate' : Separate l.next bs.length (.ref dest writeOff) capacity := by
        simpa only [B.have_eq] using separate
      have readAfter := caller_input_bytes_preserved invariant range' outputGet read separate' frame
        (fun _ get => sizes.readable_stable get)
      rcases readAfter with ⟨_, zero, empty⟩ | ⟨ref, off, array, ptr, get, fit, content⟩
      · exact Or.inl empty
      · exact Or.inr ⟨ref, array, off, ptr, get, fit, content⟩
  have advanced := retained.advance_bytes (regs := { regs with hold := l.hold, bits := l.bits })
    bound cursor count rfl rfl
  exact ⟨advanced.have_eq, advanced.next, held⟩

/-- Exact caller byte accounting and the output interval frame retain the
whole dispatch packet on generic input/output views. -/
theorem output_frame_advance_packet
    {before after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs used made : Nat}
    {z zNext : ZStream} {s sNext : InflateState} {l regs : IL} {bs : List UInt8}
    {dest : BRef} {writeOff : Nat} {output : Array UInt8}
    (buffers : DispatchBuffers before r l bs)
    (invariant : LocalStateJ before cutoff r zs z s) (current : LocalGood after cutoff r zs zNext sNext)
    (window : sNext.window = s.window)
    (sizes : ByteViewSizes before after)
    (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro before ref)
    (outputPtr : l.put = .ref dest writeOff)
    (outputGet : Space.get before dest = some output)
    (frame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨l.put, l.left.toNat⟩])
    (next : regs.next = inputAdvance l.next used)
    (haveCount : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = inputAdvance l.put made)
    (left : regs.left.toNat + made = l.left.toNat)
    (total : regs.out_ = l.out_)
    (held : regs.hold.toNat < 2 ^ regs.bits.toNat) :
    DispatchBuffers after r regs (bs.drop used) := by
  have bound : used ≤ bs.length := by rw [← buffers.bits.have_eq]; omega
  have separate : Separate l.next l.have_.toNat (.ref dest writeOff) l.left.toNat := by
    simpa only [outputPtr] using buffers.separate
  have normalizedFrame : BufferFrame before after
      (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest writeOff, l.left.toNat⟩] := by
    simpa only [outputPtr] using frame
  have bits := output_frame_advance_bits invariant buffers.bits sizes buffers.input outputGet
    separate normalizedFrame bound next haveCount held
  exact dispatch_advance_both_local buffers invariant.good current window sizes readonly next haveCount
    put left total bits


end Zlib.Inflate.Local
