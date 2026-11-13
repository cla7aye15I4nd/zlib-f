import ZlibF.Proof.«inflate.c.gzip-header-dispatch»
import ZlibF.Proof.«inflate.c.block-type»

/-!
# inflate.c: a gzip header dispatch under the default relation

Lifts one dispatch from a gzip header mode (`FLAGS` .. `HCRC`) to
`DefaultStateJ`, and carries the per-call facts the gzip header modes need
(`GzipDispatchLocal`) to the next dispatch while the decoder stays in a
header mode.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The per-call facts a dispatch in `HEAD` .. `HCRC` uses besides the
representation: the local `hbuf`, its separation from the header record's
caller regions, the header record, the `extra` buffer apart from the unread
input, and, in `EXTRA`, the extra length still the one `EXLEN` stored. -/
structure GzipDispatchLocal (c : Ctx) (h : Heap) (r : ZStreamRef) (s : InflateState) (l : IL) : Prop where
  hbuf : LocalHbuf c h
  apart : HbufApart c h s.head
  record : HeaderMemory h r s.head true
  extraApart : ExtraApart h s.head l
  extraLen : s.mode = EXTRA → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
    s.length ≤ g.extra_len

theorem separate_symm {p q : BPtr} {n m : Nat} (separate : Separate p n q m) : Separate q m p n := by
  rcases separate with empty | empty | apart
  · exact Or.inr (Or.inl empty)
  · exact Or.inl empty
  · right
    right
    cases p with
    | null => cases q <;> trivial
    | ref r i =>
      cases q with
      | null => trivial
      | ref s j =>
        rcases apart with different | before | after
        · exact Or.inl (Ne.symm different)
        · exact Or.inr (Or.inr before)
        · exact Or.inr (Or.inl after)

/-- A range apart from the unread input stays apart after input is consumed. -/
theorem separate_input_advance {p q : BPtr} {n m used : Nat} (bound : used ≤ m)
    (separate : Separate p n q m) : Separate p n (inputAdvance q used) (m - used) :=
  separate_symm (inputAdvance_separate q p m n used bound (separate_symm separate))

theorem LocalHbuf.transfer {c : Ctx} {h after : Heap} (hbuf : LocalHbuf c h)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref) :
    LocalHbuf c after := by
  obtain ⟨b, a, at_, get, size, writable⟩ := hbuf
  obtain ⟨a', get', size'⟩ := sizes.view (ref := BRef.blk b) get
  exact ⟨b, a', at_, get', size'.trans size, by rw [← writable]; exact readonly (BRef.blk b)⟩

theorem HeaderRegions.of_headers {h after : Heap} (head : GzHeaderPtr) (headers : after.gzheaders = h.gzheaders) :
    HeaderRegions after head = HeaderRegions h head := by
  unfold HeaderRegions
  rw [headers]

theorem HbufApart.of_headers {c : Ctx} {h after : Heap} {head : GzHeaderPtr} (apart : HbufApart c h head)
    (headers : after.gzheaders = h.gzheaders) : HbufApart c after head := by
  intro b at_ region member
  rw [HeaderRegions.of_headers head headers] at member
  exact apart b at_ region member

theorem HeaderMemory.transfer {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {head : GzHeaderPtr} (record : HeaderMemory h r head true)
    (before : Good h r zs z s) (current : Good after r zs stream state) (window : state.window = s.window)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (headers : after.gzheaders = h.gzheaders) : HeaderMemory after r head true := by
  rcases record with none | ⟨i, g, pointer, get, notOwned, extra, name, comment⟩
  · exact Or.inl none
  refine Or.inr ⟨i, g, pointer, by rw [headers]; exact get, ?_, ?_, ?_, ?_⟩
  · intro owned
    apply notOwned
    rw [before.streamOwned_iff]
    rw [current.streamOwned_iff] at owned
    unfold InflateOwned at owned ⊢
    rw [window] at owned
    exact owned
  · intro nonnull
    exact callerRange_capacity before current window sizes readonly (extra nonnull)
  · intro nonnull
    exact callerRange_capacity before current window sizes readonly (name nonnull)
  · intro nonnull
    exact callerRange_capacity before current window sizes readonly (comment nonnull)

theorem ExtraApart.advance {h after : Heap} {head : GzHeaderPtr} {l regs : IL} {used : Nat}
    (apart : ExtraApart h head l) (headers : after.gzheaders = h.gzheaders)
    (next : regs.next = inputAdvance l.next used) (count : regs.have_.toNat + used = l.have_.toNat) :
    ExtraApart after head regs := by
  intro i g attached get
  rw [headers] at get
  have base := apart i g attached get
  have shifted := separate_input_advance (used := used) (by omega) base
  rw [next]
  have size : regs.have_.toNat = l.have_.toNat - used := by omega
  rw [size]
  exact shifted

/-- The per-call header facts are needed only while the decoder is in `HEAD`
.. `HCRC`; header modes come first in a call and do not come back. -/
def HeaderLocal (c : Ctx) (h : Heap) (r : ZStreamRef) (s : InflateState) (l : IL) : Prop :=
  HEAD ≤ s.mode → s.mode ≤ HCRC → GzipDispatchLocal c h r s l

/-- The per-call header facts carry over to a heap with the same header
records, sizes and read-only flags, and a state with the same header record,
window, mode and length. -/
theorem GzipDispatchLocal.transfer {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l : IL} (local_ : GzipDispatchLocal c h r s l)
    (before : Good h r zs z s) (current : Good after r zs stream state) (window : state.window = s.window)
    (head : state.head = s.head) (mode : state.mode = s.mode) (length : state.length = s.length)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (headers : after.gzheaders = h.gzheaders) : GzipDispatchLocal c after r state l := by
  refine ⟨local_.hbuf.transfer sizes readonly, ?_, ?_, ?_, ?_⟩
  · rw [head]
    exact local_.apart.of_headers headers
  · rw [head]
    exact HeaderMemory.transfer local_.record before current window sizes readonly headers
  · rw [head]
    have same := local_.extraApart.advance (used := 0) (regs := l) headers (inputAdvance_zero l.next).symm (by omega)
    exact same
  · intro extra i g attached get
    rw [mode] at extra
    rw [head] at attached
    rw [headers] at get
    rw [length]
    exact local_.extraLen extra i g attached get

theorem HeaderLocal.transfer {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l : IL} (local_ : HeaderLocal c h r s l)
    (before : Good h r zs z s) (current : Good after r zs stream state) (window : state.window = s.window)
    (head : state.head = s.head) (mode : state.mode = s.mode) (length : state.length = s.length)
    (sizes : ByteViewSizes h after) (readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref)
    (headers : after.gzheaders = h.gzheaders) : HeaderLocal c after r state l := by
  intro low high
  rw [mode] at low high
  exact (local_ low high).transfer before current window head mode length sizes readonly headers

/-- Past the header range the per-call header facts are vacuous. -/
theorem HeaderLocal.of_mode {c : Ctx} {h : Heap} {r : ZStreamRef} {s : InflateState} {l : IL}
    (high : DICTID ≤ s.mode) : HeaderLocal c h r s l := by
  intro _ low
  rw [UInt32.le_iff_toNat_le] at high low
  change 16189 ≤ s.mode.toNat at high
  change s.mode.toNat ≤ 16188 at low
  omega

/-- With no header record, only the local array matters. -/
theorem GzipDispatchLocal.of_none {c : Ctx} {h : Heap} {r : ZStreamRef} {s : InflateState} {l : IL}
    (hbuf : LocalHbuf c h) (none : s.head = none) :
    GzipDispatchLocal c h r s l := by
  refine ⟨hbuf, ?_, Or.inl none, ?_, fun _ i _ attached => by rw [none] at attached; cases attached⟩
  · intro b _ region member
    rw [none] at member
    simp [HeaderRegions] at member
  · intro i g attached
    rw [none] at attached
    cases attached

/-- A header dispatch keeps the extra buffer or sets it to `Z_NULL`, so the
extra buffer stays apart from the input that remains. -/
theorem ExtraApart.of_kept {h after : Heap} {head : GzHeaderPtr} {l regs : IL} {used : Nat}
    (apart : ExtraApart h head l) (kept : RegionsKept (HeaderRegions after head) (HeaderRegions h head))
    (next : regs.next = inputAdvance l.next used) (count : regs.have_.toNat + used = l.have_.toNat) :
    ExtraApart after head regs := by
  intro i g' attached get'
  cases getBefore : h.gzheaders i with
  | none =>
    simp only [HeaderRegions, attached, get', getBefore, RegionsKept] at kept
  | some g =>
    simp only [HeaderRegions, attached, get', getBefore, RegionsKept] at kept
    obtain ⟨first, _⟩ := kept
    have size : regs.have_.toNat = l.have_.toNat - used := by omega
    rw [next, size]
    rcases first with same | ⟨null, _⟩
    · injection same with pointer length
      rw [pointer, length]
      exact separate_input_advance (by omega) (apart i g attached getBefore)
    · right
      right
      change g'.extra = .null at null
      rw [null]
      cases inputAdvance l.next used <;> trivial

/-- One dispatch from a gzip header mode keeps the default relation, the
caller packet up to the bytes of the unread input, and the per-call header
facts while the decoder stays in a header mode. -/
theorem inflate_dispatch_gzip_header_state_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (header : GzipHeaderMode s)
    (local_ : GzipDispatchLocal c h r s l) (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧
      regs.have_.toNat + used = l.have_.toNat ∧ regs.put = l.put ∧ regs.left = l.left ∧
      regs.out_ = l.out_ ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
      GzipHeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧ GzipHeaderFootprint c r zs s h after ∧
      RegionsKept (HeaderRegions after state.head) (HeaderRegions h s.head) ∧
      ((FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨ state.mode = TYPE ∨ state.mode = BAD) ∧
      (outcome = .error Ex.leave → regs.have_ = 0) ∧
      HeaderLocal c after r state regs ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  obtain ⟨low, high, gzip, read⟩ := header
  obtain ⟨outcome, regs, after, stream, state, used, bound, run, good, pending, packet, sizes, next, count,
    put, left, out, bits, static, hbuf, apart, frame, streamFrame, footprint, record, kept, extraLen, modes,
    flagsRead, leaveCause, progress⟩ :=
    inflate_dispatch_gzip_header_rank E invariant.good invariant.pending buffers local_.hbuf local_.apart
      local_.record invariant.globals local_.extraApart local_.extraLen ⟨low, high⟩ gzip read incoming
  have wrapEq : state.wrap = s.wrap := by rw [frame]
  have headEq : state.head = s.head := by rw [frame]
  have gzipAfter : GzipAllowed state.wrap := by rw [wrapEq]; exact gzip
  have range : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 := by
    rcases invariant.phase with e | e | e | e | done | pending
    · rw [e] at low; exact absurd low (by decide)
    · rw [e] at high; exact absurd high (by decide)
    · rw [e] at high; exact absurd high (by decide)
    · rw [e] at high; exact absurd high (by decide)
    · exact invariant.range_of_read done
    · exact invariant.range_of_pending pending
  have rangeAfter : 8 ≤ state.wbits.toNat ∧ state.wbits.toNat ≤ 15 := by
    have same : state.wbits = s.wbits := by rw [frame]
    rw [same]
    exact range
  have notData : ¬ DataTableMode state.mode := by
    rcases modes with ⟨l1, h1⟩ | e | e
    · unfold DataTableMode
      rw [UInt32.le_iff_toNat_le] at l1 h1
      intro active
      rcases active with a | a | a | a | a | a | a <;> rw [a] at l1 h1 <;> exact absurd h1 (by decide)
    · rw [e]; unfold DataTableMode; decide
    · rw [e]; unfold DataTableMode; decide
  have below : state.mode ≠ CODELENS ∧ state.mode ≠ LENLENS ∧ state.mode ≠ CHECK ∧ state.mode ≠ LENGTH := by
    rcases modes with ⟨l1, h1⟩ | e | e
    · rw [UInt32.le_iff_toNat_le] at h1
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> rw [a] at h1 <;> exact absurd h1 (by decide)
    · rw [e]; decide
    · rw [e]; decide
  have base : DefaultDecodeJ after r zs stream state := by
    refine ⟨good, dataTableInvariant_inactive notData, pending, fun a => absurd a below.1,
      fun a => absurd a below.2.1, by rw [frame]; exact invariant.held, Or.inl rangeAfter,
      by rw [wrapEq]; exact invariant.wrapper, fun _ => gzipAfter, ?_,
      fun late => by rcases late with a | a <;> exact absurd a (by first | exact below.2.2.1 | exact below.2.2.2),
      by change after.static = _; rw [static]; exact invariant.globals, sizes.platform invariant.platform⟩
    rcases modes with ⟨l1, h1⟩ | e | e
    · refine Or.inr (Or.inr ⟨l1, h1, gzipAfter, fun past => flagsRead ?_ ?_⟩)
      · intro bad; rw [bad] at h1; exact absurd h1 (by decide)
      · intro atFlags; rw [atFlags] at past; exact absurd past (by decide)
    · exact Or.inr (Or.inl (by rw [e]; decide))
    · exact Or.inr (Or.inl (by rw [e]; decide))
  have final : DefaultStateJ after r zs stream state := by
    refine ⟨base, ?_, ?_, ?_⟩
    · have bitsEq : state.reqbits = s.reqbits := by rw [frame]
      have widthEq : state.wbits = s.wbits := by rw [frame]
      have reqwrapEq : state.reqwrap = s.reqwrap := by rw [frame]
      exact invariant.requestedBits.congr bitsEq widthEq reqwrapEq
    · have reqwrapEq : state.reqwrap = s.reqwrap := by rw [frame]
      exact invariant.requestedWrap.congr reqwrapEq wrapEq
    · by_cases bad : state.mode = BAD
      · exact Or.inr (Or.inl bad)
      by_cases atFlags : state.mode = FLAGS
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨atFlags, gzipAfter, fun zero => by
          rw [zero] at rangeAfter; exact absurd rangeAfter.1 (by decide)⟩))))
      · obtain ⟨readFlags, nonzero⟩ := flagsRead bad atFlags
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨gzipAfter, readFlags, nonzero⟩))))))
  refine ⟨outcome, regs, after, stream, state, used, bound, run, final, packet, sizes, next, count, put, left,
    out, bits, static, frame, streamFrame, footprint, kept, modes, leaveCause, ?_, progress⟩
  intro _ _
  have kept' : RegionsKept (HeaderRegions after s.head) (HeaderRegions h s.head) := by
    rw [headEq] at kept
    exact kept
  refine ⟨hbuf, apart, record, ?_, extraLen⟩
  rw [headEq]
  exact ExtraApart.of_kept local_.extraApart kept' next count

#print axioms inflate_dispatch_gzip_header_state_rank
end Zlib.Inflate.Proofs
