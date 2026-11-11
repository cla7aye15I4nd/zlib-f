import ZlibF.Proof.«inflate.c.gzip-header-state»
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

/-- Each caller region the header record names after a step is the region
it named before, or its pointer was set to `Z_NULL` (the header has no extra
field, name or comment), with the same maximum length. -/
def RegionsKept : List Region → List Region → Prop
  | [], [] => True
  | a :: after, b :: before =>
    (a = b ∨ (a.pointer = .null ∧ a.length = b.length)) ∧ RegionsKept after before
  | _, _ => False

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

/-- WORKER STUB: batch 2 proves this statement (skeleton/inflate). -/
theorem inflate_dispatch_gzip_header_rank {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (hbuf : LocalHbuf c h) (apart : HbufApart c h s.head)
    (record : HeaderMemory h r s.head true) (globals : LibraryGlobals h)
    (extraApart : ExtraApart h s.head l)
    (extraLen : s.mode = EXTRA → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
      s.length ≤ g.extra_len)
    (mode : FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) (gzip : GzipAllowed s.wrap)
    (flags : FLAGS < s.mode → s.flags ≠ -1 ∧ s.flags ≠ 0)
    (incoming : l.bits.toNat ≤ 39) :
    ∃ outcome regs after stream state used, used ≤ bs.length ∧
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ DataPendingInvariant state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧ regs.bits.toNat ≤ 39 ∧
      after.static = h.static ∧ LocalHbuf c after ∧ HbufApart c after state.head ∧
      GzipHeaderStateFrame s state ∧ HeaderStreamFrame z stream ∧
      GzipHeaderFootprint c r zs s h after ∧ HeaderMemory after r state.head true ∧
      RegionsKept (HeaderRegions after state.head) (HeaderRegions h s.head) ∧
      (state.mode = EXTRA → ∀ i g, state.head = some (.tab i) → after.gzheaders i = some g →
        state.length ≤ g.extra_len) ∧
      ((FLAGS ≤ state.mode ∧ state.mode ≤ HCRC) ∨ state.mode = TYPE ∨ state.mode = BAD) ∧
      (state.mode ≠ BAD → state.mode ≠ FLAGS → state.flags ≠ -1 ∧ state.flags ≠ 0) ∧
      (outcome = .error Ex.leave → regs.have_ = 0) ∧
      (outcome = .error Ex.leave ∨
        (outcome = .ok () ∧ dispatchRank regs state.mode < dispatchRank l s.mode)) := by
  sorry

end Zlib.Inflate.Proofs
