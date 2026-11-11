import ZlibF.Proof.«inflate.c.default-origin-state»

/-!
# inflate.c: the decoder invariant over every reachable history (skeleton)

`InflateInv` generalizes `DefaultOriginState` to every configuration that
`inflateInit2_`, `inflateReset2` and `inflateValidate` can select: raw, zlib,
gzip and automatic detection, any window width 8 to 15, a width of 0 chosen
by the zlib header, and an attached gzip header record. It drops the platform
field: object sizes are a per-call premise of `Goal.inflate`, and
`StreamReachable` does not carry them.

Other modules use only the interface lemmas in this file, never the fields.
The remaining interface lemmas and the open proof steps are on the branch
`skeleton/inflate` and in `docs/progress.md`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Wrapper values that `inflateReset2` (0, 5, 6, 7) and `inflateValidate`
(clearing bit 2: 1, 2, 3) can store. -/
def WrapValue (w : Int32) : Prop :=
  w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5 ∨ w = 6 ∨ w = 7

/-- Bit 1 of the wrapper: a gzip header is accepted. -/
def GzipAllowed (w : Int32) : Prop :=
  w = 2 ∨ w = 3 ∨ w = 6 ∨ w = 7

/-- Configuration fields. A width of 0 occurs only before the header is
read, or when the header was rejected or a resync is under way; it has no
window. A gzip header record is attached only when gzip decoding is allowed. -/
structure InflateConfig (s : InflateState) : Prop where
  wrap : WrapValue s.wrap
  reqwrap : WrapValue s.reqwrap
  window : (8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) ∨
    (s.wbits = 0 ∧ s.window = .null ∧ (s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = SYNC))
  reqbits : s.reqbits = s.wbits ∨ (s.reqbits = 0 ∧ 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15)
  header : s.head ≠ none → GzipAllowed s.wrap
  raw : s.wrap = 0 → s.wbits ≠ 0
  reqraw : s.reqwrap = 0 → s.reqbits ≠ 0
  pair : s.wrap = 0 ∨ (GzipAllowed s.wrap ↔ GzipAllowed s.reqwrap)

/-- Header progress. Block decoding starts only after a header was read or
in raw mode. `flags` is the unread sentinel, 0 after a zlib header, or the
16-bit gzip method-and-flags word. -/
structure InflatePhase (s : InflateState) : Prop where
  started : s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = MEM ∨ s.mode = SYNC ∨
    s.wrap = 0 ∨ s.flags ≠ -1
  flags : s.flags = -1 ∨ (0 ≤ s.flags.toInt ∧ s.flags.toInt < 65536)
  gzipFlags : s.flags ≠ -1 → s.flags ≠ 0 → GzipAllowed s.wrap
  gzipModes : FLAGS ≤ s.mode → s.mode ≤ HCRC → GzipAllowed s.wrap

/-- The decoder invariant over every reachable history. -/
structure InflateInv (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Prop where
  good : Good h r zs z s
  alloc : DefAlloc z
  tables : DataTableInvariant h s
  pending : DataPendingInvariant s
  lengths : CodeLengthInvariant zs s
  headerLengths : LengthHeaderInvariant s
  held : s.hold.toNat < 2 ^ s.bits.toNat
  config : InflateConfig s
  modes : HEAD ≤ s.mode ∧ s.mode ≤ SYNC
  phase : InflatePhase s
  origin : CopyTableOrigin zs s
  globals : LibraryGlobals h

/-- The configuration the existing per-call proofs cover. -/
def DefaultConfig (s : InflateState) : Prop :=
  (s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 5) ∧ s.wbits ≠ 0

/-- `Api.inflWbits` selects a width of 0 or 8 to 15. -/
theorem inflWbits_bits {w : Int} {wrap : ZlibF.Spec.Api.Wrap} {bits : Nat}
    (selected : ZlibF.Spec.Api.inflWbits w = some (wrap, bits)) :
    bits = 0 ∨ (8 ≤ bits ∧ bits ≤ 15) := by
  unfold ZlibF.Spec.Api.inflWbits at selected
  by_cases negative : w < 0
  · rw [if_pos negative] at selected
    by_cases low : w < -15
    · rw [if_pos low] at selected
      cases selected
    · rw [if_neg low] at selected
      by_cases small : -w < 8
      · rw [if_pos small] at selected
        cases selected
      · rw [if_neg small] at selected
        cases selected
        omega
  · rw [if_neg negative] at selected
    generalize (if w < 48 then w % 16 else w) = width at selected
    have pick : ∀ wr : ZlibF.Spec.Api.Wrap,
        (if width ≠ 0 ∧ (width < 8 ∨ width > 15) then none else some (wr, width.toNat)) =
          some (wrap, bits) → bits = 0 ∨ (8 ≤ bits ∧ bits ≤ 15) := by
      intro wr chosen
      by_cases accepted : width ≠ 0 ∧ (width < 8 ∨ width > 15)
      · rw [if_pos accepted] at chosen
        cases chosen
      · rw [if_neg accepted] at chosen
        cases chosen
        omega
    by_cases zlib : w / 16 = 0
    · rw [if_pos zlib] at selected
      exact pick _ selected
    · rw [if_neg zlib] at selected
      by_cases gzip : w / 16 = 1
      · rw [if_pos gzip] at selected
        exact pick _ selected
      · rw [if_neg gzip] at selected
        by_cases auto : w / 16 = 2
        · rw [if_pos auto] at selected
          exact pick _ selected
        · rw [if_neg auto] at selected
          cases selected

/-- A raw request has a width of 8 to 15. -/
theorem inflWbits_raw {w : Int} {bits : Nat}
    (selected : ZlibF.Spec.Api.inflWbits w = some (.raw, bits)) : 8 ≤ bits := by
  unfold ZlibF.Spec.Api.inflWbits at selected
  by_cases negative : w < 0
  · rw [if_pos negative] at selected
    by_cases low : w < -15
    · rw [if_pos low] at selected
      cases selected
    · rw [if_neg low] at selected
      by_cases small : -w < 8
      · rw [if_pos small] at selected
        cases selected
      · rw [if_neg small] at selected
        cases selected
        omega
  · rw [if_neg negative] at selected
    generalize (if w < 48 then w % 16 else w) = width at selected
    have pick : ∀ wr : ZlibF.Spec.Api.Wrap, wr ≠ .raw →
        (if width ≠ 0 ∧ (width < 8 ∨ width > 15) then none else some (wr, width.toNat)) ≠
          some (.raw, bits) := by
      intro wr notRaw chosen
      by_cases accepted : width ≠ 0 ∧ (width < 8 ∨ width > 15)
      · rw [if_pos accepted] at chosen
        cases chosen
      · rw [if_neg accepted] at chosen
        cases chosen
        exact notRaw rfl
    by_cases zlib : w / 16 = 0
    · rw [if_pos zlib] at selected
      exact absurd selected (pick _ (by decide))
    · rw [if_neg zlib] at selected
      by_cases gzip : w / 16 = 1
      · rw [if_pos gzip] at selected
        exact absurd selected (pick _ (by decide))
      · rw [if_neg gzip] at selected
        by_cases auto : w / 16 = 2
        · rw [if_pos auto] at selected
          exact absurd selected (pick _ (by decide))
        · rw [if_neg auto] at selected
          cases selected

/-! ## Interface -/

/-- The default relation is an instance of the general one. -/
theorem InflateInv.of_origin {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (current : DefaultOriginState h r zs z s) (allocator : DefAlloc z) :
    InflateInv h r zs z s := by
  have nonzero : s.wbits ≠ 0 := by
    intro zero
    have low := current.window.1
    rw [zero] at low
    exact absurd low (by decide)
  refine ⟨current.good, allocator, current.tables, current.pending, current.lengths,
    current.headerLengths, current.held, ?_, current.good.live.mode, ?_, current.tableOrigin,
    current.globals⟩
  · refine ⟨?_, ?_, Or.inl current.window, Or.inl current.requestedBits, ?_,
      fun _ => nonzero, fun _ => by rw [current.requestedBits]; exact nonzero, ?_⟩
    · unfold WrapValue
      rcases current.wrapper with value | value | value <;> rw [value] <;> decide
    · unfold WrapValue
      rcases current.requestedWrap with value | value | value <;> rw [value] <;> decide
    · intro attached
      exact absurd current.header attached
    · have notGzip : ∀ w : Int32, (w = 0 ∨ w = 1 ∨ w = 5) → ¬ GzipAllowed w := by
        intro w value
        unfold GzipAllowed
        rcases value with v | v | v <;> rw [v] <;> decide
      exact Or.inr (iff_of_false (notGzip _ current.wrapper) (notGzip _ current.requestedWrap))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rcases current.phase with value | value | value | value | value | value
      · exact Or.inl value
      · exact Or.inr (Or.inl value)
      · exact Or.inr (Or.inr (Or.inl value))
      · exact Or.inr (Or.inr (Or.inr (Or.inl value)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl value))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [value]; decide)))))
    · rcases current.flagsOrigin with value | value
      · exact Or.inl value
      · exact Or.inr (by rw [value]; decide)
    · intro unread zero
      rcases current.flagsOrigin with value | value
      · exact absurd value unread
      · exact absurd value zero
    · intro low high
      exfalso
      rcases current.modes with head | ⟨dictid, _⟩
      · rw [head] at low
        exact absurd low (by decide)
      · rw [UInt32.le_iff_toNat_le] at dictid high
        exact absurd (Nat.le_trans dictid high) (by decide)

/-- The heap determines the decoder; another `Good` view of the same stream
carries the invariant. -/
theorem InflateInv.of_good {h : Heap} {r : ZStreamRef} {zs zs' : Nat} {z z' : ZStream}
    {s s' : InflateState} (current : InflateInv h r zs z s) (good : Good h r zs' z' s') :
    InflateInv h r zs' z' s' := by
  have sameStream : z = z' := Option.some.inj (current.good.live.hz.symm.trans good.live.hz)
  subst sameStream
  have sameIndex : zs = zs' := by
    have both := current.good.live.zst.symm.trans good.live.zst
    cases both
    rfl
  subst sameIndex
  have sameState : s = s' := Option.some.inj (current.good.live.hs.symm.trans good.live.hs)
  subst sameState
  exact current

/-- Every state falls in one of three classes: the default configuration,
a width still to be read from the zlib header, or gzip decoding allowed. -/
theorem InflateConfig.cases {s : InflateState} (config : InflateConfig s) :
    DefaultConfig s ∨ s.wbits = 0 ∨ (s.wbits ≠ 0 ∧ GzipAllowed s.wrap) := by
  by_cases zero : s.wbits = 0
  · exact Or.inr (Or.inl zero)
  · rcases config.wrap with value | value | value | value | value | value | value
    · exact Or.inl ⟨Or.inl value, zero⟩
    · exact Or.inl ⟨Or.inr (Or.inl value), zero⟩
    · exact Or.inr (Or.inr ⟨zero, Or.inl value⟩)
    · exact Or.inr (Or.inr ⟨zero, Or.inr (Or.inl value)⟩)
    · exact Or.inl ⟨Or.inr (Or.inr value), zero⟩
    · exact Or.inr (Or.inr ⟨zero, Or.inr (Or.inr (Or.inl value))⟩)
    · exact Or.inr (Or.inr ⟨zero, Or.inr (Or.inr (Or.inr value))⟩)

#print axioms InflateInv.of_origin
#print axioms InflateInv.of_good
#print axioms InflateConfig.cases

end Zlib.Inflate.Proofs
