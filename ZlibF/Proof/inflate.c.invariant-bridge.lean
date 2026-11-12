import ZlibF.Proof.«inflate.c.invariant»

/-!
# inflate.c: from the general invariant back to the default relation

With the object-size limit of the platform, the general invariant gives back
`DefaultOriginState` in every configuration, so the per-call proofs of
`inflate` apply. The
requested width and wrapper may differ from the current ones: `inflate`
does not read them.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem not_gzip_of_default {w : Int32} (value : w = 0 ∨ w = 1 ∨ w = 5) : ¬ GzipAllowed w := by
  unfold GzipAllowed
  rcases value with v | v | v <;> rw [v] <;> decide

/-- Without gzip, `flags` is the unread sentinel or the zlib value 0. -/
theorem InflateInv.default_flags {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r zs z s) (notGzip : ¬ GzipAllowed s.wrap) :
    s.flags = -1 ∨ s.flags = 0 := by
  by_cases unread : s.flags = -1
  · exact Or.inl unread
  · by_cases zero : s.flags = 0
    · exact Or.inr zero
    · exact absurd (current.phase.gzipFlags unread zero) notGzip

theorem InflateInv.to_origin {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r zs z s)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) :
    DefaultOriginState h r zs z s := by
  have done : s.flags ≠ -1 → HeaderDone s := by
    intro read
    by_cases zero : s.flags = 0
    · exact Or.inr (Or.inl zero)
    · exact Or.inr (Or.inr ⟨current.phase.gzipFlags read zero, read, zero⟩)
  have window : (8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) ∨
      (s.wbits = 0 ∧ s.window = .null ∧ s.flags = -1 ∧ s.wrap ≠ 0) := by
    rcases current.config.window with range | ⟨zero, null, _, unread⟩
    · exact Or.inl range
    · exact Or.inr ⟨zero, null, unread, fun raw => current.config.raw raw zero⟩
  have widthAtFlags : s.mode = FLAGS → s.wbits ≠ 0 := by
    intro atFlags zero
    rcases current.config.window with range | ⟨_, _, early, _⟩
    · rw [zero] at range
      exact absurd range.1 (by decide)
    · rcases early with e | e | e | e <;> rw [atFlags] at e <;> exact absurd e (by decide)
  have modes : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC ∨ GzipHeaderMode s := by
    have range := current.modes
    by_cases head : s.mode = HEAD
    · exact Or.inl head
    by_cases header : s.mode ≤ HCRC
    · have low : FLAGS ≤ s.mode := by
        rw [UInt32.le_iff_toNat_le] at range ⊢
        have headNat : s.mode.toNat ≠ 16180 := fun same => head (UInt32.toNat_inj.mp same)
        change 16180 ≤ s.mode.toNat ∧ _ at range
        change 16181 ≤ s.mode.toNat
        omega
      refine Or.inr (Or.inr ⟨low, header, current.phase.gzipModes low header, fun past => ?_⟩)
      have read : s.flags ≠ -1 := by
        rcases current.phase.started with e | e | e | e | raw | read | e
        all_goals first
          | exact read
          | (rw [e] at past; exact absurd past (by decide))
          | (rw [e] at header; exact absurd header (by decide))
          | exact absurd (current.phase.gzipModes low header) (by unfold GzipAllowed; rw [raw]; decide)
      exact ⟨read, current.phase.gzipRead past header⟩
    · right; left
      refine ⟨?_, range.2⟩
      rw [UInt32.le_iff_toNat_le]
      rw [UInt32.le_iff_toNat_le] at header
      change ¬ s.mode.toNat ≤ 16188 at header
      change 16189 ≤ s.mode.toNat
      omega
  have trailer : s.mode = CHECK ∨ s.mode = LENGTH → HeaderDone s := by
    intro late
    rcases current.phase.started with e | e | e | e | raw | read | e
    all_goals try (exfalso; rcases late with l | l <;> rw [l] at e <;> exact absurd e (by decide))
    · exact Or.inl raw
    · exact done read
  have phase : s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = MEM ∨ s.mode = SYNC ∨
      HeaderDone s ∨ GzipFlagsPending s := by
    rcases current.phase.started with e | e | e | e | raw | read | atFlags
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl raw)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (done read)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨atFlags,
        current.phase.gzipModes (by rw [atFlags]; decide) (by rw [atFlags]; decide),
        widthAtFlags atFlags⟩))))
  exact ⟨⟨⟨current.good, current.tables, current.pending, current.lengths, current.headerLengths,
    current.held, window, current.config.wrap,
    fun cause => cause.elim current.config.header (fun read => current.phase.gzipFlags read.1 read.2),
    modes, trailer, current.globals,
    platform⟩,
    ⟨current.config.reqbits.imp id (fun zero => zero.1), current.config.reqraw⟩,
    ⟨current.config.reqwrap, current.config.pair⟩, phase⟩, current.origin⟩

#print axioms InflateInv.to_origin

end Zlib.Inflate.Proofs
