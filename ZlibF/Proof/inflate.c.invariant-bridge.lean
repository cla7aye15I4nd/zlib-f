import ZlibF.Proof.«inflate.c.invariant»

/-!
# inflate.c: from the general invariant back to the default relation

In the default configuration, with the requested width and wrapper equal
to the current ones and the object-size limit of the platform, the general
invariant gives back `DefaultOriginState`, so the existing per-call proofs
of `inflate` apply.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The requested configuration the existing default proofs assume. -/
def DefaultRequest (s : InflateState) : Prop :=
  s.reqbits = s.wbits ∧ (s.reqwrap = 0 ∨ s.reqwrap = 1 ∨ s.reqwrap = 5)

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
    {s : InflateState} (current : InflateInv h r zs z s) (config : DefaultConfig s)
    (request : DefaultRequest s) (platform : ZlibF.PlatformMemory.ByteObjectsFit h) :
    DefaultOriginState h r zs z s := by
  obtain ⟨wrapper, nonzero⟩ := config
  have notGzip := not_gzip_of_default wrapper
  have flagsOrigin := current.default_flags notGzip
  have window : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 := by
    rcases current.config.window with range | ⟨zero, _⟩
    · exact range
    · exact absurd zero nonzero
  have header : s.head = none :=
    Classical.byContradiction fun attached => notGzip (current.config.header attached)
  have modes : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC := by
    by_cases head : s.mode = HEAD
    · exact Or.inl head
    · right
      have range := current.modes
      rw [UInt32.le_iff_toNat_le, UInt32.le_iff_toNat_le] at range
      have headNat : s.mode.toNat ≠ 16180 := fun same => head (UInt32.toNat_inj.mp same)
      have headValue : HEAD.toNat = 16180 := rfl
      have syncValue : SYNC.toNat = 16211 := rfl
      rw [headValue, syncValue] at range
      by_cases gzipMode : s.mode.toNat ≤ 16188
      · exfalso
        apply notGzip
        apply current.phase.gzipModes
        · rw [UInt32.le_iff_toNat_le]
          change 16181 ≤ s.mode.toNat
          omega
        · rw [UInt32.le_iff_toNat_le]
          change s.mode.toNat ≤ 16188
          exact gzipMode
      · rw [UInt32.le_iff_toNat_le, UInt32.le_iff_toNat_le]
        change 16189 ≤ s.mode.toNat ∧ s.mode.toNat ≤ 16211
        omega
  have trailer : s.mode = CHECK ∨ s.mode = LENGTH → s.wrap = 0 ∨ s.flags = 0 := by
    intro late
    rcases flagsOrigin with unread | zero
    · rcases current.phase.started with e | e | e | e | raw | read
      all_goals try (exfalso; rcases late with l | l <;> rw [l] at e <;> exact absurd e (by decide))
      · exact Or.inl raw
      · exact absurd unread read
    · exact Or.inr zero
  have phase : s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = MEM ∨ s.mode = SYNC ∨
      s.wrap = 0 ∨ s.flags = 0 := by
    rcases current.phase.started with e | e | e | e | raw | read
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl raw))))
    · rcases flagsOrigin with unread | zero
      · exact absurd unread read
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr zero))))
  exact ⟨⟨⟨current.good, current.tables, current.pending, current.lengths, current.headerLengths,
    current.held, window, wrapper, header, modes, trailer, current.globals, platform⟩,
    request.1, request.2, phase⟩, flagsOrigin, current.origin⟩

#print axioms InflateInv.to_origin

end Zlib.Inflate.Proofs
