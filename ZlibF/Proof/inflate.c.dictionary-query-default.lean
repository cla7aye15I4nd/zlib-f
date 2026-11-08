import ZlibF.Proof.«inflate.c.dictionary-install-default»
import ZlibF.Proof.«inflate.c.default-byte-view»
import ZlibF.Proof.«inflate.c.public-getdict»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual dictionary query preserves the complete default invariant.
The public writable caller range covers general byte objects. Null output
and an empty dictionary are included, with the actual optional length result. -/
theorem inflateGetDictionary_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (dest : BPtr) (dl : Option UInt32)
    (range : CallerRange h r dest s.whave.toNat true) :
    ∃ after, C.run (inflateGetDictionary (some r) dest dl) h =
      .ok ((Z_OK, dl.map (fun _ => s.whave)), after) ∧
      DefaultStateJ after r zs z s := by
  have good := invariant.good
  by_cases empty : dest = .null ∨ s.whave = 0
  · refine ⟨h, ?_, invariant⟩
    unfold C.run inflateGetDictionary
    rcases empty with null | zero
    · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
        good.live.hz, good.live.zst, castI, good.live.hs, null]
    · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
        good.live.hz, good.live.zst, castI, good.live.hs, zero]
  have nonnull : dest ≠ .null := fun null => empty (Or.inl null)
  have positive : s.whave ≠ 0 := fun zero => empty (Or.inr zero)
  have positiveNat : 0 < s.whave.toNat := by
    have : s.whave.toNat ≠ 0 := fun zero => positive (UInt32.toNat_inj.mp (by simpa using zero))
    omega
  obtain ⟨w, a, window, bytes, _write, size⟩ :
      ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
        h.ro w = false ∧ a.size = 2 ^ s.wbits.toNat := by
    rcases good.inv.win.block with null | block
    · have := good.inv.win.nullws null
      have := good.inv.win.hv
      simp_all
    · exact block
  have windowSize : s.wsize.toNat = a.size := by
    rcases good.inv.win.ws with zero | full
    · have := good.inv.win.hv
      omega
    · omega
  have bounded : s.whave.toNat ≤ a.size := by
    have := good.inv.win.hv
    omega
  have chronological : s.wnext.toNat ≤ s.whave.toNat := by
    rcases Nat.lt_or_ge s.whave.toNat s.wsize.toNat with growing | full
    · have := good.inv.win.eq growing
      omega
    · have := good.inv.win.wn
      have := good.inv.win.hv
      omega
  have writable : Writable h dest s.whave.toNat := by
    rcases range with null | ⟨_read, write⟩
    · exact False.elim (nonnull null)
    · exact write.1 rfl
  rcases writable with ⟨null, _⟩ | ⟨ref, off, old, pointer, get, write, room⟩
  · exact False.elim (nonnull null)
  have separate := callerRange_private_window good range pointer
  have actual := inflateGetDictionary_copy_general (dl := dl) good.live window bytes get write
    (separate w window) positive chronological bounded room
  refine ⟨Space.put h ref (getDictBytes old a off s.wnext.toNat s.whave.toNat), ?_, ?_⟩
  · simpa only [C.run, pointer] using actual
  · apply invariant.byte_view_put get write separate
    simp [getDictBytes, size_copyRange]

#print axioms inflateGetDictionary_default_state
end Zlib.Inflate.Proofs
