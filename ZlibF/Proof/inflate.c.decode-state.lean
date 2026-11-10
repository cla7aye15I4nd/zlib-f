import ZlibF.Proof.«inflate.c.misc»
import ZlibF.Proof.«inflate.c.main.macros»
import ZlibF.Spec.InflateTableInvariant

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The scalar fields written while decoding a literal, length or distance. -/
def DecodeStateFrame (before after : InflateState) : Prop :=
  after = { before with back := after.back, length := after.length, offset := after.offset, extra := after.extra, was := after.was, mode := after.mode }

theorem DecodeStateFrame.trans {a b c : InflateState} (first : DecodeStateFrame a b)
    (second : DecodeStateFrame b c) : DecodeStateFrame a c := by
  unfold DecodeStateFrame at *
  rw [second, first]

theorem DecodeStateFrame.hold_bound {before after : InflateState} (frame : DecodeStateFrame before after)
    (hold : before.hold.toNat < 2 ^ before.bits.toNat) : after.hold.toNat < 2 ^ after.bits.toNat := by
  rw [frame]
  exact hold

theorem DecodeStateFrame.sane {before after : InflateState} (frame : DecodeStateFrame before after) :
    after.sane = before.sane := by rw [frame]

/-- Scalar decoder updates preserve representation storage, window and pointers. -/
theorem _root_.Zlib.Inflate.Spec.Good.decode_update {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {before after : InflateState} (good : Good h r zs z before)
    (frame : DecodeStateFrame before after) (mode : HEAD ≤ after.mode ∧ after.mode ≤ SYNC) :
    Good (setI h zs after) r zs z after := by
  apply good_state good (by rw [frame]) mode
  apply good.inv.of_fields
  all_goals rw [frame]
  exact good.inv.bits

/-- Scalar decoder writes preserve every actual code-array view. -/
theorem decode_code_views {h : Heap} {zs : Nat} {before after : InflateState}
    (state : h.istates zs = some before) (frame : DecodeStateFrame before after) (ref : CodeRef) :
    (Space.get (setI h zs after) ref : Option (Array Code)) = Space.get h ref := by
  cases ref with
  | istate_codes i =>
    by_cases same : i = zs
    · subst i
      simp only [Space.get, setI_istates_same, state, Option.map_some]
      rw [frame]
    · simp [Space.get, setI, upd_ne _ _ _ _ same]
  | st_lenfix => rfl
  | st_distfix => rfl

/-- Retain both actual data tables across a scalar mode transition. -/
theorem _root_.Zlib.Inflate.Spec.DataTablesSafe.decode_update {h : Heap} {zs : Nat} {before after : InflateState}
    (tables : DataTablesSafe h before) (state : h.istates zs = some before)
    (frame : DecodeStateFrame before after) : DataTablesSafe (setI h zs after) after := by
  have lens : after.lencode = before.lencode := by rw [frame]
  have dists : after.distcode = before.distcode := by rw [frame]
  have lenbits : after.lenbits = before.lenbits := by rw [frame]
  have distbits : after.distbits = before.distbits := by rw [frame]
  constructor
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := tables.lengthTable
    exact ⟨ref, offset, array, lens.trans pointer, by rw [decode_code_views state frame]; exact get, by rwa [lenbits]⟩
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := tables.distanceTable
    exact ⟨ref, offset, array, dists.trans pointer, by rw [decode_code_views state frame]; exact get, by rwa [distbits]⟩

/-- Bit-source views are unaffected by private state writes. -/
theorem BitInv.decode_update {h : Heap} {l : IL} {bs : List UInt8} (inv : BitInv h l bs)
    (zs : Nat) (s : InflateState) : BitInv (setI h zs s) l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨ref, array, offset, pointer, get, bound, contents⟩
  · exact Or.inl empty
  · refine Or.inr ⟨ref, array, offset, pointer, ?_, bound, contents⟩
    cases ref <;> exact get

end Zlib.Inflate.Proofs
