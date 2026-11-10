import ZlibF.Proof.«inflate.c.check-dispatch»
import ZlibF.Proof.«inflate.c.lenlens-table-safe»
import ZlibF.Proof.«inflate.c.validate-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The initialized length-header prefix needed when LENLENS resumes.
Arbitrary unused lens cells impose no constraint. -/
def LengthHeaderInvariant (s : InflateState) : Prop :=
  s.mode = LENLENS → s.ncode.toNat ≤ 19 ∧ s.«have».toNat ≤ s.ncode.toNat ∧
    s.nlen.toNat ≤ 286 ∧ s.ndist.toNat ≤ 30 ∧ Good3 s.lens s.«have».toNat

/-- The common state relation for the default-wrapper proof. It combines
representation, actual table contents, pending scalar bounds and the two
construction phases. The default configuration is explicit: windowBits 15,
no gzip header, and raw recovery or zlib validation settings. This is a
candidate inductive invariant; full dispatch/history closure remains open. -/
structure DefaultDecodeJ (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Prop where
  good : Good h r zs z s
  tables : DataTableInvariant h s
  pending : DataPendingInvariant s
  lengths : CodeLengthInvariant zs s
  headerLengths : LengthHeaderInvariant s
  held : s.hold.toNat < 2 ^ s.bits.toNat
  window : s.wbits = 15
  wrapper : s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 5
  header : s.head = none
  modes : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC
  trailer : s.mode = CHECK ∨ s.mode = LENGTH → s.wrap = 0 ∨ s.flags = 0
  globals : LibraryGlobals h
  platform : ZlibF.PlatformMemory.ByteObjectsFit h

/-- Actual successful default initialization establishes every clause of J
on its returned heap. No representation or callee contract is assumed.
A full history theorem still requires preservation by every admitted call. -/
theorem inflate_default_J_initial
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r .zlib 15 ∧ DefaultDecodeJ after r h.nextBlk z s ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, good, head, wrap, bits, header, tables, fit, reachable⟩ :=
    inflate_default_init_boundary h r version domain platform allocation
  have sane := inflate_default_success_sane domain allocation run good
  have initialCopy := initial
  obtain ⟨stream, state, stateGood, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, frame, _⟩ := initialCopy
  have globals : LibraryGlobals after := by
    change after.static = _
    rw [← frame.1]
    exact domain.2.2.1
  refine ⟨after, z, s, run, initial, ⟨good, tables, dataPendingInvariant_head sane head,
    ?_, ?_, inflate_initial_hold initial good, ?_, Or.inr (Or.inr wrap), header,
    Or.inl head, ?_, globals, fit⟩, reachable⟩
  · intro active
    rw [head] at active
    contradiction
  · intro active
    rw [head] at active
    contradiction
  · exact UInt32.toNat_inj.mp bits
  · rintro (active | active) <;> rw [head] at active <;> contradiction

/-- The default relation has a concrete initialized caller. This rules out
an empty invariant independently of its still-open preservation proof. -/
theorem inflate_default_J_witness :
    ∃ after z s, C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DefaultDecodeJ after (.tab 0) witnessHeap.nextBlk z s ∧ StreamReachable .inflate after (.tab 0) := by
  obtain ⟨after, z, s, run, _, invariant, reachable⟩ :=
    inflate_default_J_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
      ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl
  exact ⟨after, z, s, run, invariant, reachable⟩


/-- Validation leaves raw recovery raw for every signed check argument. -/
theorem validateState_raw_wrap {s : InflateState} (wrap : s.wrap = 0) (check : Int32) :
    (validateState check s).wrap = 0 := by
  simp [validateState, wrap]

/-- A legal validation toggle preserves every clause of the default J,
including the raw state produced by recovery. The actual translated call
is executed, rather than admitted as a history-contract assumption. -/
theorem inflateValidate_default_J {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultDecodeJ h r zs z s) (check : Int32) :
    ∃ after state, C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      after = setI h zs state ∧ state = validateState check s ∧ DefaultDecodeJ after r zs z state := by
  obtain ⟨after, run, heap, current, _⟩ := inflateValidate_safe invariant.good check
  subst after
  let state := validateState check s
  have tables : DataTableInvariant (setI h zs state) state := by
    intro active
    have original := invariant.tables active
    constructor
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.lengthTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views invariant.good.live.hs]; exact get, safe⟩
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.distanceTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views invariant.good.live.hs]; exact get, safe⟩
  have wrapper : state.wrap = 0 ∨ state.wrap = 1 ∨ state.wrap = 5 := by
    rcases invariant.wrapper with raw | wrapped
    · exact Or.inl (validateState_raw_wrap raw check)
    · exact Or.inr (validateState_zlib_wrap wrapped check)
  refine ⟨setI h zs state, state, run, rfl, rfl, ⟨current, tables,
    ⟨invariant.pending.sane, invariant.pending.lenext, invariant.pending.dist,
      invariant.pending.distext, invariant.pending.matching⟩,
    invariant.lengths, invariant.headerLengths, invariant.held, invariant.window, wrapper,
    invariant.header, invariant.modes, ?_, invariant.globals, invariant.platform.with_istates _⟩⟩
  intro trailer
  rcases invariant.trailer trailer with raw | flags
  · exact Or.inl (validateState_raw_wrap raw check)
  · exact Or.inr flags

end Zlib.Inflate.Proofs
