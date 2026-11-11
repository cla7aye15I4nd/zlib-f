import ZlibF.Proof.«inflate.c.default-entry»
import ZlibF.Proof.«inflate.c.main.table2»
import ZlibF.Spec.InflatePendingInvariant
import ZlibF.Spec.InflateCodeLengthInvariant

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
construction phases. The configuration is explicit: any window width from
8 to 15 bits (equal to the requested width), no gzip header, and raw
recovery or zlib validation settings. A requested width of 0 and gzip
wrapping are not yet covered. Full dispatch/history closure remains open. -/
structure DefaultDecodeJ (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) : Prop where
  good : Good h r zs z s
  tables : DataTableInvariant h s
  pending : DataPendingInvariant s
  lengths : CodeLengthInvariant zs s
  headerLengths : LengthHeaderInvariant s
  held : s.hold.toNat < 2 ^ s.bits.toNat
  window : (8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15) ∨
    (s.wbits = 0 ∧ s.window = .null ∧ (s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = SYNC))
  wrapper : s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 5
  header : s.head = none
  modes : s.mode = HEAD ∨ DICTID ≤ s.mode ∧ s.mode ≤ SYNC
  trailer : s.mode = CHECK ∨ s.mode = LENGTH → s.wrap = 0 ∨ s.flags = 0
  globals : LibraryGlobals h
  platform : ZlibF.PlatformMemory.ByteObjectsFit h

/-- Default-history fields that reset and entry into CHECK need. An unread
or rejected header may retain the initial flags. Active block decoding
requires raw recovery or a completed zlib header. These fields supplement
the checked decoder relation; full history closure is still open. -/
structure DefaultStateJ (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    : Prop extends DefaultDecodeJ h r zs z s where
  requestedBits : s.reqbits = s.wbits ∨ (s.reqbits = 0 ∧ 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15)
  requestedWrap : s.reqwrap = 0 ∨ s.reqwrap = 1 ∨ s.reqwrap = 5
  phase : s.mode = HEAD ∨ s.mode = BAD ∨ s.mode = MEM ∨ s.mode = SYNC ∨ s.wrap = 0 ∨ s.flags = 0

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
  have headPending : DataPendingInvariant s := by
    refine ⟨sane, ?_, ?_, ?_, ?_⟩
    all_goals intro selected; rw [head] at selected; contradiction
  have initialCopy := initial
  obtain ⟨stream, state, stateGood, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, frame, _⟩ := initialCopy
  have globals : LibraryGlobals after := by
    change after.static = _
    rw [← frame.1]
    exact domain.2.2.1
  refine ⟨after, z, s, run, initial, ⟨good, tables, headPending,
    ?_, ?_, inflate_initial_hold initial good, ?_, Or.inr (Or.inr wrap), header,
    Or.inl head, ?_, globals, fit⟩, reachable⟩
  · intro active
    rw [head] at active
    contradiction
  · intro active
    rw [head] at active
    contradiction
  · exact Or.inl ⟨by omega, by omega⟩
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


/-- Successful actual default initialization establishes both the decoder
relation and its reset/header history fields. -/
theorem inflate_default_state_initial
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s, C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r .zlib 15 ∧ DefaultStateJ after r h.nextBlk z s ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, initial, invariant, reachable⟩ :=
    inflate_default_J_initial h r version domain platform allocation
  have initialCopy := initial
  obtain ⟨initialZ, initialS, good, _, _, head, _, activeBits, requested, wrap, requestedWrap, _⟩ := initialCopy
  have sameState : initialS = s := Option.some.inj (good.live.hs.symm.trans invariant.good.live.hs)
  subst initialS
  have requestedBits : s.reqbits = s.wbits := UInt32.toNat_inj.mp (requested.trans activeBits.symm)
  have wrapper : s.reqwrap = 5 := requestedWrap.trans wrap
  exact ⟨after, z, s, run, initial, ⟨invariant, Or.inl requestedBits, Or.inr (Or.inr wrapper), Or.inl head⟩, reachable⟩

/-- The history relation has an actual initialized caller. -/
theorem inflate_default_state_witness :
    ∃ after z s, C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk z s ∧ StreamReachable .inflate after (.tab 0) := by
  obtain ⟨after, z, s, run, _, invariant, reachable⟩ :=
    inflate_default_state_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
      ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl
  exact ⟨after, z, s, run, invariant, reachable⟩


#print axioms inflate_default_state_initial
#print axioms inflate_default_state_witness
end Zlib.Inflate.Proofs
