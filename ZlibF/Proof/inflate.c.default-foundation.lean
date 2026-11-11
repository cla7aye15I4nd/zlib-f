import ZlibF.Proof.«inflate.c.output-invariant»
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

/-- A caller byte range survives heap steps that keep every byte view's
extent and read-only flag and do not make its block stream-owned. -/
theorem CallerRange.transport {h after : Heap} {r : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write)
    (sizes : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)).map Array.size =
      (Space.get h ref : Option (Array UInt8)).map Array.size)
    (ro : ∀ ref : BRef, (Space.ro after ref : Bool) = Space.ro h ref)
    (owned : ∀ b, StreamOwned after r b → StreamOwned h r b) :
    CallerRange after r p n write := by
  rcases range with null | ⟨⟨xs, bytes⟩, writable, outside⟩
  · exact Or.inl null
  refine Or.inr ⟨?_, ?_, fun b root owner => outside b root (owned b owner)⟩
  · rcases bytes with ⟨pn, nz, _⟩ | ⟨ref, i, a, pointer, get, fit, _⟩
    · exact ⟨[], Or.inl ⟨pn, nz, rfl⟩⟩
    · have size := sizes ref
      rw [get] at size
      obtain ⟨a', get', sizeEq⟩ : ∃ a', (Space.get after ref : Option (Array UInt8)) = some a' ∧
          a'.size = a.size := by
        cases view : (Space.get after ref : Option (Array UInt8)) with
        | none => rw [view] at size; cases size
        | some a' => rw [view] at size; exact ⟨a', rfl, Option.some.inj size⟩
      exact ⟨(a'.toList.drop i).take n, Or.inr ⟨ref, i, a', pointer, get', by omega, rfl⟩⟩
  · intro writing
    rcases writable writing with ⟨pn, nz⟩ | ⟨ref, i, a, pointer, get, readonly, fit⟩
    · exact Or.inl ⟨pn, nz⟩
    · have size := sizes ref
      rw [get] at size
      obtain ⟨a', get', sizeEq⟩ : ∃ a', (Space.get after ref : Option (Array UInt8)) = some a' ∧
          a'.size = a.size := by
        cases view : (Space.get after ref : Option (Array UInt8)) with
        | none => rw [view] at size; cases size
        | some a' => rw [view] at size; exact ⟨a', rfl, Option.some.inj size⟩
      exact Or.inr ⟨ref, i, a', pointer, get', by rw [ro]; exact readonly, by omega⟩

/-- The writable caller header record and its buffers survive the same steps,
when the header table is unchanged. -/
theorem HeaderMemory.transport {h after : Heap} {r : ZStreamRef} {p : GzHeaderPtr}
    (memory : HeaderMemory h r p true)
    (headers : ∀ i, after.gzheaders i = h.gzheaders i)
    (sizes : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)).map Array.size =
      (Space.get h ref : Option (Array UInt8)).map Array.size)
    (ro : ∀ ref : BRef, (Space.ro after ref : Bool) = Space.ro h ref)
    (owned : ∀ b, StreamOwned after r b → StreamOwned h r b) :
    HeaderMemory after r p true := by
  rcases memory with none | ⟨i, g, pointer, get, notOwned, extra, name, comment⟩
  · exact Or.inl none
  refine Or.inr ⟨i, g, pointer, by rw [headers]; exact get, fun owner => notOwned (owned i owner),
    fun present => CallerRange.transport (extra present) sizes ro owned, ?_, ?_⟩
  · intro present
    have old := name present
    simp only [ite_true] at old ⊢
    exact CallerRange.transport old sizes ro owned
  · intro present
    have old := comment present
    simp only [ite_true] at old ⊢
    exact CallerRange.transport old sizes ro owned

/-- A byte range in the heap has a live root block. -/
theorem ByteRoot.live_of_get {h : Heap} {ref : BRef} {off : Nat} {a : Array UInt8} {b : Nat}
    (get : (Space.get h ref : Option (Array UInt8)) = some a) (root : ByteRoot (.ref ref off) b) :
    h.live b := by
  cases ref with
  | blk i =>
    change b = i at root
    subst b
    exact Or.inl (by simp only [Space.get] at get; rw [get]; simp)
  | dstate_depth i =>
    change b = i at root
    subst b
    simp only [Space.get] at get
    unfold Heap.live
    right; right; right; right; left
    intro absent
    simp [absent] at get
  | _ => exact False.elim root

/-- Range transport to another stream: blocks owned by the new stream were
owned by the old one or were not live before. -/
theorem CallerRange.transport' {h after : Heap} {r r' : ZStreamRef} {p : BPtr} {n : Nat} {write : Bool}
    (range : CallerRange h r p n write)
    (sizes : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)).map Array.size =
      (Space.get h ref : Option (Array UInt8)).map Array.size)
    (ro : ∀ ref : BRef, (Space.ro after ref : Bool) = Space.ro h ref)
    (owned : ∀ b, StreamOwned after r' b → StreamOwned h r b ∨ ¬ h.live b) :
    CallerRange after r' p n write := by
  rcases range with null | ⟨⟨xs, bytes⟩, writable, outside⟩
  · exact Or.inl null
  have rootLive : ∀ b, ByteRoot p b → h.live b := by
    intro b root
    rcases bytes with ⟨pn, _, _⟩ | ⟨ref, i, a, pointer, get, _, _⟩
    · rw [pn] at root
      exact False.elim root
    · rw [pointer] at root
      exact ByteRoot.live_of_get get root
  refine Or.inr ⟨?_, ?_, ?_⟩
  · rcases bytes with ⟨pn, nz, _⟩ | ⟨ref, i, a, pointer, get, fit, _⟩
    · exact ⟨[], Or.inl ⟨pn, nz, rfl⟩⟩
    · have size := sizes ref
      rw [get] at size
      obtain ⟨a', get', sizeEq⟩ : ∃ a', (Space.get after ref : Option (Array UInt8)) = some a' ∧
          a'.size = a.size := by
        cases view : (Space.get after ref : Option (Array UInt8)) with
        | none => rw [view] at size; cases size
        | some a' => rw [view] at size; exact ⟨a', rfl, Option.some.inj size⟩
      exact ⟨(a'.toList.drop i).take n, Or.inr ⟨ref, i, a', pointer, get', by omega, rfl⟩⟩
  · intro writing
    rcases writable writing with ⟨pn, nz⟩ | ⟨ref, i, a, pointer, get, readonly, fit⟩
    · exact Or.inl ⟨pn, nz⟩
    · have size := sizes ref
      rw [get] at size
      obtain ⟨a', get', sizeEq⟩ : ∃ a', (Space.get after ref : Option (Array UInt8)) = some a' ∧
          a'.size = a.size := by
        cases view : (Space.get after ref : Option (Array UInt8)) with
        | none => rw [view] at size; cases size
        | some a' => rw [view] at size; exact ⟨a', rfl, Option.some.inj size⟩
      exact Or.inr ⟨ref, i, a', pointer, get', by rw [ro]; exact readonly, by omega⟩
  · intro b root owner
    rcases owned b owner with old | dead
    · exact outside b root old
    · exact dead (rootLive b root)

/-- Header memory transport to another stream (as for `inflateCopy`). -/
theorem HeaderMemory.transport' {h after : Heap} {r r' : ZStreamRef} {p : GzHeaderPtr}
    (memory : HeaderMemory h r p true)
    (headers : ∀ i, after.gzheaders i = h.gzheaders i)
    (sizes : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)).map Array.size =
      (Space.get h ref : Option (Array UInt8)).map Array.size)
    (ro : ∀ ref : BRef, (Space.ro after ref : Bool) = Space.ro h ref)
    (owned : ∀ b, StreamOwned after r' b → StreamOwned h r b ∨ ¬ h.live b) :
    HeaderMemory after r' p true := by
  rcases memory with none | ⟨i, g, pointer, get, notOwned, extra, name, comment⟩
  · exact Or.inl none
  have recordLive : h.live i := by
    unfold Heap.live
    right; right; right; left
    rw [get]
    simp
  refine Or.inr ⟨i, g, pointer, by rw [headers]; exact get, ?_,
    fun present => CallerRange.transport' (extra present) sizes ro owned, ?_, ?_⟩
  · intro owner
    rcases owned i owner with old | dead
    · exact notOwned old
    · exact dead recordLive
  · intro present
    have old := name present
    simp only [ite_true] at old ⊢
    exact CallerRange.transport' old sizes ro owned
  · intro present
    have old := comment present
    simp only [ite_true] at old ⊢
    exact CallerRange.transport' old sizes ro owned

/-- The header memory survives decoder record writes that keep the window,
the head pointer, the header table, byte-view extents and read-only flags. -/
theorem HeaderMemory.records {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (memory : HeaderMemory h r s.head true) (before : Good h r zs z s)
    (current : Good after r zs stream state) (window : state.window = s.window)
    (head : state.head = s.head) (headers : ∀ i, after.gzheaders i = h.gzheaders i)
    (sizes : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)).map Array.size =
      (Space.get h ref : Option (Array UInt8)).map Array.size)
    (ro : ∀ ref : BRef, (Space.ro after ref : Bool) = Space.ro h ref) :
    HeaderMemory after r state.head true := by
  rw [head]
  apply HeaderMemory.transport memory headers sizes ro
  intro b owner
  rw [current.streamOwned_iff] at owner
  rw [before.streamOwned_iff]
  rcases owner with same | win
  · exact Or.inl same
  · exact Or.inr (window ▸ win)

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
  window : 8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15
  wrapper : s.wrap = 0 ∨ s.wrap = 1 ∨ s.wrap = 5
  header : HeaderMemory h r s.head true
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
  requestedBits : s.reqbits = s.wbits
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
    ?_, ?_, inflate_initial_hold initial good, ?_, Or.inr (Or.inr wrap), Or.inl header,
    Or.inl head, ?_, globals, fit⟩, reachable⟩
  · intro active
    rw [head] at active
    contradiction
  · intro active
    rw [head] at active
    contradiction
  · exact ⟨by omega, by omega⟩
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
  exact ⟨after, z, s, run, initial, ⟨invariant, requestedBits, Or.inr (Or.inr wrapper), Or.inl head⟩, reachable⟩

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
