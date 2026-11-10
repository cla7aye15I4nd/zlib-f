import ZlibF.Proof.«inflate.c.table-invariant»

/-!
# inflate.c: the default initialization entry

The default entry fixes windowBits to 15. Its existing public contract
includes version errors, null streams and allocation failure. Successful
execution additionally establishes the current guarded table clause and
the explicit platform scope on the same returned heap.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

set_option maxRecDepth 8192 in
/-- The existing public caller witness also satisfies the explicit
platform scope. This includes literals and represented static byte views,
not just its two caller allocations. -/
theorem inflate_default_witness_platform :
    ZlibF.PlatformMemory.ByteObjectsFit witnessHeap := by
  intro ref a get
  cases ref with
  | blk b =>
    by_cases one : b = 1
    · subst b
      simp only [BRef.get_blk, witnessHeap] at get
      cases get
      decide
    · by_cases two : b = 2
      · subst b
        simp only [BRef.get_blk, witnessHeap, upd_same] at get
        cases get
        change (Array.replicate 32768 (0 : UInt8)).size < 2 ^ 63
        rw [Array.size_replicate]
        decide
      · simp [Space.get, witnessHeap, Heap.empty, upd_ne, one, two] at get
  | str i =>
    have bounds : ∀ j : Fin strTable.size,
        (strBytes strTable[j]).size < ZlibF.PlatformMemory.byteObjectLimit := by
      decide +kernel
    by_cases inside : i < strTable.size
    · rw [BRef.get_str, Array.getElem?_eq_getElem inside] at get
      cases get
      exact bounds ⟨i, inside⟩
    · simp [BRef.get_str, Array.getElem?_eq_none (by omega : strTable.size ≤ i)] at get
  | dstate_depth i => simp [Space.get, witnessHeap, Heap.empty] at get
  | st_dist_code =>
    cases get
    decide
  | st_length_code =>
    cases get
    decide

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
The existing complete default-entry contract, including allocation failure,
does not depend on the invalid-window cleanup contract of inflateInit2_. -/
theorem inflate_default_init_contract : Goal.inflateInit_ :=
  ZlibF.Spec.Public.Proofs.InflateInit.init15_public

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
With successful state allocation, the actual default entry establishes
Good, the initial zlib wrapper with windowBits 15, the guarded data-table
clause, the platform scope and an actual reachable history. Caller storage
must satisfy the explicit LP64 byte-object scope. No table or callee
contract is a caller assumption. This is initialization, not a proof of
the subsequent inflate calls or their full persistent invariant. -/
theorem inflate_default_init_boundary
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : InitDomain h r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s,
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r .zlib 15 ∧
      Good after r h.nextBlk z s ∧ s.mode = HEAD ∧
      s.wrap = 5 ∧ s.wbits.toNat = 15 ∧ s.head = none ∧
      DataTableInvariant after s ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, run, initial, reachable, fit⟩ :=
    ZlibF.Spec.Public.Proofs.InflateInit.inflate_domain_general_platform
      h r version 15 .zlib 15 domain platform (by decide) allocation
  have initial' := initial
  obtain ⟨z, s, good, _, _, head, _, bits, _, wrap, _, _, _, _, _, _, _,
    header, _⟩ := initial
  exact ⟨after, z, s, run, initial', good, head, wrap, bits, header,
    dataTableInvariant_head head, fit, reachable⟩

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
A concrete caller heap reaches the default initial boundary under the
platform scope. Thus the added platform premise has not emptied the domain. -/
theorem inflate_default_init_witness :
    ∃ after z s,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap =
        .ok (Z_OK, after) ∧
      InflateInitial witnessHeap after (.tab 0) .zlib 15 ∧
      Good after (.tab 0) witnessHeap.nextBlk z s ∧ s.mode = HEAD ∧
      s.wrap = 5 ∧ s.wbits.toNat = 15 ∧ s.head = none ∧
      DataTableInvariant after s ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      StreamReachable .inflate after (.tab 0) :=
  inflate_default_init_boundary witnessHeap (.tab 0) (.ref (.blk 1) 0)
    ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain
    inflate_default_witness_platform rfl

/-- The actual default initializer sets the sanity field used by MATCH.
This derives the scalar fact from initialization execution and its returned
state, rather than adding it as a public caller obligation. -/
theorem inflate_default_success_sane {h after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain h r version) (allocation : h.allocOk h.nalloc = true)
    (run : C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after))
    {z : ZStream} {s : InflateState} (good : Good after r h.nextBlk z s) : s.sane = 1 := by
  obtain ⟨fresh, _, _, validVersion, before, get, allocators, _⟩ := domain
  obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have expected : C.run (inflateInit_ (some r) version 112) h =
      .ok (Z_OK, initOkHeap h r before 5 15) := by
    change inflateInit2_ (some r) 15 version 112 h = _
    exact inflateInit2_success get fresh allocation allocators.1 allocators.2 nonnull first (by decide +kernel)
  have heapEq : after = initOkHeap h r before 5 15 :=
    congrArg Prod.snd (Except.ok.inj (run.symm.trans expected))
  have stateEq : s = resetKeepState h.nextBlk (resetPre (reset2Pre 5 15 (initState r))) := by
    apply Option.some.inj
    rw [← good.live.hs, heapEq]
    simp [initOkHeap]
  rw [stateEq]
  rfl

/-- The actual initialization postcondition establishes the held-bit bound
for every accepted wrapper/window argument, on the same returned state. -/
theorem inflate_initial_hold {before after : Heap} {r : ZStreamRef} {wrap : ZlibF.Spec.Api.Wrap}
    {bits : Nat} (initial : InflateInitial before after r wrap bits)
    {z : ZStream} {s : InflateState} (good : Good after r before.nextBlk z s) :
    s.hold.toNat < 2 ^ s.bits.toNat := by
  obtain ⟨stream, state, initialGood, _, _, _, _, _, _, _, _, _, _, _, hold, bits, _⟩ := initial
  have eq : s = state := Option.some.inj (good.live.hs.symm.trans initialGood.live.hs)
  rw [eq, hold, bits]
  decide

end Zlib.Inflate.Proofs
