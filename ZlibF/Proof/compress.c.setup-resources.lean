import ZlibF.Proof.«compress.c.resources»

/-! # Actual initialization and setup create exactly the six temporary objects -/
namespace ZlibF.Spec.Public.Proofs.CompressTail
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressCaller
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Both concrete allocator indices follow from the real five successful
requests. No invariant, count or allocation oracle success is assumed. -/
theorem successful_init_indices {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (valid : VersionValue h version (some 49))
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after)) :
    after.nalloc = h.nalloc + 5 ∧ after.nextBlk = h.nextBlk + 5 := by
  have allocation := default_init_success_allocations fresh unique globals get allocators valid actual
  let zp := ZlibF.Spec.Public.preparedStream z
  let hp := r.put h zp
  have shape := shape_put get zp
  have fp : Fresh hp := shape.fresh (by simp [hp]) fresh
  have up : Uniq hp := shape.uniq unique
  have gp : r.get hp = some zp := ZStreamRef.get_put_same get _
  have ap : DefAlloc zp := prepared_allocators allocators
  obtain ⟨a1, a2, a3, qa, run, _good, _live⟩ :=
    ZlibF.Spec.Public.Proofs.DeflateInit.allocate_success fp up gp ap
      (by simpa [hp] using ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals) (by simpa [hp] using allocation)
      6 (by decide) (by decide)
  have canonical : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h =
      .ok (Z_OK, successHeap hp r zp 6 a1 a2 a3 qa) := by
    rw [C.run, entry_run get valid]
    change allocate (some r) 6 hp = _
    exact run
  have heaps : after = successHeap hp r zp 6 a1 a2 a3 qa :=
    (Prod.mk.inj (Except.ok.inj (actual.symm.trans canonical))).2
  rw [heaps]
  constructor
  · simp only [successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, hp, ZStreamRef.put_nalloc, Nat.add_assoc]
  · simp only [successHeap, setD_nextBlk, setW, readyHeap, successfulBuffers,
      publishedHeap, stateHeap, hp, ZStreamRef.put_nextBlk, Nat.add_assoc]

/-- Actual automatic storage, successful real init and the four real
buffer assignments establish the exact private allocation keys and ledger.
The automatic stream itself consumes no allocation-failure index. -/
theorem setup_resources {h initialized ready : Heap} {dest source : BPtr}
    (fresh : Fresh h) (unique : Zlib.Inflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized))
    (actualSetup : C.run (zwr (some (.tab h.nextBlk)) (fun s => bindings s dest source)) initialized =
      .ok ((), ready)) :
    ∃ z sf,
      DefaultFinishBoundary ready (.tab h.nextBlk) (localHeap h).nextBlk z sf (engineConfig sf) ∧
      LiveChange (localHeap h) ready (DeflateOwned (localHeap h).nextBlk sf) (fun _ => False) ∧
      (∀ b, DeflateOwned (localHeap h).nextBlk sf b ↔ (localHeap h).nextBlk ≤ b ∧ b < (localHeap h).nextBlk + 5) ∧
      ready.nalloc = h.nalloc + 5 ∧ ready.nextBlk = h.nextBlk + 6 := by
  have domain := automatic_stream_domain h fresh unique globals
  obtain ⟨hf, hu, hg, hv, old, getOld, allocOld, _null⟩ := domain
  obtain ⟨zf, sf, stateI⟩ := observed_default_init_encoding_state hf hu hg getOld allocOld hv actualInit
  let p := ZlibF.Spec.Public.Proofs.DeflateInit.settings 6
  have params : ZlibF.Spec.Api.deflInit? Z_DEFAULT_COMPRESSION.toInt 8 15 8 0 = some p := by decide +kernel
  obtain ⟨zf0, sf0, start0, initial, _first⟩ := common_observed_initialization_first_ordinary_encoding
    (automatic_stream_domain h fresh unique globals) params (by decide +kernel) (by decide +kernel) actualInit
  obtain ⟨zi, si, goodI, _allocI, _freeI, _level, _strategy, _bits, _hash, _wrap, _start, _look,
    _pending, _valid, _header, _tin, _tout, _msg, _frame, liveI, ownedI⟩ := initial
  have states : si = sf := Option.some.inj (goodI.live.hs.symm.trans stateI.protocol.good.live.hs)
  subst si
  let next := bindings zf dest source
  have getInit : initialized.streams h.nextBlk = some zf := stateI.protocol.good.live.hz
  have computedSetup : C.run (zwr (some (.tab h.nextBlk)) (fun s => bindings s dest source)) initialized =
      .ok ((), (ZStreamRef.tab h.nextBlk).put initialized next) := by
    simp [C.run, zwr, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.isRo, getInit, next]
  have readyEq : ready = (ZStreamRef.tab h.nextBlk).put initialized next :=
    (Prod.mk.inj (Except.ok.inj (actualSetup.symm.trans computedSetup))).2
  subst ready
  have globalsI := ZlibF.Spec.Public.Proofs.DeflateCore.initialized_globals
    (automatic_stream_domain h fresh unique globals) actualInit
  have edit := buffer_fields_rebuffer stateI.protocol.good globalsI next (by rfl)
  obtain ⟨zg, _getG, boundaryG⟩ := stateI.protocol.rebuffer edit
  have shape := shape_put stateI.protocol.good.live.hz next
  have indices := successful_init_indices hf hu hg getOld allocOld hv actualInit
  refine ⟨zg, sf, boundaryG, ?_, ownedI, ?_, ?_⟩
  · intro b
    change ((ZStreamRef.tab h.nextBlk).put initialized next).live b ↔ _
    rw [shape.live b]
    exact liveI b
  · simpa only [ZStreamRef.put_nalloc, localHeap] using indices.1
  · simpa only [ZStreamRef.put_nextBlk, localHeap, Nat.add_assoc] using indices.2

end ZlibF.Spec.Public.Proofs.CompressTail
