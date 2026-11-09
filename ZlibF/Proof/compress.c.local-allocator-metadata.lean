import ZlibF.Proof.«compress.c.local-data-history»

/-! # Allocator metadata on the same actual Fresh history

The original default initializer installs the default allocation functions.
The two real header calls preserve those fields. These observers compare
actual runs and returned live records; no caller invariant is assumed.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalAllocatorMetadata
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs.DefaultInit ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocal
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHeader
open ZlibF.Spec.Public.Proofs.CompressLocalPendingData
open ZlibF.Spec.Public.Proofs.CompressLocalDataHistory
open ZlibF.Spec.Public.Proofs.DeflateInit (resultState)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Allocator fields and zero totals are read from the actual successful
initialization result, including caller heaps with old typed collisions. -/
theorem fresh_init_allocator {h after : Heap} {returned : ZStream} {d : DeflateState}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after))
    (live : DLive after (.tab h.nextBlk) (h.nextBlk+1) returned d) :
    DefAlloc returned ∧ returned.total_in = 0 ∧ returned.total_out = 0 := by
  let root := ZStreamRef.tab h.nextBlk
  let automatic := ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h
  let old := ZlibF.Spec.Public.Proofs.CompressCaller.localStream h
  let z := ZlibF.Spec.Public.preparedStream old
  let prepared := root.put automatic z
  have get : root.get automatic = some old := by
    simp [root,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,ZStreamRef.get,old]
  obtain ⟨freshA,uniqueA⟩ := automatic_stream_local fresh
  have controls := shape_put get z
  have freshP : Fresh prepared := controls.fresh (by simp) freshA
  have uniqueP : UniqueFrom prepared h.nextBlk := uniqueA.shape controls
  have getP : root.get prepared = some z := ZStreamRef.get_put_same get _
  have allocator : DefAlloc z := by
    simp [DefAlloc,z,ZlibF.Spec.Public.preparedStream,old,ZlibF.Spec.Public.Proofs.CompressCaller.localStream]
  have static : Zlib.Trees.Proofs.Out.TreesStatic prepared.static := by
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using
      ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals
  have requests : ∀ j, j < 5 → prepared.allocOk (prepared.nalloc+j) = true := by
    intro j bound
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using allocations j bound
  obtain ⟨a1,a2,a3,qa,run,start⟩ := allocate_local_start freshP uniqueP getP allocator static requests
  let after := successHeap prepared root z 6 a1 a2 a3 qa
  have version : VersionValue automatic (.ref (.str 57) 0) (some 49) :=
    Or.inr ⟨49,rfl,Or.inr ⟨.str 57,0,strBytes ZLIB_VERSION,rfl,rfl,by decide +kernel,by decide +kernel⟩⟩
  have init := entry_run get version Z_DEFAULT_COMPRESSION
  have normalize : levelValue Z_DEFAULT_COMPRESSION = 6 := by decide +kernel
  rw [normalize,show ((6 : Int32) < 0 || (6 : Int32) > 9) = false from by decide +kernel] at init
  change deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 automatic = allocate (some root) 6 prepared at init
  have computed : C.run (deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112) automatic =
      .ok (Z_OK,successHeap prepared root z 6 a1 a2 a3 qa) := init.trans run
  have heaps := (Prod.mk.inj (Except.ok.inj (computed.symm.trans actualInit))).2
  have known := start.representation.live.hz
  rw [heaps] at known
  have sameZ : resultStream prepared root z 6 = returned :=
    Option.some.inj (known.symm.trans live.hz)
  rw [←sameZ]
  simp [DefAlloc,resultStream,rkZ,stateStream,z,ZlibF.Spec.Public.preparedStream,old,
    ZlibF.Spec.Public.Proofs.CompressCaller.localStream]

/-- The two real one-byte header calls retain the installed default
allocator functions. The actual returned stream is identified by its get. -/
theorem fresh_header_allocator {h after : Heap} {ob oo : Nat} {source : BPtr} {ai : UInt32}
    {returned : ZStream} {d : DeflateState}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 2) (input : ai ≠ 0 → source ≠ .null)
    (actual : splitHeaderPrefix (.tab h.nextBlk) (.ref (.blk ob) oo) source ai
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after))
    (live : DLive after (.tab h.nextBlk) (h.nextBlk+1) returned d) :
    DefAlloc returned ∧ returned.total_in = 0 ∧ returned.total_out = 2 := by
  obtain ⟨initialized,zi,di,ready,buf,output,init,start,bindings,first,refill,second,state,
      _account,_chains,_fields,_controls,_symbols,_pending,_busy,_last,_source,_input,_out,_zero⟩ :=
    fresh_two_header_data_prefix fresh globals allocations writable input
  have metadata := fresh_init_allocator fresh globals allocations init start.representation.live
  let bound := {zi with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai}
  let computedHeap := secondHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5)
    ob oo bound di buf output Z_NO_FLUSH
  have computed : splitHeaderPrefix (.tab h.nextBlk) (.ref (.blk ob) oo) source ai
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,computedHeap) := by
    simp only [C.run] at init bindings refill
    unfold splitHeaderPrefix
    simp only [bind_app,init,bindings,first,refill,second]
    rfl
  have heaps : computedHeap = after := (Prod.mk.inj (Except.ok.inj (computed.symm.trans actual))).2
  have known := state.live.hz
  change (ZStreamRef.tab h.nextBlk).get computedHeap = some (secondHeaderStream bound ob oo) at known
  rw [heaps] at known
  have sameZ : secondHeaderStream bound ob oo = returned := Option.some.inj (known.symm.trans live.hz)
  rw [←sameZ]
  simpa [DefAlloc,secondHeaderStream,oneHeaderStream,pendingStream,bound,metadata.2.1,metadata.2.2] using
    And.intro metadata.1 (And.intro metadata.2.1 (show (2 : UInt64) = 2 from rfl))

end ZlibF.Spec.Public.Proofs.CompressLocalAllocatorMetadata
