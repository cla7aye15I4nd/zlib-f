import ZlibF.Proof.«compress.c.shadow-init-execution»
import ZlibF.Proof.«deflate.c.engine.generic-request-encoding-state»

/-! # The same successful initialization on arbitrary Fresh caller storage

Only the default initialization seed is simulated. All five actual
allocator choices are successful in this checkpoint. Error exits and
subsequent data-loop transport are separate obligations.
-/
namespace ZlibF.Spec.Public.Proofs.CompressShadow
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateInit (resultState)
open Zlib.Trees.Proofs.Out (TreesStatic)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem allocate_run {h : Heap} {r : ZStreamRef} {z : ZStream}
    (fresh : Fresh h) (get : r.get h = some z) (allocator : DefAlloc z)
    (static : TreesStatic h.static)
    (requests : ∀ j,j<5 → h.allocOk (h.nalloc+j) = true) :
    ∃ a1 a2 a3 qa,
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      qa = wordGarbage (publishedHeap h r z) 2 ∧
      allocate (some r) 6 h = .ok (Z_OK,successHeap h r z 6 a1 a2 a3 qa) := by
  let ph := publishedHeap h r z
  have first : h.allocOk h.nalloc = true := by simpa using requests 0 (by decide)
  have rest : ∀ j,j<4 → ph.allocOk (ph.nalloc+j) = true := by
    intro j small
    simpa [ph,publishedHeap,stateHeap,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using requests (j+1) (by omega)
  have freshP : Fresh ph := fresh_stateHeap ((shape_put get _).fresh (by simp) fresh) _
  have getP : r.get ph = some (stateStream z h.nextBlk) := by
    simp [ph,publishedHeap,ZStreamRef.get_put_same get]
  have stateP : ph.dstates h.nextBlk = some (baseState r) := by
    simp [ph,publishedHeap,stateHeap]
  obtain ⟨live,trees,blocks⟩ := ready_objects 6 getP stateP
    (by simp [ph,publishedHeap,stateHeap]) allocator rfl (by simpa [ph,publishedHeap,stateHeap] using static) rest
  obtain ⟨a1,a2,a3,qa,s1,s2,s3,getQ,reset⟩ :=
    reset_run 6 live trees blocks (by decide) (by decide)
  have array : qa = wordGarbage ph 2 := by
    have actual : (readyHeap ph h.nextBlk r 6).words (ph.nextBlk+2) = some (wordGarbage ph 2) := by
      simp [readyHeap,successfulBuffers]
    exact Option.some.inj (getQ.symm.trans actual)
  refine ⟨a1,a2,a3,qa,s1,s2,s3,array,?_⟩
  rw [allocate_to_finish fresh get allocator.1 first,finish_to_reset _ _ _ _ rest,reset]
  rfl

def seedPrepared (h : Heap) : Heap :=
  (ZStreamRef.tab h.nextBlk).put (CompressCaller.localHeap h)
    (preparedStream (CompressCaller.localStream h))

def seedResult (h : Heap) (a1 a2 a3 : Array CtData) (qa : Array UInt16) : Heap :=
  successHeap (seedPrepared h) (.tab h.nextBlk) (preparedStream (CompressCaller.localStream h)) 6 a1 a2 a3 qa

theorem automatic_fresh {h : Heap} (fresh : Fresh h) : Fresh (CompressCaller.localHeap h) := by
  intro b large live
  have ne : b ≠ h.nextBlk := by change h.nextBlk+1 ≤ b at large;omega
  apply fresh b (by change h.nextBlk+1 ≤ b at large;omega)
  simpa only [CompressCaller.localHeap,Heap.live,upd_ne _ _ _ _ ne] using live

/-- Real default init with all five allocations successful, on the real
automatic stream. Old caller IDs may contain several different kinds. -/
theorem actual_seed_init {h : Heap} (fresh : Fresh h) (globals : LibraryGlobals h)
    (requests : ∀ j,j<5 → h.allocOk (h.nalloc+j) = true) :
    ∃ a1 a2 a3 qa,
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      qa = wordGarbage (publishedHeap (seedPrepared h) (.tab h.nextBlk)
        (preparedStream (CompressCaller.localStream h))) 2 ∧
      C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (CompressCaller.localHeap h) = .ok (Z_OK,seedResult h a1 a2 a3 qa) := by
  let r := ZStreamRef.tab h.nextBlk
  let old := CompressCaller.localStream h
  have get : r.get (CompressCaller.localHeap h) = some old := by
    simp [r,old,CompressCaller.localHeap,ZStreamRef.get]
  have freshP : Fresh (seedPrepared h) := (shape_put get _).fresh (by simp) (automatic_fresh fresh)
  have getP : r.get (seedPrepared h) = some (preparedStream old) := ZStreamRef.get_put_same get _
  have allocator : DefAlloc (preparedStream old) := by
    simp [DefAlloc,preparedStream,old,CompressCaller.localStream]
  obtain ⟨a1,a2,a3,qa,s1,s2,s3,array,run⟩ := allocate_run freshP getP allocator
    (by simpa [seedPrepared,CompressCaller.localHeap] using
      ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals)
    (by intro j hj;simpa [seedPrepared,CompressCaller.localHeap] using requests j hj)
  have version : VersionValue (CompressCaller.localHeap h) (.ref (.str 57) 0) (some 49) :=
    Or.inr ⟨49,rfl,Or.inr ⟨.str 57,0,strBytes ZLIB_VERSION,rfl,rfl,by decide,by decide⟩⟩
  have entry := entry_run get version Z_DEFAULT_COMPRESSION
  rw [show levelValue Z_DEFAULT_COMPRESSION = 6 from by decide,
    show ((6 : Int32) < 0 || (6 : Int32) > 9) = false from by decide] at entry
  exact ⟨a1,a2,a3,qa,s1,s2,s3,array,entry.trans run⟩

theorem shadow_seed_init {h : Heap} (globals : LibraryGlobals h)
    (requests : ∀ j,j<5 → h.allocOk (h.nalloc+j) = true) :
    ∃ a1 a2 a3 qa,
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      qa = wordGarbage (publishedHeap (seedPrepared (seedShadow h)) (.tab (7*h.nextBlk))
        (preparedStream (CompressCaller.localStream (seedShadow h)))) 2 ∧
      C.run (deflateInit_ (some (.tab (7*h.nextBlk))) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (CompressCaller.localHeap (seedShadow h)) = .ok (Z_OK,seedResult (seedShadow h) a1 a2 a3 qa) ∧
      GenericDefaultRequestTrace (.tab (7*h.nextBlk)) (seedResult (seedShadow h) a1 a2 a3 qa) ∧
      ∃ zf sf,DefaultEncodingState (seedResult (seedShadow h) a1 a2 a3 qa) (.tab (7*h.nextBlk))
        (7*h.nextBlk+1) zf sf (engineConfig sf) [] [] := by
  obtain ⟨a1,a2,a3,qa,s1,s2,s3,array,run⟩ := actual_seed_init (seed_fresh h) (seed_globals globals) requests
  have domain := automatic_shadow_domain globals
  have trace := GenericDefaultRequestTrace.init domain run
  obtain ⟨fresh,unique,global,version,z,get,allocators,_null⟩ := domain
  have encoded := observed_default_init_encoding_state fresh
    (by simpa only [Zlib.Inflate.Spec.Uniq,Zlib.Inflate.Spec.cnt,Uniq,cnt] using unique)
    global get allocators version run
  exact ⟨a1,a2,a3,qa,s1,s2,s3,array,run,trace,encoded⟩

#print axioms actual_seed_init
#print axioms shadow_seed_init
end ZlibF.Spec.Public.Proofs.CompressShadow
