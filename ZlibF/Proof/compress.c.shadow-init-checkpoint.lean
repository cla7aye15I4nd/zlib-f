import ZlibF.Proof.«compress.c.shadow-init-views»

/-! # A same-execution default-initialization shadow checkpoint

The old kinds are separated before the real automatic stream and default
initializer execute. Initialization has not yet installed caller buffers,
so unrelated old record pointers are not followed. This checkpoint covers
the five-success branch, not the data loop or a full codec simulation.
-/
namespace ZlibF.Spec.Public.Proofs.CompressShadow
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- Six new typed objects are observed: the automatic stream and five
malloc objects. Byte contents and the cleared head array correspond under
the single future-ID shift. Embedded tree references are established by
seed_state_parameters on these same returned records. The three ct_data
arrays are not claimed equal by this resource checkpoint. -/
structure SeedInitPair (h original shadow : Heap) : Prop where
  originalRun : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
    (CompressCaller.localHeap h) = .ok (Z_OK,original)
  shadowRun : C.run (deflateInit_ (some (.tab (7*h.nextBlk))) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
    (CompressCaller.localHeap (seedShadow h)) = .ok (Z_OK,shadow)
  originalNext : original.nextBlk = h.nextBlk+6
  shadowNext : shadow.nextBlk = 7*h.nextBlk+6
  originalCalls : original.nalloc = h.nalloc+5
  shadowCalls : shadow.nalloc = h.nalloc+5
  oracle : original.allocOk = shadow.allocOk
  garbage : original.garbage = shadow.garbage
  borrow : original.libcErrorBorrow = shadow.libcErrorBorrow
  window : original.bytes (h.nextBlk+2) = shadow.bytes (7*h.nextBlk+2)
  prev : original.words (h.nextBlk+3) = shadow.words (7*h.nextBlk+3)
  head : original.words (h.nextBlk+4) = shadow.words (7*h.nextBlk+4)
  pending : original.bytes (h.nextBlk+5) = shadow.bytes (7*h.nextBlk+5)
  oldBytes : ∀ b a,h.bytes b = some a →
    original.bytes b = some a ∧ shadow.bytes (rename h.nextBlk 0 b) = some a
  history : GenericDefaultRequestTrace (.tab (7*h.nextBlk)) shadow
  encoding : ∃ zf sf,DefaultEncodingState shadow (.tab (7*h.nextBlk)) (7*h.nextBlk+1)
    zf sf (engineConfig sf) [] []

theorem successful_initialization_checkpoint {h : Heap} (fresh : Fresh h) (globals : LibraryGlobals h)
    (requests : ∀ j,j<5 → h.allocOk (h.nalloc+j) = true) :
    ∃ original shadow,SeedInitPair h original shadow := by
  obtain ⟨a1,a2,a3,qa,_a1size,_a2size,_a3size,arrayO,originalRun⟩ := actual_seed_init fresh globals requests
  obtain ⟨b1,b2,b3,qb,_b1size,_b2size,_b3size,arrayS,shadowRun,history,encoding⟩ := shadow_seed_init globals requests
  have sameHead : qb = qa := arrayS.trans ((seed_qa_shadow h).trans arrayO.symm)
  let original := seedResult h a1 a2 a3 qa
  let shadow := seedResult (seedShadow h) b1 b2 b3 qb
  obtain ⟨nextO,callsO,oracleO,garbageO,_staticO,_baseO,borrowO⟩ := seed_result_metadata h a1 a2 a3 qa
  obtain ⟨nextS,callsS,oracleS,garbageS,_staticS,_baseS,borrowS⟩ := seed_result_metadata (seedShadow h) b1 b2 b3 qb
  obtain ⟨_streamO,_stateO,windowO,prevO,headO,pendingO,_writableO,_pendingWritableO⟩ :=
    seed_result_objects h a1 a2 a3 qa
  obtain ⟨_streamS,_stateS,windowS,prevS,headS,pendingS,_writableS,_pendingWritableS⟩ :=
    seed_result_objects (seedShadow h) b1 b2 b3 qb
  have nextSeed : (seedShadow h).nextBlk = 7*h.nextBlk := rfl
  rw [nextSeed] at nextS windowS prevS headS pendingS
  have byteContent (j : Nat) : byteGarbage (seedShadow h) j = byteGarbage h j := by
    unfold byteGarbage
    exact congrArg (fun f : Fin 65536 → UInt8 => Array.ofFn f) (by funext i;rfl)
  have wordContent (j : Nat) : wordGarbage (seedShadow h) j = wordGarbage h j := by
    unfold wordGarbage
    exact congrArg (fun f : Fin 32768 → UInt16 => Array.ofFn f) (by funext i;rfl)
  have oldBytes : ∀ b a,h.bytes b = some a →
      original.bytes b = some a ∧ shadow.bytes (rename h.nextBlk 0 b) = some a := by
    intro b a get
    have old : b < h.nextBlk := fresh.lt (Or.inl (by rw [get];simp))
    have shiftedOld : rename h.nextBlk 0 b < (seedShadow h).nextBlk := by
      simp only [rename,old,ite_true,seedShadow]
      omega
    have keepO := seed_result_old old a1 a2 a3 qa
    have keepS := seed_result_old shiftedOld b1 b2 b3 qb
    exact ⟨keepO.1.trans get,keepS.1.trans (seed_old_bytes fresh get).1⟩
  refine ⟨original,shadow,?_⟩
  constructor
  · exact originalRun
  · exact shadowRun
  · exact nextO
  · exact nextS
  · exact callsO
  · exact callsS
  · exact oracleO.trans oracleS.symm
  · exact garbageO.trans garbageS.symm
  · exact borrowO.trans borrowS.symm
  · apply windowO.trans
    simpa only [byteContent] using windowS.symm
  · apply prevO.trans
    simpa only [wordContent] using prevS.symm
  · exact headO.trans ((congrArg (fun q : Array UInt16 => some (clearHead q 32768)) sameHead).symm.trans headS.symm)
  · apply pendingO.trans
    simpa only [byteContent] using pendingS.symm
  · exact oldBytes
  · exact history
  · exact encoding

#print axioms successful_initialization_checkpoint

/-- The parameter templates describe the records in the same two actual
returned heaps, rather than detached sample states. In particular their
embedded tree references and depth arrays can use seed_state_parameters. -/
theorem SeedInitPair.records {h original shadow : Heap}
    (pair : SeedInitPair h original shadow) (fresh : Fresh h) (globals : LibraryGlobals h)
    (requests : ∀ j,j<5 → h.allocOk (h.nalloc+j) = true) :
    ∃ a1 a2 a3 b1 b2 b3,
      original.streams h.nextBlk = some (seedStream h) ∧
      shadow.streams (7*h.nextBlk) = some (seedStream (seedShadow h)) ∧
      original.dstates (h.nextBlk+1) = some (seedState h a1 a2 a3) ∧
      shadow.dstates (7*h.nextBlk+1) = some (seedState (seedShadow h) b1 b2 b3) ∧
      a1.size = 573 ∧ a2.size = 61 ∧ a3.size = 39 ∧
      b1.size = 573 ∧ b2.size = 61 ∧ b3.size = 39 := by
  obtain ⟨a1,a2,a3,qa,s1,s2,s3,_arrayO,runO⟩ := actual_seed_init fresh globals requests
  obtain ⟨b1,b2,b3,qb,t1,t2,t3,_arrayS,runS,_history,_encoding⟩ := shadow_seed_init globals requests
  have heapO : seedResult h a1 a2 a3 qa = original :=
    congrArg Prod.snd (Except.ok.inj (runO.symm.trans pair.originalRun))
  have heapS : seedResult (seedShadow h) b1 b2 b3 qb = shadow :=
    congrArg Prod.snd (Except.ok.inj (runS.symm.trans pair.shadowRun))
  have objO := seed_result_objects h a1 a2 a3 qa
  have objS := seed_result_objects (seedShadow h) b1 b2 b3 qb
  rw [heapO] at objO
  rw [heapS] at objS
  have nextSeed : (seedShadow h).nextBlk = 7*h.nextBlk := rfl
  rw [nextSeed] at objS
  exact ⟨a1,a2,a3,b1,b2,b3,objO.1,objS.1,objO.2.1,objS.2.1,s1,s2,s3,t1,t2,t3⟩

#print axioms SeedInitPair.records
end ZlibF.Spec.Public.Proofs.CompressShadow
