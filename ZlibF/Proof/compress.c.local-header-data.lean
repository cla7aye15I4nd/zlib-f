import ZlibF.Proof.«compress.c.local-symbol-initial»
import ZlibF.Proof.«compress.c.local-threshold»

/-! # Same real initialization and first header supply the data-entry facts -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalHeaderData
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral ZlibF.Spec.Public.Proofs.CompressLocalSymbols
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalData
open Zlib.Trees.Proofs.Out (InitialFrequencies)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

/-- All local data facts are derived from one actual successful initializer,
its real four-field binding and its complete one-byte header request.
No arbitrary local invariant is a caller premise. Old typed collisions in
the original Fresh heap remain admitted. This is a history prefix; its
subsequent pending-header drain and data request remain separate steps. -/
theorem fresh_header_data_prefix {h : Heap} {ob oo : Nat} {source : BPtr} {ai : UInt32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 1) (input : ai ≠ 0 → source ≠ .null) :
    ∃ initialized z d ready buf output,
      let first := oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo
        {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} d buf output
      let zh := oneHeaderStream {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} ob oo
      let dh := oneHeaderState d
      C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,initialized) ∧
      LocalStart initialized h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧
      C.run (zwr (some (.tab h.nextBlk)) (fun s => {s with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai}))
        initialized = .ok ((),ready) ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH ready = .ok (Z_OK,first) ∧
      LocalState first h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) zh dh ∧
      HeapChains first dh 0 ∧ InitialReadFields dh ∧ InitialDataControls h.nextBlk dh ∧
      SymbolBoundary first (h.nextBlk+1) dh [] := by
  obtain ⟨initialized,z,d,ready,buf,output,init,start,bindings,actual,stateA,_physical,_frame⟩ :=
    fresh_first_one_call fresh globals allocations writable input (Or.inl rfl)
  have fields := initialized_read_fields fresh globals allocations init start.representation
  obtain ⟨symbol,frequencies,controls⟩ := initialized_symbol_boundary fresh globals allocations init start.representation
  have chains := initialized_hash_chains fresh globals allocations init start.representation
  have computed : C.run (zwr (some (.tab h.nextBlk)) (fun s =>
      {s with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai})) initialized =
      .ok ((),(ZStreamRef.tab h.nextBlk).put initialized
        {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai}) := by
    simp only [C.run,zwr_eq,start.representation.live.hz]
  have readyEq := (Prod.mk.inj (Except.ok.inj (bindings.symm.trans computed))).2
  obtain ⟨w,p,q,wa,pa,qa,win,prev,head,getW,getP,getQ,H⟩ := chains
  have wid : w = h.nextBlk+2 := by
    exact BRef.blk.inj (Ptr.ref.inj (win.symm.trans controls.2.2.2.2.2.1)).1
  subst w
  have oldOut : ob < h.nextBlk := by
    rcases writable with ⟨impossible,_⟩ | ⟨ref,off,bytes,equal,get,_rw,_bound⟩
    · cases impossible
    obtain ⟨eq,_⟩ := Ptr.ref.inj equal
    cases eq
    exact fresh.lt (by simp [Heap.live,show h.bytes ob = some bytes from get])
  have privateNotOutput : h.nextBlk+2 ≠ ob := by omega
  have privateNotPending : h.nextBlk+2 ≠ h.nextBlk+5 := by omega
  have chainsA : HeapChains
      (oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo
        {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} d buf output)
      (oneHeaderState d) 0 := by
    refine ⟨h.nextBlk+2,p,q,wa,pa,qa,win,prev,head,?_,?_,?_,H⟩
    · simpa only [oneHeaderHeap,setD_bytes,ZStreamRef.put_bytes,
        upd_ne _ _ _ _ privateNotOutput,upd_ne _ _ _ _ privateNotPending,
        readyEq,ZStreamRef.put_bytes] using getW
    · simpa only [oneHeaderHeap,setD_words,ZStreamRef.put_words,readyEq,ZStreamRef.put_words] using getP
    · simpa only [oneHeaderHeap,setD_words,ZStreamRef.put_words,readyEq,ZStreamRef.put_words] using getQ
  have controlsA : InitialDataControls h.nextBlk (oneHeaderState d) := controls
  have frequenciesA : InitialFrequencies (oneHeaderState d).dyn_ltree (oneHeaderState d).dyn_dtree := frequencies
  obtain ⟨d0,pb,stored,trees⟩ := stateA.trees
  have same : d0 = oneHeaderState d := Option.some.inj (trees.base.dstate.symm.trans stateA.live.hs)
  subst d0
  have ledger := empty_symbol_ledger (buf := stored) controlsA.1 frequenciesA
  have balance : BlockBalance (oneHeaderState d) [] (deferredCredit (oneHeaderState d)) := by
    simp [BlockBalance,deferredCredit,controlsA.2.1,controlsA.2.2.1,controlsA.2.2.2.1,represented]
  exact ⟨initialized,z,d,ready,buf,output,init,start,bindings,actual,stateA,chainsA,
    read_fields_after_header fields,controlsA,pb,stored,trees,ledger,balance⟩

end ZlibF.Spec.Public.Proofs.CompressLocalHeaderData
