import ZlibF.Proof.«compress.c.local-header-data»

/-! # Actual pending publication retains the initialized data facts

The ordinary pending call keeps the unused hash window, initial controls
and empty symbol frequencies on its concrete copy heap. The final Fresh
history constructor supplies these facts itself; callers do not assume
an internal compressor invariant or a called specification.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalPendingData
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocalHeader
open ZlibF.Spec.Public.Proofs.CompressLocalRequest
open ZlibF.Spec.Public.Proofs.CompressLocalData
open ZlibF.Spec.Public.Proofs.CompressLocalSymbols
open ZlibF.Spec.Public.Proofs.CompressLocalHeaderData
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1400000

/-- Exact private result after the actual pending branch's two last-flush
stores and selected-byte publication. -/
def pendingDataState (d : DeflateState) (flush : Int32) (pb po : Nat) (n : UInt32) : DeflateState :=
  {pendingState {d with last_flush := flush} (.ref (.blk pb) (po+n.toNat)) n with last_flush := -1}

def pendingDataHeap (h : Heap) (r : ZStreamRef) (ds pb po ob oo : Nat) (z : ZStream) (d : DeflateState)
    (pending output : Array UInt8) (n : UInt32) (flush : Int32) : Heap :=
  setD (pendingCopyHeap (setD h ds {d with last_flush := flush}) r ds pb po ob oo z
    {d with last_flush := flush} pending output n) ds (pendingDataState d flush pb po n)

/-- Raw byte publication preserves the initialized zero frontier. If its
output aliases the still-unused window, the real copy may change only
bytes beyond the zero valid endpoint. Word-table collisions are kept. -/
theorem pending_data_chains {h : Heap} {r : ZStreamRef} {ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8} (n : UInt32) (flush : Int32)
    (chains : HeapChains h d 0) (fields : InitialReadFields d) (outGet : h.bytes ob = some output) :
    HeapChains (pendingDataHeap h r ds pb po ob oo z d pending output n flush)
      (pendingDataState d flush pb po n) 0 := by
  obtain ⟨w,p,q,wa,pa,qa,window,previous,head,getW,getP,getQ,H⟩ := chains
  by_cases same : w = ob
  · subst w
    have array : wa = output := Option.some.inj (getW.symm.trans outGet)
    subst wa
    have H' := chains_congr (w' := bfn (copyRange output pending oo po n.toNat)) H
      (fun _ => rfl) (fun _ => rfl) (by intro i before;simp [fields.1,fields.2.1] at before)
    exact ⟨ob,p,q,copyRange output pending oo po n.toNat,pa,qa,window,previous,head,
      by simp [pendingDataHeap,pendingCopyHeap],by simpa [pendingDataHeap,pendingCopyHeap] using getP,
      by simpa [pendingDataHeap,pendingCopyHeap] using getQ,H'⟩
  · exact ⟨w,p,q,wa,pa,qa,window,previous,head,
      by simpa [pendingDataHeap,pendingCopyHeap,upd_ne _ _ _ _ same] using getW,
      by simpa [pendingDataHeap,pendingCopyHeap] using getP,
      by simpa [pendingDataHeap,pendingCopyHeap] using getQ,H⟩

/-- Empty symbol bytes impose no content condition. Their actual leaf
frequencies and block balance transfer to any locally represented heap
with the same private record, including a legal caller-field rebuffer. -/
theorem empty_symbols_at_local {old h : Heap} {r : ZStreamRef} {cutoff ds oldDs : Nat}
    {z : ZStream} {d : DeflateState} (state : LocalState h cutoff r ds z d)
    (symbols : SymbolBoundary old oldDs d []) : SymbolBoundary h ds d [] := by
  obtain ⟨_oldBuffer,_oldBytes,_oldTrees,ledger,balance⟩ := symbols
  obtain ⟨found,b,buf,trees⟩ := state.trees
  have same : found = d := Option.some.inj (trees.base.dstate.symm.trans state.live.hs)
  subst found
  have stored : SymbolLedger buf d [] := {ledger with packed := by intro i s selected;simp at selected}
  exact ⟨b,buf,trees,stored,balance⟩

/-- This strengthens the actual ordinary pending call, using only the
metadata already produced by the preceding real header history. Its real
copy and typed stores supply every returned heap fact. -/
theorem local_pending_ordinary_data {h : Heap} {r : ZStreamRef} {cutoff ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8} {flush : Int32}
    (state : LocalState h cutoff r ds z d) (chains : HeapChains h d 0)
    (fields : InitialReadFields d) (controls : InitialDataControls cutoff d) (symbols : SymbolBoundary h ds d [])
    (busy : d.status = BUSY_STATE) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (positive : z.avail_out ≠ 0)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (enough : z.avail_out.toNat ≤ d.pending.toNat)
    (bits : d.bi_valid.toInt < 8) (buffer : d.pending_buf = .ref (.blk pb) 0)
    (cursor : d.pending_out = .ref (.blk pb) po) (pointer : z.next_out = .ref (.blk ob) oo)
    (outGet : h.bytes ob = some output) (pendingGet : h.bytes pb = some pending)
    (writable : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo+z.avail_out.toNat ≤ output.size) (pendingBound : po+d.pending.toNat ≤ pending.size) :
    let result := pendingDataState d flush pb po z.avail_out
    let after := pendingDataHeap h r ds pb po ob oo z d pending output z.avail_out flush
    let nextZ := pendingStream z (.ref (.blk ob) (oo+z.avail_out.toNat)) z.avail_out
    deflate (some r) flush h = .ok (Z_OK,after) ∧ LocalState after cutoff r ds nextZ result ∧
      StreamAccounting z nextZ 0 z.avail_out.toNat ∧ nextZ.avail_out = 0 ∧
      HeapChains after result 0 ∧ InitialReadFields result ∧ InitialDataControls cutoff result ∧
      SymbolBoundary after ds result [] ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 ∧
      nextZ.next_in = z.next_in ∧ nextZ.avail_in = z.avail_in := by
  obtain ⟨run,stateA,account,empty⟩ := local_pending_ordinary state busy mode positive valid enough bits buffer cursor pointer
    outGet pendingGet writable separate outBound pendingBound
  have symbolsA : SymbolBoundary (pendingDataHeap h r ds pb po ob oo z d pending output z.avail_out flush)
      ds (pendingDataState d flush pb po z.avail_out) [] := by
    obtain ⟨_oldBuffer,_oldBytes,_oldTrees,ledger,balance⟩ := symbols
    obtain ⟨found,b,buf,trees⟩ := stateA.trees
    have same : found = pendingDataState d flush pb po z.avail_out :=
      Option.some.inj (trees.base.dstate.symm.trans stateA.live.hs)
    subst found
    have kept : SymbolLedger _ (pendingDataState d flush pb po z.avail_out) [] := ledger.keep rfl rfl rfl rfl
    have stored : SymbolLedger buf (pendingDataState d flush pb po z.avail_out) [] :=
      {kept with packed := by intro i s selected;simp at selected}
    exact ⟨b,buf,trees,stored,balance⟩
  exact ⟨run,stateA,account,empty,pending_data_chains z.avail_out flush chains fields outGet,
    fields,controls,symbolsA,busy,rfl,rfl,rfl⟩

/-- The actual four caller-field writes preserve all initialized data
facts. The input and output offers are arbitrary; this does not assume
that a subsequent compression call has consumed them. -/
theorem local_data_rebuffer {h : Heap} {r : ZStreamRef} {cutoff ds : Nat} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff r ds z d) (chains : HeapChains h d 0)
    (fields : InitialReadFields d) (controls : InitialDataControls cutoff d) (symbols : SymbolBoundary h ds d [])
    (dest source : BPtr) (availableOut availableIn : UInt32) :
    let next := {z with next_out := dest,avail_out := availableOut,next_in := source,avail_in := availableIn}
    let ready := r.put h next
    C.run (zwr (some r) (fun s => {s with next_out := dest,avail_out := availableOut,next_in := source,avail_in := availableIn})) h = .ok ((),ready) ∧
      LocalState ready cutoff r ds next d ∧ HeapChains ready d 0 ∧ InitialReadFields d ∧
      InitialDataControls cutoff d ∧ SymbolBoundary ready ds d [] ∧ Frame h ready (StreamRoot r) := by
  let next := {z with next_out := dest,avail_out := availableOut,next_in := source,avail_in := availableIn}
  have stateA := local_state_setZD state (z' := next) (d' := d) rfl state.live.zalloc state.live.zfree rfl
    state.live.status state.inv (by trkeep)
  have getD : (r.put h next).dstates ds = some d := by simpa using state.live.hs
  rw [setD_self getD] at stateA
  have chainsA : HeapChains (r.put h next) d 0 := by
    obtain ⟨w,p,q,wa,pa,qa,window,previous,head,getW,getP,getQ,H⟩ := chains
    exact ⟨w,p,q,wa,pa,qa,window,previous,head,by simpa using getW,by simpa using getP,by simpa using getQ,H⟩
  refine ⟨?_,stateA,chainsA,fields,controls,empty_symbols_at_local stateA symbols,stream_store_full_frame h r next⟩
  simp [C.run,zwr_eq,state.live.hz,next]


def secondHeaderState (d : DeflateState) (flush : Int32) (pb : Nat) : DeflateState :=
  pendingDataState (oneHeaderState d) flush pb 1 1

def secondHeaderStream (z : ZStream) (ob oo : Nat) : ZStream :=
  pendingStream {(oneHeaderStream z ob oo) with avail_out := 1} (.ref (.blk ob) (oo+1+1)) 1

def secondHeaderHeap (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat) (z : ZStream) (d : DeflateState)
    (buf output : Array UInt8) (flush : Int32) : Heap :=
  let first := oneHeaderHeap h r ds pb ob oo z d buf output
  let offered := {(oneHeaderStream z ob oo) with avail_out := 1}
  let ready := r.put first offered
  pendingDataHeap ready r ds pb 1 ob (oo+1) offered (oneHeaderState d) (zlibHeaderBytes buf)
    (copyRange output (zlibHeaderBytes buf) oo 0 1) 1 flush

/-- The real one-field refill and second ordinary request retain every
initialized data fact on their exact returned heap. The input is untouched.
The Fresh history below constructs all metadata premises internally. -/
theorem local_second_header_data {h : Heap} {r : ZStreamRef} {cutoff ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {flush : Int32}
    (state : LocalState (oneHeaderHeap h r ds pb ob oo z d buf output) cutoff r ds
      (oneHeaderStream z ob oo) (oneHeaderState d))
    (chains : HeapChains (oneHeaderHeap h r ds pb ob oo z d buf output) (oneHeaderState d) 0)
    (fields : InitialReadFields (oneHeaderState d)) (controls : InitialDataControls cutoff (oneHeaderState d))
    (symbols : SymbolBoundary (oneHeaderHeap h r ds pb ob oo z d buf output) ds (oneHeaderState d) [])
    (pendingPtr : d.pending_buf = .ref (.blk pb) 0) (bits : d.bi_valid = 0)
    (one : z.avail_out = 1) (separate : ob ≠ pb) (writable : h.ro ob = false)
    (room : 2 ≤ buf.size) (outBound : oo+2 ≤ output.size)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (mode : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) :
    let first := oneHeaderHeap h r ds pb ob oo z d buf output
    let offered := {(oneHeaderStream z ob oo) with avail_out := 1}
    let ready := r.put first offered
    let after := secondHeaderHeap h r ds pb ob oo z d buf output flush
    let za := secondHeaderStream z ob oo
    let da := secondHeaderState d flush pb
    C.run (zwr (some r) (fun s => {s with avail_out := 1})) first = .ok ((),ready) ∧
      deflate (some r) flush ready = .ok (Z_OK,after) ∧ LocalState after cutoff r ds za da ∧
      StreamAccounting offered za 0 1 ∧ za.avail_out = 0 ∧ da.pending = 0 ∧ da.status = BUSY_STATE ∧ da.last_flush = -1 ∧
      HeapChains after da 0 ∧ InitialReadFields da ∧ InitialDataControls cutoff da ∧ SymbolBoundary after ds da [] ∧
      za.next_in = z.next_in ∧ za.avail_in = z.avail_in := by
  let first := oneHeaderHeap h r ds pb ob oo z d buf output
  let offered := {(oneHeaderStream z ob oo) with avail_out := 1}
  let ready := r.put first offered
  have next := local_output_refill state
  have chainsReady : HeapChains ready (oneHeaderState d) 0 := by
    obtain ⟨w,p,q,wa,pa,qa,window,previous,head,getW,getP,getQ,H⟩ := chains
    exact ⟨w,p,q,wa,pa,qa,window,previous,head,by simpa [ready] using getW,
      by simpa [ready] using getP,by simpa [ready] using getQ,H⟩
  have symbolsReady := empty_symbols_at_local next symbols
  have outGet : ready.bytes ob = some (copyRange output (zlibHeaderBytes buf) oo 0 1) := by
    simp [ready,first,oneHeaderHeap]
  have pendingGet : ready.bytes pb = some (zlibHeaderBytes buf) := by
    simp [ready,first,oneHeaderHeap,upd_ne _ _ _ _ (Ne.symm separate)]
  have bitBound : (oneHeaderState d).bi_valid.toInt < 8 := by simp [oneHeaderState,bits]
  have cursor : (oneHeaderState d).pending_out = .ref (.blk pb) 1 := by simp [oneHeaderState,pendingPtr,advance]
  have raw : offered.next_out = .ref (.blk ob) (oo+1) := rfl
  obtain ⟨actual,stateA,account,empty,chainsA,fieldsA,controlsA,symbolsA,busy,last,_input,_available⟩ :=
    local_pending_ordinary_data next chainsReady fields controls symbolsReady (by rfl) mode
      (by change (1 : UInt32) ≠ 0;decide) valid (by change (1 : Nat) ≤ 1;decide) bitBound pendingPtr cursor raw
      outGet pendingGet (by simpa [ready,first,oneHeaderHeap] using writable) separate
      (by change oo+1+1 ≤ (copyRange output (zlibHeaderBytes buf) oo 0 1).size;rw [size_copyRange];omega)
      (by change 1+1 ≤ (zlibHeaderBytes buf).size;simp only [zlibHeaderBytes,Array.size_set!];exact room)
  refine ⟨?_,actual,stateA,account,empty,?_,busy,last,chainsA,fieldsA,controlsA,symbolsA,rfl,rfl⟩
  · simp only [C.run,zwr_eq,state.live.hz]
  · change (1 : UInt64)-(1 : UInt32).toUInt64 = 0
    rfl


/-- One actual Fresh initialization, binding, first one-byte header call,
real one-field output refill and second complete pending-header call.
Every internal data fact is constructed along that history. The only
output premise is the caller's two-byte writable range. -/
theorem fresh_two_header_data_prefix {h : Heap} {ob oo : Nat} {source : BPtr} {ai : UInt32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 2) (input : ai ≠ 0 → source ≠ .null) :
    ∃ initialized z d ready buf output,
      let bound := {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai}
      let first := oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo bound d buf output
      let offered := {(oneHeaderStream bound ob oo) with avail_out := 1}
      let secondReady := (ZStreamRef.tab h.nextBlk).put first offered
      let after := secondHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo bound d buf output Z_NO_FLUSH
      let za := secondHeaderStream bound ob oo
      let da := secondHeaderState d Z_NO_FLUSH (h.nextBlk+5)
      C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,initialized) ∧
      LocalStart initialized h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧
      C.run (zwr (some (.tab h.nextBlk)) (fun s => {s with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai}))
        initialized = .ok ((),ready) ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH ready = .ok (Z_OK,first) ∧
      C.run (zwr (some (.tab h.nextBlk)) (fun s => {s with avail_out := 1})) first = .ok ((),secondReady) ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH secondReady = .ok (Z_OK,after) ∧
      LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) za da ∧ StreamAccounting offered za 0 1 ∧
      HeapChains after da 0 ∧ InitialReadFields da ∧ InitialDataControls h.nextBlk da ∧
      SymbolBoundary after (h.nextBlk+1) da [] ∧
      da.pending = 0 ∧ da.status = BUSY_STATE ∧ da.last_flush = -1 ∧
      za.next_in = source ∧ za.avail_in = ai ∧ za.next_out = .ref (.blk ob) (oo+2) ∧ za.avail_out = 0 := by
  have writableOne : Writable h (.ref (.blk ob) oo) 1 := by
    rcases writable with impossible | ⟨ref,off,array,pointer,get,rw,room⟩
    · exact Or.inl ⟨impossible.1,by omega⟩
    · exact Or.inr ⟨ref,off,array,pointer,get,rw,by omega⟩
  obtain ⟨initialized,z,d,ready,buf,output,init,start,bindings,firstRun,firstState,_physical,originalFrame⟩ :=
    fresh_first_one_call fresh globals allocations writableOne input (Or.inl rfl)
  obtain ⟨ctxInit,ctxZ,ctxD,ctxReady,ctxBuf,ctxOutput,ctxRun,ctxStart,ctxBindings,ctxFirst,ctxState,
      ctxChains,ctxFields,ctxControls,ctxSymbols⟩ := fresh_header_data_prefix fresh globals allocations writableOne input
  have sameInit : ctxInit = initialized := (Prod.mk.inj (Except.ok.inj (ctxRun.symm.trans init))).2
  subst ctxInit
  have sameReady : ctxReady = ready := (Prod.mk.inj (Except.ok.inj (ctxBindings.symm.trans bindings))).2
  subst ctxReady
  have sameFirst := (Prod.mk.inj (Except.ok.inj (ctxFirst.symm.trans firstRun))).2
  rw [sameFirst] at ctxState ctxChains ctxSymbols
  have sameD : oneHeaderState ctxD = oneHeaderState d :=
    Option.some.inj (ctxState.live.hs.symm.trans firstState.live.hs)
  rw [sameD] at ctxChains ctxFields ctxControls ctxSymbols
  have pendingPtr : d.pending_buf = .ref (.blk (h.nextBlk+5)) 0 := ctxControls.2.2.2.2.2.2.2.2
  rcases writable with ⟨impossible,_⟩ | ⟨ref,off,original,pointer,get,rw,room⟩
  · cases impossible
  obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj pointer
  subst ref off
  have oldLive : h.live ob := by simp [Heap.live,show h.bytes ob = some original from get]
  have oldKey := fresh.lt oldLive
  have oldSlot := originalFrame.2.2.2.2.2 ob oldLive (by simp)
  have outputEq : output = original := Option.some.inj (by
    simpa only [Zlib.Trees.Proofs.Out.setB,upd_same] using oldSlot.1.trans get)
  have outputRoom : oo+2 ≤ output.size := by rw [outputEq];exact room
  have outputWritable : ready.ro ob = false := by
    simpa [Zlib.Trees.Proofs.Out.setB,oneHeaderHeap] using oldSlot.2.2.2.2.2.2.2.trans rw
  have separate : ob ≠ h.nextBlk+5 := by omega
  have getPending : (oneHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo
      {z with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := ai} d buf output).bytes (h.nextBlk+5) =
      some (zlibHeaderBytes buf) := by
    simp [oneHeaderHeap,upd_ne _ _ _ _ (Ne.symm separate)]
  obtain ⟨found,pb,stored,trees⟩ := firstState.trees
  have foundEq : found = oneHeaderState d := Option.some.inj (trees.base.dstate.symm.trans firstState.live.hs)
  subst found
  have pbEq : pb = h.nextBlk+5 := BRef.blk.inj (Ptr.ref.inj (trees.base.pbuf.symm.trans pendingPtr)).1
  subst pb
  have storedEq : stored = zlibHeaderBytes buf := Option.some.inj (trees.base.bytes.symm.trans getPending)
  have bufferRoom : 2 ≤ buf.size := by
    have size := trees.base.size
    have lower := trees.base.lit_lo
    rw [storedEq] at size
    simp only [zlibHeaderBytes,Array.size_set!] at size
    omega
  obtain ⟨refill,secondRun,stateA,account,outZero,pendingZero,busy,last,chainsA,fieldsA,controlsA,symbolsA,
      _source,_input⟩ := local_second_header_data firstState ctxChains ctxFields ctxControls ctxSymbols
    pendingPtr start.bits rfl separate outputWritable bufferRoom outputRoom input (Or.inl rfl)
  exact ⟨initialized,z,d,ready,buf,output,init,start,bindings,firstRun,refill,secondRun,stateA,account,
    chainsA,fieldsA,controlsA,symbolsA,pendingZero,busy,last,rfl,rfl,rfl,outZero⟩

end ZlibF.Spec.Public.Proofs.CompressLocalPendingData
