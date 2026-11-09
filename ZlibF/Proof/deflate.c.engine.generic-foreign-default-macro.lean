import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-phase»
import ZlibF.Proof.«deflate.c.engine.flush-macro-frame»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A complete private frame preserves an admitted foreign caller output view. -/
theorem private_frame_foreign_output_same {h after : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    Space.get after (BRef.dstate_depth owner) = Space.get h (BRef.dstate_depth owner) := by
  obtain ⟨foreign,get,_,_,_,noRoot⟩ := caller_foreign_output good buffers pointer
  obtain ⟨z0,hz0,_,output,_⟩ := buffers
  have same : z0=z := Option.some.inj (hz0.symm.trans good.live.hz)
  subst z0
  rw [pointer] at output
  have outside : ¬ DeflateOwned ds d owner := by
    rcases output with impossible|⟨_,_,unowned⟩
    · cases impossible
    · intro owned
      exact unowned owner rfl ((stream_owned_deflate good owner).mpr owned)
  have slots := frame.2.2.2.2.2 owner (by simp [Heap.live,get])
    (fun yes => yes.elim noRoot outside)
  simp only [Space.get,slots.2.2.2.2.1]

/-- Actual default-memory positive-level block publication to foreign caller depth storage.
The actual encoder chooses stored, fixed or dynamic output. Its existing mathematical proof
is reused; only caller publication uses the foreign destination adapter. This is an internal
macro producer, not a theorem about complete public request histories. -/
theorem default_flush_block_only_foreign_publish {h : Heap} {r : ZStreamRef} {ds pb owner oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base+represented xs=origin+d.strstart.toNat)
    (view : ∀ i,i<fillEnd d → bfn window i=input (origin+i)) (last : Bool) :
    ∃ produced after z' result written remaining kind body padding,
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((),after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧
      FlushWorkFrame {d with block_start:=d.strstart.toUInt64.toInt64} result ∧
      result.bi_valid.toInt < 8 ∧ (last=true → result.bi_valid.toInt.toNat=0) ∧
      BlockInit.BlockClear result ∧ result.sym_next=0 ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree ∧
      (result.pending=0 → result.pending_out=result.pending_buf) ∧
      (0<z'.avail_out.toNat → PublishReady result) ∧
      result.block_start=result.strstart.toUInt64.toInt64 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
      kind<3 ∧ padding.length<8 ∧ (last=false → padding=[]) ∧ (kind=0 → padding=[]) ∧
      ZlibF.Spec.bytesToBits written++remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (Zlib.Trees.Proofs.Out.natBits (if last then 1 else 0) 1 ++
          Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool,(kind=0 → suffix.length%8=0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body++suffix) suffix
          (inputPrefix input (base+represented xs)) := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze,ready,emitted,outputBuf,kind,body,padding,encodeRun,goodE,treesE,buffersE,
    accountE,sizesE,storageE,ledgerE,clearE,sizeE,boundE,cursorE,finalE,kindBound,
    padBound,padNone,storedPad,outputE,grammar⟩ :=
    flush_default_ready (ob:=pb) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  let updated : DeflateState := {emitted with block_start:=emitted.strstart.toUInt64.toInt64}
  obtain ⟨updateRun,goodU,treesU,buffersU,sizesU,storageU⟩ :=
    flush_block_start_engine (ob:=pb) goodE treesE buffersE
  have frameE := flush_default_run_frame (ob:=pb) good trees buffers positive cursor memory pending bits ledger clear trace
    win get range balance accounted view last encodeRun goodE.live.hs
  have startE : emitted.strstart=d.strstart := by rw [frameE]
  have frameU : FlushWorkFrame {d with block_start:=d.strstart.toUInt64.toInt64} updated := by
    simpa only [updated,startE] using (frameE.block_start emitted.strstart.toUInt64.toInt64)
  have nextOut : ze.next_out=z.next_out := by rw [accountE.2.2.2.2.2.1,advance_zero]
  have pointerE : ze.next_out=.ref (.dstate_depth owner) oo := nextOut.trans pointer
  have roomU : 8*updated.pending.toNat+updated.bi_valid.toInt.toNat≤8*outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8*emitted.pending.toNat+emitted.bi_valid.toInt.toNat≤524288
    omega
  obtain ⟨produced,after,z',result,written,remaining,flush,goodA,buffersA,accountA,sizesA,
    storageA,copied,left,low,validA,fieldsA,bytes,pendingA,outputA,bufferA⟩ :=
    flush_pending_foreign_bits_frame goodU treesU buffersU pointerE cursorE roomU
  have emptyCursor := foreign_pending_run_empty_cursor goodU treesU buffersU pointerE cursorE roomU flush goodA.live.hs
  have phase := foreign_pending_publication_run_phase goodU treesU buffersU pointerE cursorE roomU flush goodA.live.hs goodA.live.hz
  have frameA : FlushWorkFrame {d with block_start:=d.strstart.toUInt64.toInt64} result := by
    rw [fieldsA]
    exact frameU.output _ _ _ _ _
  have final : last=true → result.bi_valid.toInt.toNat=0 := by
    intro flag
    have validU : updated.bi_valid.toInt=0 := finalE flag
    rw [validU] at validA
    exact validA
  have ledgerU : SymbolLedger outputBuf updated [] := ledgerE.keep rfl rfl rfl rfl
  have ledgerA : SymbolLedger outputBuf result [] := by rw [fieldsA]; exact ledgerU.keep rfl rfl rfl rfl
  have countA : result.sym_next=0 := by
    apply UInt32.toNat_inj.mp
    change result.sym_next.toNat=0
    simpa only [List.length_nil,Nat.mul_zero] using ledgerA.count
  have clearA : BlockInit.BlockClear result := by rw [fieldsA];exact ⟨clearE.bl,clearE.opt,clearE.fixed⟩
  have frequencies : Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree := by
    constructor
    · intro k bound
      simpa only [literalFrequency,countKey,Nat.add_zero] using ledgerA.literal k bound
    · intro k bound
      simpa only [distanceFrequency,countKey] using ledgerA.distance k bound
  have position : result.block_start=result.strstart.toUInt64.toInt64 := by rw [fieldsA]
  have privateStorage := storageE.trans storageU
  have storageReady : OutputStorage h (setD ready ds updated) r ds pb owner :=
    { privateStorage with frame := full_frame_weaken privateStorage.frame (by
        intro b changed
        rcases changed with root|same|same|same
        · exact Or.inl root
        · exact Or.inr (Or.inl same)
        · exact Or.inr (Or.inr (Or.inl same))
        · exact Or.inr (Or.inr (Or.inl same))) }
  have privateFrame := (storageE.trans storageU).pending_private_frame trees.base.pbuf
  have outputView := private_frame_foreign_output_same good buffers pointer privateFrame
  have bufferBig : BufferFrame (setD ready ds updated) after
      (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨.ref (.dstate_depth owner) oo,produced⟩] := by
    rw [pointerE] at bufferA
    refine ⟨full_frame_weaken bufferA.1 ?_,bufferA.2⟩
    intro b changed
    rcases changed with root|same|same
    · exact Or.inl root
    · exact Or.inr (Or.inl same)
    · subst b
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have bufferFrame := foreign_buffer_frame_precompose privateFrame (storageE.trans storageU).shape outputView bufferBig
  have bytesA : Bytes after z.next_out produced written := by rw [nextOut] at bytes;exact bytes
  have account : StreamAccounting z z' 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountE accountA
  refine ⟨produced,after,z',result,written,remaining,kind,body,padding,?_,goodA,buffersA,account,
    (sizesE.trans sizesU).trans sizesA,storageReady.trans storageA,frameA,low,final,clearA,countA,
    frequencies,emptyCursor,phase.2.2,position,bytesA,pendingA,?_,kindBound,
    padBound,padNone,storedPad,outputA.trans outputE,grammar⟩
  · have streamRead : rd (some (.tab ds)) (·.strm) (setD ready ds updated) =
        .ok (some r,setD ready ds updated) := by
      simp only [rdD_eq,setD_dstates_same]
      rw [show updated.strm=some r from goodE.live.back]
    rw [flush_block_only_arguments_source,bind_app,arguments]
    simp only [bind_app,encodeRun,updateRun]
    change (rd (some (.tab ds)) (·.strm) >>= fun strm => flush_pending strm)
      (setD ready ds updated) = .ok ((),after)
    rw [bind_app,streamRead]
    exact flush
  · simpa only [pointer] using bufferFrame

end Zlib.Deflate.Engine.Proofs
