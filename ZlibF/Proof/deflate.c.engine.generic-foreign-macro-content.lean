import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-arrays»
import ZlibF.Proof.«deflate.c.engine.flush-end-frontier»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real default-memory foreign-output macro restores the exact content and EOF
frontier while preserving its independently generated wire and block-body grammar. -/
theorem default_foreign_flush_macro_content_encoding {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (last : Bool) :
    ∃ produced after z' result before written remaining kind body padding,
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame {d with block_start := d.strstart.toUInt64.toInt64} result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ padding.length < 8 ∧ (last = false → padding = []) ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits (if last then 1 else 0) 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have account0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨produced,after,z',result,written,remaining,kind,body,padding,
      run,goodA,buffersA,accountA,sizesA,storageA,frame,lowA,_final,clearA,count,frequenciesA,
      cursorA,phaseA,positionA,bytesA,pendingA,_bufferFrame,kindA,padBound,padNone,storedPad,outputA,grammarA⟩ :=
    default_flush_block_only_foreign_publish boundary.good trees buffers positive pointer cursor memory
      pending bits ledger clear boundary.trace win get boundary.range balance0 account0 view last
  have startA : result.strstart = d.strstart := by rw [frame]
  have insertA : result.insert = d.insert := by rw [frame]
  have availableA : result.match_available = 0 := by rw [frame]; exact available
  obtain ⟨stateA, blockA, bufA, treesA⟩ := goodA.trees
  have resultEq : stateA = result := Option.some.inj (treesA.base.dstate.symm.trans goodA.live.hs)
  subst stateA
  have emptyLedger : SymbolLedger bufA result [] := empty_symbol_ledger count frequenciesA
  have cast : result.strstart.toUInt64.toInt64.toInt = (result.strstart.toNat : Int) := by
    have bound := result.strstart.toNat_lt
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp; omega
  have balanceA : BlockBalance result [] (deferredCredit result) := by
    simp only [BlockBalance, positionA, cast, represented, deferredCredit, availableA, ite_true]
    omega
  have chainsA := foreign_flush_frames_chains storageA boundary.good buffers pointer trees.base.pbuf frame boundary.chains
  have frontierA := foreign_flush_frames_chains storageA boundary.good buffers pointer trees.base.pbuf frame boundary.frontier
  obtain ⟨wc, p, q, wa, pa, qa, winC, prev, head, getC, getPrev, getHead, _chainC⟩ := boundary.chains
  have windowEq : wc = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using winC.symm
  subst wc
  have arrayEq : wa = window := Option.some.inj (getC.symm.trans get)
  subst wa
  have kept := storageA.foreign_private_arrays boundary.good buffers pointer win get prev getPrev head getHead trees.base.pbuf
  have contentA : ContentBoundary after r ds z' result input origin (base + represented xs) [] := by
    refine ⟨⟨⟨goodA, ?_, ?_, ?_, ?_, ⟨blockA, bufA, treesA, emptyLedger, balanceA⟩, ?_⟩,
      ?_, ?_, ?_⟩, Trace.empty, ?_⟩
    · simpa only [startA] using chainsA
    · rw [frame]; exact boundary.range
    · rw [frame]; exact boundary.history
    · rw [frame]; exact boundary.deferred
    · refine ⟨w, window, ?_, kept.1, ?_, ?_⟩
      · rw [frame]; exact win
      · rw [frame]; exact view
      · rw [frame]; exact form
    · rw [startA, insertA]; exact boundary.insert_le
    · simpa only [startA, insertA] using frontierA
    · rw [frame]; exact boundary.ready
    · simpa only [represented, pendingCredit, availableA, ite_true, Nat.add_zero, startA] using account0
  have keptEnd := foreign_flush_frames_chains storageA boundary.good buffers pointer trees.base.pbuf frame frontier
  have endpoint : fillEnd result = fillEnd d := by rw [frame]; rfl
  have endA : EndFrontier after result := by
    unfold EndFrontier
    simpa only [startA, endpoint] using keptEnd
  exact ⟨produced, after, z', result, Zlib.Trees.Proofs.Out.outBits buf d, written, remaining, kind, body, padding,
    run, contentA, endA, buffersA, accountA, clearA, frame, lowA, phaseA, cursorA,
    pending_bits_base trees cursor, bytesA, pendingA, kindA, padBound, padNone, storedPad, outputA, grammarA⟩

end Zlib.Deflate.Engine.Proofs
