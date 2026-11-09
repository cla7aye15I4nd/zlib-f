import ZlibF.Proof.«compress.c.local-literal»
import ZlibF.Proof.«deflate.c.engine.full-storage»

/-! # Actual match tally with local representation and exact symbol storage

The real inline tally packs three bytes, increments both frequencies and
returns its full flag. The input cursor has not advanced: the ledger grows,
and its block-balance credit decreases by the represented match length.
This leaf does not claim the subsequent match-consumption history.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalMatchTally
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHeader
open ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The actual packed-byte and state updates preserve the local private
representation without requiring uniqueness of old caller objects. -/
theorem local_match_after {h : Heap} {r : ZStreamRef} {cutoff ds b : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} (good : LocalState h cutoff r ds z d)
    (trees : TreesInvAt h ds d b buf) (distance length : UInt32) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    LocalState (setD (Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d distance.toUInt16 length.toUInt8)) ds (matchSymbolState d distance length))
      cutoff r ds z (matchSymbolState d distance length) := by
  have treeResult := tally_match_trees trees distance length room
  let hb := Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d distance.toUInt16 length.toUInt8)
  let dt := matchSymbolState d distance length
  have goodB : LocalState hb cutoff r ds z d := local_state_bytes_set good b (matchBytes buf d distance.toUInt16 length.toUInt8) buf trees.base.bytes
    (by simp [matchBytes])
  have inv : DStInv hb ds dt :=
    { goodB.inv with
      wf := treeResult.base.wf
      blocks := goodB.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sym := ⟨goodB.inv.sym.1, goodB.inv.sym.2.1, treeResult.run.sym_next_le, treeResult.run.sym_next_mod⟩ }
  have shape := shape_setD goodB.live.hs dt
  refine ⟨?_, DStInv.congr (h := hb) (h' := setD hb ds dt) rfl rfl rfl rfl inv,
    goodB.newUnique.shape shape, shape.fresh rfl goodB.fresh, ⟨dt, b, matchBytes buf d distance.toUInt16 length.toUInt8, treeResult⟩⟩
  exact ⟨by simpa only [ZStreamRef.get_setD] using goodB.live.hz, by simp, good.live.zst,
    good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩

/-- The translated tally itself has an exact canonical result heap,
updated symbol ledger and complete typed footprint. Both full and nonfull
flags are covered. Match consumption remains the caller's next step. -/
theorem local_tally_match_storage {h : Heap} {r : ZStreamRef} {cutoff ds b : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : LocalState h cutoff r ds z d) (trees : TreesInvAt h ds d b buf)
    (ledger : SymbolLedger buf d xs) (distance length : UInt32)
    (positive : 1 ≤ distance.toNat) (distanceBound : distance.toNat ≤ 32768)
    (lengthBound : length.toNat ≤ 255) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    let packed := matchBytes buf d distance.toUInt16 length.toUInt8
    let result := matchSymbolState d distance length
    let after := setD (Zlib.Trees.Proofs.Out.setB h b packed) ds result
    tally_dist (some (.tab ds)) distance length h = .ok (d.sym_next + 3 == d.sym_end, after) ∧
      LocalState after cutoff r ds z result ∧ TreesInvAt after ds result b packed ∧
      SymbolLedger packed result (xs ++ [⟨distance.toNat,length.toNat⟩]) ∧
      result.sym_next.toNat = d.sym_next.toNat + 3 ∧
      ((d.sym_next + 3 == d.sym_end) = false → result.sym_next.toNat < result.sym_end.toNat) ∧
      SlowRecordFrame d result ∧ Shape h after ∧ Frame h after (fun key => key = ds ∨ key = b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      (∀ top, HeapChains h d top → HeapChains after result top) ∧
      (∀ credit, BlockBalance d xs credit →
        BlockBalance result (xs ++ [⟨distance.toNat,length.toNat⟩])
          (credit - (length.toNat + 3 : Nat))) := by
  let packed := matchBytes buf d distance.toUInt16 length.toUInt8
  let result := matchSymbolState d distance length
  let bytesHeap := Zlib.Trees.Proofs.Out.setB h b packed
  let after := setD bytesHeap ds result
  have stored := tally_match_ledger trees.base ledger room distance length positive distanceBound (by omega : length.toNat < 256)
  have shapeB : Shape h bytesHeap := shape_setB trees.base.bytes packed
  have shape := shapeB.trans (shape_setD (h := bytesHeap) (by simpa [bytesHeap] using good.live.hs) result)
  have frameB : Frame h bytesHeap (fun key => key = ds ∨ key = b) :=
    full_frame_weaken (byte_store_full_frame h b packed) (fun _ same => Or.inr same)
  have frameD : Frame bytesHeap after (fun key => key = ds ∨ key = b) :=
    full_frame_weaken (state_store_full_frame bytesHeap ds result) (fun _ same => Or.inl same)
  refine ⟨stored.1, local_match_after good trees distance length room,
    tally_match_trees trees distance length room, stored.2, literal_count trees.base room 0,
    (fun flag => literal_not_full trees 0 room flag), rfl, shape,
    full_frame_trans_shape frameB frameD shapeB, full_shape_live_change shape, rfl, rfl, ?_, ?_⟩
  · intro top chains
    obtain ⟨w,p,q,wa,pa,qa,win,prev,head,hw,hp,hq,H⟩ :=
      local_pending_write_chains good chains trees.base.pbuf packed 0
    exact ⟨w,p,q,wa,pa,qa,win,prev,head,hw,hp,hq,H⟩
  · intro credit balance
    exact balance_match balance distance length positive

end ZlibF.Spec.Public.Proofs.CompressLocalMatchTally
