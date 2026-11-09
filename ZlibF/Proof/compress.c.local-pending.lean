import ZlibF.Proof.«compress.c.local-initialization»
import ZlibF.Proof.«deflate.c.engine.pending-resume»

/-! # Actual pending publication with local private representation

The concrete copy changes the selected output byte interval, the live
stream record and its private state. Old typed-table collisions need no
global uniqueness premise. All lookup effects follow from the same heap.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalPending
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocal
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem local_bytes {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff r ds z d) (x : Nat) (a a0 : Array UInt8)
    (get : h.bytes x = some a0) (size : a.size = a0.size) :
    LocalState {h with bytes := upd h.bytes x (some a)} cutoff r ds z d := by
  have shape := shape_setB get a
  refine ⟨⟨?_,state.live.hs,state.live.zst,state.live.back,state.live.status,
    state.live.zalloc,state.live.zfree⟩,state.inv.bytes_set x a a0 get size (fun _ _ => rfl),
    state.newUnique.shape shape,shape.fresh rfl state.fresh,TreesInv.bytes_set state.trees x a a0 get size⟩
  cases r <;> simpa [ZStreamRef.get] using state.live.hz

private theorem local_setZD {h : Heap} {cutoff ds : Nat} {r : ZStreamRef} {z nextZ : ZStream}
    {d nextD : DeflateState} (state : LocalState h cutoff r ds z d)
    (pointer : nextZ.state = z.state) (alloc : nextZ.zalloc ≠ .null) (free : nextZ.zfree ≠ .null)
    (back : nextD.strm = d.strm) (status : GoodStatus nextD.status)
    (inv : DStInv h ds nextD) (keep : TrKeep d nextD) :
    LocalState (setD (r.put h nextZ) ds nextD) cutoff r ds nextZ nextD := by
  have shape := (shape_put state.live.hz nextZ).trans (shape_setD (by simpa using state.live.hs) nextD)
  refine ⟨⟨?_,by simp,pointer.trans state.live.zst,back.trans state.live.back,status,alloc,free⟩,
    inv.congr (by simp) (by simp) (by simp) (by simp),state.newUnique.shape shape,
    shape.fresh (by simp) state.fresh,?_⟩
  · simp [ZStreamRef.get_put,state.live.hz]
  · exact TreesInv.keep (d := d) state.trees state.live.hs (by simp) (by simp) (by simp)
      (by simp) inv.wf keep inv.pending_le

/-- The real copy heap preserves the local private invariant. Only new
identities retain local uniqueness; old typed slots may collide. -/
theorem local_pending_copy_state {h : Heap} {r : ZStreamRef} {cutoff ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8}
    (state : LocalState h cutoff r ds z d) (buffer : d.pending_buf = .ref (.blk pb) 0)
    (cursor : d.pending_out = .ref (.blk pb) po) (outGet : h.bytes ob = some output) :
    let n := pendingLen d.pending z.avail_out
    LocalState (pendingCopyHeap h r ds pb po ob oo z d pending output n) cutoff r ds
      (pendingStream z (.ref (.blk ob) (oo+n.toNat)) n)
      (pendingState d (.ref (.blk pb) (po+n.toNat)) n) := by
  let n := pendingLen d.pending z.avail_out
  let copied := {h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat))}
  let result := pendingState d (.ref (.blk pb) (po+n.toNat)) n
  have localC : LocalState copied cutoff r ds z d :=
    local_bytes state ob _ output outGet (size_copyRange _ _ _ _ _)
  obtain ⟨w,p,q,b,blocks⟩ := localC.inv.blocks
  have bid : b = pb := by simpa only [buffer,Ptr.ref.injEq,BRef.blk.injEq,and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨off,oldPtr,bound⟩ := blocks.pout
  have same : off = po := by simpa only [cursor,Ptr.ref.injEq,true_and] using oldPtr.symm
  subst off
  have count := (pending_copy_counts d.pending z.avail_out).1
  have blocksA : DBlocks copied result w p q pb := by
    refine {blocks with pout := ?_}
    unfold result pendingState
    by_cases empty : (d.pending-n.toUInt64 == 0) = true
    · refine ⟨0,by simp only [empty,ite_true,buffer],?_⟩
      change 0+(d.pending-n.toUInt64).toNat ≤ d.pending_buf_size.toNat
      dsimp only [n] at *
      omega
    · refine ⟨po+n.toNat,by simp [empty],?_⟩
      change po+n.toNat+(d.pending-n.toUInt64).toNat ≤ d.pending_buf_size.toNat
      dsimp only [n] at *
      omega
  have inv : DStInv copied ds result := {localC.inv with blocks := ⟨w,p,q,pb,blocksA⟩}
  exact local_setZD localC rfl state.live.zalloc state.live.zfree rfl state.live.status inv (by trkeep)

/-- Per-table effects of the concrete publication heap. The frame also
holds at old identities occupied in more than one typed table. -/
theorem local_pending_copy_effects {h : Heap} {r : ZStreamRef} {ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8} (n : UInt32)
    (live : DLive h r ds z d) (outGet : h.bytes ob = some output) :
    let after := pendingCopyHeap h r ds pb po ob oo z d pending output n
    Shape h after ∧ after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = ob) ∧
      after.words = h.words ∧ after.gzheaders = h.gzheaders ∧ after.istates = h.istates ∧
      after.ro = h.ro ∧ after.bytes ob = some (copyRange output pending oo po n.toNat) ∧
      (∀ b, b ≠ ob → after.bytes b = h.bytes b) ∧
      (∀ b, b ≠ ds → after.dstates b = h.dstates b) ∧
      (∀ b, ¬StreamRoot r b → after.streams b = h.streams b ∧ after.gzstates b = h.gzstates b) := by
  let copied := {h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat))}
  let stream := pendingStream z (.ref (.blk ob) (oo+n.toNat)) n
  let result := pendingState d (.ref (.blk pb) (po+n.toNat)) n
  have getC : r.get copied = some z := by simpa only [copied,stream_get_bytes] using live.hz
  have shape := ((shape_setB outGet (copyRange output pending oo po n.toNat)).trans
    (shape_put getC stream)).trans (shape_setD (by simpa using live.hs) result)
  refine ⟨shape,by simp [pendingCopyHeap],by simp [pendingCopyHeap],?_,
    by simp [pendingCopyHeap],by simp [pendingCopyHeap],by simp [pendingCopyHeap],
    by simp [pendingCopyHeap],by simp [pendingCopyHeap],?_,?_,?_⟩
  · refine ⟨by simp [pendingCopyHeap],by simp [pendingCopyHeap],by simp [pendingCopyHeap],
      by simp [pendingCopyHeap],by simp [pendingCopyHeap],?_⟩
    intro b _ outside
    have root : ¬StreamRoot r b := fun same => outside (Or.inl same)
    have state : b ≠ ds := fun same => outside (Or.inr (Or.inl same))
    have byte : b ≠ ob := fun same => outside (Or.inr (Or.inr same))
    have before : SlotSame h copied b := by simp [SlotSame,copied,upd_ne _ _ _ _ byte]
    exact before.trans ((slot_put_except copied r stream b root).trans
      (slot_setD_except (r.put copied stream) ds result b state))
  · intro b different
    simp [pendingCopyHeap,upd_ne _ _ _ _ different]
  · intro b different
    simp [pendingCopyHeap,setD,upd_ne _ _ _ _ different]
  · intro b outside
    have slot := slot_put_except copied r stream b outside
    exact ⟨slot.2.2.1,slot.2.2.2.2.2.2.1⟩

/-- At every old caller identity, all six non-byte typed tables remain
pointwise equal, even if that identity occupied several tables initially.
The fresh stream/state identities alone need to lie above the cutoff. -/
theorem local_pending_old_typed {h : Heap} {r : ZStreamRef} {cutoff ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8} (n : UInt32)
    (live : DLive h r ds z d) (outGet : h.bytes ob = some output)
    (stateNew : cutoff ≤ ds) (streamNew : ∀ b, StreamRoot r b → cutoff ≤ b) :
    let after := pendingCopyHeap h r ds pb po ob oo z d pending output n
    (∀ b, after.live b ↔ h.live b) ∧
      ∀ b, b < cutoff →
        after.words b = h.words b ∧ after.streams b = h.streams b ∧
        after.gzheaders b = h.gzheaders b ∧ after.dstates b = h.dstates b ∧
        after.istates b = h.istates b ∧ after.gzstates b = h.gzstates b ∧ after.ro b = h.ro b ∧
        (b ≠ ob → after.bytes b = h.bytes b) := by
  obtain ⟨shape,_,_,_,words,headers,istates,ro,_,bytes,states,streams⟩ :=
    local_pending_copy_effects n live outGet
  refine ⟨shape.live,?_⟩
  intro b old
  have notState : b ≠ ds := by omega
  have notStream : ¬StreamRoot r b := fun root => by have bound := streamNew b root;omega
  obtain ⟨stream,gzstate⟩ := streams b notStream
  exact ⟨(by rw [words]),stream,(by rw [headers]),states b notState,
    (by rw [istates]),gzstate,(by rw [ro]),bytes b⟩

/-- The actual low-bit flush copies precisely its selected interval and
retains the local invariant, exact scalar accounting and typed-table frame.
No DGood or global uniqueness premise is used. The positive-copy condition
is explicit; the zero-selected branch is the unchanged actual heap. -/
theorem local_flush_pending_raw {h : Heap} {r : ZStreamRef} {cutoff ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8}
    (state : LocalState h cutoff r ds z d) (bits : d.bi_valid.toInt < 8)
    (buffer : d.pending_buf = .ref (.blk pb) 0) (cursor : d.pending_out = .ref (.blk pb) po)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (outGet : h.bytes ob = some output) (pendingGet : h.bytes pb = some pending)
    (writable : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo+z.avail_out.toNat ≤ output.size) (pendingBound : po+d.pending.toNat ≤ pending.size)
    (nonzero : pendingLen d.pending z.avail_out ≠ 0) :
    let n := pendingLen d.pending z.avail_out
    let after := pendingCopyHeap h r ds pb po ob oo z d pending output n
    let result := pendingState d (.ref (.blk pb) (po+n.toNat)) n
    let nextZ := pendingStream z (.ref (.blk ob) (oo+n.toNat)) n
    flush_pending (some r) h = .ok ((),after) ∧ LocalState after cutoff r ds nextZ result ∧
      StreamAccounting z nextZ 0 n.toNat ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = ob) ∧ Shape h after ∧
      (∀ i, (copyRange output pending oo po n.toNat)[i]? =
        if oo ≤ i ∧ i < oo+n.toNat then some pending[po+(i-oo)]! else output[i]?) ∧
      ∃ written remaining, Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
        ZlibF.Spec.bytesToBits written ++ remaining =
          ZlibF.Spec.bytesToBits ((pending.toList.drop po).take d.pending.toNat) ++
            Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat := by
  have count := pendingLen_value d.pending z.avail_out
  obtain ⟨shape,_,_,frame,_⟩ := local_pending_copy_effects (pendingLen d.pending z.avail_out) state.live outGet
  refine ⟨flush_pending_low_raw state.live.hz state.live.zst state.live.hs bits pointer cursor
    outGet pendingGet writable separate outBound pendingBound nonzero,
    local_pending_copy_state state buffer cursor outGet,pending_copy_accounting pointer,frame,shape,?_,?_⟩
  · intro i
    exact getElem?_copyRange _ _ _ _ _ _ (by omega)
  · exact pending_copy_cursor_bits buffer cursor pendingGet pendingBound
      (pending_bits_slice cursor pendingGet pendingBound) pointer separate outBound

/-- With zero selected bytes the real flush does not touch any table. -/
theorem local_flush_pending_zero {h : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z : ZStream} {d : DeflateState} (state : LocalState h cutoff r ds z d)
    (bits : d.bi_valid.toInt < 8) (zero : pendingLen d.pending z.avail_out = 0) :
    flush_pending (some r) h = .ok ((),h) ∧ LocalState h cutoff r ds z d :=
  ⟨flush_pending_low_zero state.live.hz state.live.zst state.live.hs bits zero,state⟩

end ZlibF.Spec.Public.Proofs.CompressLocalPending
