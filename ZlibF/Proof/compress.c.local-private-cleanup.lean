import ZlibF.Proof.«compress.c.local-client-resources»

/-! # Actual cleanup using only the newly allocated private identities -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalPrivateCleanup
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocal ZlibF.Spec.Public.Proofs.CompressLocalInit
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The four retained addresses describe exactly the five private engine
objects. Old caller occupancy is unrestricted. -/
theorem private_owned_iff {cutoff : Nat} {d : DeflateState}
    (window : d.window = .ref (.blk (cutoff+2)) 0)
    (prev : d.prev = .ref (.blk (cutoff+3)) 0)
    (head : d.head = .ref (.blk (cutoff+4)) 0)
    (pending : d.pending_buf = .ref (.blk (cutoff+5)) 0) (x : Nat) :
    DOwned d (cutoff+1) x ↔ cutoff+1 ≤ x ∧ x < cutoff+6 := by
  simp only [DOwned,window,prev,head,pending,Ptr.ref.injEq,BRef.blk.injEq,WRef.blk.injEq,and_true]
  constructor
  · intro owned
    rcases owned with rfl | ⟨w,rfl,rfl⟩ | ⟨p,rfl,rfl⟩ | ⟨q,rfl,rfl⟩ | ⟨b,rfl,rfl⟩ <;> omega
  · intro inside
    have cases : x = cutoff+1 ∨ x = cutoff+2 ∨ x = cutoff+3 ∨ x = cutoff+4 ∨ x = cutoff+5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨cutoff+2,rfl,rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨cutoff+3,rfl,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cutoff+4,rfl,rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨cutoff+5,rfl,rfl⟩)))

/-- Real End and automatic-stream release need uniqueness only at the six
actual private identities. The local representation supplies it; caller
cross-table collisions do not become a new precondition. -/
theorem private_cleanup {h : Heap} {cutoff : Nat} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff (.tab cutoff) (cutoff+1) z d)
    (allocator : z.zfree = .fn "zcfree")
    (window : d.window = .ref (.blk (cutoff+2)) 0)
    (prev : d.prev = .ref (.blk (cutoff+3)) 0)
    (head : d.head = .ref (.blk (cutoff+4)) 0)
    (pending : d.pending_buf = .ref (.blk (cutoff+5)) 0) :
    let after := ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal
      (endHeap h (.tab cutoff) (cutoff+1) z d) cutoff
    C.run (do let rc ← deflateEnd (some (.tab cutoff));freeZStream (some (.tab cutoff));pure rc) h =
      .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),after) ∧
      LiveChange h after (fun _ => False) (fun x => cutoff ≤ x ∧ x < cutoff+6) ∧
      Frame h after (fun x => cutoff ≤ x ∧ x < cutoff+6) ∧ Fresh after ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨w,p,q,b,blocks⟩ := state.inv.blocks
  have owned := private_owned_iff window prev head pending
  have unique : ∀ x, DOwned d (cutoff+1) x → UniqueAt h x := by
    intro x member
    exact state.newUnique x (by have low := ((owned x).mp member).1;omega)
  obtain ⟨run,ledger,fresh⟩ := real_cleanup_local state.live allocator blocks
    (state.newUnique cutoff (Nat.le_refl _)) unique state.fresh
  have frame := cleanup_local_frame (ds := cutoff+1) state.live.hz blocks
  have regions : ∀ x, DOwned d (cutoff+1) x ∨ x = cutoff ↔ cutoff ≤ x ∧ x < cutoff+6 := by
    intro x
    rw [owned x]
    omega
  have frame' := full_frame_weaken frame (fun x member => (regions x).mp member)
  refine ⟨run,?_,frame',fresh,?_,?_⟩
  · intro x
    simpa only [LiveChange,regions x] using ledger x
  · rw [endHeap_eq blocks]
    simp [ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal]
  · rw [endHeap_eq blocks]
    simp [ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal]

end ZlibF.Spec.Public.Proofs.CompressLocalPrivateCleanup
