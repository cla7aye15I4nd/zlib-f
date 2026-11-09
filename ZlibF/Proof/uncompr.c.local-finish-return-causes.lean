import ZlibF.Proof.«uncompr.c.local-finish»
import ZlibF.Proof.«uncompr.c.local-loop-return-causes»

namespace Zlib.Uncompr.Proof.LocalReturnCauses
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Writeback
set_option autoImplicit false

private def AllocMetaM {α : Type} (p : M α) : Prop :=
  ∀ h v after, p h = .ok (v, after) → after.nalloc = h.nalloc ∧ after.allocOk = h.allocOk

private theorem freeB_meta (p : BPtr) : AllocMetaM (freeB p) := by
  intro h value after run
  unfold freeB at run
  repeat' first | split at run | (cases run <;> exact ⟨rfl, rfl⟩)

private theorem freeZ_meta (p : ZStreamPtr) : AllocMetaM (freeZStream p) := by
  intro h value after run
  unfold freeZStream at run
  repeat' first | split at run | (cases run <;> exact ⟨rfl, rfl⟩)

private theorem freeLocals_meta (stream : ZStreamPtr) (reserved : BPtr) :
    AllocMetaM (freeLocals stream reserved) := by
  intro h value after run
  unfold freeLocals at run
  rw [bind_app] at run
  cases first : freeB reserved h with
  | error fault => rw [first] at run; cases run
  | ok pair =>
    obtain ⟨v, mid⟩ := pair
    rw [first] at run
    have before := freeB_meta reserved h v mid first
    have final := freeZ_meta stream mid value after run
    exact ⟨final.1.trans before.1, final.2.trans before.2⟩

private theorem store_meta {h after : Heap} {p : BPtr} {xs : List UInt8}
    (store : Store h p xs after) : after.nalloc = h.nalloc ∧ after.allocOk = h.allocOk := by
  rcases store with ⟨_, rfl⟩ | ⟨r, off, a, _, _, _, _, rfl⟩
  · exact ⟨rfl, rfl⟩
  · cases r with
    | dstate_depth i => cases value : h.dstates i <;> simp only [Space.put, value, and_self]
    | _ => exact ⟨rfl, rfl⟩

private theorem m_bind_assoc {α β γ : Type} (a : M α) (b : α → M β) (c : β → M γ) :
    ((a >>= b) >>= c) = (a >>= fun x => b x >>= c) := by
  funext h
  simp only [bind_app]
  cases first : a h with
  | error fault => rfl
  | ok pair => rcases pair with ⟨x, next⟩; rfl

/-- Actual ordered scalar stores, actual End and actual automatic frees
preserve the allocation event counter and oracle. The exact result map is
observed from that same returning tail, not supplied as a contract. -/
theorem finish_return_causes (h after : Heap) (cutoff b zs reserved : Nat) (z : ZStream) (s : InflateState)
    (sourceLen destLen : BPtr) (n capacity : UInt64) (l : UncLoop) (rc : Int32)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (inputRange : CallerRange h (.tab b) sourceLen 8 true)
    (outputRange : CallerRange h (.tab b) destLen 8 true) (separate : Separate sourceLen 8 destLen 8)
    (run : C.run (finish (some (.tab b)) (.ref (.blk reserved) 0) destLen sourceLen l) h = .ok (rc, after)) :
    rc = resultCode l.err (l.len + z.avail_in.toUInt64) ∧
    after.nalloc = h.nalloc ∧ after.allocOk = h.allocOk := by
  obtain ⟨mid, written, stores, current, finalAllocator, storeIn, storeOut, _⟩ :=
    LocalWriteback.ordered_length_writeback invariant allocator inputCell outputCell inputRange outputRange separate
      (l.len + z.avail_in.toUInt64) (l.left + z.avail_out.toUInt64)
  obtain ⟨clean, endRun, heapEq, _⟩ := inflateEnd_local current.good current.roots finalAllocator.2
  have ld : ldZ (some (.tab b)) h = .ok (z, h) := by
    simp [ldZ, ldZ_eq, show ZStreamRef.get h (.tab b) = some z from invariant.good.live.hz]
  let suffix : M Int32 := do
    (do store64 sourceLen ((← load64 sourceLen) - (l.len + z.avail_in.toUInt64))
        store64 destLen ((← load64 destLen) - (l.left + z.avail_out.toUInt64)))
    let _ ← inflateEnd (some (.tab b))
    freeLocals (some (.tab b)) (.ref (.blk reserved) 0)
    pure (resultCode l.err (l.len + z.avail_in.toUInt64))
  have seq : finish (some (.tab b)) (.ref (.blk reserved) 0) destLen sourceLen l h = suffix h := by
    unfold finish
    rw [bind_app, ld]
    dsimp only
    simp only [suffix, m_bind_assoc, resultCode]
  simp only [C.run] at run endRun
  rw [seq] at run
  change suffix h = .ok (rc, after) at run
  dsimp only [suffix] at run
  rw [bind_app, stores] at run
  dsimp only at run
  rw [bind_app, endRun] at run
  dsimp only at run
  rw [bind_app] at run
  cases cleanup : freeLocals (some (.tab b)) (.ref (.blk reserved) 0) clean with
  | error fault => rw [cleanup] at run; cases run
  | ok pair =>
    obtain ⟨value, finalHeap⟩ := pair
    rw [cleanup] at run
    have same := Except.ok.inj run
    have code : resultCode l.err (l.len + z.avail_in.toUInt64) = rc := congrArg Prod.fst same
    have heaps : finalHeap = after := congrArg Prod.snd same
    have freeMeta := freeLocals_meta _ _ clean value finalHeap cleanup
    have first := store_meta storeIn
    have second := store_meta storeOut
    have endMeta : clean.nalloc = written.nalloc ∧ clean.allocOk = written.allocOk := by
      rw [heapEq]
      simp only [ZStreamRef.put_nalloc, ZStreamRef.put_allocOk, endHeap, freeIst]
      unfold freeWin
      split <;> exact ⟨rfl, rfl⟩
    rw [heaps] at freeMeta
    exact ⟨code.symm, freeMeta.1.trans (endMeta.1.trans (second.1.trans first.1)),
      freeMeta.2.trans (endMeta.2.trans (second.2.trans first.2))⟩

#print axioms finish_return_causes
end Zlib.Uncompr.Proof.LocalReturnCauses
