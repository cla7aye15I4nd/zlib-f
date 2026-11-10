import ZlibF.Proof.«compress.c.shadow-init-views»

/-! # Caller byte views across the initialization seed

The five BRef constructors are handled directly. Old records are retained
as values, not recursively renamed: only their depth view is accessed by
this byte interface. Unrelated embedded pointers are not followed.
-/
namespace ZlibF.Spec.Public.Proofs.CompressShadow
open C Zlib.Deflate.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def renameByteRef (cut : Nat) : BRef → BRef
  | .blk b => .blk (rename cut 0 b)
  | .dstate_depth b => .dstate_depth (rename cut 4 b)
  | other => other

theorem seed_old_view {h : Heap} {ref : BRef} {a : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some a) :
    Space.get (seedShadow h) (renameByteRef h.nextBlk ref) = some a ∧
      Space.ro (seedShadow h) (renameByteRef h.nextBlk ref) = Space.ro h ref := by
  cases ref with
  | blk b => exact seed_old_bytes fresh get
  | str i =>
    constructor
    · simpa only [Space.get,renameByteRef,staticStringBytes,seedShadow] using get
    · rfl
  | st_dist_code | st_length_code => exact ⟨get,rfl⟩
  | dstate_depth b =>
    cases state : h.dstates b with
    | none => simp [Space.get,state] at get
    | some d =>
      have old : b < h.nextBlk := fresh.lt (by simp [Heap.live,state])
      have shifted : (seedShadow h).dstates (rename h.nextBlk 4 b) = some d := by
        simp only [seedShadow,rename,old,ite_true]
        exact (spread_at h.dstates old (by decide)).trans state
      constructor
      · simpa only [Space.get,renameByteRef,shifted,state] using get
      · rfl

theorem seed_result_old_view {h : Heap} {ref : BRef} {a : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some a)
    (a1 a2 a3 : Array CtData) (qa : Array UInt16) :
    Space.get (seedResult h a1 a2 a3 qa) ref = some a ∧
      Space.ro (seedResult h a1 a2 a3 qa) ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have old : b < h.nextBlk := fresh.lt (by simp [Heap.live,show h.bytes b = some a from get])
    obtain ⟨bytes,_,_,_,_,_,_,ro⟩ := seed_result_old old a1 a2 a3 qa
    exact ⟨bytes.trans get,ro⟩
  | dstate_depth b =>
    cases state : h.dstates b with
    | none => simp [Space.get,state] at get
    | some d =>
      have old : b < h.nextBlk := fresh.lt (by simp [Heap.live,state])
      obtain ⟨_,_,_,_,kept,_,_,_⟩ := seed_result_old old a1 a2 a3 qa
      constructor
      · simpa only [Space.get,kept] using get
      · rfl
  | str i =>
    obtain ⟨_,_,_,_,_,_,borrow⟩ := seed_result_metadata h a1 a2 a3 qa
    constructor
    · simpa only [Space.get,staticStringBytes,borrow] using get
    · rfl
  | st_dist_code | st_length_code =>
    obtain ⟨_,_,_,_,same,_,_⟩ := seed_result_metadata h a1 a2 a3 qa
    constructor
    · simpa only [Space.get,same] using get
    · rfl

theorem initialized_caller_view_pair {h : Heap} {ref : BRef} {a : Array UInt8}
    (fresh : Fresh h) (get : Space.get h ref = some a)
    (a1 a2 a3 b1 b2 b3 : Array CtData) (qa qb : Array UInt16) :
    Space.get (seedResult h a1 a2 a3 qa) ref =
      Space.get (seedResult (seedShadow h) b1 b2 b3 qb) (renameByteRef h.nextBlk ref) ∧
    Space.ro (seedResult h a1 a2 a3 qa) ref =
      Space.ro (seedResult (seedShadow h) b1 b2 b3 qb) (renameByteRef h.nextBlk ref) := by
  have old := seed_old_view fresh get
  have original := seed_result_old_view fresh get a1 a2 a3 qa
  have shadow := seed_result_old_view (seed_fresh h) old.1 b1 b2 b3 qb
  exact ⟨original.1.trans shadow.1.symm,original.2.trans (shadow.2.trans old.2).symm⟩

#print axioms seed_old_view
#print axioms initialized_caller_view_pair
end ZlibF.Spec.Public.Proofs.CompressShadow
