import ZlibF.Proof.«deflate.c.engine.caller-frame»
import ZlibF.Proof.«deflate.c.engine.fill-read-prefix»

/-! # Exact private storage effects of the refill heap operations -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem padded_storage_frame (h : Heap) (ds w : Nat) (d : DeflateState) (wa : Array UInt8)
    (changed : Nat → Prop) (stateWrite : changed ds) (windowWrite : changed w) :
    ByteFrame h (paddedHeap h ds w d wa) changed := by
  refine ⟨rfl, ?_, ?_, fun _ _ => rfl⟩
  · intro i outside
    have different : i ≠ w := by intro equal; subst i; exact outside windowWrite
    simp [paddedHeap, setD_bytes, upd_ne _ _ _ _ different]
  · intro i outside
    have different : i ≠ ds := by intro equal; subst i; exact outside stateWrite
    simp [paddedHeap, setD, upd_ne _ _ _ _ different]

theorem pending_read_storage_frame (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8)
    (changed : Nat → Prop) (stateWrite : changed ds) (windowWrite : changed w) :
    ByteFrame h (pendingReadHeap h r ds w z d ref io ia wa) changed := by
  refine ⟨by simp [pendingReadHeap], ?_, ?_, fun _ _ => by simp [pendingReadHeap]⟩
  · intro i outside
    have different : i ≠ w := by intro equal; subst i; exact outside windowWrite
    simp [pendingReadHeap, upd_ne _ _ _ _ different]
  · intro i outside
    have different : i ≠ ds := by intro equal; subst i; exact outside stateWrite
    simp [pendingReadHeap, setD, upd_ne _ _ _ _ different]

theorem slide_storage_frame (h : Heap) (ds w p q : Nat) (d : DeflateState) (wa : Array UInt8)
    (pa qa : Array UInt16) (changed : Nat → Prop) (stateWrite : changed ds) (windowWrite : changed w) :
    ByteFrame h (slideHeap h ds w p q d wa pa qa) changed := by
  refine ⟨rfl, ?_, ?_, fun _ _ => rfl⟩
  · intro i outside
    have different : i ≠ w := by intro equal; subst i; exact outside windowWrite
    simp [slideHeap, setW, upd_ne _ _ _ _ different]
  · intro i outside
    have different : i ≠ ds := by intro equal; subst i; exact outside stateWrite
    simp [slideHeap, setD, setW, upd_ne _ _ _ _ different]

end Zlib.Deflate.Engine.Proofs
