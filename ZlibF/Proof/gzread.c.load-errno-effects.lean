import ZlibF.Proof.«gzread.c.load-errno»

/-!
# gzread.c: complete first-read error OS and message observations

These are final observations of the same whole gz_load execution, rather than
prefix frames. The handler's malloc-block accounting remains a separate proof.
-/
namespace Zlib.Gzread.LoadErrno
open C C.LibcBorrow Zlib.Gzguts Zlib.GzFs Zlib.Gzlib Zlib.Gzread
open Zlib.Gzlib.Spec Zlib.Gzlib.Proofs Zlib.Gzlib.ErrnoLifetime

/-- The actual read-refusal world changes errno and the OS-call counter alone. No successful whole
caller execution can close, replace or move the supplied file descriptor here. -/
theorem gz_load_refusal_world (h after : Heap) (fs fs' : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (len : UInt32) (e rc : Int32) (got : UInt32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a) (hb : off ≤ a.size)
    (hc : fs.readChoice fs.nos = .regular) (he : ReadRefusal s.fd fs e)
    (run : gz_load (some (.tab i)) (.ref r off) len fs h = .ok (((rc, got), fs'), after)) :
    fs'.errno = e ∧ fs'.fds = fs.fds ∧ fs'.nodes = fs.nodes ∧
      fs'.names = fs.names ∧ fs'.fsizeLimit = fs.fsizeLimit ∧
      (ZlibF.Spec.Public.FileSystem fs → ZlibF.Spec.Public.FileSystem fs') := by
  have hf := (gz_load_refusal_handler_run h after fs fs' i s r off a len e rc got hs ha hb hc he run).2.2.1
  subst fs'
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun good => good⟩

/-- The final message pointer of the whole real caller is NULL or a malloc
root on every returning handler outcome. No borrowed .str pointer escapes. -/
theorem gz_load_refusal_message_owned (h after : Heap) (fs fs' : Fs) (i : Nat) (s : GzState)
    (r : BRef) (off : Nat) (a : Array UInt8) (len : UInt32) (e rc : Int32) (got : UInt32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a) (hb : off ≤ a.size)
    (hc : fs.readChoice fs.nos = .regular) (he : ReadRefusal s.fd fs e)
    (run : gz_load (some (.tab i)) (.ref r off) len fs h = .ok (((rc, got), fs'), after)) :
    MessageShape i after := by
  obtain ⟨_, _, _, v, handler⟩ :=
    gz_load_refusal_handler_run h after fs fs' i s r off a len e rc got hs ha hb hc he run
  exact gz_error_message_noescape i Z_ERRNO _ _ after v handler

/-- After the next actual strerror call, the owned error message is still the
same block/NULL pointer and its byte view is unchanged. Only the old external
borrow expires; this is not a claim about the handler's allocation ledger. -/
theorem gz_load_refusal_message_survives_next (h after : Heap) (fs fs' nextFs : Fs)
    (i : Nat) (s final : GzState) (r : BRef) (off : Nat) (a : Array UInt8)
    (len : UInt32) (e rc : Int32) (got : UInt32)
    (hs : h.gzstates i = some s) (ha : Space.get h r = some a) (hb : off ≤ a.size)
    (hc : fs.readChoice fs.nos = .regular) (he : ReadRefusal s.fd fs e)
    (run : gz_load (some (.tab i)) (.ref r off) len fs h = .ok (((rc, got), fs'), after))
    (hf : after.gzstates i = some final) :
    let next := errnoHeap after nextFs
    zstrerror nextFs after = .ok ((errnoPointer after nextFs, nextFs), next) ∧
    next.gzstates i = some final ∧
    (match final.msg with
     | .null => True
     | .ref ref _ => Space.get next ref = Space.get after ref) ∧
    Space.get next (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) e)) = none := by
  dsimp only
  have hmsg := gz_load_refusal_message_owned h after fs fs' i s r off a len e rc got hs ha hb hc he run final hf
  have invalid := (gz_load_refusal_lifetime h after fs fs' i s r off a len e rc got hs ha hb hc he run).2.2.2.2.2.2 nextFs
  refine ⟨Zlib.GzFs.Proofs.zstrerror_run after nextFs, hf, ?_, invalid⟩
  rcases hmsg with hm | ⟨b, hm⟩
  · simp [hm]
  · simp [hm, errnoHeap]

#print axioms gz_load_refusal_world
#print axioms gz_load_refusal_message_owned
#print axioms gz_load_refusal_message_survives_next
end Zlib.Gzread.LoadErrno
