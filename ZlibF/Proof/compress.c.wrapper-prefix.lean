import ZlibF.Proof.«compress.c.init-seed»
import ZlibF.Proof.«compress.c.finite-prefix»

/-! # Real wrapper initialization and returning loop executions share one input

This is the explicitly internal default/Uniq/raw-output milestone. It
states conditional correctness of actual successful executions, not
termination, capacity adequacy or the unchanged full public API goal.
-/
namespace ZlibF.Spec.Public.Proofs.CompressPrefix
open C Zlib.Compress Zlib.Deflate
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
set_option autoImplicit false

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
Original caller buffers, the actual local-stream initializer and actual
setup establish the real loop's domain. Any actual returning END from that
same loop yields independently valid bytes for the full original source.
Only the internal Uniq/raw-output scope is claimed. Init failure, final
pointer subtraction/end cleanup, bound and total completion remain separate. -/
theorem original_buffers_returning_loop {h initialized : Heap} {dest source : BPtr}
    {ob oo : Nat} {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Zlib.Inflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized)) :
    ∃ ready, C.run (zwr (some (.tab h.nextBlk)) (fun s => bindings s dest source)) initialized =
        .ok ((), ready) ∧
      ∀ after finalLeft finalSourceLen,
        loop (some (.tab h.nextBlk)) (Z_OK, capacity, sourceLen) ready =
          .ok ((Z_STREAM_END, finalLeft, finalSourceLen), after) →
        ∃ output, Bytes after dest output.length output ∧ ZlibF.Spec.Zlib.Valid xs output := by
  obtain ⟨ready, z, setup, history, get, ranges, out, _in, _outAvail, _inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  refine ⟨ready, setup, ?_⟩
  intro after finalLeft finalSourceLen actualLoop
  have outputPointer : z.next_out = .ref (.blk ob) oo := out.trans pointer
  obtain ⟨output, actualBytes, valid⟩ := actual_loop_end_encoding history get ranges outputPointer actualLoop
  exact ⟨output, by simpa only [out] using actualBytes, valid⟩

end ZlibF.Spec.Public.Proofs.CompressPrefix
