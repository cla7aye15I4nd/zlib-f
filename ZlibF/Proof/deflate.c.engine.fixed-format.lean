import ZlibF.Proof.«deflate.c.engine.fixed-payload»
import ZlibF.Math.DeflateFixedPayload

/-! # Actual fixed payload publication refines the independent block body -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`
followed by actual flush_pending. A real packed-symbol ledger and its
logical input trace produce a payload accepted by the independent fixed
Body grammar on every trailing suffix. It reproduces the exact logical
input prefix, including overlapping matches. Arbitrary raw output
capacity is included; retained PendingBits account for unwritten output.
This default-memory internal result has drained entry pending and at
most ten buffered bits. Block selection, the tag, padding and trailers
must still be composed in the unchanged public deflate target. -/
theorem fixed_payload_publish_format {h : Heap} {r : ZStreamRef} {ds pb ob oo base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (ledger : SymbolLedger buf d xs) (trace : Trace input base xs) :
    ∃ produced after z' result written remaining payload,
      (do Zlib.Trees.compress_block (some (.tab ds)) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++ payload ∧
      ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨produced, after, z', result, written, remaining, run, goodA, buffersA, account,
    sizes, storage, low, bytes, pendingA, output⟩ :=
    fixed_payload_ledger_publish good trees buffers pointer cursor memory pending bits ledger
  refine ⟨produced, after, z', result, written, remaining, _, run, goodA, buffersA,
    account, sizes, storage, low, bytes, pendingA, output, ?_⟩
  intro suffix
  exact ZlibF.Spec.Body.fixed (Zlib.Trees.Proofs.Out.fixed_payload_grammar trace suffix)

end Zlib.Deflate.Engine.Proofs
