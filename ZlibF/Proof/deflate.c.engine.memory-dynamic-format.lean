import ZlibF.Proof.«deflate.c.engine.memory-dynamic-prepared»
import ZlibF.Proof.«deflate.c.engine.dynamic-format»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sourceWords sourceLens SourceCodeFacts PreparedHeaderData dynamicHeaderBits dynamicTag)
open Zlib.Trees.Proofs.Out (TreesInvAt payloadSymBits codeBits SymbolDecodeData)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual memory-aware dynamic output decodes through the independent
format grammar to exactly the symbols' logical input trace. -/
theorem memory_dynamic_prepared_payload_format {memory : Nat} {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (capacity : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 5 ≤ memory) (memoryHigh : memory ≤ 9)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs) (last : Bool) :
    ∃ after result next body,
      dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ next.size = buf.size ∧
      result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * result.pending_buf_size.toNat ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++ (dynamicTag last ++ body) ∧
      ∀ suffix, ZlibF.Spec.Body [] 2 (inputPrefix input base) (body ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨mb, ready, after, result, next, run, goodA, treesA, buffersA, sizes, storage,
    _fields, codes, data, _codesA, sizeA, cursorA, roomA, output⟩ :=
    memory_dynamic_prepared_payload_engine (ob := ob) good trees buffers cursor capacity memoryLow memoryHigh pending bits ledger clear last
  let body := dynamicHeaderBits ready mb ++
    (xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist) (s.distance, s.value)) ++
      codeBits (sourceWords ready .lit) 256)
  refine ⟨after, result, next, body, run, goodA, treesA, buffersA, sizes, storage,
    sizeA, cursorA, roomA, ?_, ?_⟩
  · simpa only [body, List.append_assoc] using output
  · intro suffix
    exact dynamic_prepared_body ledger codes data trace suffix

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_dynamic_prepared_payload_format
