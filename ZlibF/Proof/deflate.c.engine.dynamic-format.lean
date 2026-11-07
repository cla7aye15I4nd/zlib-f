import ZlibF.Proof.«deflate.c.engine.dynamic-prepared-payload»
import ZlibF.Math.DeflateDynamicPayload

/-! # Actual constructed dynamic payload and header refine the independent format -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sourceWords sourceLens SourceCodeFacts PreparedHeaderData dynamicHeaderBits dynamicTag)
open Zlib.Trees.Proofs.Out (TreesInvAt payloadSymBits codeBits SymbolDecodeData)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The original used-symbol histogram selects the independently decodable
stored words from actual constructor execution, including END_BLOCK. -/
theorem source_symbol_decode_data {original d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (ledger : SymbolLedger buf original xs) (codes : SourceCodeFacts original d) :
    SymbolDecodeData (sourceWords d .lit) (sourceWords d .dist) (sourceLens d .lit) (sourceLens d .dist) xs := by
  constructor
  · intro s member suffix
    exact codes.literal_decode _ (valid_literal_key (ledger.valid s member)) (ledger.literal_used member) suffix
  · intro s member nonzero suffix
    have selected : s.distanceKey Zlib.Trees.Proofs.Out.dcodeN =
        some (Zlib.Trees.Proofs.Out.dcodeN (s.distance - 1)) := by
      simp only [Symbol.distanceKey, nonzero, ite_false]
    exact codes.distance_decode _ (valid_distance_key (ledger.valid s member) selected)
      (ledger.distance_used member nonzero) suffix
  · exact codes.literal_decode 256 (by decide +kernel) ledger.end_marker

/-- The actual constructed dynamic header and the actual stored payload
words form an independent DEFLATE body for the exact input trace. This
uses source-execution code data, not an assumed compressor contract. -/
theorem dynamic_prepared_body {original ready : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    {input : Nat → UInt8} {base : Nat} {mb : Int32}
    (ledger : SymbolLedger buf original xs) (codes : SourceCodeFacts original ready)
    (data : PreparedHeaderData ready mb) (trace : Trace input base xs) (suffix : List Bool) :
    ZlibF.Spec.Body [] 2 (inputPrefix input base)
      ((dynamicHeaderBits ready mb ++
        (xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist) (s.distance, s.value)) ++
          codeBits (sourceWords ready .lit) 256)) ++ suffix) suffix
      (inputPrefix input (base + represented xs)) := by
  have payload := Zlib.Trees.Proofs.Out.dynamic_payload_grammar _ _ _ _ trace
    (source_symbol_decode_data ledger codes) suffix
  have body := Zlib.Trees.Proofs.allTreeData_dynamic_body data.all data.guards data.table
    data.format.eob data.format.lit data.format.dist [] (inputPrefix input base)
    (inputPrefix input (base + represented xs)) _ suffix payload
  simpa only [dynamicHeaderBits, sourceLens, Zlib.Trees.Proofs.TK.getDesc, List.append_assoc] using body

/-- Actual construction, header emission and complete dynamic payload
have independent format meaning for the exact logical input trace. The
result includes all memory/ownership facts and final-alignment room.
The common reset/tail and flush branch selection remain separate. -/
theorem dynamic_prepared_payload_format {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs) (last : Bool) :
    ∃ after result next body,
      dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ next.size = 65536 ∧
      result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * 63488 ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++ (dynamicTag last ++ body) ∧
      ∀ suffix, ZlibF.Spec.Body [] 2 (inputPrefix input base) (body ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨mb, ready, after, result, next, run, goodA, treesA, buffersA, sizes, storage,
    _fields, codes, data, _codesA, sizeA, cursorA, roomA, output⟩ :=
    dynamic_prepared_payload_engine (ob := ob) good trees buffers cursor memory pending bits ledger clear last
  let body := dynamicHeaderBits ready mb ++
    (xs.flatMap (fun s => payloadSymBits (sourceWords ready .lit) (sourceWords ready .dist) (s.distance, s.value)) ++
      codeBits (sourceWords ready .lit) 256)
  refine ⟨after, result, next, body, run, goodA, treesA, buffersA, sizes, storage,
    sizeA, cursorA, roomA, ?_, ?_⟩
  · simpa only [body, List.append_assoc] using output
  · intro suffix
    exact dynamic_prepared_body ledger codes data trace suffix

end Zlib.Deflate.Engine.Proofs
