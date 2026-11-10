import ZlibF.Proof.«deflate.c.engine.memory-four-flush-ready»
import ZlibF.Proof.«deflate.c.engine.memory-four-flush-frame»
import ZlibF.Proof.«deflate.c.engine.memory-flush-ready»
import ZlibF.Proof.«deflate.c.engine.memory-flush-frame»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt natBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
theorem memory_from_four_flush_ready {memory : Nat} {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (capacity : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 4 ≤ memory) (memoryHigh : memory ≤ 9) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat)
    (storedStart : 0 ≤ d.block_start.toInt → d.strstart.toNat < 65536) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (z' : ZStream) (after : Heap) (result : DeflateState) (next : Array UInt8)
      (kind : Nat) (body padding : List Bool),
      Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
      next.size = buf.size ∧ result.pending.toNat ≤ next.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      (last = true → result.bi_valid.toInt = 0) ∧ kind < 3 ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧ (kind = 0 → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (natBits (if last then 1 else 0) 1 ++ natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  by_cases four : memory = 4
  · subst memory
    exact mem_four_flush_ready (ob := ob) good trees buffers positive cursor capacity pending bits ledger clear trace win get range storedStart balance accounted view last
  · have low : 5 ≤ memory := by omega
    exact memory_flush_ready (ob := ob) good trees buffers positive cursor capacity low memoryHigh pending bits ledger clear trace win get range storedStart balance accounted view last

theorem memory_from_four_flush_frame_execution {memory : Nat} {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (allocation : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 4 ≤ memory) (memoryHigh : memory ≤ 9) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat)
    (storedStart : 0 ≤ d.block_start.toInt → d.strstart.toNat < 65536) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (z' : ZStream) (after : Heap) (result : DeflateState) (next : Array UInt8),
      Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  by_cases four : memory = 4
  · subst memory
    exact mem_four_flush_frame_execution (ob := ob) good trees buffers positive cursor allocation pending bits ledger clear trace win get range storedStart balance accounted view last
  · have low : 5 ≤ memory := by omega
    exact memory_flush_frame_execution (ob := ob) good trees buffers positive cursor allocation low memoryHigh pending bits ledger clear trace win get range storedStart balance accounted view last

theorem memory_from_four_flush_run_frame {memory : Nat} {h after : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d result : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (allocation : d.lit_bufsize.toNat = 2 ^ (memory + 6))
    (memoryLow : 4 ≤ memory) (memoryHigh : memory ≤ 9) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat)
    (storedStart : 0 ≤ d.block_start.toInt → d.strstart.toNat < 65536) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
      (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after))
    (live : after.dstates ds = some result) : FlushWorkFrame d result := by
  by_cases four : memory = 4
  · subst memory
    exact mem_four_flush_run_frame (ob := ob) good trees buffers positive cursor allocation pending bits ledger clear trace win get range storedStart balance accounted view last run live
  · have low : 5 ≤ memory := by omega
    exact memory_flush_run_frame (ob := ob) good trees buffers positive cursor allocation low memoryHigh pending bits ledger clear trace win get range storedStart balance accounted view last run live

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_from_four_flush_ready
#print axioms Zlib.Deflate.Engine.Proofs.memory_from_four_flush_frame_execution
#print axioms Zlib.Deflate.Engine.Proofs.memory_from_four_flush_run_frame
