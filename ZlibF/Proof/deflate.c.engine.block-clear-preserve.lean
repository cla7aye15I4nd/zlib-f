import ZlibF.Proof.«deflate.c.engine.block-initial»

/-! # Actual reset and non-flushing frames retain the block's cleared BL data -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open BlockInit
set_option autoImplicit false

theorem BlockInit.BlockClear.slow {before after : DeflateState}
    (clear : BlockClear before) (frame : SlowRecordFrame before after) : BlockClear after := by
  rw [frame]
  exact ⟨clear.bl, clear.opt, clear.fixed⟩

theorem BlockInit.BlockClear.fill {before after : DeflateState}
    (clear : BlockClear before) (frame : FillRecordFrame before after) : BlockClear after := by
  rw [frame]
  exact ⟨clear.bl, clear.opt, clear.fixed⟩

theorem BlockInit.BlockClear.bits {before after : DeflateState}
    (clear : BlockClear before) (frame : Zlib.Trees.Proofs.Out.BitsDiff before after) : BlockClear after := by
  obtain ⟨p, word, valid, used, fields⟩ := frame
  rw [fields]
  exact ⟨clear.bl, clear.opt, clear.fixed⟩

/-- The same actual reset that restores the empty symbol ledger also
clears every BL frequency and both cost counters. No zero values are
assumed at the reset entry. -/
theorem init_block_clear_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    ∃ result,
      Zlib.Trees.init_block (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ SymbolLedger buf result [] ∧ BlockClear result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨_a1, _a2, _a3, result, run, goodA, treesA, buffersA, sizes, storage,
    _fields, ledger, output⟩ := init_block_engine (ob := ob) good trees buffers
  obtain ⟨a1, a2, a3, other, run2, _trees2, fields, _s1, _s2, _s3,
    _lit, _eob, _dist, zero, _lenL, _lenD, _lenB⟩ :=
    Zlib.Trees.Proofs.Out.init_block_spec0 trees.base trees.run.to0
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run run2
  have cleared : BlockClear result := by
    rw [same, fields]
    exact ⟨zero, rfl, rfl⟩
  exact ⟨result, run, goodA, treesA, buffersA, sizes, storage, ledger, cleared, output⟩

end Zlib.Deflate.Engine.Proofs
