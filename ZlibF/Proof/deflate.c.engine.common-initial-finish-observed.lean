import ZlibF.Proof.«deflate.c.engine.common-first-finish-one-encoding»
import ZlibF.Proof.«deflate.c.engine.common-initialized-history-environment»

/-! # An actual first one-byte FINISH retains one fixed remaining input -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual one-byte level-specific header writes only that caller
interval; the state and private pending writes retain byte-view depths. -/
theorem common_header_one_output_effect {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (get : h.bytes ob = some output) (bound : oo + 1 ≤ output.size) :
    RawOutputInterval h (levelHeaderOneHeap h r ds pb ob oo z d buf output) ob oo 1 := by
  intro before getBefore
  have same : before = output := Option.some.inj (getBefore.symm.trans get)
  subst before
  refine ⟨copyRange output (levelHeaderBytes d.level buf) oo 0 1, ?_, size_copyRange _ _ _ _ _, ?_⟩
  · simp only [levelHeaderOneHeap, setD_bytes, ZStreamRef.put_bytes, levelHeaderOneBytes, upd_same]
  · intro j _range outside
    rw [getElem?_copyRange output (levelHeaderBytes d.level buf) oo 0 1 j bound, ite_eq_right outside]

/-- A real first one-byte FINISH consumes no input and publishes exactly
120. Its fixed original input snapshot survives even for disjoint input
and output in the same raw allocation. All environment facts are retained
on the same observed returned heap. -/
theorem common_initial_finish_one_observed {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8}
    (initial : EngineStart h r ds z d)
    (boundary : BufferedBoundary h r ds z d (fun _ => 0) 0 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) (header : d.gzhead = none)
    (globals : LibraryGlobals h) (allocators : DefAlloc z) :
    ∃ after z' result,
      DataStep .deflate h after r Z_FINISH Z_OK input [120] 0 ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      Bytes after z'.next_in z'.avail_in.toNat input ∧ StreamAccounting z z' 0 1 ∧
      result.status = BUSY_STATE ∧ LibraryGlobals after ∧ DefAlloc z' := by
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshot
  obtain ⟨after, z', result, run, stateA, buffersA, accountA, bytesA, _outputA, statusA,
      _lastA, _encodingA, _checksumA⟩ :=
    public_common_first_finish_one_byte_encoding_adler initial boundary buffers pointer one valid
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have same : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro eq
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have extent := trees.base.size; have lower := trees.base.lit_lo; omega
  have canonical := first_common_finish_one_source initial trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound one valid
  have heaps : after = levelHeaderOneHeap h r ds pb ob oo z d buf output :=
    (Prod.mk.inj (Except.ok.inj (run.symm.trans canonical))).2
  have storage : OutputStorage h (levelHeaderOneHeap h r ds pb ob oo z d buf output) r ds pb ob :=
    header_write_storage initial.good trees.base.bytes outGet separate _ _ _ _
  rw [← heaps] at storage
  have effect := common_header_one_output_effect (r := r) (ds := ds) (pb := pb) (z := z) (d := d) (buf := buf)
    outGet (by rw [one] at outBound; exact outBound)
  rw [← heaps] at effect
  have originalBuffers := buffers
  obtain ⟨oldZ, oldGet, inputRange, _outputRange, separated⟩ := originalBuffers
  have oldSame : oldZ = z := Option.some.inj (oldGet.symm.trans initial.good.live.hz)
  subst oldZ
  have separatedOne : Separate z.next_in z.avail_in.toNat z.next_out 1 := by
    rw [one] at separated
    exact separated
  have preserved := caller_input_bytes_preserved initial.good buffers pointer inputRange separatedOne
    (Nat.le_refl _) snapshot (storage.private_frame trees.base.pbuf) effect
  have sameCount : z'.avail_in = z.avail_in := by
    apply UInt32.toNat_inj.mp
    have effect := accountA.2.2.1
    omega
  have sameInput : z'.next_in = z.next_in := by
    simpa only [advance_zero] using accountA.2.2.2.2.1
  have snapshotA : Bytes after z'.next_in z'.avail_in.toNat input := by
    rw [sameCount, sameInput]
    exact preserved
  have observed : DataStep .deflate h after r Z_FINISH Z_OK input [120] 0 := by
    refine ⟨z, z', initial.good.live.hz, stateA.good.live.hz, buffers,
      default_finish_active_header initial.good header, snapshot, ?_, ?_, run⟩
    · rw [sameCount]; omega
    · have count := accountA.2.2.2.1
      have amount : z.avail_out.toNat - z'.avail_out.toNat = 1 := by omega
      rw [amount]
      exact bytesA
  have globalsA : LibraryGlobals after := storage.frame.1.symm.trans globals
  have allocatorsA : DefAlloc z' := by
    rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
    exact ⟨keepAlloc.trans allocators.1, keepFree.trans allocators.2⟩
  exact ⟨after, z', result, observed, stateA.good, buffersA, snapshotA, accountA, statusA, globalsA, allocatorsA⟩

end Zlib.Deflate.Engine.Proofs
