import ZlibF.Proof.«trees.c.stored-header»
import ZlibF.Proof.«deflate.c.engine.macros»

/-! # The real stored-block byte copy and pending-counter update -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

def storedBlockCopy (s : DeflateStatePtr) (source : BPtr) (length : UInt64) : M Unit := do
  if length != 0 then
    let d ← rd s
    let dst ← Ptr.add d.pending_buf (d.pending.toNat : Int)
    memcpyB dst source length.toNat
  md s fun d => { d with pending := d.pending + length }

/-- The actual stored branch is its proved header followed by the exact
conditional memcpy and unsigned pending update. -/
theorem stored_block_source (s : DeflateStatePtr) (source : BPtr) (length : UInt64) (last : Int32) :
    «_tr_stored_block» s source length last = (do
      storedBlockHeader s length last
      storedBlockCopy s source length) := by
  rw [stored_block_header_source]
  unfold storedBlockCopy
  rfl

/-- The actual copy reads a distinct live source allocation and writes
exactly its requested range. The room inequality bounds the unsigned sum;
zero length takes the real no-memcpy path. -/
theorem stored_block_copy_run {h : Heap} {id b sourceBlock offset : Nat} {d : DeflateState}
    {buf source : Array UInt8}
    (trees : TreesInvAt h id d b buf) (get : h.bytes sourceBlock = some source)
    (separate : b ≠ sourceBlock) (length : UInt64)
    (input : offset + length.toNat ≤ source.size) (room : d.pending.toNat + length.toNat ≤ buf.size) :
    let next := copyRange buf source d.pending.toNat offset length.toNat
    let result : DeflateState := { d with pending := d.pending + length }
    storedBlockCopy (some (.tab id)) (.ref (.blk sourceBlock) offset) length h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      result.pending.toNat = d.pending.toNat + length.toNat ∧ next.size = buf.size ∧ BitsDiff d result := by
  dsimp only
  have pending : (d.pending + length).toNat = d.pending.toNat + length.toNat := by
    rw [UInt64.toNat_add]
    have size := trees.base.size
    have capacity := trees.base.lit_hi
    exact Nat.mod_eq_of_lt (by change _ < 18446744073709551616; omega)
  refine ⟨?_, ?_, pending, size_copyRange _ _ _ _ _, d.pending + length, d.bi_buf,
    d.bi_valid, d.bi_used, rfl⟩
  · unfold storedBlockCopy
    by_cases zero : length = 0
    · subst length
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, bind_app, pure_app, UInt64.add_zero]
      rw [md_run trees.base.dstate]
      change (Except.ok ((), setD h id d) : Except Fault (Unit × Heap)) =
        Except.ok ((), setD (setB h b buf) id d)
      rw [setB_self trees.base.bytes]
    · have getB : Space.get h (BRef.blk b) = some buf := trees.base.bytes
      have add := Ptr.add_nat_ok (r := BRef.blk b) (off := 0) (n := d.pending.toNat) getB
        (by omega)
      unfold OkOn at add
      have copy := memcpyB_blk_ok trees.base.bytes get trees.base.rw separate room input
      simp only [show (length != 0) = true from bne_iff_ne.mpr zero, ite_true, bind_app,
        rd_run trees.base.dstate, trees.base.pbuf, add, Nat.zero_add, copy]
      simpa only [setB, trees.base.pbuf] using
        (md_run (h := setB h b (copyRange buf source d.pending.toNat offset length.toNat))
          trees.base.dstate (fun state => { state with pending := state.pending + length }))
  · refine ⟨trees.base.step _ (size_copyRange _ _ _ _ _) _ trees.base.wf rfl rfl rfl rfl rfl ?_,
      trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat, trees.run.bldyn, trees.run.blstat,
      trees.run.bi_lo, trees.run.bi_hi, trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩
    change (d.pending + length).toNat ≤ d.pending_buf_size.toNat
    rw [pending, trees.base.psize]
    exact room

def sourceByteBits (source : Array UInt8) (offset length : Nat) : List Bool :=
  (List.range length).flatMap (fun i => natBits source[offset + i]!.toNat 8)

/-- The concrete range-copy operation appends exactly the selected source
bytes to the pending prefix. Earlier pending bytes retain their values. -/
theorem bytesBits_copyRange (destination source : Array UInt8) (pending offset count : Nat)
    (room : pending + count ≤ destination.size) :
    bytesBits (copyRange destination source pending offset count) (pending + count) =
      bytesBits destination pending ++ sourceByteBits source offset count := by
  induction count with
  | zero => simp [copyRange, sourceByteBits]
  | succ count ih =>
    rw [Zlib.Deflate.Engine.Proofs.copyRange_succ, show pending + (count + 1) = (pending + count) + 1 by omega,
      bytesBits_one _ (by rw [size_copyRange]; omega), ih (by omega)]
    simp only [sourceByteBits, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- The actual aligned memcpy and counter update append these exact bytes,
rather than merely establishing memory safety or an abstract bit grammar. -/
theorem stored_block_copy_bits {h : Heap} {id b sourceBlock offset : Nat} {d : DeflateState}
    {buf source : Array UInt8}
    (trees : TreesInvAt h id d b buf) (get : h.bytes sourceBlock = some source)
    (separate : b ≠ sourceBlock) (length : UInt64) (aligned : d.bi_valid.toInt = 0)
    (input : offset + length.toNat ≤ source.size) (room : d.pending.toNat + length.toNat ≤ buf.size) :
    let next := copyRange buf source d.pending.toNat offset length.toNat
    let result : DeflateState := { d with pending := d.pending + length }
    storedBlockCopy (some (.tab id)) (.ref (.blk sourceBlock) offset) length h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      outBits next result = outBits buf d ++ sourceByteBits source offset length.toNat ∧
      result.pending.toNat = d.pending.toNat + length.toNat ∧ next.size = buf.size ∧ BitsDiff d result := by
  obtain ⟨run, treesA, pending, size, diff⟩ := stored_block_copy_run trees get separate length input room
  refine ⟨run, treesA, ?_, pending, size, diff⟩
  unfold outBits
  dsimp only
  rw [pending, aligned]
  simp only [Int.toNat_zero, show natBits d.bi_buf.toNat 0 = [] from rfl, List.append_nil]
  exact bytesBits_copyRange buf source d.pending.toNat offset length.toNat room

end Zlib.Trees.Proofs.Out
