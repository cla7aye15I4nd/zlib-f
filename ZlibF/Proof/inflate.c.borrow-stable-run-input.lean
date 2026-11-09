import ZlibF.Proof.«inflate.c.borrow-stable-run»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»

/-! Discharge the internal borrowed-view observation using the very same actual
execution that establishes the caller output frame. The initialized default
state assumptions below are the existing internal execution theorem's domain. -/
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inflate.BorrowProofs

/-- On a real default dispatch execution, the proved output frame and the
unconditional metadata producer preserve every admitted separate caller input.
Neither a Frame contract nor BorrowStable is assumed of a callee. -/
theorem inflate_dispatch_default_input_bytes_preserved
    {c : Ctx} {l regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs xs : List UInt8}
    {outcome : Except Ex Unit} {made count off : Nat} {p : BPtr}
    {dest : BRef} {output : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (madeCount : regs.left.toNat + made = l.left.toNat)
    (outputPtr : l.put = .ref dest off) (outputGet : Space.get h dest = some output)
    (range : CallerRange h r p count false) (bytes : Bytes h p count xs)
    (separate : Separate p count (.ref dest off) made) :
    Bytes after p count xs := by
  have actualFrame := inflate_dispatch_default_frame_of_run E invariant buffers incoming run madeCount
  have frame : BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest off, made⟩] := by
    rw [outputPtr] at actualFrame
    exact inflate_buffer_frame_mono actualFrame (fun b changed =>
      changed.elim Or.inl (fun same => Or.inr (Or.inl same)))
  have borrow : after.libcErrorBorrow = h.libcErrorBorrow :=
    inflate_dispatch_borrow_eq c l regs h after outcome run
  exact caller_input_bytes_preserved invariant.good range outputGet bytes separate frame
    (fun {ref off input} _ _ => by cases ref <;> simp only [C.LibcBorrow.BorrowStable]; exact Or.inr borrow)

/-- The complete real inflate_run frame is derived from the established
initialized default loop. Its actual returning run supplies borrow stability;
the caller need not assume stability or a loop/frame callee contract. -/
theorem inflate_run_default_input_bytes_preserved
    {c : Ctx} {regs : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {xs : List UInt8} {exit : Ex}
    {made count off : Nat} {p : BPtr} {dest : BRef} {output : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after))
    (madeCount : regs.left.toNat + made = z.avail_out.toNat)
    (outputPtr : z.next_out = .ref dest off) (outputGet : Space.get h dest = some output)
    (range : CallerRange h r p count false) (bytes : Bytes h p count xs)
    (separate : Separate p count (.ref dest off) made) :
    Bytes after p count xs := by
  obtain ⟨_bs, exit', regs', after', _stream, _state, _used, made', _bound,
      execution, _current, _packet, _bits, _sizes, _next, _haveCount, _put,
      outputCount, _metadata, actualFrame⟩ :=
    inflate_run_default_view_exact_frame E invariant buffers nonnull inputValid
  rw [run] at execution
  cases execution
  have same : made' = made := by omega
  rw [same, outputPtr] at actualFrame
  have frame : BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨.ref dest off, made⟩] :=
    inflate_buffer_frame_mono actualFrame (fun b changed =>
      changed.elim Or.inl (fun same => Or.inr (Or.inl same)))
  have borrow : after.libcErrorBorrow = h.libcErrorBorrow :=
    inflate_run_borrow_eq c IL.init regs h after (.error exit) run
  exact caller_input_bytes_preserved invariant.good range outputGet bytes separate frame
    (fun {ref off input} _ _ => by cases ref <;> simp only [C.LibcBorrow.BorrowStable]; exact Or.inr borrow)

#print axioms inflate_dispatch_default_input_bytes_preserved
#print axioms inflate_run_default_input_bytes_preserved
end Zlib.Inflate.Proofs
