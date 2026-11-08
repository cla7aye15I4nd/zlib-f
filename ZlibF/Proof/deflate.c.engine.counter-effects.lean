import ZlibF.Proof.«deflate.c.engine.fill-caller»
import ZlibF.Proof.«deflate.c.engine.pending-drain»

/-! # Exact wrapping counters and operational result identification -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Returned available counts uniquely determine accepted and delivered counts. -/
theorem stream_accounting_counts_unique {z z' : ZStream} {used first produced second : Nat}
    (one : StreamAccounting z z' used produced) (two : StreamAccounting z z' first second) :
    used = first ∧ produced = second := by
  have inOne := one.2.2.1
  have inTwo := two.2.2.1
  have outOne := one.2.2.2.1
  have outTwo := two.2.2.2.1
  omega

/-- Wrapping public total counters compose over the same natural byte counts. -/
theorem stream_counter_effects_trans {z middle after : ZStream} {used first produced second : Nat}
    (input1 : middle.total_in = z.total_in + UInt64.ofNat used)
    (output1 : middle.total_out = z.total_out + UInt64.ofNat produced)
    (input2 : after.total_in = middle.total_in + UInt64.ofNat first)
    (output2 : after.total_out = middle.total_out + UInt64.ofNat second) :
    after.total_in = z.total_in + UInt64.ofNat (used + first) ∧
      after.total_out = z.total_out + UInt64.ofNat (produced + second) := by
  constructor
  · rw [input2, input1, UInt64.ofNat_add, UInt64.add_assoc]
  · rw [output2, output1, UInt64.ofNat_add, UInt64.add_assoc]

theorem uint32_counter_cast (n : UInt32) : n.toUInt64 = UInt64.ofNat n.toNat := by
  simpa only [UInt32.toNat_toUInt64] using (UInt64.ofNat_toNat (x := n.toUInt64)).symm

/-- The actual read record update changes only the wrapping input total. -/
theorem read_stream_counter_effects (z : ZStream) (n : UInt32) (ref : BRef) (off : Nat) (checksum : UInt64) :
    (readStream z n ref off checksum).total_in = z.total_in + UInt64.ofNat n.toNat ∧
      (readStream z n ref off checksum).total_out = z.total_out := by
  exact ⟨congrArg (z.total_in + ·) (uint32_counter_cast n), rfl⟩

/-- The actual pending record update changes only the wrapping output total. -/
theorem pending_stream_counter_effects (z : ZStream) (out : BPtr) (n : UInt32) :
    (pendingStream z out n).total_in = z.total_in ∧
      (pendingStream z out n).total_out = z.total_out + UInt64.ofNat n.toNat := by
  exact ⟨rfl, congrArg (z.total_out + ·) (uint32_counter_cast n)⟩

/-- Determinism identifies the stream at an independently established
actual return heap. This is an operational lemma, not a callee contract. -/
theorem actual_run_stream_unique {α : Type} {f : M α} {h first after : Heap} {r : ZStreamRef}
    {value result : α} {z z' : ZStream}
    (one : f h = .ok (value, first)) (two : f h = .ok (result, after))
    (getOne : r.get first = some z) (getTwo : r.get after = some z') : z = z' := by
  have heaps : first = after := (Prod.mk.inj (Except.ok.inj (one.symm.trans two))).2
  rw [heaps] at getOne
  exact Option.some.inj (getOne.symm.trans getTwo)

theorem unchanged_stream_counter_effects_accounted {z z' : ZStream} {used : Nat}
    (stream : z' = z) (account : StreamAccounting z z' used 0) :
    z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out := by
  rw [stream] at account ⊢
  have input := account.2.2.1
  have amount : used = 0 := by omega
  simp [amount]

theorem read_stream_counter_effects_accounted {z z' : ZStream} {used : Nat} {n : UInt32}
    {ref : BRef} {io : Nat} {checksum : UInt64}
    (stream : z' = readStream z n ref io checksum) (account : StreamAccounting z z' used 0)
    (pointer : z.next_in = .ref ref io) (bound : n.toNat ≤ z.avail_in.toNat) :
    z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out := by
  rw [stream] at account ⊢
  have expected := read_stream_accounting z n ref io checksum pointer bound
  have amount : used = n.toNat := (stream_accounting_counts_unique account expected).1
  rw [amount]
  exact read_stream_counter_effects z n ref io checksum

/-- An unchanged actual stream admits no delivered bytes under accounting. -/
theorem unchanged_stream_output_counter_effects_accounted {z z' : ZStream} {produced : Nat}
    (stream : z' = z) (account : StreamAccounting z z' 0 produced) :
    z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced := by
  rw [stream] at account ⊢
  have output := account.2.2.2.1
  have amount : produced = 0 := by omega
  simp [amount]

/-- Determinism plus availability accounting transfers exact totals to
any presentation of the same actual returned stream and byte counts. -/
theorem stream_counter_effects_identify {z expected returned : ZStream}
    {accepted delivered used produced : Nat}
    (same : expected = returned)
    (known : StreamAccounting z expected accepted delivered)
    (account : StreamAccounting z returned used produced)
    (input : expected.total_in = z.total_in + UInt64.ofNat accepted)
    (output : expected.total_out = z.total_out + UInt64.ofNat delivered) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  rw [same] at known input output
  obtain ⟨rfl, rfl⟩ := stream_accounting_counts_unique known account
  exact ⟨input, output⟩

end Zlib.Deflate.Engine.Proofs
