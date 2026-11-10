import ZlibF.Proof.«inflate.c.header-entry-classification»
namespace Zlib.Inflate.Proofs.HeaderPhaseView
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.PrivateTableHeader
set_option autoImplicit false

/-- A genuine same-call HEAD/TYPE-to-TABLE continuation whose fourteen
count bits are incomplete returns the public TABLE phase. The actual
main-loop/leave/free path determines the exact original DataLog credit. -/
theorem TableContinuation.public_table_wait
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {log : DataLog} {history : InflateDataTrace 15 r h log}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {bodyRest : List Bool}
    (scope : HeaderDataTrace.PlatformScope history)
    (entry : TableContinuation h r zs log input flush bodyRest)
    (observed : DataStep .inflate h after r flush rc input output used)
    (accepted : ∀ z, r.get h = some z → z.next_out ≠ .null ∧ (z.next_in = .null → z.avail_in = 0))
    (emptyOutput : log.output = []) (short : bodyRest.length < 14) :
    Meaning .table after r zs (credit log input output used rc) := by
  obtain ⟨z, tableZ, s, state, l, heap, sourceUsed, record, getZ, getS, pointer, current, packet, bound, source,
    _bits, mode, window, lastBound, last, view, _put, left, out, _have, mainEntry⟩ := entry
  obtain ⟨nonnull, inputValid⟩ := accepted z getZ
  have actual0 := observed
  obtain ⟨z0, returned, get0, get1, _buffers, _active, bytes, usedEq, outputBytes, _run⟩ := observed
  have sameZ : z0 = z := Option.some.inj (get0.symm.trans getZ)
  subst z0
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have env : Env c heap r zs tableZ state := ⟨rfl, rfl, current.good.live.hz, current.good.live.hs⟩
  obtain ⟨regs, _pull, tableRun, inv, shape, zero, below, held⟩ := table_insufficient_actual (c := c) packet.bits (by rwa [source])
  have dispatch := (inflate_dispatch_TABLE env l mode).trans tableRun
  have loop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => heap) 0 (by unfold fuel; decide)
    Ex.leave regs heap (by intro j impossible; omega) dispatch
  have mainRun := mainEntry.trans loop
  have noOutput : regs.out_ = regs.left := by rw [shape]; exact out
  obtain ⟨nextZ, nextS, next, allocator, frame, _nextIn, nextAvail, _nextOut, nextLeft⟩ :=
    HeaderPublicObserver.actual_wait_from_init history scope actual0 getZ pointer getS nonnull inputValid mainRun current.good.live.hs window noOutput
  have sameReturned : returned = nextZ := Option.some.inj (get1.symm.trans next.good.live.hz)
  subst returned
  have allUsed : used = input.length := by
    rw [usedEq, nextAvail, zero, UInt32.toNat_zero, Nat.sub_zero]
    exact (header_observed_bytes_length bytes).symm
  have noBytes : output = [] := by
    have length := header_observed_bytes_length outputBytes
    rw [nextLeft, shape] at length
    change output.length = z.avail_out.toNat - l.left.toNat at length
    rw [left, Nat.sub_self] at length
    exact List.length_eq_zero_iff.mp length
  have finalView : View readBlock record (bytesBits (log.input ++ input)) (natBits regs.bits.toNat regs.hold.toNat) := by
    have advanced := view.advance (bytesBits (input.drop sourceUsed))
    rw [← bytesBits_append, List.append_assoc, List.take_append_drop] at advanced
    rw [held]
    exact advanced
  refine ⟨nextZ, nextS, next, allocator, ?_, ?_, ?_, record, lastBound, ?_, ?_⟩
  · rw [frame]; exact window
  · simp only [credit, emptyOutput, noBytes, List.nil_append]
  · rw [frame]; exact mode
  · rw [frame]; exact last
  · rw [frame]
    simpa only [credit, allUsed, List.take_length, leaveState] using finalView

#print axioms TableContinuation.public_table_wait
end Zlib.Inflate.Proofs.HeaderPhaseView
