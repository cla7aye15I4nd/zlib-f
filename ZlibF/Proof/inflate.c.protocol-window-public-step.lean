import ZlibF.Proof.«inflate.c.protocol-window-history»
import ZlibF.Spec.Functional.Sequences

namespace Zlib.Inflate.Proofs.ProtocolWindow
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A real public call from an initialized, platform-scoped protocol history
produces its accounting, output, frame and allocation facts together with the
next actual protocol history. No incoming decoder invariant or successful
callee execution is assumed. This does not yet identify the output with an
independent compressed-stream parse. -/
theorem public_step_with_history
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    {z : ZStream} {input : List UInt8}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : PlatformScope trace)
    (streamGet : r.get h = some z) (buffers : StreamBuffers h r)
    (header : ActiveHeader h r) (inputBytes : Bytes h z.next_in z.avail_in.toNat input)
    (flush : Int32) :
    ∃ zs s rc after stream state used output,
      DefaultStateJ h r zs z s ∧
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      StreamAccounting z stream used output.length ∧
      Bytes after z.next_out output.length output ∧
      PublicInflateCode rc ∧ ReturnedModes rc state ∧
      (rc = Z_OK → (used ≠ 0 ∨ output ≠ []) ∧ flush ≠ Z_FINISH) ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in ∧ stream.total_out = z.total_out) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used ∧
        stream.total_out = z.total_out + UInt64.ofNat output.length) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b ∨ s.head = some (.tab b))
        (⟨z.next_out, output.length⟩ :: HeaderRegions h s.head) ∧
      LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) ∧
      DataStep .inflate h after r flush rc input output used ∧
      ∃ next : InflateProtocolTrace 15 r after
          { log with
            input := log.input ++ input.take used
            output := log.output ++ output
            result := rc
            finished := log.finished || rc == Z_STREAM_END }
          (rc == Z_NEED_DICT), PlatformScope next := by
  obtain ⟨physical, history, _exact, zs, before, s, invariant, allocator, _token, _empty⟩ :=
    exact_physical_history trace scope
  have same : before = z := Option.some.inj (invariant.good.live.hz.symm.trans streamGet)
  subst before
  have entry := history.entry invariant
  have record := ActiveHeader.record header invariant.good.live
  obtain ⟨rc, after, stream, state, used, output, run, current, finalAllocator, _freed,
    accounting, observed, totals, progress, code, memoryTotals, modes, frame, ledger⟩ :=
    inflate_default_view_public_memory_contract invariant allocator buffers entry record flush
  have usedCount : used = z.avail_in.toNat - stream.avail_in.toNat := by
    have count := accounting.2.2.1
    omega
  have madeCount : z.avail_out.toNat - stream.avail_out.toNat = output.length := by
    have count := accounting.2.2.2.1
    omega
  have actual : DataStep .inflate h after r flush rc input output used :=
    ⟨z, stream, streamGet, current.good.live.hz, buffers, header, inputBytes, usedCount,
      by simpa only [madeCount] using observed, run⟩
  exact ⟨zs, s, rc, after, stream, state, used, output, invariant, run, current,
    finalAllocator, accounting, observed, code, modes, progress, memoryTotals, totals,
    frame, ledger, actual, .step trace invariant.platform actual,
    PlatformScope.step (fit := invariant.platform) (actual := actual) scope⟩

#print axioms public_step_with_history
end Zlib.Inflate.Proofs.ProtocolWindow
