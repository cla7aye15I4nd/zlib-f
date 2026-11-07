import ZlibF.Proof.«deflate.c.engine.buffered-boundary»

/-! # Actual pending publication preserves the public buffered boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real low-bit publication preserves the caller-independent initialized
boundary and establishes strategy readiness whenever output remains.
Both cursors may start advanced. Zero-copy and partial-output cases use
the actual pending code. Written bytes and remaining pending bits retain
the exact input pending sequence on this same returned heap. -/
theorem flush_pending_buffered_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    {before : List Bool}
    (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (pending : PendingBits h d before) :
    ∃ pb produced after z' result written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      flush_pending (some r) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before := by
  obtain ⟨pb, produced, after, z', result, written, remaining, basePtr, run, goodA, buffersA, account,
      sizes, storage, amount, left, lowA, fields, reset, bytesA, pendingA, bitsA⟩ :=
    flush_pending_resume_raw_bits boundary.good buffers pointer boundary.bits pending
  obtain ⟨keptBytes, keptWords⟩ :=
    flush_pending_low_run_private boundary.good buffers pointer boundary.bits run
  obtain ⟨_output, _getOut, _rwOut, _boundOut, outside⟩ := caller_raw_output boundary.good buffers pointer
  have privateBytes : ∀ b, d.window = .ref (.blk b) 0 ∨ d.pending_buf = .ref (.blk b) 0 →
      after.bytes b = h.bytes b := by
    intro b ownedArray
    apply keptBytes b
    intro same
    subst b
    rcases ownedArray with win | buffer
    · exact outside (Or.inr (Or.inl win))
    · exact outside (Or.inr (Or.inr (Or.inr (Or.inr buffer))))
  have control : result = { d with
      pending := result.pending, pending_out := result.pending_out,
      status := result.status, last_flush := result.last_flush, wrap := result.wrap } := by
    rw [fields]
  have contentA := content_control_transfer boundary.toContentBoundary goodA privateBytes keptWords control
  have frontierA : EndFrontier after result := by
    have startEq : result.strstart = d.strstart := by rw [fields]
    have endEq : fillEnd result = fillEnd d := by rw [fields]; rfl
    unfold EndFrontier
    rw [startEq, endEq]
    exact control_heap_chains boundary.end_frontier (fun b win => privateBytes b (Or.inl win)) keptWords control
  have emptyCursorA : result.pending = 0 → result.pending_out = result.pending_buf := by
    intro empty
    by_cases moved : 0 < produced
    · exact reset moved (by rw [empty]; rfl)
    · have noCopy : pendingLen d.pending z.avail_out = 0 := by
        apply UInt32.toNat_inj.mp
        change (pendingLen d.pending z.avail_out).toNat = 0
        rw [pendingLen_value, ← amount]
        omega
      have zeroRun := flush_pending_low_zero boundary.good.live.hz boundary.good.live.zst boundary.good.live.hs boundary.bits noCopy
      have heaps : h = after := (Prod.mk.inj (Except.ok.inj (zeroRun.symm.trans run))).2
      have state : d = result := by
        have live := goodA.live.hs
        rw [← heaps] at live
        exact Option.some.inj (boundary.good.live.hs.symm.trans live)
      rw [← state] at empty ⊢
      exact boundary.empty_cursor empty
  have frame : ConfigFrame d result := by rw [fields]; rfl
  have clearA : BlockInit.BlockClear result := by rw [fields]; exact ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩
  have strictA : result.sym_next.toNat < result.sym_end.toNat := by rw [fields]; exact boundary.strict
  have stateA : BufferedBoundary after r ds z' result input origin base xs config :=
    ⟨contentA, Eq.trans frame boundary.configuration, clearA, lowA, strictA, frontierA, emptyCursorA⟩
  refine ⟨pb, produced, after, z', result, written, remaining, basePtr, run, stateA, buffersA, account, sizes,
    storage, amount, left, fields, ?_, bytesA, pendingA, bitsA⟩
  intro space
  have count := account.2.2.2.1
  have zero : result.pending.toNat = 0 := by omega
  have empty : result.pending = 0 := UInt64.toNat_inj.mp zero
  exact ⟨empty, emptyCursorA empty, lowA⟩

end Zlib.Deflate.Engine.Proofs
