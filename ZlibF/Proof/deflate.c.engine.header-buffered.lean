import ZlibF.Proof.«deflate.c.engine.buffered-boundary»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-all»

/-! # A split first header retains the initialized buffered boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
/-- Empty packed content survives pending-byte writes when the actual
window and hash arrays are retained. Output control fields may change. -/
theorem empty_content_control_transfer {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z z' : ZStream} {d result : DeflateState} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base []) (goodA : DGood after r ds z' result)
    (bytes : ∀ b, d.window = .ref (.blk b) 0 → after.bytes b = h.bytes b)
    (words : after.words = h.words)
    (fields : result = { d with
      pending := result.pending, pending_out := result.pending_out,
      status := result.status, last_flush := result.last_flush, wrap := result.wrap }) :
    ContentBoundary after r ds z' result input origin base [] := by
  have chains : ∀ top, HeapChains h d top → HeapChains after result top :=
    fun _ chain => control_heap_chains chain bytes words fields
  obtain ⟨_oldPb, _oldBuf, _trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨_w, _p, _q, pb, blocks⟩ := goodA.inv.blocks
  obtain ⟨buf, getB, _sizeB⟩ := blocks.ba
  have ledgerA : SymbolLedger buf result [] := by
    refine ⟨?_, ledger.valid, ?_, ?_, ?_⟩
    · rw [fields]; exact ledger.count
    · intro i symbol selected
      simp at selected
    · rw [fields]; exact ledger.literal
    · rw [fields]; exact ledger.distance
  have symbols : SymbolBoundary after ds result [] :=
    symbol_boundary_of_ledger goodA blocks.pbuf getB ledgerA (by rw [fields]; exact balance)
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  refine ⟨⟨⟨goodA, ?_, ?_, ?_, ?_, symbols, ?_⟩, ?_, ?_, ?_⟩, boundary.trace, ?_⟩
  · have startEq : result.strstart = d.strstart := by rw [fields]
    rw [startEq]
    exact chains d.strstart.toNat boundary.chains
  · rw [fields]; exact boundary.range
  · rw [fields]; exact boundary.history
  · rw [fields]; exact boundary.deferred
  · refine ⟨w, wa, ?_, (bytes w win).trans get, ?_, ?_⟩
    · rw [fields]; exact win
    · rw [fields]; exact view
    · rw [fields]; exact form
  · rw [fields]; exact boundary.insert_le
  · have startEq : result.strstart = d.strstart := by rw [fields]
    have insertEq : result.insert = d.insert := by rw [fields]
    rw [startEq, insertEq]
    exact chains (d.strstart.toNat - d.insert.toNat) boundary.frontier
  · rw [fields]; exact boundary.ready
  · rw [fields]; exact boundary.accounted


def headerOneState (d : DeflateState) (pb : Nat) : DeflateState :=
  { d with status := BUSY_STATE, last_flush := -1, pending := 1, pending_out := .ref (.blk pb) 1 }

def headerOneBytes (h : Heap) (pb ob oo : Nat) (buf output : Array UInt8) : Heap :=
  { h with
    bytes := upd (upd h.bytes pb (some (zlibHeaderBytes buf))) ob
      (some (copyRange output (zlibHeaderBytes buf) oo 0 1)) }

def headerOneHeap (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) : Heap :=
  setD (r.put (headerOneBytes h pb ob oo buf output)
    (pendingStream z (.ref (.blk ob) (oo + 1)) 1)) ds (headerOneState d pb)

/-- Exact actual first-call heap when the header is split after one byte. -/
theorem first_finish_one_source {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (pending : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (room : 2 ≤ buf.size) (writable : h.ro pb = false)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (outRw : h.ro ob = false) (separate : ob ≠ pb)
    (bound : oo + z.avail_out.toNat ≤ output.size) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_FINISH h = .ok (Z_OK, headerOneHeap h r ds pb ob oo z d buf output) := by
  let d0 := { d with last_flush := Z_FINISH }
  let h0 := setD h ds d0
  have good0 := last_flush_good initial.good Z_FINISH
  have header := public_default_header_run good0.live.hz initial.good.live.zst good0.live.hs
    initial.status initial.wrap initial.bits level initial.strategy initial.windowBits initial.start initial.pending
    pending initial.pendingOut (by simpa only [h0, setD_bytes] using get) room
    (by simpa only [h0, setD_ro] using writable) pointer
    (by simpa only [h0, setD_bytes] using outGet) (by simpa only [h0, setD_ro] using outRw)
    separate bound (by rw [one]; decide) (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
  have entry := public_default_finish_initial_entry initial (by rw [pointer]; intro impossible; cases impossible)
    (by rw [one]; decide) valid
  rw [entry, header]
  have selected : pendingLen 2 z.avail_out = 1 := by rw [one]; rfl
  simp only [selected, show ((2 : UInt64) - (1 : UInt32).toUInt64 != 0) = true from rfl, ite_true]
  have reset : { pendingState (zlibHeaderState d0) (.ref (.blk pb) 1) 1 with last_flush := -1 } =
      headerOneState d pb := by
    simp only [pendingState, zlibHeaderState, d0, headerOneState,
      show ((2 : UInt64) - (1 : UInt32).toUInt64) = 1 from by decide,
      show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ite_false]
  have adler : { z with adler := 1 } = z := by rw [← initial.adler]
  simp only [zlibHeaderFlushed, selected, zlibHeaderReady, reset, adler, h0, d0,
    setD_bytes, ZStreamRef.put_bytes, setD_bytes_commute, ← stream_put_bytes, ZStreamRef.put_setD, setD_setD,
    headerOneHeap, headerOneBytes,
    show ((1 : UInt32).toNat) = 1 from rfl, ZStreamRef.put_put, reset]
/-- The actual one-byte first call retains the buffered boundary before
any caller rebuffering or pending drain. -/
theorem first_finish_one_buffered {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (one : z.avail_out = 1) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result,
      deflate (some r) Z_FINISH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 1 ∧
      z'.avail_out = 0 ∧ result.pending = 1 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have extent := trees.base.size; have lower := trees.base.lit_lo; omega
  have canonical := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound one valid
  obtain ⟨after, z', result, run, goodA, buffersA, accountA, emptyA, statusA, pendingA, _bitsA, lastA⟩ :=
    public_default_first_finish_one initial level buffers pointer one valid
  have heaps : after = headerOneHeap h r ds pb ob oo z d buf output :=
    (Prod.mk.inj (Except.ok.inj (run.symm.trans canonical))).2
  have states : result = headerOneState d pb := by
    have live := goodA.live.hs
    rw [heaps] at live
    simp only [headerOneHeap, setD_dstates_same] at live
    exact Option.some.inj live.symm
  have privateWindow : ∀ b, d.window = .ref (.blk b) 0 → after.bytes b = h.bytes b := by
    intro b win
    obtain ⟨w, p, q, pb0, blocks⟩ := initial.good.inv.blocks
    have wid : w = b := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have bid : pb0 = pb := by
      simpa only [trees.base.pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst w pb0
    have outDifferent : b ≠ ob := by
      intro same
      subst b
      exact outside (Or.inr (Or.inl win))
    rw [heaps]
    simp only [headerOneHeap, headerOneBytes, setD_bytes, ZStreamRef.put_bytes,
      upd_ne _ _ _ _ outDifferent, upd_ne _ _ _ _ blocks.wb]
  have words : after.words = h.words := by
    rw [heaps]
    simp only [headerOneHeap, headerOneBytes, setD_words, ZStreamRef.put_words]
  have control : result = { d with
      pending := result.pending, pending_out := result.pending_out,
      status := result.status, last_flush := result.last_flush, wrap := result.wrap } := by rw [states]; rfl
  have contentA := empty_content_control_transfer boundary.toContentBoundary goodA privateWindow words control
  have frontierA : EndFrontier after result := by
    have ss : result.strstart = d.strstart := by rw [states]; rfl
    have endpoint : fillEnd result = fillEnd d := by rw [states]; rfl
    unfold EndFrontier
    rw [ss, endpoint]
    exact control_heap_chains boundary.end_frontier privateWindow words control
  have configA : ConfigFrame d result := by rw [states]; rfl
  have clearA : BlockInit.BlockClear result := by
    rw [states]
    exact ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩
  have lowA : result.bi_valid.toInt < 8 := by rw [states]; exact boundary.bits
  have strictA : result.sym_next.toNat < result.sym_end.toNat := by rw [states]; exact boundary.strict
  have cursorA : result.pending = 0 → result.pending_out = result.pending_buf := by
    intro empty
    rw [pendingA] at empty
    cases (show (1 : UInt64) ≠ 0 from by decide) empty
  exact ⟨after, z', result, run,
    ⟨contentA, Eq.trans configA boundary.configuration, clearA, lowA, strictA, frontierA, cursorA⟩,
    buffersA, accountA, emptyA, pendingA, statusA, lastA⟩
end Zlib.Deflate.Engine.Proofs
