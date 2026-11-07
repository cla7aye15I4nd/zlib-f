import ZlibF.Proof.«deflate.c.engine.public-first-finish»

/-! # The first default public FINISH call at every positive capacity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual header's staged bytes, BUSY store and checksum reset leave
a valid representation and caller ranges before its pending copy. -/
theorem header_ready_good_buffers {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) :
    DGood (zlibHeaderReady h r ds pb z d buf) r ds { z with adler := 1 } (zlibHeaderState d) ∧
    StreamBuffers (zlibHeaderReady h r ds pb z d buf) r := by
  let hb := { h with bytes := upd h.bytes pb (some (zlibHeaderBytes buf)) }
  have size : (zlibHeaderBytes buf).size = buf.size := by simp [zlibHeaderBytes]
  have goodB : DGood hb r ds z d := good.bytes_set pb (zlibHeaderBytes buf) buf trees.base.bytes size
  obtain ⟨w, p, q, b, blocks⟩ := goodB.inv.blocks
  have room : 2 ≤ d.pending_buf_size.toNat := by
    rw [trees.base.psize]
    have lower := trees.base.lit_lo
    have extent := trees.base.size
    omega
  have blocksA : DBlocks hb (zlibHeaderState d) w p q b :=
    { blocks with pout := ⟨0, by change d.pending_out = .ref (.blk b) 0; rw [cursor]; exact blocks.pbuf,
        by change 0 + 2 ≤ d.pending_buf_size.toNat; omega⟩ }
  have inv : DStInv hb ds (zlibHeaderState d) :=
    { goodB.inv with blocks := ⟨w, p, q, b, blocksA⟩ }
  have goodA : DGood (zlibHeaderReady h r ds pb z d buf) r ds { z with adler := 1 } (zlibHeaderState d) :=
    goodB.setZD rfl good.live.zalloc good.live.zfree rfl (by simp [GoodStatus, zlibHeaderState]) inv (by trkeep)
  have view : ∀ ref : BRef, Space.get (zlibHeaderReady h r ds pb z d buf) ref = Space.get hb ref := by
    intro ref
    rw [zlibHeaderReady, byte_view_setD_depth (d := d) (result := zlibHeaderState d)
      (by simpa only [hb, ZStreamRef.put_dstates] using goodB.live.hs) rfl, byte_get_stream_put]
  have sizes : ByteSizes h (zlibHeaderReady h r ds pb z d buf) := by
    refine ⟨?_, ?_⟩
    · intro ref a getA
      obtain ⟨next, getN, sizeN⟩ := byte_view_write_size getA trees.base.bytes size
      exact ⟨next, (view ref).trans getN, sizeN⟩
    · intro ref
      cases ref <;> simp [Space.ro, zlibHeaderReady]
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have account : StreamAccounting z { z with adler := 1 } 0 0 := stream_accounting_zero z
  exact ⟨goodA, stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account⟩

/-- The first public FINISH call with one output byte returns after the
first header byte, with one header byte queued and no input consumed. -/
theorem public_default_first_finish_one {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState}
    (initial : EngineStart h r ds z d) (level : d.level = 6) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ after z' result,
      deflate (some r) Z_FINISH h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 1 ∧
      z'.avail_out = 0 ∧ result.status = BUSY_STATE ∧ result.pending = 1 ∧
      result.bi_valid.toInt = 0 ∧ result.last_flush = -1 := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have extent := trees.base.size; have lower := trees.base.lit_lo; omega
  let d0 := { d with last_flush := Z_FINISH }
  let h0 := setD h ds d0
  have good0 := last_flush_good initial.good Z_FINISH
  have trees0 := last_flush_trees trees Z_FINISH
  have buffers0 := last_flush_buffers initial.good buffers Z_FINISH
  let staged := zlibHeaderReady h0 r ds pb z d0 buf
  obtain ⟨goodE, buffersE⟩ := header_ready_good_buffers good0 trees0 buffers0 initial.pendingOut
  have getPB : staged.bytes pb = some (zlibHeaderBytes buf) := by simp [staged, zlibHeaderReady]
  have getOut : staged.bytes ob = some output := by
    simpa only [staged, zlibHeaderReady, setD_bytes, ZStreamRef.put_bytes,
      upd_ne _ _ _ _ separate, h0, setD_bytes] using outGet
  have cursorE : (zlibHeaderState d0).pending_out = .ref (.blk pb) 0 :=
    initial.pendingOut.trans trees.base.pbuf
  have pointerE : ({ z with adler := 1 } : ZStream).next_out = .ref (.blk ob) oo := pointer
  have lowE : (zlibHeaderState d0).bi_valid.toInt < 8 := by
    change d.bi_valid.toInt < 8
    rw [initial.bits]
    decide
  have boundE : 0 + (zlibHeaderState d0).pending.toNat ≤ (zlibHeaderBytes buf).size := by
    change 2 ≤ (zlibHeaderBytes buf).size
    simpa only [zlibHeaderBytes, Array.size_set!] using room
  have nonzero : pendingLen (zlibHeaderState d0).pending ({ z with adler := 1 } : ZStream).avail_out ≠ 0 := by
    change pendingLen 2 z.avail_out ≠ 0
    rw [one]
    decide
  have raw := flush_pending_low_raw goodE.live.hz goodE.live.zst goodE.live.hs lowE pointerE cursorE
    getOut getPB (by simpa only [staged, zlibHeaderReady, h0, setD_ro, ZStreamRef.put_ro] using outRw)
    separate (by simpa only [] using outBound) boundE nonzero
  have rawRun : flush_pending (some r) staged =
      .ok ((), zlibHeaderFlushed h0 r ds pb ob oo z d0 buf output) := by
    simpa only [zlibHeaderFlushed, staged, zlibHeaderState, Nat.zero_add] using raw
  have pendingE := pending_bits_slice cursorE getPB boundE
  obtain ⟨_pb, produced, middle, z', result, _written, _remaining, _base, flushRun, goodA, buffersA,
      accountA, _sizes, _storage, amount, left, _lowA, fields, _reset, _bytes, _pendingA, _outputBits⟩ :=
    flush_pending_resume_raw_bits goodE buffersE pointerE lowE pendingE
  have heaps : middle = zlibHeaderFlushed h0 r ds pb ob oo z d0 buf output :=
    (Prod.mk.inj (Except.ok.inj (flushRun.symm.trans rawRun))).2
  have state : result = pendingState (zlibHeaderState d0) (.ref (.blk pb) 1) 1 := by
    have getD := goodA.live.hs
    rw [heaps] at getD
    simp only [zlibHeaderFlushed, one, pendingLen, show ((2 : UInt64) > (1 : UInt32).toUInt64) = True from by decide,
      ite_true, setD_dstates_same, show ((1 : UInt32).toNat) = 1 from rfl] at getD
    exact Option.some.inj getD.symm
  have count : produced = 1 := by
    rw [amount]
    change min 2 z.avail_out.toNat = 1
    rw [one]
    decide
  rw [count] at accountA left
  have outputZero : z'.avail_out = 0 := by
    apply UInt32.toNat_inj.mp
    have balance := accountA.2.2.2.1
    rw [one] at balance
    change z'.avail_out.toNat = 0
    change z'.avail_out.toNat + 1 = 1 at balance
    omega
  have header := public_default_header_run good0.live.hz initial.good.live.zst good0.live.hs
    initial.status initial.wrap initial.bits level initial.strategy initial.windowBits initial.start initial.pending
    trees.base.pbuf initial.pendingOut (by simpa only [h0, setD_bytes] using trees.base.bytes) room
    (by simpa only [h0, setD_ro] using trees.base.rw) pointer
    (by simpa only [h0, setD_bytes] using outGet) (by simpa only [h0, setD_ro] using outRw)
    separate outBound (by rw [one]; decide) (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
  have entry := public_default_finish_initial_entry initial (by rw [pointer]; intro impossible; cases impossible)
    (by rw [one]; decide) valid
  have run : deflate (some r) Z_FINISH h =
      .ok (Z_OK, setD middle ds { result with last_flush := -1 }) := by
    rw [entry, header]
    simp only [one, pendingLen, show ((2 : UInt64) > (1 : UInt32).toUInt64) = True from by decide,
      ite_true, show ((2 : UInt64) - (1 : UInt32).toUInt64 != 0) = true from rfl]
    rw [heaps, state]
    rfl
  refine ⟨_, z', _, run, last_flush_good goodA (-1), last_flush_buffers goodA buffersA (-1),
    accountA, outputZero, ?_, ?_, ?_, rfl⟩
  · rw [fields]
    rfl
  · rw [state]
    change (2 : UInt64) - (1 : UInt32).toUInt64 = 1
    decide
  · rw [fields]
    change d.bi_valid.toInt = 0
    rw [initial.bits]
    rfl
/-- The complete first public FINISH call from an initialized default
stream has a successful safety/accounting result at every positive raw
output capacity. One byte splits the header; exactly two bytes enters
compression with no output space left. Input length is unrestricted.
The call-history, full frame and format-refinement goals remain open. -/
theorem public_default_first_finish {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : StrategyBoundary h r ds z d input origin base [] config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (outputRoom : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) := by
  by_cases one : z.avail_out = 1
  · obtain ⟨after, z', result, run, goodA, buffersA, accountA, _emptyA, _statusA, _pendingA, bitsA, _lastA⟩ :=
      public_default_first_finish_one initial level buffers pointer one valid
    refine ⟨0, 1, Z_OK, after, z', result, run, goodA, buffersA, accountA, Or.inl rfl, ?_, ?_⟩
    · rw [bitsA]
      decide
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
  · have room : 2 ≤ z.avail_out.toNat := by
      have notOne : z.avail_out.toNat ≠ 1 := fun value => one (UInt32.toNat_inj.mp value)
      omega
    obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, bits, ended⟩ :=
      public_default_first_finish_header_fits initial level boundary frontier buffers pointer room memory valid
    exact ⟨used, 2 + produced, rc, after, z', result, run, goodA, buffersA, accountA, allowed, bits, ended⟩
end Zlib.Deflate.Engine.Proofs
