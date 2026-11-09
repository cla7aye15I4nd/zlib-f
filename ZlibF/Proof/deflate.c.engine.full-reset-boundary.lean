import ZlibF.Proof.«deflate.c.engine.buffered-boundary»
import ZlibF.Proof.«deflate.c.life.reset»
import ZlibF.Proof.«deflate.c.engine.full-storage»
import ZlibF.Proof.«deflate.c.engine.pending-bits»

/-! # Actual FULL hash and position reset retains the input endpoint and footprint -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual FULL_FLUSH clear/reset statements retain the content
boundary after a completed empty block. Resetting the window origin to
its absolute block base preserves the logical input history. The real
nonfinal execution must establish empty lookahead and settled credit. -/
theorem full_clear_reset_boundary {h : Heap} {r : ZStreamRef} {ds q origin base : Nat}
    {z : ZStream} {d : DeflateState} {qa : Array UInt16}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (head : d.head = .ref (.blk q) 0) (get : h.words q = some qa)
    (look : d.lookahead = 0) (available : d.match_available = 0) :
    let result : DeflateState := { d with slid := 0, strstart := 0, block_start := 0, insert := 0 }
    let after := setD (setW h q (clearHead qa d.hash_size.toNat)) ds result
    (do
      CLEAR_HASH (some (.tab ds))
      if (← rd (some (.tab ds)) (·.lookahead)) == 0 then
        wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 })) h =
          .ok ((), after) ∧
      BufferedBoundary after r ds z result input base base [] config ∧
      base = origin + d.strstart.toNat := by
  dsimp only
  let result : DeflateState := { d with slid := 0, strstart := 0, block_start := 0, insert := 0 }
  let after := setD (setW h q (clearHead qa d.hash_size.toNat)) ds result
  obtain ⟨w, p, q0, wa, pa, qa0, env, _H⟩ := heap_chains_environment boundary.good boundary.chains
  have qEq : q0 = q := by
    simpa only [head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using env.headp.symm
  subst q0
  have qaEq : qa0 = qa := Option.some.inj (env.hwords.symm.trans get)
  subst qa0
  have hashPositive : 1 ≤ d.hash_size.toNat := by
    rw [boundary.good.inv.hsize]
    exact Nat.two_pow_pos _
  have goodW := boundary.good.words_set q (clearHead qa d.hash_size.toNat) qa get (size_clearHead _ _)
  have inv : DStInv (setW h q (clearHead qa d.hash_size.toNat)) ds result :=
    { goodW.inv with blocks := goodW.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodR : DGood after r ds z result := goodW.setD' rfl goodW.live.status inv (by trkeep)
  have chainsR : HeapChains after result 0 := by
    refine ⟨w, p, q, wa, pa, clearHead qa d.hash_size.toNat,
      env.win, env.prevp, head, env.wbytes, ?_, ?_, ?_⟩
    · simpa only [after, setD_words, setW, upd_ne _ _ _ _ env.hne.symm] using env.pwords
    · simp only [after, setD_words, setW_words_same]
    · apply chains_empty
      intro k hk
      have zero := clear_head_zero qa d.hash_size.toNat (by omega) env.hsize k hk
      simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]
  obtain ⟨pb, buf, trees, ledger, _balance⟩ := boundary.symbols
  have ledgerR : SymbolLedger buf result [] := ledger.keep rfl rfl rfl rfl
  have symbolsR : SymbolBoundary after ds result [] :=
    symbol_boundary_of_ledger goodR trees.base.pbuf trees.base.bytes ledgerR
      (by simp [BlockBalance, result, represented, deferredCredit, available])
  have historyR : LazyHistory input base result := by
    refine ⟨boundary.history.1, ?_⟩
    intro large
    have nonzero := (boundary.history.2 large).2.1
    exact False.elim (nonzero available)
  have dataR : ∃ wb wbbytes, result.window = .ref (.blk wb) 0 ∧ after.bytes wb = some wbbytes ∧
      (∀ i, i < fillEnd result → bfn wbbytes i = input (base + i)) ∧
      (3 ≤ result.lookahead.toNat → InsHForm result.hash_shift result.hash_mask (bfn wbbytes) result.strstart.toNat result.ins_h) := by
    refine ⟨w, wa, env.win, env.wbytes, ?_, ?_⟩
    · intro i bound
      simp [fillEnd, result, look] at bound
    · intro large
      simp [result, look] at large
  have contentR : ContentBoundary after r ds z result input base base [] := by
    refine ⟨⟨⟨goodR, chainsR, ?_, historyR, ?_, symbolsR, dataR⟩, ?_, ?_, ?_⟩,
      boundary.trace, ?_⟩
    · simp [fillEnd, result, look]
    · intro nonzero
      exact False.elim (nonzero available)
    · simp [result]
    · simpa only [result, UInt32.toNat_zero, Nat.sub_zero] using chainsR
    · intro large
      simp [result, look] at large
    · simp [result, pendingCredit, available, represented]
  refine ⟨?_, ⟨contentR, boundary.configuration, ?_, boundary.bits, boundary.strict, ?_, boundary.empty_cursor⟩, ?_⟩
  · have run := clearHash_run boundary.good.live.hs head get hashPositive env.hsize
    simp only [bind_app, run, rdD_eq, setD_dstates_same, look, BEq.rfl, ite_true,
      wrD_eq, setD_setD]
  · exact ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩
  · change HeapChains after result (min result.strstart.toNat (fillEnd result - 2))
    have zero : min result.strstart.toNat (fillEnd result - 2) = 0 := by simp [result, fillEnd, look]
    rw [zero]
    exact chainsR
  · have account := boundary.accounted
    simpa only [pendingCredit, available, ite_true, represented, Nat.add_zero] using account

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual full reset changes only the state and hash-head allocation.
Caller buffers, bit output and allocation ledgers survive this reset. -/
theorem full_clear_reset_effects {h : Heap} {r : ZStreamRef} {ds q origin base : Nat}
    {z : ZStream} {d : DeflateState} {qa : Array UInt16}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (head : d.head = .ref (.blk q) 0) (get : h.words q = some qa)
    (look : d.lookahead = 0) (available : d.match_available = 0) :
    let result : DeflateState := { d with slid := 0, strstart := 0, block_start := 0, insert := 0 }
    let after := setD (setW h q (clearHead qa d.hash_size.toNat)) ds result
    StreamBuffers after r ∧ ByteSizes h after ∧ ConfigFrame d result ∧ Shape h after ∧
      Frame h after (fun x => x = ds ∨ x = q) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      (∀ bits, PendingBits h d bits → PendingBits after result bits) := by
  dsimp only
  let result : DeflateState := { d with slid := 0, strstart := 0, block_start := 0, insert := 0 }
  let cleared := setW h q (clearHead qa d.hash_size.toNat)
  let after := setD cleared ds result
  have reset := (full_clear_reset_boundary boundary head get look available).2.1
  have frame : ByteFrame h after (fun x => x = ds) :=
    (byte_frame_setW h q _ _).trans (byte_frame_setD cleared ds result)
  have owned := stream_owned_keys boundary.good reset.good rfl rfl rfl rfl
  have buffersA := stream_buffers_private_read boundary.good.live.hz reset.good.live.hz buffers frame
    (fun x equal => (stream_owned_deflate boundary.good x).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  have kept : ∀ ref : BRef, Space.get after ref = Space.get h ref := by
    intro ref
    have state : cleared.dstates ds = some d := boundary.good.live.hs
    rw [byte_view_setD_depth state (show result.depth = d.depth from rfl) ref]
    cases ref <;> rfl
  have sizes : ByteSizes h after := ⟨fun ref a old => ⟨a, (kept ref).trans old, rfl⟩, fun _ => rfl⟩
  have shapeW := shape_setW get (clearHead qa d.hash_size.toNat)
  have shape := shapeW.trans (shape_setD (h := cleared) boundary.good.live.hs result)
  have fw : Frame h cleared (fun x => x = ds ∨ x = q) :=
    full_frame_weaken (word_store_full_frame h q _) (fun _ equal => Or.inr equal)
  have fd : Frame cleared after (fun x => x = ds ∨ x = q) :=
    full_frame_weaken (state_store_full_frame cleared ds result) (fun _ equal => Or.inl equal)
  refine ⟨buffersA, sizes, rfl, shape, full_frame_trans_shape fw fd shapeW, rfl, rfl, ?_⟩
  intro bits pending
  obtain ⟨w, p, q0, pb, blocks⟩ := boundary.good.inv.blocks
  obtain ⟨buf, getB, sizeB⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  rw [pending_bits_cursor_value cursor getB pending]
  exact pending_bits_slice (d := result) cursor getB (by rw [sizeB, ← blocks.psize]; exact bound)

end Zlib.Deflate.Engine.Proofs
