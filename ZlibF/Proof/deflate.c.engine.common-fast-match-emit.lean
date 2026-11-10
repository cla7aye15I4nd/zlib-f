import ZlibF.Proof.«deflate.c.engine.memory-fast-borrow-private»
import ZlibF.Proof.«deflate.c.engine.common-fast-match-advance-source»
import ZlibF.Proof.«deflate.c.engine.common-fast-match-advance»
import ZlibF.Proof.«deflate.c.engine.common-fast-symbol-meaning»

/-! # Actual immediate match tally restores the initialized fast content -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual fast match tally followed by its immediate source advancement. -/
def fastMatchEmit (s : DeflateStatePtr) (head : UInt32) : M (Bool × UInt32) := do
  let d ← ldDeflateState s
  let full ← tally_dist s (d.strstart - d.match_start) (d.match_length - MIN_MATCH_u)
  let next ← fastMatchAdvance s head
  pure (full, next)

/-- The actual tally stores the exact selected match and leaf frequencies;
both actual advancement branches restore current content and the stronger
EOF frontier. The same heap has an extended input trace and exact symbol
count. A full symbol buffer is permitted here; publication follows next. -/
theorem fast_match_emit_search_boundary {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (buffers : StreamBuffers h r)
    (previous : d.prev_length = 2) (noDeferred : d.match_available = 0)
    (selected : 3 ≤ d.match_length.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat) (head : UInt32) :
    ∃ candidate after result,
      fastMatchEmit (some (.tab ds)) head h = .ok ((d.sym_next + 3 == d.sym_end, candidate), after) ∧
      ContentBoundary after r ds z result input origin base (xs ++ [fastMatchSymbol d]) ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ SlowRecordFrame d result ∧
      result.match_length = 0 ∧ result.match_available = 0 ∧ result.prev_length = 2 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat = d.sym_next.toNat + 3 ∧ result.sym_end = d.sym_end ∧
      ByteFrame h after (DeflateOwned ds d) := by
  have matching := cut.matching selected (by rw [previous]; exact selected)
  have consumed := cut.clipped selected
  have window : d.w_size.toNat ≤ 32768 := by
    rw [cut.good.inv.wsize]
    exact Nat.pow_le_pow_right (by decide) cut.good.inv.wbits_hi
  obtain ⟨distanceEq, positive, distanceBound, lengthEq, lengthBound⟩ :=
    fast_current_tally_bounds matching selected window
  let distance := d.strstart - d.match_start
  let length := d.match_length - MIN_MATCH_u
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have space := literal_room cut.good.inv strict
  let packed := matchBytes buf d distance.toUInt16 length.toUInt8
  let dt := matchSymbolState d distance length
  let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
  have goodT : DGood ht r ds z dt := match_good_after cut.good trees distance length space
  have chainsT : HeapChains ht dt (d.strstart.toNat + 1) :=
    pending_write_chains cut.good cut.chains trees.base.pbuf packed 0
  have getT : ht.bytes w = some wa :=
    pending_window_frame cut.good cut.window trees.base.pbuf cut.bytes packed dt
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (d.sym_next + 3 == d.sym_end, ht) :=
    tally_match_run trees.base distance length positive distanceBound space
  obtain ⟨candidate, after, result, advance, goodA, chainsA, endA, winA, bytesA, zeroA,
      startA, lookA, endpoint, formA, fieldsA, bytesEqA, storageA, _shapeA, _fullA,
      _liveA, _allocA, _nextA⟩ :=
    fast_match_advance_frontier_full_storage goodT chainsT cut.window getT selected cut.length
      consumed cut.range room (cut.primed (by omega)) head
  change result.strstart.toNat = d.strstart.toNat + d.match_length.toNat at startA
  change result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat at lookA
  change fillEnd result = fillEnd d at endpoint
  have frame : SlowRecordFrame d result := by
    unfold SlowRecordFrame
    rw [fieldsA]
    rfl
  have insertA : result.insert = 0 := by
    rw [frame]
    exact cut.ready (by omega)
  have availableA : result.match_available = 0 := by rw [fieldsA]; exact noDeferred
  have previousA : result.prev_length = 2 := by rw [fieldsA]; exact previous
  have ledgerT : SymbolLedger packed dt (xs ++ [fastMatchSymbol d]) :=
    ledger_match trees.base ledger space distance length positive distanceBound lengthBound
  have ledgerA : SymbolLedger packed result (xs ++ [fastMatchSymbol d]) :=
    ledgerT.keep (by rw [fieldsA]) (by rw [fieldsA]) (by rw [fieldsA]) (by rw [fieldsA])
  have getPacked : after.bytes pb = some packed := by rw [bytesEqA]; simp [ht]
  change 1 ≤ distance.toNat at positive
  have representedMatch : (fastMatchSymbol d).bytes = d.match_length.toNat := by
    change (if distance.toNat = 0 then 1 else length.toNat + 3) = _
    rw [if_neg (by omega)]
    change length.toNat = d.match_length.toNat - 3 at lengthEq
    omega
  have credit : deferredCredit d = 0 := by simp [deferredCredit, noDeferred]
  have creditA : deferredCredit result = 0 := by simp [deferredCredit, availableA]
  have blockA : result.block_start = d.block_start := by rw [frame]
  have balanceA : BlockBalance result (xs ++ [fastMatchSymbol d]) (deferredCredit result) := by
    unfold BlockBalance at balance ⊢
    rw [credit] at balance
    rw [creditA, represented_snoc, representedMatch, blockA, startA]
    omega
  have symbolsA := symbol_boundary_of_ledger goodA (by rw [fieldsA]; exact trees.base.pbuf)
    getPacked ledgerA balanceA
  have traceA := fast_match_trace cut previous noDeferred selected
  have storage := (pending_state_byte_frame h ds pb d dt packed trees.base.pbuf).trans
    (storageA.weaken (fun _ equal => Or.inl equal))
  have owned := stream_owned_keys cut.good goodA
    (by rw [frame]) (by rw [frame]) (by rw [frame]) (by rw [frame])
  have buffersA := stream_buffers_private_read cut.good.live.hz goodA.live.hz buffers storage
    (fun k own => (stream_owned_deflate cut.good k).mpr own) owned (stream_accounting_zero z)
      ((Zlib.Deflate.BorrowProofs.Private.stable_fastMatchAdvance _ _ _ _ _ advance).trans
        (show ht.libcErrorBorrow = h.libcErrorBorrow from rfl))
  have countA : result.sym_next.toNat = d.sym_next.toNat + 3 := by
    have same : result.sym_next = dt.sym_next := by rw [fieldsA]
    rw [same]
    exact literal_count trees.base space 0
  refine ⟨candidate, after, result, ?_, ?_, endA, buffersA, frame, zeroA, availableA, previousA,
    startA, lookA, endpoint, countA, by rw [frame], storage⟩
  · dsimp only [distance, length] at tally
    unfold fastMatchEmit
    simp only [bind_app, ldDeflateState_tab cut.good.live.hs, tally, advance, pure_app]
  · refine ⟨⟨⟨goodA, chainsA, ?_, ?_, ?_, symbolsA, ?_⟩, ?_, ?_, ?_⟩, traceA, ?_⟩
    · rw [endpoint]
      have windowA : result.window_size = d.window_size := by rw [frame]
      rw [windowA]
      exact cut.range
    · refine ⟨by rw [zeroA]; decide, ?_⟩
      intro impossible
      rw [zeroA] at impossible
      change 3 ≤ 0 at impossible
      omega
    · intro available
      exact False.elim (available availableA)
    · refine ⟨w, wa, winA, bytesA, ?_, fun _ => formA⟩
      intro i fit
      rw [endpoint] at fit
      exact cut.view i fit
    · simp [insertA]
    · simpa only [insertA, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chainsA
    · intro _
      exact insertA
    · simp only [pendingCredit, availableA, ite_true, Nat.add_zero]
      rw [represented_snoc, representedMatch, startA]
      have account := cut.accounted
      simp only [pendingCredit, noDeferred, ite_true, Nat.add_zero] at account
      omega

end Zlib.Deflate.Engine.Proofs
