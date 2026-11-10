import ZlibF.Proof.«inflate.c.slow-copy-fragment-safe»
import ZlibF.Proof.«inflate.c.slow-pending-output-public»
import ZlibF.Proof.«inflate.c.slow-public-output-preservation»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec ZlibF.Math.LZ77Copy
open SlowMatchCompletion SlowCopyTokenPath
set_option autoImplicit false
set_option maxRecDepth 10000
/-- The actual complete public return suffix on a produced pending token.
The real allocation failure is retained as its own result. -/
def PendingPublicReturn {L D : List Nat} (p : CopySyntax L D) (c : Ctx)
    (h : Heap) (s : InflateState) (l : IL) (bs : List UInt8) (future residual : List Bool)
    (r : ZStreamRef) (zs : Nat) (_z : ZStream) : Prop :=
  ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
    Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
    stream.next_out = l.put ∧ stream.avail_out = l.left ∧
    (∀ dest off array, l.put = .ref dest off → Space.get h dest = some array → Space.get after dest = some array) ∧
    ((PendingSyntax p state residual ∧ PendingFieldsFrame s state ∧
      (natBits state.bits.toNat state.hold.toNat ++ bytesBits bs) ++ future = residual ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_) ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM))

/-- The real return source preserves the emitted output object and
restores its public cursor, in addition to persistent token meaning. -/
theorem pending_return_source {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future residual : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s) (bits : l.bits.toNat ≤ 39)
    (phase : PendingSyntax p s residual) (source : FutureSource l bs future residual) :
    PendingPublicReturn p c h s l bs future residual r zs z := by
  obtain ⟨rc, after, stream, state, actual, current, finalTables, finalPending, semantic⟩ :=
    inflate_leave_pending_source E good allocator statics buffers tables pending bits phase source
  have cursors := inflate_leave_cursors E good pending allocator statics buffers tables bits actual current.live.hz
  refine ⟨rc, after, stream, state, actual, current, finalTables, finalPending, cursors.2.2.1, cursors.2.2.2, ?_, semantic⟩
  intro dest off array put get
  exact inflate_leave_output_array E good pending allocator buffers bits put get actual

/-- Exact token bytes and cursors are paired with actual public leave for
every input/output wait. Completion instead supplies the real successful
LEN prefix for the next original Symbols continuation. -/
def PublicCopyFragmentResult {L D : List Nat} (p : CopySyntax L D) (c : Ctx)
    (h : Heap) (s : InflateState) (l : IL) (bs dict : List UInt8) (future : List Bool)
    (r : ZStreamRef) (zs : Nat) (z : ZStream) (dest : BRef) (off : Nat) (output : Array UInt8) : Prop :=
  (∃ after state regs used residual,
    ParsePoint p h s l bs future r zs z after state regs used residual ∧
    runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after) ∧
    regs.have_ = 0 ∧ ParserWaitingMode state ∧ Space.get after dest = some output ∧
    regs.left = l.left ∧ regs.put = l.put ∧ DispatchBuffers after r regs (bs.drop used) ∧
    regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
    runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) ∧
    PendingPublicReturn p c after state regs (bs.drop used) future residual r zs z) ∨
  (∃ regs used after state array steps made,
    (MatchSteps c l h regs after steps ∨ runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after)) ∧
    used ≤ bs.length ∧ steps ≤ made ∧ made = min (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue) l.left.toNat ∧
    Good after r zs z state ∧ DataTablesSafe after state ∧ BitInv after regs (bs.drop used) ∧
    InflateDictionary after state dict ∧ FutureSource regs (bs.drop used) future p.rest ∧
    state.offset.toNat = distBases.getD p.distanceSymbol 0 + p.distanceValue ∧
    state.length.toNat + made = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
    state.was.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
    state.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0 +
      D.getD p.distanceSymbol 0 + distExtras.getD p.distanceSymbol 0) ∧
    Space.get after dest = some array ∧ array.size = output.size ∧ Space.ro after dest = false ∧
    regs.left.toNat + made = l.left.toNat ∧ regs.put = .ref dest (off + made) ∧
    regs.next = inputAdvance l.next used ∧ Separate regs.next regs.have_.toNat regs.put regs.left.toNat ∧
    writtenBytes array (off + made) (l.out_.toNat - l.left.toNat + made) =
      copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue) made
        (writtenBytes output off (l.out_.toNat - l.left.toNat)) ∧
    Token.Step L D dict (writtenBytes output off (l.out_.toNat - l.left.toNat)) p.input p.rest
      (copyBack dict (distBases.getD p.distanceSymbol 0 + p.distanceValue)
        (lengthBases.getD (p.symbol - 257) 0 + p.lengthValue)
        (writtenBytes output off (l.out_.toNat - l.left.toNat))) false ∧
    (∃ heap ps parsed, ParsePoint p h s l bs future r zs z heap ps parsed used p.rest ∧
      ps.mode = MATCH ∧ 0 < ps.length.toNat ∧
      runX (inflate_dispatch c) l h = runX (inflate_MATCH c) parsed heap ∧
      MatchSteps c parsed heap regs after steps ∧ EmitRegFrame parsed regs ∧ DecodeStateFrame ps state) ∧
    DispatchBuffers after r regs (bs.drop used) ∧ regs.bits.toNat ≤ 39 ∧ after.static = h.static ∧
    ((state.mode = LEN ∧ made = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧ MatchSteps c l h regs after steps) ∨
     (state.mode = MATCH ∧ 0 < state.length.toNat ∧ regs.left = 0 ∧ PendingSyntax p state p.rest ∧
      runX (inflate_dispatch c) regs after = .ok ((.error Ex.leave, regs), after) ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) ∧
      PendingPublicReturn p c after state regs (bs.drop used) future p.rest r zs z)))

/-- One coherent source endpoint: parse arbitrary current input, emit
any available output prefix, and execute the actual public return suffix
on each wait with produced safety resources and persistent syntax. -/
theorem slow_copy_fragment_public_prefix {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs dict : List UInt8} {future residual : List Bool}
    {lref dref : CodeRef} {lo lextent doff dextent : Nat} {lca dca : Array Code}
    {dest : BRef} {off : Nat} {output : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (lpointer : s.lencode = .ref lref lo) (lget : Space.get h lref = some lca)
    (lmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS lca lo s.lenbits.toNat lextent L)
    (lstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS lca lo s.lenbits.toNat)
    (dpointer : s.distcode = .ref dref doff) (dget : Space.get h dref = some dca)
    (dmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS dca doff s.distbits.toNat dextent D)
    (dstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS dca doff s.distbits.toNat)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (initialBits : l.bits.toNat ≤ 39) (phase : PendingSyntax p s residual) (source : FutureSource l bs future residual)
    (entry : ParserWaitingMode s ∨ s.mode = LEN_)
    (slow : s.mode = LEN ∨ s.mode = LEN_ → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (dictionary : InflateDictionary h s dict)
    (put : l.put = .ref dest off) (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : off + l.left.toNat ≤ output.size) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : l.out_.toNat - l.left.toNat ≤ off)
    (privateWindow : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (available : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    PublicCopyFragmentResult p c h s l bs dict future r zs z dest off output := by
  have lengthWidth : L.getD p.symbol 0 ≤ 15 := by
    by_cases inside : p.symbol < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact lmeaning.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ p.symbol)]
  have distanceWidth : D.getD p.distanceSymbol 0 ≤ 15 := by
    by_cases inside : p.distanceSymbol < D.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact dmeaning.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : D.length ≤ p.distanceSymbol)]
  have fragment := slow_copy_fragment_prefix_safe E good tables lpointer lget lmeaning lstable dpointer dget dmeaning dstable
    buffers pending initialBits phase source entry slow dictionary put get write room count produced privateWindow separate available
  rcases fragment with waiting | outputFragment
  · obtain ⟨after, state, regs, used, residual, point, actual, empty, mode, arrayGet, left, putEq, finalBuffers, bits, static⟩ := waiting
    have currentStatics : Zlib.Crc32.Proofs.StaticsOK after := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, static] using statics
    have env : Env c after r zs z state := ⟨E.strm, E.st, point.good.live.hz, point.good.live.hs⟩
    have invariant := pending_parser_safe point.phase mode (by rw [point.frame, pending.sane]) lengthWidth distanceWidth
    have returned : PendingPublicReturn p c after state regs (bs.drop used) future residual r zs z :=
      pending_return_source env point.good invariant allocator currentStatics finalBuffers (fun _ => point.tables)
        bits point.phase point.source
    exact Or.inl ⟨after, state, regs, used, residual, point, actual, empty, mode, arrayGet, left, putEq,
      finalBuffers, bits, static, dispatch_one_leave actual, returned⟩
  · obtain ⟨regs, used, after, state, array, steps, made, path, bound, stepBound, madeEq,
      finalGood, finalTables, finalB, finalDict, finalSource, offset, length, was, back,
      arrayGet, size, ro, left, finalPut, cursor, finalSeparate, bytes, token, provenance,
      finalBuffers, bits, static, outcome⟩ := outputFragment
    refine Or.inr ⟨regs, used, after, state, array, steps, made, path, bound, stepBound, madeEq,
      finalGood, finalTables, finalB, finalDict, finalSource, offset, length, was, back,
      arrayGet, size, ro, left, finalPut, cursor, finalSeparate, bytes, token, provenance,
      finalBuffers, bits, static, ?_⟩
    rcases outcome with done | pendingOutput
    · exact Or.inl done
    · obtain ⟨mode, positive, zero, finalPhase, dispatchWait, loop⟩ := pendingOutput
      obtain ⟨heap, ps, parsed, point, _parsedMode, _positive, _cut, _path, _emit, frame⟩ := provenance
      have currentSane : state.sane = 1 := by rw [frame, point.frame, pending.sane]
      have currentStatics : Zlib.Crc32.Proofs.StaticsOK after := by
        simpa only [Zlib.Crc32.Proofs.StaticsOK, static] using statics
      have env : Env c after r zs z state := ⟨E.strm, E.st, finalGood.live.hz, finalGood.live.hs⟩
      have returned : PendingPublicReturn p c after state regs (bs.drop used) future p.rest r zs z :=
        pending_return_source env finalGood (pending_match_safe mode finalPhase positive currentSane)
          allocator currentStatics finalBuffers (fun _ => finalTables) bits finalPhase finalSource
      exact Or.inr ⟨mode, positive, zero, finalPhase, dispatchWait, loop, returned⟩

#print axioms pending_return_source
#print axioms slow_copy_fragment_public_prefix
end Zlib.Inflate.Proofs.SlowInputFragment
