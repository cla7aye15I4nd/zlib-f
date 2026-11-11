import ZlibF.Spec.Public.Streams
import ZlibF.Spec.Public.Sequences
import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Proof.«deflate.c.universal-init»
import ZlibF.Proof.«deflate.c.universal-history»
import ZlibF.Proof.«deflate.c.universal-ledger-defs»
import ZlibF.Proof.«deflate.c.universal-call-phases»
import ZlibF.Proof.«deflate.c.universal-window»
import ZlibF.Proof.«trees.c.universal-spec»
import ZlibF.Proof.«deflate.c.init.general-main»
import ZlibF.Math.DeflateEncodingPrefix
import ZlibF.Math.DeflateSymbolTrace

/-!
# deflate.c: the universal invariant and the skeleton of result 3

Result 3 (`docs/progress.md`, Scope): `deflate` is safe and its output decodes to its input. The
public targets are `Goal.deflateInit2_`, `Goal.deflate` and `Goal.deflate_sequence`.

**One invariant.** `DInv` holds in every reachable state of a deflate stream, for every level,
`memLevel`, `windowBits`, strategy, tuning and header. It is established by `deflateInit2_` and
kept by every stream operation and by caller rebuffering. Other modules use only the interface
lemmas `DInv.*` below, never the fields.

**One ledger.** `Ledger` relates a data epoch (`DeflateDataTrace`) to the stream: the emitted bits
are a header and complete blocks that decode to a prefix of the accepted input, the current block
(symbols or stored window bytes) covers the next part, and the window holds the rest.

This file is the skeleton (`AGENTS.md`, proof workflow step 2). Every `sorry` is an open lemma,
listed in `docs/progress.md`, section "Core proof skeletons". The compositions at the end are
real proofs from these lemmas.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-! ## 1–2. The invariant and its proved interface

`DInv`, `Shape`, `Chains`, `Recorded`, `Symbols` and the proved interface lemmas are on `dev` in
`ZlibF/Proof/deflate.c.universal-invariant.lean`. `DInv.owned` and `DInv.rebuffer` are checked in `ZlibF/Proof/deflate.c.universal-history.lean`. -/



/-! ## 3. Initialization (`deflateInit2_`, `deflateReset`, `lm_init`) -/

/-- The version and stream-size refusal, before any read of the stream. -/
theorem init2_version (level method wb mem strategy : Int32) :
    ∀ h p version head size, VersionValue h version head → (head ≠ some 49 ∨ size ≠ 112) →
      C.run (Zlib.Deflate.deflateInit2_ p level method wb mem strategy version size) h =
        .ok (Z_VERSION_ERROR, h) :=
  Zlib.Deflate.Proofs.GeneralInit.init2_version level method wb mem strategy

/-- A `NULL` stream is refused. -/
theorem init2_null (level method wb mem strategy : Int32) :
    ∀ h version, VersionValue h version (some 49) →
      C.run (Zlib.Deflate.deflateInit2_ none level method wb mem strategy version 112) h =
        .ok (Z_STREAM_ERROR, h) :=
  Zlib.Deflate.Proofs.GeneralInit.init2_null level method wb mem strategy

/-- Every parameter tuple: refusal, state allocation failure, any of the four buffer
allocation failures with exact cleanup, or success with `DeflateInitial`. -/
theorem init2_main (level method wb mem strategy : Int32) :
    ∀ h r z version, Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h →
      r.get h = some z → DefaultOrNull z → VersionValue h version (some 49) →
      ∃ rc after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
          .ok (rc, after) ∧
        (match Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
        | none => rc = Z_STREAM_ERROR ∧ SameObjects (r.put h (preparedStream z)) after ∧
            after.nalloc = h.nalloc
        | some p =>
          if h.allocOk h.nalloc = false then
            rc = Z_MEM_ERROR ∧ after.nalloc = h.nalloc + 1 ∧
            SameObjects (r.put h (preparedStream z)) after
          else after.nalloc = h.nalloc + 5 ∧
            if (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) then
              rc = Z_OK ∧ DeflateInitial h after r p
            else rc = Z_MEM_ERROR ∧
              (∃ z', r.get after = some z' ∧ z'.state = none) ∧
              LiveChange h after (fun _ => False) (fun _ => False) ∧
              Frame h after (StreamRoot r)) :=
  Zlib.Deflate.Proofs.GeneralInit.init2_main level method wb mem strategy

/- `init2_inv` is checked on `dev`: `ZlibF/Proof/deflate.c.universal-init.lean`. -/

/-! ## 4. The engine under the invariant

Each lemma holds for every reachable state, every parameter tuple and every content of the
unwritten window and `prev` cells. They are the callees of `deflate_call`. -/

/- `fill_window` and `longest_match` are internal to batch B and checked on `dev`:
`fill_window_inv` and `longest_match_inserted` in `ZlibF/Proof/deflate.c.universal-window.lean`. -/

/- `FLUSH_BLOCK_ONLY` is checked on `dev` (batch C): `Block.flush_block_only_safe` in
`ZlibF/Proof/trees.c.universal-flush.lean` (explicit premises, the form the strategies use inside
their loops) and `Block.flush_block_dinv` in `ZlibF/Proof/trees.c.universal-spec.lean` (from
`DInv`), with `last` a `Bool`. Both take the room of the dynamic overlay (`DynamicOverlay`, F9)
as a premise; it is proved for `lit_bufsize ≥ 2048` (`memLevel ≥ 5`) and open for `memLevel` 1
to 4. That premise is the one open part of block emission. -/

/-- `deflate_stored` under the invariant: direct copies to the caller, window retention and
buffered stored blocks. -/
theorem stored_spec {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (level : d.level = 0) (flush : Int32) :
    ∃ bstate after z' d' used produced,
      C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ CallFrame h after r ds d z z' used produced := by
  sorry

/-- `deflate_fast` (levels 1 to 3, strategies 0, 1, 4). -/
theorem fast_spec {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (level : 1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3) (strategy : d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) (flush : Int32) :
    ∃ bstate after z' d' used produced,
      C.run (Zlib.Deflate.deflate_fast (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ CallFrame h after r ds d z z' used produced := by
  sorry

/-- `deflate_slow` (levels 4 to 9, strategies 0, 1, 4), with the lazy match state. -/
theorem slow_spec {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (level : 4 ≤ d.level.toInt) (strategy : d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) (flush : Int32) :
    ∃ bstate after z' d' used produced,
      C.run (Zlib.Deflate.deflate_slow (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ CallFrame h after r ds d z z' used produced := by
  sorry

/-- `deflate_rle` (strategy 3, nonzero level). -/
theorem rle_spec {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (level : 0 < d.level.toInt) (strategy : d.strategy.toInt = 3) (flush : Int32) :
    ∃ bstate after z' d' used produced,
      C.run (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ CallFrame h after r ds d z z' used produced := by
  sorry

/-- `deflate_huff` (strategy 2, nonzero level). -/
theorem huff_spec {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StrategyEntry h r z d) (level : 0 < d.level.toInt) (strategy : d.strategy.toInt = 2) (flush : Int32) :
    ∃ bstate after z' d' used produced,
      C.run (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      DInv after r ds z' d' ∧ StreamBuffers after r ∧ CallFrame h after r ds d z z' used produced := by
  sorry

/-! ## 5. One `deflate` call -/

/-- The clauses of `Goal.deflate` after the run and the invariant. -/
def CallClauses (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : DeflateState) (flush : Int32)
    (rc : Int32) (after : Heap) (z' : ZStream) (s' : DeflateState) (used : Nat) (out : List UInt8) : Prop :=
  StreamAccounting z z' used out.length ∧
  Bytes after z.next_out out.length out ∧
  z'.total_in = z.total_in + UInt64.ofNat used ∧
  z'.total_out = z.total_out + UInt64.ofNat out.length ∧
  (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
  (rc = Z_STREAM_ERROR ↔ DeflateRefuses z s flush) ∧
  (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
  (rc = Z_STREAM_END → flush = Z_FINISH ∧ s'.status = FINISH_STATE ∧
    z'.avail_in = 0 ∧ s'.pending = 0 ∧ s'.bi_valid = 0) ∧
  (rc = Z_BUF_ERROR → used = 0 ∧
    (out = [] ∨ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0))) ∧
  (¬ DeflateRefuses z s flush → z.avail_out = 0 → rc = Z_BUF_ERROR) ∧
  (¬ DeflateRefuses z s flush → z.avail_out ≠ 0 →
    ¬ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
    (rc = Z_BUF_ERROR ↔ z.avail_in = 0 ∧ s.pending = 0 ∧ flush ≠ Z_FINISH ∧
      deflateRank flush ≤ deflateRank s.last_flush)) ∧
  (flush = Z_FINISH → ¬ DeflateRefuses z s flush → z.avail_out ≠ 0 →
    ¬ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
    rc = Z_STREAM_END ∨ used ≠ 0 ∨ out ≠ []) ∧
  (rc = Z_OK ∨ rc = Z_STREAM_END → z'.msg = z.msg) ∧
  (rc = Z_BUF_ERROR → StaticString after z'.msg (errorText Z_BUF_ERROR.toInt)) ∧
  (rc = Z_STREAM_ERROR → 0 ≤ flush.toInt → flush.toInt ≤ 5 →
    StaticString after z'.msg (errorText Z_STREAM_ERROR.toInt)) ∧
  (z'.data_type = z.data_type ∨
    (z.data_type = Z_UNKNOWN ∧ (z'.data_type = Z_BINARY ∨ z'.data_type = Z_TEXT))) ∧
  BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) [⟨z.next_out, out.length⟩] ∧
  LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc

/-- **One `deflate` call** from the invariant: the refusals, the pending flush, the zlib and
gzip headers (extra, name, comment, header CRC, with interruption), dispatch to the five
strategies, the flush markers, `CLEAR_HASH` after a full flush, and the trailer. -/
theorem deflate_call {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (header : ActiveHeader h r) (flush : Int32) :
    ∃ rc after z' d' used out,
      C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
      DInv after r ds z' d' ∧ CallClauses h r ds z d flush rc after z' d' used out := by
  sorry

/-- The fields `deflateBound` reads, across one `deflate` call: level, `w_bits`, `hash_bits` and
`gzhead` are kept, `wrap` changes only with output (the trailer), and a call on a zlib or gzip
stream still in `INIT_STATE` or `GZIP_STATE` that is not refused and has output room delivers a
byte (the header goes to `pending` and `flush_pending` copies at least one byte). Used by
`bound_before_output`: the C `wraplen` tests `strstart ≠ 0`, the model tests the dictionary. -/
theorem call_frame {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush rc : Int32} (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (header : ActiveHeader h r)
    (run : C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after)) :
    ∃ z' d', r.get after = some z' ∧ after.dstates ds = some d' ∧
      d'.level = d.level ∧ d'.w_bits = d.w_bits ∧ d'.hash_bits = d.hash_bits ∧ d'.gzhead = d.gzhead ∧
      (z'.avail_out = z.avail_out → d'.wrap = d.wrap) ∧
      (0 < d.wrap.toInt → (d.status = INIT_STATE ∨ d.status = GZIP_STATE) →
        ¬ DeflateRefuses z d flush → z.avail_out ≠ 0 → z'.avail_out.toNat < z.avail_out.toNat) := by
  sorry

/-! ## 6. The other stream operations and the history -/

/-- The invariant after one stream operation of `StreamOperation .deflate`, with the frame and
ownership clauses of `StreamSequenceSafety`. Covers `deflate`, `deflateParams` (with its inner
`deflate(Z_BLOCK)`, slide or hash clearing), `deflateSetDictionary`, `deflatePrime`, `deflateReset`,
`deflateResetKeep`, `deflateSetHeader`, `deflateTune` (every value), `deflateGetDictionary`,
`deflatePending`, `deflateUsed`, `deflateBound` and `deflateBound_z`. -/
theorem operation_step {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {call : Call}
    (inv : DInv h r ds z d) (operation : StreamOperation .deflate r call) (args : StreamArguments h r call) :
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      (∃ ds' z' d', DInv after r ds' z' d') ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  sorry

/-- `deflateCopy` into a distinct destination establishes the invariant there. -/
theorem copy_inv {h after : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (run : C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h = .ok (Z_OK, after)) :
    ∃ ds' z' d', DInv after dest ds' z' d' := by
  sorry

/-- **Every reachable deflate state satisfies the invariant.** By induction on the history. -/
theorem reachable_inv {h : Heap} {r : ZStreamRef} (reach : StreamReachable .deflate h r) :
    ∃ ds z d, DInv h r ds z d := by
  generalize kind : StreamKind.deflate = k at reach
  induction reach with
  | inflateInit => cases kind
  | deflateInit fresh uniq globals get allocators ver run =>
    exact init2_inv fresh uniq globals get allocators ver run
  | rebuffer _ rebuffer _ ih =>
    obtain ⟨ds, z, d, inv⟩ := ih kind
    obtain ⟨z', _, inv'⟩ := inv.rebuffer rebuffer
    exact ⟨ds, z', d, inv'⟩
  | step _ _ operation args run ih =>
    subst kind
    obtain ⟨ds, z, d, inv⟩ := ih rfl
    obtain ⟨value', after', run', invAfter, -, -⟩ := operation_step inv operation args
    have same := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    exact invAfter
  | inflateCopy => cases kind
  | deflateCopy _ distinct get run ih =>
    obtain ⟨ds, z, d, inv⟩ := ih kind
    exact copy_inv inv distinct get run

/-- `deflateEnd` from the invariant (reuses `deflate_end_public`). -/
theorem end_from_inv {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) :
    ∃ rc after z', C.run (Zlib.Deflate.deflateEnd (some r)) h = .ok (rc, after) ∧
      (rc = Z_OK ∨ StreamKind.deflate = .deflate ∧ rc = Z_DATA_ERROR) ∧
      r.get after = some z' ∧ z'.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r) := by
  sorry

/-! ## 7. The ledger of a data epoch -/

/-! ### 7a. `ledger_step` split into independently provable lemmas

`LedgerAt`, `Ledger` and their parts are on `dev` (`deflate.c.universal-ledger-defs`). Each lemma
below is one cut of `deflate` (`deflate_phases`, batch C) or one callee. They share the shape:
the run returns, the delivered output grows by the bytes written to `next_out`, the accepted input
grows by the bytes read from `next_in`, and the ledger holds again. -/

/-- Entry phase: the pending flush moves pending bytes to the caller; the ledger is unchanged
in meaning. -/
theorem ledger_flush_pending {p : Api.DeflParams} {dict accepted delivered : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (ledger : LedgerAt p dict h r ds z d accepted delivered) (buffers : StreamBuffers h r)
    (out : z.next_out ≠ .null) :
    ∃ after z' d' produced bytes, C.run (Zlib.Deflate.flush_pending (some r)) h = .ok ((), after) ∧
      Bytes after z.next_out produced bytes ∧ CallFrame h after r ds d z z' 0 produced ∧
      LedgerAt p dict after r ds z' d' accepted (delivered ++ bytes) := by
  sorry

/-- Header phase: from the header phase to the data phase with no block yet (the zlib header
with `DICTID`, or the gzip header), or an interrupted header. -/
theorem ledger_header {p : Api.DeflParams} {dict delivered : List UInt8}
    {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (ledger : LedgerAt p dict h r ds z d [] delivered) (buffers : StreamBuffers h r)
    (header : ActiveHeader h r) (out : z.next_out ≠ .null) (room : z.avail_out ≠ 0)
    (phase : HeaderPhase d) (k : M Int32) :
    (∃ rc z' d' produced bytes, Zlib.Deflate.Universal.Call.headerPhase (some r) (some (.tab ds)) flush k h = .ok (rc, after) ∧
      Bytes after z.next_out produced bytes ∧ LedgerAt p dict after r ds z' d' [] (delivered ++ bytes)) ∨
    (∃ h2 z' d' produced bytes, (∀ k', Zlib.Deflate.Universal.Call.headerPhase (some r) (some (.tab ds)) flush k' h = k' h2) ∧
      d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ Bytes h2 z.next_out produced bytes ∧
      LedgerAt p dict h2 r ds z' d' [] (delivered ++ bytes)) := by
  sorry

/-- The strategy-entry premises shared by the five strategy lemmas. -/
structure LedgerEntry (p : Api.DeflParams) (dict accepted delivered inData : List UInt8)
    (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  ledger : LedgerAt p dict h r ds z d accepted delivered
  entry : StrategyEntry h r z d
  busy : d.status = BUSY_STATE
  input : Bytes h z.next_in z.avail_in.toNat inData

/-- The common conclusion of a strategy run. -/
def LedgerExit (p : Api.DeflParams) (dict accepted delivered inData : List UInt8)
    (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) {α : Type}
    (run : M α) : Prop :=
  ∃ value after z' d' used produced bytes, run h = .ok (value, after) ∧
    Bytes after z.next_out produced bytes ∧ CallFrame h after r ds d z z' used produced ∧
    LedgerAt p dict after r ds z' d' (accepted ++ inData.take used) (delivered ++ bytes)

/-- `fill_window` keeps the ledger: the read bytes join the accepted input and the lookahead;
a slide keeps the window/data relation and the block start. -/
theorem ledger_fill_window {p : Api.DeflParams} {dict accepted delivered inData : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (entry : LedgerEntry p dict accepted delivered inData h r ds z d) (level : d.level ≠ 0)
    (short : d.lookahead.toNat < 262) :
    LedgerExit p dict accepted delivered inData h r ds z d (Zlib.Deflate.fill_window (some (.tab ds))) := by
  sorry

/-- A block flush emits bits that decode to the open block's symbols: fixed, dynamic or stored
block, non-final (`BlockPrefix`) or final (`Blocks.last`). The three block types are the three
sub-lemmas `ledger_block_fixed`, `ledger_block_dynamic`, `ledger_block_stored`. -/
theorem ledger_flush_block {p : Api.DeflParams} {dict accepted delivered : List UInt8} {pre : List Bool}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {start : Nat} (last : Bool)
    (block : BlockState h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (level : 0 < d.level.toInt) (pending : d.pending = 0)
    (emitted : Emitted h d delivered pre) (recorded : Recorded h d xs)
    (window : WindowHolds h d (epochData p dict accepted))
    (startAt : BlockStartAt d (epochData p dict accepted) ((windowDictionary p dict).length + start))
    (trace : Trace (fun i => (epochData p dict accepted).getD i 0) ((windowDictionary p dict).length + start) xs)
    (covers : start + represented xs ≤ accepted.length) :
    ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat) (bytes : List UInt8) (blockBits : List Bool),
      C.run (Zlib.Deflate.FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      Bytes after z.next_out produced bytes ∧ Emitted after d' (delivered ++ bytes) (pre ++ blockBits) ∧
      (last = false → BlockPrefix (windowDictionary p dict) pre.length (accepted.take start) blockBits
        (accepted.take (start + represented xs))) ∧
      (last = true → ∀ rest, Blocks (windowDictionary p dict) (accepted.take start) (blockBits ++ rest) rest
        (accepted.take (start + represented xs))) := by
  sorry

/-- `deflate_fast` (levels 1 to 3): the recorded symbols mean the input they cover. -/
theorem ledger_fast {p : Api.DeflParams} {dict accepted delivered inData : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (entry : LedgerEntry p dict accepted delivered inData h r ds z d)
    (level : 1 ≤ d.level.toInt ∧ d.level.toInt ≤ 3) (strategy : d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    LedgerExit p dict accepted delivered inData h r ds z d (Zlib.Deflate.deflate_fast (some (.tab ds)) flush) := by
  sorry

/-- `deflate_slow` (levels 4 to 9), with the lazy literal. -/
theorem ledger_slow {p : Api.DeflParams} {dict accepted delivered inData : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (entry : LedgerEntry p dict accepted delivered inData h r ds z d)
    (level : 4 ≤ d.level.toInt) (strategy : d.strategy.toInt ≠ 2 ∧ d.strategy.toInt ≠ 3) :
    LedgerExit p dict accepted delivered inData h r ds z d (Zlib.Deflate.deflate_slow (some (.tab ds)) flush) := by
  sorry

/-- `deflate_rle` (strategy 3). -/
theorem ledger_rle {p : Api.DeflParams} {dict accepted delivered inData : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (entry : LedgerEntry p dict accepted delivered inData h r ds z d)
    (level : 0 < d.level.toInt) (strategy : d.strategy.toInt = 3) :
    LedgerExit p dict accepted delivered inData h r ds z d (Zlib.Deflate.deflate_rle (some (.tab ds)) flush) := by
  sorry

/-- `deflate_huff` (strategy 2). -/
theorem ledger_huff {p : Api.DeflParams} {dict accepted delivered inData : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (entry : LedgerEntry p dict accepted delivered inData h r ds z d)
    (level : 0 < d.level.toInt) (strategy : d.strategy.toInt = 2) :
    LedgerExit p dict accepted delivered inData h r ds z d (Zlib.Deflate.deflate_huff (some (.tab ds)) flush) := by
  sorry

/-- `deflate_stored` (level 0): buffered stored blocks and the direct copy to the caller. -/
theorem ledger_stored {p : Api.DeflParams} {dict accepted delivered inData : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (entry : LedgerEntry p dict accepted delivered inData h r ds z d) (level : d.level = 0) :
    LedgerExit p dict accepted delivered inData h r ds z d (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) := by
  sorry

/-- `Z_PARTIAL_FLUSH` marker: `_tr_align` appends an empty fixed block, a complete non-final
block, after an emptied current block. -/
theorem ledger_align {p : Api.DeflParams} {dict accepted delivered : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (ledger : LedgerAt p dict h r ds z d accepted delivered) (busy : d.status = BUSY_STATE)
    (empty : d.sym_next = 0 ∧ d.block_start.toInt = d.strstart.toNat) :
    ∃ after d', C.run (Zlib.Trees.«_tr_align» (some (.tab ds))) h = .ok ((), after) ∧
      LedgerAt p dict after r ds z d' accepted delivered := by
  sorry

/-- `Z_SYNC_FLUSH` and `Z_FULL_FLUSH` marker: an empty stored block, a complete non-final block
ending on a byte boundary; after a full flush the hash is cleared (`CLEAR_HASH`). -/
theorem ledger_empty_stored {p : Api.DeflParams} {dict accepted delivered : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (ledger : LedgerAt p dict h r ds z d accepted delivered) (busy : d.status = BUSY_STATE)
    (empty : d.sym_next = 0 ∧ d.block_start.toInt = d.strstart.toNat) :
    ∃ after d', C.run (Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0) h = .ok ((), after) ∧
      LedgerAt p dict after r ds z d' accepted delivered := by
  sorry

/-- Trailer phase: with the checksum and the count of the accepted input in the stream record,
the trailer completes the stream (`rest = []`). -/
theorem ledger_trailer {p : Api.DeflParams} {dict accepted delivered : List UInt8}
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (ledger : LedgerAt p dict h r ds z d accepted delivered) (finish : d.status = FINISH_STATE)
    (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (adler : p.wrap = .zlib → z.adler.toNat = (ZlibF.Spec.adler32 accepted).toNat)
    (crc : p.wrap = .gzip → z.adler.toNat = (ZlibF.Spec.crc32 accepted).toNat)
    (count : z.total_in.toNat % 2 ^ 32 = accepted.length % 2 ^ 32) :
    ∃ rc after z' d' produced bytes,
      C.run (Zlib.Deflate.Universal.Call.trailerPhase (some r) (some (.tab ds)) Z_FINISH) h = .ok (rc, after) ∧
      Bytes after z.next_out produced bytes ∧ d'.wrap.toInt ≤ 0 ∧
      LedgerAt p dict after r ds z' d' accepted (delivered ++ bytes) := by
  sorry

/-! ### 7b. The ledger across a data epoch -/

/-- The ledger at initialization: nothing emitted, an empty window. -/
theorem ledger_init {h after : Heap} {r : ZStreamRef} {version : BPtr} {level method wb mem strategy : Int32}
    {p : Api.DeflParams} (params : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p)
    (domain : InitDomain h r version)
    (run : C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h = .ok (Z_OK, after)) :
    Ledger p after r {} := by
  sorry

theorem ledger_rebuffer {h after : Heap} {r : ZStreamRef} {p : Api.DeflParams} {log : DataLog}
    (ledger : Ledger p h r log) (rebuffer : Rebuffer h after r) : Ledger p after r log := by
  sorry

/-- A preset dictionary before any data: the window and the zlib dictionary identifier. -/
theorem ledger_dictionary {h after : Heap} {r : ZStreamRef} {p : Api.DeflParams} {log : DataLog}
    {dict : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
    (ledger : Ledger p h r log) (noInput : log.input = []) (noOutput : log.output = [])
    (args : StreamArguments h r (.deflateSetDictionary (some r) dict n)) (read : Bytes h dict n.toNat bytes)
    (run : C.run (Zlib.Deflate.deflateSetDictionary (some r) dict n) h = .ok (rc, after)) :
    Ledger p after r
      { log with dictionary := if rc = Z_OK then log.dictionary ++ bytes else log.dictionary } := by
  sorry

/-- **One `deflate` call keeps the ledger.** Assembly of the lemmas of 7a along
`deflate_phases`, with the refusals and the `Z_BUF_ERROR` returns (nothing accepted, nothing
emitted) and the strategy dispatch. -/
theorem ledger_step {h after : Heap} {r : ZStreamRef} {p : Api.DeflParams} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (ledger : Ledger p h r log) (step : DataStep .deflate h after r flush rc input output used) :
    Ledger p after r (deflateLogStep log flush rc input output used) := by
  sorry

/-- Every data epoch has a ledger. -/
theorem trace_ledger {level method wb mem strategy : Int32} {p : Api.DeflParams} {r : ZStreamRef}
    {h : Heap} {log : DataLog}
    (params : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p)
    (trace : DeflateDataTrace level method wb mem strategy r h log) : Ledger p h r log := by
  induction trace with
  | init domain run => exact ledger_init params domain run
  | caller _ rebuffer ih => exact ledger_rebuffer ih rebuffer
  | step _ step ih => exact ledger_step ih step
  | dictionary _ noInput noOutput args read run ih => exact ledger_dictionary ih noInput noOutput args read run

/-- A finished epoch encodes its accepted input. -/
theorem ledger_finished {h : Heap} {r : ZStreamRef} {p : Api.DeflParams} {log : DataLog}
    {level method wb mem strategy : Int32}
    (trace : DeflateDataTrace level method wb mem strategy r h log) (ledger : Ledger p h r log)
    (ended : log.result = Z_STREAM_END) : DecodesFor p log.dictionary log.output log.input := by
  sorry

/-- A completed sync or full flush: all input consumed, the output ends at a flush point, and
after a full flush the rest of a finished continuation decodes from an empty history. -/
theorem ledger_flush {level method wb mem strategy : Int32} {p : Api.DeflParams} {r : ZStreamRef}
    {h after : Heap} {log : DataLog} {flush rc : Int32} {input output : List UInt8} {used : Nat} {z' : ZStream}
    (params : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p)
    (trace : DeflateDataTrace level method wb mem strategy r h log)
    (step : DataStep .deflate h after r flush rc input output used)
    (kind : flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH) (ok : rc = Z_OK)
    (get : r.get after = some z') (room : z'.avail_out ≠ 0) :
    let log₁ := deflateLogStep log flush rc input output used
    z'.avail_in = 0 ∧ FlushedFor p log₁.dictionary log₁.output log₁.input ∧
    (flush = Z_FULL_FLUSH → ∀ h₂ log₂, DeflateDataRun r after log₁ h₂ log₂ →
      log₂.result = Z_STREAM_END →
      ∃ tail, Deflate.Prefix [] (log₂.output.drop log₁.output.length) tail
        (log₂.input.drop log₁.input.length)) := by
  sorry

/-- `adler` after a successful call is the checksum of the accepted input. -/
theorem ledger_adler {level method wb mem strategy : Int32} {p : Api.DeflParams} {r : ZStreamRef}
    {h after : Heap} {log : DataLog} {flush rc : Int32} {input output : List UInt8} {used : Nat} {z' : ZStream}
    (params : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p)
    (trace : DeflateDataTrace level method wb mem strategy r h log)
    (step : DataStep .deflate h after r flush rc input output used)
    (ok : rc = Z_OK ∨ rc = Z_STREAM_END) (get : r.get after = some z') :
    let accepted := log.input ++ input.take used
    (p.wrap = .zlib → z'.adler.toNat = (ZlibF.Spec.adler32 accepted).toNat) ∧
    (p.wrap = .gzip → z'.adler.toNat = (ZlibF.Spec.crc32 accepted).toNat) := by
  sorry

/-- Before any output, `deflateBound` returns the model bound (machine arithmetic and the
wrapper length of the actual header state). -/
theorem bound_before_output {level method wb mem strategy : Int32} {p : Api.DeflParams} {r : ZStreamRef}
    {h : Heap} {log : DataLog} (n : UInt64)
    (params : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p)
    (trace : DeflateDataTrace level method wb mem strategy r h log) (noOutput : log.output = []) :
    let bound := UInt64.ofNat (min (({ Api.DeflState.fresh p with dict := some log.dictionary }).bound
      n.toNat) (2 ^ 64 - 1))
    C.run (Zlib.Deflate.deflateBound_z (some r) n) h = .ok (bound, h) ∧
    C.run (Zlib.Deflate.deflateBound (some r) n) h = .ok (bound, h) := by
  sorry

/-- **Bound adequacy**: with the finish-only bound as room, a `Z_FINISH` call ends the stream.
Needs the worst-case expansion of every strategy and block choice against the bound. -/
theorem completes : DeflateCompletes := by
  sorry

/-! ## 8. The public targets from the lemmas -/

theorem deflateInit2_proof : Goal.deflateInit2_ := fun level method wb mem strategy =>
  ⟨init2_version level method wb mem strategy, init2_null level method wb mem strategy,
   init2_main level method wb mem strategy⟩

theorem deflate_proof : Goal.deflate := by
  intro h r i z s flush reach good buffers header
  obtain ⟨ds, z₀, d, inv⟩ := reachable_inv reach
  obtain ⟨rfl, rfl, rfl⟩ := inv.unique good
  obtain ⟨rc, after, z', d', used, out, run, invAfter, clauses⟩ := deflate_call inv buffers header flush
  exact ⟨rc, after, z', d', used, out, run, invAfter.dgood, clauses⟩

theorem deflate_sequence_proof : Goal.deflate_sequence := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, completes⟩
  · intro h r reach
    obtain ⟨ds, z, d, inv⟩ := reachable_inv reach
    exact ⟨ds, z, d, inv.dgood, inv.defAlloc⟩
  · intro h r call reach _fits operation args
    obtain ⟨ds, z, d, inv⟩ := reachable_inv reach
    obtain ⟨value, after, run, ⟨ds', z', d', invAfter⟩, frame, live⟩ := operation_step inv operation args
    exact ⟨value, after, run, ⟨ds', z', d', invAfter.dgood, invAfter.defAlloc⟩, frame, live⟩
  · intro h r reach
    obtain ⟨ds, z, d, inv⟩ := reachable_inv reach
    exact end_from_inv inv
  · intro level method wb mem strategy p r h log params trace ended
    exact ledger_finished trace (trace_ledger params trace) ended
  · intro level method wb mem strategy p r h log after flush rc input output used z' params trace step kind ok get room
    exact ledger_flush params trace step kind ok get room
  · intro level method wb mem strategy p r h log after flush rc input output used z' params trace step ok get
    exact ledger_adler params trace step ok get
  · intro level method wb mem strategy p r h log n params trace noOutput
    exact bound_before_output n params trace noOutput

end Zlib.Deflate.Universal
