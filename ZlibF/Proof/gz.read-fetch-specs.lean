import ZlibF.Proof.«gz.read-avail»

/-!
# gz read side: the statements of `gz_look`, `gz_decomp` and `gz_fetch`

The three helpers are proved separately (`gz.read-look`, `gz.read-decomp`, `gz.read-fetch`). This module fixes
their statements, so that `gz_fetch_safe_of` can be proved from the two callee statements at the same time as
the callees.

Two facts of the source shape the statements.

1. **Buffered output past `GZ_OFF_MAX`.** `gz_look`'s transparent path sets `x.have = avail_in` with `x.pos`
   unchanged, and `gz_fetch`'s COPY path (patch 0004) loads one byte when `x.pos = GZ_OFF_MAX`. So after these
   helpers `x.pos + x.have` may pass `GZ_OFF_MAX`, and the pending skip may coexist with buffered output. The post
   is `GzInvOut`: the invariant of the record without its buffered output (`GzInvUpToOutput`), with the window of
   the buffered output inside `out`. The callers (`gz_read`, `gzgets`, `gz_skip`) consume or drop the output.
2. **Termination of `gz_fetch`** over empty gzip members. Each round of its loop either stops or passes through
   `gz_look` (LOOK → GZIP) or a member end (GZIP → LOOK). The measure is the input left: the read budget of the
   descriptor plus `avail_in` (`inputLeft`). With a budget (M7) neither helper raises it (without one, `gz_avail`
   raises `avail_in` freely); a member decoded from a freshly reset
   stream (inflate mode `HEAD`) to its end takes at least one byte (`GzDecompSpec`, last clause). This is a
   functional fact about `inflate` that the safety of `gz_fetch` needs.
3. **Termination of `gz_read`.** The read budget never rises (`BudgetAcc s.fd fs fs' 0` in all three statements), and
   the input left never rises. A `0` from `gz_fetch` with no output and not at the end of the input leaves
   `how = LOOK` only after a stall of `gz_look`: a non-blocking read delivered 1 to 3 bytes (`again ∧ avail_in < 4`).
   Those bytes moved from the budget into `avail_in`, so the input left is unchanged, but the budget fell by at least
   one (`BudgetAcc s.fd fs fs' 1`). With `GzReadInv.againEof` a stall has `eof = 0`, so `gz_avail` did read. Every
   other `0` in LOOK has `eof ≠ 0` and `avail_in = 0`. So a trip of `gz_read` that copies nothing either ends the
   call, leaves output or the end of the input for the next trip, or lowers the budget. Copy trips need more: output
   of a single byte per fetch would take about `2·len` trips, past the fuel for `len` near `2^63`. So a fetch fills its
   buffer (`2·size ≥ 16` bytes) unless it fails, reaches `GZ_OFF_MAX`, ends the input, or lowers `fetchRank` by 2.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The buffered output of a reader lies inside `out`, and no output means a NULL or any `next`. -/
def OutWindow (s : GzState) : Prop :=
  s.x.have ≠ 0 → ∃ c, s.x.next = padv s.out c ∧ c + s.x.have.toNat ≤ 2 * s.size.toNat

/-- **The invariant after a fetching helper**: `GzInv` of the record without its buffered output, and the
buffered output inside `out`. -/
def GzInvOut (h : Heap) (i : Nat) (s : GzState) : Prop :=
  GzInvUpToOutput h i s ∧ OutWindow s

/-- The input left to a reader: the read budget of its descriptor (0 when unbudgeted) plus `avail_in`. -/
def inputLeft (fs : Fs) (s : GzState) : Nat :=
  (if 0 ≤ s.fd.toInt then (fs.readBudget s.fd.toInt.toNat).getD 0 else 0) + s.strm.avail_in.toNat

/-- The embedded inflate stream is freshly reset: mode `HEAD`, no held bits and `last = 0` (`inflateReset` clears
them). With held bits (`inflatePrime` after `inflateReset2(-15)`), or with `last ≠ 0` and `wrap = 0` (`TYPEDO` then goes
to `CHECK`), a call from `HEAD` can reach the stream end using no input. -/
def InflateAtHead (h : Heap) (s : GzState) : Prop :=
  ∃ k st, s.strm.state = some (.inflate k) ∧ h.istates k = some st ∧ st.mode = HEAD ∧ st.bits = 0 ∧
    st.last = 0

open Classical in
/-- **The rank of a reader** for the termination of `gz_read`: 4 per byte of input left, 1 per byte of read budget,
2 while a gzip member is under way past its head (`how = GZIP` and the stream not `InflateAtHead`), and 2 until the
transparent copy mode. Neither `gz_decomp` nor `gz_fetch` raises it with a budget. A member that ends with little
output pays with this rank: from the head it took input (4), past the head its flag drops (2). A stall of `gz_look`
moves bytes from the budget into `avail_in`: the input left stays, the budget falls. -/
noncomputable def fetchRank (fs : Fs) (h : Heap) (s : GzState) : Nat :=
  4 * inputLeft fs s + (if 0 ≤ s.fd.toInt then (fs.readBudget s.fd.toInt.toNat).getD 0 else 0) +
    (if s.how = GZIP ∧ ¬ InflateAtHead h s then 2 else 0) + (if s.how = GZ_COPY then 0 else 2)

/-- The message of the embedded stream is `NULL` or a string literal of the sources (`inflateInit2_` and
`inflateReset` clear it, `inflate` sets literals). `gz_decomp` hands it to `gz_error`. **Open**: to become a clause of
the reader invariant. -/
def MsgLit (s : GzState) : Prop :=
  s.size ≠ 0 → s.strm.msg = .null ∨ ∃ j, j < strTable.size ∧ s.strm.msg = .ref (.str j) 0

/-- The record fields a fetching helper keeps. -/
def FetchKeeps (s s' : GzState) : Prop :=
  s'.mode = s.mode ∧ s'.fd = s.fd ∧ s'.skip = s.skip ∧ s'.x.pos = s.x.pos ∧
    (s.size ≠ 0 → s'.size = s.size ∧ s'.out = s.out ∧ s'.«in» = s.«in»)

/-- **`gz_look`** on a reader with no buffered output, in state LOOK (its callers, `gz_fetch` and `gzdirect`, call it
only there; from COPY with no input left it returns 0 with `how = COPY`). The read budget never rises. A `0` that leaves
`how = LOOK` is at the end of the input (`eof ≠ 0`, `avail_in = 0`) or a stall that read at least one byte, so the
budget fell by at least one. A `0` in COPY has consumed the pending input and buffered only what fits before
`GZ_OFF_MAX` (patch 0004): `x.pos + x.have ≤ GZ_OFF_MAX`, and nothing is buffered only at `x.pos = GZ_OFF_MAX`.
A `-1` leaves `how = LOOK`, no buffered output and an error recorded (`gz_error`, or the error `gz_avail` refused). -/
def GzLookSpec : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToOutput h i s → s.x.have = 0 → FileSystem fs →
    s.mode = GZ_READ → s.how = LOOK → MsgLit s →
    RunSafe (Zlib.Gzread.gz_look (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvOut ∧
      (HasBudget fs s.fd → HasBudget fs' s.fd) ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧ BudgetAcc s.fd fs fs' 0 ∧
      ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧ MsgLit s' ∧
        (HasBudget fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
        (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) ∧
        (s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
        (r = -1 → s'.how = LOOK ∧ s'.err ≠ Z_OK ∧ s'.x.have = 0) ∧
        (r = 0 → (s'.how = LOOK ∧ s'.x.have = 0 ∧
            ((s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ BudgetAcc s.fd fs fs' 1)) ∨
          (s'.how = GZIP ∧ s'.x.have = 0 ∧ InflateAtHead after s') ∨
          (s'.how = GZ_COPY ∧ s'.strm.avail_in = 0 ∧
            (s'.x.have ≠ 0 ∨ s'.x.pos.toInt = 9223372036854775807) ∧
            s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807))

/-- **`gz_decomp`** into the output region `out` (from the record's `out` in `gz_fetch`, then no caller region is
written; the caller's buffer in `gz_read`), as the skeleton states it, with the fields kept and the progress clauses `gz_fetch` needs.
The last two clauses serve `gz_read`: the rank (`fetchRank`) does not rise, and the output region is filled unless the
call failed, reached the end of the input, or lowered the rank by 2 (a member ended: from the head it took input, past
the head its flag drops). -/
def GzDecompSpec : Prop :=
  ∀ (i : Nat) (out : Region) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToOutput h i s → FileSystem fs →
    s.mode = GZ_READ → s.how = GZIP → MsgLit s →
    (s.strm.next_out = out.pointer ∧ s.strm.avail_out.toNat = out.length ∧ out.length ≠ 0 ∧
      Writable h out.pointer out.length) →
    ((∀ b, ByteRoot out.pointer b → ¬ GzOwned h i s b) ∨ out.pointer = s.out) →
    RunSafe (Zlib.Gzread.gz_decomp (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s (if out.pointer = s.out then [] else [out]) fs' after GzInvUpToOutput ∧
      (HasBudget fs s.fd → HasBudget fs' s.fd) ∧ (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      BudgetAcc s.fd fs fs' 0 ∧
      ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧ MsgLit s' ∧
        (HasBudget fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
        (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) ∧
        (s'.x.have ≠ 0 → ∃ c, s'.x.next = padv out.pointer c ∧ c + s'.x.have.toNat ≤ out.length) ∧
        (s'.how = GZIP ∨ s'.how = LOOK) ∧ (r = -1 → s'.err ≠ Z_OK) ∧
        (r = 0 → s'.x.have ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
          (s'.how = LOOK ∧ (HasBudget fs s.fd → InflateAtHead h s → s.err ≠ Z_STREAM_END →
            inputLeft fs' s' < inputLeft fs s))) ∧
        (HasBudget fs s.fd → s.err ≠ Z_STREAM_END → fetchRank fs' after s' ≤ fetchRank fs h s) ∧
        (HasBudget fs s.fd → s.err ≠ Z_STREAM_END → s'.x.have.toNat = out.length ∨ r = -1 ∨
          (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs' after s' + 2 ≤ fetchRank fs h s)

/-- **`gz_fetch`** on a reader with no buffered output: the skeleton statement with the post `GzInvOut`, the kept
fields, and its progress. The premise `err ≠ Z_STREAM_END` holds on every handle (`gz_error` never records that
code); so does `how = GZ_COPY → avail_in = 0` (`gz_look` and `gzseek` zero `avail_in` when they set COPY), and so does
`MsgLit` (the embedded stream's message is `NULL` or a literal). All three are to be discharged by clauses of the
invariant (**open**). Its progress (`GzFetchProgress` as it holds: a `0` result leaves output, the end of the input, or
`how = LOOK` after a stall of `gz_look` that lowered the read budget by at least one). The budget and the input left
never rise. The last clauses serve `gz_read`'s termination and its return to `GzInv`: the record keeps the open
premises; a `-1` records an error; the buffered output passes `GZ_OFF_MAX` only by the one byte loaded at
`x.pos = GZ_OFF_MAX` (patch 0004); the rank does not rise; a `0` with no output is at the end of the input or lowers
the rank; and output is a full buffer (`2·size`) unless the call failed, the output reaches `GZ_OFF_MAX`, the input
ended, or the rank fell by 2. -/
def GzFetchSafe : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToOutput h i s → s.x.have = 0 → FileSystem fs →
    s.mode = GZ_READ → s.err ≠ Z_STREAM_END → (s.how = GZ_COPY → s.strm.avail_in = 0) → MsgLit s →
    RunSafe (Zlib.Gzread.gz_fetch (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvOut ∧
      (HasBudget fs s.fd → HasBudget fs' s.fd) ∧ (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      BudgetAcc s.fd fs fs' 0 ∧
      ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧ MsgLit s' ∧
        (HasBudget fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
        (s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
        (r = 0 → s'.x.have ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
          (s'.how = LOOK ∧ BudgetAcc s.fd fs fs' 1)) ∧
        s'.err ≠ Z_STREAM_END ∧ (s'.how = GZ_COPY → s'.strm.avail_in = 0) ∧ (r = -1 → s'.err ≠ Z_OK) ∧
        (s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807 ∨
          (s'.x.pos.toInt = 9223372036854775807 ∧ s'.x.have.toNat ≤ 1)) ∧
        (HasBudget fs s.fd → fetchRank fs' after s' ≤ fetchRank fs h s) ∧
        (HasBudget fs s.fd → s'.x.have = 0 → r = 0 →
          (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ fetchRank fs' after s' < fetchRank fs h s) ∧
        (HasBudget fs s.fd → s'.x.have ≠ 0 → s'.x.have.toNat = 2 * s'.size.toNat ∨ r = -1 ∨
          9223372036854775807 ≤ s'.x.pos.toInt + s'.x.have.toNat ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
          fetchRank fs' after s' + 2 ≤ fetchRank fs h s)

end ZlibF.Spec.Public.GzRead
