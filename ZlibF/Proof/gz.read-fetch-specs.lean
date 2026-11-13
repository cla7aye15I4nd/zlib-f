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

/-- **M7 with a bound**: a finite read budget below `2^61` bytes. A loop of the model has `2^64` trips of fuel;
each round of `gz_decomp` and `gz_fetch` takes input or ends, so a budget below `2^61` keeps them within it. Without
the bound a source of about `2^70` bytes of empty gzip members runs `gz_fetch` out of fuel (`docs/progress.md`). -/
def ReadsBounded (fs : Fs) (fd : Int32) : Prop :=
  ReadsFinite fs fd ∧ (fs.readBudget fd.toInt.toNat).getD 0 < 2 ^ 61

/-- The embedded inflate stream is freshly reset: mode `HEAD` and no held bits (`inflateReset` clears them). With
held bits (`inflatePrime` after `inflateReset2(-15)`) a call from `HEAD` can reach the stream end using no input. -/
def InflateAtHead (h : Heap) (s : GzState) : Prop :=
  ∃ k st, s.strm.state = some (.inflate k) ∧ h.istates k = some st ∧ st.mode = HEAD ∧ st.bits = 0

/-- The record fields a fetching helper keeps. -/
def FetchKeeps (s s' : GzState) : Prop :=
  s'.mode = s.mode ∧ s'.fd = s.fd ∧ s'.skip = s.skip ∧ s'.x.pos = s.x.pos ∧
    (s.size ≠ 0 → s'.size = s.size ∧ s'.out = s.out ∧ s'.«in» = s.«in»)

/-- **`gz_look`** on a reader with no buffered output, in state LOOK (its callers, `gz_fetch` and `gzdirect`, call it
only there; from COPY with no input left it returns 0 with `how = COPY`). -/
def GzLookSpec : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToOutput h i s → s.x.have = 0 → FileSystem fs →
    s.mode = GZ_READ → s.how = LOOK →
    RunSafe (Zlib.Gzread.gz_look (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvOut ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
      (ReadsBounded fs s.fd → ReadsBounded fs' s.fd) ∧
      ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧ (ReadsFinite fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
        (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) ∧
        (s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
        (r = 0 → (s'.how = LOOK ∧ s'.x.have = 0) ∨ (s'.how = GZIP ∧ s'.x.have = 0 ∧ InflateAtHead after s') ∨
          (s'.how = GZ_COPY ∧ s'.x.have ≠ 0))

/-- **`gz_decomp`** into the output region `out` (from the record's `out` in `gz_fetch`, then no caller region is
written; the caller's buffer in `gz_read`), as the skeleton states it, with the fields kept and the progress clauses `gz_fetch` needs. -/
def GzDecompSpec : Prop :=
  ∀ (i : Nat) (out : Region) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToOutput h i s → FileSystem fs →
    s.mode = GZ_READ → s.how = GZIP →
    (s.strm.next_out = out.pointer ∧ s.strm.avail_out.toNat = out.length ∧ out.length ≠ 0 ∧
      Writable h out.pointer out.length) →
    ((∀ b, ByteRoot out.pointer b → ¬ GzOwned h i s b) ∨ out.pointer = s.out) →
    RunSafe (Zlib.Gzread.gz_decomp (gzSt i)) fs h (ReadsBounded fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s (if out.pointer = s.out then [] else [out]) fs' after GzInvUpToOutput ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧ (ReadsBounded fs s.fd → ReadsBounded fs' s.fd) ∧
      ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧ (ReadsFinite fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
        (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) ∧
        (s'.x.have ≠ 0 → ∃ c, s'.x.next = padv out.pointer c ∧ c + s'.x.have.toNat ≤ out.length) ∧
        (s'.how = GZIP ∨ s'.how = LOOK) ∧
        (r = 0 → s'.x.have ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨
          (s'.how = LOOK ∧ (ReadsFinite fs s.fd → InflateAtHead h s → s.err ≠ Z_STREAM_END →
            inputLeft fs' s' < inputLeft fs s)))

/-- **`gz_fetch`** on a reader with no buffered output: the skeleton statement with the post `GzInvOut`, the kept
fields, and its progress. The premise `err ≠ Z_STREAM_END` holds on every handle (`gz_error` never records that
code); so does `how = GZ_COPY → avail_in = 0` (`gz_look` and `gzseek` zero `avail_in` when they set COPY). Both are to be
discharged by clauses of the invariant (**open**). Its progress (`GzFetchProgress` as it holds: a `0` result leaves output, the end of the input, or
`how = LOOK` after `gz_look` found too little input). -/
def GzFetchSafe : Prop :=
  ∀ (i : Nat) (h : Heap) (fs : Fs) (s : GzState), GzInvUpToOutput h i s → s.x.have = 0 → FileSystem fs →
    s.mode = GZ_READ → s.err ≠ Z_STREAM_END → (s.how = GZ_COPY → s.strm.avail_in = 0) →
    RunSafe (Zlib.Gzread.gz_fetch (gzSt i)) fs h (ReadsBounded fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvOut ∧
      (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧ (ReadsBounded fs s.fd → ReadsBounded fs' s.fd) ∧
      ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧
        (s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
        (r = 0 → s'.x.have ≠ 0 ∨ (s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ s'.how = LOOK)

end ZlibF.Spec.Public.GzRead
