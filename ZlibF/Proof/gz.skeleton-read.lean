import ZlibF.Proof.«gz.skeleton-model»
import ZlibF.Proof.«gz.read-close»
import ZlibF.Proof.«gzread.c.skip-have»
import ZlibF.Proof.«gz.read-assembly»
import ZlibF.Proof.«gz.read-getc-step»
import ZlibF.Proof.«gz.read-gets-step»
import ZlibF.Proof.«gz.read-direct-step»

/-!
# gz file interface, safety skeleton: the read side (skeleton)

Open lemmas of `gzread.c` (owner: the deflate owner, read side). Each is a statement with `sorry`. The internal
helpers are stated on a handle in `GzInv` or, inside a reading call, in `GzInvUpToOutput` (the buffered output
may be in the caller's buffer until `gz_read` resets it: local patch for R-4). The public lemmas have the shape
`GzCallSafe` used by `Goal.gz_sequence_safety`. The six public read leaves are closed by the `dev` theorems of the
same statement (`GzRead.gzread_step`, `GzRead.gzfread_step`, `GzRead.gzgetc_step`, `GzRead.gzungetc_step`,
`GzRead.gzgets_step`, `GzRead.gzdirect_step`).

The codec steps are embedded through `GzReadInv.codec` (`StreamReachable .inflate`): `gz_look`'s
`inflateInit2_` is the `inflateInit` constructor, `inflate` and `inflateReset` are `step`s, and the gz writes of
`next_in`/`avail_in`/`next_out`/`avail_out` between them are `rebuffer`s. `Zlib.Gzlib.Spec.Uniq` is
`Zlib.Inflate.Spec.Uniq` (`gz_uniq_iff_inflate`, `Iff.rfl`).
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Internal helpers -/

/-- `gz_load(state, buf, len, &have)` (M1): `-1` or `0`, `have ≤ len`, only `[buf, buf + len)` written, errors
through `gz_error`. Termination: each `read` returns at most what is asked; the loop stops at `len` or at a
result `≤ 0` (no M7). -/
theorem gz_load_safe (i : Nat) (buf : BPtr) (len : UInt32) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToOutput h i s) (hfs : FileSystem fs) (hbuf : Writable h buf len.toNat) :
    RunSafe (Zlib.Gzread.gz_load (gzSt i) buf len) fs h True fun r fs' after =>
      (r.1 = 0 ∨ r.1 = -1) ∧ r.2.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧
      GzPost h i s [⟨buf, len.toNat⟩] fs' after GzInvUpToOutput := by
  sorry

/-- `gz_avail(state)`: refills `in` (the compaction branch is dead: every caller has `next_in == in` or
`avail_in == 0`, still proved); the input window of `GzReadInv.input` is kept. -/
theorem gz_avail_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToOutput h i s) (hfs : FileSystem fs) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzread.gz_avail (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvUpToOutput := by
  sorry

/-- `gz_look(state)`: on first use allocates `in` (`want`) and `out` (`2·want`) and runs `inflateInit2(31)`
(the `inflateInit` step of the inflate history); on failure frees both and records `Z_MEM_ERROR` (ledger:
nothing new); COPY copies `avail_in ≤ size` bytes into `out` and sets `x.next = out`. -/
theorem gz_look_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hhave : s.x.have = 0) :
    RunSafe (Zlib.Gzread.gz_look (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  sorry

/-- `gz_decomp(state)`: `inflate` steps in the inflate history (`StreamArguments`: `next_in` window in `in`,
`next_out` window `out` the output region given by the caller); afterwards `x.next = next_out - x.have` inside
`out`. Terminates: every `inflate` call consumes input or produces output, or the loop exits. -/
theorem gz_decomp_safe (i : Nat) (out : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToOutput h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hgz : s.how = GZIP)
    (hout : s.strm.next_out = out.pointer ∧ s.strm.avail_out.toNat = out.length ∧ Writable h out.pointer out.length)
    (hsep : ∀ b, ByteRoot out.pointer b → ¬ StreamOwned h (gzStrm i) b ∧ b ≠ i) :
    RunSafe (Zlib.Gzread.gz_decomp (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [out] fs' after GzInvUpToOutput ∧
      ∀ s', after.gzstates i = some s' → s'.x.have ≠ 0 →
        ∃ c, s'.x.next = padv out.pointer c ∧ c + s'.x.have.toNat ≤ out.length := by
  sorry

/-- `gz_fetch(state)`: the LOOK/COPY/GZIP dispatcher. COPY sets `x.next = out` before the load (patch 0003,
R-2). Termination needs M7: over empty gzip members the loop only consumes input. -/
theorem gz_fetch_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hhave : s.x.have = 0) :
    RunSafe (Zlib.Gzread.gz_fetch (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  sorry

/-- `gz_skip_have(state)`: consumes `min(have, skip)` buffered bytes. Relies on local patches for R-3/R-4
(`x.next += 0` on a pointer that was never written or that points into freed caller memory) and F-1. -/
theorem gz_skip_have_safe (i : Nat) (h : Heap) (s : GzState) (inv : GzInv h i s) (hm : s.mode = GZ_READ) :
    ∃ after s', C.run (Zlib.Gzread.gz_skip_have (gzSt i)) h = .ok ((), after) ∧ GzInv after i s' ∧
      after = putGz h i s' ∧ s'.skip.toInt + s'.x.pos.toInt = s.skip.toInt + s.x.pos.toInt :=
  ZlibF.Spec.Public.gz_skip_have_safe i h s inv hm

/-- `gz_skip(state)`: skip decreases, or end of input; termination needs M7. Called only with `skip ≠ 0` (every
caller tests it); with `skip = 0` the do-while still fetches and may exceed `posHave`. -/
theorem gz_skip_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ) (hskip : s.skip ≠ 0) :
    RunSafe (Zlib.Gzread.gz_skip (gzSt i)) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  sorry

/-- `gz_read(state, buf, len)`: the buffered path, the direct load into the caller's buffer and the direct inflate
into the caller's buffer; at most `len` bytes, only `[buf, buf + len)` written; `x.next` reset off the caller's
buffer (local patch for R-4); `x.pos` bounded (local patch for F-1). Termination needs M7. -/
theorem gz_read_safe (i : Nat) (buf : BPtr) (len : UInt64) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_READ)
    (hbuf : len = 0 ∨ GzRange h i s buf len.toNat true) :
    RunSafe (Zlib.Gzread.gz_read (gzSt i) buf len) fs h (ReadsFinite fs s.fd) fun r fs' after =>
      r.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧ GzPost h i s [⟨buf, len.toNat⟩] fs' after GzInv := by
  sorry

/-! ## Public calls (shape `GzCallSafe`) -/

/-- `gzread`: `int`/`unsigned` checks, then `gz_read`. Relies on local patches for F-1 and R-4. -/
theorem gzread_step (i : Nat) (buf : BPtr) (len : UInt32) :
    GzCallSafe i (.gzread (some (.in_gzstate_x i)) buf len) :=
  GzRead.gzread_step i buf len

/-- `gzfread`: the `size_t` product check, then `gz_read`. Relies on local patches for F-1 and R-4. -/
theorem gzfread_step (i : Nat) (buf : BPtr) (size nitems : UInt64) :
    GzCallSafe i (.gzfread buf size nitems (some (.in_gzstate_x i))) :=
  GzRead.gzfread_step i buf size nitems

/-- `gzgetc`: the buffered byte (`x.next` inside `out`) or `gz_read` into a local block (freed: ledger). Relies
on the local patch for F-1. -/
theorem gzgetc_step (i : Nat) : GzCallSafe i (.gzgetc (some (.in_gzstate_x i))) :=
  GzRead.gzgetc_step i

/-- `gzgetc_` is `gzgetc` (definitionally: same arguments, regions and M7 premise). -/
theorem gzgetc__step (i : Nat) : GzCallSafe i (.gzgetc_ (some (.in_gzstate_x i))) :=
  gzgetc_step i

/-- `gzungetc`: `gz_look` and `gz_skip` first, then the push back inside `out` (slide, room check);
`x.pos ≥ -2·size`. -/
theorem gzungetc_step (i : Nat) (c : Int32) : GzCallSafe i (.gzungetc c (some (.in_gzstate_x i))) :=
  GzRead.gzungetc_step i c

/-- `gzgets`: `memchr` bounded by `min(have, left)`, the copy and the final NUL inside `[buf, buf + len)`. -/
theorem gzgets_step (i : Nat) (buf : BPtr) (len : Int32) :
    GzCallSafe i (.gzgets (some (.in_gzstate_x i)) buf len) :=
  GzRead.gzgets_step i buf len

/-- `gzdirect`: one `gz_look` and `gz_skip_have` on a reader with nothing buffered. Relies on local patches for
R-3 and R-4. -/
theorem gzdirect_step (i : Nat) : GzCallSafe i (.gzdirect (some (.in_gzstate_x i))) :=
  GzRead.gzdirect_step i

/-- `gzclose_r`: refuses a writer; otherwise `inflateEnd` (part 3 of the inflate sequence goal) when buffers
exist, frees `out`, `in`, the message, the path and the record, and closes the descriptor, which is released
whatever `close` returns (M4). Closed on `dev`: `GzRead.gzclose_r_step_safe` (`gz.read-close`) is this statement
written out, with `GzRead.Close.Released`, which is `GzReleased` by definition. -/
theorem gzclose_r_step (i : Nat) : GzCloseSafe i (.gzclose_r (some (.in_gzstate_x i))) :=
  GzRead.gzclose_r_step_safe i

end ZlibF.Spec.Public.GzSkeleton
