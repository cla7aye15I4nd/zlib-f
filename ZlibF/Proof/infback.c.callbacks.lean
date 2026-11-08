import ZlibF.Proof.«infback.c.end»
import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«trees.c»

/-!
# infback.c: the contract of the two call-backs

`inflateBack(strm, in, in_desc, out, out_desc)` takes the caller's functions as parameters. They are caller code, not
library code, so a theorem about `inflateBack` is stated for all call-backs that keep the documented contract of `zlib.h`:

* `in`: "`in()` ... returns the number of bytes available ... and sets `*buf` to point to them; it returns zero if no
  more input is available". The bytes must stay valid and unchanged until the next call of `in` or until `inflateBack`
  returns.
* `out`: "should return zero on success, or non-zero on failure". It receives `len` bytes at `buf` (a pointer into the
  window) and may read them.
* "Neither `in()` nor `out()` are permitted to change the contents of the window provided to `inflateBackInit()`", and
  neither may call into the same stream: they do not touch the stream or its state.

The heap form (`CbContract`): each call changes only byte blocks of the call-back's own set (`ownI` for `in`, `ownO` for
`out`), never the window, never a record table, and allocates and frees nothing. The two own sets are disjoint, so a
buffer that `in` returned cannot change before the next call of `in`. `R` is the call-back's own invariant (for example
"my input buffer is intact"); it depends only on the own blocks, and each call keeps it. The tables are compared
pointwise.

Narrower than `zlib.h` (listed in `docs/proof/callbacks.md`): a call-back does not allocate or free heap blocks, and
the input buffer is a byte block of the heap.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The heap `h'` after a call-back that may write only the byte blocks in `own`: every table entry outside `own` is
as before, the shape of the heap (which blocks are live) and the allocator are untouched. -/
structure CbFrame (own : Nat → Prop) (h h' : Heap) : Prop where
  bytes : ∀ b, ¬ own b → h'.bytes b = h.bytes b
  live : ∀ b, (h'.bytes b).isSome = (h.bytes b).isSome
  words : ∀ b, h'.words b = h.words b
  ro : ∀ b, h'.ro b = h.ro b
  streams : ∀ b, h'.streams b = h.streams b
  gzheaders : ∀ b, h'.gzheaders b = h.gzheaders b
  dstates : ∀ b, h'.dstates b = h.dstates b
  istates : ∀ b, h'.istates b = h.istates b
  gzstates : ∀ b, h'.gzstates b = h.gzstates b
  static : h'.static = h.static
  nextBlk : h'.nextBlk = h.nextBlk
  nalloc : h'.nalloc = h.nalloc
  allocOk : h'.allocOk = h.allocOk
  garbage : h'.garbage = h.garbage

/-- `n` readable bytes start at `p` (a pointer into a byte block of `h`). -/
def ReadableAt (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ b off a, p = .ref (.blk b) off ∧ h.bytes b = some a ∧ off + n ≤ a.size

/-- **The contract of the call-backs of `inflateBack`.** `inCb`/`outCb` are the functions, `inDesc`/`outDesc` the
descriptors, `win` the block number of the window, `ownI`/`ownO` the byte blocks that `in` and `out` may write, `R` their
own invariant. See the file comment for the `zlib.h` text. -/
structure CbContract (inCb : InCb) (inDesc : BPtr) (outCb : OutCb) (outDesc : BPtr) (win : Nat)
    (ownI ownO : Nat → Prop) (R : Heap → Prop) : Prop where
  /-- the window belongs to neither call-back, and the two own sets are disjoint -/
  disj : ¬ ownI win ∧ ¬ ownO win ∧ ∀ b, ownI b → ¬ ownO b
  /-- `R` depends on the own blocks only -/
  local_ : ∀ h h', (∀ b, (ownI b ∨ ownO b) → h'.bytes b = h.bytes b) → (R h ↔ R h')
  /-- `in`: returns the count and the new `*buf`; a non-zero count comes with that many readable bytes in an
  own block, which `out` cannot change -/
  inOk : ∀ h nx, R h → ∃ n nx' h', inCb inDesc nx h = .ok ((n, nx'), h') ∧ CbFrame ownI h h' ∧ R h' ∧
    (n ≠ 0 → ∃ b off a, nx' = .ref (.blk b) off ∧ ownI b ∧ h'.bytes b = some a ∧ off + n.toNat ≤ a.size)
  /-- `out`: called with `len` readable bytes (the window), returns a result and keeps the frame -/
  outOk : ∀ h p len, R h → ReadableAt h p len.toNat → ∃ r h', outCb outDesc p len h = .ok (r, h') ∧ CbFrame ownO h h' ∧ R h'

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Infback Zlib.Infback.Spec

theorem CbFrame.refl (own : Nat → Prop) (h : Heap) : CbFrame own h h :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A call-back frame keeps the stream records: `get` of a stream reference is unchanged. -/
theorem CbFrame.zget {own : Nat → Prop} {h h' : Heap} (f : CbFrame own h h') (r : ZStreamRef) : r.get h' = r.get h := by
  cases r with
  | tab i => simp [ZStreamRef.get, f.streams]
  | in_gzstate_strm i => simp [ZStreamRef.get, f.gzstates]

/-- The simplest call-backs: `in` has no input (returns 0) and `out` accepts everything (returns 0). -/
def eofIn : InCb := fun _ nx => pure (0, nx)
def okOut : OutCb := fun _ _ _ => pure 0

/-- The trivial call-backs keep the contract, with no own blocks and `R` always true. -/
theorem cbContract_eof (win : Nat) : CbContract eofIn .null okOut .null win (fun _ => False) (fun _ => False) (fun _ => True) :=
  ⟨⟨fun h => h.elim, fun h => h.elim, fun _ h => h.elim⟩, fun _ _ _ => Iff.rfl,
   fun h nx _ => ⟨0, nx, h, rfl, CbFrame.refl _ _, trivial, fun e => absurd rfl e⟩,
   fun h _ _ _ _ => ⟨0, h, rfl, CbFrame.refl _ _, trivial⟩⟩

/-- An `out` that always fails (returns 1): the same contract. -/
def failOut : OutCb := fun _ _ _ => pure 1

theorem cbContract_fail (win : Nat) :
    CbContract eofIn .null failOut .null win (fun _ => False) (fun _ => False) (fun _ => True) :=
  ⟨⟨fun h => h.elim, fun h => h.elim, fun _ h => h.elim⟩, fun _ _ _ => Iff.rfl,
   fun h nx _ => ⟨0, nx, h, rfl, CbFrame.refl _ _, trivial, fun e => absurd rfl e⟩,
   fun h _ _ _ _ => ⟨1, h, rfl, CbFrame.refl _ _, trivial⟩⟩

/-! ### Non-vacuity on a heap made by the real `inflateBackInit_`

The heap has all static tables of the library, a stream record (block 0), a window of 256 bytes (block 1) and the
release string `"1.3.2"` (block 2). -/

/-- `Heap.empty` with every static table of the library installed. -/
def staticHeap : Heap :=
  { Heap.empty with static :=
      Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

/-- The initial heap: `staticHeap`, the stream `ZStream.zeroed` (so `zalloc`, `zfree` are `NULL`), the window block and
the release string, with every allocation succeeding. -/
def wit0 : Heap :=
  { staticHeap with
    bytes := upd (upd staticHeap.bytes 1 (some (Array.replicate 256 0))) 2 (some #[49, 46, 51, 46, 50, 0]),
    streams := upd staticHeap.streams 0 (some ZStream.zeroed),
    nextBlk := 3,
    allocOk := fun _ => true }

theorem wit0_uniq : Uniq wit0 := by
  intro b
  by_cases h1 : b = 1
  · subst h1; simp [wit0, staticHeap, Heap.empty, cnt]
  by_cases h2 : b = 2
  · subst h2; simp [wit0, staticHeap, Heap.empty, cnt]
  by_cases h0 : b = 0
  · subst h0; simp [wit0, staticHeap, Heap.empty, cnt]
  simp [wit0, staticHeap, Heap.empty, cnt, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2, upd_ne _ _ _ _ h0]

theorem wit0_fresh : Fresh wit0 := by
  intro b hb hl
  have h1 : b ≠ 1 := by simp [wit0] at hb; omega
  have h2 : b ≠ 2 := by simp [wit0] at hb; omega
  have h0 : b ≠ 0 := by simp [wit0] at hb; omega
  simp [Heap.live, wit0, staticHeap, Heap.empty, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2, upd_ne _ _ _ _ h0] at hl

/-- **Witness.** The real `inflateBackInit_(strm, 8, window, "1.3.2", 112)` runs on `wit0` and returns `Z_OK`, and on the
resulting heap the invariant `BackGood` holds together with the call-back contract for `eofIn` with `okOut` (and
with `failOut`). So the hypotheses of the `inflateBack` theorems are satisfiable by a real `inflateBackInit_` heap. -/
theorem backInit_witness :
    ∃ h' z st, C.run (inflateBackInit_ (some (.tab 0)) 8 (.ref (.blk 1) 0) (.ref (.blk 2) 0) 112) wit0 = .ok (Z_OK, h') ∧
      BackGood h' (.tab 0) 3 z st ∧
      CbContract eofIn .null okOut .null 1 (fun _ => False) (fun _ => False) (fun _ => True) ∧
      CbContract eofIn .null failOut .null 1 (fun _ => False) (fun _ => False) (fun _ => True) := by
  have hz : (ZStreamRef.tab 0).get wit0 = some ZStream.zeroed := by
    simp [ZStreamRef.get, wit0]
  have hwin : WindowOk wit0 (.ref (.blk 1) 0) (2 ^ (i2u 8).toNat) :=
    ⟨1, 0, Array.replicate 256 0, rfl, by simp [wit0], by simp [wit0, staticHeap, Heap.empty], by rw [Array.size_replicate]; decide⟩
  obtain ⟨h', hr, -, hG, -⟩ := inflateBackInit__ok (r := .tab 0) (z := ZStream.zeroed) (wb := 8) (window := .ref (.blk 1) 0)
    (version := .ref (.blk 2) 0) wit0_uniq wit0_fresh hz (by simp [wit0]) (Or.inl rfl) (Or.inl rfl) (by intro c; cases c)
    (by unfold OkOn; simp [index8, wit0]; rfl) (by decide) (by decide) hwin
  exact ⟨h', _, _, hr, by simpa [wit0] using hG, cbContract_eof 1, cbContract_fail 1⟩

end Zlib.Infback.Proofs
