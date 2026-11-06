import ZlibF.Zlib.«deflate.c»
import ZlibF.Proof.«zutil.c»
import ZlibF.Proof.«trees.c.bits»

/-!
# deflate.c: the stream invariant and the lemmas the stream functions share

The statements of `docs/spec/functions/deflate-stream.md`. The definitions of namespace `Zlib.Deflate.Spec` are part of
what a theorem means; the lemmas of `Zlib.Deflate.Proofs` are not.

* `Uniq`: a block number holds an object of at most one table.
* `DBlocks`: the four buffers of a deflate state (window, prev, head, pending_buf) are live blocks of the right size.
* `DStInv`: the representation invariant of a deflate state record (array sizes, hash and window relations, the
  ranges of level, strategy and wrapper, the pointers into the blocks, the symbol buffer and the bit buffer).
* `DLive`: the stream is one that `deflateStateCheck` accepts, and its state is the record `d` at block `ds`.
* `DGood`: `DLive`, `DStInv`, `Uniq`, `Fresh` and the trees invariant together.

The proofs of the engine (`deflate`, `fill_window`, the strategies) import this module: a function that keeps
`DGood` keeps the bounds the next function needs.

**The trees invariant.** `DGood` includes `TreesInv h ds` of `trees.c.inv`: the invariant the functions of `trees.c` need
(descriptors, static tables, the byte block that holds `pending_buf` and `sym_buf`). Several of its facts are also stated
in `DStInv` (`bits`, `sym`), so that a proof about the lifecycle functions can read them without unpacking it.
-/

namespace Zlib.Deflate.Spec
open C

/-- 1 if the table entry holds an object, else 0. -/
def cnt {α : Type} (o : Option α) : Nat := if o.isSome then 1 else 0

@[simp] theorem cnt_none {α : Type} : cnt (none : Option α) = 0 := rfl
@[simp] theorem cnt_some {α : Type} (a : α) : cnt (some a) = 1 := rfl

/-- A block number holds an object of at most one table. -/
def Uniq (h : Heap) : Prop := ∀ b,
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) +
  cnt (h.gzstates b) ≤ 1

/-- The heap with the deflate state record `ds` replaced. -/
def setD (h : Heap) (ds : Nat) (d : DeflateState) : Heap := { h with dstates := upd h.dstates ds (some d) }

/-- The status values `deflateStateCheck` accepts: the zlib header, the gzip header, extra, name, comment, header CRC,
busy and finish. -/
def GoodStatus (s : Int32) : Prop :=
  s = INIT_STATE ∨ s = GZIP_STATE ∨ s = EXTRA_STATE ∨ s = NAME_STATE ∨ s = COMMENT_STATE ∨ s = HCRC_STATE ∨
  s = BUSY_STATE ∨ s = FINISH_STATE

/-- The user's gzip header pointer: `NULL`, or a live `gz_header` record. -/
def GzOk (h : Heap) (g : Option GzHeaderRef) : Prop :=
  g = none ∨ ∃ i, g = some (.tab i) ∧ (h.gzheaders i).isSome

/-- The four buffers of the deflate state record `d`: `window` is the writable byte block `w` of `2 * w_size` bytes,
`pending_buf` the writable byte block `b` of `4 * lit_bufsize` bytes, `prev` and `head` are blocks of 16-bit words that
hold `w_size` and `hash_size` entries. The four blocks are different. `pending_out` lies in `pending_buf`
and `pending_out + pending` does not leave it. -/
structure DBlocks (h : Heap) (d : DeflateState) (w p q b : Nat) : Prop where
  win : d.window = .ref (.blk w) 0
  prev : d.prev = .ref (.blk p) 0
  head : d.head = .ref (.blk q) 0
  pbuf : d.pending_buf = .ref (.blk b) 0
  wa : ∃ a, h.bytes w = some a ∧ a.size = 2 * d.w_size.toNat
  wro : h.ro w = false
  pa : ∃ a, h.words p = some a ∧ a.size = d.w_size.toNat
  qa : ∃ a, h.words q = some a ∧ a.size = d.hash_size.toNat
  ba : ∃ a, h.bytes b = some a ∧ a.size = 4 * d.lit_bufsize.toNat
  bro : h.ro b = false
  psize : d.pending_buf_size.toNat = 4 * d.lit_bufsize.toNat
  wb : w ≠ b
  pq : p ≠ q
  pout : ∃ off, d.pending_out = .ref (.blk b) off ∧ off + d.pending.toNat ≤ d.pending_buf_size.toNat

/-- The representation invariant of a deflate state record `d` at block `ds`, as far as the stream functions and the
engine need it (`deflateInit2_` establishes it).

* sizes: `w_bits` is 9 to 15, `w_size = 2^w_bits`, `w_mask = w_size - 1`, `window_size = 2 * w_size`; `hash_bits` is 8 to
  16 (`memLevel + 7`), `hash_size = 2^hash_bits`, `hash_mask = hash_size - 1`, `hash_shift = (hash_bits + 2) / 3`,
  `lit_bufsize = hash_size / 2 = 2^(memLevel + 6)`;
* ranges: `level` 0 to 9, `strategy` 0 to 4, `method = Z_DEFLATED`, `wrap` from `-2` to `2` (negative after the trailer);
* `high_water <= window_size`;
* the symbol buffer overlays `pending_buf` at `lit_bufsize`, `sym_end = 3 (lit_bufsize - 1)`, `sym_next <= sym_end`
  and a multiple of 3;
* the bit buffer holds `bi_valid` bits (0 to 16) and no bit above them. -/
structure DStInv (h : Heap) (ds : Nat) (d : DeflateState) : Prop where
  wf : d.WellFormed
  wbits_lo : 9 ≤ d.w_bits.toNat
  wbits_hi : d.w_bits.toNat ≤ 15
  wsize : d.w_size.toNat = 2 ^ d.w_bits.toNat
  wmask : d.w_mask.toNat = d.w_size.toNat - 1
  wsz : d.window_size.toNat = 2 * d.w_size.toNat
  hbits_lo : 8 ≤ d.hash_bits.toNat
  hbits_hi : d.hash_bits.toNat ≤ 16
  hsize : d.hash_size.toNat = 2 ^ d.hash_bits.toNat
  hmask : d.hash_mask.toNat = d.hash_size.toNat - 1
  hshift : d.hash_shift.toNat = (d.hash_bits.toNat + 2) / 3
  lit : 2 * d.lit_bufsize.toNat = d.hash_size.toNat
  level_lo : 0 ≤ d.level.toInt
  level_hi : d.level.toInt ≤ 9
  strat_lo : 0 ≤ d.strategy.toInt
  strat_hi : d.strategy.toInt ≤ 4
  method : d.method = 8
  wrap_lo : -2 ≤ d.wrap.toInt
  wrap_hi : d.wrap.toInt ≤ 2
  hw : d.high_water.toNat ≤ d.window_size.toNat
  blocks : ∃ w p q b, DBlocks h d w p q b
  sym : (∃ b, d.pending_buf = .ref (.blk b) 0 ∧ d.sym_buf = .ref (.blk b) d.lit_bufsize.toNat) ∧
    d.sym_end.toNat = 3 * (d.lit_bufsize.toNat - 1) ∧ d.sym_next.toNat ≤ d.sym_end.toNat ∧ d.sym_next.toNat % 3 = 0
  bits : 0 ≤ d.bi_valid.toInt ∧ d.bi_valid.toInt ≤ 16 ∧ d.bi_buf.toNat < 2 ^ d.bi_valid.toInt.toNat
  gz : GzOk h d.gzhead

/-- The stream `r` is the record `z`; its state is the record `d` at block `ds`, which points back to the stream; the
status is one `deflateStateCheck` accepts; the allocator functions are not `NULL`. -/
structure DLive (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  hz : r.get h = some z
  hs : h.dstates ds = some d
  zst : z.state = some (.deflate ds)
  back : d.strm = some r
  status : GoodStatus d.status
  zalloc : z.zalloc ≠ .null
  zfree : z.zfree ≠ .null

/-- The stream functions can allocate and free: the allocator functions are the default ones (the only ones the model
has; any other makes the translation fault). -/
def DefAlloc (z : ZStream) : Prop := z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree"

/-- Everything the stream functions assume of the heap around a live deflate stream. -/
structure DGood (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  live : DLive h r ds z d
  inv : DStInv h ds d
  uniq : Uniq h
  fresh : Fresh h
  trees : Zlib.Trees.Proofs.Out.TreesInv h ds

/-- The blocks a stream owns: its state record and the four buffers. -/
def DOwned (d : DeflateState) (ds : Nat) (x : Nat) : Prop :=
  x = ds ∨ (∃ w, d.window = .ref (.blk w) 0 ∧ x = w) ∨ (∃ p, d.prev = .ref (.blk p) 0 ∧ x = p) ∨
  (∃ q, d.head = .ref (.blk q) 0 ∧ x = q) ∨ (∃ b, d.pending_buf = .ref (.blk b) 0 ∧ x = b)

/-- The streams `deflateStateCheck` handles: `NULL`, or a live stream record that has a `NULL` allocator function, or
no state, or a state that is a live deflate state record. (A state that is an inflate state, a freed state or a freed
stream is undefined behaviour in C and a fault here.) -/
def StreamDom (h : Heap) (strm : ZStreamPtr) : Prop :=
  strm = none ∨ ∃ r z, strm = some r ∧ r.get h = some z ∧
    (z.zalloc = .null ∨ z.zfree = .null ∨ z.state = none ∨ ∃ ds d, z.state = some (.deflate ds) ∧ h.dstates ds = some d)

/-- The stream is one `deflateStateCheck` accepts. -/
def DInitialised (h : Heap) (strm : ZStreamPtr) : Prop := ∃ r ds z d, strm = some r ∧ DLive h r ds z d

end Zlib.Deflate.Spec

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec

/-! ### Updating the heap -/

@[simp] theorem setD_dstates_same (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).dstates ds = some d := by
  simp [setD]
@[simp] theorem setD_dstates_ne (h : Heap) (ds x : Nat) (d : DeflateState) (hx : x ≠ ds) :
    (setD h ds d).dstates x = h.dstates x := by simp [setD, upd_ne _ _ _ _ hx]
@[simp] theorem setD_bytes (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).bytes = h.bytes := rfl
@[simp] theorem setD_words (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).words = h.words := rfl
@[simp] theorem setD_streams (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).streams = h.streams := rfl
@[simp] theorem setD_gzstates (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).gzstates = h.gzstates := rfl
@[simp] theorem setD_gzheaders (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).gzheaders = h.gzheaders := rfl
@[simp] theorem setD_istates (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).istates = h.istates := rfl
@[simp] theorem setD_ro (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).ro = h.ro := rfl
@[simp] theorem setD_static (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).static = h.static := rfl
@[simp] theorem setD_nextBlk (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).nextBlk = h.nextBlk := rfl
@[simp] theorem setD_nalloc (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).nalloc = h.nalloc := rfl
@[simp] theorem setD_allocOk (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).allocOk = h.allocOk := rfl
@[simp] theorem setD_garbage (h : Heap) (ds : Nat) (d : DeflateState) : (setD h ds d).garbage = h.garbage := rfl
@[simp] theorem setD_setD (h : Heap) (ds : Nat) (d d' : DeflateState) : setD (setD h ds d) ds d' = setD h ds d' := by
  simp [setD, upd_upd]
theorem setD_self {h : Heap} {ds : Nat} {d : DeflateState} (hd : h.dstates ds = some d) : setD h ds d = h := by
  simp [setD, upd_self _ _ _ hd]

theorem ZStreamRef.get_put_same {h : Heap} {r : ZStreamRef} {z : ZStream} (e : r.get h = some z) (v : ZStream) :
    r.get (r.put h v) = some v := by
  cases r with
  | tab i => simp [ZStreamRef.get] at e; simp [ZStreamRef.put, ZStreamRef.get, e]
  | in_gzstate_strm i =>
    simp [ZStreamRef.get] at e
    obtain ⟨g, hg, -⟩ := e
    simp [ZStreamRef.put, ZStreamRef.get, hg]

@[simp] theorem ZStreamRef.get_setD (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) :
    r.get (setD h ds d) = r.get h := by
  cases r <;> rfl

@[simp] theorem ZStreamRef.put_dstates (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).dstates = h.dstates := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_bytes (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).bytes = h.bytes := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_ro (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).ro = h.ro := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_words (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).words = h.words := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_istates (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).istates = h.istates := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_gzheaders (h : Heap) (r : ZStreamRef) (v : ZStream) :
    (r.put h v).gzheaders = h.gzheaders := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_nextBlk (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).nextBlk = h.nextBlk := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_nalloc (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).nalloc = h.nalloc := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_allocOk (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).allocOk = h.allocOk := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_garbage (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).garbage = h.garbage := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_static (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).static = h.static := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.get_put (h : Heap) (r : ZStreamRef) (v : ZStream) :
    r.get (r.put h v) = (r.get h).map (fun _ => v) := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.put, ZStreamRef.get]
    cases hh : h.streams i <;> simp [hh]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.put, ZStreamRef.get]
    cases hh : h.gzstates i <;> simp [hh]

@[simp] theorem ZStreamRef.put_put (h : Heap) (r : ZStreamRef) (v v' : ZStream) : r.put (r.put h v) v' = r.put h v' := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.put]
    cases hh : h.streams i <;> simp [hh, upd_upd]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.put]
    cases hh : h.gzstates i <;> simp [hh, upd_upd]

@[simp] theorem ZStreamRef.put_setD (h : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (v : ZStream) :
    r.put (setD h ds d) v = setD (r.put h v) ds d := by
  cases r with
  | tab i => simp only [ZStreamRef.put, setD]; cases hh : h.streams i <;> simp
  | in_gzstate_strm i => simp only [ZStreamRef.put, setD]; cases hh : h.gzstates i <;> simp

/-! ### Reading and writing the stream and the state -/

theorem castD {h : Heap} {ds : Nat} : castDeflateState (some (.deflate ds)) h = .ok (some (.tab ds), h) := rfl

theorem ldD_eq (h : Heap) (i : Nat) : ldDeflateState (some (.tab i)) h =
    match h.dstates i with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (deflate_state)") := rfl

theorem ldZ_eq (h : Heap) (r : ZStreamRef) : ldZStream (some r) h =
    match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (z_stream)") := rfl

theorem rdD_eq {α : Type} (h : Heap) (i : Nat) (f : DeflateState → α) : rd (some (.tab i)) f h =
    match h.dstates i with
    | some v => .ok (f v, h)
    | none => .error (.ub "access through a dangling pointer (deflate_state)") := by
  simp only [rd, bind_app, ldD_eq]; cases h.dstates i <;> rfl

theorem zrd_eq {α : Type} (h : Heap) (r : ZStreamRef) (f : ZStream → α) : zrd (some r) f h =
    match r.get h with
    | some v => .ok (f v, h)
    | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  simp only [zrd, bind_app, ldZ_eq]; cases r.get h <;> rfl

theorem stD_eq (h : Heap) (i : Nat) (v : DeflateState) : stDeflateState (some (.tab i)) v h =
    match h.dstates i with
    | some _ => .ok ((), setD h i v)
    | none => .error (.ub "access through a dangling pointer (deflate_state)") := by
  cases hh : h.dstates i with
  | none => simp [stDeflateState, DeflateStateRef.get, hh]
  | some w => simp [stDeflateState_tab hh, setD, hh]

theorem wrD_eq (h : Heap) (i : Nat) (f : DeflateState → DeflateState) : wr (some (.tab i)) f h =
    match h.dstates i with
    | some v => .ok ((), setD h i (f v))
    | none => .error (.ub "access through a dangling pointer (deflate_state)") := by
  cases hh : h.dstates i with
  | none => simp [wr, bind_app, ldD_eq, hh]
  | some v => simp [wr, bind_app, ldD_eq, hh, stD_eq]

theorem stZ_eq (h : Heap) (r : ZStreamRef) (v : ZStream) : stZStream (some r) v h =
    match r.get h with
    | some _ => .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  have hro : r.isRo = false := by cases r <;> rfl
  cases hh : r.get h with
  | none => simp [stZStream, hh]
  | some w => simp [stZStream_ok hh hro, hh]

theorem zwr_eq (h : Heap) (r : ZStreamRef) (f : ZStream → ZStream) : zwr (some r) f h =
    match r.get h with
    | some v => .ok ((), r.put h (f v))
    | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  cases hh : r.get h with
  | none => simp [zwr, bind_app, ldZ_eq, hh]
  | some v => simp [zwr, bind_app, ldZ_eq, hh, stZ_eq]

/-- Evaluate a straight-line sequence of accesses to a stream and its deflate state. -/
macro "dsimp'" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [bind_app, pure_app, ldD_eq, ldZ_eq, rdD_eq, zrd_eq, wrD_eq, zwr_eq, stD_eq, stZ_eq, castD, $ts,*])

/-! ### The stream check -/

theorem hdec {a b : UInt32} : a ≤ b ∨ b < a := by
  rcases Nat.lt_or_ge b.toNat a.toNat with h | h
  · exact Or.inr (UInt32.lt_iff_toNat_lt.mpr h)
  · exact Or.inl (UInt32.le_iff_toNat_le.mpr h)

theorem stateCheck_live {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) : deflateStateCheck (some r) h = .ok (0, h) := by
  obtain ⟨hz, hs, zst, back, st, za, zf⟩ := hL
  have e1 : ldZStream (some r) h = .ok (z, h) := ldZStream_ok hz
  unfold deflateStateCheck
  rcases st with hh | hh | hh | hh | hh | hh | hh | hh <;>
    simp [bind_app, e1, za, zf, zst, castDeflateState_ok, ldDeflateState_tab hs, back, hh]


theorem ZStreamRef.put_self {h : Heap} {r : ZStreamRef} {z : ZStream} (e : r.get h = some z) : r.put h z = h := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at e
    simp [ZStreamRef.put, e, upd_self _ _ _ e]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at e
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp e
    simp [ZStreamRef.put, hg, upd_self _ _ _ hg]

/-! ### Which objects exist: the shape of a heap -/

/-- The two heaps hold an object in the same tables at the same block numbers (the objects may differ). -/
def Shape (h h' : Heap) : Prop := ∀ b, (h'.bytes b).isSome = (h.bytes b).isSome ∧ (h'.words b).isSome = (h.words b).isSome ∧
  (h'.streams b).isSome = (h.streams b).isSome ∧ (h'.gzheaders b).isSome = (h.gzheaders b).isSome ∧
  (h'.dstates b).isSome = (h.dstates b).isSome ∧ (h'.istates b).isSome = (h.istates b).isSome ∧
  (h'.gzstates b).isSome = (h.gzstates b).isSome

theorem _root_.Zlib.Deflate.Proofs.Shape.refl (h : Heap) : Shape h h := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem _root_.Zlib.Deflate.Proofs.Shape.trans {h1 h2 h3 : Heap} (a : Shape h1 h2) (b : Shape h2 h3) : Shape h1 h3 := by
  intro x
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a x
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := b x
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩

theorem _root_.Zlib.Deflate.Proofs.Shape.uniq {h h' : Heap} (hS : Shape h h') (hU : Uniq h) : Uniq h' := by
  intro b
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hS b
  have := hU b
  simp only [cnt, e1, e2, e3, e4, e5, e6, e7] at this ⊢
  exact this

theorem _root_.Zlib.Deflate.Proofs.Shape.live {h h' : Heap} (hS : Shape h h') (b : Nat) : h'.live b ↔ h.live b := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hS b
  simp only [Heap.live, ← Option.isSome_iff_ne_none, e1, e2, e3, e4, e5, e6, e7]

theorem _root_.Zlib.Deflate.Proofs.Shape.fresh {h h' : Heap} (hS : Shape h h') (hn : h'.nextBlk = h.nextBlk) (hF : Fresh h) : Fresh h' := by
  intro b hb hl
  exact hF b (by omega) ((hS.live b).1 hl)

theorem _root_.Zlib.Deflate.Proofs.Shape.owns {h h' : Heap} (hS : Shape h h') {S : Nat → Prop} (hO : h.Owns S) : h'.Owns S :=
  fun b => (hS.live b).trans (hO b)

theorem shape_setD {h : Heap} {ds : Nat} {d0 : DeflateState} (e : h.dstates ds = some d0) (d : DeflateState) :
    Shape h (setD h ds d) := by
  intro b
  by_cases hb : b = ds
  · subst hb; simp [setD, e]
  · simp [setD, upd_ne _ _ _ _ hb]

theorem shape_put {h : Heap} {r : ZStreamRef} {z0 : ZStream} (e : r.get h = some z0) (v : ZStream) :
    Shape h (r.put h v) := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.get] at e
    intro b
    by_cases hb : b = i
    · subst hb; simp [ZStreamRef.put, e]
    · simp [ZStreamRef.put, e, upd_ne _ _ _ _ hb]
  | in_gzstate_strm i =>
    simp only [ZStreamRef.get] at e
    obtain ⟨g, hg, -⟩ := Option.map_eq_some_iff.mp e
    intro b
    by_cases hb : b = i
    · subst hb; simp [ZStreamRef.put, hg]
    · simp [ZStreamRef.put, hg, upd_ne _ _ _ _ hb]

theorem shape_setB {h : Heap} {w : Nat} {a0 : Array UInt8} (e : h.bytes w = some a0) (a : Array UInt8) :
    Shape h { h with bytes := upd h.bytes w (some a) } := by
  intro b
  by_cases hb : b = w
  · subst hb; simp [e]
  · simp [upd_ne _ _ _ _ hb]

theorem shape_setW {h : Heap} {w : Nat} {a0 : Array UInt16} (e : h.words w = some a0) (a : Array UInt16) :
    Shape h { h with words := upd h.words w (some a) } := by
  intro b
  by_cases hb : b = w
  · subst hb; simp [e]
  · simp [upd_ne _ _ _ _ hb]

/-! ### Uniqueness -/

theorem _root_.Zlib.Deflate.Spec.Uniq.bytes_only {h : Heap} (hU : Uniq h) {b : Nat} {a : Array UInt8} (hb : h.bytes b = some a) :
    h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧ h.istates b = none ∧
    h.gzstates b = none := by
  have := hU b
  simp only [hb, cnt_some] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hx : h.words b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.streams b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzheaders b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.dstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.istates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega

theorem _root_.Zlib.Deflate.Spec.Uniq.words_only {h : Heap} (hU : Uniq h) {b : Nat} {a : Array UInt16} (hb : h.words b = some a) :
    h.bytes b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧ h.istates b = none ∧
    h.gzstates b = none := by
  have := hU b
  simp only [hb, cnt_some] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hx : h.bytes b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.streams b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzheaders b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.dstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.istates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega

theorem _root_.Zlib.Deflate.Spec.Uniq.dstates_only {h : Heap} (hU : Uniq h) {b : Nat} {a : DeflateState} (hb : h.dstates b = some a) :
    h.bytes b = none ∧ h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.istates b = none ∧
    h.gzstates b = none := by
  have := hU b
  simp only [hb, cnt_some] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hx : h.bytes b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.words b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.streams b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzheaders b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.istates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega

/-! ### Preserving the invariants -/

theorem _root_.Zlib.Deflate.Spec.DBlocks.congr {h h' : Heap} {d : DeflateState} {w p q b : Nat} (hb : h'.bytes = h.bytes)
    (hw : h'.words = h.words) (hr : h'.ro = h.ro) (hB : DBlocks h d w p q b) : DBlocks h' d w p q b := by
  obtain ⟨a1, a2, a3, a4, ⟨x1, y1, z1⟩, r1, ⟨x2, y2, z2⟩, ⟨x3, y3, z3⟩, ⟨x4, y4, z4⟩, r4, ps, wb, pq, po⟩ := hB
  exact ⟨a1, a2, a3, a4, ⟨x1, by rw [hb]; exact y1, z1⟩, by rw [hr]; exact r1, ⟨x2, by rw [hw]; exact y2, z2⟩,
    ⟨x3, by rw [hw]; exact y3, z3⟩, ⟨x4, by rw [hb]; exact y4, z4⟩, by rw [hr]; exact r4, ps, wb, pq, po⟩

theorem _root_.Zlib.Deflate.Spec.DStInv.congr {h h' : Heap} {ds : Nat} {d : DeflateState} (hb : h'.bytes = h.bytes) (hw : h'.words = h.words)
    (hr : h'.ro = h.ro) (hg : h'.gzheaders = h.gzheaders) (hI : DStInv h ds d) : DStInv h' ds d := by
  obtain ⟨wf, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, ⟨w, p, q, b, hB⟩, sy, bi, gz⟩ := hI
  refine ⟨wf, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    ⟨w, p, q, b, hB.congr hb hw hr⟩, sy, bi, ?_⟩
  rcases gz with g | ⟨i, g, e⟩
  · exact Or.inl g
  · exact Or.inr ⟨i, g, by rw [hg]; exact e⟩

theorem _root_.Zlib.Deflate.Spec.DBlocks.keys {h : Heap} {d d' : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) (e1 : d'.window = d.window) (e2 : d'.prev = d.prev) (e3 : d'.head = d.head)
    (e4 : d'.pending_buf = d.pending_buf) (e5 : d'.w_size = d.w_size) (e6 : d'.hash_size = d.hash_size)
    (e7 : d'.lit_bufsize = d.lit_bufsize) (e8 : d'.pending_buf_size = d.pending_buf_size)
    (e9 : d'.pending_out = d.pending_out) (e10 : d'.pending = d.pending) : DBlocks h d' w p q b := by
  obtain ⟨a1, a2, a3, a4, ⟨x1, y1, z1⟩, r1, ⟨x2, y2, z2⟩, ⟨x3, y3, z3⟩, ⟨x4, y4, z4⟩, r4, ps, wb, pq, ⟨off, po, pl⟩⟩ := hB
  refine ⟨by rw [e1]; exact a1, by rw [e2]; exact a2, by rw [e3]; exact a3, by rw [e4]; exact a4,
    ⟨x1, y1, by rw [e5]; exact z1⟩, r1, ⟨x2, y2, by rw [e5]; exact z2⟩, ⟨x3, y3, by rw [e6]; exact z3⟩,
    ⟨x4, y4, by rw [e7]; exact z4⟩, r4, by rw [e8, e7]; exact ps, wb, pq, ⟨off, by rw [e9]; exact po, by rw [e10, e8]; exact pl⟩⟩

/-- The blocks of the state stay the same when the record changes only in fields other than the ten `DBlocks` reads
(each equality is `rfl` for a record update that leaves them alone). -/
theorem _root_.Zlib.Deflate.Spec.DStInv.blocks_keys {h : Heap} {ds : Nat} {d d' : DeflateState} (hI : DStInv h ds d)
    (e1 : d'.window = d.window) (e2 : d'.prev = d.prev) (e3 : d'.head = d.head)
    (e4 : d'.pending_buf = d.pending_buf) (e5 : d'.w_size = d.w_size) (e6 : d'.hash_size = d.hash_size)
    (e7 : d'.lit_bufsize = d.lit_bufsize) (e8 : d'.pending_buf_size = d.pending_buf_size)
    (e9 : d'.pending_out = d.pending_out) (e10 : d'.pending = d.pending) : ∃ w p q b, DBlocks h d' w p q b := by
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  exact ⟨w, p, q, b, hB.keys e1 e2 e3 e4 e5 e6 e7 e8 e9 e10⟩

/-- The fields of a state record that `trees.c` relies on are unchanged: the buffers and the symbol buffer, the three tree
descriptors, the bit buffer and the symbol count. -/
def TrKeep (d d' : DeflateState) : Prop :=
  d'.pending_buf = d.pending_buf ∧ d'.pending_buf_size = d.pending_buf_size ∧ d'.sym_buf = d.sym_buf ∧
  d'.lit_bufsize = d.lit_bufsize ∧ d'.sym_end = d.sym_end ∧ d'.l_desc = d.l_desc ∧ d'.d_desc = d.d_desc ∧
  d'.bl_desc = d.bl_desc ∧ d'.bi_valid = d.bi_valid ∧ d'.bi_buf = d.bi_buf ∧ d'.sym_next = d.sym_next

/-- Prove `TrKeep d d'` when `d'` is a record update of `d` that leaves those fields alone. -/
macro "trkeep" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- The invariant of `trees.c` survives a change of the state record that keeps the fields of `TrKeep` (and the sizes of
its arrays), on a heap with the same byte blocks, read-only flags and static tables. -/
theorem TreesInv.keep {h h' : Heap} {id : Nat} {d d' : DeflateState} (hT : Zlib.Trees.Proofs.Out.TreesInv h id)
    (hd : h.dstates id = some d) (hb : h'.bytes = h.bytes) (hr : h'.ro = h.ro) (hs : h'.static = h.static)
    (hd' : h'.dstates id = some d') (hw : d'.WellFormed) (hk : TrKeep d d')
    (hp : d'.pending.toNat ≤ d'.pending_buf_size.toNat) : Zlib.Trees.Proofs.Out.TreesInv h' id := by
  obtain ⟨d0, b, buf, hB, hR⟩ := hT
  have e : d0 = d := Option.some.inj (hB.dstate.symm.trans hd)
  subst e
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hk
  refine ⟨d', b, buf, ⟨hd', hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp⟩, ?_⟩
  · rw [hs]; exact hB.static
  · rw [k1]; exact hB.pbuf
  · rw [hb]; exact hB.bytes
  · rw [hr]; exact hB.rw
  · rw [k4]; exact hB.size
  · rw [k2]; exact hB.psize
  · rw [k3, k4]; exact hB.sym
  · rw [k4]; exact hB.lit_lo
  · rw [k4]; exact hB.lit_hi
  · rw [k5, k4]; exact hB.sym_end
  · refine ⟨by rw [k6]; exact hR.ldyn, by rw [k6]; exact hR.lstat, by rw [k7]; exact hR.ddyn, by rw [k7]; exact hR.dstat,
      by rw [k8]; exact hR.bldyn, by rw [k8]; exact hR.blstat, by rw [k9]; exact hR.bi_lo, by rw [k9]; exact hR.bi_hi,
      by rw [k10, k9]; exact hR.bi_buf, by rw [k11, k5]; exact hR.sym_next_le, by rw [k11]; exact hR.sym_next_mod⟩

/-- Replacing a block of words keeps the invariant of `trees.c` (it mentions only byte blocks). -/
theorem TreesInv.words_set {h : Heap} {id : Nat} (hT : Zlib.Trees.Proofs.Out.TreesInv h id) (x : Nat) (a : Array UInt16) :
    Zlib.Trees.Proofs.Out.TreesInv { h with words := upd h.words x (some a) } id := by
  obtain ⟨d, b, buf, hB, hR⟩ := hT
  exact ⟨d, b, buf, ⟨hB.dstate, hB.wf, hB.static, hB.pbuf, hB.bytes, hB.rw, hB.size, hB.psize, hB.sym, hB.lit_lo,
    hB.lit_hi, hB.sym_end, hB.pending_le⟩, hR⟩

/-- Replacing a byte block by an array of the same size keeps the invariant of `trees.c`: if it is the block of
`pending_buf` the content changes, which the invariant allows. -/
theorem TreesInv.bytes_set {h : Heap} {id : Nat} (hT : Zlib.Trees.Proofs.Out.TreesInv h id) (x : Nat) (a a0 : Array UInt8)
    (hx : h.bytes x = some a0) (hsz : a.size = a0.size) :
    Zlib.Trees.Proofs.Out.TreesInv { h with bytes := upd h.bytes x (some a) } id := by
  obtain ⟨d, b, buf, hB, hR⟩ := hT
  by_cases hxb : x = b
  · subst hxb
    have : buf = a0 := Option.some.inj (hB.bytes.symm.trans hx)
    subst this
    exact ⟨d, x, a, ⟨hB.dstate, hB.wf, hB.static, hB.pbuf, by simp, hB.rw, by rw [hsz]; exact hB.size,
      by rw [hsz]; exact hB.psize, hB.sym, hB.lit_lo, hB.lit_hi, hB.sym_end, hB.pending_le⟩, hR⟩
  · exact ⟨d, b, buf, ⟨hB.dstate, hB.wf, hB.static, hB.pbuf, by simp [upd_apply, Ne.symm hxb, hB.bytes], hB.rw, hB.size,
      hB.psize, hB.sym, hB.lit_lo, hB.lit_hi, hB.sym_end, hB.pending_le⟩, hR⟩

theorem _root_.Zlib.Deflate.Spec.DStInv.pending_le {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d) :
    d.pending.toNat ≤ d.pending_buf_size.toNat := by
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  obtain ⟨off, -, hpl⟩ := hB.pout
  omega

/-- Rewrite the stream record and the state record of a live stream, keeping the state pointer, the back pointer and
the status; the new state record satisfies the invariant and keeps the fields `trees.c` relies on (`TrKeep`). -/
theorem _root_.Zlib.Deflate.Spec.DGood.setZD {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) {z' : ZStream} {d' : DeflateState}
    (hz : z'.state = z.state) (hza : z'.zalloc ≠ .null) (hzf : z'.zfree ≠ .null) (hback : d'.strm = d.strm)
    (hst : GoodStatus d'.status) (hI : DStInv h ds d') (hk : TrKeep d d') :
    DGood (setD (r.put h z') ds d') r ds z' d' := by
  have hS : Shape h (setD (r.put h z') ds d') :=
    (shape_put hG.live.hz z').trans (shape_setD (by simpa using hG.live.hs) d')
  have hT : Zlib.Trees.Proofs.Out.TreesInv (setD (r.put h z') ds d') ds :=
    TreesInv.keep (d := d) (d' := d') (h := h) hG.trees hG.live.hs (by simp) (by simp) (by simp) (by simp) hI.wf hk
      hI.pending_le
  refine ⟨⟨?_, by simp, hz.trans hG.live.zst, hback.trans hG.live.back, hst, hza, hzf⟩,
    DStInv.congr (h := h) (h' := setD (r.put h z') ds d') (by simp) (by simp) (by simp) (by simp) hI,
    hS.uniq hG.uniq, hS.fresh (by simp) hG.fresh, hT⟩
  simp [ZStreamRef.get_put, hG.live.hz]

/-- The same for a change of the state record only. -/
theorem _root_.Zlib.Deflate.Spec.DGood.setD' {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) {d' : DeflateState} (hback : d'.strm = d.strm) (hst : GoodStatus d'.status)
    (hI : DStInv h ds d') (hk : TrKeep d d') : DGood (setD h ds d') r ds z d' := by
  have e : r.put h z = h := ZStreamRef.put_self hG.live.hz
  have := hG.setZD (z' := z) (d' := d') rfl hG.live.zalloc hG.live.zfree hback hst hI hk
  rw [e] at this
  exact this

/-- Replacing a block of words by an array of the same size keeps the four buffers. -/
theorem _root_.Zlib.Deflate.Spec.DBlocks.words_set {h : Heap} {d : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) (x : Nat) (a : Array UInt16) (a0 : Array UInt16) (hx : h.words x = some a0)
    (hsz : a.size = a0.size) : DBlocks { h with words := upd h.words x (some a) } d w p q b := by
  obtain ⟨a1, a2, a3, a4, wa, r1, ⟨pa, hpa, pz⟩, ⟨qa, hqa, qz⟩, ba, r4, ps, wb, pq, po⟩ := hB
  refine ⟨a1, a2, a3, a4, wa, r1, ?_, ?_, ba, r4, ps, wb, pq, po⟩
  · by_cases hxp : x = p
    · subst hxp
      have : pa = a0 := Option.some.inj (hpa.symm.trans hx)
      subst this
      exact ⟨a, by simp, by omega⟩
    · exact ⟨pa, by simp [upd_apply, Ne.symm hxp, hpa], pz⟩
  · by_cases hxq : x = q
    · subst hxq
      have : qa = a0 := Option.some.inj (hqa.symm.trans hx)
      subst this
      exact ⟨a, by simp, by omega⟩
    · exact ⟨qa, by simp [upd_apply, Ne.symm hxq, hqa], qz⟩

/-- Replacing a byte block by an array of the same size keeps the four buffers. -/
theorem _root_.Zlib.Deflate.Spec.DBlocks.bytes_set {h : Heap} {d : DeflateState} {w p q b : Nat}
    (hB : DBlocks h d w p q b) (x : Nat) (a : Array UInt8) (a0 : Array UInt8) (hx : h.bytes x = some a0)
    (hsz : a.size = a0.size) : DBlocks { h with bytes := upd h.bytes x (some a) } d w p q b := by
  obtain ⟨a1, a2, a3, a4, ⟨wa, hwa, wz⟩, r1, pa, qa, ⟨ba, hba, bz⟩, r4, ps, wb, pq, po⟩ := hB
  refine ⟨a1, a2, a3, a4, ?_, r1, pa, qa, ?_, r4, ps, wb, pq, po⟩
  · by_cases hxw : x = w
    · subst hxw
      have : wa = a0 := Option.some.inj (hwa.symm.trans hx)
      subst this
      exact ⟨a, by simp, by omega⟩
    · exact ⟨wa, by simp [upd_apply, Ne.symm hxw, hwa], wz⟩
  · by_cases hxb : x = b
    · subst hxb
      have : ba = a0 := Option.some.inj (hba.symm.trans hx)
      subst this
      exact ⟨a, by simp, by omega⟩
    · exact ⟨ba, by simp [upd_apply, Ne.symm hxb, hba], bz⟩

theorem _root_.Zlib.Deflate.Spec.DStInv.words_set {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d)
    (x : Nat) (a a0 : Array UInt16) (hx : h.words x = some a0) (hsz : a.size = a0.size) :
    DStInv { h with words := upd h.words x (some a) } ds d := by
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  exact { hI with blocks := ⟨w, p, q, b, hB.words_set x a a0 hx hsz⟩ }

theorem _root_.Zlib.Deflate.Spec.DStInv.bytes_set {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d)
    (x : Nat) (a a0 : Array UInt8) (hx : h.bytes x = some a0) (hsz : a.size = a0.size)
    (hro : ∀ y, y = x → h.ro y = h.ro y) :
    DStInv { h with bytes := upd h.bytes x (some a) } ds d := by
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  exact { hI with blocks := ⟨w, p, q, b, hB.bytes_set x a a0 hx hsz⟩ }

/-- Replacing a block of words of a good heap by an array of the same size keeps it good. -/
theorem _root_.Zlib.Deflate.Spec.DGood.words_set {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (x : Nat) (a a0 : Array UInt16) (hx : h.words x = some a0) (hsz : a.size = a0.size) :
    DGood { h with words := upd h.words x (some a) } r ds z d := by
  have hS := shape_setW hx a
  refine ⟨⟨?_, ?_, hG.live.zst, hG.live.back, hG.live.status, hG.live.zalloc, hG.live.zfree⟩, hG.inv.words_set x a a0 hx hsz,
    hS.uniq hG.uniq, hS.fresh rfl hG.fresh, TreesInv.words_set hG.trees x a⟩
  · cases r <;> simpa [ZStreamRef.get] using hG.live.hz
  · exact hG.live.hs

/-- Replacing a byte block of a good heap by an array of the same size keeps it good. -/
theorem _root_.Zlib.Deflate.Spec.DGood.bytes_set {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (x : Nat) (a a0 : Array UInt8) (hx : h.bytes x = some a0) (hsz : a.size = a0.size) :
    DGood { h with bytes := upd h.bytes x (some a) } r ds z d := by
  have hS := shape_setB hx a
  refine ⟨⟨?_, ?_, hG.live.zst, hG.live.back, hG.live.status, hG.live.zalloc, hG.live.zfree⟩,
    hG.inv.bytes_set x a a0 hx hsz (fun _ _ => rfl), hS.uniq hG.uniq, hS.fresh rfl hG.fresh, TreesInv.bytes_set hG.trees x a a0 hx hsz⟩
  · cases r <;> simpa [ZStreamRef.get] using hG.live.hz
  · exact hG.live.hs

/-- The owned blocks are live. -/
theorem _root_.Zlib.Deflate.Spec.DOwned.live {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) {x : Nat} (hx : DOwned d ds x) : h.live x := by
  obtain ⟨w, p, q, b, hB⟩ := hG.inv.blocks
  rcases hx with rfl | ⟨w', hw, rfl⟩ | ⟨p', hp, rfl⟩ | ⟨q', hq, rfl⟩ | ⟨b', hb, rfl⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [hG.live.hs])))))
  · rw [hB.win] at hw; cases hw
    obtain ⟨a, ha, -⟩ := hB.wa
    exact Or.inl (by simp [ha])
  · rw [hB.prev] at hp; cases hp
    obtain ⟨a, ha, -⟩ := hB.pa
    exact Or.inr (Or.inl (by simp [ha]))
  · rw [hB.head] at hq; cases hq
    obtain ⟨a, ha, -⟩ := hB.qa
    exact Or.inr (Or.inl (by simp [ha]))
  · rw [hB.pbuf] at hb; cases hb
    obtain ⟨a, ha, -⟩ := hB.ba
    exact Or.inl (by simp [ha])


/-- **deflateStateCheck, safety and specification.** On every stream of the domain `StreamDom` (`NULL`, or a live stream
whose state pointer is `NULL`, a deflate state, or irrelevant because an allocator function is `NULL`) the check
returns without a fault and without changing the heap; it returns 0 exactly for an initialised stream (the stream and
its state point to each other, the allocator functions are not `NULL`, and the status is one of the eight values)
and 1 otherwise. -/
theorem deflateStateCheck_total {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) :
    ∃ v, deflateStateCheck strm h = .ok (v, h) ∧ (v = 0 ∧ DInitialised h strm ∨ v = 1 ∧ ¬ DInitialised h strm) := by
  rcases hD with rfl | ⟨r, z, rfl, hr, hcase⟩
  · refine ⟨1, by simp [deflateStateCheck], Or.inr ⟨rfl, ?_⟩⟩
    rintro ⟨r, ds, z, d, hh, -⟩; cases hh
  · have e1 : ldZStream (some r) h = .ok (z, h) := ldZStream_ok hr
    by_cases hza : z.zalloc = .null
    · refine ⟨1, by simp [deflateStateCheck, e1, hza], Or.inr ⟨rfl, ?_⟩⟩
      rintro ⟨r', ds, z', d, hh, hL⟩
      cases hh; exact hL.zalloc (by rw [hL.hz] at hr; cases hr; exact hza)
    by_cases hzf : z.zfree = .null
    · refine ⟨1, by simp [deflateStateCheck, e1, hza, hzf], Or.inr ⟨rfl, ?_⟩⟩
      rintro ⟨r', ds, z', d, hh, hL⟩
      cases hh; exact hL.zfree (by rw [hL.hz] at hr; cases hr; exact hzf)
    rcases hcase with h1 | h1 | h1 | ⟨ds, d, hzs, hst⟩
    · exact absurd h1 hza
    · exact absurd h1 hzf
    · refine ⟨1, by simp [deflateStateCheck, e1, hza, hzf, h1, castDeflateState], Or.inr ⟨rfl, ?_⟩⟩
      rintro ⟨r', ds, z', d, hh, hL⟩
      cases hh; rw [hL.hz] at hr; cases hr; rw [hL.zst] at h1; cases h1
    · by_cases c1 : d.strm = some r
      · by_cases c2 : GoodStatus d.status
        · have hL : DLive h r ds z d := ⟨hr, hst, hzs, c1, c2, hza, hzf⟩
          exact ⟨0, stateCheck_live hL, Or.inl ⟨rfl, r, ds, z, d, rfl, hL⟩⟩
        · refine ⟨1, ?_, Or.inr ⟨rfl, ?_⟩⟩
          · simp only [GoodStatus, not_or] at c2
            simp [deflateStateCheck, bind_app, e1, castD, ldD_eq, hza, hzf, hzs, hst, c1, c2]
          · rintro ⟨r', ds', z', d', hh, hL⟩
            cases hh
            rw [hL.hz] at hr; cases hr
            rw [hL.zst] at hzs; cases hzs
            rw [hL.hs] at hst; cases hst
            exact c2 hL.status
      · refine ⟨1, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · simp [deflateStateCheck, bind_app, e1, castD, ldD_eq, hza, hzf, hzs, hst, c1]
        · rintro ⟨r', ds', z', d', hh, hL⟩
          cases hh
          rw [hL.hz] at hr; cases hr
          rw [hL.zst] at hzs; cases hzs
          rw [hL.hs] at hst; cases hst
          exact c1 hL.back

/-- The state check fails: a function that starts with it returns `Z_STREAM_ERROR` and changes nothing. -/
theorem notInit_check {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm) :
    deflateStateCheck strm h = .ok (1, h) := by
  obtain ⟨v, hv, hc⟩ := deflateStateCheck_total hD
  rcases hc with ⟨rfl, hI⟩ | ⟨rfl, -⟩
  · exact absurd hI hN
  · exact hv

/-! ### The stream check refuses -/

/-- A function of the shape `if deflateStateCheck strm ≠ 0 then return X; rest` returns `X` and changes nothing when
the check refuses the stream. -/
theorem check_refuse {α : Type} {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (X : α) (rest : M α) :
    (do if (← deflateStateCheck strm) != 0 then return X
        rest : M α) h = .ok (X, h) := by
  simp [bind_app, notInit_check hD hN]

end Zlib.Deflate.Proofs
