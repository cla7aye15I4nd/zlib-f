import ZlibF.Zlib.«inflate.c»
import ZlibF.Proof.«zutil.c»

/-!
# inflate.c: the stream invariant and the lemmas the stream functions share

The statements of `docs/proof/inflate.md`, the window invariant W and of `docs/spec/api/inflate-stream.md`.
The definitions of namespace `Zlib.Inflate.Spec` are part of what a theorem means (they are locked by the audit); the
lemmas of `Zlib.Inflate.Proofs` are not.

* `Uniq`: a block number holds an object of at most one table (the allocator takes `nextBlk` for every kind).
* `WinInv`: the window of an inflate state.
* `StInv`: the representation invariant of an inflate state (window, bit buffer, table pointers).
* `Live`: the stream is one that `inflateStateCheck` accepts, and its state is the record `st` at block `zs`.
* `Good`: `Live`, `StInv`, `Uniq` and `Fresh` together.
-/

namespace Zlib.Inflate.Spec
open C

/-- The heap with the state record `zs` replaced. -/
def setI (h : Heap) (zs : Nat) (s : InflateState) : Heap := { h with istates := upd h.istates zs (some s) }

/-- 1 if the table entry holds an object, else 0. -/
def cnt {α : Type} (o : Option α) : Nat := if o.isSome then 1 else 0

@[simp] theorem cnt_none {α : Type} : cnt (none : Option α) = 0 := rfl
@[simp] theorem cnt_some {α : Type} (a : α) : cnt (some a) = 1 := rfl

/-- A block number holds an object of at most one table. -/
def Uniq (h : Heap) : Prop := ∀ b,
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) +
  cnt (h.gzstates b) ≤ 1

/-- The window of an inflate state `st`: `NULL` with nothing in use, or a writable byte block of `2^wbits` bytes.
`wsize` is 0 or `2^wbits`; `whave` bytes are valid; `wnext` is the next write position, which equals `whave` while the
window is not full (`docs/proof/inflate.md`, invariant W). -/
structure WinInv (h : Heap) (st : InflateState) : Prop where
  wbits : st.wbits.toNat ≤ 15
  block : st.window = .null ∨
    ∃ w a, st.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧ a.size = 2 ^ st.wbits.toNat
  nullws : st.window = .null → st.wsize = 0
  ws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat
  hv : st.whave.toNat ≤ st.wsize.toNat
  wn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0)
  eq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat

/-- The table pointers of the state `zs`: `next` is in `codes`; `lencode` and `distcode` are both in `codes` (a
dynamic block, or the start) or are the two static fixed tables (a stream stopped inside a fixed block). -/
def PtrInv (zs : Nat) (st : InflateState) : Prop :=
  (∃ i, st.next = .ref (.istate_codes zs) i ∧ i ≤ 1444) ∧
  ((∃ i j, st.lencode = .ref (.istate_codes zs) i ∧ st.distcode = .ref (.istate_codes zs) j ∧ i ≤ 1443 ∧ j ≤ 1443) ∨
   (st.lencode = .ref .st_lenfix 0 ∧ st.distcode = .ref .st_distfix 0))

/-- The representation invariant of an inflate state, as far as the stream functions need it: the arrays have the
size of the C declaration, the window invariant, `reqbits` is a valid window size, the bit buffer holds at most 39 bits
(`NEEDBITS` of at most 32 bits pulls whole bytes while fewer are present), and the table pointers. -/
structure StInv (h : Heap) (zs : Nat) (st : InflateState) : Prop where
  wf : st.WellFormed
  win : WinInv h st
  reqbits : st.reqbits.toNat ≤ 15
  bits : st.bits.toNat ≤ 39
  ptr : PtrInv zs st

/-- The stream `r` is the record `z`; its state is the record `st` at block `zs`, which points back to the stream; the
mode is in the range `inflateStateCheck` accepts; the stream has the default allocator functions or none. -/
structure Live (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (st : InflateState) : Prop where
  hz : r.get h = some z
  hs : h.istates zs = some st
  zst : z.state = some (.inflate zs)
  back : st.strm = some r
  mode : HEAD ≤ st.mode ∧ st.mode ≤ SYNC
  zalloc : z.zalloc ≠ .null
  zfree : z.zfree ≠ .null

/-- The stream functions can allocate and free: the allocator functions are the default ones (the only ones the model
has; any other makes the translation fault). -/
def DefAlloc (z : ZStream) : Prop := z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree"

/-- Everything the stream functions assume of the heap around a live stream. -/
structure Good (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (st : InflateState) : Prop where
  live : Live h r zs z st
  inv : StInv h zs st
  uniq : Uniq h
  fresh : Fresh h

/-- The window block of the state, if there is one. -/
def WinBlk (st : InflateState) (w : Nat) : Prop := st.window = .ref (.blk w) 0

/-- The blocks a stream owns: its state record and its window block. -/
def OwnedBy (zs : Nat) (st : InflateState) (b : Nat) : Prop := b = zs ∨ ∃ w, WinBlk st w ∧ b = w

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

@[simp] theorem setI_istates_same (h : Heap) (zs : Nat) (s : InflateState) : (setI h zs s).istates zs = some s := by
  simp [setI]
@[simp] theorem setI_istates_ne (h : Heap) (zs x : Nat) (s : InflateState) (hx : x ≠ zs) :
    (setI h zs s).istates x = h.istates x := by simp [setI, upd_ne _ _ _ _ hx]
@[simp] theorem setI_bytes (h : Heap) (zs : Nat) (s : InflateState) : (setI h zs s).bytes = h.bytes := rfl
@[simp] theorem setI_streams (h : Heap) (zs : Nat) (s : InflateState) : (setI h zs s).streams = h.streams := rfl
@[simp] theorem setI_gzstates (h : Heap) (zs : Nat) (s : InflateState) : (setI h zs s).gzstates = h.gzstates := rfl
@[simp] theorem setI_ro (h : Heap) (zs : Nat) (s : InflateState) : (setI h zs s).ro = h.ro := rfl
@[simp] theorem setI_nextBlk (h : Heap) (zs : Nat) (s : InflateState) : (setI h zs s).nextBlk = h.nextBlk := rfl
@[simp] theorem setI_setI (h : Heap) (zs : Nat) (s s' : InflateState) : setI (setI h zs s) zs s' = setI h zs s' := by
  simp [setI, upd_upd]

theorem ZStreamRef.get_put_same {h : Heap} {r : ZStreamRef} {z : ZStream} (e : r.get h = some z) (v : ZStream) :
    r.get (r.put h v) = some v := by
  cases r with
  | tab i => simp [ZStreamRef.get] at e; simp [ZStreamRef.put, ZStreamRef.get, e]
  | in_gzstate_strm i =>
    simp [ZStreamRef.get] at e
    obtain ⟨g, hg, -⟩ := e
    simp [ZStreamRef.put, ZStreamRef.get, hg]

@[simp] theorem ZStreamRef.get_setI (h : Heap) (r : ZStreamRef) (zs : Nat) (s : InflateState) :
    r.get (setI h zs s) = r.get h := by
  cases r <;> rfl

@[simp] theorem ZStreamRef.put_istates (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).istates = h.istates := by
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

@[simp] theorem ZStreamRef.put_dstates (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).dstates = h.dstates := by
  cases r with
  | tab i => simp only [ZStreamRef.put]; split <;> rfl
  | in_gzstate_strm i => simp only [ZStreamRef.put]; split <;> rfl

@[simp] theorem ZStreamRef.put_gzheaders (h : Heap) (r : ZStreamRef) (v : ZStream) : (r.put h v).gzheaders = h.gzheaders := by
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

@[simp] theorem ZStreamRef.put_setI (h : Heap) (r : ZStreamRef) (zs : Nat) (s : InflateState) (v : ZStream) :
    r.put (setI h zs s) v = setI (r.put h v) zs s := by
  cases r with
  | tab i => simp only [ZStreamRef.put, setI]; cases hh : h.streams i <;> simp
  | in_gzstate_strm i => simp only [ZStreamRef.put, setI]; cases hh : h.gzstates i <;> simp

/-! ### Reading and writing the stream and the state -/

theorem castI {h : Heap} {zs : Nat} : castInflateState (some (.inflate zs)) h = .ok (some (.tab zs), h) := rfl

/-- The access functions as rewrite rules: they read the table, so that a proof rewrites with the facts about the table. -/
theorem ldI_eq (h : Heap) (i : Nat) : ldInflateState (some (.tab i)) h =
    match h.istates i with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (inflate_state)") := rfl

theorem ldZ_eq (h : Heap) (r : ZStreamRef) : ldZStream (some r) h =
    match r.get h with
    | some v => .ok (v, h)
    | none => .error (.ub "access through a dangling pointer (z_stream)") := rfl

theorem rdI_eq {α : Type} (h : Heap) (i : Nat) (f : InflateState → α) : rdS (some (.tab i)) f h =
    match h.istates i with
    | some v => .ok (f v, h)
    | none => .error (.ub "access through a dangling pointer (inflate_state)") := by
  simp only [rdS, bind_app, ldI_eq]; cases h.istates i <;> rfl

theorem rdZ_eq {α : Type} (h : Heap) (r : ZStreamRef) (f : ZStream → α) : rdZ (some r) f h =
    match r.get h with
    | some v => .ok (f v, h)
    | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  simp only [rdZ, bind_app, ldZ_eq]; cases r.get h <;> rfl

theorem wrI_eq (h : Heap) (i : Nat) (f : InflateState → InflateState) : wrS (some (.tab i)) f h =
    match h.istates i with
    | some v => .ok ((), setI h i (f v))
    | none => .error (.ub "access through a dangling pointer (inflate_state)") := by
  cases hh : h.istates i with
  | none => simp [wrS, bind_app, ldI_eq, hh]
  | some v => simp [wrS, bind_app, ldI_eq, hh, stInflateState_tab hh, setI]

theorem wrZ_eq (h : Heap) (r : ZStreamRef) (f : ZStream → ZStream) : wrZ (some r) f h =
    match r.get h with
    | some v => .ok ((), r.put h (f v))
    | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  have hro : r.isRo = false := by cases r <;> rfl
  cases hh : r.get h with
  | none => simp [wrZ, bind_app, ldZ_eq, hh]
  | some v => simp [wrZ, bind_app, ldZ_eq, hh, stZStream_ok hh hro]

theorem stI_eq (h : Heap) (i : Nat) (v : InflateState) : stInflateState (some (.tab i)) v h =
    match h.istates i with
    | some _ => .ok ((), setI h i v)
    | none => .error (.ub "access through a dangling pointer (inflate_state)") := by
  cases hh : h.istates i with
  | none => simp [stInflateState, InflateStateRef.get, hh]
  | some w => simp [stInflateState_tab hh, setI, hh]

theorem stZ_eq (h : Heap) (r : ZStreamRef) (v : ZStream) : stZStream (some r) v h =
    match r.get h with
    | some _ => .ok ((), r.put h v)
    | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  have hro : r.isRo = false := by cases r <;> rfl
  cases hh : r.get h with
  | none => simp [stZStream, hh]
  | some w => simp [stZStream_ok hh hro, hh]

/-- Evaluate a straight-line sequence of accesses to a stream and its state. -/
macro "isimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [bind_app, pure_app, ldI_eq, ldZ_eq, rdI_eq, rdZ_eq, wrI_eq, wrZ_eq, stI_eq, stZ_eq, castI, $ts,*])

/-! ### The stream check -/

theorem stateCheck_live {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) : inflateStateCheck (some r) h = .ok (0, h) := by
  obtain ⟨hz, hs, zst, back, ⟨m1, m2⟩, za, zf⟩ := hL
  have e1 : ldZStream (some r) h = .ok (z, h) := ldZStream_ok hz
  unfold inflateStateCheck
  have c : ¬ (st.mode < HEAD ∨ SYNC < st.mode) := by
    rintro (c | c)
    · have := UInt32.lt_iff_toNat_lt.mp c; have := UInt32.le_iff_toNat_le.mp m1; omega
    · have := UInt32.lt_iff_toNat_lt.mp c; have := UInt32.le_iff_toNat_le.mp m2; omega
  simp [bind_app, e1, za, zf, zst, castInflateState_ok, ldInflateState_tab hs, back, c]

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Spec
open C

/-- The state record after `inflateResetKeep` (`zs` is its block number). -/
def resetKeepState (zs : Nat) (st : InflateState) : InflateState :=
  { st with
    total := 0, mode := HEAD, last := 0, havedict := 0, flags := -1, dmax := 32768, head := none,
    hold := 0, bits := 0, next := .ref (.istate_codes zs) 0, distcode := .ref (.istate_codes zs) 0,
    lencode := .ref (.istate_codes zs) 0, sane := 1, back := -1 }

/-- The stream record after `inflateResetKeep` of a stream whose state is `st`: `adler` is bit 0 of `wrap` unless
`wrap` is 0. -/
def resetKeepStream (z : ZStream) (st : InflateState) : ZStream :=
  { z with
    total_out := 0, total_in := 0, msg := .null, data_type := 0,
    adler := if st.wrap != 0 then Zlib.Inflate.i2ul (st.wrap &&& 1) else z.adler }

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem resetKeep_run {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) :
    inflateResetKeep (some r) h = .ok (Z_OK, setI (r.put h (resetKeepStream z st)) zs (resetKeepState zs st)) := by
  have hz := hL.hz
  have hs := hL.hs
  unfold inflateResetKeep
  by_cases hw : st.wrap = 0
  · isimp [stateCheck_live hL, hL.zst, hz, hs, resetKeepState, resetKeepStream, hw, codesP]
  · isimp [stateCheck_live hL, hL.zst, hz, hs, resetKeepState, resetKeepStream, hw, codesP]


/-! ### Which objects exist: the shape of a heap -/

/-- The two heaps hold an object in the same tables at the same block numbers (the objects may differ). -/
def Shape (h h' : Heap) : Prop := ∀ b, (h'.bytes b).isSome = (h.bytes b).isSome ∧ (h'.words b).isSome = (h.words b).isSome ∧
  (h'.streams b).isSome = (h.streams b).isSome ∧ (h'.gzheaders b).isSome = (h.gzheaders b).isSome ∧
  (h'.dstates b).isSome = (h.dstates b).isSome ∧ (h'.istates b).isSome = (h.istates b).isSome ∧
  (h'.gzstates b).isSome = (h.gzstates b).isSome

theorem Shape.refl (h : Heap) : Shape h h := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Shape.trans {h1 h2 h3 : Heap} (a : Shape h1 h2) (b : Shape h2 h3) : Shape h1 h3 := by
  intro x
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a x
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := b x
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩

theorem Shape.uniq {h h' : Heap} (hS : Shape h h') (hU : Uniq h) : Uniq h' := by
  intro b
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hS b
  have := hU b
  simp only [cnt, e1, e2, e3, e4, e5, e6, e7] at this ⊢
  exact this

theorem Shape.live {h h' : Heap} (hS : Shape h h') (b : Nat) : h'.live b ↔ h.live b := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hS b
  simp only [Heap.live, ← Option.isSome_iff_ne_none, e1, e2, e3, e4, e5, e6, e7]

theorem Shape.fresh {h h' : Heap} (hS : Shape h h') (hn : h'.nextBlk = h.nextBlk) (hF : Fresh h) : Fresh h' := by
  intro b hb hl
  exact hF b (by omega) ((hS.live b).1 hl)

theorem shape_setI {h : Heap} {zs : Nat} {s0 : InflateState} (e : h.istates zs = some s0) (s : InflateState) :
    Shape h (setI h zs s) := by
  intro b
  by_cases hb : b = zs
  · subst hb; simp [setI, e]
  · simp [setI, upd_ne _ _ _ _ hb]

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

/-! ### Preserving the invariants -/

theorem _root_.Zlib.Inflate.Spec.WinInv.congr {h h' : Heap} {st : InflateState} (hb : h'.bytes = h.bytes) (hr : h'.ro = h.ro)
    (hW : WinInv h st) : WinInv h' st := by
  refine ⟨hW.wbits, ?_, hW.nullws, hW.ws, hW.hv, hW.wn, hW.eq⟩
  rcases hW.block with hn | ⟨w, a, hw, ha, hro, hsz⟩
  · exact Or.inl hn
  · exact Or.inr ⟨w, a, hw, by rw [hb]; exact ha, by rw [hr]; exact hro, hsz⟩

theorem _root_.Zlib.Inflate.Spec.StInv.congr {h h' : Heap} {zs : Nat} {st : InflateState} (hb : h'.bytes = h.bytes) (hr : h'.ro = h.ro)
    (hI : StInv h zs st) : StInv h' zs st :=
  ⟨hI.wf, hI.win.congr hb hr, hI.reqbits, hI.bits, hI.ptr⟩

/-- Rewrite the stream record and the state record of a live stream, keeping the state pointer, the back pointer, the
mode range and the allocator functions. -/
theorem _root_.Zlib.Inflate.Spec.Good.setZI {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) {z' : ZStream} {st' : InflateState}
    (hz : z'.state = z.state) (hza : z'.zalloc ≠ .null) (hzf : z'.zfree ≠ .null) (hback : st'.strm = st.strm)
    (hm : HEAD ≤ st'.mode ∧ st'.mode ≤ SYNC) (hI : StInv h zs st') :
    Good (setI (r.put h z') zs st') r zs z' st' := by
  have hS : Shape h (setI (r.put h z') zs st') :=
    (shape_put hG.live.hz z').trans (shape_setI (by simpa using hG.live.hs) st')
  refine ⟨⟨?_, by simp, hz.trans hG.live.zst, hback.trans hG.live.back, hm, hza, hzf⟩, StInv.congr (h := h) (h' := setI (r.put h z') zs st') (by simp) (by simp) hI,
    hS.uniq hG.uniq, hS.fresh (by simp) hG.fresh⟩
  simp [ZStreamRef.get_put, hG.live.hz]

theorem Shape.owns {h h' : Heap} (hS : Shape h h') {S : Nat → Prop} (hO : h.Owns S) : h'.Owns S :=
  fun b => (hS.live b).trans (hO b)

/-! ### The stream check, in general -/

theorem hdec {a b : UInt32} : a ≤ b ∨ b < a := by
  rcases Nat.lt_or_ge b.toNat a.toNat with h | h
  · exact Or.inr (UInt32.lt_iff_toNat_lt.mpr h)
  · exact Or.inl (UInt32.le_iff_toNat_le.mpr h)

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Spec
open C

/-- The streams `inflateStateCheck` handles: `NULL`, or a live stream record that has a `NULL` allocator function, or no
state, or a state that is a live inflate state record. (A state that is a deflate state, a freed state or a freed
stream is undefined behaviour in C and a fault here.) -/
def StreamDom (h : Heap) (strm : ZStreamPtr) : Prop :=
  strm = none ∨ ∃ r z, strm = some r ∧ r.get h = some z ∧
    (z.zalloc = .null ∨ z.zfree = .null ∨ z.state = none ∨ ∃ zs st, z.state = some (.inflate zs) ∧ h.istates zs = some st)

/-- The heap after `free(p)` for a window pointer: the byte block is gone, everything else is as it was. -/
def freeWin (h : Heap) (p : BPtr) : Heap :=
  match p with
  | .ref (.blk w) 0 => { h with bytes := upd h.bytes w none }
  | _ => h

/-- The stream is one `inflateStateCheck` accepts. -/
def Initialised (h : Heap) (strm : ZStreamPtr) : Prop := ∃ r zs z st, strm = some r ∧ Live h r zs z st

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- **inflateStateCheck, safety and specification.** On every stream of the domain `StreamDom` (`NULL`, or a live stream
whose state pointer is `NULL`, an inflate state or irrelevant because an allocator function is `NULL`) the check
returns without a fault and without changing the heap; it returns 0 exactly for an initialised stream (the stream and
its state point to each other, the allocator functions are not `NULL`, and the mode is in the range from `HEAD` to
`SYNC`) and 1 otherwise. -/
theorem inflateStateCheck_total {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) :
    ∃ v, inflateStateCheck strm h = .ok (v, h) ∧ (v = 0 ∧ Initialised h strm ∨ v = 1 ∧ ¬ Initialised h strm) := by
  rcases hD with rfl | ⟨r, z, rfl, hr, hcase⟩
  · refine ⟨1, by simp [inflateStateCheck], Or.inr ⟨rfl, ?_⟩⟩
    rintro ⟨r, zs, z, st, hh, -⟩; cases hh
  · have e1 : ldZStream (some r) h = .ok (z, h) := ldZStream_ok hr
    by_cases hza : z.zalloc = .null
    · refine ⟨1, by simp [inflateStateCheck, e1, hza], Or.inr ⟨rfl, ?_⟩⟩
      rintro ⟨r', zs, z', st, hh, hL⟩
      cases hh; exact hL.zalloc (by rw [hL.hz] at hr; cases hr; exact hza)
    by_cases hzf : z.zfree = .null
    · refine ⟨1, by simp [inflateStateCheck, e1, hza, hzf], Or.inr ⟨rfl, ?_⟩⟩
      rintro ⟨r', zs, z', st, hh, hL⟩
      cases hh; exact hL.zfree (by rw [hL.hz] at hr; cases hr; exact hzf)
    rcases hcase with h1 | h1 | h1 | ⟨zs, st, hzs, hst⟩
    · exact absurd h1 hza
    · exact absurd h1 hzf
    · refine ⟨1, by simp [inflateStateCheck, e1, hza, hzf, h1, castInflateState], Or.inr ⟨rfl, ?_⟩⟩
      rintro ⟨r', zs, z', st, hh, hL⟩
      cases hh; rw [hL.hz] at hr; cases hr; rw [hL.zst] at h1; cases h1
    · have ec : castInflateState z.state h = .ok (some (.tab zs), h) := by rw [hzs]; exact castI
      by_cases c1 : st.strm = some r
      · by_cases c2 : st.mode < HEAD ∨ SYNC < st.mode
        · refine ⟨1, ?_, Or.inr ⟨rfl, ?_⟩⟩
          · simp [inflateStateCheck, bind_app, e1, castI, ldInflateState_tab hst, hza, hzf, hzs, c1, c2]
          · rintro ⟨r', zs', z', st', hh, hL⟩
            cases hh
            rw [hL.hz] at hr; cases hr
            rw [hL.zst] at hzs; cases hzs
            rw [hL.hs] at hst; cases hst
            have m1 := UInt32.le_iff_toNat_le.mp hL.mode.1
            have m2 := UInt32.le_iff_toNat_le.mp hL.mode.2
            rcases c2 with c | c
            · have := UInt32.lt_iff_toNat_lt.mp c; omega
            · have := UInt32.lt_iff_toNat_lt.mp c; omega
        · have m1 : HEAD ≤ st.mode := by
            rcases hdec (a := HEAD) (b := st.mode) with c | c
            · exact c
            · exact absurd (Or.inl c) c2
          have m2 : st.mode ≤ SYNC := by
            rcases hdec (a := st.mode) (b := SYNC) with c | c
            · exact c
            · exact absurd (Or.inr c) c2
          have hL : Live h r zs z st := ⟨hr, hst, hzs, c1, ⟨m1, m2⟩, hza, hzf⟩
          exact ⟨0, stateCheck_live hL, Or.inl ⟨rfl, r, zs, z, st, rfl, hL⟩⟩
      · refine ⟨1, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · simp [inflateStateCheck, bind_app, e1, castI, ldInflateState_tab hst, hza, hzf, hzs, c1]
        · rintro ⟨r', zs', z', st', hh, hL⟩
          cases hh
          rw [hL.hz] at hr; cases hr
          rw [hL.zst] at hzs; cases hzs
          rw [hL.hs] at hst; cases hst
          exact c1 hL.back


/-- The state check fails: a function that starts with it returns `Z_STREAM_ERROR` and changes nothing. -/
theorem notInit_check {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ Initialised h strm) :
    inflateStateCheck strm h = .ok (1, h) := by
  obtain ⟨v, hv, hc⟩ := inflateStateCheck_total hD
  rcases hc with ⟨rfl, hI⟩ | ⟨rfl, -⟩
  · exact absurd hI hN
  · exact hv

/-! ### `inflateResetKeep` -/

theorem _root_.Zlib.Inflate.Spec.StInv.resetKeep {h : Heap} {zs : Nat} {st : InflateState} (hI : StInv h zs st) :
    StInv h zs (resetKeepState zs st) := by
  refine ⟨hI.wf, ?_, hI.reqbits, by simp [resetKeepState], ?_⟩
  · exact ⟨hI.win.wbits, hI.win.block, hI.win.nullws, hI.win.ws, hI.win.hv, hI.win.wn, hI.win.eq⟩
  · refine ⟨⟨0, by simp [resetKeepState], by omega⟩, Or.inl ⟨0, 0, by simp [resetKeepState], by simp [resetKeepState], by omega, by omega⟩⟩

theorem mode_head : HEAD ≤ HEAD ∧ HEAD ≤ SYNC := by decide

/-- **inflateResetKeep, safety.** On an initialised stream (`Good`) the call returns `Z_OK`, runs without a fault, and
changes exactly the stream record (`resetKeepStream`) and the state record (`resetKeepState`). Afterwards the stream is
initialised again with the invariants intact, and the set of live blocks is the same (no allocation, no free). -/
theorem inflateResetKeep_safe {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) :
    ∃ h', C.run (inflateResetKeep (some r)) h = .ok (Z_OK, h') ∧
      h' = setI (r.put h (resetKeepStream z st)) zs (resetKeepState zs st) ∧
      Good h' r zs (resetKeepStream z st) (resetKeepState zs st) ∧ (∀ b, h'.live b ↔ h.live b) := by
  refine ⟨_, resetKeep_run hG.live, rfl, ?_, ?_⟩
  · exact hG.setZI (by simp [resetKeepStream]) (by simpa [resetKeepStream] using hG.live.zalloc)
      (by simpa [resetKeepStream] using hG.live.zfree) (by simp [resetKeepState]) (by simpa [resetKeepState] using mode_head)
      hG.inv.resetKeep
  · intro b
    exact ((shape_put hG.live.hz _).trans (shape_setI (by simpa using hG.live.hs) _)).live b


/-! ### Uniqueness and freeing -/

theorem Uniq.bytes_only {h : Heap} (hU : Uniq h) {b : Nat} {a : Array UInt8} (hb : h.bytes b = some a) :
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

theorem Uniq.istates_only {h : Heap} (hU : Uniq h) {b : Nat} {a : InflateState} (hb : h.istates b = some a) :
    h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧ h.bytes b = none ∧
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
  · cases hx : h.bytes b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega
  · cases hx : h.gzstates b with
    | none => rfl
    | some _ => simp only [hx, cnt_some] at this <;> omega

theorem freeWin_blk (h : Heap) (w : Nat) : freeWin h (.ref (.blk w) 0) = { h with bytes := upd h.bytes w none } := rfl
theorem freeWin_null (h : Heap) : freeWin h .null = h := rfl

@[simp] theorem freeWin_istates (h : Heap) (p : BPtr) : (freeWin h p).istates = h.istates := by
  unfold freeWin; split <;> rfl
@[simp] theorem freeWin_streams (h : Heap) (p : BPtr) : (freeWin h p).streams = h.streams := by
  unfold freeWin; split <;> rfl
@[simp] theorem freeWin_gzstates (h : Heap) (p : BPtr) : (freeWin h p).gzstates = h.gzstates := by
  unfold freeWin; split <;> rfl
@[simp] theorem freeWin_nextBlk (h : Heap) (p : BPtr) : (freeWin h p).nextBlk = h.nextBlk := by
  unfold freeWin; split <;> rfl
@[simp] theorem freeWin_words (h : Heap) (p : BPtr) : (freeWin h p).words = h.words := by
  unfold freeWin; split <;> rfl
@[simp] theorem freeWin_ro (h : Heap) (p : BPtr) : (freeWin h p).ro = h.ro := by
  unfold freeWin; split <;> rfl
@[simp] theorem freeWin_dstates (h : Heap) (p : BPtr) : (freeWin h p).dstates = h.dstates := by
  unfold freeWin; split <;> rfl
@[simp] theorem freeWin_gzheaders (h : Heap) (p : BPtr) : (freeWin h p).gzheaders = h.gzheaders := by
  unfold freeWin; split <;> rfl

@[simp] theorem ZStreamRef.get_freeWin (h : Heap) (p : BPtr) (r : ZStreamRef) : r.get (freeWin h p) = r.get h := by
  cases r <;> simp [ZStreamRef.get]

@[simp] theorem ZStreamRef.put_freeWin (h : Heap) (p : BPtr) (r : ZStreamRef) (v : ZStream) :
    r.put (freeWin h p) v = freeWin (r.put h v) p := by
  cases p with
  | null => rfl
  | ref x o =>
    cases x with
    | blk w =>
      cases o with
      | zero => cases r <;> simp [ZStreamRef.put, freeWin] <;> split <;> rfl
      | succ o => rfl
    | _ => rfl

@[simp] theorem setI_freeWin (h : Heap) (p : BPtr) (zs : Nat) (s : InflateState) :
    setI (freeWin h p) zs s = freeWin (setI h zs s) p := by
  cases p with
  | null => rfl
  | ref x o =>
    cases x with
    | blk w => cases o with
      | zero => simp [freeWin, setI]
      | succ o => rfl
    | _ => rfl

theorem zfreeB_run {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hf : z.zfree = .fn "zcfree")
    {p : BPtr} (hp : p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false) :
    ZFREEB (some r) p h = .ok ((), freeWin h p) := by
  rcases hp with rfl | ⟨b, a, rfl, hb, hro⟩
  · simp [ZFREEB, ldZ_eq, hz, hf, Zlib.Zutil.zcfree, freeWin_null, freeB_null]
  · simp [ZFREEB, ldZ_eq, hz, hf, Zlib.Zutil.zcfree, freeWin_blk, freeB_ok hb hro]

theorem uniq_freeWin {h : Heap} (hU : Uniq h) (p : BPtr) : Uniq (freeWin h p) := by
  cases p with
  | null => exact hU
  | ref x o =>
    cases x with
    | blk w =>
      cases o with
      | zero =>
        intro b
        have := hU b
        by_cases hb : b = w
        · subst hb
          simp only [freeWin_blk, upd_same, cnt_none] at this ⊢
          omega
        · simpa only [freeWin_blk, upd_ne _ _ _ _ hb] using this
      | succ o => exact hU
    | _ => exact hU

theorem live_freeWin {h : Heap} (p : BPtr) (b : Nat) : (freeWin h p).live b → h.live b := by
  cases p with
  | null => exact id
  | ref x o =>
    cases x with
    | blk w =>
      cases o with
      | zero =>
        intro hl
        by_cases hb : b = w
        · subst hb
          simp only [Heap.live, freeWin_blk, upd_same] at hl
          rcases hl with hl | hl
          · exact absurd rfl hl
          · exact Or.inr hl
        · simp only [Heap.live, freeWin_blk, upd_ne _ _ _ _ hb] at hl
          exact hl
      | succ o => exact id
    | _ => exact id

theorem fresh_freeWin {h : Heap} (hF : Fresh h) (p : BPtr) : Fresh (freeWin h p) := by
  intro b hb hl
  exact hF b (by simpa using hb) (live_freeWin p b hl)

theorem owns_freeWin {h : Heap} (hU : Uniq h) {w : Nat} {a : Array UInt8} (hb : h.bytes w = some a) {S : Nat → Prop}
    (hO : h.Owns S) : (freeWin h (.ref (.blk w) 0)).Owns (fun b => S b ∧ b ≠ w) := by
  intro b
  by_cases hbw : b = w
  · subst hbw
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := Uniq.bytes_only hU hb
    simp [Heap.live, freeWin_blk, e1, e2, e3, e4, e5, e6]
  · have := hO b
    simp only [Heap.live, freeWin_blk, upd_ne _ _ _ _ hbw] at this ⊢
    simp [hbw, this]

end Zlib.Inflate.Proofs
