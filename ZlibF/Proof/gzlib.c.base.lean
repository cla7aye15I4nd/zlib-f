import ZlibF.Zlib.«gzlib.c»

/-!
# gzlib.c: the representation invariant of a gz handle and the rules that every proof of gzlib.c, gzread.c, gzwrite.c
and gzclose.c uses

A `gzFile` is a pointer into the `gzstates` table (`some (.in_gzstate_x gs)`); `gs` is the block number of the
`gz_state` record `s`. The invariant `GzGood h gs s` has the shape of `Good` of `inflate.c.base`:

* the record is live (`hs`) and its mode is `GZ_READ` or `GZ_WRITE` (what `gz_open` makes of the mode string);
* `path` is a NUL-terminated writable byte block, `msg` is `NULL` or the same kind of block, `in` and `out` are `NULL` or
  writable byte blocks, and the four blocks are pairwise different;
* `Z_MEM_ERROR` goes with no message (`gz_error` frees the message before it records an error);
* `Uniq` (a block number holds an object of at most one table) and `Fresh` (block numbers from `nextBlk` on are unused).

What is not in `GzGood`, on purpose: the pointer `x.next` (it dangles after a direct read, issue 5 of
`docs/spec/functions/gz-file.md`; `NextOk` is a separate hypothesis of the theorems that dereference it), and the
state of the embedded stream `strm` (the read and write proofs add it).
-/

namespace Zlib.Gzlib.Spec
open C Zlib.GzFs Zlib.Gzguts

/-- The heap with the `gz_state` record `gs` replaced. -/
def setS (h : Heap) (gs : Nat) (s : GzState) : Heap := { h with gzstates := upd h.gzstates gs (some s) }

/-- 1 if the table entry holds an object, else 0. -/
def cnt {α : Type} (o : Option α) : Nat := if o.isSome then 1 else 0

@[simp] theorem cnt_none {α : Type} : cnt (none : Option α) = 0 := rfl
@[simp] theorem cnt_some {α : Type} (a : α) : cnt (some a) = 1 := rfl

/-- A block number holds an object of at most one table. -/
def Uniq (h : Heap) : Prop := ∀ b,
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) +
  cnt (h.gzstates b) ≤ 1

/-- The two heaps hold an object in the same tables at the same block numbers (the objects may differ). -/
def Shape (h h' : Heap) : Prop := ∀ b, (h'.bytes b).isSome = (h.bytes b).isSome ∧ (h'.words b).isSome = (h.words b).isSome ∧
  (h'.streams b).isSome = (h.streams b).isSome ∧ (h'.gzheaders b).isSome = (h.gzheaders b).isSome ∧
  (h'.dstates b).isSome = (h.dstates b).isSome ∧ (h'.istates b).isSome = (h.istates b).isSome ∧
  (h'.gzstates b).isSome = (h.gzstates b).isSome

/-- The block of a byte pointer into a heap block, if it is one. -/
def ptrBlk : BPtr → Option Nat
  | .ref (.blk b) _ => some b
  | _ => none

/-- `p` is the start of the writable byte block `b`, which holds a NUL byte (a C string owned by the handle). -/
def StrBlk (h : Heap) (p : BPtr) (b : Nat) : Prop :=
  p = .ref (.blk b) 0 ∧ ∃ a : Array UInt8, h.bytes b = some a ∧ h.ro b = false ∧ ∃ k : Nat, a[k]? = some 0

/-- `NULL` or the start of a writable byte block. -/
def OptBlk (h : Heap) (p : BPtr) : Prop := p = .null ∨ ∃ b a, p = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false

/-- The representation invariant of the handle whose `gz_state` is the record `s` at block `gs`. -/
structure GzGood (h : Heap) (gs : Nat) (s : GzState) : Prop where
  hs : h.gzstates gs = some s
  mode : s.mode = GZ_READ ∨ s.mode = GZ_WRITE
  path : ∃ pb, StrBlk h s.path pb
  msg : s.msg = .null ∨ ∃ mb, StrBlk h s.msg mb
  inb : OptBlk h s.in
  outb : OptBlk h s.out
  nodup : ([s.path, s.msg, s.in, s.out].filterMap ptrBlk).Nodup
  memerr : s.err = Z_MEM_ERROR → s.msg = .null
  uniq : Uniq h
  fresh : Fresh h

/-- `x.next` can be advanced by up to `x.have` bytes: it is `NULL` with nothing buffered, or points into a live array with
`x.have` bytes after it; and it does not point into the message block. (After a direct read it can dangle: that case is
excluded by this hypothesis, and `seekTail_dangling_ub` shows the fault.) -/
def NextOk (h : Heap) (s : GzState) : Prop :=
  ((s.x.next = .null ∧ s.x.«have» = 0) ∨
    ∃ r a off, s.x.next = .ref r off ∧ Space.get h r = some a ∧ off + s.x.«have».toNat ≤ a.size) ∧
  (∀ b, ptrBlk s.x.next = some b → ptrBlk s.msg ≠ some b)

/-- The pointer advanced by `n` bytes (`Ptr.add` when it does not fault). -/
def padv : BPtr → Nat → BPtr
  | .null, _ => .null
  | .ref r o, n => .ref r (o + n)

/-- The handle pointer of the record at block `gs`. -/
def hnd (gs : Nat) : GzFilePtr := some (.in_gzstate_x gs)

end Zlib.Gzlib.Spec

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec

@[simp] theorem setS_gz_same (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).gzstates gs = some s := by
  simp [setS]
@[simp] theorem setS_gz_ne (h : Heap) (gs x : Nat) (s : GzState) (hx : x ≠ gs) :
    (setS h gs s).gzstates x = h.gzstates x := by simp [setS, upd_ne _ _ _ _ hx]
@[simp] theorem setS_bytes (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).bytes = h.bytes := rfl
@[simp] theorem setS_words (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).words = h.words := rfl
@[simp] theorem setS_streams (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).streams = h.streams := rfl
@[simp] theorem setS_gzheaders (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).gzheaders = h.gzheaders := rfl
@[simp] theorem setS_dstates (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).dstates = h.dstates := rfl
@[simp] theorem setS_istates (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).istates = h.istates := rfl
@[simp] theorem setS_ro (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).ro = h.ro := rfl
@[simp] theorem setS_nextBlk (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).nextBlk = h.nextBlk := rfl
@[simp] theorem setS_nalloc (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).nalloc = h.nalloc := rfl
@[simp] theorem setS_allocOk (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).allocOk = h.allocOk := rfl
@[simp] theorem setS_garbage (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).garbage = h.garbage := rfl
@[simp] theorem setS_static (h : Heap) (gs : Nat) (s : GzState) : (setS h gs s).static = h.static := rfl
@[simp] theorem setS_setS (h : Heap) (gs : Nat) (s s' : GzState) : setS (setS h gs s) gs s' = setS h gs s' := by
  simp [setS, upd_upd]

/-! ### Reading and writing the record and its fields -/

@[simp] theorem castState_hnd (gs : Nat) : castState (hnd gs) = some (.tab gs) := rfl
@[simp] theorem castFile_tab (gs : Nat) : castFile (some (.tab gs)) = hnd gs := rfl
@[simp] theorem strmOf_tab (gs : Nat) : strmOf (some (.tab gs)) = some (.in_gzstate_strm gs) := rfl
@[simp] theorem hnd_isNone (gs : Nat) : (hnd gs).isNone = false := rfl

theorem ldS_run {h : Heap} {gs : Nat} {s : GzState} (e : h.gzstates gs = some s) :
    ldS (some (.tab gs)) h = .ok (s, h) := ldGzState_tab e

theorem updS_run {h : Heap} {gs : Nat} {s : GzState} (e : h.gzstates gs = some s) (f : GzState → GzState) :
    updS (some (.tab gs)) f h = .ok ((), setS h gs (f s)) := by
  unfold updS
  simp [bind_app, ldGzState_tab e, stGzState_tab e, setS]

theorem updX_run {h : Heap} {gs : Nat} {s : GzState} (e : h.gzstates gs = some s) (f : GzFile → GzFile) :
    updX (some (.tab gs)) f h = .ok ((), setS h gs { s with x := f s.x }) := by
  unfold updX; exact updS_run e _

theorem ldZ_run {h : Heap} {gs : Nat} {s : GzState} (e : h.gzstates gs = some s) :
    ldZ (some (.in_gzstate_strm gs)) h = .ok (s.strm, h) := by
  unfold ldZ
  exact ldZStream_ok (r := .in_gzstate_strm gs) (v := s.strm) (by simp [ZStreamRef.get, e])

theorem updZ_run {h : Heap} {gs : Nat} {s : GzState} (e : h.gzstates gs = some s) (f : ZStream → ZStream) :
    updZ (some (.in_gzstate_strm gs)) f h = .ok ((), setS h gs { s with strm := f s.strm }) := by
  unfold updZ
  have e1 : ldZStream (some (.in_gzstate_strm gs)) h = .ok (s.strm, h) := ldZ_run e
  simp only [bind_app, e1]
  rw [stZStream_ok (r := .in_gzstate_strm gs) (v := s.strm) (by simp [ZStreamRef.get, e]) rfl]
  simp [ZStreamRef.put, e, setS]

/-! ### The arithmetic of the translation -/

theorem i64chk_ok (r : Int) (h : -9223372036854775808 ≤ r ∧ r < 9223372036854775808) :
    i64chk r = pure (Int64.ofInt r) := by
  simp [i64chk, h]

theorem i64add_run (a b : Int64) (hlo : -9223372036854775808 ≤ a.toInt + b.toInt)
    (hhi : a.toInt + b.toInt < 9223372036854775808) (h : Heap) :
    i64add a b h = .ok (Int64.ofInt (a.toInt + b.toInt), h) := by
  simp [i64add, i64chk, hlo, hhi]

theorem i64sub_run (a b : Int64) (hlo : -9223372036854775808 ≤ a.toInt - b.toInt)
    (hhi : a.toInt - b.toInt < 9223372036854775808) (h : Heap) :
    i64sub a b h = .ok (Int64.ofInt (a.toInt - b.toInt), h) := by
  simp [i64sub, i64chk, hlo, hhi]

theorem i64neg_run (a : Int64) (hlo : -9223372036854775808 ≤ -a.toInt)
    (hhi : -a.toInt < 9223372036854775808) (h : Heap) :
    i64neg a h = .ok (Int64.ofInt (-a.toInt), h) := by
  simp [i64neg, i64chk, hlo, hhi]

theorem i64add_ub (a b : Int64) (h : Heap) (hb : ¬ (-9223372036854775808 ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt < 9223372036854775808)) :
    i64add a b h = .error (.ub "signed overflow (long)") := by
  show i64chk _ h = _
  unfold i64chk; simp only [hb, ite_false]; rfl

theorem i64sub_ub (a b : Int64) (h : Heap) (hb : ¬ (-9223372036854775808 ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 9223372036854775808)) :
    i64sub a b h = .error (.ub "signed overflow (long)") := by
  show i64chk _ h = _
  unfold i64chk; simp only [hb, ite_false]; rfl

theorem i64neg_ub (a : Int64) (h : Heap) (hb : ¬ (-9223372036854775808 ≤ -a.toInt ∧ -a.toInt < 9223372036854775808)) :
    i64neg a h = .error (.ub "signed overflow (long)") := by
  show i64chk _ h = _
  unfold i64chk; simp only [hb, ite_false]; rfl

theorem bmod64 (n : Int) (h1 : -9223372036854775808 ≤ n) (h2 : n < 9223372036854775808) :
    n.bmod Int64.size = n := by
  have : Int64.size = 18446744073709551616 := rfl
  rw [this]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem i64_toInt_ofInt {n : Int} (h1 : -9223372036854775808 ≤ n) (h2 : n < 9223372036854775808) :
    (Int64.ofInt n).toInt = n := by
  rw [Int64.toInt_ofInt]; exact bmod64 n h1 h2

theorem u32ToI64_toInt (u : UInt32) : (u32ToI64 u).toInt = (u.toNat : Int) := by
  unfold u32ToI64
  rw [Int64.toInt_ofNat']
  have := u.toNat_lt
  exact bmod64 _ (by omega) (by omega)

/-! ### Preserving the invariant -/

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
  exact hF b (by omega) ((Shape.live hS b).1 hl)

theorem Shape.owns {h h' : Heap} (hS : Shape h h') {S : Nat → Prop} (hO : h.Owns S) : h'.Owns S :=
  fun b => (Shape.live hS b).trans (hO b)

theorem shape_setS {h : Heap} {gs : Nat} {s0 : GzState} (e : h.gzstates gs = some s0) (s : GzState) :
    Shape h (setS h gs s) := by
  intro b
  by_cases hb : b = gs
  · subst hb; simp [setS, e]
  · simp [setS, upd_ne _ _ _ _ hb]

/-- A heap that holds objects only where `h` does, with a `nextBlk` that is not smaller, is `Fresh` if `h` is. -/
theorem Fresh.of_sub {h h' : Heap} (hF : Fresh h) (hn : h.nextBlk ≤ h'.nextBlk) (hl : ∀ b, h'.live b → h.live b) :
    Fresh h' := fun b hb hb' => hF b (by omega) (hl b hb')

/-- The record, with any other record in its place that keeps the strings, the buffers, the mode and the message
rule, keeps the invariant. -/
theorem GzGood.withRec {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) {s' : GzState}
    (hm : s'.mode = s.mode ∨ (s'.mode = GZ_READ ∨ s'.mode = GZ_WRITE))
    (hp : s'.path = s.path) (hmsg : s'.msg = s.msg) (hi : s'.in = s.in) (ho : s'.out = s.out)
    (he : s'.err = Z_MEM_ERROR → s'.msg = .null) : GzGood (setS h gs s') gs s' := by
  have hS : Shape h (setS h gs s') := shape_setS hG.hs s'
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, he, Shape.uniq hS hG.uniq, Shape.fresh hS (by simp) hG.fresh⟩
  · rcases hm with h1 | h1
    · rw [h1]; exact hG.mode
    · exact h1
  · rw [hp]; simpa [StrBlk] using hG.path
  · rw [hmsg]; simpa [StrBlk] using hG.msg
  · rw [hi]; simpa [OptBlk] using hG.inb
  · rw [ho]; simpa [OptBlk] using hG.outb
  · rw [hp, hmsg, hi, ho]; exact hG.nodup


/-! ### Equation forms (for `simp`: no hypothesis to find) -/

theorem ldS_eq (h : Heap) (gs : Nat) : ldS (some (.tab gs)) h = match h.gzstates gs with
    | some v => .ok (v, h) | none => .error (.ub "access through a dangling pointer (gz_state)") := by
  cases hh : h.gzstates gs with
  | none => simp [ldS, ldGzState, GzStateRef.get, hh]
  | some v => simp [ldS_run hh, hh]

theorem updS_eq (h : Heap) (gs : Nat) (f : GzState → GzState) : updS (some (.tab gs)) f h = match h.gzstates gs with
    | some v => .ok ((), setS h gs (f v)) | none => .error (.ub "access through a dangling pointer (gz_state)") := by
  cases hh : h.gzstates gs with
  | none => simp [updS, ldGzState, GzStateRef.get, hh, bind_app]
  | some v => simp [updS_run hh, hh]

theorem updX_eq (h : Heap) (gs : Nat) (f : GzFile → GzFile) : updX (some (.tab gs)) f h = match h.gzstates gs with
    | some v => .ok ((), setS h gs { v with x := f v.x }) | none => .error (.ub "access through a dangling pointer (gz_state)") := by
  unfold updX; exact updS_eq h gs _

theorem ldZ_eq (h : Heap) (gs : Nat) : ldZ (some (.in_gzstate_strm gs)) h = match h.gzstates gs with
    | some v => .ok (v.strm, h) | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  cases hh : h.gzstates gs with
  | none => simp [ldZ, ldZStream, ZStreamRef.get, hh]
  | some v => simp [ldZ_run hh, hh]

theorem updZ_eq (h : Heap) (gs : Nat) (f : ZStream → ZStream) : updZ (some (.in_gzstate_strm gs)) f h = match h.gzstates gs with
    | some v => .ok ((), setS h gs { v with strm := f v.strm }) | none => .error (.ub "access through a dangling pointer (z_stream)") := by
  cases hh : h.gzstates gs with
  | none => simp [updZ, ldZ, ldZStream, ZStreamRef.get, hh, bind_app]
  | some v => simp [updZ_run hh, hh]

/-- Evaluate a straight-line sequence of accesses to a `gz_state` record and its embedded stream. -/
macro "gsimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [bind_app, pure_app, ldS_eq, updS_eq, updX_eq, ldZ_eq, updZ_eq, castState_hnd, $ts,*])

/-! ### Freeing a string block -/

/-- The heap after `free(p)` of a byte block. -/
def freeStr (h : Heap) (p : BPtr) : Heap :=
  match p with
  | .ref (.blk b) _ => { h with bytes := upd h.bytes b none }
  | _ => h

theorem freeB_run {h : Heap} {p : BPtr} {b : Nat} (hp : p = .ref (.blk b) 0) {a : Array UInt8}
    (ha : h.bytes b = some a) (hro : h.ro b = false) : freeB p h = .ok ((), freeStr h p) := by
  subst hp
  simp [freeB, freeStr, ha, hro]

theorem freeB_null (h : Heap) : freeB .null h = .ok ((), h) := rfl

@[simp] theorem freeStr_null (h : Heap) : freeStr h .null = h := rfl

@[simp] theorem freeStr_blk (h : Heap) (b : Nat) : freeStr h (.ref (.blk b) 0) = { h with bytes := upd h.bytes b none } := rfl

/-- The block numbers a handle's strings and buffers take. -/
def blocksOf (s : GzState) : List Nat := [s.path, s.msg, s.in, s.out].filterMap ptrBlk

end Zlib.Gzlib.Proofs
