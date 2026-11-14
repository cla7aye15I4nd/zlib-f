import ZlibF.Proof.«gzwrite.c.vacate»

/-!
# gzwrite.c: safety of `gz_write`

`gz_write_safe_of`: the skeleton statement `gz_write_safe` (branch `skeleton/gz`, `gz.skeleton-write.lean`), from the
facts of `gz_error` (`GzErrorSpec`, `GzErrorOwn`). The callees are `gz_init_run`, `gz_zero_safe_shape` and
`gz_comp_safe_shape_of'`.

The caller buffer is readable and not owned by the handle (`GzRange`, as `CB`). It stays so across every step that
returns to `gz_write` with success: the steps write only owned blocks, own no block that was live before and not
owned, and keep the `strerror` borrow when they succeed.

1. **Prefix.** `gz_init` when there are no buffers (on success the buffers exist), `gz_zero` when a skip is pending
   (on success no skip is left), and the position check of patch 0004: past it, `x.pos + len ≤ GZ_OFF_MAX`. The
   refusal calls `gz_error` with a literal.
2. **Small path** (`len < size`): the copy loop keeps `GzInv` between trips, with the pending input in `in`. A trip
   copies `min(size - have, len)` bytes, then compresses when `len` is left. Its measure is `2·len` plus one while
   input is pending: a trip that copies nothing compresses a full buffer, which then is empty.
3. **Large path**: the pending input is compressed first; then `next_in` points into the caller buffer and the
   invariant is `GzInvUpToInput` over that buffer. Each trip offers `min(len, 2^32 - 1)` bytes; on success
   `gz_comp` consumes them all and `next_in` is where the count says (`InTrack`). On failure, and at the end,
   `next_in` is set back to `in` with no pending input, which gives `GzInv`.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section write
variable {i : Nat}

/-! ## The caller buffer -/

/-- A caller range: readable, and none of its blocks is owned by the handle. -/
def CB (h : Heap) (s : GzState) (p : BPtr) (n : Nat) : Prop :=
  (∃ xs, Bytes h p n xs) ∧ ∀ b, ByteRoot p b → ¬ GzOwned h i s b

theorem cb_of_post {P : Heap → Nat → GzState → Prop} {h h' : Heap} {s : GzState} {fs : Fs} {p : BPtr} {n : Nat}
    (cb : CB (i := i) h s p n) (post : GzPost h i s [] fs h' P) (hbor : h'.libcErrorBorrow = h.libcErrorBorrow) :
    ∃ s', P h' i s' ∧ CB (i := i) h' s' p n := by
  obtain ⟨-, s', hp, -, -, ⟨fr, -⟩, -, ng⟩ := post
  have fr' : Frame h h' (GzOwned h i s) := fr
  obtain ⟨⟨xs, hb⟩, no⟩ := cb
  refine ⟨s', hp, ⟨xs, bytes_after hb no (fun r o hroot => get_of_frame fr' hbor r o hroot)⟩, fun b hr ho => ?_⟩
  rcases ng b ho with o | nl
  · exact no b hr o
  · exact nl (root_live_of_bytes hb hr)

theorem cb_put {h : Heap} {s v : GzState} {p : BPtr} {n : Nat} (cb : CB (i := i) h s p n)
    (ho : ∀ b, GzOwned (putGz h i v) i v b ↔ GzOwned h i s b) : CB (i := i) (putGz h i v) v p n := by
  obtain ⟨⟨xs, hb⟩, no⟩ := cb
  exact ⟨⟨xs, (bytes_putGz _ _ _ _ _ _).2 hb⟩, fun b hr x => no b hr ((ho b).1 x)⟩

theorem cb_ref {h : Heap} {s : GzState} {p : BPtr} {n : Nat} (cb : CB (i := i) h s p n) (hn : n ≠ 0) :
    ∃ r o a, p = .ref r o ∧ Space.get h r = some a ∧ o + n ≤ a.size := by
  obtain ⟨⟨xs, hb⟩, -⟩ := cb
  rcases hb with ⟨-, e, -⟩ | ⟨r, o, a, hp, hg, hle, -⟩
  · exact absurd e hn
  · exact ⟨r, o, a, hp, hg, hle⟩

/-- The caller range across a record write. -/
theorem cb_rec {H : Heap} {a b : GzState} {p : BPtr} {n : Nat} (cb : CB (i := i) (putGz H i a) a p n)
    (ho : ∀ x, GzOwned (putGz H i b) i b x ↔ GzOwned (putGz H i a) i a x) : CB (i := i) (putGz H i b) b p n := by
  obtain ⟨⟨xs, hb⟩, no⟩ := cb
  exact ⟨⟨xs, (bytes_putGz _ _ _ _ _ _).2 ((bytes_putGz _ _ _ _ _ _).1 hb)⟩, fun x hr y => no x hr ((ho x).1 y)⟩

/-- A tail of a caller range. -/
theorem cb_tail {h : Heap} {s : GzState} {r : BRef} {o n c : Nat} (cb : CB (i := i) h s (.ref r o) n) (hc : c ≤ n) :
    CB (i := i) h s (.ref r (o + c)) (n - c) := by
  obtain ⟨⟨xs, hb⟩, no⟩ := cb
  obtain ⟨ys, hys⟩ := bytes_sub hb (a := c) (m := n - c) (by omega)
  exact ⟨⟨ys, hys⟩, fun b hr => no b (by cases r <;> exact hr)⟩

/-- The caller range across a write of another byte block and of the record. -/
theorem cb_other {h h' : Heap} {s s' : GzState} {r : BRef} {o n : Nat} (cb : CB (i := i) h s (.ref r o) n)
    (hget : Space.get h' r = Space.get h r) (ho : ∀ b, GzOwned h' i s' b ↔ GzOwned h i s b) :
    CB (i := i) h' s' (.ref r o) n := by
  obtain ⟨⟨xs, hb⟩, no⟩ := cb
  refine ⟨⟨xs, ?_⟩, fun b hr x => no b hr ((ho b).1 x)⟩
  rcases hb with ⟨e, -, -⟩ | ⟨r', o', a, hp, hg, hle, hx⟩
  · cases e
  · cases hp
    exact Or.inr ⟨r, o, a, rfl, by rw [hget]; exact hg, hle, hx⟩

/-! ## Arithmetic -/

theorem int64_toUInt64_toNat {k : Int} (h0 : 0 ≤ k) (h1 : k < 9223372036854775808) :
    (Int64.ofInt k).toUInt64.toNat = k.toNat := by
  have hk : (Int64.ofInt k).toInt = k := Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) h1
  have h0' : (0 : Int64) ≤ Int64.ofInt k := by rw [Int64.le_iff_toInt_le, hk]; simpa using h0
  rw [Int64.toNat_toUInt64_of_le h0', ← Int64.toNat_toInt, hk]

theorem int64_toUInt32_toNat {k : Int} (h0 : 0 ≤ k) (h1 : k < 4294967296) :
    (Int64.ofInt k).toUInt64.toUInt32.toNat = k.toNat := by
  rw [UInt64.toNat_toUInt32, int64_toUInt64_toNat h0 (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem padv_ref_zero (r : BRef) (a : Nat) : padv (.ref r 0) a = .ref r a := by
  simp [padv]

theorem padv_zero_self (p : BPtr) : padv p 0 = p := by
  cases p <;> rfl

/-- The literal of the refusal of patch 0004 is a C string. -/
theorem posov_cstring (H : Heap) {k : Nat} (hk : strIndex "position overflow" = some k) :
    ∃ t, CString H (.ref (.str k) 0) t := by
  have hb : strBytes "position overflow" =
      #[112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 118, 101, 114, 102, 108, 111, 119, 0] := by
    decide +kernel
  have hg : Space.get H (BRef.str k) =
      some #[112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 118, 101, 114, 102, 108, 111, 119, 0] := by
    have he := strLitRef_get (h := H) hk
    rw [hb] at he
    exact he
  exact ⟨[112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 118, 101, 114, 102, 108, 111, 119],
    Or.inr ⟨.str k, 0, _, rfl, hg, by decide, by decide⟩, by decide, by decide⟩

/-- `memcpy` into the `in` block from a caller range in another view. -/
theorem memcpy_put {Hx : Heap} {w : GzState} {B : Nat} {arr sa : Array UInt8} {rs : BRef} {d os n : Nat}
    (hB : Hx.bytes B = some arr) (hro : Hx.ro B = false) (hsa : Space.get Hx rs = some sa) (hrs : rs ≠ BRef.blk B)
    (hd : d + n ≤ arr.size) (hos : os + n ≤ sa.size) :
    memcpyB (.ref (.blk B) d) (.ref rs os) n (putGz Hx i w) =
      .ok ((), putGz (Space.put Hx (BRef.blk B) (copyRange arr sa d os n)) i w) := by
  have g1 : Space.get (putGz Hx i w) (BRef.blk B) = some arr := hB
  have g2 : Space.get (putGz Hx i w) rs = some sa := by rw [get_putGz]; exact hsa
  have r1 : Space.ro (putGz Hx i w) (BRef.blk B) = false := hro
  have hne : BRef.blk B ≠ rs := fun e => hrs e.symm
  have e := Space.modify_eq (putGz Hx i w) (BRef.blk B) arr (fun da => copyRange da sa d os n) g1
  simp only [memcpyB, Ptr.memcpy, g1, g2, r1, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hd, hos, and_self,
    ne_eq, hne, not_false_eq_true, true_or]
  rw [e]
  rfl

/-! ## The prefix result -/

/-- The post-condition of `gz_write` from a start `(h0, s0, fs0)`. -/
def WP (h0 : Heap) (s0 : GzState) (fs0 : Fs) (len : UInt64) (r : UInt64) (fs' : Fs) (after : Heap) : Prop :=
  r.toNat ≤ len.toNat ∧ GetcUngetc.Eff i h0 s0 fs0 fs' after

/-! ## The small path: the copy loop -/

/-- The part of a trip of the copy loop from the `memcpy` on. -/
def smallRest (i : Nat) (put : UInt64) (l : Zlib.Gzwrite.WriteLoop) (s : GzState) (hv copy : UInt32) :
    G Zlib.Gzwrite.WriteLoop := do
  memcpyB (← s.«in».add hv.toNat) l.buf copy.toNat
  updZ (strmOf (gzSt i)) fun z => { z with avail_in := z.avail_in + copy }
  let s ← ldS (gzSt i)
  let np ← i64add s.x.pos (u32ToI64 copy)
  updX (gzSt i) fun x => { x with pos := np }
  let buf ← l.buf.add copy.toNat
  let len := l.len - copy.toUInt64
  if len == 0 then return { l with buf, len, brk := true }
  if (← Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH) == -1 then
    return { l with buf, len, res := some (if (← ldS (gzSt i)).again != 0 then put - len else 0) }
  return { l with buf, len }

/-- The part of a trip of the copy loop after the reset of an empty input. -/
def smallMid (i : Nat) (put : UInt64) (l : Zlib.Gzwrite.WriteLoop) : G Zlib.Gzwrite.WriteLoop := do
  let z ← ldZ (strmOf (gzSt i))
  let s ← ldS (gzSt i)
  let tp ← z.next_in.add z.avail_in.toNat
  let hv : UInt32 := (← Ptr.diff tp s.«in»).toUInt64.toUInt32
  let copy := s.size - hv
  if copy.toUInt64 > l.len then smallRest i put l s hv l.len.toUInt32 else smallRest i put l s hv copy

/-- A trip of the copy loop. -/
def smallBody (i : Nat) (put : UInt64) (l : Zlib.Gzwrite.WriteLoop) : G Zlib.Gzwrite.WriteLoop := do
  if (← ldZ (strmOf (gzSt i))).avail_in == 0 then
    let s ← ldS (gzSt i)
    updZ (strmOf (gzSt i)) fun z => { z with next_in := s.«in» }
    smallMid i put l
  else
    smallMid i put l

/-- The condition of the copy loop. -/
def smallCond (l : Zlib.Gzwrite.WriteLoop) : G (Bool × Zlib.Gzwrite.WriteLoop) :=
  pure (!l.brk && l.res.isNone, l)

/-- The state of the copy loop before a trip. -/
def SmallOn (h0 : Heap) (s0 : GzState) (fs0 fs : Fs) (put : UInt64) (Hx : Heap) (v : GzState)
    (l : Zlib.Gzwrite.WriteLoop) : Prop :=
  GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hx i v) ∧ GzInv (putGz Hx i v) i v ∧ v.mode = GZ_WRITE ∧ v.size ≠ 0 ∧
    v.skip = 0 ∧ 1 ≤ l.len.toNat ∧ l.len.toNat ≤ put.toNat ∧ l.len.toNat < v.size.toNat ∧
    v.x.pos.toInt + l.len.toNat ≤ 9223372036854775807 ∧ CB (i := i) (putGz Hx i v) v l.buf l.len.toNat

/-- The invariant of the copy loop: a trip to do, or the loop has ended. -/
def SJ (h0 : Heap) (s0 : GzState) (fs0 : Fs) (put : UInt64) (l : Zlib.Gzwrite.WriteLoop) (fs : Fs) (h : Heap) :
    Prop :=
  (l.brk = false ∧ l.res = none ∧ ∃ Hx v, h = putGz Hx i v ∧ SmallOn (i := i) h0 s0 fs0 fs put Hx v l) ∨
  (l.brk = true ∧ l.res = none ∧ GetcUngetc.Eff i h0 s0 fs0 fs h) ∨
  (∃ r, l.res = some r ∧ r.toNat ≤ put.toNat ∧ GetcUngetc.Eff i h0 s0 fs0 fs h)

/-- One while input is pending. -/
def availBit (i : Nat) (h : Heap) : Nat := match h.gzstates i with
  | some v => if v.strm.avail_in = 0 then 0 else 1
  | none => 0

/-- The measure of the copy loop. -/
def smallMu (i : Nat) (l : Zlib.Gzwrite.WriteLoop) (h : Heap) : Nat :=
  if (!l.brk && l.res.isNone) = true then 2 * l.len.toNat + availBit i h + 1 else 0

theorem availBit_put (Hx : Heap) (v : GzState) :
    availBit i (putGz Hx i v) = if v.strm.avail_in = 0 then 0 else 1 := by
  simp [availBit, putGz]

theorem uint32_add_toNat {a b : UInt32} (h : a.toNat + b.toNat < 4294967296) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

/-- **The rest of a trip of the copy loop**: the copy, the position, and the compression when input is left. -/
theorem smallRest_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {put : UInt64} {Hx : Heap} {v1 : GzState} {l : Zlib.Gzwrite.WriteLoop}
    {B a1 os : Nat} {arr sa : Array UInt8} {rs : BRef} {hv c : UInt32}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hx i v1)) (inv : GzInv (putGz Hx i v1) i v1)
    (hw : v1.mode = GZ_WRITE) (hsz : v1.size ≠ 0) (hsk : v1.skip = 0)
    (hin : v1.«in» = .ref (.blk B) 0) (hB : Hx.bytes B = some arr) (hro : Hx.ro B = false)
    (hasz : arr.size = 2 * v1.size.toNat)
    (hni : v1.strm.next_in = .ref (.blk B) a1) (ha : a1 + v1.strm.avail_in.toNat ≤ v1.size.toNat)
    (ha0 : v1.strm.avail_in = 0 → a1 = 0)
    (hhv : hv.toNat = a1 + v1.strm.avail_in.toNat)
    (hc : c.toNat = min (v1.size.toNat - (a1 + v1.strm.avail_in.toNat)) l.len.toNat)
    (hl1 : 1 ≤ l.len.toNat) (hlp : l.len.toNat ≤ put.toNat) (hls : l.len.toNat < v1.size.toNat)
    (hpos : v1.x.pos.toInt + l.len.toNat ≤ 9223372036854775807)
    (hbuf : l.buf = .ref rs os) (hsa : Space.get Hx rs = some sa) (hos : os + l.len.toNat ≤ sa.size)
    (hrs : rs ≠ BRef.blk B) (cb : CB (i := i) (putGz Hx i v1) v1 l.buf l.len.toNat)
    (hbl : l.brk = false) (hrl : l.res = none) :
    ∃ z fs' h', smallRest i put l v1 hv c fs (putGz Hx i v1) = .ok ((z, fs'), h') ∧
      SJ (i := i) h0 s0 fs0 put z fs' h' ∧
      smallMu i z h' < 2 * l.len.toNat + (if v1.strm.avail_in = 0 then 0 else 1) + 1 := by
  have hfs : FileSystem fs := E.2.1
  have hwv := inv.writer hw
  have hav := v1.strm.avail_in.toNat_lt
  have hS32 := v1.size.toNat_lt
  have hcl : c.toNat ≤ l.len.toNat := by rw [hc]; exact Nat.min_le_right _ _
  have hcs : a1 + v1.strm.avail_in.toNat + c.toNat ≤ v1.size.toNat := by rw [hc]; omega
  have hlo : 0 ≤ v1.x.pos.toInt := by
    have e := inv.common.pos.2.2
    rw [hwv.have0] at e
    simpa using e
  -- the copy
  obtain ⟨arr', harr'⟩ : ∃ arr', arr' = copyRange arr sa (0 + hv.toNat) os c.toNat := ⟨_, rfl⟩
  have hadd : Ptr.add v1.«in» (hv.toNat : Int) (putGz Hx i v1) =
      .ok (.ref (.blk B) (0 + hv.toNat), putGz Hx i v1) := by
    rw [hin]
    exact Ptr.add_nat_ok (R := BRef) (h := putGz Hx i v1) (a := arr) hB (by omega)
  obtain ⟨Hm, hHm⟩ : ∃ Hm, Hm = Space.put Hx (BRef.blk B) arr' := ⟨_, rfl⟩
  have hmem : memcpyB (.ref (.blk B) (0 + hv.toNat)) l.buf c.toNat (putGz Hx i v1) =
      .ok ((), putGz Hm i v1) := by
    rw [hbuf, hHm, harr']
    exact memcpy_put hB hro hsa hrs (by omega) (by omega)
  obtain ⟨invm, hom, frm, hlm⟩ := inv_in_put inv hw hsz hin (show (putGz Hx i v1).bytes B = some arr from hB) hro
    (show arr'.size = arr.size by rw [harr', size_copyRange])
  have em : Space.put (putGz Hx i v1) (BRef.blk B) arr' = putGz Hm i v1 := by rw [hHm]; rfl
  rw [em] at invm hom frm hlm
  have E1 : GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hm i v1) :=
    GetcUngetc.Eff.trans E inv (post_frame inv.common.live hfs frm hlm hom rfl rfl invm) (fun _ => Iff.rfl)
  -- the record writes
  obtain ⟨v2, hv2⟩ : ∃ v2 : GzState, v2 = { v1 with strm := { v1.strm with avail_in := v1.strm.avail_in + c } } :=
    ⟨_, rfl⟩
  have hU : updZ (strmOf (gzSt i)) (fun z => { z with avail_in := z.avail_in + c }) (putGz Hm i v1) =
      .ok ((), putGz Hm i v2) := by rw [hv2]; exact updZ_put _ _ _
  have hp2 : v2.x.pos = v1.x.pos := by rw [hv2]
  obtain ⟨np, hnp⟩ : ∃ np : Int64, np = Int64.ofInt (v1.x.pos.toInt + c.toNat) := ⟨_, rfl⟩
  have hnpv : np.toInt = v1.x.pos.toInt + c.toNat := by
    rw [hnp]; exact Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
  have fpos : i64add v2.x.pos (u32ToI64 c) (putGz Hm i v2) = .ok (np, putGz Hm i v2) := by
    have := Zlib.Gzlib.Proofs.i64add_run v1.x.pos (u32ToI64 c) (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt]; omega)
      (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt]; omega) (putGz Hm i v2)
    rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, ← hnp] at this
    rw [hp2]; exact this
  obtain ⟨v3, hv3⟩ : ∃ v3 : GzState, v3 = recW v1 v1.strm.next_in (v1.strm.avail_in + c) np v1.skip := ⟨_, rfl⟩
  have hX : updX (gzSt i) (fun x => { x with pos := np }) (putGz Hm i v2) = .ok ((), putGz Hm i v3) := by
    rw [hv3, hv2]; exact updX_put _ _ _
  have hcsum : (v1.strm.avail_in + c).toNat = v1.strm.avail_in.toNat + c.toNat := uint32_add_toNat (by omega)
  obtain ⟨inv3, ho3⟩ := inv_recW (h := putGz Hm i v1) (by simp [putGz]) (clear_of_inv invm hw) hw
    v1.strm.next_in (v1.strm.avail_in + c) np v1.skip
    ⟨by rw [hsk]; simp, by rw [hsk, hnpv]; simp; omega, by rw [hnpv, hwv.have0]; simp; omega⟩
    (Or.inr ⟨hsz, a1, by show v1.strm.next_in = padv v1.«in» a1; rw [hni, hin, padv_ref_zero], by
      show a1 + (v1.strm.avail_in + c).toNat ≤ v1.size.toNat; rw [hcsum]; omega⟩)
  have P3 := post_put (P := GzInv) (fs := fs) (h := putGz Hm i v1) (by simp [putGz]) invm.common.live hfs ho3 rfl rfl
    inv3
  rw [putGz_putGz, ← hv3] at P3 inv3 ho3
  have E2 : GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hm i v3) := GetcUngetc.Eff.trans E1 invm P3 (fun _ => Iff.rfl)
  have hw3 : v3.mode = GZ_WRITE := by rw [hv3]; exact hw
  have hsz3 : v3.size = v1.size := by rw [hv3]; rfl
  have hin3 : v3.«in» = v1.«in» := by rw [hv3]; rfl
  have hpos3 : v3.x.pos = np := by rw [hv3]; rfl
  have hsk3 : v3.skip = 0 := by rw [hv3]; exact hsk
  -- the caller buffer
  have hgetm : Space.get (putGz Hm i v3) rs = some sa := by
    rw [get_putGz, hHm, Zlib.Inflate.Proofs.byte_view_get_put_ne Hx hrs arr']; exact hsa
  have hbadd : Ptr.add l.buf (c.toNat : Int) (putGz Hm i v3) = .ok (.ref rs (os + c.toNat), putGz Hm i v3) := by
    rw [hbuf]; exact Ptr.add_nat_ok (R := BRef) (h := putGz Hm i v3) (a := sa) hgetm (by omega)
  obtain ⟨len', hlen'⟩ : ∃ len' : UInt64, len' = l.len - c.toUInt64 := ⟨_, rfl⟩
  have hcu : c.toUInt64.toNat = c.toNat := UInt32.toNat_toUInt64 c
  have hlenN : len'.toNat = l.len.toNat - c.toNat := by
    rw [hlen', UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hcu]; exact hcl), hcu]
  have hS : ∀ (H : Heap) (w : GzState), ldS (gzSt i) (putGz H i w) = .ok (w, putGz H i w) := fun H w => ldS_put H w
  have cbt : CB (i := i) (putGz Hm i v3) v3 (.ref rs (os + c.toNat)) len'.toNat := by
    have cb1 := cb_tail (r := rs) (o := os) (by rw [← hbuf]; exact cb) hcl
    rw [← hlenN] at cb1
    exact cb_other cb1 (by rw [hgetm, get_putGz]; exact hsa.symm) (fun b => (ho3 b).trans (hom b))
  by_cases hz : len' = 0
  · have hz' : (len' == 0) = true := by simp [hz]
    refine ⟨{ l with buf := .ref rs (os + c.toNat), len := len', brk := true }, fs, putGz Hm i v3, ?_,
      Or.inr (Or.inl ⟨rfl, hrl, E2⟩), by simp [smallMu]⟩
    unfold smallRest
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hadd,
      hmem, hU, hS, fpos, hX, hbadd, ← hlen', hz', ↓reduceIte]
  · have hz' : (len' == 0) = false := by simpa using hz
    have U3 := upTo_of_inv inv3 hw3 (by rw [hsz3]; exact hsz)
    obtain ⟨r, fs2, H2, run, hr, hk2, p2⟩ := comp_run err errOwn U3 hfs (by rw [hsz3]; exact hsz)
    have E3 := GetcUngetc.EffI.trans GetcUngetc.good_inv (good_cq _ _ _ _ _) E2 (by simp [putGz]) p2 hk2
    have hfs2 : FileSystem fs2 := E3.2.1
    have Ef : ∀ (hc2 : ∀ s', CQ ⟨v3.«in», v3.size.toNat⟩ v3 (putGz Hm i v3) Z_NO_FLUSH r H2 i s' → GzInv H2 i s'),
        GetcUngetc.Eff i h0 s0 fs0 fs2 H2 := fun hc2 => ⟨E3.1, GetcUngetc.GzPost.mono E3.2 hc2⟩
    have Eff2 : GetcUngetc.Eff i h0 s0 fs0 fs2 H2 :=
      Ef fun s' q => inv_of_cq (by rw [hsz3]; exact hsz) q
    obtain ⟨-, s2', q2', -⟩ := id p2
    obtain ⟨hs2, -, hw2, -⟩ := cq_base q2'
    have hcomp : Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH fs (putGz Hm i v3) = .ok ((r, fs2), putGz H2 i s2') := by
      rw [putGz_self hs2]; exact run
    rcases hr with rfl | rfl
    · -- the call succeeded: the input was compressed, the caller buffer is still readable
      have hbor : H2.libcErrorBorrow = (putGz Hm i v3).libcErrorBorrow := q2'.2.2.2 rfl
      obtain ⟨s2, q2, cb2⟩ := cb_of_post cbt p2 hbor
      obtain ⟨hs2b, -, -, -⟩ := cq_base q2
      have e2 : s2 = s2' := Option.some.inj (hs2b.symm.trans hs2)
      subst e2
      have inv2 : GzInv H2 i s2 := inv_of_cq (by rw [hsz3]; exact hsz) q2
      obtain ⟨-, -, -, sh2size, -, -, -, sh2skip, sh2pos, -, -, -⟩ := q2.2.1
      have hai0 : s2.strm.avail_in = 0 := q2.2.2.1 rfl rfl
      refine ⟨{ l with buf := .ref rs (os + c.toNat), len := len' }, fs2, putGz H2 i s2, ?_,
        Or.inl ⟨hbl, hrl, H2, s2, rfl, ?_⟩, ?_⟩
      · unfold smallRest
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hadd,
          hmem, hU, hS, fpos, hX, hbadd, ← hlen', hz', Bool.false_eq_true, ↓reduceIte, hcomp,
          int32_zero_ne_neg_one]
      · unfold SmallOn; rw [putGz_self hs2]
        have hz0 : len'.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
        refine ⟨Eff2, inv2, hw2, by rw [sh2size, hsz3]; exact hsz, by rw [sh2skip, hsk3], ?_, ?_, ?_, ?_, cb2⟩
        · show 1 ≤ len'.toNat; omega
        · show len'.toNat ≤ put.toNat; omega
        · show len'.toNat < s2.size.toNat; rw [sh2size, hsz3]; omega
        · show s2.x.pos.toInt + len'.toNat ≤ _; rw [sh2pos, hpos3, hnpv]; omega
      · have hb2 : availBit i (putGz H2 i s2) = 0 := by rw [availBit_put, if_pos hai0]
        simp only [smallMu, hbl, hrl, Bool.not_false, Option.isNone_none, Bool.and_self, ↓reduceIte, hb2]
        have hc0 : c.toNat = 0 → v1.strm.avail_in ≠ 0 := by
          intro e e'
          have := ha0 e'
          rw [e'] at hc
          simp at hc
          omega
        by_cases hc1 : c.toNat = 0
        · have := hc0 hc1
          rw [if_neg this]
          omega
        · split <;> omega
    · -- the call failed
      refine ⟨{ l with
                buf := .ref rs (os + c.toNat), len := len', res := some (if s2'.again != 0 then put - len' else 0) },
        fs2, putGz H2 i s2', ?_,
        Or.inr (Or.inr ⟨_, rfl, ?_, by rw [putGz_self hs2]; exact Eff2⟩), by simp [smallMu]⟩
      · unfold smallRest
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hadd,
          hmem, hU, hS, fpos, hX, hbadd, ← hlen', hz', Bool.false_eq_true, ↓reduceIte, hcomp, beq_self_eq_true]
      · split
        · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
          omega
        · simp

/-- **The middle of a trip of the copy loop**: the count already in `in`, and the copy count. -/
theorem smallMid_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {put : UInt64} {Hx : Heap} {v1 : GzState} {l : Zlib.Gzwrite.WriteLoop}
    {B a1 os : Nat} {arr sa : Array UInt8} {rs : BRef}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs (putGz Hx i v1)) (inv : GzInv (putGz Hx i v1) i v1)
    (hw : v1.mode = GZ_WRITE) (hsz : v1.size ≠ 0) (hsk : v1.skip = 0)
    (hin : v1.«in» = .ref (.blk B) 0) (hB : Hx.bytes B = some arr) (hro : Hx.ro B = false)
    (hasz : arr.size = 2 * v1.size.toNat)
    (hni : v1.strm.next_in = .ref (.blk B) a1) (ha : a1 + v1.strm.avail_in.toNat ≤ v1.size.toNat)
    (ha0 : v1.strm.avail_in = 0 → a1 = 0)
    (hl1 : 1 ≤ l.len.toNat) (hlp : l.len.toNat ≤ put.toNat) (hls : l.len.toNat < v1.size.toNat)
    (hpos : v1.x.pos.toInt + l.len.toNat ≤ 9223372036854775807)
    (hbuf : l.buf = .ref rs os) (hsa : Space.get Hx rs = some sa) (hos : os + l.len.toNat ≤ sa.size)
    (hrs : rs ≠ BRef.blk B) (cb : CB (i := i) (putGz Hx i v1) v1 l.buf l.len.toNat)
    (hbl : l.brk = false) (hrl : l.res = none) :
    ∃ z fs' h', smallMid i put l fs (putGz Hx i v1) = .ok ((z, fs'), h') ∧
      SJ (i := i) h0 s0 fs0 put z fs' h' ∧
      smallMu i z h' < 2 * l.len.toNat + (if v1.strm.avail_in = 0 then 0 else 1) + 1 := by
  have hS32 := v1.size.toNat_lt
  have hadd : Ptr.add v1.strm.next_in (v1.strm.avail_in.toNat : Int) (putGz Hx i v1) =
      .ok (.ref (.blk B) (a1 + v1.strm.avail_in.toNat), putGz Hx i v1) := by
    rw [hni]
    exact Ptr.add_nat_ok (R := BRef) (h := putGz Hx i v1) (a := arr) hB (by omega)
  have hdiff : Ptr.diff (Ptr.ref (BRef.blk B) (a1 + v1.strm.avail_in.toNat)) v1.«in» (putGz Hx i v1) =
      .ok (Int64.ofInt (((a1 + v1.strm.avail_in.toNat : Nat) : Int) - ((0 : Nat) : Int)), putGz Hx i v1) := by
    rw [hin]
    exact Ptr.diff_ok (R := BRef) (h := putGz Hx i v1) (a := arr) hB (by omega) (by omega) (by omega)
  obtain ⟨hv, hhvdef⟩ : ∃ hv : UInt32,
      hv = (Int64.ofInt (((a1 + v1.strm.avail_in.toNat : Nat) : Int) - ((0 : Nat) : Int))).toUInt64.toUInt32 :=
    ⟨_, rfl⟩
  have hhv : hv.toNat = a1 + v1.strm.avail_in.toNat := by
    rw [hhvdef, int64_toUInt32_toNat (by omega) (by omega)]
    omega
  have hcopy : (v1.size - hv).toNat = v1.size.toNat - (a1 + v1.strm.avail_in.toNat) := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hhv]; exact ha), hhv]
  have hS : ldS (gzSt i) (putGz Hx i v1) = .ok (v1, putGz Hx i v1) := ldS_put Hx v1
  have hZ : ldZ (strmOf (gzSt i)) (putGz Hx i v1) = .ok (v1.strm, putGz Hx i v1) := ldZ_put Hx v1
  have hlt := l.len.toNat_lt
  by_cases hgt : (v1.size - hv).toUInt64 > l.len
  · have hgt' : l.len.toNat < v1.size.toNat - (a1 + v1.strm.avail_in.toNat) := by
      have := UInt64.lt_iff_toNat_lt.mp hgt
      rw [UInt32.toNat_toUInt64, hcopy] at this
      exact this
    have hc : l.len.toUInt32.toNat = min (v1.size.toNat - (a1 + v1.strm.avail_in.toNat)) l.len.toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨z, fs', h', run, sj, mu⟩ := smallRest_ok err errOwn E inv hw hsz hsk hin hB hro hasz hni ha ha0 hhv hc
      hl1 hlp hls hpos hbuf hsa hos hrs cb hbl hrl
    refine ⟨z, fs', h', ?_, sj, mu⟩
    unfold smallMid
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ, hS,
      hadd, hdiff, ← hhvdef]
    rw [if_pos hgt]
    exact run
  · have hc : (v1.size - hv).toNat = min (v1.size.toNat - (a1 + v1.strm.avail_in.toNat)) l.len.toNat := by
      have : ¬ l.len.toNat < (v1.size - hv).toNat := by
        intro x
        exact hgt (UInt64.lt_iff_toNat_lt.mpr (by rw [UInt32.toNat_toUInt64]; exact x))
      omega
    obtain ⟨z, fs', h', run, sj, mu⟩ := smallRest_ok err errOwn E inv hw hsz hsk hin hB hro hasz hni ha ha0 hhv hc
      hl1 hlp hls hpos hbuf hsa hos hrs cb hbl hrl
    refine ⟨z, fs', h', ?_, sj, mu⟩
    unfold smallMid
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ, hS,
      hadd, hdiff, ← hhvdef]
    rw [if_neg hgt]
    exact run

/-- **A trip of the copy loop.** -/
theorem smallBody_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {put : UInt64} {Hx : Heap} {v : GzState} {l : Zlib.Gzwrite.WriteLoop}
    (S : SmallOn (i := i) h0 s0 fs0 fs put Hx v l) (hbl : l.brk = false) (hrl : l.res = none) :
    ∃ z fs' h', smallBody i put l fs (putGz Hx i v) = .ok ((z, fs'), h') ∧
      SJ (i := i) h0 s0 fs0 put z fs' h' ∧
      smallMu i z h' < 2 * l.len.toNat + (if v.strm.avail_in = 0 then 0 else 1) + 1 := by
  obtain ⟨E, inv, hw, hsz, hsk, hl1, hlp, hls, hpos, cb⟩ := S
  have hfs : FileSystem fs := E.2.1
  have w := inv.writer hw
  obtain ⟨B, arr, hin, hB, hro, hasz⟩ := (w.bufs hsz).1
  have hB' : Hx.bytes B = some arr := hB
  have hro' : Hx.ro B = false := hro
  obtain ⟨rs, os, sa, hbuf, hsa, hos⟩ := cb_ref cb (by omega)
  have hsa' : Space.get Hx rs = some sa := by rw [get_putGz] at hsa; exact hsa
  have hrs : rs ≠ BRef.blk B := by
    rintro rfl
    exact cb.2 B (by rw [hbuf]; rfl) (Or.inr (Or.inr (Or.inr ⟨hsz, Or.inl hin⟩)))
  have hZ : ldZ (strmOf (gzSt i)) (putGz Hx i v) = .ok (v.strm, putGz Hx i v) := ldZ_put Hx v
  by_cases hav : v.strm.avail_in = 0
  · have hav' : (v.strm.avail_in == 0) = true := by simp [hav]
    obtain ⟨v1, hv1⟩ : ∃ v1 : GzState, v1 = { v with strm := { v.strm with next_in := v.«in» } } := ⟨_, rfl⟩
    have hU1 : updZ (strmOf (gzSt i)) (fun z => { z with next_in := v.«in» }) (putGz Hx i v) =
        .ok ((), putGz Hx i v1) := by rw [hv1]; exact updZ_put _ _ _
    obtain ⟨inv1, ho1⟩ := inv_rebuf inv hw v.«in» v.strm.avail_in
      (Or.inr ⟨hsz, 0, by show v.«in» = padv v.«in» 0; rw [hin]; rfl, by
        show 0 + v.strm.avail_in.toNat ≤ v.size.toNat; rw [hav]; simp⟩)
    have P1 := post_put (P := GzInv) (fs := fs) (h := putGz Hx i v) (by simp [putGz]) inv.common.live hfs ho1 rfl rfl
      inv1
    have e1 : recI v v.«in» v.strm.avail_in = v1 := by rw [hv1]; rfl
    rw [putGz_putGz, e1] at P1 inv1 ho1
    have E1 := GetcUngetc.Eff.trans E inv P1 (fun _ => Iff.rfl)
    have hav1 : v1.strm.avail_in = v.strm.avail_in := by rw [hv1]
    obtain ⟨z, fs', h', run, sj, mu⟩ := smallMid_ok (v1 := v1) (a1 := 0) err errOwn E1 inv1
      (by rw [hv1]; exact hw) (by rw [hv1]; exact hsz) (by rw [hv1]; exact hsk) (by rw [hv1]; exact hin) hB' hro'
      (by rw [hv1]; exact hasz) (by rw [hv1]; exact hin) (by rw [hav1, hav]; simp) (fun _ => rfl)
      hl1 hlp (by rw [hv1]; exact hls) (by rw [hv1]; exact hpos) hbuf hsa' hos hrs (cb_rec cb ho1) hbl hrl
    refine ⟨z, fs', h', ?_, sj, by rw [hav1] at mu; exact mu⟩
    unfold smallBody
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ, hav',
      ↓reduceIte, ldS_put, hU1]
    exact run
  · have hav' : (v.strm.avail_in == 0) = false := by simpa using hav
    obtain ⟨a1, ha1, hle⟩ : ∃ a1, v.strm.next_in = padv v.«in» a1 ∧ a1 + v.strm.avail_in.toNat ≤ v.size.toNat := by
      rcases w.input with ⟨-, e⟩ | ⟨-, a1, ha1, hle⟩
      · exact absurd e hav
      · exact ⟨a1, ha1, hle⟩
    obtain ⟨z, fs', h', run, sj, mu⟩ := smallMid_ok (v1 := v) (a1 := a1) err errOwn E inv hw hsz hsk hin hB' hro'
      hasz (by rw [ha1, hin, padv_ref_zero]) hle (fun e => absurd e hav) hl1 hlp hls hpos hbuf hsa' hos hrs cb hbl hrl
    refine ⟨z, fs', h', ?_, sj, mu⟩
    unfold smallBody
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ, hav',
      Bool.false_eq_true, ↓reduceIte]
    exact run

/-- **The copy loop.** -/
theorem small_loop (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {put : UInt64} {Hx : Heap} {v : GzState} {l : Zlib.Gzwrite.WriteLoop}
    (S : SmallOn (i := i) h0 s0 fs0 fs put Hx v l) (hb : l.brk = false) (hr : l.res = none) :
    ∃ y fs' h', gwhile smallCond (smallBody i put) l fs (putGz Hx i v) = .ok ((y, fs'), h') ∧
      ((y.res = none ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h') ∨
        (∃ r, y.res = some r ∧ r.toNat ≤ put.toNat ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h')) := by
  let P : Zlib.Gzwrite.WriteLoop → Fs → Heap → Prop := fun y fs h =>
    (y.res = none ∧ GetcUngetc.Eff i h0 s0 fs0 fs h) ∨
      (∃ r, y.res = some r ∧ r.toNat ≤ put.toNat ∧ GetcUngetc.Eff i h0 s0 fs0 fs h)
  have step : ∀ x fs h, SJ (i := i) h0 s0 fs0 put x fs h → ∃ c y fs1 h1,
      smallCond x fs h = .ok (((c, y), fs1), h1) ∧ (c = false → P y fs1 h1) ∧
      (c = true → ∃ z fs2 h2, smallBody i put y fs1 h1 = .ok ((z, fs2), h2) ∧
        SJ (i := i) h0 s0 fs0 put z fs2 h2 ∧ smallMu i z h2 < smallMu i x h) := by
    rintro x fs h (⟨hb, hr, Hx, v, rfl, S⟩ | ⟨hb, hr, E⟩ | ⟨r, hr, hle, E⟩)
    · refine ⟨true, x, fs, putGz Hx i v, by simp [smallCond, hb, hr, cpure_app], fun e => absurd e (by decide),
        fun _ => ?_⟩
      obtain ⟨z, fs', h', run, sj, mu⟩ := smallBody_ok err errOwn S hb hr
      refine ⟨z, fs', h', run, sj, ?_⟩
      have e : smallMu i x (putGz Hx i v) = 2 * x.len.toNat + (if v.strm.avail_in = 0 then 0 else 1) + 1 := by
        simp only [smallMu, hb, hr, Bool.not_false, Option.isNone_none, Bool.and_self, ↓reduceIte, availBit_put]
      rw [e]; exact mu
    · exact ⟨false, x, fs, h, by simp [smallCond, hb, cpure_app], fun _ => Or.inl ⟨hr, E⟩,
        fun e => absurd e (by decide)⟩
    · exact ⟨false, x, fs, h, by simp [smallCond, hr, cpure_app], fun _ => Or.inr ⟨r, hr, hle, E⟩,
        fun e => absurd e (by decide)⟩
  have hl := S.2.2.2.2.2.2.2.1
  have hs32 := v.size.toNat_lt
  obtain ⟨y, fs', h', run, post⟩ := gwhile_go_spec smallCond (smallBody i put) (SJ (i := i) h0 s0 fs0 put) P
    (fun l _ h => smallMu i l h) step C.fuel l fs (putGz Hx i v) (Or.inl ⟨hb, hr, Hx, v, rfl, S⟩) (by
      show smallMu i l (putGz Hx i v) < C.fuel
      simp only [smallMu, hb, hr, Bool.not_false, Option.isNone_none, Bool.and_self, ↓reduceIte, availBit_put]
      unfold C.fuel
      split <;> omega)
  exact ⟨y, fs', h', run, post⟩

/-! ## The large path: the caller buffer as the input -/

/-- A trip of the direct loop from the input write on. -/
def largeRest (i : Nat) (put : UInt64) (l : Zlib.Gzwrite.WriteLoop) (n : UInt32) : G Zlib.Gzwrite.WriteLoop := do
  updZ (strmOf (gzSt i)) fun z => { z with avail_in := n }
  let ret ← Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH
  let n := n - (← ldZ (strmOf (gzSt i))).avail_in
  let s ← ldS (gzSt i)
  let np ← i64add s.x.pos (u32ToI64 n)
  updX (gzSt i) fun x => { x with pos := np }
  let len := l.len - n.toUInt64
  if ret == -1 then
    let s ← ldS (gzSt i)
    updZ (strmOf (gzSt i)) fun z => { z with avail_in := 0, next_in := s.«in» }
    return { l with len, res := some (if s.again != 0 then put - len else 0) }
  return { l with len }

/-- A trip of the direct loop. -/
def largeBody (i : Nat) (put : UInt64) (l : Zlib.Gzwrite.WriteLoop) : G Zlib.Gzwrite.WriteLoop :=
  let n : UInt32 := 0xFFFFFFFF
  if n.toUInt64 > l.len then largeRest i put l l.len.toUInt32 else largeRest i put l n

/-- The condition of the direct loop. -/
def largeCond (l : Zlib.Gzwrite.WriteLoop) : G (Bool × Zlib.Gzwrite.WriteLoop) :=
  pure (l.res.isNone && l.len != 0, l)

/-- The state of the direct loop: `next_in` in the caller buffer after the consumed bytes, no pending input. -/
def LargeOn (h0 : Heap) (s0 : GzState) (fs0 fs : Fs) (put : UInt64) (buf : BPtr) (B : Nat) (Hx : Heap) (w : GzState)
    (l : Zlib.Gzwrite.WriteLoop) : Prop :=
  GetcUngetc.EffI (fun h j s => GzInvUpToInput h j s ⟨buf, put.toNat⟩) i h0 s0 fs0 fs (putGz Hx i w) ∧
    GzInvUpToInput (putGz Hx i w) i w ⟨buf, put.toNat⟩ ∧ w.strm.avail_in = 0 ∧
    w.strm.next_in = padv buf (put.toNat - l.len.toNat) ∧ l.len.toNat ≤ put.toNat ∧
    w.x.pos.toInt + l.len.toNat ≤ 9223372036854775807 ∧ w.skip = 0 ∧ w.size ≠ 0 ∧ w.«in» = .ref (.blk B) 0

/-- The invariant of the direct loop before a trip. -/
def LJ (h0 : Heap) (s0 : GzState) (fs0 : Fs) (put : UInt64) (buf : BPtr) (B : Nat) (l : Zlib.Gzwrite.WriteLoop)
    (fs : Fs) (h : Heap) : Prop :=
  l.res = none ∧ 1 ≤ l.len.toNat ∧ ∃ Hx w, h = putGz Hx i w ∧ LargeOn (i := i) h0 s0 fs0 fs put buf B Hx w l

/-- The end of the direct loop. -/
def LP (h0 : Heap) (s0 : GzState) (fs0 : Fs) (put : UInt64) (buf : BPtr) (B : Nat) (l : Zlib.Gzwrite.WriteLoop)
    (fs : Fs) (h : Heap) : Prop :=
  (l.res = none ∧ l.len = 0 ∧ ∃ Hx w, h = putGz Hx i w ∧ LargeOn (i := i) h0 s0 fs0 fs put buf B Hx w l) ∨
    (∃ r, l.res = some r ∧ r.toNat ≤ put.toNat ∧ GetcUngetc.Eff i h0 s0 fs0 fs h)

theorem good_upTo (src : Region) : GetcUngetc.Good (fun h j s => GzInvUpToInput h j s src) :=
  good_clear fun _ _ _ u => ⟨u.1, u.2.1⟩

/-- **The rest of a trip of the direct loop.** -/
theorem largeRest_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {put : UInt64} {buf : BPtr} {B : Nat} {Hx : Heap} {w : GzState} {l : Zlib.Gzwrite.WriteLoop} {n : UInt32}
    (L : LargeOn (i := i) h0 s0 fs0 fs put buf B Hx w l) (hrl : l.res = none)
    (hn1 : 1 ≤ n.toNat) (hnl : n.toNat ≤ l.len.toNat) :
    ∃ z fs' h', largeRest i put l n fs (putGz Hx i w) = .ok ((z, fs'), h') ∧
      ((z.res = none ∧ z.len.toNat < l.len.toNat ∧ ∃ Hx' w', h' = putGz Hx' i w' ∧
          LargeOn (i := i) h0 s0 fs0 fs' put buf B Hx' w' z) ∨
        (∃ r, z.res = some r ∧ r.toNat ≤ put.toNat ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h')) := by
  obtain ⟨E, U, hai, hni, hlp, hpos, hsk, hsz, hin⟩ := L
  have hfs : FileSystem fs := E.2.1
  have hs := U.1
  have invC := U.2.1
  have hw := U.2.2.1
  have hhw : w.x.have = 0 := (invC.writer hw).have0
  have hlo : 0 ≤ w.x.pos.toInt := by
    have e : 0 ≤ w.x.pos.toInt + (w.x.have.toNat : Int) := invC.common.pos.2.2
    rw [hhw] at e
    simpa using e
  have own0 : ∀ b, GzOwned (putGz Hx i w) i w b → (putGz Hx i w).live b := ((good_upTo _) _ _ _ U).2
  -- the input write
  obtain ⟨w1, hw1⟩ : ∃ w1 : GzState, w1 = { w with strm := { w.strm with avail_in := n } } := ⟨_, rfl⟩
  have hU : updZ (strmOf (gzSt i)) (fun z => { z with avail_in := n }) (putGz Hx i w) = .ok ((), putGz Hx i w1) := by
    rw [hw1]; exact updZ_put _ _ _
  obtain ⟨U1, ho1⟩ := upTo_recW (src := ⟨buf, put.toNat⟩) hs invC hw w.strm.next_in n w.x.pos w.skip
    ⟨by rw [hsk]; simp, by rw [hsk]; simp; omega, by rw [hhw]; simpa using hlo⟩
    (Or.inr ⟨put.toNat - l.len.toNat, hni, by show put.toNat - l.len.toNat + n.toNat ≤ put.toNat; omega⟩)
    U.2.2.2.2
  have P1 := post_put (P := fun h j s => GzInvUpToInput h j s ⟨buf, put.toNat⟩) (fs := fs) hs own0 hfs ho1 rfl rfl U1
  have e1 : recW w w.strm.next_in n w.x.pos w.skip = w1 := by rw [hw1]; rfl
  rw [putGz_putGz, e1] at P1 U1 ho1
  have E1 := GetcUngetc.EffI.trans (good_upTo _) (good_upTo _) E hs P1 (fun _ => Iff.rfl)
  have hsz1 : w1.size ≠ 0 := by rw [hw1]; exact hsz
  -- the call
  obtain ⟨r, fs2, H2, run, hr, hk2, p2⟩ := comp_run (src := ⟨buf, put.toNat⟩) err errOwn U1 hfs hsz1
  have E3 := GetcUngetc.EffI.trans (good_upTo _) (good_cq _ _ _ _ _) E1 (by simp [putGz]) p2 hk2
  have hfs2 : FileSystem fs2 := E3.2.1
  obtain ⟨-, s2, q2, -⟩ := id p2
  obtain ⟨hs2, invC2, hw2, inp2⟩ := cq_base q2
  have own2 : ∀ b, GzOwned H2 i s2 b → H2.live b := ((good_cq _ _ _ _ _) H2 i s2 q2).2
  obtain ⟨-, sh2in, -, sh2size, -, -, -, sh2skip, sh2pos, -, -, ⟨used, hused, hsum⟩⟩ := q2.2.1
  have hin2 : s2.«in» = .ref (.blk B) 0 := by rw [sh2in, hw1]; exact hin
  have hsz2 : s2.size ≠ 0 := by rw [sh2size, hw1]; exact hsz
  have hsk2 : s2.skip = 0 := by rw [sh2skip, hw1]; exact hsk
  have hpos2 : s2.x.pos = w.x.pos := by rw [sh2pos, hw1]
  have hn1' : w1.strm.avail_in = n := by rw [hw1]
  have hni1 : w1.strm.next_in = w.strm.next_in := by rw [hw1]
  rw [hn1'] at hsum
  rw [hni1] at hused
  have hcomp : Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH fs (putGz Hx i w1) = .ok ((r, fs2), putGz H2 i s2) := by
    rw [putGz_self hs2]; exact run
  -- the consumed count and the position
  obtain ⟨nn, hnn⟩ : ∃ nn : UInt32, nn = n - s2.strm.avail_in := ⟨_, rfl⟩
  have hnnv : nn.toNat = used := by
    rw [hnn, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]
    omega
  obtain ⟨np, hnp⟩ : ∃ np : Int64, np = Int64.ofInt (w.x.pos.toInt + used) := ⟨_, rfl⟩
  have hnpv : np.toInt = w.x.pos.toInt + used := by
    rw [hnp]; exact Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)
  have fpos : i64add s2.x.pos (u32ToI64 nn) (putGz H2 i s2) = .ok (np, putGz H2 i s2) := by
    have := Zlib.Gzlib.Proofs.i64add_run s2.x.pos (u32ToI64 nn)
      (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, hpos2, hnnv]; omega)
      (by rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, hpos2, hnnv]; omega) (putGz H2 i s2)
    rw [Zlib.Gzlib.Proofs.u32ToI64_toInt, hnnv] at this
    rw [this, hnp, hpos2]
  obtain ⟨v3, hv3⟩ : ∃ v3 : GzState, v3 = recW s2 s2.strm.next_in s2.strm.avail_in np s2.skip := ⟨_, rfl⟩
  have hX : updX (gzSt i) (fun x => { x with pos := np }) (putGz H2 i s2) = .ok ((), putGz H2 i v3) := by
    rw [hv3]; exact updX_put _ _ _
  obtain ⟨len', hlen'⟩ : ∃ len' : UInt64, len' = l.len - nn.toUInt64 := ⟨_, rfl⟩
  have hnu : nn.toUInt64.toNat = used := by rw [UInt32.toNat_toUInt64, hnnv]
  have hlenN : len'.toNat = l.len.toNat - used := by
    rw [hlen', UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hnu]; omega), hnu]
  have pos3 : 0 ≤ s2.skip.toInt ∧ np.toInt + s2.skip.toInt ≤ 9223372036854775807 ∧
      0 ≤ np.toInt + s2.x.have.toNat := by
    have hh := (invC2.writer hw2).have0
    change s2.x.have = 0 at hh
    rw [hsk2, hnpv, hh]; simp; omega
  rcases hr with rfl | rfl
  · -- all the offered input was compressed
    have hai0 : s2.strm.avail_in = 0 := q2.2.2.1 rfl rfl
    have hused' : used = n.toNat := by rw [hai0] at hsum; simpa using hsum
    have u : GzInvUpToInput H2 i s2 ⟨buf, put.toNat⟩ := by have := q2.1; rwa [if_pos rfl] at this
    obtain ⟨U3, ho3⟩ := upTo_recW (src := ⟨buf, put.toNat⟩) hs2 invC2 hw2 s2.strm.next_in s2.strm.avail_in np s2.skip
      pos3 (Or.inr ⟨put.toNat - l.len.toNat + n.toNat, by
        show s2.strm.next_in = padv buf (put.toNat - l.len.toNat + n.toNat)
        rw [hused, hni, advance_padv, hused'], by show _ + s2.strm.avail_in.toNat ≤ put.toNat; rw [hai0]; simp; omega⟩)
      u.2.2.2.2
    rw [← hv3] at U3 ho3
    have E4 := GetcUngetc.EffI.trans (good_cq _ _ _ _ _) (good_upTo _) E3 hs2
      (post_put (P := fun h j s => GzInvUpToInput h j s ⟨buf, put.toNat⟩) (fs := fs2) hs2 own2 hfs2 ho3
        (by rw [hv3]; rfl) (by rw [hv3]; rfl) U3) (fun _ => Iff.rfl)
    refine ⟨{ l with len := len' }, fs2, putGz H2 i v3, ?_, Or.inl ⟨hrl, by show len'.toNat < _; omega, H2, v3, rfl,
      E4, U3, by rw [hv3]; exact hai0, ?_, by show len'.toNat ≤ _; omega,
      by rw [hv3]; show np.toInt + len'.toNat ≤ _; omega, by rw [hv3]; exact hsk2, by rw [hv3]; exact hsz2,
      by rw [hv3]; exact hin2⟩⟩
    · unfold largeRest
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hU,
        hcomp, ldZ_put, ← hnn, ldS_put, fpos, hX, ← hlen', int32_zero_ne_neg_one, Bool.false_eq_true, ↓reduceIte]
    · rw [hv3]
      show s2.strm.next_in = padv buf (put.toNat - len'.toNat)
      rw [hused, hni, advance_padv, hused', hlenN]
      congr 1
      omega
  · -- the call failed: back to `in` with no pending input
    obtain ⟨v4, hv4⟩ : ∃ v4 : GzState, v4 = recW s2 s2.«in» 0 np s2.skip := ⟨_, rfl⟩
    have hU4 : updZ (strmOf (gzSt i)) (fun z => { z with avail_in := 0, next_in := v3.«in» }) (putGz H2 i v3) =
        .ok ((), putGz H2 i v4) := by rw [hv4, hv3]; exact updZ_put _ _ _
    obtain ⟨inv4, ho4⟩ := inv_recW hs2 invC2 hw2 s2.«in» 0 np s2.skip pos3
      (Or.inr ⟨hsz2, 0, by show s2.«in» = padv s2.«in» 0; rw [hin2]; rfl, by show 0 + 0 ≤ s2.size.toNat; omega⟩)
    rw [← hv4] at inv4 ho4
    have E4 : GetcUngetc.Eff i h0 s0 fs0 fs2 (putGz H2 i v4) :=
      GetcUngetc.EffI.trans (good_cq _ _ _ _ _) GetcUngetc.good_inv E3 hs2
        (post_put hs2 own2 hfs2 ho4 (by rw [hv4]; rfl) (by rw [hv4]; rfl) inv4) (fun _ => Iff.rfl)
    refine ⟨{ l with len := len', res := some (if v3.again != 0 then put - len' else 0) }, fs2, putGz H2 i v4, ?_,
      Or.inr ⟨_, rfl, ?_, E4⟩⟩
    · unfold largeRest
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hU,
        hcomp, ldZ_put, ← hnn, ldS_put, fpos, hX, ← hlen', beq_self_eq_true, ↓reduceIte, hU4]
    · split
      · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
        omega
      · simp

/-- **A trip of the direct loop**: at most `2^32 - 1` bytes are offered. -/
theorem largeBody_ok (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {put : UInt64} {buf : BPtr} {B : Nat} {Hx : Heap} {w : GzState} {l : Zlib.Gzwrite.WriteLoop}
    (L : LargeOn (i := i) h0 s0 fs0 fs put buf B Hx w l) (hrl : l.res = none) (hl1 : 1 ≤ l.len.toNat) :
    ∃ z fs' h', largeBody i put l fs (putGz Hx i w) = .ok ((z, fs'), h') ∧
      ((z.res = none ∧ z.len.toNat < l.len.toNat ∧ ∃ Hx' w', h' = putGz Hx' i w' ∧
          LargeOn (i := i) h0 s0 fs0 fs' put buf B Hx' w' z) ∨
        (∃ r, z.res = some r ∧ r.toNat ≤ put.toNat ∧ GetcUngetc.Eff i h0 s0 fs0 fs' h')) := by
  by_cases hgt : (0xFFFFFFFF : UInt32).toUInt64 > l.len
  · have hgt' : l.len.toNat < 4294967295 := by
      have := UInt64.lt_iff_toNat_lt.mp hgt
      simpa using this
    have hn : l.len.toUInt32.toNat = l.len.toNat := by
      rw [UInt64.toNat_toUInt32]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨z, fs', h', run, res⟩ := largeRest_ok (n := l.len.toUInt32) err errOwn L hrl (by omega) (by omega)
    refine ⟨z, fs', h', ?_, res⟩
    show (if (0xFFFFFFFF : UInt32).toUInt64 > l.len then largeRest i put l l.len.toUInt32
      else largeRest i put l 0xFFFFFFFF) fs (putGz Hx i w) = _
    rw [if_pos hgt]; exact run
  · have hgt' : 4294967295 ≤ l.len.toNat := by
      have : ¬ (0xFFFFFFFF : UInt32).toUInt64.toNat > l.len.toNat := fun x => hgt (UInt64.lt_iff_toNat_lt.mpr x)
      simp at this
      omega
    obtain ⟨z, fs', h', run, res⟩ := largeRest_ok (n := 0xFFFFFFFF) err errOwn L hrl (by decide) (by
      show (4294967295 : Nat) ≤ _; omega)
    refine ⟨z, fs', h', ?_, res⟩
    show (if (0xFFFFFFFF : UInt32).toUInt64 > l.len then largeRest i put l l.len.toUInt32
      else largeRest i put l 0xFFFFFFFF) fs (putGz Hx i w) = _
    rw [if_neg hgt]; exact run

/-- **The direct loop.** -/
theorem large_loop (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {put : UInt64} {buf : BPtr} {B : Nat} {l : Zlib.Gzwrite.WriteLoop} {h : Heap}
    (J : LJ (i := i) h0 s0 fs0 put buf B l fs h) :
    ∃ y fs' h', gdoWhile (largeBody i put) largeCond l fs h = .ok ((y, fs'), h') ∧
      LP (i := i) h0 s0 fs0 put buf B y fs' h' := by
  have step : ∀ x fs h, LJ (i := i) h0 s0 fs0 put buf B x fs h → ∃ y fs1 h1,
      largeBody i put x fs h = .ok ((y, fs1), h1) ∧ ∃ c z fs2 h2, largeCond y fs1 h1 = .ok (((c, z), fs2), h2) ∧
        (c = true → LJ (i := i) h0 s0 fs0 put buf B z fs2 h2 ∧ z.len.toNat < x.len.toNat) ∧
        (c = false → LP (i := i) h0 s0 fs0 put buf B z fs2 h2) := by
    rintro x fs h ⟨hr, hl1, Hx, w, rfl, L⟩
    obtain ⟨y, fs1, h1, run, res⟩ := largeBody_ok err errOwn L hr hl1
    refine ⟨y, fs1, h1, run, ?_⟩
    rcases res with ⟨hy, hlt, Hx', w', rfl, L'⟩ | ⟨r, hy, hle, E⟩
    · by_cases hz : y.len = 0
      · exact ⟨false, y, fs1, putGz Hx' i w', by simp [largeCond, hy, hz, cpure_app], fun e => absurd e (by decide),
          fun _ => Or.inl ⟨hy, hz, Hx', w', rfl, L'⟩⟩
      · have hz' : 1 ≤ y.len.toNat := by
          have : y.len.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
          omega
        exact ⟨true, y, fs1, putGz Hx' i w', by simp [largeCond, hy, hz, cpure_app],
          fun _ => ⟨⟨hy, hz', Hx', w', rfl, L'⟩, hlt⟩, fun e => absurd e (by decide)⟩
    · exact ⟨false, y, fs1, h1, by simp [largeCond, hy, cpure_app], fun e => absurd e (by decide),
        fun _ => Or.inr ⟨r, hy, hle, E⟩⟩
  obtain ⟨y, fs', h', run, post⟩ := gdoWhile_go_spec' (largeBody i put) largeCond (LJ (i := i) h0 s0 fs0 put buf B)
    (LP (i := i) h0 s0 fs0 put buf B) (fun l _ _ => l.len.toNat) step C.fuel l fs h J (by
      show l.len.toNat < C.fuel
      unfold C.fuel
      exact l.len.toNat_lt)
  exact ⟨y, fs', h', run, post⟩

/-! ## The stages of `gz_write` -/

/-- The small path after the position check. -/
def smallTail (i : Nat) (buf : BPtr) (len : UInt64) : G UInt64 := do
  let l ← gwhile smallCond (smallBody i len) { len, buf, res := none, brk := false }
  if let some r := l.res then return r
  return len

/-- The large path after the pending input was compressed. -/
def largeTail (i : Nat) (buf : BPtr) (len : UInt64) : G UInt64 := do
  updZ (strmOf (gzSt i)) fun z => { z with next_in := buf }
  let l ← gdoWhile (largeBody i len) largeCond { len, buf, res := none, brk := false }
  if let some r := l.res then return r
  let s ← ldS (gzSt i)
  updZ (strmOf (gzSt i)) fun z => { z with next_in := s.«in» }
  return len

/-- After the position check. -/
def writeT3 (i : Nat) (buf : BPtr) (len : UInt64) : G UInt64 := do
  if len < (← ldS (gzSt i)).size.toUInt64 then
    smallTail i buf len
  else
    if (← ldZ (strmOf (gzSt i))).avail_in != 0 then
      if (← Zlib.Gzwrite.gz_comp (gzSt i) Z_NO_FLUSH) == -1 then return 0
    largeTail i buf len

/-- From the position check on. -/
def writeT2 (i : Nat) (buf : BPtr) (len : UInt64) : G UInt64 := do
  if (← i64sub GZ_OFF_MAX (← ldS (gzSt i)).x.pos).toUInt64 < len then
    Zlib.Gzlib.gz_error (gzSt i) Z_DATA_ERROR (← Zlib.GzFs.strLit "position overflow")
    return 0
  writeT3 i buf len

/-- From the pending skip on. -/
def writeT1 (i : Nat) (buf : BPtr) (len : UInt64) : G UInt64 := do
  if (← ldS (gzSt i)).skip != 0 then
    if (← Zlib.Gzwrite.gz_zero (gzSt i)) == -1 then return 0
  writeT2 i buf len

theorem gz_write_source (i : Nat) (buf : BPtr) (len : UInt64) :
    Zlib.Gzwrite.gz_write (gzSt i) buf len = (do
      if len == 0 then return 0
      if (← ldS (gzSt i)).size == 0 then
        if (← Zlib.Gzwrite.gz_init (gzSt i)) == -1 then return 0
      writeT1 i buf len) := rfl

/-- The mode of the record a `GzPost` step leaves. -/
theorem post_mode {P : Heap → Nat → GzState → Prop} {h h' : Heap} {s t : GzState} {fs : Fs}
    (post : GzPost h i s [] fs h' P) (rec : ∀ s', P h' i s' → h'.gzstates i = some s')
    (ht : h'.gzstates i = some t) : t.mode = s.mode := by
  obtain ⟨-, s', hp, hm, -⟩ := post
  have e := (rec s' hp).symm.trans ht
  cases e
  exact hm

theorem large_tail (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {buf : BPtr} {len : UInt64} {H : Heap} {v : GzState} {B : Nat}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    (hsk : v.skip = 0) (hav : v.strm.avail_in = 0) (hin : v.«in» = .ref (.blk B) 0) (hl1 : 1 ≤ len.toNat)
    (hpos : v.x.pos.toInt + len.toNat ≤ 9223372036854775807) (cb : CB (i := i) H v buf len.toNat) :
    ∃ r fs' h', largeTail i buf len fs H = .ok ((r, fs'), h') ∧ WP (i := i) h0 s0 fs0 len r fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hv := inv.common.record
  obtain ⟨w0, hw0⟩ : ∃ w0 : GzState, w0 = { v with strm := { v.strm with next_in := buf } } := ⟨_, rfl⟩
  have hU0 : updZ (strmOf (gzSt i)) (fun z => { z with next_in := buf }) H = .ok ((), putGz H i w0) := by
    rw [hw0]; exact Zlib.Gzlib.Proofs.updZ_run hv _
  obtain ⟨U0, ho0⟩ := upTo_recW (src := ⟨buf, len.toNat⟩) hv (clear_of_inv inv hw) hw buf v.strm.avail_in v.x.pos
    v.skip inv.common.pos
    (Or.inr ⟨0, (padv_zero_self buf).symm, by show 0 + v.strm.avail_in.toNat ≤ len.toNat; rw [hav]; simp⟩)
    (Or.inr cb)
  have e0 : recW v buf v.strm.avail_in v.x.pos v.skip = w0 := by rw [hw0]; rfl
  rw [e0] at U0 ho0
  have E0 := GetcUngetc.EffI.trans GetcUngetc.good_inv (good_upTo _) E hv
    (post_put (P := fun h j s => GzInvUpToInput h j s ⟨buf, len.toNat⟩) (fs := fs) hv inv.common.live hfs ho0
      (by rw [hw0]) (by rw [hw0]) U0) (fun _ => Iff.rfl)
  have J : LJ (i := i) h0 s0 fs0 len buf B { len, buf, res := none, brk := false } fs (putGz H i w0) :=
    ⟨rfl, hl1, H, w0, rfl, E0, U0, by rw [hw0]; exact hav,
      by rw [hw0]; show buf = padv buf (len.toNat - len.toNat); rw [Nat.sub_self, padv_zero_self],
      Nat.le_refl _, by rw [hw0]; exact hpos, by rw [hw0]; exact hsk, by rw [hw0]; exact hsz,
      by rw [hw0]; exact hin⟩
  obtain ⟨y, fs', h', run, post⟩ := large_loop err errOwn J
  rcases post with ⟨hy, -, Hx, w, rfl, L⟩ | ⟨r, hy, hle, E'⟩
  · obtain ⟨EL, U, hai, -, -, -, -, hszw, hinw⟩ := L
    have hs := U.1
    have hww := U.2.2.1
    obtain ⟨inv5, ho5⟩ := inv_recW hs U.2.1 hww w.«in» w.strm.avail_in w.x.pos w.skip
      (by have := U.2.1.common.pos; exact this)
      (Or.inr ⟨hszw, 0, by show w.«in» = padv w.«in» 0; rw [hinw]; rfl, by
        show 0 + w.strm.avail_in.toNat ≤ w.size.toNat; rw [hai]; simp⟩)
    have P5 := post_put (P := GzInv) (fs := fs') hs ((good_upTo _) _ _ _ U).2 EL.2.1 ho5 rfl rfl inv5
    rw [putGz_putGz] at P5
    have E5 := GetcUngetc.EffI.trans (good_upTo _) GetcUngetc.good_inv EL hs P5 (fun _ => Iff.rfl)
    refine ⟨len, fs', putGz Hx i (recW w w.«in» w.strm.avail_in w.x.pos w.skip), ?_, Nat.le_refl _, E5⟩
    unfold largeTail
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hU0, run,
      hy, ldS_put, updZ_put, putGz_putGz]
    rfl
  · refine ⟨r, fs', h', ?_, hle, E'⟩
    unfold largeTail
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hU0, run,
      hy]

theorem write_t3 (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {buf : BPtr} {len : UInt64} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    (hsk : v.skip = 0) (hl1 : 1 ≤ len.toNat)
    (hpos : v.x.pos.toInt + len.toNat ≤ 9223372036854775807) (cb : CB (i := i) H v buf len.toNat) :
    ∃ r fs' h', writeT3 i buf len fs H = .ok ((r, fs'), h') ∧ WP (i := i) h0 s0 fs0 len r fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hv := inv.common.record
  have w := inv.writer hw
  obtain ⟨B, arr, hin, -, -, -⟩ := (w.bufs hsz).1
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hv
  have hZ : ldZ (strmOf (gzSt i)) H = .ok (v.strm, H) := Zlib.Gzlib.Proofs.ldZ_run hv
  by_cases hsm : len < v.size.toUInt64
  · have hsm' : len.toNat < v.size.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hsm
      rwa [UInt32.toNat_toUInt64] at this
    have S : SmallOn (i := i) h0 s0 fs0 fs len H v { len, buf, res := none, brk := false } := by
      unfold SmallOn
      rw [putGz_self hv]
      exact ⟨E, inv, hw, hsz, hsk, hl1, Nat.le_refl _, hsm', hpos, cb⟩
    obtain ⟨y, fs', h', run, post⟩ := small_loop err errOwn S rfl rfl
    rw [putGz_self hv] at run
    rcases post with ⟨hy, E'⟩ | ⟨r, hy, hle, E'⟩
    · refine ⟨len, fs', h', ?_, Nat.le_refl _, E'⟩
      unfold writeT3 smallTail
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsm,
        decide_true, ↓reduceIte, run, hy]
    · refine ⟨r, fs', h', ?_, hle, E'⟩
      unfold writeT3 smallTail
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsm,
        decide_true, ↓reduceIte, run, hy]
  · by_cases hav : v.strm.avail_in = 0
    · have hav' : (v.strm.avail_in != 0) = false := by simp [hav]
      obtain ⟨r, fs', h', run, post⟩ := large_tail err errOwn E inv hw hsz hsk hav hin hl1 hpos cb
      refine ⟨r, fs', h', ?_, post⟩
      unfold writeT3
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsm,
        decide_false, Bool.false_eq_true, ↓reduceIte, hZ, hav', run]
    · have hav' : (v.strm.avail_in != 0) = true := by simpa using hav
      obtain ⟨r, fs2, H2, run, hr, hk2, p2⟩ := comp_run (src := ⟨v.«in», v.size.toNat⟩) err errOwn
        (upTo_of_inv inv hw hsz) hfs hsz
      have E3 := GetcUngetc.EffI.trans GetcUngetc.good_inv (good_cq _ _ _ _ _) E hv p2 hk2
      have Eff2 : GetcUngetc.Eff i h0 s0 fs0 fs2 H2 :=
        ⟨E3.1, GetcUngetc.GzPost.mono E3.2 fun s' q => inv_of_cq hsz q⟩
      rcases hr with rfl | rfl
      · obtain ⟨-, s2', q2', -⟩ := id p2
        have hbor : H2.libcErrorBorrow = H.libcErrorBorrow := q2'.2.2.2 rfl
        obtain ⟨s2, q2, cb2⟩ := cb_of_post cb p2 hbor
        have inv2 := inv_of_cq hsz q2
        obtain ⟨-, sh2in, -, sh2size, sh2mode, -, -, sh2skip, sh2pos, -, -, -⟩ := q2.2.1
        obtain ⟨r, fs', h', run2, post⟩ := large_tail err errOwn Eff2 inv2 (by rw [sh2mode]; exact hw)
          (by rw [sh2size]; exact hsz) (by rw [sh2skip]; exact hsk) (q2.2.2.1 rfl rfl) (by rw [sh2in]; exact hin) hl1
          (by rw [sh2pos]; exact hpos) cb2
        refine ⟨r, fs', h', ?_, post⟩
        unfold writeT3
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hsm, decide_false, Bool.false_eq_true, ↓reduceIte, hZ, hav', run, int32_zero_ne_neg_one, run2]
      · refine ⟨0, fs2, H2, ?_, by simp, Eff2⟩
        unfold writeT3
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
          hsm, decide_false, Bool.false_eq_true, ↓reduceIte, hZ, hav', run, beq_self_eq_true]

theorem write_t2 (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {buf : BPtr} {len : UInt64} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    (hsk : v.skip = 0) (hl1 : 1 ≤ len.toNat) (cb : CB (i := i) H v buf len.toNat) :
    ∃ r fs' h', writeT2 i buf len fs H = .ok ((r, fs'), h') ∧ WP (i := i) h0 s0 fs0 len r fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hv := inv.common.record
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hv
  obtain ⟨hp, hpk, hlo⟩ := inv.common.pos
  have hhave : v.x.have = 0 := (inv.writer hw).have0
  have hlo' : 0 ≤ v.x.pos.toInt := by rw [hhave] at hlo; simpa using hlo
  have hpk' : v.x.pos.toInt ≤ 9223372036854775807 := by rw [hsk] at hpk; simpa using hpk
  have hmax : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide
  have hsub : i64sub GZ_OFF_MAX v.x.pos H = .ok (Int64.ofInt (9223372036854775807 - v.x.pos.toInt), H) := by
    have := Zlib.Gzlib.Proofs.i64sub_run GZ_OFF_MAX v.x.pos (by rw [hmax]; omega) (by rw [hmax]; omega) H
    rw [hmax] at this
    exact this
  have hd : (Int64.ofInt (9223372036854775807 - v.x.pos.toInt)).toUInt64.toNat =
      (9223372036854775807 - v.x.pos.toInt).toNat := int64_toUInt64_toNat (by omega) (by omega)
  by_cases hc : (Int64.ofInt (9223372036854775807 - v.x.pos.toInt)).toUInt64 < len
  · -- the refusal of patch 0004
    obtain ⟨k, hk⟩ := strIndex_of_mem (s := "position overflow") (by decide +kernel)
    obtain ⟨t, ct⟩ := posov_cstring H hk
    have hmsg : (Ptr.ref (BRef.str k) 0 : BPtr) = .null ∨ ∃ t, CString H (.ref (.str k) 0) t ∧
        ∀ b, ByteRoot (.ref (.str k) 0) b → ¬ GzOwned H i v b :=
      Or.inr ⟨t, ct, fun b hb => by simp [ByteRoot] at hb⟩
    obtain ⟨after, s', run, inv', e', -, fr, lc⟩ := err inv Z_DATA_ERROR (.ref (.str k) 0) hmsg
    have own := errOwn H i v Z_DATA_ERROR (.ref (.str k) 0) after inv hmsg run s' inv'.common.record
    have P := GetcUngetc.post_of_gz_error (fs := fs) inv inv' e' fr lc own hfs
    have run' : Zlib.Gzlib.gz_error (gzSt i) Z_DATA_ERROR (.ref (.str k) 0) H = .ok ((), after) := run
    refine ⟨0, fs, after, ?_, by simp, GetcUngetc.Eff.trans E inv P (fun _ => Iff.rfl)⟩
    unfold writeT2
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsub,
      hc, ↓reduceIte, Zlib.GzFs.strLit, strLitRef_of_index hk, run']
  · have hpos : v.x.pos.toInt + len.toNat ≤ 9223372036854775807 := by
      have : ¬ (Int64.ofInt (9223372036854775807 - v.x.pos.toInt)).toUInt64.toNat < len.toNat :=
        fun x => hc (UInt64.lt_iff_toNat_lt.mpr x)
      rw [hd] at this
      omega
    obtain ⟨r, fs', h', run, post⟩ := write_t3 err errOwn E inv hw hsz hsk hl1 hpos cb
    refine ⟨r, fs', h', ?_, post⟩
    unfold writeT2
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsub,
      hc, ↓reduceIte, run]

theorem write_t1 (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 : Heap} {s0 : GzState} {fs0 fs : Fs}
    {buf : BPtr} {len : UInt64} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    (hl1 : 1 ≤ len.toNat) (cb : CB (i := i) H v buf len.toNat) :
    ∃ r fs' h', writeT1 i buf len fs H = .ok ((r, fs'), h') ∧ WP (i := i) h0 s0 fs0 len r fs' h' := by
  have hfs : FileSystem fs := E.2.1
  have hv := inv.common.record
  have hS : ldS (gzSt i) H = .ok (v, H) := Zlib.Gzlib.Proofs.ldS_run hv
  by_cases hsk : v.skip = 0
  · have hsk' : (v.skip != 0) = false := by simp [hsk]
    obtain ⟨r, fs', h', run, post⟩ := write_t2 err errOwn E inv hw hsz hsk hl1 cb
    refine ⟨r, fs', h', ?_, post⟩
    unfold writeT1
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS, hsk',
      Bool.false_eq_true, ↓reduceIte, run]
  · have hsk' : (v.skip != 0) = true := by simpa using hsk
    have R := gz_zero_safe_shape err errOwn i H fs v inv hfs hw hsz
    obtain ⟨r, fs1, H1, run⟩ := R.2.1 trivial
    obtain ⟨hr, hk, p⟩ := R.2.2 r fs1 H1 run
    have E1 : GetcUngetc.Eff i h0 s0 fs0 fs1 H1 :=
      GetcUngetc.Eff.trans E inv (GetcUngetc.GzPost.mono p fun _ q => q.1) hk
    rcases hr with rfl | rfl
    · obtain ⟨-, s1', q1', -⟩ := id p
      have hbor : H1.libcErrorBorrow = H.libcErrorBorrow := (q1'.2.2 rfl).2
      obtain ⟨s1, ⟨inv1, hsz1, hq1⟩, cb1⟩ := cb_of_post cb p hbor
      have hw1 : s1.mode = GZ_WRITE :=
        (post_mode p (fun s' q => q.1.common.record) inv1.common.record).trans hw
      obtain ⟨r2, fs', h', run2, post⟩ := write_t2 err errOwn E1 inv1 hw1 (by rw [hsz1]; exact hsz) (hq1 rfl).1 hl1 cb1
      refine ⟨r2, fs', h', ?_, post⟩
      unfold writeT1
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hsk', ↓reduceIte, run, int32_zero_ne_neg_one, Bool.false_eq_true, run2]
    · refine ⟨0, fs1, H1, ?_, by simp, E1⟩
      unfold writeT1
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hS,
        hsk', ↓reduceIte, run, beq_self_eq_true]

/-- **`gz_write` is safe**, given the facts of `gz_error`: the statement of `gz_write_safe` of
`gz.skeleton-write`. -/
theorem gz_write_safe_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (i : Nat) (buf : BPtr) (len : UInt64) (h : Heap)
    (fs : Fs) (s : GzState) (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE)
    (hbuf : len = 0 ∨ GzRange h i s buf len.toNat false) :
    RunSafe (Zlib.Gzwrite.gz_write (gzSt i) buf len) fs h True fun r fs' after =>
      r.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv := by
  suffices H : Ok (Zlib.Gzwrite.gz_write (gzSt i) buf len) fs h
      (fun r fs' after => r.toNat ≤ len.toNat ∧ GetcUngetc.Eff i h s fs fs' after) by
    exact runSafe_of_ok (H.mono fun r fs' after ⟨hr, k, p⟩ => ⟨hr, k, p⟩)
  have hs := inv.common.record
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run hs
  have E0 : GetcUngetc.Eff i h s fs fs h := GetcUngetc.Eff.refl inv hfs
  rw [gz_write_source]
  by_cases hl0 : len = 0
  · subst hl0
    refine ⟨0, fs, h, ?_, by simp, E0⟩
    simp only [beq_self_eq_true, ↓reduceIte, cpure_app]
  have hl0' : (len == 0) = false := by simpa using hl0
  have hl1 : 1 ≤ len.toNat := by
    have : len.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
    omega
  have cb : CB (i := i) h s buf len.toNat := by
    rcases hbuf with e | e
    · exact absurd e hl0
    · rcases e with e | ⟨hb, -, no⟩
      · omega
      · exact ⟨hb, no⟩
  by_cases hsz : s.size = 0
  · obtain ⟨v, after, run, hv, post, hsucc⟩ := Zlib.Gzwrite.SafeInit.gz_init_run err errOwn i h fs s inv hfs hm hsz
    have hz : (s.size == 0) = true := by simp [hsz]
    rcases hv with rfl | rfl
    · obtain ⟨⟨s1', hs1', hsz1⟩, hbor⟩ := hsucc rfl
      obtain ⟨s1, inv1, cb1⟩ := cb_of_post cb post hbor
      have e1 : s1 = s1' := Option.some.inj (inv1.common.record.symm.trans hs1')
      subst e1
      have hw1 : s1.mode = GZ_WRITE := (post_mode post (fun s' q => q.common.record) inv1.common.record).trans hm
      obtain ⟨r, fs', h', run2, wp⟩ := write_t1 err errOwn ⟨fun _ => Iff.rfl, post⟩ inv1 hw1 hsz1 hl1 cb1
      refine ⟨r, fs', h', ?_, wp⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hl0',
        Bool.false_eq_true, ↓reduceIte, hS, hz, run, int32_zero_ne_neg_one, run2]
    · refine ⟨0, fs, after, ?_, by simp, ⟨fun _ => Iff.rfl, post⟩⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hl0',
        Bool.false_eq_true, ↓reduceIte, hS, hz, run, beq_self_eq_true]
  · have hz : (s.size == 0) = false := by simpa using hsz
    obtain ⟨r, fs', h', run, wp⟩ := write_t1 err errOwn E0 inv hm hsz hl1 cb
    refine ⟨r, fs', h', ?_, wp⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hl0',
      Bool.false_eq_true, ↓reduceIte, hS, hz, run]

end write

end ZlibF.Spec.Public.GzSkeleton
