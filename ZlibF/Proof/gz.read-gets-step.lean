import ZlibF.Proof.«gz.read-leaf-common»
import ZlibF.Proof.«gzread.c.skip-gets»
import ZlibF.Proof.«gz.read-fetch»
import ZlibF.Proof.«gz.read-assembly»

/-!
# gz read side: `gzgets` is safe

`gzgets(file, buf, len)` reads at most `len - 1` bytes into `buf`, up to and including a newline, and ends the string
with a NUL. The proof follows the translation:

1. the refusals (`buf == NULL`, `len < 1`, a writer, a serious error with nothing buffered);
2. `gz_error(state, Z_OK, NULL)` after a stall, then `gz_skip` for a pending skip;
3. the loop: `gz_fetch` when nothing is buffered, then the bounded `memchr`, the copy into the caller's buffer
   and the advance of `x.have`, `x.next`, `x.pos`. The loop variable `left` drops on each trip that continues;
4. the final NUL at `buf[len - 1]` at most.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Heap facts -/

theorem get_setS_ref (H : Heap) (j : Nat) (t : GzState) (r : BRef) :
    Space.get (setS H j t) r = Space.get H r := by
  cases r <;> rfl

theorem ro_setS_ref (H : Heap) (j : Nat) (t : GzState) (r : BRef) :
    Space.ro (setS H j t) r = Space.ro H r := by
  cases r <;> rfl

theorem get_put_blk_ne (H : Heap) (r : BRef) (arr : Array UInt8) {b : Nat} (hne : r ≠ BRef.blk b) :
    Space.get (Space.put H r arr) (BRef.blk b) = Space.get H (BRef.blk b) := by
  cases r with
  | blk c =>
    have hcb : b ≠ c := fun e => hne (by rw [e])
    show upd H.bytes c (some arr) b = H.bytes b
    exact upd_ne _ _ _ _ hcb
  | dstate_depth c =>
    show Space.get (match H.dstates c with
      | some s => { H with dstates := upd H.dstates c (some { s with depth := arr }) } | none => H) (BRef.blk b) = _
    cases H.dstates c <;> rfl
  | _ => rfl

theorem byteRoot_off (r : BRef) (o1 o2 b : Nat) : ByteRoot (.ref r o1) b ↔ ByteRoot (.ref r o2) b := by
  cases r <;> exact Iff.rfl

/-! ## The copy step -/

/-- The record after a copy of `n` buffered bytes. -/
def getsRec (s : GzState) (b off n : Nat) : GzState :=
  { s with x := { «have» := s.x.have - UInt32.ofNat n, next := .ref (BRef.blk b) (off + n),
                  pos := Int64.ofInt (s.x.pos.toInt + n) } }

private theorem read_ne_write'' : GZ_READ ≠ GZ_WRITE := by decide

/-- **The copy step of `gzgets`**: `memcpy(buf, x.next, n)` into the caller's buffer, then `x.have -= n`,
`x.next += n`, `x.pos += n`, `left -= n`, `buf += n`, on a reader in `GzInv` with no pending skip. -/
theorem getsCopy_run {E : GetsEnv} (C : GetsCaller E) {fs : Fs} {h : Heap} {s : GzState}
    {l : Zlib.Gzread.GetsLoop} {n : UInt32} {eol : BPtr} {fin : Prop}
    (ok : E.Ok fs h) (inv : GzInv h E.i s) (hm : s.mode = GZ_READ)
    (hn1 : 1 ≤ n.toNat) (hnh : n.toNat ≤ s.x.have.toNat) (hnl : n.toNat ≤ l.left.toNat)
    (hl0 : l.left.toNat ≤ E.left0) (hbuf : l.buf = .ref E.r (E.off + (E.left0 - l.left.toNat))) :
    RunSafe (getsCopy (gzSt E.i) l s n eol) fs h fin fun l' fs' h' =>
      l'.brk = l.brk ∧ l'.eol = eol ∧ l'.left.toNat = l.left.toNat - n.toNat ∧
      l'.buf = .ref E.r (E.off + (E.left0 - l'.left.toNat)) ∧ E.Ok fs' h' ∧ fs' = fs := by
  obtain ⟨acc, hsk⟩ := ok
  have c := inv.common
  have r := inv.reader hm
  have hs := c.record
  have hsk0 : s.skip = 0 := hsk s hs
  have hh : s.x.have ≠ 0 := by
    intro e; rw [e] at hnh; simp at hnh; omega
  obtain ⟨b, off, a, hx, -, hob, -, hba, hle⟩ := c.next hh
  obtain ⟨ac, hac, hacs, hro, hun⟩ := C.now acc
  have hfit := C.fit
  have hph := r.posHave
  have hlo := c.pos.2.2
  have hpl := s.x.pos.toInt_lt
  have hhl := s.x.have.toNat_lt
  have hnl32 := n.toNat_lt
  have hne : E.r ≠ BRef.blk b := by
    intro e
    exact hun s hs b (by rw [e]; rfl) hob
  have hba' : Space.get h (BRef.blk b) = some a := hba
  have hcp : memcpyB l.buf s.x.next n.toNat h =
      .ok ((), Space.put h E.r (copyRange ac a (E.off + (E.left0 - l.left.toNat)) off n.toNat)) := by
    rw [hbuf, hx]
    exact Ptr.memcpy_ok hac hba' hro (by omega) (by omega) (Or.inl hne)
  -- the caller's buffer after the copy
  have hcov : ∀ j, j < ac.size → ¬ Zlib.Inflate.Proofs.RegionCovers E.R E.r j →
      (copyRange ac a (E.off + (E.left0 - l.left.toNat)) off n.toNat)[j]? = ac[j]? := by
    intro j _ hnc
    apply Zlib.Inflate.Proofs.copyRange_getElem?_outside
    by_cases h1 : E.off ≤ j
    · by_cases h2 : j ≤ E.off + E.left0
      · exact absurd (C.covers h1 h2) hnc
      · right; omega
    · left; omega
  obtain ⟨acc1, inv1⟩ := acc.region_put (off := E.off) inv hac hro (size_copyRange _ _ _ _ _)
    (fun b' hb' => hun s hs b' hb') C.root hcov C.views
  have hs1 := inv1.common.record
  have hba1 : Space.get (Space.put h E.r (copyRange ac a (E.off + (E.left0 - l.left.toNat)) off n.toNat))
      (BRef.blk b) = some a := by
    rw [get_put_blk_ne _ _ _ hne]; exact hba'
  generalize Space.put h E.r (copyRange ac a (E.off + (E.left0 - l.left.toNat)) off n.toNat) = h1 at hcp acc1 inv1 hs1 hba1
  have hnv : (s.x.have - n).toNat = s.x.have.toNat - n.toNat := by
    rw [UInt32.toNat_sub_of_le]
    exact UInt32.le_iff_toNat_le.mpr hnh
  have hpos := i64_toInt_ofInt (n := s.x.pos.toInt + n.toNat) (by omega) (by omega)
  unfold getsCopy
  refine RunSafe.bind_lift hcp ?_
  refine RunSafe.bind_lift (updX_run hs1 _) ?_
  refine RunSafe.bind_lift (ldS_run (setS_gz_same _ _ _)) ?_
  dsimp only
  have hadd : Ptr.add s.x.next (n.toNat : Int) (setS h1 E.i { s with x := { s.x with «have» := s.x.have - n } }) =
      .ok (.ref (BRef.blk b) (off + n.toNat), setS h1 E.i { s with x := { s.x with «have» := s.x.have - n } }) := by
    rw [hx]
    exact Ptr.add_nat_ok (by rw [get_setS_ref]; exact hba1) (by omega)
  refine RunSafe.bind_lift hadd ?_
  refine RunSafe.bind_lift (updX_run (setS_gz_same _ _ _) _) ?_
  refine RunSafe.bind_lift (ldS_run (setS_gz_same _ _ _)) ?_
  dsimp only
  have hinc : ∀ H : Heap, i64add s.x.pos (u32ToI64 n) H = .ok (Int64.ofInt (s.x.pos.toInt + n.toNat), H) := by
    intro H
    have := i64add_run s.x.pos (u32ToI64 n) (by rw [u32ToI64_toInt]; omega) (by rw [u32ToI64_toInt]; omega) H
    rw [u32ToI64_toInt] at this
    exact this
  refine RunSafe.bind_lift (hinc _) ?_
  refine RunSafe.bind_lift (updX_run (setS_gz_same _ _ _) _) ?_
  rw [setS_setS, setS_setS]
  -- the record after the copy
  have inv2 := GzInv.put_consume (h := h1) (i := E.i) inv1 (s' := getsRec s b off n.toNat)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ n.toNat
    (by rw [hx]; rfl)
    (by show n.toNat + (s.x.have - UInt32.ofNat n.toNat).toNat ≤ _; rw [UInt32.ofNat_toNat, hnv]; omega)
    ⟨c.want.1, c.want.2, Or.inr rfl⟩
    ⟨c.pos.1, by show (Int64.ofInt (s.x.pos.toInt + n.toNat)).toInt + s.skip.toInt ≤ _; rw [hpos, hsk0]; simp; omega,
      by show 0 ≤ (Int64.ofInt (s.x.pos.toInt + n.toNat)).toInt + ((s.x.have - UInt32.ofNat n.toNat).toNat : Int)
         rw [hpos, UInt32.ofNat_toNat, hnv]; omega⟩
    (fun _ => ⟨r.how, r.copyDirect, r.gzipDirect, r.junk, r.flags.1, r.flags.2.1, r.flags.2.2,
      fun hz => (r.unalloc hz).2.2.1, r.againSize,
      by show (Int64.ofInt (s.x.pos.toInt + n.toNat)).toInt + ((s.x.have - UInt32.ofNat n.toNat).toNat : Int) ≤ _
         rw [hpos, UInt32.ofNat_toNat, hnv]; omega,
      fun _ => hsk0, r.againEof⟩)
    (fun hw => absurd (hm.symm.trans hw) read_ne_write'') (fun _ hc => r.copyIn hc)
  have acc2 := acc1.put inv1 inv2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl C.views
  have erec : ({ s with x := { s.x with «have» := s.x.have - n, next := Ptr.ref (BRef.blk b) (off + n.toNat), pos := Int64.ofInt (s.x.pos.toInt + n.toNat) } } : GzState) =
      getsRec s b off n.toNat := by
    simp only [getsRec, UInt32.ofNat_toNat]
  rw [erec]
  have ok2 : E.Ok fs (putGz h1 E.i (getsRec s b off n.toNat)) :=
    ⟨acc2, fun sc hsc => by
      simp only [putGz, upd_same, Option.some.injEq] at hsc
      subst hsc
      exact hsk0⟩
  obtain ⟨ac2, hac2, hacs2, -, -⟩ := C.now acc2
  have hbadd : Ptr.add l.buf (n.toNat : Int) (setS h1 E.i (getsRec s b off n.toNat)) =
      .ok (.ref E.r (E.off + (E.left0 - l.left.toNat) + n.toNat), setS h1 E.i (getsRec s b off n.toNat)) := by
    rw [hbuf]
    exact Ptr.add_nat_ok hac2 (by omega)
  refine RunSafe.bind_lift hbadd ?_
  refine RunSafe.pure' ⟨rfl, rfl, ?_, ?_, ok2, rfl⟩
  · show (l.left - n).toNat = _
    rw [UInt32.toNat_sub_of_le]
    exact UInt32.le_iff_toNat_le.mpr hnl
  · show Ptr.ref E.r (E.off + (E.left0 - l.left.toNat) + n.toNat) = Ptr.ref E.r (E.off + (E.left0 - (l.left - n).toNat))
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hnl)]
    congr 1
    omega

theorem diff_count (j : Nat) (hj : j < 2 ^ 31) :
    ((Int64.ofInt (j : Int)).toUInt64.toUInt32 + 1).toNat = j + 1 := by
  have h0 : (0 : Int64) ≤ Int64.ofInt (j : Int) := by
    rw [Int64.le_iff_toInt_le, i64_toInt_ofInt (by omega) (by omega)]; simp
  have hv : (Int64.ofInt (j : Int)).toUInt64.toUInt32.toNat = j := by
    rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt,
      i64_toInt_ofInt (by omega) (by omega)]
    simp only [Int.toNat_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  rw [GetcUngetc.have_succ_toNat (by rw [hv]; omega), hv]

theorem rec_skip0 (s : GzState) (hs : s.skip = 0) : ({ s with past := 1 } : GzState) = { s with skip := 0, past := 1 } := by
  rw [← hs]

/-- What a trip of the `gzgets` loop leaves, relative to the loop variable `l` at its start. -/
def GetsPost (E : GetsEnv) (fs0 : Fs) (l : Zlib.Gzread.GetsLoop) (l' : Zlib.Gzread.GetsLoop) (fs' : Fs) (h' : Heap) :
    Prop :=
  (l'.brk = false → l'.eol = .null → l'.left ≠ 0 → l'.left.toNat < l.left.toNat) ∧ l'.left.toNat ≤ E.left0 ∧
    l'.buf = .ref E.r (E.off + (E.left0 - l'.left.toNat)) ∧ E.Ok fs' h' ∧ fs' = fs0

/-- **The rest of a trip of `gzgets`** from a reader in `GzInv` (no pending skip): `past = 1` with nothing
buffered, else the bounded `memchr` and the copy. The `position overflow` refusal cannot happen: `GzReadInv.posHave`
leaves room for the buffered bytes. -/
theorem getsRest_inv {E : GetsEnv} (C : GetsCaller E) {fs : Fs} {h : Heap} {s : GzState}
    {l : Zlib.Gzread.GetsLoop} {fin : Prop}
    (ok : E.Ok fs h) (inv : GzInv h E.i s) (hm : s.mode = GZ_READ) (hbrk : l.brk = false) (hleft : l.left ≠ 0)
    (hl0 : l.left.toNat ≤ E.left0) (hbuf : l.buf = .ref E.r (E.off + (E.left0 - l.left.toNat))) :
    RunSafe (getsRest (gzSt E.i) l) fs h fin (GetsPost E fs l) := by
  have c := inv.common
  have rd := inv.reader hm
  have hs := c.record
  have hsk0 : s.skip = 0 := ok.2 s hs
  have hleft' : l.left.toNat ≠ 0 := fun e => hleft (UInt32.toNat_inj.mp (by rw [e]; rfl))
  have hsmall := C.small
  unfold getsRest
  refine RunSafe.bind_lift (ldS_run hs) ?_
  refine RunSafe.ite (fun h0 => ?_) (fun h0 => ?_)
  · -- nothing buffered: `past = 1`, break
    refine RunSafe.bind_lift (updS_run hs _) ?_
    have inv2 := inv.put_past hm
    rw [← rec_skip0 s hsk0] at inv2
    have acc2 := ok.1.put inv inv2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl C.views
    refine RunSafe.pure' ⟨fun e => by simp at e, hl0, hbuf, ⟨acc2, fun sc hsc => ?_⟩, rfl⟩
    simp only [setS, upd_same, Option.some.injEq] at hsc
    subst hsc
    exact hsk0
  have hh : s.x.have ≠ 0 := by simpa using h0
  have hh' : s.x.have.toNat ≠ 0 := fun e => hh (UInt32.toNat_inj.mp (by rw [e]; rfl))
  refine RunSafe.bind_lift (ldS_run hs) ?_
  dsimp only
  obtain ⟨n, hrun, hle, hpn, hz⟩ := gz_room_run hs (if s.x.«have» > l.left then l.left else s.x.«have»)
  have hn0 : (if s.x.«have» > l.left then l.left else s.x.«have»).toNat ≠ 0 := by
    split <;> assumption
  have hn0' : (if s.x.«have» > l.left then l.left else s.x.«have»).toNat ≤ s.x.have.toNat ∧
      (if s.x.«have» > l.left then l.left else s.x.«have»).toNat ≤ l.left.toNat := by
    split
    · rename_i hg
      have := UInt32.lt_iff_toNat_lt.mp hg
      omega
    · rename_i hg
      have : ¬ l.left.toNat < s.x.have.toNat := fun hh => hg (UInt32.lt_iff_toNat_lt.mpr hh)
      omega
  have hph := rd.posHave
  have hlo := c.pos.2.2
  have hnz : n ≠ 0 := by
    intro e
    rcases hz e with e' | e'
    · exact hn0 (by rw [e']; rfl)
    · omega
  have hnz' : n.toNat ≠ 0 := fun e => hnz (UInt32.toNat_inj.mp (by rw [e]; rfl))
  refine RunSafe.bind_lift hrun ?_
  refine RunSafe.ite (fun e => absurd (by simpa using e) hnz) (fun _ => ?_)
  obtain ⟨b, off, a, hx, -, -, -, hba, hlea⟩ := c.next hh
  have hba' : Space.get h (BRef.blk b) = some a := hba
  obtain ⟨eol, hmc, heol⟩ := memchrB_run hba' (off := off) (n := n.toNat) (by omega) 10
  refine RunSafe.bind_lift (by rw [hx]; exact hmc) ?_
  have tail : ∀ m : UInt32, 1 ≤ m.toNat → m.toNat ≤ n.toNat → (eol = .null ∨ m.toNat ≤ n.toNat) →
      RunSafe (getsCopy (gzSt E.i) l s m eol) fs h fin (GetsPost E fs l) := by
    intro m hm1 hmn _
    refine (getsCopy_run C ok inv hm hm1 (by omega) (by omega) hl0 hbuf).mono ?_
    rintro l' fs' h' ⟨hb', he', hl', hbf, ok', hfs'⟩
    refine ⟨fun _ _ _ => by omega, by omega, hbf, ok', hfs'⟩
  try dsimp only
  refine RunSafe.ite (fun hne => ?_) (fun hne => ?_)
  · have hne' : eol ≠ .null := by simpa using hne
    obtain ⟨j, hj, rfl⟩ := heol.resolve_left hne'
    have hd : Ptr.diff (Ptr.ref (BRef.blk b) (off + j)) s.x.next h = .ok (Int64.ofInt (j : Int), h) := by
      rw [hx]
      have := Ptr.diff_ok (h := h) (r := BRef.blk b) hba' (o1 := off + j) (o2 := off) (by omega) (by omega)
        (by constructor <;> omega)
      have e : ((off + j : Nat) : Int) - (off : Int) = (j : Int) := by omega
      rw [e] at this
      exact this
    refine RunSafe.bind_lift hd ?_
    have hc := diff_count j (by have := n.toNat_lt; omega)
    exact tail _ (by omega) (by omega) (Or.inr (by omega))
  · exact tail n (by omega) (Nat.le_refl _) (Or.inr (Nat.le_refl _))

/-! ## The trip that meets the largest position -/

set_option maxRecDepth 20000 in
/-- The literal `"position overflow"`. -/
theorem lit_posov (h : Heap) : ∃ p, strLit "position overflow" h = .ok (p, h) ∧
    (∃ t, CString h p t) ∧ ∀ b, ¬ ByteRoot p b := by
  obtain ⟨p, hp, ht, hr⟩ := lit_run "position overflow"
    [112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 118, 101, 114, 102, 108, 111, 119]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) h
  exact ⟨p, hp, ⟨_, ht⟩, hr⟩

/-- **The trip at the largest position**: after a fetch at `x.pos = GZ_OFF_MAX` (patch 0004 loads one byte to see
the end of the input), `gz_room` gives `0`, the buffered output is dropped and `"position overflow"` is recorded.
`h1` is the heap before the fetch (a reader in `GzInv`), `post` the fetch's post-condition. -/
theorem getsRest_max {E : GetsEnv} (C : GetsCaller E) {fs fs2 : Fs} {h h2 : Heap} {s s2 : GzState}
    {l : Zlib.Gzread.GetsLoop} {fin : Prop}
    (ok : E.Ok fs h) (inv : GzInv h E.i s) (post : GzPost h E.i s [] fs2 h2 GzInvOut) (kept : FdsKept fs fs2)
    (hs2 : h2.gzstates E.i = some s2) (hm2 : s2.mode = GZ_READ) (hsk2 : s2.skip = 0)
    (hmax : s2.x.pos.toInt = 9223372036854775807) (hh2 : s2.x.have ≠ 0) (hleft : l.left ≠ 0)
    (hl0 : l.left.toNat ≤ E.left0) (hbuf : l.buf = .ref E.r (E.off + (E.left0 - l.left.toNat))) :
    RunSafe (getsRest (gzSt E.i) l) fs2 h2 fin (fun l' fs' h' => l'.brk = true ∧ l'.left = l.left ∧
      l'.buf = l.buf ∧ E.Ok fs' h' ∧ fs' = fs2) := by
  have V := C.views
  have hfs2 : FileSystem fs2 := post.1
  obtain ⟨t2, ht2, -⟩ := post.2
  have e2 : t2 = s2 := Option.some.inj (ht2.1.1.symm.trans hs2)
  subst e2
  have ho2 := ht2
  unfold getsRest
  refine RunSafe.bind_lift (ldS_run hs2) ?_
  refine RunSafe.ite (fun h0 => absurd (by simpa using h0) hh2) (fun _ => ?_)
  refine RunSafe.bind_lift (ldS_run hs2) ?_
  dsimp only
  have hn0 : (if t2.x.«have» > l.left then l.left else t2.x.«have») ≠ 0 := by
    split <;> assumption
  refine RunSafe.bind_lift (gz_room_zero hs2 hmax _ hn0) ?_
  refine RunSafe.ite (fun _ => ?_) (fun hne => absurd (by decide) hne)
  refine RunSafe.bind_lift (updX_run hs2 _) ?_
  -- the record with the buffered output dropped is in `GzInv`
  have hu3 := upToOutput_x ho2.1 0 t2.x.next
  have e3 : ({ t2 with x := { t2.x with «have» := 0, next := t2.x.next } } : GzState) =
      { t2 with x := { t2.x with «have» := 0 } } := rfl
  rw [e3] at hu3
  have inv3 := GzInvUpToOutput.inv0 hu3 hm2 rfl
  have live2 : ∀ b, GzOwned h2 E.i t2 b → h2.live b := fun b hb =>
    (putGz_live ho2.1.1 b).1 (ho2.1.2.common.live b
      ((putGz_owned (s' := clearOut t2) ho2.1.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).2 hb))
  have p3 := post_put_any (I := GzInv) (fs := fs2) hs2 live2 inv3 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl hfs2
  have acc3 := ok.1.step inv (post_trans post (fun t ht => ht.1.1) hs2 p3) kept V
  obtain ⟨p, hp, ⟨tm, htm⟩, hroot⟩ := lit_posov (putGz h2 E.i { t2 with x := { t2.x with «have» := 0 } })
  refine RunSafe.bind_lift hp ?_
  have hmsg : p = .null ∨ ∃ t, CString (putGz h2 E.i { t2 with x := { t2.x with «have» := 0 } }) p t ∧
      ∀ b, ByteRoot p b → ¬ GzOwned (putGz h2 E.i { t2 with x := { t2.x with «have» := 0 } }) E.i
        { t2 with x := { t2.x with «have» := 0 } } b :=
    Or.inr ⟨tm, htm, fun b hb => absurd hb (hroot b)⟩
  obtain ⟨after, s', hrun, inv', hs', -, fr, lc⟩ := inv3.gz_error Z_DATA_ERROR p hmsg (by decide)
  have own := inv3.gz_error_own Z_DATA_ERROR p hmsg (by decide) hrun
  refine RunSafe.bind_lift hrun ?_
  have acc4 := acc3.step inv3 (post_of_gz_error inv3 inv' hs' fr lc own hfs2) (fun _ => Iff.rfl) V
  refine RunSafe.pure' ⟨rfl, rfl, rfl, ⟨acc4, fun sc hsc => ?_⟩, rfl⟩
  rw [inv'.common.record] at hsc
  cases hsc
  rw [hs']
  exact hsk2

/-! ## The loop -/

/-- What a trip of the loop keeps: `GetsPost` and the read budget. -/
def GetsTrip (E : GetsEnv) (l l' : Zlib.Gzread.GetsLoop) (fs' : Fs) (h' : Heap) : Prop :=
  (l'.brk = false → l'.eol = .null → l'.left ≠ 0 → l'.left.toNat < l.left.toNat) ∧ l'.left.toNat ≤ E.left0 ∧
    l'.buf = .ref E.r (E.off + (E.left0 - l'.left.toNat)) ∧ E.Ok fs' h' ∧
    (ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs' E.s0.fd)

/-- **One trip of the `gzgets` loop**: `gz_fetch` when nothing is buffered, then the rest of the trip. -/
theorem getsBody_run (P : ReadInvFacts) (head : DecompFacts) (room : GzFetchRoom) {E : GetsEnv}
    (C : GetsCaller E) {fs : Fs} {h : Heap} {l : Zlib.Gzread.GetsLoop}
    (ok : E.Ok fs h) (rf : ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs E.s0.fd) (hbrk : l.brk = false)
    (hleft : l.left ≠ 0) (hl0 : l.left.toNat ≤ E.left0) (hbuf : l.buf = .ref E.r (E.off + (E.left0 - l.left.toNat))) :
    RunSafe (getsBody (gzSt E.i) l) fs h (ReadsFinite E.fs0 E.s0.fd) (GetsTrip E l) := by
  have V := C.views
  obtain ⟨s, inv, hm0, hfd⟩ := ok.1.cur
  have hm : s.mode = GZ_READ := hm0.trans C.mode
  have hs := inv.common.record
  have hsk : s.skip = 0 := ok.2 s hs
  have hfs := ok.1.fsys
  -- `getsRest` from a reader in `GzInv`
  have restInv : ∀ {fs1 : Fs} {h1 : Heap} {s1 : GzState}, E.Ok fs1 h1 → GzInv h1 E.i s1 → s1.mode = GZ_READ →
      (ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs1 E.s0.fd) →
      RunSafe (getsRest (gzSt E.i) l) fs1 h1 (ReadsFinite E.fs0 E.s0.fd) (GetsTrip E l) := by
    intro fs1 h1 s1 ok1 inv1 hm1 rf1
    refine (getsRest_inv C ok1 inv1 hm1 hbrk hleft hl0 hbuf).mono ?_
    rintro l' fs' h' ⟨a, b, c', d, e⟩
    subst e
    exact ⟨a, b, c', d, rf1⟩
  unfold getsBody
  refine RunSafe.bind_lift (ldS_run hs) ?_
  refine RunSafe.ite (fun h0 => ?_) (fun _ => restInv ok inv hm rf)
  have h0' : s.x.have = 0 := by simpa using h0
  have hu := GzInv.upToOutput inv hm h0'
  have F := gz_fetch_safe_of gz_look_safe (gz_decomp_safe_of head) E.i h fs s hu h0' hfs hm
    (P.noEnd h E.i s inv hm) (P.copyIn h E.i s inv hm) (P.msgLit h E.i s inv hm)
  have F' : RunSafe (Zlib.Gzread.gz_fetch (gzSt E.i)) fs h (ReadsFinite E.fs0 E.s0.fd) fun r fs2 h2 =>
      ((r = 0 ∨ r = -1) ∧ FdsKept fs fs2 ∧ GzPost h E.i s [] fs2 h2 GzInvOut ∧
        (ReadsFinite fs s.fd → ReadsFinite fs2 s.fd) ∧ ∃ s2, h2.gzstates E.i = some s2 ∧ FetchKeeps s s2) ∧
      ∀ s2, h2.gzstates E.i = some s2 →
        s2.x.pos.toInt + s2.x.have.toNat ≤ 9223372036854775807 ∨ s2.x.pos.toInt = 9223372036854775807 :=
    ⟨F.1, fun f => F.2.1 (by rw [hfd]; exact rf f), fun r fs2 h2 he => by
      obtain ⟨hr, k, post, -, rf2, -, s2, hs2, keep, -⟩ := F.2.2 r fs2 h2 he
      exact ⟨⟨hr, k, post, rf2, s2, hs2, keep⟩, room E.i h fs s r fs2 h2 hu h0' hfs hm (P.noEnd h E.i s inv hm)
        (P.copyIn h E.i s inv hm) (P.msgLit h E.i s inv hm) he⟩⟩
  refine RunSafe.bind F' ?_
  rintro r fs2 h2 ⟨⟨hr, k2, post2, rf2, s2, hs2, keep⟩, hroom⟩
  have hm2 : s2.mode = GZ_READ := keep.1.trans hm
  have hsk2 : s2.skip = 0 := keep.2.2.1.trans hsk
  have rf2' : ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs2 E.s0.fd := fun f => by
    rw [← hfd]; exact rf2 (by rw [hfd]; exact rf f)
  have ho2 : GzInvOut h2 E.i s2 := by
    obtain ⟨-, t, ht, -⟩ := post2
    have e : t = s2 := Option.some.inj (ht.1.1.symm.trans hs2)
    subst e
    exact ht
  -- the record after the fetch is in `GzInv` when its output fits
  have toOk : s2.x.pos.toInt + s2.x.have.toNat ≤ 9223372036854775807 → E.Ok fs2 h2 ∧ GzInv h2 E.i s2 := by
    intro hb
    have inv2 : GzInv h2 E.i s2 := (GzInvOut.upToSkip ho2 hm2 hb).inv (Or.inr hsk2)
    refine ⟨⟨ok.1.step inv (post2.mono fun t ht => ?_) k2 V, fun sc hsc => ?_⟩, inv2⟩
    · have e : t = s2 := Option.some.inj (ht.1.1.symm.trans hs2)
      subst e
      exact inv2
    · rw [hs2] at hsc; cases hsc; exact hsk2
  have rest : RunSafe (getsRest (gzSt E.i) l) fs2 h2 (ReadsFinite E.fs0 E.s0.fd) (GetsTrip E l) := by
    rcases hroom s2 hs2 with hb | hmax
    · obtain ⟨ok2, inv2⟩ := toOk hb
      exact restInv ok2 inv2 hm2 rf2'
    · by_cases hh2 : s2.x.have = 0
      · obtain ⟨ok2, inv2⟩ := toOk (by have := s2.x.pos.toInt_lt; rw [hh2]; simp; omega)
        exact restInv ok2 inv2 hm2 rf2'
      · refine (getsRest_max C ok inv post2 k2 hs2 hm2 hsk2 hmax hh2 hleft hl0 hbuf).mono ?_
        rintro l' fs' h' ⟨hb', hl', hbf', ok', e⟩
        subst e
        exact ⟨fun hf => (by rw [hb'] at hf; cases hf), (by rw [hl']; exact hl0), (by rw [hbf', hl']; exact hbuf),
          ok', rf2'⟩
  refine RunSafe.ite (fun _ => ?_) (fun _ => rest)
  refine RunSafe.bind_lift (ldS_run hs2) ?_
  refine RunSafe.ite (fun hz => ?_) (fun _ => rest)
  have hz' : s2.x.have = 0 := by simpa using hz
  obtain ⟨ok2, -⟩ := toOk (by have := s2.x.pos.toInt_lt; rw [hz']; simp; omega)
  exact RunSafe.pure' ⟨fun hf => (by cases hf), hl0, hbuf, ok2, rf2'⟩

/-- **The `gzgets` loop**: it returns, under the read budget, with `buf` inside the caller's buffer. -/
theorem gets_loop (P : ReadInvFacts) (head : DecompFacts) (room : GzFetchRoom) {E : GetsEnv}
    (C : GetsCaller E) {fs : Fs} {h : Heap} {l : Zlib.Gzread.GetsLoop}
    (ok : E.Ok fs h) (rf : ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs E.s0.fd) (hbrk : l.brk = false)
    (hleft : l.left ≠ 0) (heol : l.eol = .null) (hl0 : l.left.toNat ≤ E.left0)
    (hbuf : l.buf = .ref E.r (E.off + (E.left0 - l.left.toNat))) :
    RunSafe (gdoWhile (getsBody (gzSt E.i))
      (fun (l : Zlib.Gzread.GetsLoop) => pure (!l.brk && l.left != 0 && l.eol == .null, l)) l) fs h
      (ReadsFinite E.fs0 E.s0.fd) fun l' fs' h' =>
        l'.left.toNat ≤ E.left0 ∧ l'.buf = .ref E.r (E.off + (E.left0 - l'.left.toNat)) ∧ E.Ok fs' h' := by
  refine RunSafe.doWhile
    (fun k (l : Zlib.Gzread.GetsLoop) fs h => k = l.left.toNat ∧ l.brk = false ∧ l.left ≠ 0 ∧ l.eol = .null ∧
      l.left.toNat ≤ E.left0 ∧ l.buf = .ref E.r (E.off + (E.left0 - l.left.toNat)) ∧ E.Ok fs h ∧
      (ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs E.s0.fd))
    (fun k l' fs h => (l'.brk = false → l'.eol = .null → l'.left ≠ 0 → l'.left.toNat < k) ∧ l'.left.toNat ≤ E.left0 ∧
      l'.buf = .ref E.r (E.off + (E.left0 - l'.left.toNat)) ∧ E.Ok fs h ∧
      (ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs E.s0.fd)) _ ?_ ?_ (k := l.left.toNat)
    (fun _ => by have := l.left.toNat_lt; omega) ⟨rfl, hbrk, hleft, heol, hl0, hbuf, ok, rf⟩
  · rintro k l1 fs1 h1 ⟨rfl, b1, l1ne, -, ll1, bf1, ok1, rf1⟩
    exact getsBody_run P head room C ok1 rf1 b1 l1ne ll1 bf1
  · rintro k l1 fs1 h1 ⟨dec, ll1, bf1, ok1, rf1⟩
    refine RunSafe.pure' ⟨fun hc => ?_, fun _ => ⟨ll1, bf1, ok1⟩⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at hc
    obtain ⟨⟨hb, hl⟩, he⟩ := hc
    exact ⟨l1.left.toNat, fun _ => dec hb he hl, rfl, hb, hl, he, ll1, bf1, ok1, rf1⟩

/-! ## The end of `gzgets`: the NUL -/

theorem left_toNat (len : Int32) (hl : 1 ≤ len.toInt) : (len.toUInt32 - 1).toNat = len.toInt.toNat - 1 := by
  have h0 : (0 : Int32) ≤ len := by rw [Int32.le_iff_toInt_le]; simp; omega
  have hv : len.toUInt32.toNat = len.toInt.toNat := by
    rw [Int32.toNat_toUInt32_of_le h0, Int32.toNat_toInt]
  have hlt := len.toInt_lt
  rw [UInt32.toNat_sub_of_le]
  · rw [hv]; rfl
  · rw [UInt32.le_iff_toNat_le, hv, UInt32.toNat_one]; omega

/-- **After the skip**: the loop, then `buf[0] = 0` at the end of what was read, inside `[buf, buf + len)`. -/
theorem getsMain_run (P : ReadInvFacts) (head : DecompFacts) (room : GzFetchRoom) {E : GetsEnv}
    (C : GetsCaller E) {fs : Fs} {h : Heap} (len : Int32)
    (ok : E.Ok fs h) (rf : ReadsFinite E.fs0 E.s0.fd → ReadsFinite fs E.s0.fd)
    (hl1 : 1 ≤ len.toInt) (hlen : len.toInt.toNat = E.left0 + 1) :
    RunSafe (getsMain (gzSt E.i) (.ref E.r E.off) len) fs h (ReadsFinite E.fs0 E.s0.fd)
      (fun _ fs' h' => E.Ok fs' h') := by
  have hleft := left_toNat len hl1
  have tail : ∀ (b : BPtr) (k : Nat) (fs1 : Fs) (h1 : Heap), b = .ref E.r (E.off + k) → k ≤ E.left0 →
      E.Ok fs1 h1 → RunSafe (do
        if b == Ptr.ref E.r E.off && len > 1 then return .null
        store8 b 0
        return Ptr.ref E.r E.off : G BPtr) fs1 h1 (ReadsFinite E.fs0 E.s0.fd) (fun _ fs' h' => E.Ok fs' h') := by
    intro b k fs1 h1 hb hk ok1
    refine RunSafe.ite (fun _ => RunSafe.pure' ok1) (fun _ => ?_)
    obtain ⟨s1, inv1, -, -⟩ := ok1.1.cur
    obtain ⟨ac, hac, hacs, hro, hun⟩ := C.now ok1.1
    have hfit := C.fit
    have hst : store8 b 0 h1 = .ok ((), Space.put h1 E.r (ac.set! (E.off + k) 0)) := by
      rw [hb]; exact Ptr.store_ok hac hro (by omega)
    refine RunSafe.bind_lift hst ?_
    have hcov : ∀ j, j < ac.size → ¬ Zlib.Inflate.Proofs.RegionCovers E.R E.r j →
        (ac.set! (E.off + k) 0)[j]? = ac[j]? := by
      intro j _ hnc
      have hne : E.off + k ≠ j := by
        intro e
        exact hnc (C.covers (by omega) (by omega))
      simp [Array.set!, Array.getElem?_setIfInBounds_ne hne]
    obtain ⟨acc2, -⟩ := ok1.1.region_put (off := E.off) inv1 hac hro (by simp [Array.set!])
      (fun b' hb' => hun s1 inv1.common.record b' hb') C.root hcov C.views
    refine RunSafe.pure' ⟨acc2, fun sc hsc => ok1.2 sc ?_⟩
    have : (Space.put h1 E.r (ac.set! (E.off + k) 0)).gzstates E.i = h1.gzstates E.i := by
      cases E.r with
      | dstate_depth c =>
        show (match h1.dstates c with
          | some s => { h1 with dstates := upd h1.dstates c (some { s with depth := ac.set! (E.off + k) 0 }) }
          | none => h1).gzstates E.i = _
        cases h1.dstates c <;> rfl
      | _ => rfl
    rw [← this]; exact hsc
  unfold getsMain
  dsimp only
  refine RunSafe.ite (fun hne => ?_) (fun hz => ?_)
  · have hne' : (len.toUInt32 - 1).toNat ≠ 0 := by
      intro e
      have h0 : len.toUInt32 - 1 = 0 := UInt32.toNat_inj.mp (by rw [e]; rfl)
      simp [h0] at hne
    refine RunSafe.bind (gets_loop P head room C ok rf rfl
      (show len.toUInt32 - 1 ≠ 0 from fun e => hne' (by rw [e]; rfl)) rfl
      (show (len.toUInt32 - 1).toNat ≤ E.left0 by rw [hleft]; omega)
      (show Ptr.ref E.r E.off = Ptr.ref E.r (E.off + (E.left0 - (len.toUInt32 - 1).toNat)) by
        rw [hleft, show E.left0 - (len.toInt.toNat - 1) = 0 by omega]; rfl)) ?_
    rintro l fs1 h1 ⟨hl, hb, ok1⟩
    exact tail l.buf (E.left0 - l.left.toNat) fs1 h1 hb (by omega) ok1
  · exact tail (.ref E.r E.off) 0 fs h rfl (Nat.zero_le _) ok

/-! ## `gzgets` -/

theorem gzgets_eq (i : Nat) (buf : BPtr) (len : Int32) :
    Zlib.Gzread.gzgets (some (.in_gzstate_x i)) buf len = (do
      if buf == .null || len < 1 then return .null
      let s ← ldS (some (.tab i))
      if s.mode != GZ_READ then return .null
      if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return .null
      if s.again != 0 then Zlib.Gzlib.gz_error (some (.tab i)) Z_OK .null
      if (← ldS (some (.tab i))).skip != 0 then
        if (← Zlib.Gzread.gz_skip (some (.tab i))) == -1 then return .null
      getsMain (some (.tab i)) buf len : G BPtr) := rfl

/-- From the skip test on: `gz_skip` when a skip is pending, then `getsMain`. -/
theorem gets_afterAgain (P : ReadInvFacts) (head : DecompFacts) (room : GzFetchRoom)
    (skip : GzSkipRead) {E : GetsEnv} (C : GetsCaller E) {h1 : Heap} {s1 : GzState} (len : Int32)
    (acc : Acc E.h0 E.i E.s0 E.fs0 E.R E.fs0 h1) (inv1 : GzInv h1 E.i s1)
    (hl1 : 1 ≤ len.toInt) (hlen : len.toInt.toNat = E.left0 + 1) :
    RunSafe (do
        if (← ldS (some (.tab E.i))).skip != 0 then
          if (← Zlib.Gzread.gz_skip (some (.tab E.i))) == -1 then return .null
        getsMain (some (.tab E.i)) (.ref E.r E.off) len : G BPtr) E.fs0 h1 (ReadsFinite E.fs0 E.s0.fd)
      (fun _ fs' after => Acc E.h0 E.i E.s0 E.fs0 E.R fs' after) := by
  have V := C.views
  obtain ⟨t1, it1, hm1, hfd1⟩ := acc.cur
  have e1 : t1 = s1 := it1.state_eq inv1.common.record
  subst e1
  have hm : t1.mode = GZ_READ := hm1.trans C.mode
  have hfs := acc.fsys
  refine RunSafe.bind_lift (ldS_run inv1.common.record) ?_
  refine RunSafe.ite (fun hk => ?_) (fun hk => ?_)
  · have hk' : t1.skip ≠ 0 := by simpa using hk
    have rd := inv1.reader hm
    refine RunSafe.bind (RunSafe.fin_mono (skip E.i h1 E.fs0 t1 inv1 hfs hm hk' rd.errEnd rd.copyIn rd.msgLit)
      (fun f => by rw [hfd1]; exact f)) ?_
    rintro r fs2 h2 ⟨hr01, k2, post2, rf2, s2', hs2', -, -, -, hsk2'⟩
    have hsk2 : r = 0 → ∀ sc, h2.gzstates E.i = some sc → sc.skip = 0 := fun h0 sc hsc => by
      rw [hs2'] at hsc; cases hsc; exact hsk2' h0
    have acc2 := acc.step inv1 post2 k2 V
    refine RunSafe.ite (fun _ => RunSafe.pure' acc2) (fun hr => ?_)
    have hr0 : r = 0 := by
      rcases hr01 with h0 | h0
      · exact h0
      · exact absurd (by simp [h0]) hr
    refine (getsMain_run P head room C len ⟨acc2, hsk2 hr0⟩
      (fun f => by rw [← hfd1]; exact rf2 (by rw [hfd1]; exact f)) hl1 hlen).mono fun _ _ _ ok => ok.1
  · have hk' : t1.skip = 0 := by simpa using hk
    refine (getsMain_run P head room C len ⟨acc, fun sc hsc => ?_⟩ id hl1 hlen).mono fun _ _ _ ok => ok.1
    rw [inv1.common.record] at hsc; cases hsc; exact hk'

/-- **The run of `gzgets`**: the effect over the declared caller region. -/
theorem gzgets_run (P : ReadInvFacts) (head : DecompFacts) (room : GzFetchRoom) (skip : GzSkipRead)
    (i : Nat) (buf : BPtr) (len : Int32) (h : Heap) (fs : Fs) (s : GzState) (inv : GzInv h i s)
    (hfs : FileSystem fs) (hargs : GzArguments h i s (.gzgets (some (.in_gzstate_x i)) buf len)) :
    RunSafe (Zlib.Gzread.gzgets (some (.in_gzstate_x i)) buf len) fs h (ReadsFinite fs s.fd)
      (fun _ fs' after => Acc h i s fs (GzWriteRegions (.gzgets (some (.in_gzstate_x i)) buf len)) fs' after) := by
  rw [gzgets_eq]
  refine RunSafe.ite (fun _ => RunSafe.pure' (Acc.refl _ inv hfs)) (fun hc => ?_)
  have hbn : buf ≠ .null := by intro e; apply hc; simp [e]
  have hl1 : 1 ≤ len.toInt := by
    have : ¬ len < 1 := by intro e; apply hc; simp [e]
    rw [Int32.lt_iff_toInt_lt] at this
    have h1 : (1 : Int32).toInt = 1 := by decide
    omega
  have hlt := len.toInt_lt
  have hR : GzWriteRegions (.gzgets (some (.in_gzstate_x i)) buf len) = [⟨buf, len.toInt.toNat⟩] := by
    simp [GzWriteRegions, hl1]
  have hrg : GzRange h i s buf len.toInt.toNat true := by
    have hc' : ¬ (len.toInt < 1 ∨ buf = .null) := by
      rintro (hh | hh)
      · omega
      · exact hbn hh
    have := hargs
    simp only [GzArguments, if_neg hc'] at this
    exact this
  obtain ⟨r, off, a, rfl, hg, hro, hfit⟩ : ∃ r off a, buf = .ref r off ∧ Space.get h r = some a ∧
      Space.ro h r = false ∧ off + len.toInt.toNat ≤ a.size := by
    rcases hrg with hz | ⟨-, hw, -⟩
    · omega
    · rcases hw rfl with ⟨hn, -⟩ | ⟨r, off, a, e, hg, hro, hfit⟩
      · exact absurd hn hbn
      · exact ⟨r, off, a, e, hg, hro, hfit⟩
  have hun : ∀ b, ByteRoot (.ref r off) b → ¬ GzOwned h i s b := by
    rcases hrg with hz | ⟨-, -, hun⟩
    · omega
    · exact hun
  let E : GetsEnv := ⟨h, i, s, fs, GzWriteRegions (.gzgets (some (.in_gzstate_x i)) (.ref r off) len), r, off,
    len.toInt.toNat - 1, a⟩
  have hlen : len.toInt.toNat = E.left0 + 1 := by show _ = len.toInt.toNat - 1 + 1; omega
  refine RunSafe.bind_lift (ldS_run inv.common.record) ?_
  refine RunSafe.ite (fun _ => RunSafe.pure' (Acc.refl _ inv hfs)) (fun hm' => ?_)
  have hm : s.mode = GZ_READ := by simpa using hm'
  have C : GetsCaller E := {
    region := by
      show GzWriteRegions (Call.gzgets (some (GzFileRef.in_gzstate_x i)) (.ref r off) len) =
        [⟨.ref r off, len.toInt.toNat - 1 + 1⟩]
      rw [hR, show len.toInt.toNat - 1 + 1 = len.toInt.toNat by omega]
    get := hg
    ro := hro
    fit := by show off + (len.toInt.toNat - 1) + 1 ≤ a.size; omega
    unowned := hun
    mode := hm
    small := by show len.toInt.toNat - 1 < 2 ^ 31; omega }
  have acc0 : Acc E.h0 E.i E.s0 E.fs0 E.R E.fs0 h := Acc.refl _ inv hfs
  refine RunSafe.ite (fun _ => RunSafe.pure' acc0) (fun _ => ?_)
  refine RunSafe.ite (fun _ => ?_) (fun _ => gets_afterAgain P head room skip C len acc0 inv hl1 hlen)
  obtain ⟨after, s', hrun, inv', hs', -, fr, lc⟩ := inv.gz_error Z_OK .null (Or.inl rfl) (by decide)
  have own := inv.gz_error_own Z_OK .null (Or.inl rfl) (by decide) hrun
  refine RunSafe.bind_lift hrun ?_
  exact gets_afterAgain P head room skip C len
    (acc0.step inv (post_of_gz_error inv inv' hs' fr lc own hfs) (fun _ => Iff.rfl) C.views) inv' hl1 hlen

/-- **`gzgets_step`** (skeleton statement) from `gz_skip`'s statement `GzSkipRead` and the facts of the fetch. -/
theorem gzgets_step_of' (P : ReadInvFacts) (head : DecompFacts) (room : GzFetchRoom)
    (skip : GzSkipRead) (i : Nat) (buf : BPtr) (len : Int32) :
    GzCallSafe i (.gzgets (some (.in_gzstate_x i)) buf len) := by
  intro h fs s inv hfs hargs
  have R := gzgets_run P head room skip i buf len h fs s inv hfs hargs
  refine ⟨R.1, fun hn => R.2.1 (hn trivial), fun v fs' after he => ?_⟩
  obtain ⟨k, hfs', s', inv', m, f, bf, lc, -⟩ := R.2.2 v fs' after he
  exact ⟨k, hfs', s', inv', m, f, bf, lc⟩

/-- **`gzgets_step`** (skeleton statement), from the one open fact of `inflate` that the whole read side rests on
(`InflateStuckNoOutput`, as for `gzread_step_stuck`). `gz_skip` is batch 3's `gzSkipRead_holds`. -/
theorem gzgets_step_stuck (stuck : InflateStuckNoOutput) (i : Nat) (buf : BPtr) (len : Int32) :
    GzCallSafe i (.gzgets (some (.in_gzstate_x i)) buf len) :=
  gzgets_step_of' readInvFacts_holds stuck (gzFetchRoom_holds stuck)
    (gzSkipRead_holds (gz_fetch_safe_stuck stuck)) i buf len

/-- **`gzgets_step`**, the skeleton statement. -/
theorem gzgets_step (i : Nat) (buf : BPtr) (len : Int32) : GzCallSafe i (.gzgets (some (.in_gzstate_x i)) buf len) :=
  gzgets_step_stuck inflateStuckNoOutput_holds i buf len

end ZlibF.Spec.Public.GzRead

