import ZlibF.Proof.«inffast.c.sig»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

theorem u8_forall (P : UInt8 → Prop) (h : ∀ n, n < 256 → P (UInt8.ofNat n)) : ∀ x, P x := by
  intro x
  have := h x.toNat x.toNat_lt
  simpa using this

theorem mask16 : ∀ x : UInt8, ((x.toUInt32 &&& 16) != 0) = ((x &&& 16) != 0) :=
  u8_forall _ (by decide +kernel)
theorem mask64 : ∀ x : UInt8, ((x.toUInt32 &&& 64) == 0) = ((x &&& 64) == 0) :=
  u8_forall _ (by decide +kernel)
theorem mask32 : ∀ x : UInt8, ((x.toUInt32 &&& 32) != 0) = ((x &&& 32) != 0) :=
  u8_forall _ (by decide +kernel)
theorem mask15 : ∀ x : UInt8, (x.toUInt32 &&& 15).toNat = (x &&& 15).toNat :=
  u8_forall _ (by decide +kernel)
theorem toNat32 : ∀ x : UInt8, x.toUInt32.toNat = x.toNat :=
  u8_forall _ (by decide +kernel)

variable {e : Env} {c : Ctx}

theorem LS.congr {l l' : L} {i o : Nat} (hl : LS e l i o) (h1 : l'.in_ = l.in_) (h2 : l'.out = l.out)
    (h3 : l'.hold = l.hold) (h4 : l'.bits = l.bits) : LS e l' i o := by
  obtain ⟨a, b, c, d, f, g, h, k⟩ := hl
  exact ⟨by rw [h1]; exact a, by rw [h2]; exact b, c, d, f, by rw [h4]; exact g, by rw [h3, h4]; exact h,
    by rw [h4]; exact k⟩

/-- `hold >>= k; bits -= k;` -/
def dropL (l : L) (k : UInt32) : L := { l with hold := l.hold >>> k.toUInt64, bits := l.bits - k }

theorem dropL_hold (l : L) (k : UInt32) (hk : k.toNat < 64) :
    (dropL l k).hold.toNat = l.hold.toNat / 2 ^ k.toNat := u64_shr hk

theorem dropL_bits (l : L) (k : UInt32) (hk : k.toNat ≤ l.bits.toNat) :
    (dropL l k).bits.toNat = l.bits.toNat - k.toNat := u32_toNat_sub hk

theorem LS.dropL {l : L} {i o : Nat} (hl : LS e l i o) (k : UInt32) (hk : k.toNat ≤ l.bits.toNat) (hk64 : k.toNat < 64) :
    LS e (dropL l k) i o := by
  have h1 := dropL_hold l k hk64
  have h2 := dropL_bits l k hk
  refine ⟨hl.hin, hl.hout, hl.hi0, hl.hi1, hl.ho0, by rw [h2]; have := hl.hb; omega, ?_, by rw [h2]; have := hl.hacc; omega⟩
  rw [h1, h2]
  have := hl.hH
  have hp : 2 ^ l.bits.toNat = 2 ^ (l.bits.toNat - k.toNat) * 2 ^ k.toNat := by
    rw [← Nat.pow_add]; congr 1; omega
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr
  rw [hp] at this
  exact this

theorem Sg_drop (H b i k : Nat) (hk : k ≤ b) : Sg e (H / 2 ^ k) (b - k) i = (Sg e H b i).drop k := by
  unfold Sg
  rw [bitsOfNat_drop H b k hk, List.drop_append_of_le_length (by rw [bitsOfNat_length]; exact hk)]

theorem Sg_dropL (l : L) (k : UInt32) (i : Nat) (hk : k.toNat ≤ l.bits.toNat) (hk64 : k.toNat < 64) :
    Sg e (dropL l k).hold.toNat (dropL l k).bits.toNat i = (Sg e l.hold.toNat l.bits.toNat i).drop k.toNat := by
  rw [dropL_hold l k hk64, dropL_bits l k hk]
  exact Sg_drop _ _ _ _ hk

theorem LS.pullL {l : L} {i o : Nat} (hl : LS e l i o) (hb : l.bits.toNat ≤ 22) (hi : i < e.i0 + e.sm0.avail_in.toNat) :
    LS e (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (i + 1) o :=
  LS.pull e hl hb hi _

theorem Sg_pullL {l : L} {i o : Nat} (hl : LS e l i o) (hb : l.bits.toNat ≤ 22) (hi : i < e.i0 + e.sm0.avail_in.toNat) :
    Sg e (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).hold.toNat
      (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat (i + 1) = Sg e l.hold.toNat l.bits.toNat i := by
  rw [pullL_hold _ _ _ hl.hb hl.hH, pullL_bits _ _ _ hl.hb]
  exact Sg_pull e _ _ _ hl.hH hi


theorem shl32_ok {h : Heap} {x n : UInt32} (hn : n.toNat < 32) : OkOn h (shl32 x n) (x <<< n) := by
  rw [shl32_eq hn]; rfl

theorem shr64_ok {h : Heap} {x n : UInt64} (hn : n.toNat < 64) : OkOn h (shr64 x n) (x >>> n) := by
  rw [shr64_eq hn]; rfl

theorem i64_toU32 (n : Nat) (h : n < 2 ^ 32) :
    (Int64.ofInt (n : Int)).toUInt64.toUInt32.toNat = n := by
  rw [Int64.ofInt_eq_ofNat, UInt64.toNat_toUInt32, ← Int64.toNat_toBitVec]
  simp
  omega

theorem i64_toInt (n : Nat) (h : n < 2 ^ 62) : (Int64.ofInt (n : Int)).toInt = n := by
  rw [Int64.ofInt_eq_ofNat]; exact Int64.toInt_ofNat_of_lt (by omega)

theorem Env.bg_le (e : Env) : e.bg ≤ e.o0 := by unfold Env.bg; omega

/-- `strm->avail_in`-style facts used everywhere. -/
theorem Env.hroomA (e : Env) : e.o0 + e.sm0.avail_out.toNat ≤ e.A0.size := e.hAsz

/-- The continuation of the distance block after the extra bits were read: add the extra bits to the base, drop them,
compute how much of the output of this call there is, and copy. -/
def distCont (c : Ctx) (l : L) : M L := do
  let m ← shl32 1 l.op
  let l : L := { l with dist := l.dist + (l.hold.toUInt32 &&& m - 1) }
  let __do_lift ← shr64 l.hold l.op.toUInt64
  let l : L := { l with hold := __do_lift }
  let l : L := { l with bits := l.bits - l.op }
  let d ← Ptr.diff l.out c.beg
  let l : L := { l with op := d.toUInt64.toUInt32 }
  copyMatch c l

theorem distCont_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63)
    (hx : l.op.toNat ≤ 13) (hxb : l.op.toNat ≤ l.bits.toNat) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false) :
    Wp (distCont c l) (e.heap A msg m) (fun l' h' =>
      ∃ xv rest, readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (xv, rest) ∧
        l'.in_ = l.in_ ∧ l'.againD = l.againD ∧
        ((l'.broke = false ∧ LS e l' i (o + l.len.toNat) ∧ Sg e l'.hold.toNat l'.bits.toNat i = rest ∧
            h' = e.heap (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o (l.dist.toNat + xv) l.len.toNat A) msg m) ∨
         (l'.broke = true ∧ LS e l' i o ∧ Sg e l'.hold.toNat l'.bits.toNat i = rest ∧ ∃ p, h' = e.heap A p BAD))) := by
  have hbgo : e.bg ≤ o := by have := e.bg_le; have := hls.ho0; omega
  have hoA : o ≤ A.size := by omega
  have hxs : l.op.toNat < 32 := by omega
  unfold distCont
  refine Wp.bindO (shl32_ok hxs) ?_
  dsimp only
  have hlow := hold_low32 (x := l.hold) (k := l.op) hxs
  have hlowlt : l.hold.toNat % 2 ^ l.op.toNat < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hpow : 2 ^ l.op.toNat ≤ 2 ^ 13 := Nat.pow_le_pow_right (by omega) hx
  have hdist' : (l.dist + (l.hold.toUInt32 &&& (1 <<< l.op) - 1)).toNat = l.dist.toNat + l.hold.toNat % 2 ^ l.op.toNat := by
    rw [u32_toNat_add (by rw [hlow]; omega), hlow]
  refine Wp.bindO (shr64_ok (x := l.hold) (n := l.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega)) ?_
  have hbgdef : e.bg = e.o0 - (e.start.toNat - e.sm0.avail_out.toNat) := rfl
  have hst32 := UInt32.toNat_lt e.start
  have hstart := e.hstart
  have hbeg := e.hbeg
  have hdiff : OkOn (e.heap A msg m) (Ptr.diff l.out c.beg) (Int64.ofInt (((o - e.bg : Nat)) : Int)) := by
    rw [hls.hout, hc.beg]
    have := Ptr.diff_ok (r := BRef.blk e.ob) (a := A) (o1 := o) (o2 := e.bg) (e.heap_bytes_ob A msg m) hoA (by omega)
      ⟨by omega, by omega⟩
    have e1 : (o : Int) - (e.bg : Int) = ((o - e.bg : Nat) : Int) := by omega
    rw [e1] at this
    exact this
  refine Wp.bindO hdiff ?_
  have hopn : (Int64.ofInt (((o - e.bg : Nat)) : Int)).toUInt64.toUInt32.toNat = o - e.bg := i64_toU32 _ (by omega)
  have hls1 : LS e (dropL l l.op) i o := hls.dropL l.op hxb (by omega)
  have hrb := readBits_bitsOfNat l.op.toNat l.bits.toNat l.hold.toNat (inBits e i) hxb
  have hsg := Sg_dropL (e := e) l l.op i hxb (by omega)
  refine Wp.mono (copyMatch_run (e := e) (c := c) hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op, here := l.here,
      op := (Int64.ofInt (((o - e.bg : Nat)) : Int)).toUInt64.toUInt32, len := l.len,
      dist := l.dist + (l.hold.toUInt32 &&& 1 <<< l.op - 1), from_ := l.from_, broke := l.broke, againL := l.againL,
      againD := l.againD } o hls.hout hbgo hopn (by simp only [hdist']; omega) hlen.1 (by simp; omega) hbroke) ?_
  intro l' h' hq
  have hho0 := hls.ho0
  obtain ⟨hin, hhold, hbits, -, hagD, hres⟩ := hq
  refine ⟨l.hold.toNat % 2 ^ l.op.toNat, Sg e (dropL l l.op).hold.toNat (dropL l l.op).bits.toNat i, ?_, hin, hagD, ?_⟩
  · unfold Sg; rw [hrb, dropL_hold l l.op (by omega), dropL_bits l l.op hxb]
  · rcases hres with ⟨hb, hout, hh⟩ | ⟨hb, p, hh, hout⟩
    · refine Or.inl ⟨hb, ⟨?_, hout, hls.hi0, hls.hi1, by omega, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hin]; exact hls.hin
      · rw [hbits]; exact hls1.hb
      · rw [hhold, hbits]; exact hls1.hH
      · rw [hbits]; exact hls1.hacc
      · rw [hhold, hbits]; rfl
      · rw [hh, hdist']
    · refine Or.inr ⟨hb, ⟨?_, ?_, hls.hi0, hls.hi1, hls.ho0, ?_, ?_, ?_⟩, ?_, p, hh⟩
      · rw [hin]; exact hls.hin
      · rw [hout]; exact hls.hout
      · rw [hbits]; exact hls1.hb
      · rw [hhold, hbits]; exact hls1.hH
      · rw [hbits]; exact hls1.hacc
      · rw [hhold, hbits]; rfl


theorem Env.heap_cget (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32) (r : CodeRef) :
    Space.get (e.heap A msg m) r = Space.get e.h0 r := by
  cases r with
  | istate_codes id =>
    simp only [Space.get, e.heap_istates]
    by_cases hid : id = e.stid
    · subst hid; simp [e.hs0, upd_same]
    · simp [upd_ne _ _ _ _ hid]
  | st_lenfix => simp [Space.get, e.heap_static]
  | st_distfix => simp [Space.get, e.heap_static]

theorem Env.heap_cget_DCA (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32) :
    Space.get (e.heap A msg m) e.rd = some e.DCA := by rw [e.heap_cget]; exact e.hDCA

theorem Env.heap_cget_LCA (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32) :
    Space.get (e.heap A msg m) e.rl = some e.LCA := by rw [e.heap_cget]; exact e.hLCA

theorem Env.heap_bytes_in (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32) :
    (e.heap A msg m).bytes e.ib = some e.IN := by rw [e.heap_bytes_ne A msg m e.hsep]; exact e.hIN

/-- How a distance-table entry is treated by `dodist`. -/
abbrev DistClass (e : Env) (E : Code) : Prop :=
  (E.op &&& 16 ≠ 0 ∧ (E.op &&& 15).toNat ≤ 13 ∧ 1 ≤ E.val.toNat) ∨
  (E.op &&& 16 = 0 ∧ E.op &&& 64 = 0 ∧ 1 ≤ E.op.toNat ∧ E.op.toNat ≤ 15 ∧ e.od + E.val.toNat + 2 ^ E.op.toNat ≤ e.DCA.size) ∨
  (E.op &&& 16 = 0 ∧ E.op &&& 64 ≠ 0)

/-- A distance block that ended (no link): a match of length `len` was copied, or an error was found. `S` is the bit
stream after the code of the distance symbol. -/
def DistEnd (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32) (S : List Bool) (i o len : Nat) (E : Code) (l' : L)
    (h' : Heap) : Prop :=
  ¬ DistLink E ∧ l'.againD = false ∧
  ((∃ i' xv rest, i ≤ i' ∧ i' ≤ i + 2 ∧ readBits (E.op &&& 15).toNat S = some (xv, rest) ∧
      l'.broke = false ∧ LS e l' i' (o + len) ∧ Sg e l'.hold.toNat l'.bits.toNat i' = rest ∧
      h' = e.heap (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o (E.val.toNat + xv) len A) msg m) ∨
   (∃ i' p, i ≤ i' ∧ i' ≤ i + 2 ∧ l'.broke = true ∧ LS e l' i' o ∧ h' = e.heap A p BAD))


/-- After the distance base and the number `op` of extra bits are set: refill the bit buffer (at most twice) and copy. -/
def dodistBase (c : Ctx) (l_2 : L) : M L := do
  if l_2.bits < l_2.op then do
    let __x ← pull l_2
    if __x.bits < __x.op then do
      let __x ← pull __x
      distCont c __x
    else distCont c __x
  else distCont c l_2

theorem dodistBase_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hx : l.op.toNat ≤ 13) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 5 ≤ l.bits.toNat)) :
    Wp (dodistBase c l) (e.heap A msg m) (fun l' h' =>
      ∃ i' xv rest, i ≤ i' ∧ i' ≤ i + 2 ∧ readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (xv, rest) ∧
        l'.againD = l.againD ∧
        ((l'.broke = false ∧ LS e l' i' (o + l.len.toNat) ∧ Sg e l'.hold.toNat l'.bits.toNat i' = rest ∧
            h' = e.heap (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o (l.dist.toNat + xv) l.len.toNat A) msg m) ∨
         (l'.broke = true ∧ LS e l' i' o ∧ ∃ p, h' = e.heap A p BAD))) := by
  unfold dodistBase
  by_cases h1 : l.bits < l.op
  · simp only [h1, ite_true]
    have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m)) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1)) hls.hb
    by_cases h2 : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits <
        (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op
    · simp only [h2, ite_true]
      have h2' : l.bits.toNat + 8 < l.op.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp h2
        simp only [pullL] at this hb3 ⊢
        omega
      have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
      have hb3' : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat ≤ 22 := by omega
      refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m)) ?_
      have hl4 := hl3.pullL hb3' hi2
      have hs4 := Sg_pullL hl3 hb3' hi2
      have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))) (e.IN.getD (i + 1) 0)
        (.ref (BRef.blk e.ib) (i + 1 + 1)) hl3.hb
      refine Wp.mono (distCont_wp hc A msg m _ (i + 1 + 1) o hl4 hA ho hAb (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 hb4 ⊢; omega) (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
      refine ⟨i + 1 + 1, xv, rest, by omega, by omega, ?_, hagD, ?_⟩
      · simp only [pullL] at hr hs4 hs3 ⊢
        rw [hs4, hs3] at hr
        exact hr
      · simp only [pullL] at hres ⊢
        exact Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres
    · simp only [h2, ite_false]
      have h2n : (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op.toNat ≤
          (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat := by
        have : ¬ ((pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).bits.toNat <
            (pullL l (e.IN.getD i 0) (.ref (BRef.blk e.ib) (i + 1))).op.toNat) :=
          fun h => h2 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (distCont_wp hc A msg m _ (i + 1) o hl3 hA ho hAb (by simp only [pullL]; omega)
        h2n (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
      refine ⟨i + 1, xv, rest, by omega, by omega, ?_, hagD, ?_⟩
      · simp only [pullL] at hr hs3 ⊢
        rw [hs3] at hr
        exact hr
      · simp only [pullL] at hres ⊢
        exact Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres
  · simp only [h1, ite_false]
    have h1' : l.op.toNat ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    refine Wp.mono (distCont_wp hc A msg m l i o hls hA ho hAb hx h1' hd1 hd2 hlen hbroke) ?_
    intro l' h' hq
    obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
    exact ⟨i, xv, rest, by omega, by omega, hr, hagD, Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres⟩

end Zlib.Inffast.Proofs
