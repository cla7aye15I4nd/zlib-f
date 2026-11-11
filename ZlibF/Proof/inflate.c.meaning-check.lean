import ZlibF.Proof.«inflate.c.check-dispatch»
import ZlibF.Proof.«inflate.c.meaning-trailer»
import ZlibF.Proof.«inflate.c.meaning-checksum»

/-!
# inflate.c: `CHECK` keeps the format meaning in the loop

Batch 2, `trailer_steps`. In a zlib or gzip trailer stage with nothing of the
trailer read, `case CHECK:` either leaves for more input, or adds this call's
output since the check base to `total` and to the running check, compares
the check field, and then falls through to `LENGTH`: a gzip trailer goes on
to its length field (`MeaningTrailer.length_step`), a zlib stream ends. A
check field that differs from the check of the output enters `BAD`, and no
valid stream continues the input read.

Raw data reaches `CHECK` in the end stage (`wrap = 0` skips the check); that
case waits for the end-stage interface change agreed with batch 1.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `inflate_CHECK_views_run` (`inflate.c.check-dispatch`) with the value of
the check update: when the check is updated, it is `UPDATE_CHECK` of the `out`
bytes before `put`. -/
theorem inflate_CHECK_value_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (out : UInt32) (hout : out = l.out_ - l.left)
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (hw : s.wrap ≠ 0) (B : BitInv h l bs) (hS : Zlib.Crc32.Proofs.StaticsOK h)
    (hput : chkCond s out = true → ∃ ref off array, l.put = .ref ref off ∧
      Space.get h ref = some array ∧ out.toNat ≤ off ∧ off ≤ array.size) :
    ∃ rr l' j, runX (NEEDBITS 32) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 32 ∧
        runX (inflate_CHECK c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 32 ≤ l'.bits.toNat ∧ ∃ v,
        (chkCond s out = true → ∀ ref off array, l.put = .ref ref off → Space.get h ref = some array →
          v = inflateChecksumValue s.flags s.check ((array.toList.drop (off - out.toNat)).take out.toNat)) ∧
        ((s.wrap &&& 4) ≠ 0 → (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠ (chkS s out v).check →
          ∃ i, strTable[i]? = some "incorrect data check" ∧
            runX (inflate_CHECK c) l h =
              .ok ((.ok (), { l' with out_ := l.left }), tcBadHeap (chkH h r zs z s out v) r zs (chkZ z s out v) (chkS s out v) i)) ∧
        (¬ ((s.wrap &&& 4) ≠ 0 ∧ (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠ (chkS s out v).check) →
          runX (inflate_CHECK c) l h =
            runX (inflate_LENGTH c) { l' with out_ := l.left, hold := 0, bits := 0 }
              (setI (chkH h r zs z s out v) zs { chkS s out v with mode := LENGTH }))) := by
  obtain ⟨rr, l', j, hrun, hj, B', hS', hbits, hshape, hmax, hid, hok, hleave⟩ := NEEDBITS_run B 32 (by decide)
  have hw' : ¬ s.wrap = 0 := hw
  have hput' : l'.put = l.put := by rw [hshape]
  have hleft' : l'.left = l.left := by rw [hshape]
  have hout' : l'.out_ = l.out_ := by rw [hshape]
  refine ⟨rr, l', j, hrun, hj, B', hS', ?_, ?_⟩
  · intro e
    obtain ⟨h1, h2, h3⟩ := hleave e
    refine ⟨h2, h1, h3, ?_⟩
    unfold inflate_CHECK
    rw [hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, runX_throw]
  · intro e
    refine ⟨hok e, ?_⟩
    by_cases hcond : chkCond s out = true
    · obtain ⟨ref, off, a, hp, hb, ho1, ho2⟩ := hput hcond
      have hct' : chkCond s (l.out_ - l.left) = true := by rw [← hout]; exact hcond
      have hct3 : ¬ s.wrap &&& 4 = 0 ∧ ¬ l.out_ - l.left = 0 := by
        simpa [chkCond, ← hout] using hcond
      -- the heap after `total_out += out; total += out`
      let h1 : Heap := setI (r.put h { z with total_out := z.total_out + out.toUInt64 }) zs
        { s with total := s.total + out.toUInt64 }
      have hg1 : (Space.get h1 ref : Option (Array UInt8)) = some a := by
        rw [byte_view_get_setI, byte_view_get_stream_put]
        exact hb
      have hs1 : h1.istates zs = some { s with total := s.total + out.toUInt64 } := by simp [h1]
      have hS1 : Zlib.Crc32.Proofs.StaticsOK h1 := by
        simpa only [Zlib.Crc32.Proofs.StaticsOK, h1, setI, ZStreamRef.put_static] using hS
      have hptr : Ptr.add l.put (-(out.toNat : Int)) h1 = .ok (.ref ref (off - out.toNat), h1) := by
        rw [hp]; exact Ptr.sub_nat_ok hg1 ho1 ho2
      let v := inflateChecksumValue s.flags s.check ((a.toList.drop (off - out.toNat)).take out.toNat)
      have hv : UPDATE_CHECK (some (.tab zs)) s.check (.ref ref (off - out.toNat)) out h1 = .ok (v, h1) :=
        UPDATE_CHECK_all_views hS1 hs1 hg1 (by omega) s.check
      have hptr2 := hptr
      have hv2 := hv
      simp [h1, hout] at hptr2 hv2
      refine ⟨v, ?_, ?_, ?_⟩
      · intro _ ref' off' a' hp' hb'
        rw [hp] at hp'
        cases hp'
        rw [hb] at hb'
        cases hb'
        rfl
      · intro hbad hne
        have hz2 : r.get (chkH h r zs z s out v) = some (chkZ z s out v) := by
          simp [chkH, hz]
        have hs2 : (chkH h r zs z s out v).istates zs = some (chkS s out v) := by simp [chkH]
        obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check hr hc hz2 hs2
        refine ⟨i, hi, ?_⟩
        simp [chkH, chkZ, chkS, tcBadHeap, hcond, hct', hout] at hbm
        have hbad2 : (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v) := by
          refine ⟨hbad, ?_⟩
          simp only [chkS, hcond, ↓reduceIte] at hne
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0]
            rw [if_neg (by simpa using hf0)] at hne
            exact hne
          · rw [if_neg hf0]
            rw [if_pos hf0] at hne
            exact hne
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hct3, hct', hbad2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcond, hbm, chkCond,
          hput', hptr2, hv2]
        simp [tcBadHeap]
      · intro hn
        have hn2 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v) := by
          rintro ⟨ha, hb⟩
          apply hn
          refine ⟨ha, ?_⟩
          simp only [chkS, hcond, ↓reduceIte]
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0] at hb
            rw [if_neg (by simpa using hf0)]
            exact hb
          · rw [if_neg hf0] at hb
            rw [if_pos hf0]
            exact hb
        have hn3 : (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v := by
          by_cases hh : (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = v
          · exact hh
          · exact absurd ⟨hct3.1, hh⟩ hn2
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hct3, hct', hn3, setMode, runX_INITBITS, chkH, chkZ, chkS, hcond, chkCond,
          hput', hptr2, hv2]
    · have hcf : chkCond s out = false := by simpa using hcond
      have hcf' : chkCond s (l.out_ - l.left) = false := by rw [← hout]; exact hcf
      have hcf2 : ¬ ((s.wrap &&& 4) != 0 && (l.out_ - l.left) != 0) = true := by
        simpa [chkCond, ← hout] using hcond
      have hcf3 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ l.out_ - l.left = 0) := by
        simpa [chkCond, ← hout] using hcond
      refine ⟨s.check, fun cond => absurd cond hcond, ?_, ?_⟩
      · intro hbad hne
        have hz2 : r.get (chkH h r zs z s out s.check) = some (chkZ z s out s.check) := by
          simp [chkH, hz]
        have hs2 : (chkH h r zs z s out s.check).istates zs = some (chkS s out s.check) := by simp [chkH]
        obtain ⟨i, hi, hbm⟩ := tcBadMode_run (c := c) "incorrect data check" lit_data_check hr hc hz2 hs2
        refine ⟨i, hi, ?_⟩
        have hcf4 : l.out_ - l.left = 0 := by
          by_cases hz0 : l.out_ - l.left = 0
          · exact hz0
          · exact absurd ⟨hbad, hz0⟩ hcf3
        simp [chkH, chkZ, chkS, tcBadHeap, hcf, hcf', hout, hcf4, chkCond] at hbm
        have hbad2 : (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = s.check) := by
          refine ⟨hbad, ?_⟩
          simp only [chkS, hcf, Bool.false_eq_true, ↓reduceIte, ite_self] at hne
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0]
            rw [if_neg (by simpa using hf0)] at hne
            exact hne
          · rw [if_neg hf0]
            rw [if_pos hf0] at hne
            exact hne
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz,
          hout, hout', hleft', runX_pure, hcf3, hcf4, hcf', hbad2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcf, hbm, chkCond]
        simp [tcBadHeap]
      · intro hn
        have hn2 : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ (if s.flags = 0 then ZSWAP32 l'.hold else l'.hold) = s.check) := by
          rintro ⟨ha, hb⟩
          apply hn
          refine ⟨ha, ?_⟩
          simp only [chkS, hcf, Bool.false_eq_true, ↓reduceIte]
          by_cases hf0 : s.flags = 0
          · rw [if_pos hf0] at hb
            rw [if_neg (by simpa using hf0)]
            exact hb
          · rw [if_neg hf0] at hb
            rw [if_pos hf0]
            exact hb
        unfold inflate_CHECK
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, hw', hrun, e, hr, runX_modify, runX_get, wrZ_eq, wrI_eq, hz, hcf2,
          hout, hout', hleft', runX_pure, hcf3, hcf', hn2, setMode, runX_INITBITS, chkH, chkZ, chkS, hcf]

#print axioms inflate_CHECK_value_run

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs.MeaningCheck
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningBits Zlib.Inflate.Proofs.MeaningFields Zlib.Inflate.Proofs.MeaningTrailer
set_option autoImplicit false

/-! ## Heap-free facts -/

/-- The one-byte path of `adler32_z` on a canonical seed. -/
theorem adler_one (A B : Nat) (_lo : A % 65536 < 65521) (hi : A / 65536 < 65521) (_hb : B < 256) :
    ((A % 65536 + B) % 65521 + 65536 * (if 65521 ≤ A / 65536 % 65536 + (A % 65536 + B) % 65521 then
      A / 65536 % 65536 + (A % 65536 + B) % 65521 - 65521 else A / 65536 % 65536 + (A % 65536 + B) % 65521)) %
      18446744073709551616 =
    ((A / 65536 + (A % 65536 + B) % 65521) % 65521 * 65536 + (A % 65536 + B) % 65521) % 4294967296 := by
  have m : A / 65536 % 65536 = A / 65536 := Nat.mod_eq_of_lt (by omega)
  rw [m]
  have lowLt : (A % 65536 + B) % 65521 < 65521 := Nat.mod_lt _ (by decide)
  generalize (A % 65536 + B) % 65521 = L at lowLt ⊢
  generalize A / 65536 = H at hi ⊢
  split
  · next ge =>
    obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le ge
    rw [hD, Nat.add_sub_cancel_left]
    have d : (65521 + D) % 65521 = D := by omega
    rw [d, Nat.mod_eq_of_lt (show L + 65536 * D < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show D * 65536 + L < 4294967296 by omega)]
    omega
  · next lt =>
    have d : (H + L) % 65521 = H + L := Nat.mod_eq_of_lt (by omega)
    rw [d, Nat.mod_eq_of_lt (show L + 65536 * (H + L) < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show (H + L) * 65536 + L < 4294967296 by omega)]
    omega

/-- zlib's Adler-32 update (`adler32_z`, with its one-byte path) continues the
Adler-32 of the output so far. -/
theorem adlerValue_continue (xs ys : List UInt8) :
    adlerValue (adler32 xs).toUInt64 ys = (adler32 (xs ++ ys)).toUInt64 := by
  obtain ⟨lo, hi⟩ := MeaningChecksum.adler32_canonical xs
  have lt := (adler32 xs).toNat_lt
  have seed : (adler32 xs).toUInt64.toNat = (adler32 xs).toNat := UInt32.toNat_toUInt64 _
  have whole : adler32 (xs ++ ys) = adler32Update (adler32 xs) ys := by
    rw [adler32, adler32, adler32Update_append]
  rw [whole]
  unfold adlerValue
  split
  · next one =>
    match ys, one with
    | [b], _ =>
      have hb := b.toNat_lt
      apply UInt64.toNat_inj.mp
      have key := adler_one (adler32 xs).toNat b.toNat lo hi hb
      simpa only [adler32Update, List.foldl, adlerStep, List.headD, seed, UInt32.toNat_toUInt64,
        UInt64.toNat_ofNat', UInt32.toNat_ofNat'] using key
  · have start : adlerStart (adler32 xs).toUInt64 = adler32 xs := by
      apply UInt32.toNat_inj.mp
      unfold adlerStart
      rw [seed, UInt32.toNat_ofNat']
      omega
    rw [start]

/-- The CRC-32 seed as a 64-bit check value reads back unchanged. -/
theorem toUInt32_toUInt64 (x : UInt32) : x.toUInt64.toUInt32 = x := by
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64]
  exact Nat.mod_eq_of_lt x.toNat_lt

/-- A 64-bit length plus a 32-bit count. -/
theorem total_add (n : Nat) (x : UInt32) : UInt64.ofNat n + x.toUInt64 = UInt64.ofNat (n + x.toNat) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
  omega

/-- The trailer a complete wrapped header announces, and the check the decoder
keeps for it: gzip (`flags ≠ 0`, CRC-32 and length) or zlib (`flags = 0`,
Adler-32). -/
theorem trailer_kind {wrap : Api.Wrap} {configured : Nat} {dict header bodyDict : List UInt8}
    {s : InflateState} (wh : WrapHeader wrap configured dict header bodyDict) (wrapped : wrap ≠ .raw)
    (flagsM : FlagsMatch s wrap header) :
    (IsGzipHeader header ∧ s.flags ≠ 0 ∧ (wrap = .gzip ∨ (wrap = .auto ∧ header.take 2 = [31, 139])) ∧
      ∀ out, WrapTrailer wrap header out = le32 (crc32 out).toNat ++ le32 (out.length % 2 ^ 32)) ∨
    (s.flags = 0 ∧ ¬ (wrap = .gzip ∨ (wrap = .auto ∧ header.take 2 = [31, 139])) ∧
      ∀ out, WrapTrailer wrap header out = be32 (adler32 out).toNat) := by
  unfold FlagsMatch at flagsM
  simp only [wrapped, ite_false] at flagsM
  by_cases gz : IsGzipHeader header
  · rw [if_pos gz] at flagsM
    obtain ⟨gzipH, trailerEq⟩ := wrapHeader_gzip wh gz wrapped
    have method := gzipHeader_method gzipH
    left
    refine ⟨gz, ?_, ?_, fun out => congrFun trailerEq out⟩
    · intro zero
      rw [zero] at flagsM
      have eq : (0 : Int) = ((header.getD 2 0).toNat : Int) + 256 * ((header.getD 3 0).toNat : Int) := by
        simpa [gzipFlagsWord] using flagsM
      rw [method] at eq
      simp at eq
      omega
    · cases wrap with
      | raw => exact absurd rfl wrapped
      | zlib =>
        obtain ⟨_, zh, _⟩ := wh
        exact absurd gz (zlibHeader_not_gzip zh)
      | gzip => exact Or.inl rfl
      | auto => exact Or.inr ⟨rfl, gz⟩
  · rw [if_neg gz] at flagsM
    right
    refine ⟨flagsM, ?_, ?_⟩
    · rintro (g | ⟨_, magic⟩)
      · subst g
        obtain ⟨gh, _⟩ := wh
        exact gz (gzipHeader_is_gzip gh)
      · exact gz magic
    · intro out
      cases wrap with
      | raw => exact absurd rfl wrapped
      | zlib => rfl
      | gzip =>
        obtain ⟨gh, _⟩ := wh
        exact absurd (gzipHeader_is_gzip gh) gz
      | auto =>
        simp only [WrapTrailer]
        rw [if_neg gz]

/-- The last `p` bytes of the call's output are the `p` bytes before `put`. -/
theorem pending_bytes {h : Heap} {start put : BPtr} {callOut : List UInt8} {ref : BRef} {off p : Nat}
    {array : Array UInt8} (outBytes : Bytes h start callOut.length callOut)
    (putEq : put = inputAdvance start callOut.length) (ptr : put = .ref ref off)
    (get : Space.get h ref = some array) (le : p ≤ callOut.length) :
    (array.toList.drop (off - p)).take p = callOut.drop (callOut.length - p) := by
  rcases outBytes with ⟨null, _, _⟩ | ⟨r0, i0, a0, ptr0, get0, _, eq0⟩
  · rw [null] at putEq
    rw [putEq] at ptr
    cases ptr
  · rw [ptr0] at putEq
    rw [putEq] at ptr
    simp only [inputAdvance] at ptr
    cases ptr
    rw [get0] at get
    cases get
    generalize callOut.length = n at eq0 le ⊢
    rw [eq0, List.drop_take, List.drop_drop]
    rw [show n - (n - p) = p by omega, show i0 + (n - p) = i0 + n - p by omega]

/-- The output since the check base continues the checked output to the whole
output of the stage. -/
theorem checked_append (logOut callOut : List UInt8) (p : Nat) (le : p ≤ callOut.length) :
    (logOut ++ callOut).take ((logOut ++ callOut).length - p) ++ callOut.drop (callOut.length - p) =
      logOut ++ callOut := by
  have z : logOut.drop (logOut.length + (callOut.length - p)) = [] := List.drop_eq_nil_of_le (by omega)
  have tail : callOut.drop (callOut.length - p) =
      (logOut ++ callOut).drop ((logOut ++ callOut).length - p) := by
    rw [List.length_append, show logOut.length + callOut.length - p = logOut.length + (callOut.length - p) by
      omega, List.drop_append, z, List.nil_append, Nat.add_sub_cancel_left]
  rw [tail, List.take_append_drop]

#print axioms adlerValue_continue
#print axioms trailer_kind
#print axioms pending_bytes

/-! ## The loop step -/

/-- In the loop, a `CHECK` state stands for a trailer position. -/
theorem stage_of_check {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageM : LoopStageMatches h s f checked stage) (mode : s.mode = CHECK) :
    ∃ header out bytes, stage = .trailer header out bytes := by
  rcases stage with b | b | ⟨b, pos⟩ | ⟨header, out, bytes⟩ | out
  · have hi : s.mode ≤ DICTID := stageM.2
    rw [mode] at hi; exact absurd hi (by decide)
  · have m : s.mode = DICT := stageM; rw [mode] at m; exact absurd m (by decide)
  · have range := body_mode_range stageM.1
    rw [mode] at range
    exact absurd range (by decide)
  · exact ⟨header, out, bytes, rfl⟩
  · have m : s.mode = DONE := stageM; rw [mode] at m; exact absurd m (by decide)

/-- A heap with the same byte views and read-only flags. -/
def SameViews (h h' : Heap) : Prop :=
  ∀ ref : BRef, (Space.get h' ref : Option (Array UInt8)) = Space.get h ref ∧ Space.ro h' ref = Space.ro h ref

theorem SameViews.bytes {h h' : Heap} (views : SameViews h h') {p : BPtr} {n : Nat} {xs : List UInt8}
    (b : Bytes h p n xs) : Bytes h' p n xs := by
  rcases b with null | ⟨r, i, a, ptr, get, fits, eq⟩
  · exact Or.inl null
  · exact Or.inr ⟨r, i, a, ptr, by rw [(views r).1]; exact get, fits, eq⟩

theorem SameViews.writable {h h' : Heap} (views : SameViews h h') {p : BPtr} {n : Nat}
    (w : Writable h p n) : Writable h' p n := by
  rcases w with null | ⟨r, i, a, ptr, get, ro, fits⟩
  · exact Or.inl null
  · exact Or.inr ⟨r, i, a, ptr, by rw [(views r).1]; exact get, by rw [(views r).2]; exact ro, fits⟩

theorem sameViews_chk (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (out : UInt32)
    (v : UInt64) (S : InflateState) : SameViews h (setI (chkH h r zs z s out v) zs S) := by
  intro ref
  simp only [chkH]
  rw [byte_view_get_setI, byte_view_get_setI, byte_view_get_stream_put, byte_view_ro_setI, byte_view_ro_setI,
    byte_view_ro_stream_put]
  exact ⟨rfl, rfl⟩

theorem SameViews.setI {h h' : Heap} (views : SameViews h h') (zs : Nat) (S : InflateState) :
    SameViews h (setI h' zs S) := by
  intro ref
  rw [byte_view_get_setI, byte_view_ro_setI]
  exact views ref

/-- Setting and resetting the return register keeps the loop meaning. -/
theorem LoopMatches.ret_roundtrip {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} (loop : LoopMatches c f h l) :
    LoopMatches c f h { { l with ret := Z_STREAM_END } with ret := Z_OK } := by
  have retOk : l.ret = Z_OK := by
    obtain ⟨_, _, _, _, _, _, _, _, ok, _⟩ := loop
    exact ok
  have same : ({ { l with ret := Z_STREAM_END } with ret := Z_OK } : IL) = l := by
    cases l
    simp only at retOk ⊢
    rw [retOk]
  rw [same]
  exact loop

/-- `case CHECK:` of a zlib or gzip trailer in the loop: it leaves for more
input; or it adds the call's output since the check base to `total` and the
check, and then a matching gzip check field goes on to the length field
(`LENGTH`, which runs in the same trip), a matching zlib check ends the
stream, and a differing check field enters `BAD` with the input doomed. -/
theorem check_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (check : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = CHECK)
    (wrapped : f.wrap ≠ .raw) :
    ∃ result l' h', runX (inflate_CHECK c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  have loop0 := loop
  obtain ⟨zs, s, callOut0, consumed0, held0, stage0, st, hs, _, config0, _, _, binv0, leftLe0, pend0,
    putEq0, outBytes0, _, _, _, _, bitsEq0, heldBits0, parsed0, stageM0, wrapM0, _⟩ := loop
  have mode : s.mode = CHECK := check zs s st hs
  have sameState : ∀ zs' s', c.st = some (.tab zs') → h.istates zs' = some s' → zs = zs' ∧ s = s' := by
    intro zs' s' st' hs'
    rw [st] at st'
    cases st'
    exact ⟨rfl, Option.some.inj (hs.symm.trans hs')⟩
  obtain ⟨header0, out0, bytes0, rfl⟩ := stage_of_check stageM0 mode
  obtain ⟨_, _, ⟨checkFacts0, _, bitsBound0⟩⟩ := wrapM0
  have empty0 : bytes0 = [] := checkFacts0 mode
  subst empty0
  have aligned0 := trailer_aligned parsed0
  have heldAligned : l.bits.toNat % 8 = 0 := by
    have lengths := congrArg List.length bitsEq0
    simp only [List.length_append, bytesToBits_length'] at lengths
    have := heldBits0.1
    simp only [loopState] at this
    omega
  have bitsBound : l.bits.toNat ≤ 32 := bitsBound0
  have wrapNZ : s.wrap ≠ 0 := fun zero => wrapped (wrapCode_zero (config0.1.symm.trans zero))
  have wrap4 : (s.wrap &&& 4) ≠ 0 := by
    have code : s.wrap = wrapCode f.wrap := config0.1
    rw [code]
    revert wrapped
    generalize f.wrap = w
    intro wrapped
    cases w with
    | raw => exact absurd rfl wrapped
    | zlib => decide
    | gzip => decide
    | auto => decide
  -- the bytes since the check base are the last bytes before `put`
  have outNat : (l.out_ - l.left).toNat = loopPending l :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr leftLe0)
  have putAt : chkCond s (l.out_ - l.left) = true → ∃ ref off array, l.put = .ref ref off ∧
      Space.get h ref = some array ∧ (l.out_ - l.left).toNat ≤ off ∧ off ≤ array.size := by
    intro cond
    have nonzero : (l.out_ - l.left) ≠ 0 := by
      simp only [chkCond, Bool.and_eq_true, bne_iff_ne, ne_eq] at cond
      exact cond.2
    have pos : 0 < (l.out_ - l.left).toNat :=
      Nat.pos_of_ne_zero (fun zero => nonzero (UInt32.toNat_inj.mp (by simpa using zero)))
    rcases outBytes0 with ⟨_, len0, _⟩ | ⟨r0, i0, a0, ptr0, get0, fit0, _⟩
    · have := pend0.1
      omega
    · refine ⟨r0, i0 + callOut0.length, a0, by rw [putEq0, ptr0]; rfl, get0, ?_, fit0⟩
      have := pend0.1
      omega
  obtain ⟨rr, l', j', needRun, _, _, _, leaveRun, okRun⟩ :=
    inflate_CHECK_value_run (l.out_ - l.left) rfl strm st hz hs wrapNZ binv0 statics putAt
  obtain ⟨result, l'', j, needRun', shape, readEq, bitsCount, enough, leaveFacts, kinds, bitsMax,
    loopAt⟩ := LoopMatches.needbits loop0 (ok := (· ≤ 32))
      (fun zs' s' checked stage st' hs' stageM' => by
        obtain ⟨rfl, rfl⟩ := sameState zs' s' st' hs'
        obtain ⟨header, out, bytes, rfl⟩ := stage_of_check stageM' mode
        exact bitsFree_trailer f header out bytes) 32 (by decide)
  rw [needRun] at needRun'
  simp only [Except.ok.injEq, Prod.mk.injEq] at needRun'
  obtain ⟨⟨rfl, rfl⟩, _⟩ := needRun'
  have leftEq : l'.left = l.left := by rw [shape]
  have outEq : l'.out_ = l.out_ := by rw [shape]
  have putEq' : l'.put = l.put := by rw [shape]
  rcases kinds with okResult | leaveResult
  · -- 32 bits held: the check field
    subst okResult
    have bits32 : l'.bits.toNat = 32 := by
      have atLeast := enough rfl
      have n32 : (32 : UInt32).toNat = 32 := rfl
      rw [n32] at atLeast bitsMax
      omega
    have loop' := loopAt (by omega)
    obtain ⟨zs1, s1, callOut, consumed, held, stage, st1, hs1, retOk1, config1, haveLe1, inLen1,
      binv1, leftLe1, pend1, putEq1, outBytes1, writable1, sepIn1, sepWin1, sepOutIn1, bitsEq1,
      heldBits1, parsed1, stageM1, wrapM1, outputEq1⟩ := loop'
    obtain ⟨rfl, rfl⟩ := sameState zs1 s1 st1 hs1
    obtain ⟨header, out, bytes, rfl⟩ := stage_of_check stageM1 mode
    obtain ⟨flagsM1, widthM1, ⟨checkFacts1, _, _⟩⟩ := wrapM1
    have empty1 : bytes = [] := checkFacts1 mode
    subst empty1
    have outputEq : out = f.logOut ++ callOut := outputEq1
    have aligned1 := trailer_aligned parsed1
    have fieldEq := held_bytes bitsEq1 aligned1
    obtain ⟨field, fieldDef⟩ : ∃ x, x = (f.logIn ++ f.inp.take (loopRead l')).drop (consumed.length / 8) :=
      ⟨_, rfl⟩
    rw [← fieldDef] at fieldEq
    have heldLength : held.length = 32 := by
      have := heldBits1.1
      simp only [loopState] at this
      omega
    have fieldLength : field.length = 4 := by
      have := congrArg List.length fieldEq
      rw [heldLength, bytesToBits_length'] at this
      omega
    have holdValue : l'.hold.toNat = leValue field := by
      have := heldBits1.2
      simp only [loopState] at this
      rw [this]
      change heldValue held = _
      rw [fieldEq, heldValue_bytesToBits]
    have bitsField : bytesToBits (f.logIn ++ f.inp.take (loopRead l')) = consumed ++ bytesToBits field := by
      rw [bitsEq1, fieldEq]
    obtain ⟨bodyDict1, _, _, wh1, _⟩ := id parsed1
    -- the check after adding the output since the check base
    have pendLe : loopPending l' ≤ callOut.length := pend1.1
    have pendSame : loopPending l' = loopPending l := by
      unfold loopPending
      rw [leftEq, outEq]
    have outNat' : (l.out_ - l.left).toNat = loopPending l' := by rw [outNat, pendSame]
    let checked := (f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l')
    let pend := callOut.drop (callOut.length - loopPending l')
    have whole : checked ++ pend = out := by
      rw [outputEq]
      exact checked_append f.logOut callOut (loopPending l') pendLe
    have cm : CheckMeaning s f.wrap header checked := stageM1.2
    obtain ⟨_, v, value, badRun, matchRun⟩ := okRun rfl
    have vValue : chkCond s (l.out_ - l.left) = true →
        v = inflateChecksumValue s.flags s.check pend := by
      intro cond
      obtain ⟨ref, off, array, ptr, get, _, _⟩ := putAt cond
      rw [value cond ref off array ptr get, outNat']
      congr 1
      exact pending_bytes (put := l.put) outBytes1 (by rw [← putEq']; exact putEq1) ptr get pendLe
    -- the trailer kind
    have kind := trailer_kind wh1 wrapped flagsM1
    let expected : UInt64 := if f.wrap = .gzip ∨ (f.wrap = .auto ∧ header.take 2 = [31, 139]) then
      (crc32 out).toUInt64 else (adler32 out).toUInt64
    have newCheck : (chkS s (l.out_ - l.left) v).check = expected := by
      have old := cm.2 wrap4
      by_cases cond : chkCond s (l.out_ - l.left) = true
      · simp only [chkS, cond, ite_true]
        rw [vValue cond]
        rcases kind with ⟨_, flagsNZ, choice, _⟩ | ⟨flags0, choice, _⟩
        · simp only [expected, choice, ite_true] at old ⊢
          rw [inflateChecksumValue, if_neg (show s.flags ≠ 0 from flagsNZ), old, toUInt32_toUInt64, MeaningChecksum.crc_continue, whole]
        · simp only [expected, choice, ite_false] at old ⊢
          rw [inflateChecksumValue, if_pos (show s.flags = 0 from flags0), old, adlerValue_continue, whole]
      · have cond' : chkCond s (l.out_ - l.left) = false := by simpa using cond
        simp only [chkS, cond', Bool.false_eq_true, ite_false]
        have zero : loopPending l' = 0 := by
          have outZero : l.out_ - l.left = 0 := by
            by_cases z0 : l.out_ - l.left = 0
            · exact z0
            · exfalso
              apply cond
              simp only [chkCond, Bool.and_eq_true, bne_iff_ne, ne_eq]
              exact ⟨wrap4, z0⟩
          rw [← outNat', outZero]
          rfl
        have same : checked = out := by
          rw [← whole]
          simp only [pend, zero, Nat.sub_zero, List.drop_length, List.append_nil]
        rw [old, same]
    have newTotal : (chkS s (l.out_ - l.left) v).total = UInt64.ofNat out.length := by
      simp only [chkS]
      rw [cm.1, total_add, outNat', ← whole, List.length_append]
      congr 1
      simp only [pend, List.length_drop]
      omega
    have newCM : CheckMeaning (chkS s (l.out_ - l.left) v) f.wrap header out :=
      ⟨newTotal, fun _ => newCheck⟩
    have views2 := sameViews_chk h r zs z s (l.out_ - l.left) v
      { chkS s (l.out_ - l.left) v with mode := LENGTH }
    have binv2 := binv1.byte_views (fun ref => (views2 ref).1)
    have pendZero : loopPending { l' with out_ := l.left, hold := 0, bits := 0 } = 0 := by
      show l.left.toNat - l'.left.toNat = 0
      rw [leftEq]
      exact Nat.sub_self _
    have allChecked : (f.logOut ++ callOut).take ((f.logOut ++ callOut).length -
        loopPending { l' with out_ := l.left, hold := 0, bits := 0 }) = out := by
      rw [pendZero, Nat.sub_zero, List.take_length, ← outputEq]
    have hz2 : r.get (setI (chkH h r zs z s (l.out_ - l.left) v) zs
        { chkS s (l.out_ - l.left) v with mode := LENGTH }) = some (chkZ z s (l.out_ - l.left) v) := by
      simp [chkH, hz]
    obtain ⟨a, b, c', d, rfl⟩ : ∃ a b c' d, field = [a, b, c', d] := by
      match field, fieldLength with
      | [a, b, c', d], _ => exact ⟨a, b, c', d, rfl⟩
    obtain ⟨c1, c2, c3, c4, c5, _⟩ := config1
    rcases kind with ⟨isGzip, flagsNZ, choice, trailerEq⟩ | ⟨flags0, choice, trailerEq⟩
    · -- gzip: the CRC-32 field, then the length field
      have expEq : expected = (crc32 out).toUInt64 := by simp only [expected, choice, ite_true]
      have iff : l'.hold = (crc32 out).toUInt64 ↔ [a, b, c', d] <+: WrapTrailer f.wrap header out := by
        rw [hold_eq_le32 holdValue, trailerEq out]
        constructor
        · intro e
          rw [e]
          exact List.prefix_append _ _
        · intro pre
          have short : [a, b, c', d] <+: le32 (crc32 out).toNat :=
            List.prefix_of_prefix_length_le pre (List.prefix_append _ _) (by simp [le32])
          exact short.eq_of_length (by simp [le32])
      by_cases agree : l'.hold = (crc32 out).toUInt64
      · have notBad : ¬ ((s.wrap &&& 4) ≠ 0 ∧ (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠
            (chkS s (l.out_ - l.left) v).check) := by
          rintro ⟨_, ne⟩
          apply ne
          rw [newCheck, expEq, if_pos (show s.flags ≠ 0 from flagsNZ)]
          exact agree
        have run := matchRun notBad
        have pre : [] ++ [a, b, c', d] <+: WrapTrailer f.wrap header out := iff.mp agree
        have notComplete : [] ++ [a, b, c', d] ≠ WrapTrailer f.wrap header out := by
          rw [trailerEq out]
          intro e
          have := congrArg List.length e
          simp [le32] at this
        have loop2 : LoopMatches c f (setI (chkH h r zs z s (l.out_ - l.left) v) zs
            { chkS s (l.out_ - l.left) v with mode := LENGTH }) { l' with out_ := l.left, hold := 0, bits := 0 } := by
          refine ⟨zs, { chkS s (l.out_ - l.left) v with mode := LENGTH }, callOut, consumed ++ bytesToBits [a, b, c', d],
            [], .trailer header out [a, b, c', d], st, setI_istates_same _ _ _, retOk1,
            ⟨c1, c2, c3, c4, c5, show LENGTH ≠ SYNC by decide⟩, haveLe1, inLen1,
            ⟨binv2.have_eq, binv2.next, by simp⟩, Nat.le_of_eq (by rw [leftEq]),
            ⟨by rw [pendZero]; exact Nat.zero_le _, fun _ _ e => by cases e⟩, putEq1,
            views2.bytes outBytes1, views2.writable writable1, sepIn1, sepWin1, sepOutIn1,
            by rw [List.append_nil]; exact bitsField, ⟨rfl, rfl⟩,
            (wrapParsed_trailer_step parsed1 pre).1 notComplete, ?_, ?_, outputEq1⟩
          · rw [allChecked]
            exact ⟨Or.inr rfl, newCM⟩
          · refine ⟨flagsM1, widthM1, fun m => absurd (show LENGTH = CHECK from m) (by decide),
              fun _ => ⟨rfl, wrapped, isGzip, newTotal⟩, by simp [loopState]⟩
        have lengthHyp : ∀ zs' s', c.st = some (.tab zs') →
            (setI (chkH h r zs z s (l.out_ - l.left) v) zs
              { chkS s (l.out_ - l.left) v with mode := LENGTH }).istates zs' = some s' → s'.mode = LENGTH := by
          intro zs' s' st' hs'
          rw [st] at st'
          cases st'
          rw [setI_istates_same] at hs'
          cases hs'
          rfl
        obtain ⟨res, l3, h3, run3, trip⟩ := length_step loop2 strm hz2 lengthHyp
        exact ⟨res, l3, h3, run.trans run3, trip⟩
      · obtain ⟨i, _, bad⟩ := badRun wrap4 (by
          rw [newCheck, expEq, if_pos (show s.flags ≠ 0 from flagsNZ)]
          exact agree)
        refine ⟨_, _, _, bad, Or.inl ⟨rfl, Or.inr ?_⟩⟩
        refine ⟨zs, { chkS s (l.out_ - l.left) v with mode := BAD }, st, setI_istates_same _ _ _, rfl,
          retOk1, ⟨c1, c2, c3, c4, c5, show BAD ≠ SYNC by decide⟩, haveLe1, inLen1, ?_⟩
        intro source decoded valid _
        exact trailer_reject parsed1 bitsField (fun pre => agree (iff.mpr pre)) valid
    · -- zlib: the Adler-32 field ends the stream
      have expEq : expected = (adler32 out).toUInt64 := by simp only [expected, choice, ite_false]
      have cmpEq : (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) = ZSWAP32 l'.hold :=
        if_neg (fun ne => ne flags0)
      have iff : ZSWAP32 l'.hold = (adler32 out).toUInt64 ↔ [a, b, c', d] <+: WrapTrailer f.wrap header out := by
        rw [swap_eq_be32 holdValue, trailerEq out]
        constructor
        · intro e
          rw [e]
          exact List.prefix_refl _
        · intro pre
          exact pre.eq_of_length (by simp [be32])
      by_cases agree : ZSWAP32 l'.hold = (adler32 out).toUInt64
      · have notBad : ¬ ((s.wrap &&& 4) ≠ 0 ∧ (if s.flags ≠ 0 then l'.hold else ZSWAP32 l'.hold) ≠
            (chkS s (l.out_ - l.left) v).check) := by
          rintro ⟨_, ne⟩
          apply ne
          rw [newCheck, expEq, cmpEq]
          exact agree
        have run := matchRun notBad
        have pre : [] ++ [a, b, c', d] <+: WrapTrailer f.wrap header out := iff.mp agree
        have complete : [] ++ [a, b, c', d] = WrapTrailer f.wrap header out := by
          rw [trailerEq out]
          exact (swap_eq_be32 holdValue).mp agree
        have skip := inflate_LENGTH_skip (l := { l' with out_ := l.left, hold := 0, bits := 0 }) st
          (setI_istates_same (chkH h r zs z s (l.out_ - l.left) v) zs
            { chkS s (l.out_ - l.left) v with mode := LENGTH }) (Or.inr flags0)
        have views3 := views2.setI zs ({ chkS s (l.out_ - l.left) v with mode := DONE } : InflateState)
        have binv3 := binv1.byte_views (fun ref => (views3 ref).1)
        have loop3 : LoopMatches c f
            (setI (setI (chkH h r zs z s (l.out_ - l.left) v) zs
              { chkS s (l.out_ - l.left) v with mode := LENGTH }) zs
              ({ chkS s (l.out_ - l.left) v with mode := DONE } : InflateState))
            { l' with out_ := l.left, hold := 0, bits := 0 } := by
          refine ⟨zs, ({ chkS s (l.out_ - l.left) v with mode := DONE } : InflateState), callOut,
            consumed ++ bytesToBits [a, b, c', d], [], .done out, st, setI_istates_same _ _ _, retOk1,
            ⟨c1, c2, c3, c4, c5, show DONE ≠ SYNC by decide⟩, haveLe1, inLen1,
            ⟨binv3.have_eq, binv3.next, by simp⟩, Nat.le_of_eq (by rw [leftEq]),
            ⟨by rw [pendZero]; exact Nat.zero_le _, fun _ _ e => by cases e⟩, putEq1,
            views3.bytes outBytes1, views3.writable writable1, sepIn1, sepWin1, sepOutIn1,
            by rw [List.append_nil]; exact bitsField, ⟨rfl, rfl⟩,
            (wrapParsed_trailer_step parsed1 pre).2 complete, rfl, rfl, outputEq1⟩
        exact ⟨_, _, _, run.trans skip, Or.inr ⟨rfl, Or.inr (Or.inl ⟨rfl, LoopMatches.ret_roundtrip loop3⟩)⟩⟩
      · obtain ⟨i, _, bad⟩ := badRun wrap4 (by
          rw [newCheck, expEq, cmpEq]
          exact agree)
        refine ⟨_, _, _, bad, Or.inl ⟨rfl, Or.inr ?_⟩⟩
        refine ⟨zs, { chkS s (l.out_ - l.left) v with mode := BAD }, st, setI_istates_same _ _ _, rfl,
          retOk1, ⟨c1, c2, c3, c4, c5, show BAD ≠ SYNC by decide⟩, haveLe1, inLen1, ?_⟩
        intro source decoded valid _
        exact trailer_reject parsed1 bitsField (fun pre => agree (iff.mpr pre)) valid
  · -- the input ran out
    subst leaveResult
    obtain ⟨_, _, _, leaveRun'⟩ := leaveRun rfl
    exact ⟨_, _, _, leaveRun', Or.inr ⟨rfl, Or.inl (loopAt (by
      have below := (leaveFacts rfl).2
      have n32 : (32 : UInt32).toNat = 32 := rfl
      rw [n32] at below
      omega))⟩⟩

#print axioms check_step

end Zlib.Inflate.Proofs.MeaningCheck
