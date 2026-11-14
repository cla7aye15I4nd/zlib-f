import ZlibF.Proof.«gzwrite.c.flush-params»

/-!
# gzwrite.c: the runs inside `gzvprintf`

The pieces of `gzvprintf` that are not calls of a proved callee:

1. `gz_vacate_inv_run`: the first `gz_vacate` of `gzvprintf`, on a record in `GzInv`, returns 0 and changes nothing
   (W4 puts the pending input in the first half of `in`). The proof is that of `gz_vacate_safe_of`.
2. `PrintfArgs.at`: the format and the `%s` strings read the same on every later heap of the call. The argument
   domain (`GzArguments`) puts the format and every `%s` string apart from the blocks the handle owns, so a step that
   changes only owned blocks and keeps the `strerror` borrow keeps their bytes (`bytes_of_post`). The formatter is
   monotone in its string resolver (`formatGo_mono`): a string that resolved before resolves to the same bytes after.
3. `vsnprintf_in`: `vsnprintf` into the `in` buffer at `in + o`, with room `size` (`o + size ≤ 2·size`, W3). On the
   oracle's success it stores the first `size - 1` bytes of the output and a NUL; on its failure, junk and a NUL. Both
   write only the `in` buffer, which is a data buffer of the handle: `GzInv` holds after.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section printfRun
variable {i : Nat}

/-! ## The first `gz_vacate` -/

/-- **`gz_vacate` on a record in `GzInv`** returns 0 and changes nothing. -/
theorem gz_vacate_inv_run {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s) (hm : s.mode = GZ_WRITE)
    (hsz : s.size ≠ 0) : Zlib.Gzwrite.gz_vacate (gzSt i) fs h = .ok ((0, fs), h) := by
  have hs := inv.common.record
  have w := inv.writer hm
  have hZ : ldZ (strmOf (gzSt i)) h = .ok (s.strm, h) := Zlib.Gzlib.Proofs.ldZ_run hs
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run hs
  unfold Zlib.Gzwrite.gz_vacate
  rcases w.input with ⟨hn, -⟩ | ⟨-, a, ha, hle⟩
  · have hnull : (s.strm.next_in == .null) = true := by rw [hn]; rfl
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, ↓reduceIte]
  · obtain ⟨B, arr, hin, hB, -, hasz⟩ := (w.bufs hsz).1
    have hni : s.strm.next_in = .ref (.blk B) a := by rw [ha, hin]; simp [padv]
    have hnull : (Ptr.ref (BRef.blk B) a == (.null : BPtr)) = false := rfl
    have hg : Space.get h (BRef.blk B) = some arr := hB
    have h1 : Ptr.add (Ptr.ref (BRef.blk B) a) (s.strm.avail_in.toNat : Int) h =
        .ok (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat), h) :=
      Ptr.add_nat_ok (R := BRef) hg (by omega)
    have h2 : Ptr.add s.«in» (s.size.toNat : Int) h = .ok (Ptr.ref (BRef.blk B) s.size.toNat, h) := by
      rw [hin]
      have := Ptr.add_nat_ok (R := BRef) (h := h) (off := 0) (n := s.size.toNat) hg (by omega)
      rw [Nat.zero_add] at this
      exact this
    have h3 : Ptr.le (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) (Ptr.ref (BRef.blk B) s.size.toNat) h =
        .ok (true, h) := by
      have hlt : ¬ s.size.toNat < a + s.strm.avail_in.toNat := by omega
      have c1 : s.size.toNat ≤ arr.size ∧ a + s.strm.avail_in.toNat ≤ arr.size := ⟨by omega, by omega⟩
      have hlt' : Ptr.lt (Ptr.ref (BRef.blk B) s.size.toNat) (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) h =
          .ok (false, h) := by
        simp [Ptr.lt, hg, c1, hlt]
      simp only [Ptr.le, bind_app, hlt']
      rfl
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, Bool.false_eq_true, ↓reduceIte, hS, hni, h1, h2, h3]

/-! ## The strings of the call on later heaps -/

/-- What `strlenFrom` finds: the first NUL at or after `i`. -/
theorem strlenFrom_spec (a : Array UInt8) : ∀ (n j k : Nat), a.size - j ≤ n → strlenFrom a j = some k →
    j ≤ k ∧ k < a.size ∧ a[k]? = some 0 ∧ ∀ m, j ≤ m → m < k → a[m]? ≠ some 0 := by
  intro n
  induction n with
  | zero =>
    intro j k hn hk
    rw [strlenFrom] at hk
    have : ¬ j < a.size := by omega
    simp [this] at hk
  | succ n ih =>
    intro j k hn hk
    rw [strlenFrom] at hk
    by_cases hj : j < a.size
    · simp only [hj, dite_true] at hk
      by_cases hz : a[j] = 0
      · simp only [hz, beq_self_eq_true, ite_true, Option.some.injEq] at hk
        subst hk
        exact ⟨Nat.le_refl _, hj, by simp [hj, hz], fun m h1 h2 => absurd h2 (by omega)⟩
      · have hz' : (a[j] == 0) = false := by simpa using hz
        simp only [hz', Bool.false_eq_true, ite_false] at hk
        obtain ⟨h1, h2, h3, h4⟩ := ih (j + 1) k (by omega) hk
        refine ⟨by omega, h2, h3, fun m hm1 hm2 => ?_⟩
        by_cases e : m = j
        · subst e; simp [hj, hz]
        · exact h4 m (by omega) hm2
    · simp [hj] at hk

/-- **A string the heap resolver finds is a C string**, in a heap whose byte objects fit. -/
theorem cstring_of_heapStr {h : Heap} (fit : ZlibF.PlatformMemory.ByteObjectsFit h) {p : BPtr}
    {t : Array UInt8} (ht : heapStr h p = some t) : ∃ xs, CString h p xs ∧ t = xs.toArray := by
  unfold heapStr at ht
  cases hc : cstring p h with
  | error e => rw [hc] at ht; cases ht
  | ok res =>
    obtain ⟨t', h'⟩ := res
    rw [hc] at ht
    simp only [Option.some.injEq] at ht
    subst ht
    obtain ⟨n, h1, hl⟩ : ∃ n h1, strlenB p h = .ok (n, h1) := by
      cases e : strlenB p h with
      | error err =>
        have : cstring p h = .error err := by unfold cstring; simp [bind_app, e]
        rw [this] at hc; cases hc
      | ok r => exact ⟨r.1, r.2, rfl⟩
    cases p with
    | null => simp [strlenB] at hl
    | ref r off =>
      cases hg : Space.get h r with
      | none => simp [strlenB, hg] at hl
      | some a =>
        cases hk : strlenFrom a off with
        | none => simp [strlenB, hg, hk] at hl
        | some k =>
          obtain ⟨k1, k2, k3, k4⟩ := strlenFrom_spec a (a.size - off) off k (Nat.le_refl _) hk
          have hfit := fit r a hg
          unfold ZlibF.PlatformMemory.byteObjectLimit at hfit
          let xs := (a.toList.drop off).take (k - off)
          have hlen : xs.length = k - off := by
            simp only [xs, List.length_take, List.length_drop, Array.length_toList]; omega
          have hget : ∀ m, m < k - off → xs[m]? = a[off + m]? := by
            intro m hm
            simp only [xs, List.getElem?_take, hm, ite_true, List.getElem?_drop, Array.getElem?_toList]
          have hcs : CString h (.ref r off) xs := by
            refine ⟨Or.inr ⟨r, off, a, rfl, hg, by omega, ?_⟩, ?_, by omega⟩
            · rw [hlen, List.take_succ]
              congr 1
              rw [List.getElem?_drop, Array.getElem?_toList, Nat.add_sub_cancel' k1, k3]
              rfl
            · intro hm
              obtain ⟨m, hm1, hm2⟩ := List.getElem_of_mem hm
              have e1 := hget m (by omega)
              rw [List.getElem?_eq_getElem hm1, hm2] at e1
              exact k4 (off + m) (by omega) (by omega) e1.symm
          refine ⟨xs, hcs, ?_⟩
          rw [Zlib.GzFs.Proofs.cstring_of_CString hcs] at hc
          injection hc with hc
          injection hc with hc
          exact hc.symm

theorem argStr_mono {res res' : BPtr → Option (Array UInt8)} {p : BPtr} {t : Array UInt8}
    (hp : argStr res p = some t) (hr : ∀ u, res p = some u → res' p = some u) : argStr res' p = some t := by
  unfold argStr at hp ⊢
  by_cases hn : (p == Ptr.null) = true
  · rw [if_pos hn] at hp ⊢; exact hp
  · rw [if_neg hn] at hp ⊢; exact hr t hp

/-- **The formatter is monotone in its string resolver**: a run that succeeds with `res` succeeds with the same
output under every resolver that finds the same strings for the `%s` arguments `res` finds. -/
theorem formatGo_mono (f : Array UInt8) (res res' : BPtr → Option (Array UInt8)) :
    ∀ (fuel j : Nat) (args : List VaArg) (out y : Array UInt8),
      (∀ q, VaArg.str q ∈ args → ∀ u, res q = some u → res' q = some u) →
      formatGo f res fuel j args out = .ok y → formatGo f res' fuel j args out = .ok y := by
  intro fuel
  induction fuel with
  | zero => intro j args out y _ hy; simpa [formatGo] using hy
  | succ n ih =>
    intro j args out y hres hy
    have tl : ∀ (a : VaArg) (r : List VaArg), args = a :: r → ∀ q, VaArg.str q ∈ r → ∀ u, res q = some u →
        res' q = some u := fun a r e q hq => hres q (by rw [e]; exact List.mem_cons_of_mem _ hq)
    simp only [formatGo] at hy ⊢
    by_cases c1 : j < f.size
    case neg => simp only [c1, if_false] at hy ⊢; exact hy
    simp only [c1, if_true] at hy ⊢
    by_cases c2 : (f[j]! != 37) = true
    · simp only [c2, if_true] at hy ⊢
      exact ih _ _ _ _ hres hy
    simp only [c2, Bool.false_eq_true, if_false] at hy ⊢
    cases hp : parseSpec f (j + 1) with
    | none => simp only [hp] at hy; cases hy
    | some pr =>
      obtain ⟨sp, j2⟩ := pr
      simp only [hp] at hy ⊢
      by_cases d1 : (sp.conv == 37) = true
      · simp only [d1, if_true] at hy ⊢
        exact ih _ _ _ _ hres hy
      simp only [d1, Bool.false_eq_true, if_false] at hy ⊢
      by_cases d2 : (sp.conv == 99) = true
      · simp only [d2, if_true] at hy ⊢
        rcases args with _ | ⟨a, r⟩
        · cases hy
        · cases a with
          | int v => exact ih _ _ _ _ (tl _ r rfl) hy
          | _ => cases hy
      simp only [d2, Bool.false_eq_true, if_false] at hy ⊢
      by_cases d3 : (sp.conv == 115) = true
      · simp only [d3, if_true] at hy ⊢
        rcases args with _ | ⟨a, r⟩
        · cases hy
        · cases a with
          | str p =>
            simp only at hy ⊢
            cases ha : argStr res p with
            | none => simp only [ha] at hy; cases hy
            | some t =>
              have ha' := argStr_mono ha (hres p (List.mem_cons_self ..))
              simp only [ha] at hy
              simp only [ha']
              exact ih _ _ _ _ (tl _ r rfl) hy
          | _ => cases hy
      simp only [d3, Bool.false_eq_true, if_false] at hy ⊢
      by_cases d4 : (sp.conv == 100 || sp.conv == 105) = true
      · simp only [d4, if_true] at hy ⊢
        cases hl : sp.long <;> rcases args with _ | ⟨a, r⟩ <;> simp only [hl] at hy ⊢ <;>
          first
          | cases hy
          | (cases a <;> first | cases hy | exact ih _ _ _ _ (tl _ r rfl) hy)
      simp only [d4, Bool.false_eq_true, if_false] at hy ⊢
      by_cases d5 : (sp.conv == 117 || sp.conv == 120 || sp.conv == 88 || sp.conv == 111) = true
      · simp only [d5, if_true] at hy ⊢
        cases hl : sp.long <;> rcases args with _ | ⟨a, r⟩ <;> simp only [hl] at hy ⊢ <;>
          first
          | cases hy
          | (cases a <;> first | cases hy | exact ih _ _ _ _ (tl _ r rfl) hy)
      simp only [d5, Bool.false_eq_true, if_false] at hy
      cases hy

/-- The format and the `%s` strings of a `gzprintf` call, on the heap `h0` of the call: the argument domain
(`GzArguments`) and the fit of the byte objects. -/
def PrintfArgs (h0 : Heap) (i : Nat) (s0 : GzState) (format : BPtr) (va : List VaArg) : Prop :=
  ZlibF.PlatformMemory.ByteObjectsFit h0 ∧ (∃ xs, Formatted h0 format va xs) ∧
    (∀ b, ByteRoot format b → ¬ GzOwned h0 i s0 b) ∧
    ∀ q, VaArg.str q ∈ va → ∀ b, ByteRoot q b → ¬ GzOwned h0 i s0 b

/-- **The strings of the call read the same on a later heap** of the call that keeps the `strerror` borrow. -/
theorem PrintfArgs.at {h0 H : Heap} {s0 : GzState} {fs : Fs} {P : Heap → Nat → GzState → Prop} {format : BPtr}
    {va : List VaArg} (A : PrintfArgs h0 i s0 format va) (post : GzPost h0 i s0 [] fs H P)
    (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) :
    ∃ (fmt xs : List UInt8), CString H format fmt ∧ formatGo fmt.toArray (heapStr H) (fmt.length + 1) 0 va #[] = .ok xs.toArray := by
  obtain ⟨fit, ⟨xs, fmt, hc, hx⟩, nof, noa⟩ := A
  refine ⟨fmt, xs, ⟨bytes_of_post hc.1 nof post hbor, hc.2⟩, ?_⟩
  refine formatGo_mono _ _ _ _ _ _ _ _ (fun q hq u hu => ?_) hx
  obtain ⟨ys, hcs, rfl⟩ := cstring_of_heapStr fit hu
  exact Zlib.GzFs.Proofs.heapStr_of_CString ⟨bytes_of_post hcs.1 (noa q hq) post hbor, hcs.2⟩

/-! ## `vsnprintf` into the `in` buffer -/

/-- **`storeBytes` into the `in` buffer** keeps `GzInv` and writes only that buffer. -/
theorem in_storeBytes {H : Heap} {v : GzState} {fs : Fs} (inv : GzInv H i v) (hsz : v.size ≠ 0) {B : Nat}
    {arr : Array UInt8} (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr) (hro : H.ro B = false)
    {o : Nat} (bs : Array UInt8) (hfit : o + bs.size ≤ arr.size) (hfs : FileSystem fs) :
    ∃ H2 arr2, storeBytes (.ref (.blk B) o) bs H = .ok ((), H2) ∧ H2.bytes B = some arr2 ∧ arr2.size = arr.size ∧
      H2.ro B = false ∧ GzInv H2 i v ∧ GzPost H i v [] fs H2 GzInv := by
  by_cases hne : bs.isEmpty = true
  · refine ⟨H, arr, by unfold storeBytes; simp [hne], hB, rfl, hro, inv, (GetcUngetc.Eff.refl inv hfs).2⟩
  have hne' : bs.isEmpty = false := by simpa using hne
  obtain ⟨H2, run, st⟩ := GzRead.storeBytes_view H (BRef.blk B) o arr bs hB hro hfit
    (Fresh.slotUsed_next inv.common.fresh) hne'
  have hdB : GzRead.DataBuf v B := ⟨hsz, Or.inl hin⟩
  have hx : (copyRange arr bs o 0 bs.size).size = arr.size := size_copyRange _ _ _ _ _
  obtain ⟨inv2, hl2, ho2⟩ := GzRead.GzInv.stored inv st hB hx (Or.inl ⟨B, rfl, hdB⟩)
  have Bl : H.live B := inv.common.live B hdB.owned
  have hBn : B ≠ H.nextBlk := fun e => inv.common.fresh B (by omega) Bl
  have fr : Frame H H2 (GzOwned H i v) := by
    refine ⟨st.static.symm, st.allocOk.symm, st.garbage.symm, by rw [st.nextBlk]; omega,
      by rw [st.nalloc]; exact Nat.le_refl _, fun b hl hn => ?_⟩
    have hbB : b ≠ B := fun e => hn (e ▸ hdB.owned)
    have hbn : b ≠ H.nextBlk := fun e => inv.common.fresh b (by omega) hl
    exact ⟨st.bytes b (fun e => hbB (BRef.blk.inj e).symm), by rw [st.words], by rw [st.streams],
      by rw [st.gzheaders], st.dstates b (fun e => by cases e), by rw [st.istates], by rw [st.gzstates], st.ro b hbn⟩
  exact ⟨H2, _, run, st.view, hx, by rw [st.ro B hBn]; exact hro, inv2,
    post_frame inv.common.live hfs fr hl2 ho2 rfl rfl inv2⟩

/-- **A NUL into the `in` buffer** keeps `GzInv`. -/
theorem in_store0 {H : Heap} {v : GzState} {fs : Fs} (inv : GzInv H i v) (hw : v.mode = GZ_WRITE)
    (hsz : v.size ≠ 0) {B : Nat} {arr : Array UInt8} (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr)
    (hro : H.ro B = false) {n : Nat} (hn : n < arr.size) (hfs : FileSystem fs) :
    store8 (.ref (.blk B) n) 0 H = .ok ((), Space.put H (BRef.blk B) (arr.set! n 0)) ∧
      GzInv (Space.put H (BRef.blk B) (arr.set! n 0)) i v ∧
      GzPost H i v [] fs (Space.put H (BRef.blk B) (arr.set! n 0)) GzInv ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).bytes B = some (arr.set! n 0) ∧ (arr.set! n 0).size = arr.size ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).ro B = false ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).libcErrorBorrow = H.libcErrorBorrow ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).gzstates = H.gzstates := by
  have hg : Space.get H (BRef.blk B) = some arr := hB
  have hro' : Space.ro H (BRef.blk B) = false := hro
  obtain ⟨inv', ho, fr, hl⟩ := inv_in_put inv hw hsz hin hB hro (arr := arr.set! n 0) (by simp)
  refine ⟨Ptr.store_ok hg hro' hn, inv', post_frame inv.common.live hfs fr hl ho rfl rfl inv', ?_, by simp,
    hro, rfl, rfl⟩
  show upd H.bytes B (some (arr.set! n 0)) B = some (arr.set! n 0)
  exact upd_same _ _ _

/-- `vsnprintf` after its oracle call count. -/
theorem vsnprintf_app (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) (fs : Fs) (h : Heap) :
    vsnprintf dst size fmt args fs h = (do
      let f ← cstring fmt
      let out ← formatBytes f args
      if fs.printfOk fs.nprintf && out.size ≤ 2147483647 then
        snprintf dst size fmt args
      else
        let e := fs.printfErrno fs.nprintf
        setErrno (if out.size > 2147483647 || e == 0 then EOVERFLOW else e)
        if size != 0 then
          let junk := (fs.printfJunk fs.nprintf).extract 0 (size.toNat - 1)
          storeBytes dst junk
          let q ← dst.add junk.size
          store8 q 0
        return -1 : G Int32) { fs with nprintf := fs.nprintf + 1 } h := rfl

/-- **`vsnprintf` into the `in` buffer**, at `in + o` with room `size` (`o + size ≤ 2·size`), with a format that
formats on the heap: it returns, keeps `GzInv` and the size of `in`, and changes only `in`. -/
theorem vsnprintf_in {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    {B : Nat} {arr : Array UInt8} (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr)
    (hasz : arr.size = 2 * v.size.toNat) {o : Nat} (ho : o ≤ v.size.toNat)
    {format : BPtr} {va : List VaArg} {fmt xs : List UInt8} (hc : CString H format fmt)
    (hx : formatGo fmt.toArray (heapStr H) (fmt.length + 1) 0 va #[] = .ok xs.toArray) :
    ∃ len fs' H', vsnprintf (.ref (.blk B) o) v.size.toUInt64 format va fs H = .ok ((len, fs'), H') ∧
      GetcUngetc.Eff i h0 s0 fs0 fs' H' ∧ GzInv H' i v ∧ ∃ arr', H'.bytes B = some arr' ∧ arr'.size = arr.size := by
  have hfs : FileSystem fs := E.2.1
  have hro : H.ro B = false := by
    obtain ⟨B', a', hin', hB', hro', -⟩ := ((inv.writer hw).bufs hsz).1
    rw [hin] at hin'
    cases hin'
    exact hro'
  have hf : cstring format H = .ok (fmt.toArray, H) := Zlib.GzFs.Proofs.cstring_of_CString hc
  have hfb : formatBytes fmt.toArray va H = .ok (xs.toArray, H) := by
    simp only [formatBytes, List.size_toArray, hx]
  have hS32 := v.size.toNat_lt
  have hsn64 : v.size.toUInt64.toNat = v.size.toNat := UInt32.toNat_toUInt64 _
  have hpos : 0 < v.size.toNat := by
    rcases Nat.eq_zero_or_pos v.size.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hsz
    · exact e
  have hsn : (v.size.toUInt64 != 0) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro e
    have := congrArg UInt64.toNat e
    rw [hsn64] at this
    simp at this
    omega
  rw [vsnprintf_app]
  by_cases hok : (fs.printfOk fs.nprintf && decide (xs.toArray.size ≤ 2147483647)) = true
  · -- the oracle succeeds: the output, cut to `size - 1` bytes, and a NUL
    obtain ⟨k, hk⟩ : ∃ k, k = min xs.toArray.size (v.size.toUInt64.toNat - 1) := ⟨_, rfl⟩
    have hkle : k ≤ v.size.toNat - 1 := by rw [hk, hsn64]; exact Nat.min_le_right _ _
    have hks : (xs.toArray.extract 0 k).size = k := by
      simp only [Array.size_extract]; rw [hk]; omega
    obtain ⟨H2, arr2, run2, hB2, hsz2, hro2, inv2, P2⟩ :=
      in_storeBytes (fs := { fs with nprintf := fs.nprintf + 1 }) inv hsz hin hB hro (o := o)
        (xs.toArray.extract 0 k) (by rw [hks]; omega) hfs
    have hadd : Ptr.add (Ptr.ref (BRef.blk B) o) (k : Int) H2 = .ok (.ref (.blk B) (o + k), H2) :=
      Ptr.add_nat_ok (R := BRef) (show Space.get H2 (BRef.blk B) = some arr2 from hB2) (by omega)
    obtain ⟨run3, inv3, P3, hB3, hsz3, -⟩ := in_store0 (fs := { fs with nprintf := fs.nprintf + 1 }) inv2 hw hsz hin
      hB2 hro2 (n := o + k) (by omega) hfs
    have hsnp : snprintf (.ref (.blk B) o) v.size.toUInt64 format va H =
        .ok ((if xs.toArray.size > 2147483647 then -1 else Int32.ofNat xs.toArray.size),
          Space.put H2 (BRef.blk B) (arr2.set! (o + k) 0)) := by
      unfold snprintf
      simp only [bind_app, hf, hfb, hsn, ite_true, ← hk, run2, hadd, run3, pure_app]
    refine ⟨(if xs.toArray.size > 2147483647 then -1 else Int32.ofNat xs.toArray.size),
      { fs with nprintf := fs.nprintf + 1 }, Space.put H2 (BRef.blk B) (arr2.set! (o + k) 0), ?_, GetcUngetc.Eff.trans (GetcUngetc.Eff.trans E inv P2 (fun _ => Iff.rfl)) inv2 P3
      (fun _ => Iff.rfl), inv3, _, hB3, by rw [hsz3, hsz2]⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hf,
      hfb, hok, ↓reduceIte, hsnp]
  · -- the oracle fails: junk and a NUL
    have hok' : (fs.printfOk fs.nprintf && decide (xs.toArray.size ≤ 2147483647)) = false := by simpa using hok
    obtain ⟨junk, hj⟩ : ∃ junk, junk = (fs.printfJunk fs.nprintf).extract 0 (v.size.toUInt64.toNat - 1) := ⟨_, rfl⟩
    have hjs : junk.size ≤ v.size.toNat - 1 := by
      rw [hj, Array.size_extract, hsn64]; omega
    obtain ⟨e, he⟩ : ∃ e : Int32, e = (if xs.toArray.size > 2147483647 || fs.printfErrno fs.nprintf == 0 then EOVERFLOW
        else fs.printfErrno fs.nprintf) := ⟨_, rfl⟩
    obtain ⟨fs2, hfs2⟩ : ∃ fs2 : Fs, fs2 = { { fs with nprintf := fs.nprintf + 1 } with errno := e } := ⟨_, rfl⟩
    have hfsok : FileSystem fs2 := by rw [hfs2]; exact hfs
    obtain ⟨H2, arr2, run2, hB2, hsz2, hro2, inv2, P2⟩ :=
      in_storeBytes (fs := fs2) inv hsz hin hB hro (o := o) junk (by omega) hfsok
    have hadd : Ptr.add (Ptr.ref (BRef.blk B) o) (junk.size : Int) H2 = .ok (.ref (.blk B) (o + junk.size), H2) :=
      Ptr.add_nat_ok (R := BRef) (show Space.get H2 (BRef.blk B) = some arr2 from hB2) (by omega)
    obtain ⟨run3, inv3, P3, hB3, hsz3, -⟩ := in_store0 (fs := fs2) inv2 hw hsz hin hB2 hro2 (n := o + junk.size)
      (by omega) hfsok
    have hset : setErrno e { fs with nprintf := fs.nprintf + 1 } H = .ok (((), fs2), H) := by rw [hfs2]; rfl
    refine ⟨-1, fs2, Space.put H2 (BRef.blk B) (arr2.set! (o + junk.size) 0), ?_,
      GetcUngetc.Eff.trans (GetcUngetc.Eff.trans E inv P2 (by rw [hfs2]; exact fun _ => Iff.rfl)) inv2 P3
      (fun _ => Iff.rfl), inv3, _, hB3, by rw [hsz3, hsz2]⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hf,
      hfb, hok', Bool.false_eq_true, ↓reduceIte, ← he, hsn, ← hj, hset, run2, hadd, run3]

end printfRun

end ZlibF.Spec.Public.GzSkeleton
