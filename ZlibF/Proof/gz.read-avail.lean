import ZlibF.Proof.«gz.read-load-error»

/-!
# gz read side: `gz_avail` is safe

`gz_avail(state)` refills the input buffer `in`. With a serious error it returns `-1`, at the end of the input `0`.
Otherwise it moves the pending input to the start of `in` (a byte copy that every caller makes dead, since they have
`next_in == in` or `avail_in == 0`; it is proved anyway), loads `size - avail_in` more bytes behind it with
`gz_load`, and sets the input window to the start of `in`.

1. `copy_loop`: the byte copy stays inside `in` and changes only its bytes.
2. `gz_load_safe` loads into the rest of `in`.
3. `GzInv.set_input`: the new input window keeps the invariant (the codec history allows a caller to change
   `next_in` and `avail_in`).
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The compaction copy -/

/-- The body of the copy loop of `gz_avail`: `*p++ = *q++`. -/
def copyBody (st : BPtr × BPtr × UInt32) : M (BPtr × BPtr × UInt32) := do
  let b ← load8 st.2.fst
  store8 st.fst b
  let p ← Ptr.add st.fst 1
  let q ← Ptr.add st.2.fst 1
  pure (p, q, st.2.snd)

/-- The condition of the copy loop: `--n`. -/
def copyCond (st : BPtr × BPtr × UInt32) : M (Bool × (BPtr × BPtr × UInt32)) :=
  pure (st.2.snd - 1 != 0, st.fst, st.2.fst, st.2.snd - 1)

theorem add_one_ok {h : Heap} {b : Nat} {a : Array UInt8} (hg : h.bytes b = some a) {off : Nat}
    (hle : off + 1 ≤ a.size) : Ptr.add (Ptr.ref (BRef.blk b) off) (1 : Int) h = .ok (Ptr.ref (BRef.blk b) (off + 1), h) := by
  have := Ptr.add_ok (h := h) (r := BRef.blk b) (a := a) (off := off) (k := 1) hg (by omega) (by omega)
  have e : ((off : Int) + 1).toNat = off + 1 := by omega
  rw [e] at this
  exact this

/-- **The copy loop**: from `p = in + k` and `q = in + a + k` with `m ≥ 1` bytes left, all inside the block, the
loop returns and only the bytes of the block change, keeping its size. -/
theorem copy_loop (b : Nat) (a : Nat) :
    ∀ (m k : Nat) (n : UInt32) (Z : Heap) (arr : Array UInt8) (F : Nat),
      Z.bytes b = some arr → Z.ro b = false → n.toNat = m → 1 ≤ m → a + k + m ≤ arr.size → m ≤ F →
      ∃ st arr', cdoWhile.go copyBody copyCond F (Ptr.ref (BRef.blk b) k, Ptr.ref (BRef.blk b) (a + k), n) Z =
        .ok (st, { Z with bytes := upd Z.bytes b (some arr') }) ∧ arr'.size = arr.size := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ _ _ _ _ h1; omega
  | succ m ih =>
    intro k n Z arr F hb hro hn h1 hfit hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have hk : k < arr.size := by omega
    have hak : a + k < arr.size := by omega
    let v := arr[a + k]
    let arr1 := arr.set! k v
    let Z1 : Heap := { Z with bytes := upd Z.bytes b (some arr1) }
    have hsz1 : arr1.size = arr.size := by simp [arr1]
    have hb1 : Z1.bytes b = some arr1 := by simp [Z1]
    have hload : load8 (Ptr.ref (BRef.blk b) (a + k)) Z = .ok (v, Z) := Ptr.load_ok (h := Z) hb hak
    have hstore : store8 (Ptr.ref (BRef.blk b) k) v Z = .ok ((), Z1) := by
      have := Ptr.store_ok (h := Z) (r := BRef.blk b) (off := k) (v := v) hb hro hk
      exact this
    have hp : Ptr.add (Ptr.ref (BRef.blk b) k) (1 : Int) Z1 = .ok (Ptr.ref (BRef.blk b) (k + 1), Z1) :=
      add_one_ok hb1 (by omega)
    have hq : Ptr.add (Ptr.ref (BRef.blk b) (a + k)) (1 : Int) Z1 = .ok (Ptr.ref (BRef.blk b) (a + k + 1), Z1) :=
      add_one_ok hb1 (by omega)
    have hbody : copyBody (Ptr.ref (BRef.blk b) k, Ptr.ref (BRef.blk b) (a + k), n) Z =
        .ok ((Ptr.ref (BRef.blk b) (k + 1), Ptr.ref (BRef.blk b) (a + k + 1), n), Z1) := by
      simp only [copyBody, bind_app, hload, hstore, hp, hq, pure_app]
    have hcond : copyCond (Ptr.ref (BRef.blk b) (k + 1), Ptr.ref (BRef.blk b) (a + k + 1), n) Z1 =
        .ok ((n - 1 != 0, (Ptr.ref (BRef.blk b) (k + 1), Ptr.ref (BRef.blk b) (a + k + 1), n - 1)), Z1) := rfl
    have hgo : cdoWhile.go copyBody copyCond (F' + 1) (Ptr.ref (BRef.blk b) k, Ptr.ref (BRef.blk b) (a + k), n) Z =
        (if (n - 1 != 0) = true then
          cdoWhile.go copyBody copyCond F' (Ptr.ref (BRef.blk b) (k + 1), Ptr.ref (BRef.blk b) (a + k + 1), n - 1) Z1
        else .ok ((Ptr.ref (BRef.blk b) (k + 1), Ptr.ref (BRef.blk b) (a + k + 1), n - 1), Z1)) := by
      simp only [cdoWhile.go, bind_app, hbody, hcond]
      split <;> rfl
    rw [hgo]
    by_cases hm : m = 0
    · subst hm
      have hn1 : (n - 1 != 0) = false := by
        have : n = 1 := UInt32.toNat_inj.mp (by rw [hn]; rfl)
        subst this; decide
      rw [hn1]
      exact ⟨(Ptr.ref (BRef.blk b) (k + 1), Ptr.ref (BRef.blk b) (a + k + 1), n - 1), arr1, rfl, hsz1⟩
    · have hn1 : (n - 1 != 0) = true := by
        have : (n - 1).toNat = m := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp; omega
        simp only [bne_iff_ne, ne_eq]
        intro e; rw [e] at this; simp at this; omega
      rw [if_pos hn1]
      have hn' : (n - 1).toNat = m := by
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp; omega
      obtain ⟨st, arr', run, hsz'⟩ := ih (k + 1) (n - 1) Z1 arr1 F' hb1 (by simp [Z1]; exact hro) hn' (by omega)
        (by rw [hsz1]; omega) (by omega)
      have e : a + (k + 1) = a + k + 1 := by omega
      rw [e] at run
      refine ⟨st, arr', ?_, hsz'.trans hsz1⟩
      rw [run]
      simp [Z1, upd_upd]

#print axioms copy_loop

/-! ## The input window -/

/-- **Setting the input window to the start of `in`** (`next_in = in`, `avail_in = n ≤ size`) keeps `GzInv`. -/
theorem GzInv.set_input {h : Heap} {i : Nat} {s : GzState} (inv : GzInv h i s) (hm0 : s.mode = GZ_READ)
    (hz0 : s.size ≠ 0) (n : UInt32) (hn : n.toNat ≤ s.size.toNat) (hae : s.again ≠ 0 → s.eof ≠ 0 → n = 0) :
    GzInv (putGz h i { s with strm := { s.strm with avail_in := n, next_in := s.«in» } }) i
      { s with strm := { s.strm with avail_in := n, next_in := s.«in» } } ∧
    (∀ b, GzOwned (putGz h i { s with strm := { s.strm with avail_in := n, next_in := s.«in» } }) i
      { s with strm := { s.strm with avail_in := n, next_in := s.«in» } } b ↔ GzOwned h i s b) := by
  have c := inv.common
  have hs := c.record
  have gH : ZStreamRef.get (putGz h i { s with strm := { s.strm with avail_in := n, next_in := s.«in» } }) (gzStrm i) =
      some { s.strm with avail_in := n, next_in := s.«in» } := by
    simp [ZStreamRef.get, gzStrm, putGz]
  have gh : ZStreamRef.get h (gzStrm i) = some s.strm := by simp [ZStreamRef.get, gzStrm, hs]
  have hso : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_in := n, next_in := s.«in» } }) (gzStrm i) b ↔
      StreamOwned h (gzStrm i) b := by
    intro b
    unfold StreamOwned
    rw [gH, gh]
    simp only [Option.some.injEq, exists_eq_left']
    try rfl
  have hso' : ∀ b, StreamOwned (putGz h i { s with strm := { s.strm with avail_in := n, next_in := s.«in» } })
      (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := hso
  have hown : ∀ b, GzOwned (putGz h i { s with strm := { s.strm with avail_in := n, next_in := s.«in» } }) i
      { s with strm := { s.strm with avail_in := n, next_in := s.«in» } } b ↔ GzOwned h i s b := by
    intro b
    unfold GzOwned
    dsimp only
    rw [hso']
  have hreb : Rebuffer h (putGz h i { s with strm := { s.strm with avail_in := n, next_in := s.«in» } }) (gzStrm i) := by
    refine ⟨putGz_fresh hs c.fresh, putGz_uniq hs c.uniq, c.globals, ?_, s.strm,
      { s.strm with avail_in := n, next_in := s.«in» }, gh, gH, rfl⟩
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := by
      intro e
      subst e
      exact hb c.recordFree
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  have fitH := putGz_fit (s' := { s with strm := { s.strm with avail_in := n, next_in := s.«in» } }) (i := i) c.fit
  refine ⟨⟨?_, ?_, ?_⟩, hown⟩
  · exact {
      record := by simp [putGz]
      mode := c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := fitH
      path := by
        obtain ⟨p, hp, hm⟩ := c.path
        exact ⟨p, (putGz_cstring _ _).2 hp, hm⟩
      msg := by
        rcases c.msg with hn | ⟨m, hm, hb⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, (putGz_cstring _ _).2 hm, hb⟩
      memerr := c.memerr
      want := c.want
      size := c.size
      distinct := ⟨c.distinct.1, fun p hp b hb =>
        ⟨(c.distinct.2 p hp b hb).1, by rw [hso]; exact (c.distinct.2 p hp b hb).2⟩⟩
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := c.pos
      next := fun hh => by
        obtain ⟨b, off, a, hx, hbi, ho, hmb, hb, hle⟩ := c.next hh
        exact ⟨b, off, a, hx, hbi, (hown b).2 ho, hmb, hb, hle⟩
      nullHave := c.nullHave
      recordFree := by rw [hso]; exact c.recordFree }
  · intro hm
    have r := inv.reader hm
    exact {
      how := r.how
      copyDirect := r.copyDirect
      gzipDirect := r.gzipDirect
      direct := r.direct
      junk := r.junk
      flags := r.flags
      unalloc := fun hz => absurd hz hz0
      bufs := r.bufs
      input := by
        obtain ⟨bb, a, hin, _⟩ := (r.bufs hz0).1
        refine Or.inr ⟨0, ?_, by simpa using hn⟩
        show s.«in» = padv s.«in» 0
        rw [hin]; rfl
      output := r.output
      codec := fun hz => by
        obtain ⟨reach, z, k, st, hzget, hzst, hk, hhead⟩ := r.codec hz
        have hz' : z = s.strm := by rw [gh] at hzget; exact (Option.some.inj hzget).symm
        subst hz'
        exact ⟨StreamReachable.rebuffer reach hreb (fun _ => fitH), _, k, st, gH, hzst, hk, hhead⟩
      posHave := r.posHave
      againSize := r.againSize
      haveSkip := r.haveSkip
      againEof := hae }
  · intro hm
    exact absurd (hm0.symm.trans hm) (by decide)


/-! ## The pieces of `gz_avail` -/

/-- The tail of `gz_avail` after the copy: load behind the pending input, then set the window. -/
def availLoad (i : Nat) : G Int32 := do
  let s ← StateT.lift (ldS (some (.tab i)))
  let z ← StateT.lift (ldZ (strmOf (some (.tab i))))
  let p ← StateT.lift (Ptr.add s.«in» ↑z.avail_in.toNat)
  let x ← Zlib.Gzread.gz_load (some (.tab i)) p (s.size - z.avail_in)
  if (x.fst == -1) = true then pure (-1)
  else do
    let s ← StateT.lift (ldS (some (.tab i)))
    StateT.lift (updZ (strmOf (some (.tab i))) fun z => { z with next_in := s.«in», avail_in := z.avail_in + x.snd })
    pure 0

theorem gz_avail_source (i : Nat) : Zlib.Gzread.gz_avail (gzSt i) = (do
    let s ← StateT.lift (ldS (some (.tab i)))
    if (s.err != Z_OK && s.err != Z_BUF_ERROR) = true then pure (-1)
    else if (s.eof == 0) = true then do
      let z ← StateT.lift (ldZ (strmOf (some (.tab i))))
      if (z.avail_in != 0) = true then
        if (z.next_in != s.«in») = true then do
          let _ ← StateT.lift (cdoWhile copyBody copyCond (s.«in», z.next_in, z.avail_in))
          availLoad i
        else availLoad i
      else availLoad i
    else pure 0) := rfl

#print axioms gz_avail_source

/-! ## The copy keeps the invariant -/

/-- **The compaction copy** returns, keeps the invariant up to the buffered output, and changes only the bytes of
`in`. -/
theorem copy_run {h : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ)
    (hsz : s.size ≠ 0) (hav : s.strm.avail_in ≠ 0) :
    ∃ st Z, cdoWhile copyBody copyCond (s.«in», s.strm.next_in, s.strm.avail_in) h = .ok (st, Z) ∧
      GzInvUpToOutput Z i s ∧ (∀ b, Z.live b ↔ h.live b) ∧ (∀ b, GzOwned Z i s b ↔ GzOwned h i s b) ∧
      Frame h Z (GzOwned h i s) ∧ Z.gzstates = h.gzstates ∧ Z.nextBlk = h.nextBlk ∧
      (∀ b c, s.«in» = .ref (.blk c) 0 → b ≠ c → Z.bytes b = h.bytes b) ∧ Z.istates = h.istates := by
  have inv : GzInv (putGz h i (clearOut s)) i (clearOut s) := hu.2
  have rd := inv.reader hm
  obtain ⟨inb, arr, hin, hb, hro, hsize⟩ := (rd.bufs hsz).1
  have hb0 : h.bytes inb = some arr := hb
  have hro0 : h.ro inb = false := hro
  have hin' : s.«in» = .ref (.blk inb) 0 := hin
  have hsize' : arr.size = s.size.toNat := hsize
  obtain ⟨a, hq, hfit⟩ : ∃ a, s.strm.next_in = .ref (.blk inb) a ∧ a + s.strm.avail_in.toNat ≤ s.size.toNat := by
    rcases rd.input with hz | ⟨a, hq, hle⟩
    · exact absurd hz hav
    · refine ⟨a, ?_, hle⟩
      have hq' : s.strm.next_in = padv s.«in» a := hq
      rw [hq', hin']
      simp [padv]
  have hm1 : 1 ≤ s.strm.avail_in.toNat := by
    have : s.strm.avail_in.toNat ≠ 0 := fun e => hav (UInt32.toNat_inj.mp (by rw [e]; rfl))
    omega
  obtain ⟨st, arr', run, hsz'⟩ := copy_loop inb a s.strm.avail_in.toNat 0 s.strm.avail_in h arr fuel hb0 hro0 rfl
    hm1 (by omega) (by have := s.strm.avail_in.toNat_lt; unfold fuel; omega)
  let Z : Heap := { h with bytes := upd h.bytes inb (some arr') }
  have hlive : ∀ b, Z.live b ↔ h.live b := by
    intro b
    have e : (Z.bytes b ≠ none) ↔ (h.bytes b ≠ none) := by
      show upd h.bytes inb (some arr') b ≠ none ↔ h.bytes b ≠ none
      rw [upd_apply]
      by_cases hb : b = inb
      · subst hb; simp [hb0]
      · simp [hb]
    unfold Heap.live
    rw [e]
  have hcnt : ∀ b, cnt (Z.bytes b) = cnt (h.bytes b) := by
    intro b
    show cnt (upd h.bytes inb (some arr') b) = _
    rw [upd_apply]
    by_cases e : b = inb
    · subst e; simp [hb0]
    · simp [e]
  have isData : DataBuf (clearOut s) inb := ⟨hsz, Or.inl hin⟩
  have fr : Frame (putGz h i (clearOut s)) (putGz Z i (clearOut s))
      (fun b => ¬ GzOwned (putGz h i (clearOut s)) i (clearOut s) b ∨ DataBuf (clearOut s) b) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hb => ?_⟩
    have hne : b ≠ inb := fun e => hb (Or.inr (e ▸ isData))
    exact ⟨upd_ne _ _ _ _ hne, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdata : ∀ b, DataBuf (clearOut s) b →
      (∃ x x', (putGz h i (clearOut s)).bytes b = some x ∧ (putGz Z i (clearOut s)).bytes b = some x' ∧
        x'.size = x.size) ∧
      (putGz Z i (clearOut s)).ro b = (putGz h i (clearOut s)).ro b ∧
      (putGz Z i (clearOut s)).words b = (putGz h i (clearOut s)).words b ∧
      (putGz Z i (clearOut s)).streams b = (putGz h i (clearOut s)).streams b ∧
      (putGz Z i (clearOut s)).gzheaders b = (putGz h i (clearOut s)).gzheaders b ∧
      (putGz Z i (clearOut s)).dstates b = (putGz h i (clearOut s)).dstates b ∧
      (putGz Z i (clearOut s)).istates b = (putGz h i (clearOut s)).istates b ∧
      (putGz Z i (clearOut s)).gzstates b = (putGz h i (clearOut s)).gzstates b := by
    intro b hd
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    by_cases e : b = inb
    · subst e
      exact ⟨arr, arr', hb, by show upd h.bytes b (some arr') b = _; simp, hsz'⟩
    · have hsome : ∃ x, h.bytes b = some x := by
        obtain ⟨hz, hio⟩ := hd
        rcases hio with hi | ⟨_, ho⟩
        · rw [hin] at hi; cases hi; exact absurd rfl e
        · obtain ⟨ob, oa, hout, hob, _, _⟩ := (rd.bufs hsz).2
          rw [hout] at ho; cases ho
          exact ⟨oa, hob⟩
      obtain ⟨x, hx⟩ := hsome
      exact ⟨x, x, hx, by show upd h.bytes inb (some arr') b = _; rw [upd_ne _ _ _ _ e]; exact hx, rfl⟩
  have hsZ : Z.gzstates i = some s := hu.1
  have freshZ : Fresh (putGz Z i (clearOut s)) := fun b hb hl =>
    inv.common.fresh b hb ((putGz_live hu.1 b).2 ((hlive b).1 ((putGz_live hsZ b).1 hl)))
  have uniqZ : Zlib.Gzlib.Spec.Uniq (putGz Z i (clearOut s)) := by
    intro b
    have u := inv.common.uniq b
    have e : cnt ((putGz Z i (clearOut s)).bytes b) = cnt ((putGz h i (clearOut s)).bytes b) := hcnt b
    rw [e]
    exact u
  have fitZ : ZlibF.PlatformMemory.ByteObjectsFit (putGz Z i (clearOut s)) := by
    have f0 : ZlibF.PlatformMemory.ByteObjectsFit h := fun r x g => inv.common.fit r x (by rw [putGz_space]; exact g)
    have bound : arr'.size < ZlibF.PlatformMemory.byteObjectLimit := by
      rw [hsz']; exact f0 (.blk inb) arr hb0
    exact putGz_fit (f0.with_bytes bound)
  obtain ⟨invZ, ownZ⟩ := GzInv.frame_data inv fr hdata freshZ uniqZ inv.common.globals fitZ
  have run' : cdoWhile copyBody copyCond (s.«in», s.strm.next_in, s.strm.avail_in) h = .ok (st, Z) := by
    rw [hin', hq]; exact run
  refine ⟨st, Z, run', ⟨hsZ, invZ⟩, hlive, ?_, ?_, rfl, rfl, ?_, rfl⟩
  · intro b
    have e1 := putGz_owned (s' := clearOut s) hsZ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b
    have e2 := putGz_owned (s' := clearOut s) hu.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b
    rw [← e1, ownZ b, e2]
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hnc => ?_⟩
    have hne : b ≠ inb := by
      intro e; subst e
      exact hnc ((putGz_owned (s' := clearOut s) hu.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).1
        (DataBuf.owned isData))
    exact ⟨upd_ne _ _ _ _ hne, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b c hc hbc
    rw [hin'] at hc; cases hc
    exact upd_ne _ _ _ _ hbc

#print axioms copy_run

/-! ## Composing post-conditions -/

section compose
variable {h Z h2 : Heap} {i : Nat} {s : GzState} {fs1 : Fs}

/-- A buffer frame over one region inside a block the frame may change is a frame. -/
theorem frame_of_bf_blk {C : Nat → Prop} {c off n : Nat}
    (bf : BufferFrame Z h2 C [⟨.ref (.blk c) off, n⟩]) (hc : C c) : Frame Z h2 C := by
  obtain ⟨⟨s1, a1, g1, n1, c1, slots⟩, _⟩ := bf
  have o := Zlib.Inflate.Proofs.restoreRegions_other Z h2 [⟨.ref (.blk c) off, n⟩]
  refine ⟨s1.trans o.1, a1.trans o.2.1, g1.trans o.2.2.1, by have := o.2.2.2.1; omega,
    by have := o.2.2.2.2.1; omega, fun b hl hb => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := slots b hl hb
  have hbc : b ≠ c := fun e => hb (e ▸ hc)
  have keep : (restoreRegions Z h2 [⟨.ref (.blk c) off, n⟩]).bytes b = h2.bytes b ∧
      (restoreRegions Z h2 [⟨.ref (.blk c) off, n⟩]).dstates b = h2.dstates b := by
    rw [restore_single]
    unfold restoreOne
    dsimp only
    cases Space.get Z (BRef.blk c) with
    | none => exact ⟨rfl, rfl⟩
    | some a => exact ⟨upd_ne _ _ _ _ hbc, rfl⟩
  refine ⟨keep.1 ▸ e1, ?_, ?_, ?_, keep.2 ▸ e5, ?_, ?_, ?_⟩
  · rw [← o.2.2.2.2.2.1]; exact e2
  · rw [← o.2.2.2.2.2.2.1]; exact e3
  · rw [← o.2.2.2.2.2.2.2.1]; exact e4
  · rw [← o.2.2.2.2.2.2.2.2.1]; exact e6
  · rw [← o.2.2.2.2.2.2.2.2.2.1]; exact e7
  · rw [← o.2.2.2.2.2.2.2.2.2.2]; exact e8

/-- The post-condition with a caller region inside an owned block is the post-condition with no region. -/
theorem post_drop_region {c off n : Nat}
    (post : GzPost Z i s [⟨.ref (.blk c) off, n⟩] fs1 h2 GzInvUpToOutput) (hc : GzOwned Z i s c) :
    GzPost Z i s [] fs1 h2 GzInvUpToOutput := by
  obtain ⟨hfs, s', inv', m, f, bf, lc, ng⟩ := post
  exact ⟨hfs, s', inv', m, f, ⟨frame_of_bf_blk bf hc, fun _ hm => by cases hm⟩, lc, ng⟩

/-- A record write after a call extends its post-condition. -/
theorem post_put {s2 s3 : GzState} (post : GzPost Z i s [] fs1 h2 GzInvUpToOutput)
    (hs2 : h2.gzstates i = some s2) (inv3 : GzInvUpToOutput (putGz h2 i s3) i s3)
    (own : ∀ b, GzOwned (putGz h2 i s3) i s3 b ↔ GzOwned h2 i s2 b) (hmode : s3.mode = s2.mode)
    (hfd : s3.fd = s2.fd) : GzPost Z i s [] fs1 (putGz h2 i s3) GzInvUpToOutput := by
  obtain ⟨hfs, s', inv', m, f, bf, lc, ng⟩ := post
  have e : s' = s2 := Option.some.inj (inv'.1.symm.trans hs2)
  subst e
  have fr : Frame Z h2 (GzOwned Z i s) := bf.1
  have fr2 : Frame Z (putGz h2 i s3) (GzOwned Z i s) := by
    refine ⟨fr.1, fr.2.1, fr.2.2.1, fr.2.2.2.1, fr.2.2.2.2.1, fun b hl hb => ?_⟩
    have hbi : b ≠ i := fun e => hb (Or.inl e)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := fr.2.2.2.2.2 b hl hb
    exact ⟨e1, e2, e3, e4, e5, e6, (upd_ne _ _ _ _ hbi).trans e7, e8⟩
  refine ⟨hfs, s3, inv3, hmode.trans m, hfd.trans f, ⟨fr2, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · intro b
    have L := lc b
    simp only at L ⊢
    rw [putGz_live hs2, own b]
    exact L
  · intro b hb
    exact ng b ((own b).1 hb)

/-- A change of owned blocks before a call extends its post-condition. -/
theorem post_pre (fr : Frame h Z (GzOwned h i s)) (hlive : ∀ b, Z.live b ↔ h.live b)
    (hown : ∀ b, GzOwned Z i s b ↔ GzOwned h i s b) (post : GzPost Z i s [] fs1 h2 GzInvUpToOutput) :
    GzPost h i s [] fs1 h2 GzInvUpToOutput := by
  obtain ⟨hfs, s', inv', m, f, bf, lc, ng⟩ := post
  have fr2 : Frame Z h2 (GzOwned h i s) := frame_mono' bf.1 (fun x hx => (hown x).1 hx)
  refine ⟨hfs, s', inv', m, f, ⟨frame_comp fr fr2, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · intro b
    have L := lc b
    simp only at L ⊢
    rw [L, hlive b, hown b]
  · intro b hb
    rcases ng b hb with e | e
    · exact Or.inl ((hown b).1 e)
    · exact Or.inr (fun hl => e ((hlive b).2 hl))

/-- The post-condition of a call that changed nothing. -/
theorem post_refl (hu : GzInvUpToOutput h i s) (hfs : FileSystem fs1) :
    GzPost h i s [] fs1 h GzInvUpToOutput := by
  refine ⟨hfs, s, hu, rfl, rfl, ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
    fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, fun _ hm => by cases hm⟩, ?_, fun b hb => Or.inl hb⟩
  intro b
  constructor
  · intro hl; exact Or.inl ⟨hl, fun hh => hh.2 hh.1⟩
  · rintro (⟨hl, _⟩ | ⟨_, hn⟩)
    · exact hl
    · exact absurd (hu.2.common.live b ((putGz_owned (s' := clearOut s) hu.1
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).2 ‹_›) |> (putGz_live hu.1 b).1) hn

end compose

/-! ## `gz_avail` -/

/-- The record after `gz_avail`: the old one with the flags, the error, the message and the input window changed. -/
def AvailRec (s t : GzState) : Prop :=
  let z : ZStream := { s.strm with avail_in := t.strm.avail_in, next_in := t.strm.next_in }
  t = { s with again := t.again, eof := t.eof, err := t.err, msg := t.msg, strm := z }

/-- The read budget and the error across `gz_avail`: `avail_in` grows by what the budget lost, and the error is the
old one or one that `gz_load` reports. -/
def AvailFs (s s' : GzState) (fs fs' : Fs) : Prop :=
  BudgetAcc s.fd fs fs' (s'.strm.avail_in.toNat - s.strm.avail_in.toNat) ∧
    s.strm.avail_in.toNat ≤ s'.strm.avail_in.toNat ∧ (s'.err = s.err ∨ s'.err = Z_ERRNO ∨ s'.err = Z_MEM_ERROR)

/-- The result and the flags across `gz_avail`: a `-1` leaves an error that is not `Z_OK`; a `0` keeps the error, and
a `0` with no input left has reached the end of the file (`eof ≠ 0`). A `0` that leaves `eof = 0` read at least one
byte: `gz_load` ran, and a load of nothing sets `eof`. -/
def AvailFlags (r : Int32) (s s' : GzState) : Prop :=
  (r = -1 → s'.err ≠ Z_OK) ∧ (r = 0 → s'.err = s.err) ∧ (r = 0 → s'.strm.avail_in = 0 → s'.eof ≠ 0) ∧
    (r = 0 → s'.eof = 0 → s.strm.avail_in.toNat < s'.strm.avail_in.toNat)

theorem AvailFs.refl (s : GzState) (fs : Fs) : AvailFs s s fs fs :=
  ⟨by simpa using BudgetAcc.refl s.fd fs, Nat.le_refl _, Or.inl rfl⟩

/-- **The tail of `gz_avail`**: load behind the pending input, then set the window. -/
theorem availLoad_run {h : Heap} {i : Nat} {s : GzState} {fs : Fs} (hu : GzInvUpToOutput h i s)
    (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0) (hfs : FileSystem fs)
    (hav : s.strm.avail_in.toNat ≤ s.size.toNat) (heof0 : s.eof = 0) :
    ∃ r fs' after, availLoad i fs h = .ok ((r, fs'), after) ∧ (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after GzInvUpToOutput ∧ ∃ s', after.gzstates i = some s' ∧ AvailRec s s' ∧ AvailFs s s' fs fs' ∧
        AvailFlags r s s' ∧ ∀ k, after.istates k = h.istates k := by
  have hs : h.gzstates i = some s := hu.1
  have inv : GzInv (putGz h i (clearOut s)) i (clearOut s) := hu.2
  have rd := inv.reader hm
  obtain ⟨inb, arr, hin, hb, hro, hsize⟩ := (rd.bufs hsz).1
  have hin' : s.«in» = .ref (.blk inb) 0 := hin
  have hb0 : h.bytes inb = some arr := hb
  have hsize' : arr.size = s.size.toNat := hsize
  have hadd : Ptr.add s.«in» (↑s.strm.avail_in.toNat : Int) h =
      .ok (.ref (.blk inb) (0 + s.strm.avail_in.toNat), h) := by
    rw [hin']
    exact Ptr.add_nat_ok (h := h) (r := BRef.blk inb) (a := arr) hb0 (by omega)
  have hlen : (s.size - s.strm.avail_in).toNat = s.size.toNat - s.strm.avail_in.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact hav)
  have hw : Writable h (.ref (.blk inb) (0 + s.strm.avail_in.toNat)) (s.size - s.strm.avail_in).toNat :=
    Or.inr ⟨.blk inb, _, arr, rfl, hb0, hro, by rw [hlen]; omega⟩
  have isData : DataBuf (clearOut s) inb := ⟨hsz, Or.inl hin⟩
  obtain ⟨-, hex, hpost⟩ := gz_load_safe i _ (s.size - s.strm.avail_in) h fs s hu hm hsz hfs hw
    (Or.inl ⟨inb, _, rfl, isData⟩) (fun he => absurd heof0 he)
  obtain ⟨⟨r, got⟩, fs1, h2, run⟩ := hex trivial
  have hist2 : ∀ k, h2.istates k = h.istates k := gz_load_istates i _ _ h fs s hu hm hsz hfs hw (Or.inl ⟨inb, _, rfl, isData⟩) (fun he => absurd heof0 he) run
  obtain ⟨hr, hgot, hkept, post, ⟨ag, ef, e, mm, hrec2, herr2, hf0, hf1, hf2, hfa⟩, hbud2⟩ := hpost _ _ _ run
  have hown_in : GzOwned h i s inb := DataBuf.owned (s := s) ⟨hsz, Or.inl hin'⟩
  have postZ := post_drop_region post hown_in
  have hld : (StateT.lift (ldS (some (.tab i))) : G GzState) fs h = .ok ((s, fs), h) := by
    rw [g_lift_app, ldS_eq, hs]
  have hz : (StateT.lift (ldZ (strmOf (some (.tab i)))) : G ZStream) fs h = .ok ((s.strm, fs), h) := by
    rw [g_lift_app, show ldZ (strmOf (some (GzStateRef.tab i))) h = .ok (s.strm, h) from ldZ_run hs]
  have hp : (StateT.lift (Ptr.add s.«in» (↑s.strm.avail_in.toNat : Int)) : G BPtr) fs h =
      .ok ((.ref (.blk inb) (0 + s.strm.avail_in.toNat), fs), h) := by
    rw [g_lift_app, hadd]
  have run' : Zlib.Gzread.gz_load (some (.tab i)) (.ref (.blk inb) (0 + s.strm.avail_in.toNat))
      (s.size - s.strm.avail_in) fs h = .ok (((r, got), fs1), h2) := run
  let s2 : GzState := { s with again := ag, eof := ef, err := e, msg := mm }
  have hs2 : h2.gzstates i = some s2 := hrec2
  unfold availLoad
  simp only [g_bind_app, hld, hz, hp, run']
  by_cases hr1 : r = -1
  · subst hr1
    simp only [beq_self_eq_true, ite_true]
    exact ⟨-1, fs1, h2, rfl, Or.inr rfl, hkept, postZ, s2, hs2, by unfold AvailRec; rfl,
      ⟨hbud2.mono (by show s.strm.avail_in.toNat - s.strm.avail_in.toNat ≤ _; omega), Nat.le_refl _, herr2⟩,
      ⟨(fun _ => hf1 rfl), (fun h0 => absurd h0 (by decide)), (fun h0 => absurd h0 (by decide)),
        (fun h0 => absurd h0 (by decide))⟩, hist2⟩
  have hr0 : r = 0 := hr.resolve_right hr1
  subst hr0
  have hne : ((0 : Int32) == -1) = false := by decide
  simp only [hne, Bool.false_eq_true, ite_false]
  have hld2 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs1 h2 = .ok ((s2, fs1), h2) := by
    rw [g_lift_app, ldS_eq, hs2]
  let s3 : GzState := { s2 with strm := { s2.strm with next_in := s2.«in», avail_in := s2.strm.avail_in + got } }
  have hupd : (StateT.lift (updZ (strmOf (some (.tab i))) fun z =>
      { z with next_in := s2.«in», avail_in := z.avail_in + got }) : G Unit) fs1 h2 =
      .ok (((), fs1), putGz h2 i s3) := by
    rw [g_lift_app, show updZ (strmOf (some (GzStateRef.tab i))) (fun z =>
      { z with next_in := s2.«in», avail_in := z.avail_in + got }) h2 = .ok ((), setS h2 i s3) from updZ_run hs2 _]
    rfl
  simp only [g_bind_app, hld2, hupd, g_pure_app]
  -- the new window
  obtain ⟨hfs1, s', inv', -, -, -, -, -⟩ := postZ
  have es : s' = s2 := Option.some.inj (inv'.1.symm.trans hs2)
  subst es
  have hgot' : got.toNat ≤ s.size.toNat - s.strm.avail_in.toNat := by
    have := hgot; rw [hlen] at this; exact this
  have hn : (s2.strm.avail_in + got).toNat ≤ s2.size.toNat := by
    show (s.strm.avail_in + got).toNat ≤ s.size.toNat
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by have := s.size.toNat_lt; omega)]
    omega
  have hae2 : s2.again ≠ 0 → s2.eof ≠ 0 → (s2.strm.avail_in + got) = 0 := fun ha he => by
    have : ef = 0 := (hfa ha).trans heof0
    exact absurd this he
  obtain ⟨inv3c, own3c⟩ := GzInv.set_input inv'.2 hm hsz (s2.strm.avail_in + got) hn hae2
  have e3 : putGz (putGz h2 i s3) i (clearOut s3) = putGz (putGz h2 i (clearOut s2)) i (clearOut s3) := by
    rw [putGz_putGz', putGz_putGz']
  have hs3 : (putGz h2 i s3).gzstates i = some s3 := by simp [putGz]
  have inv3 : GzInvUpToOutput (putGz h2 i s3) i s3 := ⟨hs3, by rw [e3]; exact inv3c⟩
  have own3 : ∀ b, GzOwned (putGz h2 i s3) i s3 b ↔ GzOwned h2 i s2 b := by
    intro b
    have a1 := putGz_owned (s' := clearOut s3) hs3 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b
    have a2 := putGz_owned (s' := clearOut s2) hs2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b
    rw [← a1, e3, ← a2]
    exact own3c b
  have e3 : s3.strm.avail_in.toNat = s.strm.avail_in.toNat + got.toNat := by
    show (s.strm.avail_in + got).toNat = _
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by have := hgot'; have := s.size.toNat_lt; omega)]
  refine ⟨0, fs1, putGz h2 i s3, rfl, Or.inl rfl, hkept, post_put (post_drop_region post hown_in) hs2 inv3 own3 rfl rfl,
    s3, hs3, by unfold AvailRec; rfl, ⟨?_, ?_, herr2⟩, ?_, hist2⟩
  · exact hbud2.mono (by show _ ≤ got.toNat; rw [e3]; omega)
  · show s.strm.avail_in.toNat ≤ (s.strm.avail_in + got).toNat
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by have := hgot'; have := s.size.toNat_lt; omega)]
    omega
  · unfold AvailFlags
    refine ⟨(fun h0 => absurd h0 (by decide)), (fun _ => hf0 rfl), (fun _ h0 => ?_), (fun _ h0 => ?_)⟩
    · -- nothing was read: the last `read` returned `0`, so `gz_load` set `eof`
      have hz0 : s3.strm.avail_in.toNat = 0 := by rw [h0]; rfl
      have hg0 : got = 0 := UInt32.toNat_inj.mp (by rw [UInt32.toNat_zero]; omega)
      show ef ≠ 0
      rw [hf2 rfl hg0]
      decide
    · -- `eof` stayed `0`, so the load read at least one byte
      have h0' : ef = 0 := h0
      have hg : got.toNat ≠ 0 := fun e => by
        have hg0 : got = 0 := UInt32.toNat_inj.mp (by rw [UInt32.toNat_zero]; exact e)
        rw [hf2 rfl hg0] at h0'
        exact absurd h0' (by decide)
      show s.strm.avail_in.toNat < s3.strm.avail_in.toNat
      rw [e3]
      omega

/-- **`gz_avail(state)` is safe** (the skeleton statement `gz_avail_safe`, with the premise that the handle is a
reader; `gz_avail` is a reading helper). It does not fault, returns `0` or `-1`, keeps the open descriptors, and
satisfies `GzPost` with no caller region; the record changes only in its flags, error, message and input window.
`AvailFlags` ties the result to the error and the end of the file. -/
theorem gz_avail_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (hu : GzInvUpToOutput h i s) (hm : s.mode = GZ_READ) (hfs : FileSystem fs) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzread.gz_avail (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvUpToOutput ∧
      ∃ s', after.gzstates i = some s' ∧ AvailRec s s' ∧ AvailFs s s' fs fs' ∧ AvailFlags r s s' ∧
        ∀ k, after.istates k = h.istates k := by
  have hs : h.gzstates i = some s := hu.1
  have key : ∃ r fs' after, Zlib.Gzread.gz_avail (gzSt i) fs h = .ok ((r, fs'), after) ∧
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvUpToOutput ∧
      ∃ s', after.gzstates i = some s' ∧ AvailRec s s' ∧ AvailFs s s' fs fs' ∧ AvailFlags r s s' ∧
        ∀ k, after.istates k = h.istates k := by
    rw [gz_avail_source]
    have hld : (StateT.lift (ldS (some (.tab i))) : G GzState) fs h = .ok ((s, fs), h) := by
      rw [g_lift_app, ldS_eq, hs]
    simp only [g_bind_app, hld]
    by_cases herr : (s.err != Z_OK && s.err != Z_BUF_ERROR) = true
    · rw [if_pos herr]
      exact ⟨-1, fs, h, rfl, Or.inr rfl, fun _ => Iff.rfl, post_refl hu hfs, s, hs, by unfold AvailRec; rfl, AvailFs.refl s fs,
        ⟨(fun _ e => by rw [e] at herr; revert herr; decide), (fun h0 => absurd h0 (by decide)),
        (fun h0 => absurd h0 (by decide)), (fun h0 => absurd h0 (by decide))⟩, fun _ => rfl⟩
    rw [if_neg herr]
    by_cases heof : ¬ (s.eof == 0) = true
    · rw [if_neg heof]
      exact ⟨0, fs, h, rfl, Or.inl rfl, fun _ => Iff.rfl, post_refl hu hfs, s, hs, by unfold AvailRec; rfl, AvailFs.refl s fs,
        ⟨(fun h0 => absurd h0 (by decide)), (fun _ => rfl), (fun _ _ e => heof (by simp [e])),
          (fun _ e => (heof (by simp [e])).elim)⟩, fun _ => rfl⟩
    rw [if_pos (Classical.not_not.mp heof)]
    have heof0 : s.eof = 0 := by simpa using Classical.not_not.mp heof
    have hz : (StateT.lift (ldZ (strmOf (some (.tab i)))) : G ZStream) fs h = .ok ((s.strm, fs), h) := by
      rw [g_lift_app, show ldZ (strmOf (some (GzStateRef.tab i))) h = .ok (s.strm, h) from ldZ_run hs]
    simp only [g_bind_app, hz]
    have hav : s.strm.avail_in.toNat ≤ s.size.toNat := by
      rcases (hu.2.reader hm).input with z | ⟨a, _, hle⟩
      · have z' : s.strm.avail_in = 0 := z
        rw [z']; exact Nat.zero_le _
      · have hle' : a + s.strm.avail_in.toNat ≤ s.size.toNat := hle
        omega
    by_cases h1 : (s.strm.avail_in != 0) = true
    · rw [if_pos h1]
      by_cases h2 : (s.strm.next_in != s.«in») = true
      · rw [if_pos h2]
        have hav0 : s.strm.avail_in ≠ 0 := by simpa using h1
        obtain ⟨st, Z, crun, huZ, hliveZ, hownZ, frZ, -, -, -, histZ⟩ := copy_run hu hm hsz hav0
        have crun' : (StateT.lift (cdoWhile copyBody copyCond (s.«in», s.strm.next_in, s.strm.avail_in)) :
            G _) fs h = .ok ((st, fs), Z) := by rw [g_lift_app, crun]
        simp only [g_bind_app, crun']
        obtain ⟨r, fs', after, run, hr, hk, post, s', hs', hrec, hfs', hfl, hist⟩ := availLoad_run huZ hm hsz hfs hav heof0
        exact ⟨r, fs', after, run, hr, hk, post_pre frZ hliveZ hownZ post, s', hs', hrec, hfs', hfl, fun k => (hist k).trans (by rw [histZ])⟩
      · rw [if_neg h2]
        exact availLoad_run hu hm hsz hfs hav heof0
    · rw [if_neg h1]
      exact availLoad_run hu hm hsz hfs hav heof0
  obtain ⟨r, fs', after, run, post⟩ := key
  refine ⟨fun e he => ?_, fun _ => ⟨r, fs', after, run⟩, fun r' fs3 after' he => ?_⟩
  · rw [run] at he; cases he
  · rw [run] at he
    cases he
    exact post

#print axioms availLoad_run
#print axioms gz_avail_safe

end ZlibF.Spec.Public.GzRead
