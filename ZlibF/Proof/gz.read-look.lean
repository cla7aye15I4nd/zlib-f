import ZlibF.Proof.«gz.read-fetch-specs»
import ZlibF.Proof.«gz.read-budget»
import ZlibF.Proof.«inflate.c.reachable»
import ZlibF.Proof.«inflate.c.start»
import ZlibF.Proof.«inflate.c.reset»
import ZlibF.Proof.«gzwrite.c.init»
import ZlibF.Proof.«public-inflate-init»

/-!
# gz read side: `gz_look` is safe

`gz_look(state)` sets up the reader on its first call (`size == 0`: the buffers `in` and `out`, then
`inflateInit2(strm, 31)`), and then decides how to read: a gzip member (`inflateReset`, `how = GZIP`), or a
transparent copy of the input (`how = COPY`, the pending input moved to `out`).

1. `gz_look_source`: the source as a composition of named pieces (`lookAlloc`, `lookMain`, `lookAuto`,
   `lookMagic`, `lookGzip`, `lookCopy`), proved by `rfl`.
2. `GzInv.rebuild`: a reader record whose codec and scalars change, over a heap that changes only the record and
   the codec's blocks, keeps the invariant.
3. `post_trans`: two `GzPost` steps compose.
4. One run lemma per piece; `gz_look_safe` assembles them.
-/

namespace ZlibF.Spec.Public.GzRead
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec Zlib.Gzlib.Proofs ZlibF.Spec.Public
set_option autoImplicit false

namespace Look

/-! ## The source in pieces -/

/-- `inflateReset(strm); state->how = GZIP; state->junk = f(junk); state->direct = 0; return 0;` -/
def lookGzip (i : Nat) (f : Int32 → Int32) : G Int32 := do
  let _ ← StateT.lift (Zlib.Inflate.inflateReset (strmOf (some (.tab i))))
  StateT.lift (updS (some (.tab i)) fun s => { s with how := GZIP, junk := f s.junk, direct := 0 })
  pure 0

/-- The copy path: the pending input goes to `out`, at most the room left before `GZ_OFF_MAX` is buffered, and the
rest gives `Z_DATA_ERROR` (patch 0004). -/
def lookCopy (i : Nat) (z : ZStream) : G Int32 := do
  let s ← StateT.lift (ldS (some (.tab i)))
  StateT.lift (updX (some (.tab i)) fun x => { x with next := s.out })
  StateT.lift (memcpyB s.out z.next_in z.avail_in.toNat)
  let room ← StateT.lift (Zlib.Gzread.gz_room (some (.tab i)) z.avail_in)
  StateT.lift (updX (some (.tab i)) fun x => { x with «have» := room })
  if (← StateT.lift (ldS (some (.tab i)))).x.«have» < (← StateT.lift (ldZ (strmOf (some (.tab i))))).avail_in then
    StateT.lift (Zlib.Gzlib.gz_error (some (.tab i)) Z_DATA_ERROR (← StateT.lift (strLitRef "position overflow")))
  StateT.lift (updZ (strmOf (some (.tab i))) fun z => { z with avail_in := 0 })
  StateT.lift (updS (some (.tab i)) fun s => { s with how := GZ_COPY })
  pure 0

/-- After the magic-byte test. -/
def lookFinal (i : Nat) (z : ZStream) (isGz : Bool) : G Int32 :=
  if isGz then lookGzip i (fun _ => 0) else lookCopy i z

/-- The magic-byte test. -/
def lookMagic (i : Nat) (z : ZStream) : G Int32 :=
  if z.avail_in > 3 then do
    let b0 ← StateT.lift (index8 z.next_in 0)
    if (b0 == 31) = true then do
      let b1 ← StateT.lift (index8 z.next_in 1)
      if (b1 == 139) = true then do
        let b2 ← StateT.lift (index8 z.next_in 2)
        if (b2 == 8) = true then do
          let b3 ← StateT.lift (index8 z.next_in 3)
          if b3 < 32 then lookFinal i z true else lookFinal i z false
        else lookFinal i z false
      else lookFinal i z false
    else lookFinal i z false
  else lookFinal i z false

/-- The auto-detecting path. -/
def lookAuto (i : Nat) : G Int32 := do
  let a ← Zlib.Gzread.gz_avail (some (.tab i))
  if (a == -1) = true then pure (-1) else do
  let z ← StateT.lift (ldZ (strmOf (some (.tab i))))
  let s ← StateT.lift (ldS (some (.tab i)))
  if (z.avail_in == 0 || (s.again != 0 && z.avail_in < 4)) = true then pure 0 else lookMagic i z

/-- Everything after the allocation. -/
def lookMain (i : Nat) : G Int32 := do
  let s ← StateT.lift (ldS (some (.tab i)))
  if (s.direct == -1 || s.junk == 0) = true then do
    let z ← StateT.lift (ldZ (strmOf (some (.tab i))))
    if (s.junk == 0 && z.avail_in == 0) = true then do
      let a ← Zlib.Gzread.gz_avail (some (.tab i))
      if (a == -1) = true then pure (-1) else do
        let z ← StateT.lift (ldZ (strmOf (some (.tab i))))
        if (z.avail_in == 0) = true then pure 0 else lookGzip i (fun j => if j != -1 then 1 else 0)
    else lookGzip i (fun j => if j != -1 then 1 else 0)
  else lookAuto i

/-- The allocation (`size == 0`). -/
def lookAlloc (i : Nat) (s : GzState) : G Int32 := do
  let inb ← StateT.lift (allocB s.want.toNat)
  StateT.lift (updS (some (.tab i)) fun s => { s with «in» := inb })
  let s ← StateT.lift (ldS (some (.tab i)))
  let outb ← StateT.lift (allocB (s.want <<< 1).toNat)
  StateT.lift (updS (some (.tab i)) fun s => { s with out := outb })
  if (inb == .null || outb == .null) = true then do
    StateT.lift (freeB outb)
    StateT.lift (freeB inb)
    let m ← StateT.lift (strLitRef "out of memory")
    StateT.lift (Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR m)
    pure (-1)
  else do
    let _ ← StateT.lift (ldS (some (.tab i)))
    StateT.lift (updS (some (.tab i)) fun s => { s with size := s.want })
    StateT.lift (updZ (strmOf (some (.tab i))) fun z =>
      { z with zalloc := .null, zfree := .null, «opaque» := .null, avail_in := 0, next_in := .null })
    let ver ← StateT.lift (strLitRef ZLIB_VERSION)
    let r ← StateT.lift (Zlib.Inflate.inflateInit2_ (strmOf (some (.tab i))) 31 ver 112)
    if (r != Z_OK) = true then do
      let s ← StateT.lift (ldS (some (.tab i)))
      StateT.lift (freeB s.out)
      StateT.lift (freeB s.«in»)
      StateT.lift (updS (some (.tab i)) fun s => { s with size := 0 })
      let m ← StateT.lift (strLitRef "out of memory")
      StateT.lift (Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR m)
      pure (-1)
    else lookMain i

theorem gz_look_source (i : Nat) : Zlib.Gzread.gz_look (gzSt i) = (do
    let s ← StateT.lift (ldS (some (.tab i)))
    if (s.size == 0) = true then lookAlloc i s else lookMain i) := rfl

/-! ## The reader invariant after a change of the codec and of scalars -/

section rebuild
variable {h h' : Heap} {i : Nat} {s s' : GzState}

/-- The four pointer blocks of a reader with buffers are kept by a frame over the record and the codec. -/
theorem GzInv.ptr_kept (inv : GzInv h i s) (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0)
    (fr : Frame h h' (fun b => b = i ∨ StreamOwned h (gzStrm i) b)) {p : BPtr}
    (hp : p = s.path ∨ p = s.msg ∨ p = s.«in» ∨ p = s.out) {b : Nat} (hb : p = .ref (.blk b) 0) :
    h'.bytes b = h.bytes b ∧ h'.ro b = h.ro b ∧ h.live b ∧ h'.live b := by
  have mem : p ∈ ownedPtrs s := by
    unfold ownedPtrs
    rw [if_pos hsz, if_pos (Or.inl hm)]
    rcases hp with e | e | e | e <;> subst e <;> simp
  have hbk : blkOf p = some b := by rw [hb]; rfl
  obtain ⟨hbi, hso⟩ := inv.common.distinct.2 p mem b hbk
  have hl := inv.ptr_live mem hbk
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := fr.2.2.2.2.2 b hl (fun hc => hc.elim hbi hso)
  refine ⟨e1, e8, hl, ?_⟩
  unfold Heap.live at hl ⊢
  rw [e1, e2, e3, e4, e5, e6, e7]
  exact hl

/-- **A reader record whose codec and scalars change keeps the invariant**, over a heap that changes only the
record and the codec's blocks, when the codec owns no new block, the input window is in `in` and the codec
history continues. The record has no buffered output (`x.next = NULL`). -/
theorem GzInv.rebuild (inv : GzInv h i s) (hm : s.mode = GZ_READ) (hsz : s.size ≠ 0) (hx0 : s.x.have = 0)
    (hxn : s.x.next = .null) (rec : h'.gzstates i = some s')
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.«in» = s.«in» ∧ s'.out = s.out ∧ s'.size = s.size ∧
      s'.mode = s.mode ∧ s'.want = s.want ∧ s'.err = s.err ∧ s'.x = s.x ∧ s'.skip = s.skip ∧
      s'.eof = s.eof ∧ s'.past = s.past ∧ s'.again = s.again)
    (scal : (s'.how = LOOK ∨ s'.how = GZ_COPY ∨ s'.how = GZIP) ∧ (s'.how = GZ_COPY → s'.direct = 0 ∨ s'.direct = 1) ∧
      (s'.how = GZIP → s'.direct = 0) ∧ (s'.direct = -1 ∨ s'.direct = 0 ∨ s'.direct = 1) ∧
      (s'.junk = -1 ∨ s'.junk = 0 ∨ s'.junk = 1))
    (input : s'.strm.avail_in = 0 ∨
      ∃ a, s'.strm.next_in = padv s'.«in» a ∧ a + s'.strm.avail_in.toNat ≤ s'.size.toNat)
    (hae : s'.again ≠ 0 → s'.eof ≠ 0 → s'.strm.avail_in = 0)
    (fr : Frame h h' (fun b => b = i ∨ StreamOwned h (gzStrm i) b))
    (sown : ∀ b, StreamOwned h' (gzStrm i) b → StreamOwned h (gzStrm i) b ∧ h'.live b)
    (fresh : Fresh h') (uniq : Zlib.Gzlib.Spec.Uniq h') (globals : LibraryGlobals h')
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h')
    (codec : StreamReachable .inflate h' (gzStrm i) ∧
      ∃ z k st, (gzStrm i).get h' = some z ∧ z.state = some (.inflate k) ∧ h'.istates k = some st ∧
        st.head = none) :
    GzInv h' i s' := by
  obtain ⟨epath, emsg, ein, eout, esize, emode, ewant, eerr, ex, eskip, eeof, epast, eagain⟩ := same
  obtain ⟨show_, scopy, sgzip, sdirect, sjunk⟩ := scal
  have c := inv.common
  have rd := inv.reader hm
  have hm' : s'.mode = GZ_READ := emode.trans hm
  have hsz' : s'.size ≠ 0 := by rw [esize]; exact hsz
  have kept := fun {p : BPtr} (hp : p = s.path ∨ p = s.msg ∨ p = s.«in» ∨ p = s.out) {b : Nat}
    (hb : p = .ref (.blk b) 0) => GzInv.ptr_kept inv hm hsz fr hp hb
  have hmalloc : ∀ p n, (p = s.path ∨ p = s.msg ∨ p = s.«in» ∨ p = s.out) → MallocBuffer h p n →
      MallocBuffer h' p n := by
    intro p n hp hx
    obtain ⟨b, a, e, hb, hr, hn⟩ := hx
    obtain ⟨k1, k2, -, -⟩ := kept hp e
    exact ⟨b, a, e, by rw [k1]; exact hb, by rw [k2]; exact hr, hn⟩
  have hexact : ∀ p n, (p = s.path ∨ p = s.msg ∨ p = s.«in» ∨ p = s.out) → ExactBuffer h p n →
      ExactBuffer h' p n := by
    intro p n hp hx
    obtain ⟨b, a, e, hb, hr, hn⟩ := hx
    obtain ⟨k1, k2, -, -⟩ := kept hp e
    exact ⟨b, a, e, by rw [k1]; exact hb, by rw [k2]; exact hr, hn⟩
  have hptrs : ownedPtrs s' = ownedPtrs s := by
    simp [ownedPtrs, epath, emsg, esize, ein, eout, hsz, hm, hm']
  refine ⟨?_, fun _ => ?_, fun hw => absurd (hm'.symm.trans hw) (by decide)⟩
  · exact {
      record := rec
      mode := Or.inl hm'
      fresh := fresh
      uniq := uniq
      globals := globals
      fit := fit
      path := by
        obtain ⟨p, hc, hmb⟩ := c.path
        refine ⟨p, ?_, by rw [epath]; exact hmalloc _ _ (Or.inl rfl) hmb⟩
        obtain ⟨pb, a, hp, -, -, -⟩ := hmb
        rw [epath, hp]
        rw [hp] at hc
        exact (cstring_blk_congr (kept (Or.inl rfl) hp).1).2 hc
      msg := by
        rw [emsg]
        rcases c.msg with hn | ⟨m, hc, hmb⟩
        · exact Or.inl hn
        · refine Or.inr ⟨m, ?_, hmalloc _ _ (Or.inr (Or.inl rfl)) hmb⟩
          obtain ⟨mb, a, hp, -, -, -⟩ := hmb
          rw [hp]
          rw [hp] at hc
          exact (cstring_blk_congr (kept (Or.inr (Or.inl rfl)) hp).1).2 hc
      memerr := by rw [eerr, emsg]; exact c.memerr
      want := by rw [ewant]; exact c.want
      size := by rw [esize, ewant]; exact c.size
      distinct := by
        rw [hptrs]
        exact ⟨c.distinct.1, fun p hp b hb =>
          ⟨(c.distinct.2 p hp b hb).1, fun ho => (c.distinct.2 p hp b hb).2 (sown b ho).1⟩⟩
      live := by
        intro b ho
        rcases ho with e | e | e | ⟨-, e | ⟨-, e | e⟩⟩
        · subst e; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [rec]; intro x; cases x))))))
        · exact (kept (Or.inl rfl) (by rw [← epath]; exact e)).2.2.2
        · exact (kept (Or.inr (Or.inl rfl)) (by rw [← emsg]; exact e)).2.2.2
        · exact (kept (Or.inr (Or.inr (Or.inl rfl))) (by rw [← ein]; exact e)).2.2.2
        · exact (kept (Or.inr (Or.inr (Or.inr rfl))) (by rw [← eout]; exact e)).2.2.2
        · exact (sown b e).2
      pos := by rw [ex, eskip]; exact c.pos
      next := fun hh => absurd (by rw [ex]; exact hx0) hh
      nullHave := fun _ => by rw [ex]; exact hx0
      recordFree := fun ho => c.recordFree (sown i ho).1 }
  · exact {
      how := show_
      copyDirect := scopy
      gzipDirect := sgzip
      direct := sdirect
      junk := sjunk
      flags := by rw [eeof, epast, eagain]; exact rd.flags
      unalloc := fun hz => absurd hz hsz'
      bufs := fun _ => by
        rw [ein, eout, esize]
        exact ⟨hexact _ _ (Or.inr (Or.inr (Or.inl rfl))) (rd.bufs hsz).1,
          hexact _ _ (Or.inr (Or.inr (Or.inr rfl))) (rd.bufs hsz).2⟩
      input := input
      output := fun hh => absurd (by rw [ex]; exact hx0) hh
      codec := fun _ => codec
      posHave := by rw [ex]; exact rd.posHave
      againSize := fun hz => absurd hz hsz'
      haveSkip := fun hh => absurd (by rw [ex]; exact hx0) hh
      againEof := hae }

end rebuild

/-! ## Composing post-conditions -/

section posts
variable {h h1 h2 : Heap} {i : Nat} {s s1 : GzState} {fs1 fs2 : Fs}

theorem live_trans_logic (a a1 a2 o o1 o2 : Prop) (L1 : a1 ↔ (a ∧ ¬ (o ∧ ¬ o1)) ∨ (o1 ∧ ¬ a))
    (L2 : a2 ↔ (a1 ∧ ¬ (o1 ∧ ¬ o2)) ∨ (o2 ∧ ¬ a1)) (N1 : o1 → o ∨ ¬ a) (N2 : o2 → o1 ∨ ¬ a1) :
    (a2 ↔ (a ∧ ¬ (o ∧ ¬ o2)) ∨ (o2 ∧ ¬ a)) ∧ (o2 → o ∨ ¬ a) := by
  rcases Classical.em a with ha | ha <;> rcases Classical.em o with ho | ho <;>
    rcases Classical.em o1 with ho1 | ho1 <;> rcases Classical.em o2 with ho2 | ho2 <;> simp_all

/-- **Two post-conditions compose.** -/
theorem post_trans {P : Heap → Nat → GzState → Prop}
    (p1 : GzPost h i s [] fs1 h1 GzInvUpToOutput) (hs1 : h1.gzstates i = some s1)
    (p2 : GzPost h1 i s1 [] fs2 h2 P) : GzPost h i s [] fs2 h2 P := by
  obtain ⟨-, t1, inv1, m1, f1, bf1, lc1, ng1⟩ := p1
  have e : t1 = s1 := Option.some.inj (inv1.1.symm.trans hs1)
  subst e
  obtain ⟨hfs2, t2, inv2, m2, f2, bf2, lc2, ng2⟩ := p2
  have fr1 : Frame h h1 (GzOwned h i s) := bf1.1
  have fr2 : Frame h1 h2 (GzOwned h1 i t1) := bf2.1
  have key : ∀ b, (h2.live b ↔ (h.live b ∧ ¬ (GzOwned h i s b ∧ ¬ GzOwned h2 i t2 b)) ∨
      (GzOwned h2 i t2 b ∧ ¬ h.live b)) ∧ (GzOwned h2 i t2 b → GzOwned h i s b ∨ ¬ h.live b) :=
    fun b => live_trans_logic _ _ _ _ _ _ (lc1 b) (lc2 b) (ng1 b) (ng2 b)
  refine ⟨hfs2, t2, inv2, m2.trans m1, f2.trans f1, ⟨?_, fun _ hm => by cases hm⟩, fun b => (key b).1,
    fun b => (key b).2⟩
  refine ⟨fr1.1.trans fr2.1, fr1.2.1.trans fr2.2.1, fr1.2.2.1.trans fr2.2.2.1,
    Nat.le_trans fr1.2.2.2.1 fr2.2.2.2.1, Nat.le_trans fr1.2.2.2.2.1 fr2.2.2.2.2.1, ?_⟩
  intro b hl hno
  have hl1 : h1.live b := (lc1 b).2 (Or.inl ⟨hl, fun hr => hno hr.1⟩)
  have hno1 : ¬ GzOwned h1 i t1 b := fun ho => (ng1 b ho).elim hno (fun hn => hn hl)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := fr1.2.2.2.2.2 b hl hno
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := fr2.2.2.2.2.2 b hl1 hno1
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7, b8.trans a8⟩

/-- The post-condition with the buffered output inside `out`. -/
theorem post_out (p : GzPost h i s [] fs1 h1 GzInvUpToOutput)
    (hw : ∀ s', h1.gzstates i = some s' → OutWindow s') : GzPost h i s [] fs1 h1 GzInvOut := by
  obtain ⟨hfs, s', inv', m, f, bf, lc, ng⟩ := p
  exact ⟨hfs, s', ⟨inv', hw s' inv'.1⟩, m, f, bf, lc, ng⟩

/-- An owned block of a handle in `GzInvUpToOutput` is live. -/
theorem upTo_owned_live (hu : GzInvUpToOutput h i s) (b : Nat) (ho : GzOwned h i s b) : h.live b :=
  (putGz_live hu.1 b).1 (hu.2.common.live b
    ((putGz_owned (s' := clearOut s) hu.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ b).2 ho))

/-- **One step** that removes the blocks `D` (owned before) and creates the blocks `C` (not live before). -/
theorem post_step {D C : Nat → Prop} (hu : GzInvUpToOutput h i s) (hu1 : GzInvUpToOutput h1 i s1)
    (hfs : FileSystem fs1) (hmode : s1.mode = s.mode) (hfd : s1.fd = s.fd) (fr : Frame h h1 (GzOwned h i s))
    (hD : ∀ b, D b → GzOwned h i s b) (hC : ∀ b, C b → ¬ h.live b)
    (own : ∀ b, GzOwned h1 i s1 b ↔ (GzOwned h i s b ∧ ¬ D b) ∨ C b)
    (live : ∀ b, h1.live b ↔ (h.live b ∧ ¬ D b) ∨ C b) :
    GzPost h i s [] fs1 h1 GzInvUpToOutput := by
  refine ⟨hfs, s1, hu1, hmode, hfd, ⟨fr, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · intro b
    have L := live b
    have O := own b
    have ol := upTo_owned_live hu b
    have dc := hD b
    have cc := hC b
    show h1.live b ↔ (h.live b ∧ ¬ (GzOwned h i s b ∧ ¬ GzOwned h1 i s1 b)) ∨ (GzOwned h1 i s1 b ∧ ¬ h.live b)
    rcases Classical.em (h.live b) with ha | ha <;> rcases Classical.em (D b) with hd | hd <;>
      rcases Classical.em (C b) with hc | hc <;> rcases Classical.em (GzOwned h i s b) with ho | ho <;>
      simp_all
  · intro b ho
    rcases (own b).1 ho with ⟨o, _⟩ | c
    · exact Or.inl o
    · exact Or.inr (hC b c)

end posts

/-! ## Sub-heaps -/

/-- A heap whose tables hold at most the objects of another, with the same static data, keeps freshness,
uniqueness, the globals and the object-size bound. -/
theorem sub_heap {W V : Heap} (hb : ∀ b, V.bytes b = W.bytes b ∨ V.bytes b = none) (hw : V.words = W.words)
    (hs : V.streams = W.streams) (hg : V.gzheaders = W.gzheaders) (hd : V.dstates = W.dstates)
    (hi : ∀ b, (V.istates b).isSome = (W.istates b).isSome) (hz : ∀ b, (V.gzstates b).isSome = (W.gzstates b).isSome)
    (hn : V.nextBlk = W.nextBlk) (hst : V.static = W.static) (hl : V.libcErrorBorrow = W.libcErrorBorrow) :
    (∀ b, V.live b → W.live b) ∧ (Fresh W → Fresh V) ∧ (Zlib.Gzlib.Spec.Uniq W → Zlib.Gzlib.Spec.Uniq V) ∧
    (LibraryGlobals W → LibraryGlobals V) ∧
    (ZlibF.PlatformMemory.ByteObjectsFit W → ZlibF.PlatformMemory.ByteObjectsFit V) := by
  have lv : ∀ b, V.live b → W.live b := by
    intro b hv
    unfold Heap.live at hv ⊢
    rw [hw, hs, hg, hd] at hv
    rcases hv with e | e | e | e | e | e | e
    · rcases hb b with x | x
      · exact Or.inl (by rw [← x]; exact e)
      · exact absurd x e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
      have := hi b
      intro n; rw [n] at this; cases hv' : V.istates b <;> simp_all
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
      have := hz b
      intro n; rw [n] at this; cases hv' : V.gzstates b <;> simp_all
  refine ⟨lv, fun f b hb' hlv => f b (by rw [← hn]; exact hb') (lv b hlv), fun u b => ?_, fun g => ?_, fun f => ?_⟩
  · have ub := u b
    have c1 : Zlib.Gzlib.Spec.cnt (V.bytes b) ≤ Zlib.Gzlib.Spec.cnt (W.bytes b) := by
      rcases hb b with x | x <;> rw [x] <;> simp [Zlib.Gzlib.Spec.cnt]
    have c6 : Zlib.Gzlib.Spec.cnt (V.istates b) = Zlib.Gzlib.Spec.cnt (W.istates b) := by
      simp only [Zlib.Gzlib.Spec.cnt, hi b]
    have c7 : Zlib.Gzlib.Spec.cnt (V.gzstates b) = Zlib.Gzlib.Spec.cnt (W.gzstates b) := by
      simp only [Zlib.Gzlib.Spec.cnt, hz b]
    rw [hw, hs, hg, hd, c6, c7]
    omega
  · unfold LibraryGlobals at g ⊢
    rw [hst]; exact g
  · intro r a e
    apply f r a
    cases r with
    | blk b =>
      have e' : V.bytes b = some a := e
      rcases hb b with x | x
      · show W.bytes b = some a
        rw [← x]; exact e'
      · rw [x] at e'; cases e'
    | str j =>
      have e' : staticStringBytes V j = some a := by simpa [Space.get] using e
      show Space.get W (BRef.str j) = some a
      simp only [Space.get]
      unfold staticStringBytes at e' ⊢
      rw [← hl]; exact e'
    | dstate_depth k =>
      have e' := e
      simp only [Space.get] at e' ⊢
      rw [← hd]; exact e'
    | st_dist_code =>
      have e' := e
      simp only [Space.get] at e' ⊢
      rw [← hst]; exact e'
    | st_length_code =>
      have e' := e
      simp only [Space.get] at e' ⊢
      rw [← hst]; exact e'

/-! ## `inflateReset` on the embedded stream -/

section reset
open Zlib.Inflate.Spec Zlib.Inflate.Proofs

theorem cnt_none_of {α : Type} {o : Option α} (e : Zlib.Gzlib.Spec.cnt o = 0) : o = none := by
  cases o with
  | none => rfl
  | some _ => simp at e

/-- A byte block holds nothing else. -/
theorem uniq_bytes_all {W : Heap} (u : Zlib.Gzlib.Spec.Uniq W) {b : Nat} {a : Array UInt8} (e : W.bytes b = some a) :
    W.words b = none ∧ W.streams b = none ∧ W.gzheaders b = none ∧ W.dstates b = none ∧ W.istates b = none ∧
      W.gzstates b = none := by
  have hu := u b
  rw [e] at hu
  simp only [Zlib.Gzlib.Spec.cnt_some] at hu
  exact ⟨cnt_none_of (by omega), cnt_none_of (by omega), cnt_none_of (by omega), cnt_none_of (by omega),
    cnt_none_of (by omega), cnt_none_of (by omega)⟩

theorem resetHeap_eq (H : Heap) (st : InflateState) :
    resetHeap H st = { H with bytes := (resetHeap H st).bytes } := by
  unfold resetHeap freeWin
  split
  · split <;> rfl
  · rfl

theorem resetHeap_bytes (H : Heap) (st : InflateState) (b : Nat) :
    (resetHeap H st).bytes b =
      if st.wbits ≠ st.reqbits ∧ st.window = .ref (.blk b) 0 then none else H.bytes b := by
  unfold resetHeap
  by_cases hw : st.wbits = st.reqbits
  · simp [hw]
  · have hb : (st.wbits != st.reqbits) = true := by simpa using hw
    rw [if_pos hb]
    unfold freeWin
    split
    · rename_i w heq
      by_cases e : w = b
      · subst e; simp [heq, hw]
      · simp [heq, e, upd_ne _ _ _ _ (Ne.symm e)]
    · rename_i hn
      have : ¬ st.window = .ref (.blk b) 0 := fun e => hn b e
      simp [this]

theorem look_resetPre_window (st : InflateState) :
    (resetPre st).window = if st.wbits = st.reqbits then st.window else .null := by
  unfold resetPre
  by_cases hw : st.wbits = st.reqbits
  · simp [hw]
  · simp [hw]

/-- The codec of a reader with buffers: a live inflate stream in the decoder invariant, on a reachable history. -/
theorem codec_facts {W : Heap} {i : Nat} {u : GzState} (inv : GzInv W i u) (hm : u.mode = GZ_READ)
    (hsz : u.size ≠ 0) :
    ∃ k st, u.strm.state = some (.inflate k) ∧ W.istates k = some st ∧ st.head = none ∧
      StreamReachable .inflate W (gzStrm i) ∧ InflateInv W (gzStrm i) k u.strm st := by
  obtain ⟨reach, z, k, st, hz, hzst, hk, hhead⟩ := (inv.reader hm).codec hsz
  have hget : (gzStrm i).get W = some u.strm := by simp [ZStreamRef.get, gzStrm, inv.common.record]
  have hzu : z = u.strm := by rw [hget] at hz; exact (Option.some.inj hz).symm
  subst hzu
  obtain ⟨k', z', st', I, -⟩ := reachable_invariant_kind reach rfl
  have e1 : z' = u.strm := Option.some.inj (I.good.live.hz.symm.trans hget)
  subst e1
  have e2 : k' = k := by
    have := I.good.live.zst.symm.trans hzst
    cases this; rfl
  subst e2
  have e3 : st' = st := Option.some.inj (I.good.live.hs.symm.trans hk)
  subst e3
  exact ⟨_, _, hzst, hk, hhead, reach, I⟩

/-- **`inflateReset(strm); how = GZIP; junk = f(junk); direct = 0`** on a reader with buffers: it returns `0`, keeps
the invariant up to the buffered output with the post-condition, and leaves the decoder at `HEAD` with the input
window unchanged. -/
theorem lookGzip_run {H : Heap} {i : Nat} {t : GzState} (fs : Fs) (hu : GzInvUpToOutput H i t)
    (hm : t.mode = GZ_READ) (hsz : t.size ≠ 0) (hfs : FileSystem fs) (f : Int32 → Int32)
    (hf : ∀ j, f j = 0 ∨ f j = 1) :
    ∃ H' t', lookGzip i f fs H = .ok ((0, fs), H') ∧ H'.gzstates i = some t' ∧
      GzPost H i t [] fs H' GzInvUpToOutput ∧
      t' = { t with how := GZIP, junk := f t.junk, direct := 0, strm := t'.strm } ∧
      t'.strm.avail_in = t.strm.avail_in ∧ t'.strm.next_in = t.strm.next_in ∧ InflateAtHead H' t' ∧
      t'.strm.msg = .null := by
  have hs : H.gzstates i = some t := hu.1
  have inv : GzInv (putGz H i (clearOut t)) i (clearOut t) := hu.2
  have hmc : (clearOut t).mode = GZ_READ := hm
  have hszc : (clearOut t).size ≠ 0 := hsz
  have rd := inv.reader hmc
  have c := inv.common
  obtain ⟨k, st, hzst, hk, hhead, reach, I⟩ := codec_facts inv hmc hszc
  have hzst' : t.strm.state = some (.inflate k) := hzst
  have hkH : H.istates k = some st := hk
  have hLW : Live (putGz H i (clearOut t)) (.in_gzstate_strm i) k t.strm st := I.good.live
  have hL : Live H (.in_gzstate_strm i) k t.strm st :=
    ⟨by simp [ZStreamRef.get, hs], hkH, hLW.zst, hLW.back, hLW.mode, hLW.zalloc, hLW.zfree⟩
  have hfree : t.strm.zfree = .fn "zcfree" := I.alloc.2
  have hwin := windowBlock I.good.inv.win
  have hwinH : st.window = .null ∨ ∃ b a, st.window = .ref (.blk b) 0 ∧ H.bytes b = some a ∧ H.ro b = false :=
    hwin
  have hrun := inflateReset_run hL hfree (Or.inr hwinH)
  have hrunW := inflateReset_run hLW hfree (Or.inr hwin)
  -- the pieces of the result
  generalize hz1 : resetKeepStream t.strm (resetPre st) = z1 at hrun hrunW
  generalize hst1 : resetKeepState k (resetPre st) = st1 at hrun hrunW
  have z1in : z1.avail_in = t.strm.avail_in ∧ z1.next_in = t.strm.next_in ∧ z1.state = t.strm.state := by
    subst hz1; exact ⟨rfl, rfl, rfl⟩
  have z1msg : z1.msg = .null := by subst hz1; rfl
  have st1f : st1.head = none ∧ st1.mode = HEAD ∧ st1.bits = 0 ∧ st1.last = 0 ∧
      st1.window = (resetPre st).window := by
    subst hst1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hB : ∀ b, (resetHeap H st).bytes b =
      if st.wbits ≠ st.reqbits ∧ st.window = .ref (.blk b) 0 then none else H.bytes b := resetHeap_bytes H st
  have hBW : (resetHeap (putGz H i (clearOut t)) st).bytes = (resetHeap H st).bytes := by
    unfold resetHeap
    split
    · unfold freeWin; split <;> rfl
    · rfl
  generalize hBdef : (resetHeap H st).bytes = B at hB hBW
  have eRH : resetHeap H st = { H with bytes := B } := by rw [resetHeap_eq, hBdef]
  have eRW : resetHeap (putGz H i (clearOut t)) st = { putGz H i (clearOut t) with bytes := B } := by
    rw [resetHeap_eq, hBW]
  rw [eRH] at hrun
  rw [eRW] at hrunW
  let t1 : GzState := { t with strm := z1 }
  let t2 : GzState := { t1 with how := GZIP, junk := f t1.junk, direct := 0 }
  let H1 : Heap := { H with bytes := B, gzstates := upd H.gzstates i (some t1), istates := upd H.istates k (some st1) }
  have eH1 : setI ((ZStreamRef.in_gzstate_strm i).put { H with bytes := B } z1) k st1 = H1 := by
    simp [setI, ZStreamRef.put, hs, H1, t1]
  rw [eH1] at hrun
  have hH1 : H1.gzstates i = some t1 := by simp [H1]
  let Hx : Heap := { H with bytes := B, gzstates := upd H.gzstates i (some t2), istates := upd H.istates k (some st1) }
  have eHx : Zlib.Gzlib.Spec.setS H1 i t2 = Hx := by simp [Zlib.Gzlib.Spec.setS, H1, Hx, upd_upd]
  have run : lookGzip i f fs H = .ok ((0, fs), Hx) := by
    unfold lookGzip
    have hr' : (StateT.lift (Zlib.Inflate.inflateReset (strmOf (some (.tab i)))) : G Int32) fs H =
        .ok ((Z_OK, fs), H1) := by
      rw [g_lift_app, strmOf_tab]
      rw [show Zlib.Inflate.inflateReset (some (.in_gzstate_strm i)) H = .ok (Z_OK, H1) from hrun]
    have hu' : (StateT.lift (updS (some (.tab i)) fun s => { s with how := GZIP, junk := f s.junk, direct := 0 }) :
        G Unit) fs H1 = .ok (((), fs), Hx) := by
      rw [g_lift_app, updS_run hH1, ← eHx]
    simp only [g_bind_app, hr', hu', g_pure_app]
  have hHx : Hx.gzstates i = some t2 := by simp [Hx]
  -- the old world and the new one
  let W : Heap := putGz H i (clearOut t)
  let V : Heap := putGz Hx i (clearOut t2)
  have gW : (gzStrm i).get W = some t.strm := by simp [ZStreamRef.get, gzStrm, W, putGz, clearOut]
  have gV : (gzStrm i).get V = some z1 := by simp [ZStreamRef.get, gzStrm, V, putGz, clearOut, t2, t1]
  have hkW : W.istates k = some st := hk
  have hkV : V.istates k = some st1 := by simp [V, Hx, putGz]
  have soW : ∀ b, StreamOwned W (gzStrm i) b ↔ b = k ∨ st.window = .ref (.blk b) 0 := by
    intro b
    constructor
    · rintro ⟨z, hz, ⟨k0, s0, hk0, hs0, ho⟩ | ⟨k0, d0, hk0, -, -⟩⟩
      · rw [gW] at hz; cases hz
        rw [hzst'] at hk0; cases hk0
        rw [hkW] at hs0; cases hs0
        exact ho
      · rw [gW] at hz; cases hz
        rw [hzst'] at hk0; cases hk0
    · intro ho
      exact ⟨t.strm, gW, Or.inl ⟨k, st, hzst', hkW, ho⟩⟩
  have soV : ∀ b, StreamOwned V (gzStrm i) b ↔ b = k ∨ (st.wbits = st.reqbits ∧ st.window = .ref (.blk b) 0) := by
    intro b
    have hw1 : st1.window = if st.wbits = st.reqbits then st.window else .null := by
      rw [st1f.2.2.2.2, look_resetPre_window]
    constructor
    · rintro ⟨z, hz, ⟨k0, s0, hk0, hs0, ho⟩ | ⟨k0, d0, hk0, -, -⟩⟩
      · rw [gV] at hz; cases hz
        rw [z1in.2.2, hzst'] at hk0; cases hk0
        rw [hkV] at hs0; cases hs0
        rcases ho with e | e
        · exact Or.inl e
        · right
          rw [hw1] at e
          by_cases hw : st.wbits = st.reqbits
          · rw [if_pos hw] at e; exact ⟨hw, e⟩
          · rw [if_neg hw] at e; cases e
      · rw [gV] at hz; cases hz
        rw [z1in.2.2, hzst'] at hk0; cases hk0
    · intro ho
      refine ⟨z1, gV, Or.inl ⟨k, st1, by rw [z1in.2.2]; exact hzst', hkV, ?_⟩⟩
      rcases ho with e | ⟨hw, e⟩
      · exact Or.inl e
      · exact Or.inr (by rw [hw1, if_pos hw]; exact e)
  have soH : ∀ b, StreamOwned H (gzStrm i) b ↔ StreamOwned W (gzStrm i) b := by
    intro b
    have g1 : (gzStrm i).get H = (gzStrm i).get W := by
      rw [gW]; simp [ZStreamRef.get, gzStrm, hs]
    unfold StreamOwned
    rw [g1]
    rfl
  -- the window block is a byte block, distinct from the state and the record
  have winBlk : ∀ b, st.window = .ref (.blk b) 0 → ∃ a, H.bytes b = some a := by
    intro b e
    rcases hwinH with n | ⟨b', a, e', ha, -⟩
    · rw [n] at e; cases e
    · rw [e] at e'; cases e'; exact ⟨a, ha⟩
  have winNe : ∀ b, st.window = .ref (.blk b) 0 → b ≠ k ∧ b ≠ i := by
    intro b e
    obtain ⟨a, ha⟩ := winBlk b e
    obtain ⟨-, -, -, -, h5, h6⟩ := uniq_bytes_all c.uniq (W := W) (b := b) (a := a) ha
    refine ⟨fun x => ?_, fun x => ?_⟩
    · subst x; rw [hkW] at h5; cases h5
    · subst x; simp [W, putGz] at h6
  have hki : k ≠ i := by
    intro x
    have hu0 := c.uniq i
    have g0 : W.gzstates i = some (clearOut t) := by simp [W, putGz]
    rw [x] at hkW
    rw [g0, hkW] at hu0
    simp only [Zlib.Gzlib.Spec.cnt_some] at hu0
    omega
  have ptrNotWin : ∀ p, p ∈ ownedPtrs (clearOut t) → ∀ b, p = .ref (.blk b) 0 → ¬ st.window = .ref (.blk b) 0 := by
    intro p hp b e hw
    have := (c.distinct.2 p hp b (by rw [e]; rfl)).2
    exact this ((soW b).2 (Or.inr hw))
  have memP : ∀ p, (p = t.path ∨ p = t.msg ∨ p = t.«in» ∨ p = t.out) → p ∈ ownedPtrs (clearOut t) := by
    intro p hp
    unfold ownedPtrs
    rw [if_pos hszc, if_pos (Or.inl hmc)]
    rcases hp with e | e | e | e <;> subst e <;> simp [clearOut]
  -- the new world keeps the invariant
  have frWV : Frame W V (fun b => b = i ∨ StreamOwned W (gzStrm i) b) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hno
    have hbi : b ≠ i := fun e => hno (Or.inl e)
    have hbk : b ≠ k := fun e => hno (Or.inr ((soW b).2 (Or.inl e)))
    have hbw : ¬ st.window = .ref (.blk b) 0 := fun e => hno (Or.inr ((soW b).2 (Or.inr e)))
    refine ⟨?_, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · show B b = H.bytes b
      rw [hB b, if_neg (fun hc => hbw hc.2)]
    · show upd H.istates k (some st1) b = H.istates b
      rw [upd_ne _ _ _ _ hbk]
    · show upd (upd H.gzstates i (some t2)) i (some (clearOut t2)) b = upd H.gzstates i (some (clearOut t)) b
      rw [upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi]
  have sownV : ∀ b, StreamOwned V (gzStrm i) b → StreamOwned W (gzStrm i) b ∧ V.live b := by
    intro b ho
    rcases (soV b).1 ho with e | ⟨hw, e⟩
    · subst e
      refine ⟨(soW b).2 (Or.inl rfl), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))⟩
      rw [hkV]; exact Option.some_ne_none _
    · refine ⟨(soW b).2 (Or.inr e), Or.inl ?_⟩
      show B b ≠ none
      rw [hB b, if_neg (fun hc => hc.1 hw)]
      obtain ⟨a, ha⟩ := winBlk b e
      rw [ha]; exact Option.some_ne_none _
  obtain ⟨-, freshV, uniqV, globalsV, fitV⟩ := sub_heap (W := W) (V := V)
    (fun b => by
      show B b = H.bytes b ∨ B b = none
      rw [hB b]; split
      · exact Or.inr rfl
      · exact Or.inl rfl)
    rfl rfl rfl rfl
    (fun b => by
      show (upd H.istates k (some st1) b).isSome = (H.istates b).isSome
      by_cases e : b = k
      · subst e; rw [hkH]; simp
      · rw [upd_ne _ _ _ _ e])
    (fun b => by
      show (upd (upd H.gzstates i (some t2)) i (some (clearOut t2)) b).isSome =
        (upd H.gzstates i (some (clearOut t)) b).isSome
      by_cases e : b = i
      · subst e; simp
      · rw [upd_ne _ _ _ _ e, upd_ne _ _ _ _ e, upd_ne _ _ _ _ e])
    rfl rfl rfl
  have freshV' := freshV c.fresh
  have uniqV' := uniqV c.uniq
  have globalsV' := globalsV c.globals
  have fitV' := fitV c.fit
  -- the codec history: the reset as a step, then the scalar write as a rebuffer
  let W1 : Heap := setI ((ZStreamRef.in_gzstate_strm i).put { W with bytes := B } z1) k st1
  have hexec : Call.execute (.inflateReset (some (gzStrm i))) default W = .ok ((Z_OK, default), W1) := by
    show heapCall (Zlib.Inflate.inflateReset (some (gzStrm i))) default W = _
    unfold heapCall
    rw [show Zlib.Inflate.inflateReset (some (gzStrm i)) W = .ok (Z_OK, W1) from hrunW]
    rfl
  have reach1 : StreamReachable .inflate W1 (gzStrm i) :=
    StreamReachable.step (call := .inflateReset (some (gzStrm i))) reach (fun _ => c.fit) ⟨rfl, rfl⟩ trivial hexec
  have eW1 : W1 = { H with bytes := B, gzstates := upd H.gzstates i (some { (clearOut t) with strm := z1 }), istates := upd H.istates k (some st1) } := by
    (simp [W1, W, setI, ZStreamRef.put, putGz, upd_upd]) <;> rfl
  have g1 : (gzStrm i).get W1 = some z1 := by
    rw [eW1]; simp [ZStreamRef.get, gzStrm]
  have soW1 : ∀ b, StreamOwned W1 (gzStrm i) b ↔ StreamOwned V (gzStrm i) b := by
    intro b
    have ei : W1.istates = V.istates := by rw [eW1]; rfl
    have ed : W1.dstates = V.dstates := by rw [eW1]; rfl
    unfold StreamOwned
    rw [g1, gV, ei, ed]
  have hreb : Rebuffer W1 V (gzStrm i) := by
    refine ⟨freshV', uniqV', globalsV', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, z1, z1, g1, gV, rfl⟩
    · rw [eW1]; rfl
    · rw [eW1]; rfl
    · rw [eW1]; rfl
    · rw [eW1]; exact Nat.le_refl _
    · rw [eW1]; exact Nat.le_refl _
    · intro b _ hc
      have ho : StreamOwned V (gzStrm i) b := (soW1 b).1 (Classical.byContradiction hc)
      have hbi : b ≠ i := by
        rcases (soV b).1 ho with e | ⟨-, e⟩
        · subst e; exact hki
        · exact (winNe b e).2
      rw [eW1]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
      show upd (upd H.gzstates i (some t2)) i (some (clearOut t2)) b = upd H.gzstates i _ b
      rw [upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi]
  have codecV : StreamReachable .inflate V (gzStrm i) ∧
      ∃ z k st, (gzStrm i).get V = some z ∧ z.state = some (.inflate k) ∧ V.istates k = some st ∧
        st.head = none :=
    ⟨StreamReachable.rebuffer reach1 hreb (fun _ => fitV'), z1, k, st1, gV,
      by rw [z1in.2.2]; exact hzst', hkV, st1f.1⟩
  have invV : GzInv V i (clearOut t2) := by
    refine GzInv.rebuild inv hmc hszc rfl rfl (by simp [V, putGz])
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨Or.inr (Or.inr rfl), fun e => absurd (show GZIP = GZ_COPY from e) (by decide), fun _ => rfl,
        Or.inr (Or.inl rfl), ?_⟩
      ?_ ?_ frWV sownV freshV' uniqV' globalsV' fitV' codecV
    · show f t.junk = -1 ∨ f t.junk = 0 ∨ f t.junk = 1
      rcases hf t.junk with e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
    · show z1.avail_in = 0 ∨ ∃ a, z1.next_in = padv t.«in» a ∧ a + z1.avail_in.toNat ≤ t.size.toNat
      rw [z1in.1, z1in.2.1]
      exact rd.input
    · intro ha he
      show z1.avail_in = 0
      rw [z1in.1]
      exact rd.againEof ha he
  have hu2 : GzInvUpToOutput Hx i t2 := ⟨hHx, invV⟩
  -- the post-condition
  have gHx : (gzStrm i).get Hx = some z1 := by simp [ZStreamRef.get, gzStrm, Hx, t2, t1]
  have soHx : ∀ b, StreamOwned Hx (gzStrm i) b ↔ StreamOwned V (gzStrm i) b := by
    intro b
    have ei : Hx.istates = V.istates := rfl
    have ed : Hx.dstates = V.dstates := rfl
    unfold StreamOwned
    rw [gHx, gV, ei, ed]
  let D : Nat → Prop := fun b => st.wbits ≠ st.reqbits ∧ st.window = .ref (.blk b) 0
  have frH : Frame H Hx (GzOwned H i t) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hno
    have hbi : b ≠ i := fun e => hno (Or.inl e)
    have hso : ¬ StreamOwned W (gzStrm i) b := fun so =>
      hno (Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inr ((soH b).2 so)⟩⟩)))
    have hbk : b ≠ k := fun e => hso ((soW b).2 (Or.inl e))
    have hbw : ¬ st.window = .ref (.blk b) 0 := fun e => hso ((soW b).2 (Or.inr e))
    refine ⟨?_, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · show B b = H.bytes b
      rw [hB b, if_neg (fun hc => hbw hc.2)]
    · show upd H.istates k (some st1) b = H.istates b
      rw [upd_ne _ _ _ _ hbk]
    · show upd H.gzstates i (some t2) b = H.gzstates b
      rw [upd_ne _ _ _ _ hbi]
  have hD : ∀ b, D b → GzOwned H i t b := fun b hd =>
    Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inr ((soH b).2 ((soW b).2 (Or.inr hd.2)))⟩⟩))
  have notD : ∀ b, (t.path = .ref (.blk b) 0 ∨ t.msg = .ref (.blk b) 0 ∨ t.«in» = .ref (.blk b) 0 ∨
      t.out = .ref (.blk b) 0) → ¬ D b := by
    intro b hp hd
    rcases hp with e | e | e | e
    · exact ptrNotWin _ (memP _ (Or.inl rfl)) b e hd.2
    · exact ptrNotWin _ (memP _ (Or.inr (Or.inl rfl))) b e hd.2
    · exact ptrNotWin _ (memP _ (Or.inr (Or.inr (Or.inl rfl)))) b e hd.2
    · exact ptrNotWin _ (memP _ (Or.inr (Or.inr (Or.inr rfl)))) b e hd.2
  have own : ∀ b, GzOwned Hx i t2 b ↔ (GzOwned H i t b ∧ ¬ D b) ∨ False := by
    intro b
    rw [or_false]
    constructor
    · rintro (e | e | e | ⟨-, e | ⟨-, e | so⟩⟩)
      · subst e
        exact ⟨Or.inl rfl, fun hd => (winNe b hd.2).2 rfl⟩
      · exact ⟨Or.inr (Or.inl e), notD b (Or.inl e)⟩
      · exact ⟨Or.inr (Or.inr (Or.inl e)), notD b (Or.inr (Or.inl e))⟩
      · exact ⟨Or.inr (Or.inr (Or.inr ⟨hsz, Or.inl e⟩)), notD b (Or.inr (Or.inr (Or.inl e)))⟩
      · exact ⟨Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inl e⟩⟩)), notD b (Or.inr (Or.inr (Or.inr e)))⟩
      · have so' := (soHx b).1 so
        refine ⟨Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inr ((soH b).2 (sownV b so').1)⟩⟩)), ?_⟩
        rcases (soV b).1 so' with e | ⟨hw, -⟩
        · subst e; intro hd; exact (winNe b hd.2).1 rfl
        · intro hd; exact hd.1 hw
    · rintro ⟨e | e | e | ⟨-, e | ⟨-, e | so⟩⟩, hd⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inl e⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inr rfl, Or.inl e⟩⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inr rfl, Or.inr ((soHx b).2 ((soV b).2 ?_))⟩⟩))
        rcases (soW b).1 ((soH b).1 so) with e | e
        · exact Or.inl e
        · refine Or.inr ⟨Classical.byContradiction fun hw => hd ⟨hw, e⟩, e⟩
  have hlive : ∀ b, Hx.live b ↔ (H.live b ∧ ¬ D b) ∨ False := by
    intro b
    rw [or_false]
    by_cases hd : D b
    · obtain ⟨a, ha⟩ := winBlk b hd.2
      obtain ⟨hbk, hbi⟩ := winNe b hd.2
      obtain ⟨u1, u2, u3, u4, u5, u6⟩ := uniq_bytes_all c.uniq (W := W) (b := b) (a := a) ha
      have u6' : H.gzstates b = none := by
        have : upd H.gzstates i (some (clearOut t)) b = none := u6
        rwa [upd_ne _ _ _ _ hbi] at this
      have hBb : B b = none := by rw [hB b, if_pos hd]
      have hl : ¬ Hx.live b := by
        show ¬ (B b ≠ none ∨ H.words b ≠ none ∨ H.streams b ≠ none ∨ H.gzheaders b ≠ none ∨ H.dstates b ≠ none ∨
          upd H.istates k (some st1) b ≠ none ∨ upd H.gzstates i (some t2) b ≠ none)
        rw [upd_ne _ _ _ _ hbk, upd_ne _ _ _ _ hbi, hBb]
        have v1 : H.words b = none := u1
        have v2 : H.streams b = none := u2
        have v3 : H.gzheaders b = none := u3
        have v4 : H.dstates b = none := u4
        have v5 : H.istates b = none := u5
        rw [v1, v2, v3, v4, v5, u6']
        simp
      exact ⟨fun x => absurd x hl, fun x => absurd hd x.2⟩
    · have hBb : B b = H.bytes b := by rw [hB b, if_neg hd]
      have i1 : (upd H.istates k (some st1) b ≠ none) ↔ (H.istates b ≠ none) := by
        by_cases e : b = k
        · subst e; rw [hkH]; simp
        · rw [upd_ne _ _ _ _ e]
      have g1 : (upd H.gzstates i (some t2) b ≠ none) ↔ (H.gzstates b ≠ none) := by
        by_cases e : b = i
        · subst e; rw [hs]; simp
        · rw [upd_ne _ _ _ _ e]
      show (B b ≠ none ∨ H.words b ≠ none ∨ H.streams b ≠ none ∨ H.gzheaders b ≠ none ∨ H.dstates b ≠ none ∨
          upd H.istates k (some st1) b ≠ none ∨ upd H.gzstates i (some t2) b ≠ none) ↔ (H.live b ∧ ¬ D b)
      rw [hBb, i1, g1]
      exact ⟨fun x => ⟨x, hd⟩, fun x => x.1⟩
  have post : GzPost H i t [] fs Hx GzInvUpToOutput :=
    post_step (D := D) (C := fun _ => False) hu hu2 hfs rfl rfl frH hD (fun _ f => f.elim) own hlive
  exact ⟨Hx, t2, run, hHx, post, rfl, z1in.1, z1in.2.1,
    ⟨k, st1, by rw [z1in.2.2]; exact hzst', by simp [Hx], st1f.2.1, st1f.2.2.1, st1f.2.2.2.1⟩, z1msg⟩

end reset

/-- Replacing the array of a byte block by one of the same size keeps the live blocks, freshness, uniqueness, the
globals and the object-size bound. -/
theorem replace_bytes {W : Heap} {b : Nat} {x y : Array UInt8} (hy : W.bytes b = some y) (hsz : x.size = y.size) :
    (∀ c, ({ W with bytes := upd W.bytes b (some x) } : Heap).live c ↔ W.live c) ∧
    (Fresh W → Fresh { W with bytes := upd W.bytes b (some x) }) ∧
    (Zlib.Gzlib.Spec.Uniq W → Zlib.Gzlib.Spec.Uniq { W with bytes := upd W.bytes b (some x) }) ∧
    (LibraryGlobals W → LibraryGlobals { W with bytes := upd W.bytes b (some x) }) ∧
    (ZlibF.PlatformMemory.ByteObjectsFit W → ZlibF.PlatformMemory.ByteObjectsFit
      { W with bytes := upd W.bytes b (some x) }) := by
  have hcnt : ∀ c, Zlib.Gzlib.Spec.cnt (upd W.bytes b (some x) c) = Zlib.Gzlib.Spec.cnt (W.bytes c) := by
    intro c
    by_cases e : c = b
    · subst e; simp [hy]
    · rw [upd_ne _ _ _ _ e]
  have hl : ∀ c, ({ W with bytes := upd W.bytes b (some x) } : Heap).live c ↔ W.live c := by
    intro c
    have e1 : (upd W.bytes b (some x) c ≠ none) ↔ (W.bytes c ≠ none) := by
      by_cases e : c = b
      · subst e; simp [hy]
      · rw [upd_ne _ _ _ _ e]
    unfold Heap.live
    show (upd W.bytes b (some x) c ≠ none ∨ _) ↔ _
    rw [e1]
  refine ⟨hl, fun f c hc hlc => f c hc ((hl c).1 hlc), fun u c => ?_, fun g => g, fun f => ?_⟩
  · have := u c
    show Zlib.Gzlib.Spec.cnt (upd W.bytes b (some x) c) + _ + _ + _ + _ + _ + _ ≤ 1
    rw [hcnt c]
    exact this
  · have bound : x.size < ZlibF.PlatformMemory.byteObjectLimit := by
      rw [hsz]; exact f (.blk b) y hy
    exact ZlibF.PlatformMemory.ByteObjectsFit.with_bytes f bound

/-! ## A reader with no buffers -/

section size0
variable {h h' : Heap} {i : Nat} {s s' : GzState}

/-- **A reader with no buffers keeps the invariant** under a change of the record that keeps what the invariant
reads (the dangling `in`, `out` and a stream with no state are free), over a heap that changes only the record. -/
theorem GzInv.size0_rebuild (inv : GzInv h i s) (hm : s.mode = GZ_READ) (hsz : s.size = 0)
    (hxn : s.x.next = .null) (rec : h'.gzstates i = some s')
    (same : s'.path = s.path ∧ s'.msg = s.msg ∧ s'.size = s.size ∧ s'.mode = s.mode ∧ s'.want = s.want ∧
      s'.err = s.err ∧ s'.x = s.x ∧ s'.skip = s.skip ∧ s'.eof = s.eof ∧ s'.past = s.past ∧ s'.again = s.again ∧
      s'.how = s.how ∧ s'.direct = s.direct ∧ s'.junk = s.junk)
    (hst : s'.strm.state = none) (hav : s'.strm.avail_in = 0)
    (fr : Frame h h' (fun b => b = i))
    (fresh : Fresh h') (uniq : Zlib.Gzlib.Spec.Uniq h') (globals : LibraryGlobals h')
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h') :
    GzInv h' i s' := by
  obtain ⟨epath, emsg, esize, emode, ewant, eerr, ex, eskip, eeof, epast, eagain, ehow, edirect, ejunk⟩ := same
  have c := inv.common
  have rd := inv.reader hm
  have hm' : s'.mode = GZ_READ := emode.trans hm
  have hsz' : s'.size = 0 := esize.trans hsz
  have hptrs : ownedPtrs s' = ownedPtrs s := by
    unfold ownedPtrs
    rw [epath, emsg, esize, if_neg (fun x => x hsz), if_neg (fun x => x hsz)]
  have kept : ∀ p, (p = s.path ∨ p = s.msg) → ∀ b, p = .ref (.blk b) 0 →
      h'.bytes b = h.bytes b ∧ h'.ro b = h.ro b ∧ h'.live b := by
    intro p hp b e
    have mem : p ∈ ownedPtrs s := by
      unfold ownedPtrs; rcases hp with x | x <;> subst x <;> simp
    have hbk : blkOf p = some b := by rw [e]; rfl
    have hbi := (c.distinct.2 p mem b hbk).1
    have hl := inv.ptr_live mem hbk
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := fr.2.2.2.2.2 b hl hbi
    refine ⟨e1, e8, ?_⟩
    unfold Heap.live at hl ⊢
    rw [e1, e2, e3, e4, e5, e6, e7]
    exact hl
  have hmalloc : ∀ p n, (p = s.path ∨ p = s.msg) → MallocBuffer h p n → MallocBuffer h' p n := by
    intro p n hp hx
    obtain ⟨b, a, e, hb, hr, hn⟩ := hx
    obtain ⟨k1, k2, -⟩ := kept p hp b e
    exact ⟨b, a, e, by rw [k1]; exact hb, by rw [k2]; exact hr, hn⟩
  have noSO : ∀ b, ¬ StreamOwned h' (gzStrm i) b := noCodec_owned rec hst
  have hx0 : s.x.have = 0 := (rd.unalloc hsz).1
  refine ⟨?_, fun _ => ?_, fun hw => absurd (hm'.symm.trans hw) (by decide)⟩
  · exact {
      record := rec
      mode := Or.inl hm'
      fresh := fresh
      uniq := uniq
      globals := globals
      fit := fit
      path := by
        obtain ⟨p, hc, hmb⟩ := c.path
        refine ⟨p, ?_, by rw [epath]; exact hmalloc _ _ (Or.inl rfl) hmb⟩
        obtain ⟨pb, a, hp, -, -, -⟩ := hmb
        rw [epath, hp]
        rw [hp] at hc
        exact (cstring_blk_congr (kept _ (Or.inl rfl) pb hp).1).2 hc
      msg := by
        rw [emsg]
        rcases c.msg with hn | ⟨m, hc, hmb⟩
        · exact Or.inl hn
        · refine Or.inr ⟨m, ?_, hmalloc _ _ (Or.inr rfl) hmb⟩
          obtain ⟨mb, a, hp, -, -, -⟩ := hmb
          rw [hp]
          rw [hp] at hc
          exact (cstring_blk_congr (kept _ (Or.inr rfl) mb hp).1).2 hc
      memerr := by rw [eerr, emsg]; exact c.memerr
      want := by rw [ewant]; exact c.want
      size := by rw [esize, ewant]; exact c.size
      distinct := by
        rw [hptrs]
        exact ⟨c.distinct.1, fun p hp b hb => ⟨(c.distinct.2 p hp b hb).1, noSO b⟩⟩
      live := by
        intro b ho
        rcases ho with e | e | e | ⟨hz, -⟩
        · subst e; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [rec]; intro x; cases x))))))
        · exact (kept _ (Or.inl rfl) b (by rw [← epath]; exact e)).2.2
        · exact (kept _ (Or.inr rfl) b (by rw [← emsg]; exact e)).2.2
        · exact absurd hsz' hz
      pos := by rw [ex, eskip]; exact c.pos
      next := fun hh => absurd (by rw [ex]; exact hx0) hh
      nullHave := fun _ => by rw [ex]; exact hx0
      recordFree := noSO i }
  · exact {
      how := by rw [ehow]; exact rd.how
      copyDirect := by rw [ehow, edirect]; exact rd.copyDirect
      gzipDirect := by rw [ehow, edirect]; exact rd.gzipDirect
      direct := by rw [edirect]; exact rd.direct
      junk := by rw [ejunk]; exact rd.junk
      flags := by rw [eeof, epast, eagain]; exact rd.flags
      unalloc := fun _ => ⟨by rw [ex]; exact hx0, hav, by rw [ehow]; exact (rd.unalloc hsz).2.2.1, hst⟩
      bufs := fun hz => absurd hsz' hz
      input := Or.inl hav
      output := fun hh => absurd (by rw [ex]; exact hx0) hh
      codec := fun hz => absurd hsz' hz
      posHave := by rw [ex]; exact rd.posHave
      againSize := fun _ => by rw [eagain]; exact rd.againSize hsz
      haveSkip := fun hh => absurd (by rw [ex]; exact hx0) hh
      againEof := fun _ _ => hav }

end size0

/-! ## `gz_error` inside `gz_look` -/

/-- **`gz_error(state, err, literal)`** keeps the invariant up to the buffered output, with the post-condition. -/
theorem err_post {H : Heap} {i : Nat} {s : GzState} (fs : Fs) (hfs : FileSystem fs) (hu : GzInvUpToOutput H i s)
    (err : Int32) {msg : BPtr} (hmsg : ∃ t, CString H msg t) (hroot : ∀ b, ¬ ByteRoot msg b) :
    ∃ after s', Zlib.Gzlib.gz_error (gzSt i) err msg H = .ok ((), after) ∧ after.gzstates i = some s' ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = err ∨ s'.err = Z_MEM_ERROR) ∧
      GzPost H i s [] fs after GzInvUpToOutput := by
  have hs : H.gzstates i = some s := hu.1
  have inv : GzInv (putGz H i (clearOut s)) i (clearOut s) := hu.2
  obtain ⟨t, ct⟩ := hmsg
  obtain ⟨after, s4, run4, hs4, shape4, post4⟩ := gz_error_upToOutput hu err msg
    (Or.inr ⟨t, ct, fun b hb => (hroot b hb).elim⟩)
  obtain ⟨inv4, -, herr4, fr4, lc4, -, -, ng4, keep4⟩ := post4
  have liveW : ∀ b, (putGz H i (clearOut s)).live b ↔ H.live b := fun b => putGz_live hs b
  have liveA : ∀ b, (putGz after i (clearOut s4)).live b ↔ after.live b := fun b => putGz_live hs4 b
  have ownA : ∀ b, GzOwned (putGz after i (clearOut s4)) i (clearOut s4) b ↔ GzOwned after i s4 b :=
    putGz_owned (s' := clearOut s4) hs4 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ownW : ∀ b, GzOwned (putGz H i (clearOut s)) i (clearOut s) b ↔ GzOwned H i s b :=
    putGz_owned (s' := clearOut s) hs ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have msgOld : ∀ b, blkOf s.msg = some b → GzOwned H i s b := by
    intro b hb
    rcases inv.common.msg with hn | ⟨_, _, mb, _, hp, _⟩
    · have : s.msg = .null := hn
      rw [this] at hb; cases hb
    · have hp' : s.msg = .ref (.blk mb) 0 := hp
      rw [hp'] at hb; cases hb; exact Or.inr (Or.inr (Or.inl hp'))
  have msgNew : ∀ b, blkOf s4.msg = some b → GzOwned after i s4 b := by
    intro b hb
    rcases inv4.common.msg with hn | ⟨_, _, mb, _, hp, _⟩
    · have : s4.msg = .null := hn
      rw [this] at hb; cases hb
    · have hp' : s4.msg = .ref (.blk mb) 0 := hp
      rw [hp'] at hb; cases hb; exact Or.inr (Or.inr (Or.inl hp'))
  have live4 : ∀ b, GzOwned after i s4 b → after.live b := fun b ho =>
    (liveA b).1 (inv4.common.live b ((ownA b).2 ho))
  have frA : Frame H after (GzOwned H i s) := by
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fr4
    refine ⟨f1, f2, f3, f4, f5, fun b hl hno => ?_⟩
    have hbi : b ≠ i := fun e => hno (Or.inl e)
    have hbm : ¬ blkOf s.msg = some b := fun e => hno (msgOld b e)
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := f6 b ((liveW b).2 hl) (fun x => x.elim hbi hbm)
    refine ⟨e1, e2, e3, e4, e5, e6, ?_, e8⟩
    have e7' : upd after.gzstates i (some (clearOut s4)) b = upd H.gzstates i (some (clearOut s)) b := e7
    rw [upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi] at e7'
    exact e7'
  have hshape : s4 = { s with err := s4.err, msg := s4.msg } := shape4
  refine ⟨after, s4, run4, hs4, hshape, herr4.elim Or.inl (fun e => Or.inr e.1), hfs, s4, ⟨hs4, inv4⟩,
    by rw [hshape], by rw [hshape], ⟨frA, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · intro b
    have L := lc4 b
    simp only [liveA, liveW] at L
    show after.live b ↔ (H.live b ∧ ¬ (GzOwned H i s b ∧ ¬ GzOwned after i s4 b)) ∨
      (GzOwned after i s4 b ∧ ¬ H.live b)
    constructor
    · intro hl
      rcases L.1 hl with ⟨hl, hno⟩ | ⟨hn, hnl⟩
      · exact Or.inl ⟨hl, fun ⟨o, no4⟩ => no4 ((ownA b).1 (keep4 b ((ownW b).2 o) hno))⟩
      · exact Or.inr ⟨msgNew b hn, hnl⟩
    · rintro (⟨hl, hk⟩ | ⟨o4, -⟩)
      · by_cases o4 : GzOwned after i s4 b
        · exact live4 b o4
        · exact L.2 (Or.inl ⟨hl, fun hm => hk ⟨msgOld b hm, o4⟩⟩)
      · exact live4 b o4
  · intro b ho
    rcases ng4 b ((ownA b).2 ho) with o | n
    · exact Or.inl ((ownW b).1 o)
    · exact Or.inr (fun hl => n ((liveW b).2 hl))

/-! ## The copy path -/

theorem look_GZ_OFF_MAX_toInt : GZ_OFF_MAX.toInt = 9223372036854775807 := by decide

/-- `gz_room(state, max)` (patch 0004): no fault, no change; at most `max`, keeps `x.pos + n ≤ GZ_OFF_MAX`, and `0`
only for `max = 0` or `x.pos = GZ_OFF_MAX`. -/
theorem look_room_run {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (max : UInt32) :
    ∃ n, Zlib.Gzread.gz_room (gzSt i) max h = .ok (n, h) ∧ n.toNat ≤ max.toNat ∧
      s.x.pos.toInt + n.toNat ≤ 9223372036854775807 ∧ (n = 0 → max = 0 ∨ s.x.pos.toInt = 9223372036854775807) := by
  have hpl := s.x.pos.toInt_lt
  have hpg := s.x.pos.le_toInt
  have hml := max.toNat_lt
  unfold Zlib.Gzread.gz_room
  simp only [gzSt, bind_app, pure_app, ldS_eq, hs]
  by_cases hp : s.x.pos > 0
  · have hp' : 0 < s.x.pos.toInt := by have := (Int64.lt_iff_toInt_lt).1 hp; simpa using this
    have hsub := i64sub_run GZ_OFF_MAX s.x.pos (by rw [look_GZ_OFF_MAX_toInt]; omega)
      (by rw [look_GZ_OFF_MAX_toInt]; omega) h
    rw [look_GZ_OFF_MAX_toInt] at hsub
    simp only [hp, ite_true, bind_app, hsub]
    have hd : (Int64.ofInt (9223372036854775807 - s.x.pos.toInt)).toInt = 9223372036854775807 - s.x.pos.toInt :=
      i64_toInt_ofInt (by omega) (by omega)
    by_cases hlt : Int64.ofInt (9223372036854775807 - s.x.pos.toInt) < u32ToI64 max
    · simp only [hlt, ite_true, pure_app]
      have hlt' := (Int64.lt_iff_toInt_lt).1 hlt
      rw [hd, u32ToI64_toInt] at hlt'
      have h0 : (0 : Int64) ≤ Int64.ofInt (9223372036854775807 - s.x.pos.toInt) := by
        rw [Int64.le_iff_toInt_le, hd]; simp; omega
      have hv : (Int64.ofInt (9223372036854775807 - s.x.pos.toInt)).toUInt64.toUInt32.toNat =
          (9223372036854775807 - s.x.pos.toInt).toNat := by
        rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt, hd]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨_, rfl, by rw [hv]; omega, by rw [hv]; omega, fun hz => Or.inr ?_⟩
      have := congrArg UInt32.toNat hz
      rw [hv] at this
      simp at this
      omega
    · simp only [hlt, Bool.false_eq_true, ite_false, pure_app]
      have hge : ¬ (9223372036854775807 - s.x.pos.toInt < (max.toNat : Int)) := by
        intro hh; apply hlt; rw [Int64.lt_iff_toInt_lt, hd, u32ToI64_toInt]; exact hh
      refine ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz⟩
  · have hp' : s.x.pos.toInt ≤ 0 := by
      have : ¬ (0 : Int64).toInt < s.x.pos.toInt := fun hh => hp ((Int64.lt_iff_toInt_lt).2 hh)
      simp at this; omega
    simp only [hp, Bool.false_eq_true, ite_false, pure_app, decide_false]
    exact ⟨_, rfl, Nat.le_refl _, by omega, fun hz => Or.inl hz⟩

/-- The literal of the refusal of patch 0004 is a C string. -/
theorem look_posov_cstring (H : Heap) {k : Nat} (hk : strIndex "position overflow" = some k) :
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

/-- The record after the copy path: no pending input, `how = COPY`. -/
def copied (u : GzState) : GzState := { u with strm := { u.strm with avail_in := 0 }, how := GZ_COPY }

/-- **The end of the copy path**, `strm->avail_in = 0; state->how = COPY;`, on a reader with buffers: the two steps
and the post-condition. -/
theorem copyTail_run {G0 : Heap} {i : Nat} {u : GzState} (fs : Fs) (hu : GzInvUpToOutput G0 i u)
    (hm : u.mode = GZ_READ) (hsz : u.size ≠ 0) (hfs : FileSystem fs) (hd : u.direct ≠ -1) :
    (StateT.lift (updZ (strmOf (some (.tab i))) fun z => { z with avail_in := 0 }) : G Unit) fs G0 =
        .ok (((), fs), Zlib.Gzlib.Spec.setS G0 i { u with strm := { u.strm with avail_in := 0 } }) ∧
      (StateT.lift (updS (some (.tab i)) fun s => { s with how := GZ_COPY }) : G Unit) fs
        (Zlib.Gzlib.Spec.setS G0 i { u with strm := { u.strm with avail_in := 0 } }) =
        .ok (((), fs), { G0 with gzstates := upd G0.gzstates i (some (copied u)) }) ∧
      GzPost G0 i u [] fs { G0 with gzstates := upd G0.gzstates i (some (copied u)) } GzInvUpToOutput := by
  have hs : G0.gzstates i = some u := hu.1
  have inv : GzInv (putGz G0 i (clearOut u)) i (clearOut u) := hu.2
  have hmc : (clearOut u).mode = GZ_READ := hm
  have hszc : (clearOut u).size ≠ 0 := hsz
  have rd := inv.reader hmc
  have c := inv.common
  let u4 : GzState := { u with strm := { u.strm with avail_in := 0 } }
  let Hf : Heap := { G0 with gzstates := upd G0.gzstates i (some (copied u)) }
  have s5 : (StateT.lift (updZ (strmOf (some (.tab i))) fun z => { z with avail_in := 0 }) : G Unit) fs G0 =
      .ok (((), fs), Zlib.Gzlib.Spec.setS G0 i u4) := by
    rw [g_lift_app, strmOf_tab, updZ_run hs]
  have s6 : (StateT.lift (updS (some (.tab i)) fun s => { s with how := GZ_COPY }) : G Unit) fs
      (Zlib.Gzlib.Spec.setS G0 i u4) = .ok (((), fs), Hf) := by
    rw [g_lift_app, updS_run (s := u4) (by simp [Zlib.Gzlib.Spec.setS])]
    (simp [Zlib.Gzlib.Spec.setS, Hf, copied, u4, upd_upd]) <;> rfl
  refine ⟨s5, s6, ?_⟩
  let W : Heap := putGz G0 i (clearOut u)
  have gW : W.gzstates i = some (clearOut u) := by simp [W, putGz]
  let V : Heap := putGz Hf i (clearOut (copied u))
  have eV : V = putGz W i (clearOut (copied u)) := by simp [V, W, Hf, putGz, upd_upd]
  have gzW : (gzStrm i).get W = some u.strm := by simp [ZStreamRef.get, gzStrm, gW, clearOut]
  have gzV : (gzStrm i).get V = some { u.strm with avail_in := 0 } := by
    simp [ZStreamRef.get, gzStrm, V, putGz, clearOut, copied]
  have soVW : ∀ b, StreamOwned V (gzStrm i) b ↔ StreamOwned W (gzStrm i) b := by
    intro b
    have ei : V.istates = W.istates := by rw [eV]; rfl
    have ed : V.dstates = W.dstates := by rw [eV]; rfl
    constructor
    · rintro ⟨z, hz, h1⟩
      rw [gzV] at hz; cases hz
      refine ⟨u.strm, gzW, ?_⟩
      rw [ei, ed] at h1
      exact h1
    · rintro ⟨z, hz, h1⟩
      rw [gzW] at hz; cases hz
      refine ⟨{ u.strm with avail_in := 0 }, gzV, ?_⟩
      rw [ei, ed]
      exact h1
  have liveV : ∀ b, V.live b ↔ W.live b := by rw [eV]; exact putGz_live gW
  have freshV : Fresh V := by rw [eV]; exact putGz_fresh gW c.fresh
  have uniqV : Zlib.Gzlib.Spec.Uniq V := by rw [eV]; exact putGz_uniq gW c.uniq
  have globalsV : LibraryGlobals V := by rw [eV]; exact c.globals
  have fitV : ZlibF.PlatformMemory.ByteObjectsFit V := by rw [eV]; exact putGz_fit c.fit
  have frV : ∀ b, b ≠ i → V.bytes b = W.bytes b ∧ V.words b = W.words b ∧ V.streams b = W.streams b ∧
      V.gzheaders b = W.gzheaders b ∧ V.dstates b = W.dstates b ∧ V.istates b = W.istates b ∧
      V.gzstates b = W.gzstates b ∧ V.ro b = W.ro b := by
    intro b hb
    rw [eV]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hb], rfl⟩
  obtain ⟨reachW, z0, k0, st0, hz0, hzst0, hk0, hhead0⟩ := rd.codec hszc
  have hz0' : z0 = u.strm := by rw [gzW] at hz0; exact (Option.some.inj hz0).symm
  subst hz0'
  have hreb : Rebuffer W V (gzStrm i) := by
    refine ⟨freshV, uniqV, globalsV, ⟨by rw [eV]; rfl, by rw [eV]; rfl, by rw [eV]; rfl, by rw [eV]; exact Nat.le_refl _,
      by rw [eV]; exact Nat.le_refl _, fun b _ hc => ?_⟩, u.strm, { u.strm with avail_in := 0 }, gzW, gzV, rfl⟩
    have hbi : b ≠ i := by
      intro e; subst e
      exact c.recordFree (Classical.byContradiction hc)
    exact frV b hbi
  have invV : GzInv V i (clearOut (copied u)) := by
    refine GzInv.rebuild inv hmc hszc rfl rfl (by simp [V, putGz])
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨Or.inr (Or.inl rfl), fun _ => ?_, fun e => absurd (show GZ_COPY = GZIP from e) (by decide), rd.direct, rd.junk⟩
      (Or.inl rfl) (fun _ _ => rfl)
      ⟨by rw [eV]; rfl, by rw [eV]; rfl, by rw [eV]; rfl, by rw [eV]; exact Nat.le_refl _,
        by rw [eV]; exact Nat.le_refl _, fun b _ hc => frV b (fun e => hc (Or.inl e))⟩
      (fun b ho => ⟨(soVW b).1 ho, (liveV b).2 (c.live b (inv.streamOwned_owned ((soVW b).1 ho)))⟩)
      freshV uniqV globalsV fitV
      ⟨StreamReachable.rebuffer reachW hreb (fun _ => fitV), { u.strm with avail_in := 0 }, k0, st0, gzV,
        hzst0, by rw [eV]; exact hk0, hhead0⟩
    show u.direct = 0 ∨ u.direct = 1
    rcases rd.direct with e | e | e
    · exact absurd e hd
    · exact Or.inl e
    · exact Or.inr e
  have hHf : Hf.gzstates i = some (copied u) := by simp [Hf]
  have hu2 : GzInvUpToOutput Hf i (copied u) := ⟨hHf, invV⟩
  have soHf : ∀ b, StreamOwned Hf (gzStrm i) b ↔ StreamOwned G0 (gzStrm i) b := by
    intro b
    have g1 : (gzStrm i).get Hf = some { u.strm with avail_in := 0 } := by
      simp [ZStreamRef.get, gzStrm, Hf, copied]
    have g2 : (gzStrm i).get G0 = some u.strm := by simp [ZStreamRef.get, gzStrm, hs]
    constructor
    · rintro ⟨z, hz, h1⟩
      rw [g1] at hz; cases hz
      exact ⟨u.strm, g2, h1⟩
    · rintro ⟨z, hz, h1⟩
      rw [g2] at hz; cases hz
      exact ⟨{ u.strm with avail_in := 0 }, g1, h1⟩
  have frH : Frame G0 Hf (GzOwned G0 i u) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hno => ?_⟩
    have hbi : b ≠ i := fun e => hno (Or.inl e)
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, upd_ne _ _ _ _ hbi, rfl⟩
  have own : ∀ b, GzOwned Hf i (copied u) b ↔ (GzOwned G0 i u b ∧ ¬ False) ∨ False := by
    intro b
    simp only [not_false_eq_true, and_true, or_false]
    unfold GzOwned
    rw [show StreamOwned Hf (.in_gzstate_strm i) b ↔ StreamOwned G0 (.in_gzstate_strm i) b from soHf b]
    rfl
  have hlive : ∀ b, Hf.live b ↔ (G0.live b ∧ ¬ False) ∨ False := by
    intro b
    simp only [not_false_eq_true, and_true, or_false]
    have e2 : (upd G0.gzstates i (some (copied u)) b ≠ none) ↔ (G0.gzstates b ≠ none) := by
      by_cases e : b = i
      · subst e; simp [hs]
      · rw [upd_ne _ _ _ _ e]
    unfold Heap.live
    show (G0.bytes b ≠ none ∨ G0.words b ≠ none ∨ G0.streams b ≠ none ∨ G0.gzheaders b ≠ none ∨
      G0.dstates b ≠ none ∨ G0.istates b ≠ none ∨ upd G0.gzstates i (some (copied u)) b ≠ none) ↔ _
    rw [e2]
  exact post_step (D := fun _ => False) (C := fun _ => False) hu hu2 hfs rfl rfl frH
    (fun _ f => f.elim) (fun _ f => f.elim) own hlive

/-- **The copy path** on a reader with buffers and pending input: the input moves to the start of `out`, `x.have`
is the room left before `GZ_OFF_MAX` (all of the input below the limit), `Z_DATA_ERROR` is recorded when input is
left over (patch 0004), `avail_in` is 0, and `how = COPY`. -/
theorem lookCopy_run {H : Heap} {i : Nat} {t : GzState} (fs : Fs) (hu : GzInvUpToOutput H i t)
    (hm : t.mode = GZ_READ) (hsz : t.size ≠ 0) (hfs : FileSystem fs) (hav : t.strm.avail_in ≠ 0)
    (hd : t.direct ≠ -1) :
    ∃ Hf tf room, lookCopy i t.strm fs H = .ok ((0, fs), Hf) ∧ Hf.gzstates i = some tf ∧
      tf = { t with x := { t.x with next := t.out, «have» := room }, strm := { t.strm with avail_in := 0 },
                    how := GZ_COPY, err := tf.err, msg := tf.msg } ∧
      (tf.err = t.err ∨ tf.err = Z_DATA_ERROR ∨ tf.err = Z_MEM_ERROR) ∧
      room.toNat ≤ t.strm.avail_in.toNat ∧ t.x.pos.toInt + room.toNat ≤ 9223372036854775807 ∧
      (room = 0 → t.x.pos.toInt = 9223372036854775807) ∧
      GzPost H i t [] fs Hf GzInvUpToOutput := by
  have hs : H.gzstates i = some t := hu.1
  have inv : GzInv (putGz H i (clearOut t)) i (clearOut t) := hu.2
  have hmc : (clearOut t).mode = GZ_READ := hm
  have hszc : (clearOut t).size ≠ 0 := hsz
  have rd := inv.reader hmc
  have c := inv.common
  obtain ⟨ib, iarr, hin, hib, hiro, hisz⟩ := (rd.bufs hszc).1
  obtain ⟨ob, oarr, hout, hob, horo, hosz⟩ := (rd.bufs hszc).2
  have hin' : t.«in» = .ref (.blk ib) 0 := hin
  have hout' : t.out = .ref (.blk ob) 0 := hout
  have hib' : H.bytes ib = some iarr := hib
  have hob' : H.bytes ob = some oarr := hob
  have hiro' : H.ro ib = false := hiro
  have horo' : H.ro ob = false := horo
  have hisz' : iarr.size = t.size.toNat := hisz
  have hosz' : oarr.size = 2 * t.size.toNat := hosz
  obtain ⟨a, hq, hle⟩ : ∃ a, t.strm.next_in = .ref (.blk ib) a ∧ a + t.strm.avail_in.toNat ≤ t.size.toNat := by
    rcases rd.input with z | ⟨a, hq, hle⟩
    · exact absurd z hav
    · refine ⟨a, ?_, hle⟩
      have hq' : t.strm.next_in = padv t.«in» a := hq
      rw [hq', hin']; simp [padv]
  have hne : ob ≠ ib := by
    have nd := c.distinct.1
    have e : ownedPtrs (clearOut t) = [t.path, t.msg, t.«in», t.out] := by
      unfold ownedPtrs; rw [if_pos hszc, if_pos (Or.inl hmc)]; rfl
    rw [e, hin', hout'] at nd
    intro x; subst x
    have := nd.sublist (List.Sublist.filterMap blkOf (List.Sublist.cons _ (List.Sublist.cons _ (List.Sublist.refl _))))
    simp [blkOf] at this
  -- the run up to `x.have = room`
  let n := t.strm.avail_in.toNat
  let arr' := copyRange oarr iarr 0 a n
  have harr : arr'.size = oarr.size := size_copyRange _ _ _ _ _
  let t1 : GzState := { t with x := { t.x with next := t.out } }
  let H2 : Heap := { Zlib.Gzlib.Spec.setS H i t1 with bytes := upd H.bytes ob (some arr') }
  have hcpy : memcpyB t.out t.strm.next_in n (Zlib.Gzlib.Spec.setS H i t1) = .ok ((), H2) := by
    rw [hout', hq]
    exact memcpyB_blk_ok (h := Zlib.Gzlib.Spec.setS H i t1) hob' hib' horo' hne (by omega) (by omega)
  have g2 : H2.gzstates i = some t1 := by simp [H2, Zlib.Gzlib.Spec.setS]
  obtain ⟨room, hroom, hrle, hrpos, hr0⟩ := look_room_run g2 t.strm.avail_in
  let t3 : GzState := { t1 with x := { t1.x with «have» := room } }
  let H3 : Heap := Zlib.Gzlib.Spec.setS H2 i t3
  have s1 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs H = .ok ((t, fs), H) := by
    rw [g_lift_app, ldS_run hs]
  have s2 : (StateT.lift (updX (some (.tab i)) fun x => { x with next := t.out }) : G Unit) fs H =
      .ok (((), fs), Zlib.Gzlib.Spec.setS H i t1) := by
    rw [g_lift_app, updX_run hs]
  have s3 : (StateT.lift (memcpyB t.out t.strm.next_in t.strm.avail_in.toNat) : G Unit) fs
      (Zlib.Gzlib.Spec.setS H i t1) = .ok (((), fs), H2) := by
    rw [g_lift_app, hcpy]
  have sr : (StateT.lift (Zlib.Gzread.gz_room (some (.tab i)) t.strm.avail_in) : G UInt32) fs H2 =
      .ok ((room, fs), H2) := by
    rw [g_lift_app]
    rw [show Zlib.Gzread.gz_room (some (.tab i)) t.strm.avail_in H2 = .ok (room, H2) from hroom]
  have s4 : (StateT.lift (updX (some (.tab i)) fun x => { x with «have» := room }) : G Unit) fs H2 =
      .ok (((), fs), H3) := by
    rw [g_lift_app, updX_run g2]
  have g3 : H3.gzstates i = some t3 := by simp [H3, Zlib.Gzlib.Spec.setS]
  have l1 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs H3 = .ok ((t3, fs), H3) := by
    rw [g_lift_app, ldS_run g3]
  have l2 : (StateT.lift (ldZ (strmOf (some (.tab i)))) : G ZStream) fs H3 = .ok ((t3.strm, fs), H3) := by
    rw [g_lift_app, strmOf_tab, ldZ_run g3]
  -- the invariant after the copy: the bytes of `out` change, the record changes only in its output
  let W : Heap := putGz H i (clearOut t)
  let W' : Heap := { W with bytes := upd W.bytes ob (some arr') }
  have isData : DataBuf (clearOut t) ob := ⟨hszc, Or.inr ⟨Or.inl hmc, hout⟩⟩
  have dataIff : ∀ b, DataBuf (clearOut t) b → b = ib ∨ b = ob := by
    rintro b ⟨-, e | ⟨-, e⟩⟩
    · have e' : t.«in» = _ := e
      rw [hin'] at e'; cases e'; exact Or.inl rfl
    · have e' : t.out = _ := e
      rw [hout'] at e'; cases e'; exact Or.inr rfl
  have frWW : Frame W W' (fun b => ¬ GzOwned W i (clearOut t) b ∨ DataBuf (clearOut t) b) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hb => ?_⟩
    have hbo : b ≠ ob := fun e => hb (Or.inr (e ▸ isData))
    exact ⟨upd_ne _ _ _ _ hbo, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdata : ∀ b, DataBuf (clearOut t) b →
      (∃ x x', W.bytes b = some x ∧ W'.bytes b = some x' ∧ x'.size = x.size) ∧
      W'.ro b = W.ro b ∧ W'.words b = W.words b ∧ W'.streams b = W.streams b ∧
      W'.gzheaders b = W.gzheaders b ∧ W'.dstates b = W.dstates b ∧ W'.istates b = W.istates b ∧
      W'.gzstates b = W.gzstates b := by
    intro b hb
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rcases dataIff b hb with e | e <;> rw [e]
    · exact ⟨iarr, iarr, hib, by show upd H.bytes ob (some arr') ib = _; rw [upd_ne _ _ _ _ (Ne.symm hne)]; exact hib',
        rfl⟩
    · exact ⟨oarr, arr', hob, by show upd H.bytes ob (some arr') ob = _; simp, harr⟩
  obtain ⟨liveW', freshW', uniqW', globalsW', fitW'⟩ := replace_bytes (W := W) (b := ob) (x := arr') hob harr
  obtain ⟨invW', -⟩ := GzInv.frame_data inv frWW hdata (freshW' c.fresh) (uniqW' c.uniq) (globalsW' c.globals)
    (fitW' c.fit)
  have eW' : putGz H3 i (clearOut t3) = W' := by
    simp [H3, H2, W', W, putGz, Zlib.Gzlib.Spec.setS, upd_upd, clearOut, t3, t1]
  have hu3 : GzInvUpToOutput H3 i t3 := ⟨g3, by rw [eW']; exact invW'⟩
  -- the post-condition up to here
  have frH3 : Frame H H3 (GzOwned H i t) := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hno => ?_⟩
    have hbi : b ≠ i := fun e => hno (Or.inl e)
    have hbo : b ≠ ob := fun e => hno (Or.inr (Or.inr (Or.inr ⟨hsz, Or.inr ⟨Or.inl hm, Or.inl (by rw [e]; exact hout')⟩⟩)))
    refine ⟨upd_ne _ _ _ _ hbo, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    show upd (upd H.gzstates i (some t1)) i (some t3) b = H.gzstates b
    rw [upd_ne _ _ _ _ hbi, upd_ne _ _ _ _ hbi]
  have so3 : ∀ b, StreamOwned H3 (gzStrm i) b ↔ StreamOwned H (gzStrm i) b := by
    intro b
    have g1 : (gzStrm i).get H3 = some t.strm := by simp [ZStreamRef.get, gzStrm, g3, t3, t1]
    have g2' : (gzStrm i).get H = some t.strm := by simp [ZStreamRef.get, gzStrm, hs]
    constructor
    · rintro ⟨z, hz, h1⟩
      rw [g1] at hz; cases hz
      exact ⟨t.strm, g2', h1⟩
    · rintro ⟨z, hz, h1⟩
      rw [g2'] at hz; cases hz
      exact ⟨t.strm, g1, h1⟩
  have own3 : ∀ b, GzOwned H3 i t3 b ↔ (GzOwned H i t b ∧ ¬ False) ∨ False := by
    intro b
    simp only [not_false_eq_true, and_true, or_false]
    unfold GzOwned
    rw [show StreamOwned H3 (.in_gzstate_strm i) b ↔ StreamOwned H (.in_gzstate_strm i) b from so3 b]
  have live3 : ∀ b, H3.live b ↔ (H.live b ∧ ¬ False) ∨ False := by
    intro b
    simp only [not_false_eq_true, and_true, or_false]
    have e1 : (upd H.bytes ob (some arr') b ≠ none) ↔ (H.bytes b ≠ none) := by
      by_cases e : b = ob
      · subst e; simp [hob']
      · rw [upd_ne _ _ _ _ e]
    have e2 : (upd (upd H.gzstates i (some t1)) i (some t3) b ≠ none) ↔ (H.gzstates b ≠ none) := by
      by_cases e : b = i
      · subst e; simp [hs]
      · rw [upd_ne _ _ _ _ e, upd_ne _ _ _ _ e]
    unfold Heap.live
    show (upd H.bytes ob (some arr') b ≠ none ∨ H.words b ≠ none ∨ H.streams b ≠ none ∨ H.gzheaders b ≠ none ∨
      H.dstates b ≠ none ∨ H.istates b ≠ none ∨ upd (upd H.gzstates i (some t1)) i (some t3) b ≠ none) ↔ _
    rw [e1, e2]
  have post3 : GzPost H i t [] fs H3 GzInvUpToOutput :=
    post_step (D := fun _ => False) (C := fun _ => False) hu hu3 hfs rfl rfl frH3
      (fun _ f => f.elim) (fun _ f => f.elim) own3 live3
  have hpos : t.x.pos.toInt + room.toNat ≤ 9223372036854775807 := hrpos
  have hz : room = 0 → t.x.pos.toInt = 9223372036854775807 := fun e => (hr0 e).resolve_left hav
  by_cases hc : room < t.strm.avail_in
  · -- input past the room: `gz_error(state, Z_DATA_ERROR, "position overflow")`
    obtain ⟨k, hk⟩ : ∃ k, strIndex "position overflow" = some k :=
      Option.isSome_iff_exists.mp (by decide +kernel)
    obtain ⟨after, s', grun, hs', shape, herr, post4⟩ := err_post fs hfs hu3 Z_DATA_ERROR
      (look_posov_cstring H3 hk) (fun _ h => h)
    have hu4 : GzInvUpToOutput after i s' := by
      obtain ⟨-, t', inv', -⟩ := post4
      have e := Option.some.inj (inv'.1.symm.trans hs')
      subst e; exact inv'
    have hm4 : s'.mode = GZ_READ := by rw [shape]; exact hm
    have hsz4 : s'.size ≠ 0 := by rw [shape]; exact hsz
    have hd4 : s'.direct ≠ -1 := by rw [shape]; exact hd
    obtain ⟨s5, s6, post5⟩ := copyTail_run fs hu4 hm4 hsz4 hfs hd4
    have sl : (StateT.lift (strLitRef "position overflow") : G BPtr) fs H3 =
        .ok ((.ref (.str k) 0, fs), H3) := by
      rw [g_lift_app, strLitRef_of_index hk]
    have se : (StateT.lift (Zlib.Gzlib.gz_error (some (.tab i)) Z_DATA_ERROR (.ref (.str k) 0)) : G Unit) fs H3 =
        .ok (((), fs), after) := by
      rw [g_lift_app]
      rw [show Zlib.Gzlib.gz_error (some (.tab i)) Z_DATA_ERROR (.ref (.str k) 0) H3 = .ok ((), after) from grun]
    refine ⟨_, copied s', room, ?_, by simp, ?_,
      herr.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr e)),
      hrle, hpos, hz, post_trans (post_trans post3 g3 post4) hs' post5⟩
    · unfold lookCopy
      simp only [g_bind_app, s1, s2, s3, sr, s4, l1, l2]
      split
      · simp only [g_bind_app, sl, se, s5, s6, g_pure_app]
      · rename_i hn; exact absurd hc hn
    · rw [shape]; rfl
  · -- all of the input fits
    obtain ⟨s5, s6, post5⟩ := copyTail_run fs hu3 hm hsz hfs hd
    refine ⟨_, copied t3, room, ?_, by simp, rfl, Or.inl rfl, hrle, hpos, hz, post_trans post3 g3 post5⟩
    unfold lookCopy
    simp only [g_bind_app, s1, s2, s3, sr, s4, l1, l2]
    split
    · rename_i hy; exact absurd hy hc
    · simp only [g_bind_app, s5, s6, g_pure_app]

/-! ## The post-condition of `gz_look` -/

/-- The post-condition of `GzLookSpec` for one result. -/
def LookPost (h : Heap) (i : Nat) (s : GzState) (fs : Fs) (r : Int32) (fs' : Fs) (after : Heap) : Prop :=
  (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInvOut ∧
    (ReadsFinite fs s.fd → ReadsFinite fs' s.fd) ∧
    (ReadsBounded fs s.fd → ReadsBounded fs' s.fd) ∧ BudgetAcc s.fd fs fs' 0 ∧
    ∃ s', after.gzstates i = some s' ∧ FetchKeeps s s' ∧ MsgLit s' ∧
      (ReadsFinite fs s.fd → inputLeft fs' s' ≤ inputLeft fs s) ∧
      (s.err ≠ Z_STREAM_END → s'.err ≠ Z_STREAM_END) ∧
      (s'.size = 0 → s'.err ≠ Z_OK ∧ s'.err ≠ Z_BUF_ERROR) ∧
      (r = 0 → (s'.how = LOOK ∧ s'.x.have = 0 ∧
          ((s'.eof ≠ 0 ∧ s'.strm.avail_in = 0) ∨ BudgetAcc s.fd fs fs' 1)) ∨
        (s'.how = GZIP ∧ s'.x.have = 0 ∧ InflateAtHead after s') ∨
        (s'.how = GZ_COPY ∧ s'.strm.avail_in = 0 ∧
          (s'.x.have ≠ 0 ∨ s'.x.pos.toInt = 9223372036854775807) ∧
          s'.x.pos.toInt + s'.x.have.toNat ≤ 9223372036854775807))

theorem lookPost_of {H : Heap} {i : Nat} {t t' : GzState} {fs fs' : Fs} {r : Int32} {after : Heap}
    (hr : r = 0 ∨ r = -1) (hk : FdsKept fs fs') (post : GzPost H i t [] fs' after GzInvUpToOutput)
    (hrec : after.gzstates i = some t') (hout : OutWindow t')
    (rf : ReadsFinite fs t.fd → ReadsFinite fs' t.fd) (rb : ReadsBounded fs t.fd → ReadsBounded fs' t.fd)
    (bud : BudgetAcc t.fd fs fs' 0)
    (keeps : FetchKeeps t t') (ml : MsgLit t') (il : ReadsFinite fs t.fd → inputLeft fs' t' ≤ inputLeft fs t)
    (er : t.err ≠ Z_STREAM_END → t'.err ≠ Z_STREAM_END) (sz : t'.size = 0 → t'.err ≠ Z_OK ∧ t'.err ≠ Z_BUF_ERROR)
    (res : r = 0 → (t'.how = LOOK ∧ t'.x.have = 0 ∧
          ((t'.eof ≠ 0 ∧ t'.strm.avail_in = 0) ∨ BudgetAcc t.fd fs fs' 1)) ∨
        (t'.how = GZIP ∧ t'.x.have = 0 ∧ InflateAtHead after t') ∨
        (t'.how = GZ_COPY ∧ t'.strm.avail_in = 0 ∧
          (t'.x.have ≠ 0 ∨ t'.x.pos.toInt = 9223372036854775807) ∧
          t'.x.pos.toInt + t'.x.have.toNat ≤ 9223372036854775807)) :
    LookPost H i t fs r fs' after :=
  ⟨hr, hk, post_out post (fun s' hs' => by rw [hrec] at hs'; cases hs'; exact hout), rf, rb, bud, t', hrec, keeps, ml,
    il, er, sz, res⟩

theorem AvailRec.fields {t t1 : GzState} (h : AvailRec t t1) :
    t1.mode = t.mode ∧ t1.fd = t.fd ∧ t1.skip = t.skip ∧ t1.x = t.x ∧ t1.size = t.size ∧ t1.out = t.out ∧
      t1.«in» = t.«in» ∧ t1.how = t.how ∧ t1.direct = t.direct ∧ t1.junk = t.junk := by
  unfold AvailRec at h
  dsimp only at h
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem inputLeft_le {fs : Fs} {t t' : GzState} (hfd : t'.fd = t.fd)
    (hav : t'.strm.avail_in.toNat ≤ t.strm.avail_in.toNat) : inputLeft fs t' ≤ inputLeft fs t := by
  unfold inputLeft
  rw [hfd]
  omega

theorem look_padv_zero (p : BPtr) : padv p 0 = p := by
  cases p <;> simp [padv]

/-- `gz_avail` inside `gz_look`, with its budget facts. -/
theorem avail_step {H : Heap} {i : Nat} {t : GzState} (fs : Fs) (hu : GzInvUpToOutput H i t)
    (hm : t.mode = GZ_READ) (hsz : t.size ≠ 0) (hfs : FileSystem fs) :
    ∃ r1 fs1 H1 t1, Zlib.Gzread.gz_avail (some (.tab i)) fs H = .ok ((r1, fs1), H1) ∧ (r1 = 0 ∨ r1 = -1) ∧
      FdsKept fs fs1 ∧ GzPost H i t [] fs1 H1 GzInvUpToOutput ∧ H1.gzstates i = some t1 ∧ AvailRec t t1 ∧
      (ReadsFinite fs t.fd → ReadsFinite fs1 t.fd ∧ inputLeft fs1 t1 ≤ inputLeft fs t) ∧
      (ReadsBounded fs t.fd → ReadsBounded fs1 t.fd) ∧ (t.err ≠ Z_STREAM_END → t1.err ≠ Z_STREAM_END) ∧
      AvailFs t t1 fs fs1 ∧ AvailFlags r1 t t1 := by
  obtain ⟨-, hex, hpost⟩ := gz_avail_safe i H fs t hu hm hfs hsz
  obtain ⟨r1, fs1, H1, run⟩ := hex trivial
  obtain ⟨hr, hk, post, t1, ht1, hrec, hafs, hafl, -⟩ := hpost _ _ _ run
  obtain ⟨b1, b2, b3⟩ := gz_avail_budget i H fs t hu hm hfs hsz run t1 ht1
  exact ⟨r1, fs1, H1, t1, run, hr, hk, post, ht1, hrec, b1, b2, b3, hafs, hafl⟩

/-- The magic-byte test reads four bytes of the input window and decides. -/
theorem lookMagic_eq {H : Heap} {i : Nat} {z : ZStream} {ib a : Nat} {arr : Array UInt8} (fs : Fs)
    (hq : z.next_in = .ref (.blk ib) a) (hb : H.bytes ib = some arr) (hle : z.avail_in > 3 → a + 4 ≤ arr.size) :
    ∃ g, lookMagic i z fs H = lookFinal i z g fs H := by
  unfold lookMagic
  by_cases h3 : z.avail_in > 3
  · rw [if_pos h3]
    have hl := hle h3
    have r0 : (StateT.lift (index8 z.next_in 0) : G UInt8) fs H = .ok ((arr[a + 0]'(by omega), fs), H) := by
      rw [g_lift_app, hq]
      rw [show index8 (.ref (.blk ib) a) 0 H = .ok (arr[a + 0]'(by omega), H) from index8_ok (i := 0) hb (by omega)]
    have r1 : (StateT.lift (index8 z.next_in 1) : G UInt8) fs H = .ok ((arr[a + 1]'(by omega), fs), H) := by
      rw [g_lift_app, hq]
      rw [show index8 (.ref (.blk ib) a) 1 H = .ok (arr[a + 1]'(by omega), H) from index8_ok (i := 1) hb (by omega)]
    have r2 : (StateT.lift (index8 z.next_in 2) : G UInt8) fs H = .ok ((arr[a + 2]'(by omega), fs), H) := by
      rw [g_lift_app, hq]
      rw [show index8 (.ref (.blk ib) a) 2 H = .ok (arr[a + 2]'(by omega), H) from index8_ok (i := 2) hb (by omega)]
    have r3 : (StateT.lift (index8 z.next_in 3) : G UInt8) fs H = .ok ((arr[a + 3]'(by omega), fs), H) := by
      rw [g_lift_app, hq]
      rw [show index8 (.ref (.blk ib) a) 3 H = .ok (arr[a + 3]'(by omega), H) from index8_ok (i := 3) hb (by omega)]
    simp only [g_bind_app, r0]
    split
    · simp only [g_bind_app, r1]
      split
      · simp only [g_bind_app, r2]
        split
        · simp only [g_bind_app, r3]
          split
          · exact ⟨true, rfl⟩
          · exact ⟨false, rfl⟩
        · exact ⟨false, rfl⟩
      · exact ⟨false, rfl⟩
    · exact ⟨false, rfl⟩
  · rw [if_neg h3]
    exact ⟨false, rfl⟩

/-! ## After the allocation -/

/-- A reader with buffers, no buffered output and `how = LOOK`. -/
structure LookPre (H : Heap) (i : Nat) (t : GzState) : Prop where
  hu : GzInvUpToOutput H i t
  mode : t.mode = GZ_READ
  size : t.size ≠ 0
  have0 : t.x.have = 0
  look : t.how = LOOK
  msg : MsgLit t

/-- The tail of a path through `gz_avail` and a final step: the post-condition from that of the final step. -/
theorem lookPost_after_avail {H H1 Hf : Heap} {i : Nat} {t t1 tf : GzState} {fs fs1 : Fs} (P : LookPre H i t)
    (hk1 : FdsKept fs fs1) (post1 : GzPost H i t [] fs1 H1 GzInvUpToOutput) (ht1 : H1.gzstates i = some t1)
    (hrec1 : AvailRec t t1)
    (bf1 : ReadsFinite fs t.fd → ReadsFinite fs1 t.fd ∧ inputLeft fs1 t1 ≤ inputLeft fs t)
    (bb1 : ReadsBounded fs t.fd → ReadsBounded fs1 t.fd) (be1 : t.err ≠ Z_STREAM_END → t1.err ≠ Z_STREAM_END)
    (bud1 : BudgetAcc t.fd fs fs1 0)
    (post2 : GzPost H1 i t1 [] fs1 Hf GzInvUpToOutput) (htf : Hf.gzstates i = some tf) (hout : OutWindow tf)
    (ml : MsgLit tf)
    (same : tf.mode = t1.mode ∧ tf.fd = t1.fd ∧ tf.skip = t1.skip ∧ tf.x.pos = t1.x.pos ∧ tf.size = t1.size ∧
      tf.out = t1.out ∧ tf.«in» = t1.«in» ∧ (tf.err = t1.err ∨ tf.err = Z_DATA_ERROR ∨ tf.err = Z_MEM_ERROR))
    (hav : tf.strm.avail_in.toNat ≤ t1.strm.avail_in.toNat) {r : Int32} (hr : r = 0 ∨ r = -1)
    (res : r = 0 → (tf.how = LOOK ∧ tf.x.have = 0 ∧
          ((tf.eof ≠ 0 ∧ tf.strm.avail_in = 0) ∨ BudgetAcc t.fd fs fs1 1)) ∨
        (tf.how = GZIP ∧ tf.x.have = 0 ∧ InflateAtHead Hf tf) ∨
        (tf.how = GZ_COPY ∧ tf.strm.avail_in = 0 ∧
          (tf.x.have ≠ 0 ∨ tf.x.pos.toInt = 9223372036854775807) ∧
          tf.x.pos.toInt + tf.x.have.toNat ≤ 9223372036854775807)) :
    LookPost H i t fs r fs1 Hf := by
  obtain ⟨fm, ffd, fsk, fx, fsz, fout, fin, -, -, -⟩ := AvailRec.fields hrec1
  obtain ⟨sm, sfd, ssk, spos, ssz, sout, sin, serr⟩ := same
  refine lookPost_of hr hk1 (post_trans post1 ht1 post2) htf hout (fun h => (bf1 h).1) bb1 bud1
    ⟨sm.trans fm, sfd.trans ffd, ssk.trans fsk, by rw [spos, fx], fun _ => ⟨ssz.trans fsz, sout.trans fout,
      sin.trans fin⟩⟩ ml (fun h => Nat.le_trans (inputLeft_le sfd hav) (bf1 h).2) ?_ ?_ res
  · intro h
    rcases serr with e | e | e
    · rw [e]; exact be1 h
    · rw [e]; decide
    · rw [e]; decide
  intro hz
  exact absurd (by rw [← fsz, ← ssz]; exact hz) P.size

/-- **The auto-detecting path.** -/
theorem lookAuto_run {H : Heap} {i : Nat} {t : GzState} (fs : Fs) (P : LookPre H i t) (hfs : FileSystem fs)
    (hd : t.direct ≠ -1) :
    ∃ r fs' after, lookAuto i fs H = .ok ((r, fs'), after) ∧ LookPost H i t fs r fs' after := by
  obtain ⟨r1, fs1, H1, t1, run1, hr1, hk1, post1, ht1, hrec1, bf1, bb1, be1, afs1, afl1⟩ :=
    avail_step fs P.hu P.mode P.size hfs
  have bud1 : BudgetAcc t.fd fs fs1 0 := afs1.1.mono (Nat.zero_le _)
  obtain ⟨fm, ffd, fsk, fx, fsz, fout, fin, fhow, fdir, fjunk⟩ := AvailRec.fields hrec1
  have hu1 : GzInvUpToOutput H1 i t1 := by
    obtain ⟨-, t1', inv1, -⟩ := post1
    have e : t1' = t1 := Option.some.inj (inv1.1.symm.trans ht1)
    subst e; exact inv1
  have hm1 : t1.mode = GZ_READ := fm.trans P.mode
  have hsz1 : t1.size ≠ 0 := by rw [fsz]; exact P.size
  have hx1 : t1.x.have = 0 := by rw [fx]; exact P.have0
  have refl1 : GzPost H1 i t1 [] fs1 H1 GzInvUpToOutput := post_refl hu1 post1.1
  have same1 : t1.mode = t1.mode ∧ t1.fd = t1.fd ∧ t1.skip = t1.skip ∧ t1.x.pos = t1.x.pos ∧ t1.size = t1.size ∧
      t1.out = t1.out ∧ t1.«in» = t1.«in» ∧ (t1.err = t1.err ∨ t1.err = Z_DATA_ERROR ∨ t1.err = Z_MEM_ERROR) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  have out1 : OutWindow t1 := fun hh => absurd hx1 hh
  have ml1 : MsgLit t1 := fun _ => by
    have e := hrec1
    simp only [AvailRec] at e
    rw [e]
    exact P.msg P.size
  unfold lookAuto
  simp only [g_bind_app, run1]
  by_cases e1 : r1 = -1
  · subst e1
    simp only [beq_self_eq_true, ite_true]
    exact ⟨-1, fs1, H1, rfl, lookPost_after_avail P hk1 post1 ht1 hrec1 bf1 bb1 be1 bud1 refl1 ht1 out1 ml1 same1
      (Nat.le_refl _) (Or.inr rfl) (fun e => absurd e (by decide))⟩
  have e0 : r1 = 0 := hr1.resolve_right e1
  subst e0
  have hz1 : (StateT.lift (ldZ (strmOf (some (.tab i)))) : G ZStream) fs1 H1 = .ok ((t1.strm, fs1), H1) := by
    rw [g_lift_app, strmOf_tab, ldZ_run ht1]
  have hs1 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs1 H1 = .ok ((t1, fs1), H1) := by
    rw [g_lift_app, ldS_run ht1]
  simp only [show ((0 : Int32) == -1) = false from rfl, Bool.false_eq_true, ite_false, g_bind_app, hz1, hs1]
  by_cases c : (t1.strm.avail_in == 0 || (t1.again != 0 && t1.strm.avail_in < 4)) = true
  · rw [if_pos c]
    -- no input at the end of the file, or a stall after a read that delivered at least one byte
    have prog : (t1.eof ≠ 0 ∧ t1.strm.avail_in = 0) ∨ BudgetAcc t.fd fs fs1 1 := by
      by_cases ha0 : t1.strm.avail_in = 0
      · exact Or.inl ⟨afl1.2.2.1 rfl ha0, ha0⟩
      · right
        have hag : t1.again ≠ 0 := by
          intro e; apply ha0; simpa [e] using c
        have he0 : t1.eof = 0 := Classical.byContradiction fun he => ha0 ((hu1.2.reader hm1).againEof hag he)
        have hlt := afl1.2.2.2 rfl he0
        exact afs1.1.mono (by omega)
    exact ⟨0, fs1, H1, rfl, lookPost_after_avail P hk1 post1 ht1 hrec1 bf1 bb1 be1 bud1 refl1 ht1 out1 ml1 same1
      (Nat.le_refl _) (Or.inl rfl) (fun _ => Or.inl ⟨by rw [fhow]; exact P.look, hx1, prog⟩)⟩
  rw [if_neg c]
  have hav : t1.strm.avail_in ≠ 0 := by
    intro e; apply c; simp [e]
  have rd1 := hu1.2.reader hm1
  obtain ⟨ib, iarr, hin, hib, -, hisz⟩ := (rd1.bufs hsz1).1
  have hin' : t1.«in» = .ref (.blk ib) 0 := hin
  have hisz' : iarr.size = t1.size.toNat := hisz
  obtain ⟨a, hq, hle⟩ : ∃ a, t1.strm.next_in = .ref (.blk ib) a ∧ a + t1.strm.avail_in.toNat ≤ t1.size.toNat := by
    rcases rd1.input with z | ⟨a, hq, hle⟩
    · exact absurd z hav
    · refine ⟨a, ?_, hle⟩
      have hq' : t1.strm.next_in = padv t1.«in» a := hq
      rw [hq', hin']; simp [padv]
  obtain ⟨g, hg⟩ := lookMagic_eq (H := H1) (i := i) fs1 hq (show H1.bytes ib = some iarr from hib) (fun h3 => by
    have : 3 < t1.strm.avail_in.toNat := UInt32.lt_iff_toNat_lt.mp h3
    omega)
  rw [hg]
  cases g with
  | true =>
    obtain ⟨Hf, tf, run2, htf, post2, eqf, avf, -, head, hmsg⟩ :=
      lookGzip_run fs1 hu1 hm1 hsz1 post1.1 (fun _ => 0) (fun _ => Or.inl rfl)
    refine ⟨0, fs1, Hf, by unfold lookFinal; exact run2, ?_⟩
    have same : tf.mode = t1.mode ∧ tf.fd = t1.fd ∧ tf.skip = t1.skip ∧ tf.x.pos = t1.x.pos ∧ tf.size = t1.size ∧
        tf.out = t1.out ∧ tf.«in» = t1.«in» ∧ (tf.err = t1.err ∨ tf.err = Z_DATA_ERROR ∨ tf.err = Z_MEM_ERROR) := by
      rw [eqf]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
    have hxf : tf.x.have = 0 := by rw [eqf]; exact hx1
    have hhow : tf.how = GZIP := by rw [eqf]
    exact lookPost_after_avail P hk1 post1 ht1 hrec1 bf1 bb1 be1 bud1 post2 htf (fun hh => absurd hxf hh) (fun _ => Or.inl hmsg) same
      (by rw [avf]; exact Nat.le_refl _) (Or.inl rfl) (fun _ => Or.inr (Or.inl ⟨hhow, hxf, head⟩))
  | false =>
    obtain ⟨Hf, tf, room, run2, htf, eqf, herrf, hrle, hpos, hz, post2⟩ :=
      lookCopy_run fs1 hu1 hm1 hsz1 post1.1 hav (by rw [fdir]; exact hd)
    refine ⟨0, fs1, Hf, by unfold lookFinal; exact run2, ?_⟩
    have same : tf.mode = t1.mode ∧ tf.fd = t1.fd ∧ tf.skip = t1.skip ∧ tf.x.pos = t1.x.pos ∧ tf.size = t1.size ∧
        tf.out = t1.out ∧ tf.«in» = t1.«in» ∧ (tf.err = t1.err ∨ tf.err = Z_DATA_ERROR ∨ tf.err = Z_MEM_ERROR) := by
      rw [eqf]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, herrf⟩
    have hml : MsgLit tf := fun _ => by rw [eqf]; exact ml1 hsz1
    have hav' : tf.strm.avail_in.toNat ≤ t1.strm.avail_in.toNat := by rw [eqf]; simp
    have hres : tf.how = GZ_COPY ∧ tf.strm.avail_in = 0 ∧
        (tf.x.have ≠ 0 ∨ tf.x.pos.toInt = 9223372036854775807) ∧
        tf.x.pos.toInt + tf.x.have.toNat ≤ 9223372036854775807 := by
      rw [eqf]
      refine ⟨rfl, rfl, ?_, hpos⟩
      show room ≠ 0 ∨ t1.x.pos.toInt = 9223372036854775807
      by_cases h0 : room = 0
      · exact Or.inr (hz h0)
      · exact Or.inl h0
    refine lookPost_after_avail P hk1 post1 ht1 hrec1 bf1 bb1 be1 bud1 post2 htf ?_ hml same hav' (Or.inl rfl)
      (fun _ => Or.inr (Or.inr hres))
    intro _
    rw [eqf]
    refine ⟨0, look_padv_zero t1.out |>.symm, ?_⟩
    show 0 + room.toNat ≤ 2 * t1.size.toNat
    omega

/-- **Everything after the allocation.** -/
theorem lookMain_run {H : Heap} {i : Nat} {t : GzState} (fs : Fs) (P : LookPre H i t) (hfs : FileSystem fs) :
    ∃ r fs' after, lookMain i fs H = .ok ((r, fs'), after) ∧ LookPost H i t fs r fs' after := by
  have hs : H.gzstates i = some t := P.hu.1
  have hsH : (StateT.lift (ldS (some (.tab i))) : G GzState) fs H = .ok ((t, fs), H) := by
    rw [g_lift_app, ldS_run hs]
  unfold lookMain
  simp only [g_bind_app, hsH]
  by_cases c1 : (t.direct == -1 || t.junk == 0) = true
  rotate_left
  · rw [if_neg c1]
    exact lookAuto_run fs P hfs (fun e => c1 (by simp [e]))
  rw [if_pos c1]
  have hzH : (StateT.lift (ldZ (strmOf (some (.tab i)))) : G ZStream) fs H = .ok ((t.strm, fs), H) := by
    rw [g_lift_app, strmOf_tab, ldZ_run hs]
  simp only [g_bind_app, hzH]
  have hf : ∀ j : Int32, (if (j != -1) = true then (1 : Int32) else 0) = 0 ∨
      (if (j != -1) = true then (1 : Int32) else 0) = 1 := by
    intro j; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases c2 : (t.junk == 0 && t.strm.avail_in == 0) = true
  rotate_left
  · rw [if_neg c2]
    -- straight to a gzip member
    obtain ⟨Hf, tf, run2, htf, post2, eqf, avf, -, head, hmsg⟩ :=
      lookGzip_run fs P.hu P.mode P.size hfs _ hf
    refine ⟨0, fs, Hf, run2, ?_⟩
    have hxf : tf.x.have = 0 := by rw [eqf]; exact P.have0
    have keeps : FetchKeeps t tf := by
      rw [eqf]; exact ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
    refine lookPost_of (Or.inl rfl) (fun _ => Iff.rfl) post2 htf (fun hh => absurd hxf hh) id id (BudgetAcc.refl _ _)
      keeps (fun _ => Or.inl hmsg)
      (fun _ => inputLeft_le (by rw [eqf]) (by rw [avf]; exact Nat.le_refl _)) (by rw [eqf]; exact id) ?_
      (fun _ => Or.inr (Or.inl ⟨by rw [eqf], hxf, head⟩))
    intro hz
    exact absurd (by rw [eqf] at hz; exact hz) P.size
  rw [if_pos c2]
  obtain ⟨r1, fs1, H1, t1, run1, hr1, hk1, post1, ht1, hrec1, bf1, bb1, be1, afs1, afl1⟩ :=
    avail_step fs P.hu P.mode P.size hfs
  have bud1 : BudgetAcc t.fd fs fs1 0 := afs1.1.mono (Nat.zero_le _)
  obtain ⟨fm, ffd, fsk, fx, fsz, fout, fin, fhow, fdir, fjunk⟩ := AvailRec.fields hrec1
  have hu1 : GzInvUpToOutput H1 i t1 := by
    obtain ⟨-, t1', inv1, -⟩ := post1
    have e : t1' = t1 := Option.some.inj (inv1.1.symm.trans ht1)
    subst e; exact inv1
  have hm1 : t1.mode = GZ_READ := fm.trans P.mode
  have hsz1 : t1.size ≠ 0 := by rw [fsz]; exact P.size
  have hx1 : t1.x.have = 0 := by rw [fx]; exact P.have0
  have refl1 : GzPost H1 i t1 [] fs1 H1 GzInvUpToOutput := post_refl hu1 post1.1
  have same1 : t1.mode = t1.mode ∧ t1.fd = t1.fd ∧ t1.skip = t1.skip ∧ t1.x.pos = t1.x.pos ∧ t1.size = t1.size ∧
      t1.out = t1.out ∧ t1.«in» = t1.«in» ∧ (t1.err = t1.err ∨ t1.err = Z_DATA_ERROR ∨ t1.err = Z_MEM_ERROR) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  have out1 : OutWindow t1 := fun hh => absurd hx1 hh
  have ml1 : MsgLit t1 := fun _ => by
    have e := hrec1
    simp only [AvailRec] at e
    rw [e]
    exact P.msg P.size
  simp only [g_bind_app, run1]
  by_cases e1 : r1 = -1
  · subst e1
    simp only [beq_self_eq_true, ite_true]
    exact ⟨-1, fs1, H1, rfl, lookPost_after_avail P hk1 post1 ht1 hrec1 bf1 bb1 be1 bud1 refl1 ht1 out1 ml1 same1
      (Nat.le_refl _) (Or.inr rfl) (fun e => absurd e (by decide))⟩
  have e0 : r1 = 0 := hr1.resolve_right e1
  subst e0
  have hz1 : (StateT.lift (ldZ (strmOf (some (.tab i)))) : G ZStream) fs1 H1 = .ok ((t1.strm, fs1), H1) := by
    rw [g_lift_app, strmOf_tab, ldZ_run ht1]
  simp only [show ((0 : Int32) == -1) = false from rfl, Bool.false_eq_true, ite_false, g_bind_app, hz1]
  by_cases c3 : (t1.strm.avail_in == 0) = true
  · rw [if_pos c3]
    have ha0 : t1.strm.avail_in = 0 := by simpa using c3
    exact ⟨0, fs1, H1, rfl, lookPost_after_avail P hk1 post1 ht1 hrec1 bf1 bb1 be1 bud1 refl1 ht1 out1 ml1 same1
      (Nat.le_refl _) (Or.inl rfl)
      (fun _ => Or.inl ⟨by rw [fhow]; exact P.look, hx1, Or.inl ⟨afl1.2.2.1 rfl ha0, ha0⟩⟩)⟩
  rw [if_neg c3]
  obtain ⟨Hf, tf, run2, htf, post2, eqf, avf, -, head, hmsg⟩ := lookGzip_run fs1 hu1 hm1 hsz1 post1.1 _ hf
  refine ⟨0, fs1, Hf, run2, ?_⟩
  have same : tf.mode = t1.mode ∧ tf.fd = t1.fd ∧ tf.skip = t1.skip ∧ tf.x.pos = t1.x.pos ∧ tf.size = t1.size ∧
      tf.out = t1.out ∧ tf.«in» = t1.«in» ∧ (tf.err = t1.err ∨ tf.err = Z_DATA_ERROR ∨ tf.err = Z_MEM_ERROR) := by
    rw [eqf]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  have hxf : tf.x.have = 0 := by rw [eqf]; exact hx1
  exact lookPost_after_avail P hk1 post1 ht1 hrec1 bf1 bb1 be1 bud1 post2 htf (fun hh => absurd hxf hh) (fun _ => Or.inl hmsg) same
    (by rw [avf]; exact Nat.le_refl _) (Or.inl rfl) (fun _ => Or.inr (Or.inl ⟨by rw [eqf], hxf, head⟩))

/-! ## The allocation -/

section alloc
open Zlib.Gzwrite.SafeInit (Ext aHeap fHeap dHeap allocB_eq freeB_eq oom_cstring version_index version_value rec_lt
  aHeap_bytes aHeap_ro aHeap_gz dHeap_gz fHeap_gz)
open Zlib.Inflate.Spec Zlib.Inflate.Proofs

theorem upTo_base {H : Heap} {i : Nat} {s : GzState} (hu : GzInvUpToOutput H i s) :
    Fresh H ∧ Zlib.Gzlib.Spec.Uniq H ∧ ZlibF.PlatformMemory.ByteObjectsFit H ∧ LibraryGlobals H := by
  have hs := hu.1
  have c := hu.2.common
  have hsW : (putGz H i (clearOut s)).gzstates i = some (clearOut s) := by simp [putGz]
  have eH : putGz (putGz H i (clearOut s)) i s = H := by rw [putGz_putGz']; exact upd_self_heap hs
  refine ⟨fun b hb hl => c.fresh b hb ((putGz_live hs b).2 hl), ?_,
    fun r a e => c.fit r a (by rw [putGz_space]; exact e), c.globals⟩
  rw [← eH]; exact putGz_uniq hsW c.uniq

theorem oom_lit : ∃ k, strIndex "out of memory" = some k :=
  Option.isSome_iff_exists.mp (by decide +kernel)

theorem want_lim {s : GzState} (hw : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31) :
    s.want.toNat < mallocLimit ∧ s.want.toNat < ZlibF.PlatformMemory.byteObjectLimit ∧
      (s.want <<< 1).toNat = 2 * s.want.toNat ∧ 2 * s.want.toNat < mallocLimit ∧
      2 * s.want.toNat < ZlibF.PlatformMemory.byteObjectLimit := by
  have e : (s.want <<< 1).toNat = 2 * s.want.toNat := by
    rw [UInt32.toNat_shiftLeft]
    have : (1 : UInt32).toNat % 32 = 1 := rfl
    rw [this, Nat.shiftLeft_eq, Nat.pow_one]
    have : (2 : Nat) ^ 32 = 4294967296 := by decide
    omega
  refine ⟨lt_mallocLimit_of_lt_pow32 (by omega), ?_, e, lt_mallocLimit_of_lt_pow32 (by omega), ?_⟩ <;>
    · unfold ZlibF.PlatformMemory.byteObjectLimit
      have : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
      omega

/-- **The failure report**: `gz_error(state, Z_MEM_ERROR, "out of memory"); return -1;` on a heap that has the
record changed (no buffers: `size = 0`, dangling `in` and `out`, a stream with no state) and no new block. -/
theorem fail_err {H Hq : Heap} {i : Nat} {s sq : GzState} (fs : Fs) (hfs : FileSystem fs)
    (hu : GzInvUpToOutput H i s) (hm : s.mode = GZ_READ) (hsz : s.size = 0) (hx0 : s.x.have = 0)
    (E : Ext H Hq i sq) (hnone : ∀ x, H.nextBlk ≤ x → Hq.bytes x = none)
    {p q : BPtr} {zq : ZStream} {sz : UInt32} (hsq : sq = { s with «in» := p, out := q, strm := zq, size := sz })
    (hsz' : sz = 0) (hst : zq.state = none) (hav : zq.avail_in = 0) :
    ∃ after, (do
        let m ← StateT.lift (strLitRef "out of memory")
        StateT.lift (Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR m)
        pure (-1) : G Int32) fs Hq = .ok ((-1, fs), after) ∧ LookPost H i s fs (-1) fs after := by
  subst hsz'
  subst hsq
  have hs := hu.1
  have inv : GzInv (putGz H i (clearOut s)) i (clearOut s) := hu.2
  have hmc : (clearOut s).mode = GZ_READ := hm
  obtain ⟨freshH, uniqH, fitH, globalsH⟩ := upTo_base hu
  have hq : Hq.gzstates i = some { s with «in» := p, out := q, strm := zq, size := 0 } := E.recd
  have liveq : ∀ x, Hq.live x ↔ H.live x := by
    intro x
    rw [E.live_iff hs freshH x]
    constructor
    · rintro (l | ⟨hx, n⟩)
      · exact l
      · exact absurd (hnone x hx) n
    · exact Or.inl
  -- the invariant of the changed record
  let sq : GzState := { s with «in» := p, out := q, strm := zq, size := 0 }
  have EW : Ext H (putGz Hq i (clearOut sq)) i (clearOut sq) := E.setS (clearOut sq)
  have frH := EW.frame freshH
  have frW : Frame (putGz H i (clearOut s)) (putGz Hq i (clearOut sq)) (fun b => b = i) := by
    refine ⟨frH.1, frH.2.1, frH.2.2.1, frH.2.2.2.1, frH.2.2.2.2.1, fun b hl hbi => ?_⟩
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := frH.2.2.2.2.2 b ((putGz_live hs b).1 hl) hbi
    refine ⟨e1, e2, e3, e4, e5, e6, ?_, e8⟩
    rw [e7]
    show H.gzstates b = upd H.gzstates i (some (clearOut s)) b
    rw [upd_ne _ _ _ _ hbi]
  have invq : GzInv (putGz Hq i (clearOut sq)) i (clearOut sq) :=
    GzInv.size0_rebuild inv hmc hsz rfl (by simp [putGz])
      ⟨rfl, rfl, hsz.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hst hav frW
      (EW.fresh' hs freshH) (EW.uniq hs freshH uniqH) (EW.globals globalsH) (EW.fit fitH)
  have huq : GzInvUpToOutput Hq i sq := ⟨hq, invq⟩
  have post0 : GzPost H i s [] fs Hq GzInvUpToOutput := by
    refine post_step (D := fun _ => False) (C := fun _ => False) hu huq hfs rfl rfl ?_ (fun _ f => f.elim)
      (fun _ f => f.elim) ?_ ?_
    · have f := E.frame freshH
      exact ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1, fun b hl hno => f.2.2.2.2.2 b hl (fun e => hno (Or.inl e))⟩
    · intro b
      simp only [not_false_eq_true, and_true, or_false]
      constructor
      · rintro (e | e | e | ⟨hz, -⟩)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl e))
        · exact absurd rfl hz
      · rintro (e | e | e | ⟨hz, -⟩)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl e))
        · exact absurd hsz hz
    · intro b
      simp only [not_false_eq_true, and_true, or_false]
      exact liveq b
  obtain ⟨k, hk⟩ := oom_lit
  obtain ⟨after, s', run, hs', shape, herr, post1⟩ := err_post fs hfs huq Z_MEM_ERROR (oom_cstring Hq hk)
    (fun _ h => h)
  have run' : Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0) Hq = .ok ((), after) := run
  refine ⟨after, ?_, ?_⟩
  · have r1 : (StateT.lift (strLitRef "out of memory") : G BPtr) fs Hq = .ok ((.ref (.str k) 0, fs), Hq) := by
      rw [g_lift_app, strLitRef_of_index hk]
    have r2 : (StateT.lift (Zlib.Gzlib.gz_error (some (.tab i)) Z_MEM_ERROR (.ref (.str k) 0)) : G Unit) fs Hq =
        .ok (((), fs), after) := by
      rw [g_lift_app, run']
    simp only [g_bind_app, r1, r2, g_pure_app]
  have hmem : s'.err = Z_MEM_ERROR := herr.elim id id
  refine lookPost_of (Or.inr rfl) (fun _ => Iff.rfl) (post_trans post0 hq post1) hs' ?_ id id (BudgetAcc.refl _ _)
    ?_ ?_ ?_ ?_ ?_
    (fun e => absurd e (by decide))
  · intro hh
    exfalso; apply hh
    rw [shape]; exact hx0
  · rw [shape]; exact ⟨rfl, rfl, rfl, rfl, fun h => absurd hsz h⟩
  · intro hz
    exfalso; apply hz
    rw [shape]
  · intro _
    exact inputLeft_le (by rw [shape]) (by rw [shape]; show zq.avail_in.toNat ≤ _; rw [hav]; exact Nat.zero_le _)
  · intro _; rw [hmem]; decide
  · intro _; rw [hmem]; decide

theorem init_reset2Heap (X : Heap) (r : ZStreamRef) (wb : Int32) : reset2Heap X wb (initState r) = X := by
  unfold reset2Heap
  split <;> rfl

theorem init_window (k : Nat) (r : ZStreamRef) (wrap wb : Int32) :
    (resetKeepState k (resetPre (reset2Pre wrap wb (initState r)))).window = .null := by
  simp only [resetKeepState, resetPre, reset2Pre, initState, bne_self_eq_false, Bool.false_eq_true, ite_false]
  by_cases h2 : (InflateState.zeroed.wbits != Zlib.Inflate.i2u wb) = true
  · simp [h2]
  · simp [h2]

/-- The heap after a successful `inflateInit2_` on the embedded stream. -/
theorem initOk_eq {X : Heap} {i : Nat} {t : GzState} (hX : X.gzstates i = some t) (z : ZStream)
    (wrap wb : Int32) :
    initOkHeap X (.in_gzstate_strm i) z wrap wb =
      { X with gzstates := upd X.gzstates i (some { t with strm := resetKeepStream (initStream2 z X.nextBlk) (resetPre (reset2Pre wrap wb (initState (.in_gzstate_strm i)))) }), istates := upd X.istates X.nextBlk (some (resetKeepState X.nextBlk (resetPre (reset2Pre wrap wb (initState (.in_gzstate_strm i)))))), nextBlk := X.nextBlk + 1, nalloc := X.nalloc + 1 } := by
  simp [initOkHeap, allocIstHeap, init_reset2Heap, setI, ZStreamRef.put, hX, upd_upd]

/-- **A successful `inflateInit2_(strm, 31)`** after the two allocations: the reader has its buffers and a fresh
inflate stream, in the invariant up to the buffered output, with the post-condition from the start. -/
theorem init_success {H H5 : Heap} {i : Nat} {s : GzState} (fs : Fs) (hfs : FileSystem fs)
    (hu : GzInvUpToOutput H i s) (hm : s.mode = GZ_READ) (hsz : s.size = 0) (hx0 : s.x.have = 0)
    (E5 : Ext H H5 i { s with «in» := .ref (.blk H.nextBlk) 0, out := .ref (.blk (H.nextBlk + 1)) 0, size := s.want, strm := { s.strm with zalloc := .null, zfree := .null, «opaque» := .null, avail_in := 0, next_in := .null } })
    (hnext : H5.nextBlk = H.nextBlk + 2)
    (hb0 : ∃ a, H5.bytes H.nextBlk = some a ∧ a.size = s.want.toNat)
    (hb1 : ∃ a, H5.bytes (H.nextBlk + 1) = some a ∧ a.size = 2 * s.want.toNat)
    (hro0 : H5.ro H.nextBlk = false) (hro1 : H5.ro (H.nextBlk + 1) = false)
    (hok : H5.allocOk H5.nalloc = true) :
    ∃ H6, Zlib.Inflate.inflateInit2_ (some (.in_gzstate_strm i)) 31 (.ref (.str 57) 0) 112 H5 =
        .ok (Z_OK, H6) ∧
      ∃ s6, H6.gzstates i = some s6 ∧ LookPre H6 i s6 ∧ GzPost H i s [] fs H6 GzInvUpToOutput ∧
        s6.mode = s.mode ∧ s6.fd = s.fd ∧ s6.skip = s.skip ∧ s6.x = s.x ∧ s6.strm.avail_in = 0 ∧
        s6.err = s.err := by
  have hs := hu.1
  have inv : GzInv (putGz H i (clearOut s)) i (clearOut s) := hu.2
  have hmc : (clearOut s).mode = GZ_READ := hm
  have c := inv.common
  have rd := inv.reader hmc
  obtain ⟨freshH, uniqH, fitH, globalsH⟩ := upTo_base hu
  have hlook : s.how = LOOK := (rd.unalloc hsz).2.2.1
  have hwant : 8 ≤ s.want.toNat ∧ s.want.toNat < 2 ^ 31 := c.want
  have hw0 : s.want ≠ 0 := by intro e; rw [e] at hwant; simp at hwant
  let nb := H.nextBlk
  let ks := H.nextBlk + 2
  let r : ZStreamRef := .in_gzstate_strm i
  let z4 : ZStream := { s.strm with zalloc := .null, zfree := .null, «opaque» := .null, avail_in := 0, next_in := .null }
  let s4 : GzState := { s with «in» := .ref (.blk nb) 0, out := .ref (.blk (nb + 1)) 0, size := s.want, strm := z4 }
  have h4 : H5.gzstates i = some s4 := E5.recd
  have fresh5 : Fresh H5 := E5.fresh' hs freshH
  have uniq5 : Zlib.Gzlib.Spec.Uniq H5 := E5.uniq hs freshH uniqH
  have hz5 : r.get H5 = some z4 := by simp [r, ZStreamRef.get, h4, s4]
  have ver := version_value H5
  obtain ⟨hvn, hv0⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read ver
  obtain ⟨⟨wrap, wb⟩, hp⟩ : ∃ p, reset2Params 31 = some p := Option.isSome_iff_exists.mp (by decide)
  obtain ⟨H6, run6, eH6, good6, -⟩ := inflateInit2_ok (r := r) (z := z4) (w := 31) uniq5 fresh5 hz5 hok
    (Or.inl rfl) (Or.inl rfl) hvn hv0 hp
  let z6 := resetKeepStream (initStream2 z4 ks) (resetPre (reset2Pre wrap wb (initState r)))
  let st6 := resetKeepState ks (resetPre (reset2Pre wrap wb (initState r)))
  let s6 : GzState := { s4 with strm := z6 }
  have eH6' : H6 = { H5 with gzstates := upd H5.gzstates i (some s6), istates := upd H5.istates ks (some st6), nextBlk := ks + 1, nalloc := H5.nalloc + 1 } := by
    rw [eH6, initOk_eq h4]
    simp only [hnext, ks, s6, z6, st6]
    rfl
  have hs6 : H6.gzstates i = some s6 := by rw [eH6']; simp
  have hks : H5.nextBlk = ks := hnext
  have zst6 : z6.state = some (.inflate ks) := by
    rfl
  have win6 : st6.window = .null := init_window _ _ _ _
  have hlt : ∀ b, H.live b → b < nb := fun b hl => Fresh.lt freshH hl
  have hil : i < nb := rec_lt hs freshH
  -- the new world
  let V : Heap := putGz H6 i (clearOut s6)
  have eV : V = { H5 with gzstates := upd H5.gzstates i (some (clearOut s6)), istates := upd H5.istates ks (some st6), nextBlk := ks + 1, nalloc := H5.nalloc + 1 } := by
    show putGz H6 i (clearOut s6) = _
    rw [eH6']; simp only [putGz, upd_upd]
  have gV : r.get V = some z6 := by rw [eV]; simp [r, ZStreamRef.get, clearOut, s6]
  have kV : V.istates ks = some st6 := by rw [eV]; simp
  have g6 : r.get H6 = some z6 := by rw [eH6']; simp [r, ZStreamRef.get, s6]
  have k6 : H6.istates ks = some st6 := by rw [eH6']; simp
  have soOf : ∀ (X : Heap), r.get X = some z6 → X.istates ks = some st6 →
      ∀ b, StreamOwned X r b ↔ b = ks := by
    intro X gX kX b
    constructor
    · rintro ⟨z, hz, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, -, -⟩⟩
      · rw [gX] at hz; cases hz
        rw [zst6] at hk; cases hk
        rw [kX] at hst; cases hst
        rcases ho with e | e
        · exact e
        · rw [win6] at e; cases e
      · rw [gX] at hz; cases hz
        rw [zst6] at hk; cases hk
    · intro e
      exact ⟨z6, gX, Or.inl ⟨ks, st6, zst6, kX, Or.inl e⟩⟩
  have soV := soOf V gV kV
  have so6 := soOf H6 g6 k6
  -- the codec history, from the same initialization on the world of the invariant
  let W5 : Heap := putGz H5 i (clearOut s4)
  have EW5 : Ext H W5 i (clearOut s4) := E5.setS (clearOut s4)
  have hW5 : W5.gzstates i = some (clearOut s4) := by simp [W5, putGz]
  have hzW5 : r.get W5 = some z4 := by simp [r, ZStreamRef.get, hW5, clearOut, s4]
  obtain ⟨hvnW, hv0W⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read (version_value W5)
  obtain ⟨HW, runW, eHW, -, -⟩ := inflateInit2_ok (r := r) (z := z4) (w := 31) (EW5.uniq hs freshH uniqH)
    (EW5.fresh' hs freshH) hzW5 hok (Or.inl rfl) (Or.inl rfl) hvnW hv0W hp
  have eVW : HW = V := by
    rw [eHW, initOk_eq hW5, eV]
    simp only [W5, putGz, upd_upd, hks]
    rfl
  have reach : StreamReachable .inflate V r := by
    have := StreamReachable.inflateInit (EW5.fresh' hs freshH) (EW5.uniq hs freshH uniqH)
      (EW5.globals globalsH) hzW5 ⟨Or.inl rfl, Or.inl rfl⟩ (version_value W5) runW
    rw [eVW] at this
    exact this
  -- the invariant
  have ownS : ownedPtrs (clearOut s) = [s.path, s.msg] := by
    unfold ownedPtrs; rw [if_neg (show ¬ ((clearOut s).size ≠ 0) from fun x => x hsz)]; rfl
  have own6 : ownedPtrs (clearOut s6) = [s.path, s.msg, .ref (.blk nb) 0, .ref (.blk (nb + 1)) 0] := by
    unfold ownedPtrs
    rw [if_pos (show (clearOut s6).size ≠ 0 from hw0),
      if_pos (show (clearOut s6).mode = GZ_READ ∨ (clearOut s6).direct = 0 from Or.inl hm)]
    rfl
  have ltP : ∀ p, p ∈ [s.path, s.msg] → ∀ b, blkOf p = some b → b < nb := fun p hp b hb =>
    hlt b ((putGz_live hs b).1 (inv.ptr_live (by rw [ownS]; exact hp) hb))
  have keptP : ∀ p, (p = s.path ∨ p = s.msg) → ∀ b, p = .ref (.blk b) 0 →
      V.bytes b = H.bytes b ∧ V.ro b = H.ro b ∧ b < nb ∧ b ≠ i ∧ V.live b := by
    intro p hp b e
    have mem : p ∈ ownedPtrs (clearOut s) := by rw [ownS]; rcases hp with x | x <;> subst x <;> simp
    have hbk : blkOf p = some b := by rw [e]; rfl
    have hbi := (c.distinct.2 p mem b hbk).1
    have hlW := inv.ptr_live mem hbk
    have hl : H.live b := (putGz_live hs b).1 hlW
    have hb := hlt b hl
    have vb : V.bytes b = H.bytes b := by rw [eV]; exact E5.bytes b hb
    have vr : V.ro b = H.ro b := by rw [eV]; exact E5.ro b hb hl hbi
    refine ⟨vb, vr, hb, hbi, ?_⟩
    have hbks : b ≠ ks := by omega
    rw [eV]
    unfold Heap.live at hl ⊢
    show H5.bytes b ≠ none ∨ H5.words b ≠ none ∨ H5.streams b ≠ none ∨ H5.gzheaders b ≠ none ∨
      H5.dstates b ≠ none ∨ upd H5.istates ks (some st6) b ≠ none ∨ upd H5.gzstates i (some (clearOut s6)) b ≠ none
    rw [upd_ne _ _ _ _ hbks, upd_ne _ _ _ _ hbi, E5.bytes b hb, E5.words, E5.streams, E5.gzheaders, E5.dstates,
      E5.istates, E5.gzstates, if_neg hbi]
    exact hl
  obtain ⟨a0, ha0, hsz0⟩ := hb0
  obtain ⟨a1, ha1, hsz1⟩ := hb1
  have vb0 : V.bytes nb = some a0 := by rw [eV]; exact ha0
  have vb1 : V.bytes (nb + 1) = some a1 := by rw [eV]; exact ha1
  have vr0 : V.ro nb = false := by rw [eV]; exact hro0
  have vr1 : V.ro (nb + 1) = false := by rw [eV]; exact hro1
  have hmalloc : ∀ p n, (p = s.path ∨ p = s.msg) → MallocBuffer (putGz H i (clearOut s)) p n →
      MallocBuffer V p n := by
    intro p n hp hx
    obtain ⟨b, a, e, hb, hr, hn⟩ := hx
    obtain ⟨k1, k2, -⟩ := keptP p hp b e
    exact ⟨b, a, e, by rw [k1]; exact hb, by rw [k2]; exact hr, hn⟩
  have fresh6 : Fresh H6 := good6.fresh
  have uniq6 : Zlib.Gzlib.Spec.Uniq H6 := (gz_uniq_iff_inflate H6).2 good6.uniq
  have invV : GzInv V i (clearOut s6) := by
    refine ⟨?_, fun _ => ?_, fun hw => absurd (hm.symm.trans hw) (by decide)⟩
    · exact {
        record := by simp [V, putGz]
        mode := Or.inl hm
        fresh := putGz_fresh hs6 fresh6
        uniq := putGz_uniq hs6 uniq6
        globals := by
          unfold LibraryGlobals
          rw [eV]
          show H5.static = _
          rw [E5.static]; exact globalsH
        fit := by
          refine ZlibF.PlatformMemory.ByteObjectsFit.of_storage_eq (E5.fit fitH) ?_ ?_ ?_ <;> rw [eV]
        path := by
          obtain ⟨p, hc, hmb⟩ := c.path
          refine ⟨p, ?_, hmalloc _ _ (Or.inl rfl) hmb⟩
          obtain ⟨pb, a, hp, -, -, -⟩ := hmb
          have hp' : s.path = .ref (.blk pb) 0 := hp
          show CString V s.path p
          rw [hp']
          have hc' : CString (putGz H i (clearOut s)) (.ref (.blk pb) 0) p := by rw [← hp']; exact hc
          exact (cstring_blk_congr (keptP _ (Or.inl rfl) pb hp').1).2 hc'
        msg := by
          rcases c.msg with hn | ⟨m, hc, hmb⟩
          · exact Or.inl hn
          · refine Or.inr ⟨m, ?_, hmalloc _ _ (Or.inr rfl) hmb⟩
            obtain ⟨mb, a, hp, -, -, -⟩ := hmb
            have hp' : s.msg = .ref (.blk mb) 0 := hp
            show CString V s.msg m
            rw [hp']
            have hc' : CString (putGz H i (clearOut s)) (.ref (.blk mb) 0) m := by rw [← hp']; exact hc
            exact (cstring_blk_congr (keptP _ (Or.inr rfl) mb hp').1).2 hc'
        memerr := c.memerr
        want := c.want
        size := Or.inr rfl
        distinct := by
          rw [own6]
          refine ⟨?_, ?_⟩
          · have nd0 := c.distinct.1
            rw [ownS] at nd0
            have e : List.filterMap blkOf [s.path, s.msg, .ref (.blk nb) 0, .ref (.blk (nb + 1)) 0] =
                List.filterMap blkOf [s.path, s.msg] ++ [nb, nb + 1] := by
              rw [show [s.path, s.msg, .ref (.blk nb) 0, .ref (.blk (nb + 1)) 0] =
                [s.path, s.msg] ++ [.ref (.blk nb) 0, .ref (.blk (nb + 1)) 0] from rfl, List.filterMap_append]
              rfl
            rw [e, List.nodup_append]
            refine ⟨nd0, by simp, ?_⟩
            intro a ha b hb
            obtain ⟨p, hp, hpa⟩ := List.mem_filterMap.1 ha
            have := ltP p hp a hpa
            simp at hb
            omega
          · intro p hp b hb
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with e | e | e | e
            · have hm' : p ∈ [s.path, s.msg] := by rw [e]; simp
              have hbi := (c.distinct.2 p (by rw [ownS]; exact hm') b hb).1
              have := ltP p hm' b hb
              exact ⟨hbi, fun so => by have := (soV b).1 so; omega⟩
            · have hm' : p ∈ [s.path, s.msg] := by rw [e]; simp
              have hbi := (c.distinct.2 p (by rw [ownS]; exact hm') b hb).1
              have := ltP p hm' b hb
              exact ⟨hbi, fun so => by have := (soV b).1 so; omega⟩
            · subst e; cases hb
              exact ⟨by omega, fun so => by have := (soV nb).1 so; omega⟩
            · subst e; cases hb
              exact ⟨by omega, fun so => by have := (soV (nb + 1)).1 so; omega⟩
        live := by
          intro b ho
          rcases ho with e | e | e | ⟨-, e | ⟨-, e | so⟩⟩
          · subst e
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [V, putGz]))))))
          · exact (keptP _ (Or.inl rfl) b e).2.2.2.2
          · exact (keptP _ (Or.inr rfl) b e).2.2.2.2
          · cases e; exact Or.inl (by rw [vb0]; exact Option.some_ne_none _)
          · cases e; exact Or.inl (by rw [vb1]; exact Option.some_ne_none _)
          · have := (soV b).1 so
            subst this
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [kV]; exact Option.some_ne_none _))))))
        pos := c.pos
        next := fun hh => absurd rfl hh
        nullHave := fun _ => rfl
        recordFree := fun so => by have := (soV i).1 so; omega }
    · exact {
        how := Or.inl hlook
        copyDirect := fun e => absurd (hlook.symm.trans e) (by decide)
        gzipDirect := fun e => absurd (hlook.symm.trans e) (by decide)
        direct := rd.direct
        junk := rd.junk
        flags := rd.flags
        unalloc := fun hz => absurd hz hw0
        bufs := fun _ => ⟨⟨nb, a0, rfl, vb0, vr0, hsz0⟩, ⟨nb + 1, a1, rfl, vb1, vr1, hsz1⟩⟩
        input := Or.inl rfl
        output := fun hh => absurd rfl hh
        codec := fun _ => ⟨reach, z6, ks, st6, gV, zst6, kV, rfl⟩
        posHave := rd.posHave
        againSize := fun hz => absurd hz hw0
        haveSkip := fun hh => absurd rfl hh
        againEof := fun _ _ => rfl }
  have hu6 : GzInvUpToOutput H6 i s6 := ⟨hs6, invV⟩
  -- the post-condition
  have live6 : ∀ b, H6.live b ↔ H.live b ∨ (b = nb ∨ b = nb + 1 ∨ b = ks) := by
    intro b
    have L5 := E5.live_iff hs freshH b
    have l6 : H6.live b ↔ H5.live b ∨ b = ks := by
      rw [eH6']
      unfold Heap.live
      show (H5.bytes b ≠ none ∨ H5.words b ≠ none ∨ H5.streams b ≠ none ∨ H5.gzheaders b ≠ none ∨
        H5.dstates b ≠ none ∨ upd H5.istates ks (some st6) b ≠ none ∨ upd H5.gzstates i (some s6) b ≠ none) ↔ _
      by_cases e1 : b = ks
      · subst e1; simp
      by_cases e2 : b = i
      · subst e2; simp [h4]
      rw [upd_ne _ _ _ _ e1, upd_ne _ _ _ _ e2]
      simp [e1]
    rw [l6, L5]
    have nw : ∀ b, nb ≤ b → (H5.bytes b ≠ none ↔ b = nb ∨ b = nb + 1) := by
      intro b hb
      constructor
      · intro hn
        by_cases hge : H5.nextBlk ≤ b
        · exact absurd (E5.fresh b hge) hn
        · omega
      · rintro (e | e) <;> subst e
        · rw [ha0]; exact Option.some_ne_none _
        · rw [ha1]; exact Option.some_ne_none _
    constructor
    · rintro ((l | ⟨hb, hn⟩) | e)
      · exact Or.inl l
      · exact Or.inr (((nw b hb).1 hn).elim Or.inl (fun x => Or.inr (Or.inl x)))
      · exact Or.inr (Or.inr (Or.inr e))
    · rintro (l | e | e | e)
      · exact Or.inl (Or.inl l)
      · subst e; exact Or.inl (Or.inr ⟨Nat.le_refl _, (nw _ (Nat.le_refl _)).2 (Or.inl rfl)⟩)
      · subst e; exact Or.inl (Or.inr ⟨by omega, (nw _ (by omega)).2 (Or.inr rfl)⟩)
      · exact Or.inr e
  have frH : Frame H H6 (GzOwned H i s) := by
    rw [eH6']
    refine ⟨E5.static.symm, E5.allocOk.symm, E5.garbage.symm, by show H.nextBlk ≤ ks + 1; omega,
      by show H.nalloc ≤ H5.nalloc + 1; have := E5.nalloc; omega, fun b hl hno => ?_⟩
    have hbi : b ≠ i := fun e => hno (Or.inl e)
    have hb := hlt b hl
    have hbks : b ≠ ks := by omega
    refine ⟨E5.bytes b hb, E5.words b, E5.streams b, E5.gzheaders b, E5.dstates b, ?_, ?_, E5.ro b hb hl hbi⟩
    · show upd H5.istates ks (some st6) b = H.istates b
      rw [upd_ne _ _ _ _ hbks]; exact E5.istates b
    · show upd H5.gzstates i (some s6) b = H.gzstates b
      rw [upd_ne _ _ _ _ hbi, E5.gzstates, if_neg hbi]
  have post : GzPost H i s [] fs H6 GzInvUpToOutput := by
    refine post_step (D := fun _ => False) (C := fun b => b = nb ∨ b = nb + 1 ∨ b = ks) hu hu6 hfs rfl rfl frH
      (fun _ f => f.elim) ?_ ?_ ?_
    · rintro b (e | e | e) hl <;> have := hlt b hl <;> omega
    · intro b
      simp only [not_false_eq_true, and_true]
      constructor
      · rintro (e | e | e | ⟨-, e | ⟨-, e | so⟩⟩)
        · exact Or.inl (Or.inl e)
        · exact Or.inl (Or.inr (Or.inl e))
        · exact Or.inl (Or.inr (Or.inr (Or.inl e)))
        · cases e; exact Or.inr (Or.inl rfl)
        · cases e; exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr ((so6 b).1 so)))
      · rintro ((e | e | e | ⟨hz, -⟩) | e | e | e)
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl e))
        · exact absurd hsz hz
        · subst e; exact Or.inr (Or.inr (Or.inr ⟨hw0, Or.inl rfl⟩))
        · subst e; exact Or.inr (Or.inr (Or.inr ⟨hw0, Or.inr ⟨Or.inl hm, Or.inl rfl⟩⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hw0, Or.inr ⟨Or.inl hm, Or.inr ((so6 b).2 e)⟩⟩))
    · intro b
      simp only [not_false_eq_true, and_true]
      exact live6 b
  refine ⟨H6, ?_, s6, hs6, ⟨hu6, hm, hw0, hx0, hlook, fun _ => Or.inl rfl⟩, post, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold C.run at run6
  exact run6


theorem lookPost_transfer {H H6 : Heap} {i : Nat} {s s6 : GzState} {fs fs' : Fs} {r : Int32} {after : Heap}
    (p0 : GzPost H i s [] fs H6 GzInvUpToOutput) (hs6 : H6.gzstates i = some s6) (hsz : s.size = 0)
    (same : s6.mode = s.mode ∧ s6.fd = s.fd ∧ s6.skip = s.skip ∧ s6.x = s.x ∧
      s6.strm.avail_in = s.strm.avail_in ∧ s6.err = s.err)
    (L : LookPost H6 i s6 fs r fs' after) : LookPost H i s fs r fs' after := by
  obtain ⟨m, fd, sk, x, av, er⟩ := same
  obtain ⟨hr, hk, post, rf, rb, bud, s', hs', ⟨k1, k2, k3, k4, -⟩, ml, il, er', sz, res⟩ := L
  refine ⟨hr, hk, post_trans p0 hs6 post, by rw [← fd]; exact rf, by rw [← fd]; exact rb,
    by rw [← fd]; exact bud, s', hs', ⟨k1.trans m, k2.trans fd, k3.trans sk, by rw [k4, x], fun h => absurd hsz h⟩, ml, ?_,
    by rw [← er]; exact er', sz, by rw [← fd]; exact res⟩
  intro h
  have e : inputLeft fs s6 = inputLeft fs s := by unfold inputLeft; rw [fd, av]
  rw [← e]; exact il (by rw [fd]; exact h)

theorem ref_beq_null (r : BRef) (o : Nat) : ((Ptr.ref r o : BPtr) == Ptr.null) = false := rfl

theorem null_beq_null : ((Ptr.null : BPtr) == Ptr.null) = true := rfl

theorem look_freeB_null (H : Heap) : freeB (.null : BPtr) H = .ok ((), H) := rfl

theorem look_freeB_run {H : Heap} {b : Nat} {a : Array UInt8} (hb : H.bytes b = some a) (hro : H.ro b = false) :
    freeB (.ref (.blk b) 0) H = .ok ((), dHeap H b) := by
  rw [freeB_eq, hb]; simp [hro]

set_option maxHeartbeats 4000000 in
/-- **The allocation** (`size == 0`) and everything after it. -/
theorem lookAlloc_run {H : Heap} {i : Nat} {s : GzState} (fs : Fs) (hu : GzInvUpToOutput H i s)
    (hm : s.mode = GZ_READ) (hsz : s.size = 0) (hx0 : s.x.have = 0) (hfs : FileSystem fs) :
    ∃ r fs' after, lookAlloc i s fs H = .ok ((r, fs'), after) ∧ LookPost H i s fs r fs' after := by
  have hs := hu.1
  have c := hu.2.common
  have rd := hu.2.reader hm
  obtain ⟨freshH, uniqH, fitH, globalsH⟩ := upTo_base hu
  obtain ⟨-, hav0, -, hst0⟩ := rd.unalloc hsz
  have hav0' : s.strm.avail_in = 0 := hav0
  have hst0' : s.strm.state = none := hst0
  obtain ⟨lim1, olim1, eshift, lim2, olim2⟩ := want_lim (s := s) c.want
  have E0 := Ext.base hs freshH
  have slot0 : ¬ (H.slotUsed H.nextBlk = true) := by rw [Fresh.slotUsed_next freshH]; decide
  have none0 : ∀ x, H.nextBlk ≤ x → H.bytes x = none := fun x hx => Fresh.bytes freshH hx
  unfold lookAlloc
  by_cases a1 : H.allocOk H.nalloc = true
  · -- `in` allocated at block `H.nextBlk`
    have r1 : (StateT.lift (allocB s.want.toNat) : G BPtr) fs H =
        .ok ((.ref (.blk H.nextBlk) 0, fs), aHeap H s.want.toNat) := by
      rw [g_lift_app, allocB_eq, if_pos (show H.allocOk H.nalloc = true ∧ s.want.toNat < mallocLimit from ⟨a1, lim1⟩),
        if_neg slot0]
    let s1 : GzState := { s with «in» := .ref (.blk H.nextBlk) 0 }
    let H2 := Zlib.Gzlib.Spec.setS (aHeap H s.want.toNat) i s1
    have r2 : (StateT.lift (updS (some (.tab i)) fun s => { s with «in» := (.ref (.blk H.nextBlk) 0 : BPtr) }) :
        G Unit) fs (aHeap H s.want.toNat) = .ok (((), fs), H2) := by
      rw [g_lift_app, updS_run (show (aHeap H s.want.toNat).gzstates i = some s from hs)]
    have h2 : H2.gzstates i = some s1 := by simp [H2]
    have r3 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs H2 = .ok ((s1, fs), H2) := by
      rw [g_lift_app, ldS_run h2]
    have E2 : Ext H H2 i s1 := (E0.alloc _ olim1).setS s1
    have fresh2 := E2.fresh' hs freshH
    have slot2 : ¬ (H2.slotUsed H2.nextBlk = true) := by rw [Fresh.slotUsed_next fresh2]; decide
    have b2 : H2.bytes H.nextBlk = some (Array.ofFn (n := s.want.toNat) fun j => Junk.of (H.garbage H.nalloc j.val)) := by
      simp [H2, aHeap_bytes]
    by_cases a2 : H.allocOk (H.nalloc + 1) = true
    · -- both allocated
      have r4 : (StateT.lift (allocB (s1.want <<< 1).toNat) : G BPtr) fs H2 =
          .ok ((.ref (.blk (H.nextBlk + 1)) 0, fs), aHeap H2 (s1.want <<< 1).toNat) := by
        rw [g_lift_app, allocB_eq, if_pos (show H2.allocOk H2.nalloc = true ∧ (s1.want <<< 1).toNat < mallocLimit from
          ⟨a2, by show (s.want <<< 1).toNat < mallocLimit; rw [eshift]; exact lim2⟩), if_neg slot2]
        rfl
      let s2 : GzState := { s1 with out := .ref (.blk (H.nextBlk + 1)) 0 }
      let H4 := Zlib.Gzlib.Spec.setS (aHeap H2 (s1.want <<< 1).toNat) i s2
      have r5 : (StateT.lift (updS (some (.tab i)) fun s => { s with out := (.ref (.blk (H.nextBlk + 1)) 0 : BPtr) }) :
          G Unit) fs (aHeap H2 (s1.want <<< 1).toNat) = .ok (((), fs), H4) := by
        rw [g_lift_app, updS_run (show (aHeap H2 (s1.want <<< 1).toNat).gzstates i = some s1 from h2)]
      have h4 : H4.gzstates i = some s2 := by simp [H4]
      simp only [g_bind_app, r1, r2, r3, r4, r5]
      rw [if_neg (by simp only [ref_beq_null]; decide)]
      let s3 : GzState := { s2 with size := s2.want }
      let H5' := Zlib.Gzlib.Spec.setS H4 i s3
      let z4 : ZStream := { s3.strm with zalloc := .null, zfree := .null, «opaque» := .null, avail_in := 0, next_in := .null }
      let s4 : GzState := { s3 with strm := z4 }
      let H5 := Zlib.Gzlib.Spec.setS H5' i s4
      have r6 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs H4 = .ok ((s2, fs), H4) := by
        rw [g_lift_app, ldS_run h4]
      have r7 : (StateT.lift (updS (some (.tab i)) fun s => { s with size := s.want }) : G Unit) fs H4 =
          .ok (((), fs), H5') := by
        rw [g_lift_app, updS_run h4]
      have h5' : H5'.gzstates i = some s3 := by simp [H5']
      have r8 : (StateT.lift (updZ (strmOf (some (.tab i))) fun z => { z with zalloc := .null, zfree := .null, «opaque» := .null, avail_in := 0, next_in := .null }) : G Unit) fs H5' = .ok (((), fs), H5) := by
        rw [g_lift_app, strmOf_tab, updZ_run h5']
      have r9 : (StateT.lift (strLitRef ZLIB_VERSION) : G BPtr) fs H5 = .ok ((.ref (.str 57) 0, fs), H5) := by
        rw [g_lift_app, strLitRef_of_index version_index]
      simp only [g_bind_app, r6, r7, r8, r9]
      have E5 : Ext H H5 i s4 :=
        (((E2.alloc _ (by show (s.want <<< 1).toNat < _; rw [eshift]; exact olim2)).setS s2).setS s3).setS s4
      have h5 : H5.gzstates i = some s4 := E5.recd
      have hb0 : ∃ a, H5.bytes H.nextBlk = some a ∧ a.size = s.want.toNat := by
        refine ⟨Array.ofFn (n := s.want.toNat) fun j => Junk.of (H.garbage H.nalloc j.val), ?_, Array.size_ofFn⟩
        show (aHeap H2 (s1.want <<< 1).toNat).bytes H.nextBlk = _
        rw [aHeap_bytes, upd_ne _ _ _ _ (by show H.nextBlk ≠ H.nextBlk + 1; omega)]
        exact b2
      have hb1 : ∃ a, H5.bytes (H.nextBlk + 1) = some a ∧ a.size = 2 * s.want.toNat := by
        refine ⟨Array.ofFn (n := (s1.want <<< 1).toNat) fun j => Junk.of (H2.garbage H2.nalloc j.val), ?_,
          by rw [Array.size_ofFn]; exact eshift⟩
        show (aHeap H2 (s1.want <<< 1).toNat).bytes (H.nextBlk + 1) = _
        rw [aHeap_bytes]
        exact upd_same _ _ _
      have hro0 : H5.ro H.nextBlk = false := by
        show (aHeap H2 (s1.want <<< 1).toNat).ro H.nextBlk = false
        rw [aHeap_ro, upd_ne _ _ _ _ (by show H.nextBlk ≠ H.nextBlk + 1; omega)]
        show (aHeap H s.want.toNat).ro H.nextBlk = false
        rw [aHeap_ro]; exact upd_same _ _ _
      have hro1 : H5.ro (H.nextBlk + 1) = false := by
        show (aHeap H2 (s1.want <<< 1).toNat).ro (H.nextBlk + 1) = false
        rw [aHeap_ro]; exact upd_same _ _ _
      by_cases a3 : H5.allocOk H5.nalloc = true
      · obtain ⟨H6, run6, s6, hs6, P6, post6, m6, fd6, sk6, x6, av6, er6⟩ :=
          init_success fs hfs hu hm hsz hx0 E5 rfl hb0 hb1 hro0 hro1 a3
        have r10 : (StateT.lift (Zlib.Inflate.inflateInit2_ (strmOf (some (.tab i))) 31 (.ref (.str 57) 0) 112) :
            G Int32) fs H5 = .ok ((Z_OK, fs), H6) := by
          rw [g_lift_app, strmOf_tab, run6]
        simp only [g_bind_app, r10]
        rw [if_neg (by simp)]
        obtain ⟨r, fs', after, runM, LP⟩ := lookMain_run fs P6 hfs
        exact ⟨r, fs', after, runM, lookPost_transfer post6 hs6 hsz
          ⟨m6, fd6, sk6, x6, by rw [av6, hav0'], er6⟩ LP⟩
      · -- `inflateInit2_` failed
        have fresh5 : Fresh H5 := E5.fresh' hs freshH
        have hz5 : (ZStreamRef.in_gzstate_strm i).get H5 = some z4 := by simp [ZStreamRef.get, h5, s4]
        obtain ⟨hvn, hv0⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read (version_value H5)
        have run6 := inflateInit2_memfail (w := 31) hz5 fresh5 a3 (Or.inl rfl) (Or.inl rfl) hvn hv0
        let s5 : GzState := { s4 with strm := initStream z4 }
        have eHm : initMemHeap H5 (.in_gzstate_strm i) z4 = fHeap (Zlib.Gzlib.Spec.setS H5 i s5) := by
          simp [initMemHeap, fHeap, ZStreamRef.put, h5, Zlib.Gzlib.Spec.setS, s5]
        rw [eHm] at run6
        let Hm := fHeap (Zlib.Gzlib.Spec.setS H5 i s5)
        have r10 : (StateT.lift (Zlib.Inflate.inflateInit2_ (strmOf (some (.tab i))) 31 (.ref (.str 57) 0) 112) :
            G Int32) fs H5 = .ok ((Z_MEM_ERROR, fs), Hm) := by
          rw [g_lift_app, strmOf_tab, run6]
        have hm5 : Hm.gzstates i = some s5 := by simp [Hm, fHeap]
        have r11 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs Hm = .ok ((s5, fs), Hm) := by
          rw [g_lift_app, ldS_run hm5]
        obtain ⟨a1', ha1', -⟩ := hb1
        obtain ⟨a0', ha0', -⟩ := hb0
        have r12 : (StateT.lift (freeB s5.out) : G Unit) fs Hm = .ok (((), fs), dHeap Hm (H.nextBlk + 1)) := by
          rw [g_lift_app]
          rw [show freeB s5.out Hm = .ok ((), dHeap Hm (H.nextBlk + 1)) from look_freeB_run (b := H.nextBlk + 1)
            (by show H5.bytes _ = _; exact ha1') (by show H5.ro _ = _; exact hro1)]
        have r13 : (StateT.lift (freeB s5.«in») : G Unit) fs (dHeap Hm (H.nextBlk + 1)) =
            .ok (((), fs), dHeap (dHeap Hm (H.nextBlk + 1)) H.nextBlk) := by
          rw [g_lift_app]
          rw [show freeB s5.«in» (dHeap Hm (H.nextBlk + 1)) = .ok ((), dHeap (dHeap Hm (H.nextBlk + 1)) H.nextBlk)
            from look_freeB_run (b := H.nextBlk)
            (by show upd H5.bytes (H.nextBlk + 1) none H.nextBlk = _
                rw [upd_ne _ _ _ _ (by omega)]; exact ha0')
            (by show H5.ro _ = _; exact hro0)]
        let s7 : GzState := { s5 with size := 0 }
        let Hq := Zlib.Gzlib.Spec.setS (dHeap (dHeap Hm (H.nextBlk + 1)) H.nextBlk) i s7
        have r14 : (StateT.lift (updS (some (.tab i)) fun s => { s with size := 0 }) : G Unit) fs
            (dHeap (dHeap Hm (H.nextBlk + 1)) H.nextBlk) = .ok (((), fs), Hq) := by
          have hm5' : (dHeap (dHeap Hm (H.nextBlk + 1)) H.nextBlk).gzstates i = some s5 := by
            rw [dHeap_gz, dHeap_gz]; exact hm5
          rw [g_lift_app, updS_run hm5']
        simp only [g_bind_app, r10]
        rw [if_pos (by simp [Z_MEM_ERROR, Z_OK])]
        simp only [g_bind_app, r11, r12, r13, r14]
        have Eq : Ext H Hq i s7 := ((((E5.setS s5).failed).drop _ (by omega)).drop _ (Nat.le_refl _)).setS s7
        obtain ⟨after, run, LP⟩ := fail_err fs hfs hu hm hsz hx0 Eq
          (fun x hx => by
            show upd (upd H5.bytes (H.nextBlk + 1) none) H.nextBlk none x = none
            by_cases e0 : x = H.nextBlk
            · subst e0; exact upd_same _ _ _
            rw [upd_ne _ _ _ _ e0]
            by_cases e1 : x = H.nextBlk + 1
            · subst e1; exact upd_same _ _ _
            rw [upd_ne _ _ _ _ e1]
            exact E5.fresh x (by show H.nextBlk + 2 ≤ x; omega))
          (p := .ref (.blk H.nextBlk) 0) (q := .ref (.blk (H.nextBlk + 1)) 0) (zq := initStream z4) rfl rfl
          (by show s.strm.state = none; exact hst0') rfl
        refine ⟨-1, fs, after, ?_, LP⟩
        simp only [g_bind_app, g_lift_app] at run
        try simp only [g_bind_app, g_lift_app, look_freeB_null] at ⊢
        try exact run
    · -- `out` failed
      have r4 : (StateT.lift (allocB (s1.want <<< 1).toNat) : G BPtr) fs H2 = .ok ((.null, fs), fHeap H2) := by
        rw [g_lift_app, allocB_eq, if_neg (show ¬ (H2.allocOk H2.nalloc = true ∧ (s1.want <<< 1).toNat < mallocLimit)
          from fun x => a2 x.1)]
      let s2 : GzState := { s1 with out := .null }
      let H4 := Zlib.Gzlib.Spec.setS (fHeap H2) i s2
      have r5 : (StateT.lift (updS (some (.tab i)) fun s => { s with out := (.null : BPtr) }) : G Unit) fs (fHeap H2) =
          .ok (((), fs), H4) := by
        rw [g_lift_app, updS_run (show (fHeap H2).gzstates i = some s1 from h2)]
      have r6 : (StateT.lift (freeB (.null : BPtr)) : G Unit) fs H4 = .ok (((), fs), H4) := rfl
      have r7 : (StateT.lift (freeB (.ref (.blk H.nextBlk) 0 : BPtr)) : G Unit) fs H4 =
          .ok (((), fs), dHeap H4 H.nextBlk) := by
        rw [g_lift_app, look_freeB_run (by show H2.bytes _ = _; exact b2)
          (by show (aHeap H s.want.toNat).ro _ = _; rw [aHeap_ro]; exact upd_same _ _ _)]
      simp only [g_bind_app, r1, r2, r3, r4, r5]
      rw [if_pos (by simp only [ref_beq_null, null_beq_null]; decide)]
      simp only [g_bind_app, r6, r7]
      have Eq : Ext H (dHeap H4 H.nextBlk) i s2 := ((E2.failed).setS s2).drop _ (Nat.le_refl _)
      obtain ⟨after, run, LP⟩ := fail_err fs hfs hu hm hsz hx0 Eq
        (fun x hx => by
          show upd (aHeap H s.want.toNat).bytes H.nextBlk none x = none
          by_cases e0 : x = H.nextBlk
          · subst e0; exact upd_same _ _ _
          rw [upd_ne _ _ _ _ e0, aHeap_bytes, upd_ne _ _ _ _ e0]
          exact none0 x hx)
        (p := .ref (.blk H.nextBlk) 0) (q := .null) (zq := s.strm) rfl hsz hst0' hav0'
      refine ⟨-1, fs, after, ?_, LP⟩
      simp only [g_bind_app, g_lift_app] at run
      try simp only [g_bind_app, g_lift_app, look_freeB_null] at ⊢
      try exact run
  · -- `in` failed
    have r1 : (StateT.lift (allocB s.want.toNat) : G BPtr) fs H = .ok ((.null, fs), fHeap H) := by
      rw [g_lift_app, allocB_eq, if_neg (show ¬ (H.allocOk H.nalloc = true ∧ s.want.toNat < mallocLimit)
        from fun x => a1 x.1)]
    let s1 : GzState := { s with «in» := .null }
    let H2 := Zlib.Gzlib.Spec.setS (fHeap H) i s1
    have r2 : (StateT.lift (updS (some (.tab i)) fun s => { s with «in» := (.null : BPtr) }) : G Unit) fs (fHeap H) =
        .ok (((), fs), H2) := by
      rw [g_lift_app, updS_run (show (fHeap H).gzstates i = some s from hs)]
    have h2 : H2.gzstates i = some s1 := by simp [H2]
    have r3 : (StateT.lift (ldS (some (.tab i))) : G GzState) fs H2 = .ok ((s1, fs), H2) := by
      rw [g_lift_app, ldS_run h2]
    have E2 : Ext H H2 i s1 := (E0.failed).setS s1
    have fresh2 := E2.fresh' hs freshH
    have slot2 : ¬ (H2.slotUsed H2.nextBlk = true) := by rw [Fresh.slotUsed_next fresh2]; decide
    have r6 : ∀ fs' h', (StateT.lift (freeB (.null : BPtr)) : G Unit) fs' h' = .ok (((), fs'), h') := fun _ _ => rfl
    by_cases a2 : H.allocOk (H.nalloc + 1) = true
    · have r4 : (StateT.lift (allocB (s1.want <<< 1).toNat) : G BPtr) fs H2 =
          .ok ((.ref (.blk H.nextBlk) 0, fs), aHeap H2 (s1.want <<< 1).toNat) := by
        rw [g_lift_app, allocB_eq, if_pos (show H2.allocOk H2.nalloc = true ∧ (s1.want <<< 1).toNat < mallocLimit from
          ⟨a2, by show (s.want <<< 1).toNat < mallocLimit; rw [eshift]; exact lim2⟩), if_neg slot2]
        rfl
      let s2 : GzState := { s1 with out := .ref (.blk H.nextBlk) 0 }
      let H4 := Zlib.Gzlib.Spec.setS (aHeap H2 (s1.want <<< 1).toNat) i s2
      have r5 : (StateT.lift (updS (some (.tab i)) fun s => { s with out := (.ref (.blk H.nextBlk) 0 : BPtr) }) :
          G Unit) fs (aHeap H2 (s1.want <<< 1).toNat) = .ok (((), fs), H4) := by
        rw [g_lift_app, updS_run (show (aHeap H2 (s1.want <<< 1).toNat).gzstates i = some s1 from h2)]
      have r7 : (StateT.lift (freeB (.ref (.blk H.nextBlk) 0 : BPtr)) : G Unit) fs H4 =
          .ok (((), fs), dHeap H4 H.nextBlk) := by
        rw [g_lift_app, look_freeB_run (by show (aHeap H2 (s1.want <<< 1).toNat).bytes _ = _; rw [aHeap_bytes]; exact upd_same _ _ _)
          (by show (aHeap H2 (s1.want <<< 1).toNat).ro _ = _; rw [aHeap_ro]; exact upd_same _ _ _)]
      simp only [g_bind_app, r1, r2, r3, r4, r5]
      rw [if_pos (by simp only [ref_beq_null, null_beq_null]; decide)]
      simp only [g_bind_app, r6, r7]
      have Eq : Ext H (dHeap H4 H.nextBlk) i s2 :=
        (((E2.alloc _ (by show (s.want <<< 1).toNat < _; rw [eshift]; exact olim2)).setS s2).drop _ (Nat.le_refl _))
      obtain ⟨after, run, LP⟩ := fail_err fs hfs hu hm hsz hx0 Eq
        (fun x hx => by
          show upd (aHeap H2 (s1.want <<< 1).toNat).bytes H.nextBlk none x = none
          by_cases e0 : x = H.nextBlk
          · subst e0; exact upd_same _ _ _
          rw [upd_ne _ _ _ _ e0, aHeap_bytes, upd_ne _ _ _ _ (show x ≠ H2.nextBlk from e0)]
          exact none0 x hx)
        (p := .null) (q := .ref (.blk H.nextBlk) 0) (zq := s.strm) rfl hsz hst0' hav0'
      refine ⟨-1, fs, after, ?_, LP⟩
      simp only [g_bind_app, g_lift_app] at run
      try simp only [g_bind_app, g_lift_app, look_freeB_null] at ⊢
      try exact run
    · have r4 : (StateT.lift (allocB (s1.want <<< 1).toNat) : G BPtr) fs H2 = .ok ((.null, fs), fHeap H2) := by
        rw [g_lift_app, allocB_eq, if_neg (show ¬ (H2.allocOk H2.nalloc = true ∧ (s1.want <<< 1).toNat < mallocLimit)
          from fun x => a2 x.1)]
      let s2 : GzState := { s1 with out := .null }
      let H4 := Zlib.Gzlib.Spec.setS (fHeap H2) i s2
      have r5 : (StateT.lift (updS (some (.tab i)) fun s => { s with out := (.null : BPtr) }) : G Unit) fs (fHeap H2) =
          .ok (((), fs), H4) := by
        rw [g_lift_app, updS_run (show (fHeap H2).gzstates i = some s1 from h2)]
      simp only [g_bind_app, r1, r2, r3, r4, r5]
      rw [if_pos (by simp only [ref_beq_null, null_beq_null]; decide)]
      simp only [g_bind_app, r6]
      have Eq : Ext H H4 i s2 := ((E2.failed).setS s2)
      obtain ⟨after, run, LP⟩ := fail_err fs hfs hu hm hsz hx0 Eq (fun x hx => none0 x hx)
        (p := .null) (q := .null) (zq := s.strm) rfl hsz hst0' hav0'
      refine ⟨-1, fs, after, ?_, LP⟩
      simp only [g_bind_app, g_lift_app] at run
      try simp only [g_bind_app, g_lift_app, look_freeB_null] at ⊢
      try exact run

end alloc

end Look

/-! ## `gz_look` -/

open Look in

/-- **`gz_look(state)` is safe** (`GzLookSpec`). -/
theorem gz_look_safe : GzLookSpec := by
  intro i h fs s hu hx hfs hm hlook hml
  have key : ∃ r fs' after, Zlib.Gzread.gz_look (gzSt i) fs h = .ok ((r, fs'), after) ∧
      LookPost h i s fs r fs' after := by
    rw [gz_look_source]
    have hld : (StateT.lift (ldS (some (.tab i))) : G GzState) fs h = .ok ((s, fs), h) := by
      rw [g_lift_app, ldS_run hu.1]
    simp only [g_bind_app, hld]
    by_cases hz : s.size = 0
    · rw [if_pos (by simp [hz])]
      exact lookAlloc_run fs hu hm hz hx hfs
    · rw [if_neg (by simpa using hz)]
      exact lookMain_run fs ⟨hu, hm, hz, hx, hlook, hml⟩ hfs
  obtain ⟨r, fs', after, run, post⟩ := key
  refine ⟨fun e he => ?_, fun _ => ⟨r, fs', after, run⟩, fun r' fs3 after' he => ?_⟩
  · rw [run] at he; cases he
  · rw [run] at he
    cases he
    exact post

#print axioms gz_look_safe

end ZlibF.Spec.Public.GzRead
