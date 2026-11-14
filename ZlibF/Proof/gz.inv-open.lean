import ZlibF.Proof.«gzlib.c.dopen-complete»
import ZlibF.Proof.«gz.inv-seek»
import ZlibF.Spec.Public.GzSafety

/-!
# gz file interface, safety: a fresh handle is in `GzInv`; `gzdopen`

The skeleton leaf `gzdopen_safe` (`skeleton/gz`, `gz.skeleton.lean`), and the facts it shares with `gzopen`:

1. `open_inv`: a record in `OpenState` (the public open contract), with no codec (`strm.state` NULL), no pending
   input pointer (`strm.next_in` NULL), the writer's `reset` cleared, an accepted `direct`, a private path block other
   than the record, and object sizes in the platform scope, is in `GzInv`. `OpenState` gives `size = 0`, so every
   clause about buffers or buffered output is vacuous.
2. `parsedOpenRecord_inv_facts`: the record that `gz_open` actually returns has those extra fields. They are fields
   of the fresh record that `gz_open` does not write: in the model a fresh pointer is NULL (`GzState.garbage`), which
   is weaker than C. C never reads `strm.state` or `strm.next_in` before `gz_look` or `gz_init` writes them
   (`docs/spec/safety.md`, section 3).
3. `gz_open_supplied_shape`: the world and heap of every return of `gz_open` with a supplied descriptor.
4. `fit_of_frame_new`: the platform object bound after a call that frames the caller's heap.
5. `gzdopen_safe_proof`, restated as the skeleton's `gzdopen_safe`.

Patches: none beyond those of the reused open lemmas.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Math.GzModeParser
set_option autoImplicit false

/-! ## The fields of the record `gz_open` returns -/

theorem modeActionState_strm (s : GzState) (a : Action) : (modeActionState s a).strm = s.strm := by
  cases a with
  | mode m => cases m <;> rfl
  | _ => rfl

theorem modeActionState_direct (s : GzState) (a : Action) :
    (modeActionState s a).direct = s.direct ∨ (modeActionState s a).direct = -1 ∨
      (modeActionState s a).direct = 1 := by
  cases a with
  | mode m => cases m <;> exact Or.inl rfl
  | gzipOnly => exact Or.inr (Or.inl rfl)
  | transparent => exact Or.inr (Or.inr rfl)
  | _ => exact Or.inl rfl

/-- The mode loop leaves the embedded stream alone and sets `direct` only to -1 or 1. -/
theorem modeFold_strm_direct (bs : List UInt8) (q : ModeAccum)
    (hq : q.state.direct = -1 ∨ q.state.direct = 0 ∨ q.state.direct = 1) :
    (modeFold bs q).state.strm = q.state.strm ∧
      ((modeFold bs q).state.direct = -1 ∨ (modeFold bs q).state.direct = 0 ∨
        (modeFold bs q).state.direct = 1) := by
  induction bs generalizing q with
  | nil => exact ⟨rfl, hq⟩
  | cons b bs ih =>
    have hstep : (modeAccumStep q b).state.direct = -1 ∨ (modeAccumStep q b).state.direct = 0 ∨
        (modeAccumStep q b).state.direct = 1 := by
      rcases modeActionState_direct q.state (sourceAction b) with e | e | e
      · have e' : (modeAccumStep q b).state.direct = q.state.direct := e
        rw [e']
        exact hq
      · exact Or.inl e
      · exact Or.inr (Or.inr e)
    have htail := ih (modeAccumStep q b) hstep
    exact ⟨htail.1.trans (modeActionState_strm q.state (sourceAction b)), htail.2⟩

/-- `gz_reset` keeps `direct`, the mode and the codec pointers, and clears a writer's `reset`. -/
theorem resetRec_keep (t : GzState) :
    (resetRec t).direct = t.direct ∧ (resetRec t).mode = t.mode ∧
      (resetRec t).strm.state = t.strm.state ∧ (resetRec t).strm.next_in = t.strm.next_in ∧
      (t.mode ≠ GZ_READ → (resetRec t).reset = 0) := by
  unfold resetRec
  by_cases hm : t.mode = GZ_READ <;> simp [hm]

/-- The record that `gz_open` returns for an accepted mode has no codec, no pending input pointer, `reset = 0` for
a writer, and an accepted `direct` (-1, 0 or 1; 0 or 1 for a writer). -/
theorem parsedOpenRecord_inv_facts (h : Heap) (bs : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (level : Int) (strategy : Nat) (direct : Int) (fd : Int32) (fs : Fs)
    (hp : ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct))
    (s : GzState) (hs : s = parsedOpenRecord h bs mode fd fs) :
    s.strm.state = none ∧ s.strm.next_in = .null ∧ (s.mode = GZ_WRITE → s.reset = 0) ∧
      (s.direct = -1 ∨ s.direct = 0 ∨ s.direct = 1) ∧
      (s.mode = GZ_WRITE → s.direct = 0 ∨ s.direct = 1) := by
  obtain ⟨hm, _, _, _, _, hwrite⟩ := modePrepared_parsed h bs mode level strategy direct hp
  have hfold := modeFold_strm_direct bs { state := openFrontRecord h, flags := 0, exclusive := 0 }
    (Or.inr (Or.inl rfl))
  have hst : (modePreparedRecord h bs).strm = (openFrontRecord h).strm := hfold.1
  have hd0 : (modePreparedRecord h bs).direct = -1 ∨ (modePreparedRecord h bs).direct = 0 ∨
      (modePreparedRecord h bs).direct = 1 := hfold.2
  subst hs
  unfold parsedOpenRecord
  obtain ⟨rd, rm, rs, rn, rr⟩ := resetRec_keep
    (suppliedRecord (modeCopiedRecord (modePreparedHeap h bs) (modePreparedRecord h bs) mode) mode fd fs)
  have tstrm : (suppliedRecord (modeCopiedRecord (modePreparedHeap h bs) (modePreparedRecord h bs) mode)
      mode fd fs).strm = (modePreparedRecord h bs).strm := by
    by_cases hc : mode = .read ∧ (modePreparedRecord h bs).direct = 0
    · simp only [suppliedRecord, modeCopiedRecord, checkedModeRecord, if_pos hc]
    · simp only [suppliedRecord, modeCopiedRecord, checkedModeRecord, if_neg hc]
  have tdir : (suppliedRecord (modeCopiedRecord (modePreparedHeap h bs) (modePreparedRecord h bs) mode)
      mode fd fs).direct =
      if mode = .read ∧ (modePreparedRecord h bs).direct = 0 then 1 else (modePreparedRecord h bs).direct := by
    by_cases hc : mode = .read ∧ (modePreparedRecord h bs).direct = 0
    · rw [if_pos hc]
      simp only [suppliedRecord, modeCopiedRecord, checkedModeRecord, if_pos hc]
    · rw [if_neg hc]
      simp only [suppliedRecord, modeCopiedRecord, checkedModeRecord, if_neg hc]
  have tmode : (suppliedRecord (modeCopiedRecord (modePreparedHeap h bs) (modePreparedRecord h bs) mode)
      mode fd fs).mode = if mode = .append then GZ_WRITE else (modePreparedRecord h bs).mode := by
    by_cases hc : mode = .read ∧ (modePreparedRecord h bs).direct = 0
    · simp only [suppliedRecord, modeCopiedRecord, checkedModeRecord, if_pos hc]
    · simp only [suppliedRecord, modeCopiedRecord, checkedModeRecord, if_neg hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rs, tstrm, hst]
    rfl
  · rw [rn, tstrm, hst]
    rfl
  · intro hw
    apply rr
    rw [← rm, hw]
    decide
  · rw [rd, tdir]
    by_cases hc : mode = .read ∧ (modePreparedRecord h bs).direct = 0
    · rw [if_pos hc]
      exact Or.inr (Or.inr rfl)
    · rw [if_neg hc]
      exact hd0
  · intro hw
    have hnr : mode ≠ .read := by
      intro hr
      subst hr
      rw [rm, tmode, hm] at hw
      simp [modeCode, GZ_READ, GZ_WRITE] at hw
    rw [rd, tdir, if_neg (fun hc => hnr hc.1)]
    rcases hd0 with e | e | e
    · exact absurd e (hwrite hnr)
    · exact Or.inl e
    · exact Or.inr e

/-! ## The returns of `gz_open` with a supplied descriptor -/

/-- Every return of `gz_open` with a supplied descriptor: NULL leaves the world as it was; a handle is the parsed
record at the first new block, with the world of the start or end `lseek` and the exact heap of the run. -/
theorem gz_open_supplied_shape (h : Heap) (fs : Fs) (path modePtr : BPtr) (fd : Int32)
    (bs name : List UInt8) (hf : Fresh h) (hu : Uniq h)
    (hc : ZlibF.Spec.Public.CString h path name) (hmode : ZlibF.Spec.Public.CString h modePtr bs)
    (hlen : name.length ≤ 2147483647) (hfd : fd ≠ -1)
    (file : GzFilePtr) (fs' : Fs) (after : Heap)
    (hrun : gz_open path fd modePtr fs h = .ok ((file, fs'), after)) :
    (file = none → fs' = fs) ∧
    (∀ i, file = some (.in_gzstate_x i) → ∃ mode level strategy direct,
      ZlibF.Spec.Public.parsedMode bs = some (mode, level, strategy, direct) ∧ i = h.nextBlk ∧
      fs' = suppliedWorld mode fd fs ∧ after = parsedOpenHeap h bs mode name fd fs) := by
  obtain ⟨pr, po, pa, hpp, _, _, _⟩ := writerCString_view h path name hc
  obtain ⟨mr, mo, ma, hmp, _, _, _⟩ := writerCString_view h modePtr bs hmode
  have hpn : path ≠ .null := by simp [hpp]
  have hmn : modePtr ≠ .null := by simp [hmp]
  by_cases ha : h.allocOk h.nalloc = true
  · cases hp : ZlibF.Spec.Public.parsedMode bs with
    | none =>
      rw [gz_open_parsed_reject h fs path modePtr fd bs hf hpn hmode hp ha] at hrun
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨⟨rfl, rfl⟩, -⟩ := hrun
      exact ⟨fun _ => rfl, fun i hi => by cases hi⟩
    | some parsed =>
      rcases parsed with ⟨mode, level, strategy, direct⟩
      by_cases ha1 : h.allocOk (h.nalloc + 1) = true
      · rw [gz_open_parsed_supplied_run h fs path modePtr fd bs name mode level strategy direct
          hf hu hc hmode hp hlen hfd ha ha1] at hrun
        simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrun
        refine ⟨fun hn => (by cases hn), fun i hi => ?_⟩
        simp only [Option.some.injEq, GzFileRef.in_gzstate_x.injEq] at hi
        exact ⟨mode, level, strategy, direct, rfl, hi.symm, rfl, rfl⟩
      · have he : h.allocOk (h.nalloc + 1) = false := by simpa using ha1
        rw [gz_open_parsed_path_failure h fs path modePtr fd bs name mode level strategy direct
          hf hc hmode hp ha he] at hrun
        simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨⟨rfl, rfl⟩, -⟩ := hrun
        exact ⟨fun _ => rfl, fun i hi => by cases hi⟩
  · have he : h.allocOk h.nalloc = false := by simpa using ha
    rw [gz_open_alloc_failure h fs path fd modePtr hpn hmn he] at hrun
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨⟨rfl, rfl⟩, -⟩ := hrun
    exact ⟨fun _ => rfl, fun i hi => by cases hi⟩

/-- The start or end `lseek` of a supplied descriptor keeps a well-formed world and its open descriptors. -/
theorem suppliedWorld_fs {fs : Fs} (hfs : ZlibF.Spec.Public.FileSystem fs) (mode : ZlibF.Spec.Api.GzMode)
    (fd : Int32) :
    ZlibF.Spec.Public.FileSystem (suppliedWorld mode fd fs) ∧
      ZlibF.Spec.Public.FdsKept fs (suppliedWorld mode fd fs) := by
  cases mode with
  | read => exact ZlibF.Spec.Public.lseekRes_fs hfs fd 0 SEEK_CUR
  | write => exact ⟨hfs, fun _ => Iff.rfl⟩
  | append => exact ZlibF.Spec.Public.lseekRes_fs hfs fd 0 SEEK_END

/-- The private path of the record `gz_open` returns holds the path and its NUL. -/
theorem parsedOpenHeap_path_bytes (h : Heap) (bs : List UInt8) (mode : ZlibF.Spec.Api.GzMode)
    (name : List UInt8) (fd : Int32) (fs : Fs) :
    (parsedOpenHeap h bs mode name fd fs).bytes (h.nextBlk + 1) = some (name.toArray.push 0) := by
  show (writerFormattedHeap (checkedModeHeap (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode)
    h.nextBlk (checkedModeRecord (modePreparedRecord h bs) mode) name).bytes (h.nextBlk + 1) = _
  have hnb : (checkedModeHeap (modePreparedHeap h bs) h.nextBlk (modePreparedRecord h bs) mode).nextBlk =
      h.nextBlk + 1 := by
    rw [(checkedMode_counts _ _ _ _).1]
    rfl
  rw [← hnb]
  exact writerFormatted_private_bytes _ _ _ _

/-! ## Heap facts -/

theorem uniq_gz_bytes {H : Heap} (u : Uniq H) {x : Nat} {g : GzState} {a : Array UInt8}
    (hg : H.gzstates x = some g) (ha : H.bytes x = some a) : False := by
  have hu := u x
  rw [hg, ha] at hu
  simp only [cnt_some] at hu
  omega

theorem uniq_gz_dstates {H : Heap} (u : Uniq H) {x : Nat} {g : GzState} {d : DeflateState}
    (hg : H.gzstates x = some g) (hd : H.dstates x = some d) : False := by
  have hu := u x
  rw [hg, hd] at hu
  simp only [cnt_some] at hu
  omega

theorem uniq_bytes_dstates {H : Heap} (u : Uniq H) {x : Nat} {a : Array UInt8} {d : DeflateState}
    (ha : H.bytes x = some a) (hd : H.dstates x = some d) : False := by
  have hu := u x
  rw [ha, hd] at hu
  simp only [cnt_some] at hu
  omega

/-- The platform object bound after a call that frames the caller's heap: the old objects keep their sizes, and
every block that was not live before is bounded or holds no deflate state. -/
theorem fit_of_frame_new {h after : Heap} (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (fr : ZlibF.Spec.Public.Frame h after (fun _ => False))
    (hB : ∀ b a, ¬ h.live b → after.bytes b = some a → a.size < ZlibF.PlatformMemory.byteObjectLimit)
    (hD : ∀ b d, ¬ h.live b → after.dstates b ≠ some d) :
    ZlibF.PlatformMemory.ByteObjectsFit after := by
  have statics : after.static = h.static := fr.1.symm
  intro ref arr get
  cases ref with
  | blk b =>
    change after.bytes b = some arr at get
    by_cases hl : h.live b
    · rw [(fr.2.2.2.2.2 b hl not_false).1] at get
      exact fit (.blk b) arr get
    · exact hB b arr hl get
  | str i =>
    by_cases source : i < strTable.size
    · have same := C.LibcBorrow.str_view_stable (before := h) (after := after) (i := i) (Or.inl source)
      rw [same] at get
      exact fit (.str i) arr get
    · have bounded := C.LibcBorrow.external_view_size (by omega : strTable.size ≤ i) get
      unfold ZlibF.PlatformMemory.byteObjectLimit
      omega
  | dstate_depth b =>
    change (after.dstates b).map (·.depth) = some arr at get
    cases hd : after.dstates b with
    | none =>
      rw [hd] at get
      cases get
    | some d =>
      by_cases hl : h.live b
      · have e := (fr.2.2.2.2.2 b hl not_false).2.2.2.2.1
        apply fit (.dstate_depth b) arr
        change (h.dstates b).map (·.depth) = some arr
        rw [← e]
        exact get
      · exact absurd hd (hD b d hl)
  | st_dist_code => exact fit .st_dist_code arr (by simpa only [Space.get, statics] using get)
  | st_length_code => exact fit .st_length_code arr (by simpa only [Space.get, statics] using get)

end Zlib.Gzlib.Proofs

namespace ZlibF.Spec.Public.GzOpenInv
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- **A fresh handle is in `GzInv`.** `OpenState` with the fields `gz_open` leaves in the fresh record (no codec, no
pending input pointer, the writer's `reset` cleared, an accepted `direct`), a private path block other than the
record, and object sizes in the platform scope. -/
theorem open_inv {h : Heap} {i pb : Nat} {s : GzState} {mode : Api.GzMode} {level : Int}
    {strategy : Nat} {direct : Int} {fd : Int32} {name : List UInt8}
    (ho : OpenState h i s mode level strategy direct fd name)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (hpath : s.path = .ref (.blk pb) 0) (hpb : pb ≠ i)
    (hstate : s.strm.state = none) (hnext : s.strm.next_in = .null)
    (hreset : s.mode = GZ_WRITE → s.reset = 0)
    (hdir : s.direct = -1 ∨ s.direct = 0 ∨ s.direct = 1)
    (hwdir : s.mode = GZ_WRITE → s.direct = 0 ∨ s.direct = 1) : GzInv h i s := by
  obtain ⟨⟨hrec, hm, hfresh, huniq, hglob, hpathx, hmsgx, hmemerr, hw8, hw31, -, -⟩,
    hmode, -, -, -, -, -, hsize, -, herrO, hmsg, hhave, hpos, hpast, hagain, hskip, havail, hread⟩ := ho
  have nso : ∀ b, ¬ StreamOwned h (gzStrm i) b := noCodec_owned hrec hstate
  have hown : ownedPtrs s = [.ref (.blk pb) 0, .null] := by
    simp [ownedPtrs, hsize, hpath, hmsg]
  have common : GzCommon h i s :=
    { record := hrec
      mode := hm
      fresh := hfresh
      uniq := huniq
      globals := hglob
      fit := fit
      path := hpathx
      msg := hmsgx
      memerr := hmemerr
      want := ⟨hw8, hw31⟩
      size := Or.inl hsize
      distinct := by
        rw [hown]
        refine ⟨?_, ?_⟩
        · rw [show List.filterMap blkOf [Ptr.ref (BRef.blk pb) 0, (Ptr.null : BPtr)] = [pb] from rfl]
          simp
        intro p hp b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with hp | hp
        · subst hp
          simp only [blkOf, Option.some.injEq] at hb
          subst hb
          exact ⟨hpb, nso pb⟩
        · subst hp
          simp [blkOf] at hb
      live := by
        intro b hb
        rcases hb with hb | hb | hb | ⟨hs, -⟩
        · subst hb
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [hrec]))))))
        · obtain ⟨p, -, b', a, hp', ha, -, -⟩ := hpathx
          rw [hb] at hp'
          simp only [Ptr.ref.injEq, BRef.blk.injEq, and_true] at hp'
          subst hp'
          exact Or.inl (by simp [ha])
        · rw [hmsg] at hb
          cases hb
        · exact absurd hsize hs
      pos := by simp [hskip, hpos, hhave]
      next := fun hh => absurd hhave hh
      nullHave := fun _ => hhave
      recordFree := nso i }
  refine ⟨common, fun hr => ?_, fun hw => ?_⟩
  · have hmr : mode = .read := by
      by_cases hne : mode = .read
      · exact hne
      exfalso
      rw [if_neg hne] at hmode
      rw [hmode] at hr
      exact absurd hr (by decide)
    obtain ⟨heof, hhow, hjunk⟩ := hread hmr
    exact
      { how := Or.inl hhow
        copyDirect := fun hc => absurd (hhow.symm.trans hc) (by decide)
        gzipDirect := fun hc => absurd (hhow.symm.trans hc) (by decide)
        direct := hdir
        junk := Or.inl hjunk
        flags := ⟨Or.inl heof, Or.inl hpast, Or.inl hagain⟩
        unalloc := fun _ => ⟨hhave, havail, hhow, hstate⟩
        bufs := fun hs => absurd hsize hs
        input := Or.inl havail
        output := fun hh => absurd hhave hh
        codec := fun hs => absurd hsize hs
        posHave := by simp [hpos, hhave]
        againSize := fun _ => hagain
        haveSkip := fun _ => hskip
        againEof := fun ha => absurd hagain ha
        errEnd := by rw [herrO]; decide
        copyIn := fun hc => absurd (hhow.symm.trans hc) (by decide)
        msgLit := fun hs => absurd hsize hs }
  · exact
      { have0 := hhave
        direct := hwdir hw
        reset := Or.inl (hreset hw)
        unalloc := fun _ => hstate
        bufs := fun hs => absurd hsize hs
        input := Or.inl ⟨hnext, havail⟩
        output := fun _ hs => absurd hsize hs
        codec := fun _ hs => absurd hsize hs
        transparent := fun _ => hstate }

end ZlibF.Spec.Public.GzOpenInv

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
set_option autoImplicit false

/-- `gzdopen` (`GzDopenSafe`): the cases of `gzdopen_complete`, with the world, the record and the heap of the run
exposed (`gz_open_supplied_shape`) to establish `GzInv`, the platform bound and the descriptor facts. -/
theorem gzdopen_safe_proof : ZlibF.Spec.Public.GzDopenSafe := by
  intro h fs fd mode flags hf hu hg hfit hfs hm
  by_cases hneg : fd.toInt < 0
  · obtain ⟨hfr, hlc⟩ := descriptorFrame_refl h
    exact ⟨none, fs, h, gzdopen_negative h fs fd mode (Int32.lt_iff_toInt_lt.mpr (by simpa using hneg)),
      hfr, hfs, fun _ => Iff.rfl, hlc⟩
  have hn : 0 ≤ fd.toInt := by omega
  by_cases hnull : mode = .null
  · subst mode
    obtain ⟨after, hrun, hframe, hledger⟩ := gzdopen_null_mode h fs fd hf hu hn
    exact ⟨none, fs, after, hrun, hframe, hfs, fun _ => Iff.rfl, hledger⟩
  have hfd : fd ≠ -1 := by
    intro he
    rw [he] at hn
    contradiction
  have hc := hm hnull
  by_cases ha : h.allocOk h.nalloc = true
  · obtain ⟨hfe, hue⟩ := descriptorEntry_invariants h fd hf hu
    have hmode := descriptorEntry_cstring h fd mode flags hf hc
    have hpath := descriptorEntry_path h fd hn
    have hlen : (descriptorPath fd).length ≤ 2147483647 := by
      have hl := descriptorPath_length fd hn
      omega
    obtain ⟨file, fs', inner, hrun, hframe, hpost⟩ :=
      gz_open_supplied_short (descriptorEntryHeap h fd) fs (.ref (.blk h.nextBlk) 0) mode fd
        flags (descriptorPath fd) hfe hue (descriptorEntry_globals h fd hg) hpath hmode hlen hfd
    have hshape := gz_open_supplied_shape (descriptorEntryHeap h fd) fs (.ref (.blk h.nextBlk) 0) mode fd
      flags (descriptorPath fd) hfe hue hpath hmode hlen hfd file fs' inner hrun
    have houter : gzdopen fd mode fs h =
        .ok ((file, fs'), descriptorReleased inner h.nextBlk) := by
      rw [gzdopen_entry h fs fd mode hf hn ha]
      unfold descriptorOpenTail
      offsetsimp [hrun, descriptor_free_frame h fd inner hframe]
    have hcf := descriptorCaller_frame h fd inner hf hframe
    refine ⟨file, fs', descriptorReleased inner h.nextBlk, houter, hcf, ?_⟩
    cases file with
    | none =>
      obtain ⟨-, hledger, -⟩ := hpost
      have hfs' : fs' = fs := hshape.1 rfl
      subst hfs'
      exact ⟨hfs, fun _ => Iff.rfl,
        descriptorCaller_ledger h fd inner (fun _ => False) hf hue hframe hledger (by simp)⟩
    | some file =>
      cases file with
      | in_gzstate_x i =>
        obtain ⟨s, parsed, level, strategy, direct, hp, ho, -, hledger⟩ := hpost
        obtain ⟨mode', level', strategy', direct', hp', -, hfs', hinner⟩ := hshape.2 i rfl
        rw [hp] at hp'
        simp only [Option.some.injEq, Prod.mk.injEq] at hp'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hp'
        have hstate := ho.1.1
        obtain ⟨hi, hprivate, hsize, hmsg⟩ := gz_open_supplied_success_layout (descriptorEntryHeap h fd)
          fs (.ref (.blk h.nextBlk) 0) mode fd flags (descriptorPath fd) hfe hue hpath hmode hlen hfd
          i fs' inner s hrun hstate
        have hcount := (descriptorEntry_counts h fd).1
        have hrecord : s = parsedOpenRecord (descriptorEntryHeap h fd) flags parsed fd fs := by
          have hs' : (parsedOpenHeap (descriptorEntryHeap h fd) flags parsed (descriptorPath fd) fd fs).gzstates
              (descriptorEntryHeap h fd).nextBlk =
              some (parsedOpenRecord (descriptorEntryHeap h fd) flags parsed fd fs) := by
            simp [parsedOpenHeap, modeSuppliedHeap, setS, parsedOpenRecord]
          rw [hinner, hi, hs'] at hstate
          exact (Option.some.inj hstate).symm
        have hsep : s.path ≠ .ref (.blk h.nextBlk) 0 := by
          rw [hprivate, hcount]
          intro he
          simp only [Ptr.ref.injEq, BRef.blk.injEq, and_true] at he
          omega
        have hnot : ¬ ZlibF.Spec.Public.GzOwned inner i s h.nextBlk := by
          simp only [ZlibF.Spec.Public.GzOwned, hi, hprivate, hsize, hmsg]
          rw [hcount]
          simp
          omega
        have hfinal := descriptorCaller_ledger h fd inner (ZlibF.Spec.Public.GzOwned inner i s)
          hf hue hframe hledger hnot
        have hoa : ZlibF.Spec.Public.OpenState (descriptorReleased inner h.nextBlk) i s parsed level strategy
            direct fd (descriptorPath fd) :=
          descriptorReleased_OpenState inner i h.nextBlk s parsed level strategy direct fd
            (descriptorPath fd) _ ho (descriptor_temp_frame h fd inner hframe) hsep
        have hlc : ZlibF.Spec.Public.LiveChange h (descriptorReleased inner h.nextBlk)
            (ZlibF.Spec.Public.GzOwned (descriptorReleased inner h.nextBlk) i s) (fun _ => False) := by
          intro b
          change (descriptorReleased inner h.nextBlk).live b ↔
            ((h.live b ∧ ¬ False) ∨ ZlibF.Spec.Public.GzOwned (descriptorReleased inner h.nextBlk) i s b)
          rw [← descriptorOwned_zero_heap inner (descriptorReleased inner h.nextBlk) i s hsize b]
          exact hfinal b
        have hU : Uniq (descriptorReleased inner h.nextBlk) := hoa.1.2.2.2.1
        have hrecA : (descriptorReleased inner h.nextBlk).gzstates i = some s := hoa.1.1
        have hbytes : (descriptorReleased inner h.nextBlk).bytes ((descriptorEntryHeap h fd).nextBlk + 1) =
            some ((descriptorPath fd).toArray.push 0) := by
          show (upd inner.bytes h.nextBlk none) ((descriptorEntryHeap h fd).nextBlk + 1) = _
          rw [upd_ne _ _ _ _ (by rw [hcount]; omega), hinner]
          exact parsedOpenHeap_path_bytes _ _ _ _ _ _
        have howned : ∀ b, ¬ h.live b → (descriptorReleased inner h.nextBlk).live b →
            b = i ∨ b = (descriptorEntryHeap h fd).nextBlk + 1 := by
          intro b hl hlive
          rcases (hlc b).1 hlive with ⟨hl', -⟩ | hown
          · exact absurd hl' hl
          · rcases hown with hb | hb | hb | ⟨hs0, -⟩
            · exact Or.inl hb
            · rw [hprivate] at hb
              simp only [Ptr.ref.injEq, BRef.blk.injEq, and_true] at hb
              exact Or.inr hb.symm
            · rw [hmsg] at hb
              cases hb
            · exact absurd hsize hs0
        have hfitA : ZlibF.PlatformMemory.ByteObjectsFit (descriptorReleased inner h.nextBlk) := by
          apply fit_of_frame_new hfit hcf
          · intro b a hl hb
            rcases howned b hl (Or.inl (by simp [hb])) with e | e
            · subst e
              exact (uniq_gz_bytes hU hrecA hb).elim
            · subst e
              rw [hbytes] at hb
              cases hb
              have hl15 := descriptorPath_length fd hn
              simp only [Array.size_push, List.size_toArray]
              unfold ZlibF.PlatformMemory.byteObjectLimit
              omega
          · intro b d hl hd
            rcases howned b hl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [hd])))))) with e | e
            · subst e
              exact uniq_gz_dstates hU hrecA hd
            · subst e
              exact uniq_bytes_dstates hU hbytes hd
        obtain ⟨hst, hnext, hreset, hdir, hwdir⟩ :=
          parsedOpenRecord_inv_facts (descriptorEntryHeap h fd) flags parsed level strategy direct fd fs hp
            s hrecord
        have hinv : ZlibF.Spec.Public.GzInv (descriptorReleased inner h.nextBlk) i s :=
          ZlibF.Spec.Public.GzOpenInv.open_inv hoa hfitA hprivate (by rw [hi]; omega) hst hnext hreset hdir
            hwdir
        subst hfs'
        obtain ⟨hfs2, hkept⟩ := suppliedWorld_fs hfs parsed fd
        exact ⟨hfs2, hkept, s, hinv, hoa.2.2.1, hlc⟩
  · have he : h.allocOk h.nalloc = false := by simpa using ha
    have hneg' : ¬ fd < 0 := fun he => by
      have he' := Int32.lt_iff_toInt_lt.mp he
      simp at he'
      omega
    obtain ⟨hframe, hledger, -⟩ := writerFirstFailure_checks h he
    exact ⟨none, fs, _, gzdopen_alloc_failure h fs fd mode hneg' he, hframe, hfs, fun _ => Iff.rfl, hledger⟩

#print axioms gz_open_supplied_shape
#print axioms parsedOpenRecord_inv_facts
#print axioms fit_of_frame_new
#print axioms gzdopen_safe_proof

end Zlib.Gzlib.Proofs

namespace ZlibF.Spec.Public.GzSkeleton
open ZlibF.Spec.Public
set_option autoImplicit false

/-- `gzdopen`: restate `gzdopen_complete` to `GzInv` (relies on the local patch for R-3 through `gz_reset`). -/
theorem gzdopen_safe : GzDopenSafe := Zlib.Gzlib.Proofs.gzdopen_safe_proof

#print axioms gzdopen_safe

end ZlibF.Spec.Public.GzSkeleton
