import ZlibF.Proof.«public-uncompress-loop»
import ZlibF.Proof.«public-inflate-init»

/-!
# uncompr.c: preparation and initialization of the automatic stream

After the argument checks `uncompress2_z` reads both lengths, clears the input
and the allocator fields of its automatic stream and calls `inflateInit`. On success
it binds the output and enters the loop in a loop state; on an allocation failure
it frees its automatic objects and returns `Z_MEM_ERROR`.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
open Zlib.Inflate (inflateInit_ inflateInit2_ inflate inflateEnd)
set_option autoImplicit false

/-- The automatic stream after `next_in`, `avail_in` and the allocator fields are set. -/
def preStream (h : Heap) (source : BPtr) : ZStream :=
  { ZStream.garbage (h.garbage h.nalloc) with next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null }

/-- The heap before `inflateInit`. -/
def preHeap (h : Heap) (source : BPtr) : Heap :=
  { localHeap h with streams := upd (localHeap h).streams h.nextBlk (some (preStream h source)) }

theorem localHeap_stream_get (h : Heap) :
    (localHeap h).streams h.nextBlk = some (ZStream.garbage (h.garbage h.nalloc)) := by
  simp [localHeap, streamHeap]

theorem prepare_run (h : Heap) (source : BPtr) :
    updZ (some (.tab h.nextBlk)) (fun z => { z with next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null })
      (localHeap h) = .ok ((), preHeap h source) := by
  simp [updZ, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo,
    localHeap_stream_get, preHeap, preStream]

theorem version_index : strIndex ZLIB_VERSION = some 57 := by decide +kernel

theorem version_run (H : Heap) : Zlib.GzFs.strLit ZLIB_VERSION H = .ok (.ref (.str 57) 0, H) := by
  simp [Zlib.GzFs.strLit, strLitRef, version_index]

set_option maxRecDepth 100000 in
theorem version_byte (H : Heap) : OkOn H (index8 (.ref (.str 57) 0) 0) 49 := by
  have hg : Space.get H (BRef.str 57) = some (strBytes ZLIB_VERSION) := by
    rw [BRef.get_str]
    rfl
  exact Ptr.index_ok (i := 0) hg (by decide)

set_option maxRecDepth 100000 in
theorem version_value (H : Heap) : VersionValue H (.ref (.str 57) 0) (some 49) := by
  have hg : Space.get H (BRef.str 57) = some (strBytes ZLIB_VERSION) := by
    rw [BRef.get_str]
    rfl
  refine Or.inr ⟨49, rfl, Or.inr ⟨.str 57, 0, strBytes ZLIB_VERSION, rfl, hg, by decide, by decide⟩⟩

theorem preHeap_live (h : Heap) (source : BPtr) (b : Nat) :
    (preHeap h source).live b ↔ h.live b ∨ b = h.nextBlk ∨ b = h.nextBlk + 1 := by
  simp only [preHeap, localHeap, streamHeap, Heap.live, upd_apply]
  by_cases e0 : b = h.nextBlk
  · subst e0; simp
  by_cases e1 : b = h.nextBlk + 1
  · subst e1; simp
  simp [e0, e1]

theorem preHeap_fresh {h : Heap} (fresh : Fresh h) (source : BPtr) : Fresh (preHeap h source) := by
  intro b hb live
  rw [preHeap_live] at live
  simp only [preHeap, localHeap] at hb
  rcases live with l | l | l
  · exact fresh b (by omega) l
  · omega
  · omega

theorem preHeap_uniq {h : Heap} (fresh : Fresh h) (u : Uniq h) (source : BPtr) : Uniq (preHeap h source) := by
  intro b
  have ub := u b
  have n0 := fresh h.nextBlk (Nat.le_refl _)
  have n1 := fresh (h.nextBlk + 1) (by omega)
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at n0 n1
  simp only [preHeap, localHeap, streamHeap, upd_apply]
  by_cases e0 : b = h.nextBlk
  · subst e0; simp [n0.1, n0.2.1, n0.2.2.1, n0.2.2.2.1, n0.2.2.2.2.1, n0.2.2.2.2.2.1, n0.2.2.2.2.2.2]
  by_cases e1 : b = h.nextBlk + 1
  · subst e1; simp [n1.1, n1.2.1, n1.2.2.1, n1.2.2.2.1, n1.2.2.2.2.1, n1.2.2.2.2.2.1, n1.2.2.2.2.2.2]
  simpa [e0, e1] using ub

theorem preHeap_get {h : Heap} (fresh : Fresh h) (source : BPtr) (rr : BRef) :
    Space.get (preHeap h source) rr = Space.get h rr ∨
      (rr = .blk (h.nextBlk + 1) ∧ Space.get (preHeap h source) rr = some (reservedBytes h)) := by
  cases rr with
  | blk c =>
    by_cases e : c = h.nextBlk + 1
    · subst e; right; simp [Space.get, preHeap, localHeap]
    · left; simp [Space.get, preHeap, localHeap, streamHeap, upd_ne _ _ _ _ e]
  | _ => left; simp [Space.get, preHeap, localHeap, streamHeap, staticStringBytes]

theorem preHeap_fit {h : Heap} (fresh : Fresh h) (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (source : BPtr) :
    ZlibF.PlatformMemory.ByteObjectsFit (preHeap h source) := by
  intro rr a g
  rcases preHeap_get fresh source rr with e | ⟨-, e⟩
  · rw [e] at g; exact fit rr a g
  · rw [e] at g; cases g
    simp [reservedBytes, ZlibF.PlatformMemory.byteObjectLimit]

theorem preHeap_stream (h : Heap) (source : BPtr) :
    (ZStreamRef.tab h.nextBlk).get (preHeap h source) = some (preStream h source) := by
  simp [ZStreamRef.get, preHeap]

/-- The heap after a successful `inflateInit`. -/
def initHeap (h : Heap) (source : BPtr) : Heap :=
  initOkHeap (preHeap h source) (.tab h.nextBlk) (preStream h source) 5 15

/-- The stream record after a successful `inflateInit`. -/
def initStreamRec (h : Heap) (source : BPtr) : ZStream :=
  resetKeepStream (initStream2 (preStream h source) (h.nextBlk + 2))
    (resetPre (reset2Pre 5 15 (initState (.tab h.nextBlk))))

theorem preStream_alloc (h : Heap) (source : BPtr) :
    (preStream h source).zalloc = .null ∧ (preStream h source).zfree = .null := ⟨rfl, rfl⟩

theorem init_ok_run {h : Heap} (fresh : Fresh h) (source : BPtr) (ok : h.allocOk h.nalloc = true) :
    inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112 (preHeap h source) =
      .ok (Z_OK, initHeap h source) := by
  rw [inflateInit__eq]
  exact inflateInit2_success (preHeap_stream h source) (preHeap_fresh fresh source) ok (Or.inl rfl) (Or.inl rfl)
    (by simp) (version_byte _) params15

set_option maxRecDepth 100000 in
theorem init2_ok_run {h : Heap} (fresh : Fresh h) (source : BPtr) (ok : h.allocOk h.nalloc = true) :
    C.run (inflateInit2_ (some (.tab h.nextBlk)) 15 (.ref (.str 57) 0) 112) (preHeap h source) =
      .ok (Z_OK, initHeap h source) := by
  show inflateInit2_ _ _ _ _ _ = _
  unfold initHeap
  exact inflateInit2_success (preHeap_stream h source) (preHeap_fresh fresh source) ok (Or.inl rfl) (Or.inl rfl)
    (by simp) (version_byte _) params15

theorem init_fail_run {h : Heap} (fresh : Fresh h) (source : BPtr) (bad : ¬ h.allocOk h.nalloc = true) :
    inflateInit_ (some (.tab h.nextBlk)) (.ref (.str 57) 0) 112 (preHeap h source) =
      .ok (Z_MEM_ERROR, initMemHeap (preHeap h source) (.tab h.nextBlk) (preStream h source)) := by
  rw [inflateInit__eq]
  exact inflateInit2_memfail (preHeap_stream h source) (preHeap_fresh fresh source) bad (Or.inl rfl) (Or.inl rfl)
    (by simp) (version_byte _)

theorem initHeap_stream (h : Heap) (source : BPtr) :
    (ZStreamRef.tab h.nextBlk).get (initHeap h source) = some (initStreamRec h source) := by
  simp [initHeap, initOkHeap, initStreamRec, setI, reset2Heap, reset2Pre, initState, freeWin, allocIstHeap,
    ZStreamRef.get, ZStreamRef.put, preHeap, localHeap, streamHeap]

theorem initStreamRec_fields (h : Heap) (source : BPtr) :
    (initStreamRec h source).next_in = source ∧ (initStreamRec h source).avail_in = 0 := by
  simp [initStreamRec, resetKeepStream, initStream2, initStream, preStream]

theorem initHeap_get (h : Heap) (source : BPtr) (rr : BRef) :
    Space.get (initHeap h source) rr = Space.get (preHeap h source) rr ∧
      Space.ro (initHeap h source) rr = Space.ro (preHeap h source) rr ∧
      (initHeap h source).libcErrorBorrow = (preHeap h source).libcErrorBorrow := by
  cases rr <;> simp [initHeap, initOkHeap, setI, reset2Heap, reset2Pre, initState, freeWin, allocIstHeap,
    Space.get, Space.ro, ZStreamRef.put, preHeap, localHeap, streamHeap, staticStringBytes]

/-- The stream after the output is bound. -/
def boundStream (h : Heap) (source out0 : BPtr) : ZStream :=
  { initStreamRec h source with next_out := out0, avail_out := 0 }

/-- The heap when the loop starts. -/
def startHeap (h : Heap) (source out0 : BPtr) : Heap :=
  (ZStreamRef.tab h.nextBlk).put (initHeap h source) (boundStream h source out0)

theorem bind_run (h : Heap) (source out0 : BPtr) :
    updZ (some (.tab h.nextBlk)) (fun z => { z with next_out := out0, avail_out := 0 }) (initHeap h source) =
      .ok ((), startHeap h source out0) := by
  simp [updZ, ldZStream, stZStream, initHeap_stream, ZStreamRef.isRo, startHeap, boundStream]

set_option maxRecDepth 100000 in
/-- The loop starts in a loop state. -/
theorem start_state {e : Env} (ok : EnvOK e) (uniq : Uniq e.h₀)
    (globals : LibraryGlobals e.h₀) (fit : ZlibF.PlatformMemory.ByteObjectsFit e.h₀)
    (alloc : e.h₀.allocOk e.h₀.nalloc = true) (len left : UInt64)
    (hlen : len.toNat = e.n) (hleft : left.toNat = e.cap) :
    ∃ s, State e { err := Z_OK, len := len, left := left } (startHeap e.h₀ e.source e.out0) {}
      (e.h₀.nextBlk + 2) (boundStream e.h₀ e.source e.out0) s := by
  have fresh := ok.fresh
  have k0 : ¬ e.h₀.live e.h₀.nextBlk := fresh e.h₀.nextBlk (Nat.le_refl _)
  have kr : e.r = .tab e.h₀.nextBlk := rfl
  have kk : e.k = e.h₀.nextBlk := rfl
  have globalsP : LibraryGlobals (preHeap e.h₀ e.source) := by
    simpa [LibraryGlobals, preHeap, localHeap, streamHeap] using globals
  have domain : InitDomain (preHeap e.h₀ e.source) (.tab e.h₀.nextBlk) (.ref (.str 57) 0) :=
    ⟨preHeap_fresh fresh _, preHeap_uniq fresh uniq _, globalsP, version_value _, preStream e.h₀ e.source,
      preHeap_stream e.h₀ e.source, ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  have run : C.run (inflateInit2_ (some (.tab e.h₀.nextBlk)) 15 (.ref (.str 57) 0) 112) (preHeap e.h₀ e.source) =
      .ok (Z_OK, initHeap e.h₀ e.source) := by
    exact init2_ok_run fresh e.source alloc
  have initial := ZlibF.Spec.Public.Proofs.InflateInit.init15_initial (preHeap_fresh fresh e.source) (preHeap_uniq fresh uniq e.source)
    (preHeap_stream e.h₀ e.source) alloc (Or.inl rfl) (Or.inl rfl) (by simp) (version_byte _)
  obtain ⟨zI, sI, goodI, zallocI, zfreeI, modeI, winI, -, -, -, -, -, -, -, -, -, -, headI, -, -, -,
    frameI, liveI⟩ := initial
  have toInit : initOkHeap (preHeap e.h₀ e.source) (.tab e.h₀.nextBlk) (preStream e.h₀ e.source) 5 15 =
      initHeap e.h₀ e.source := rfl
  rw [toInit] at goodI frameI liveI
  have zIeq : zI = initStreamRec e.h₀ e.source :=
    Option.some.inj (goodI.live.hz.symm.trans (initHeap_stream e.h₀ e.source))
  subst zIeq
  have nb : (preHeap e.h₀ e.source).nextBlk = e.h₀.nextBlk + 2 := rfl
  rw [nb] at goodI liveI
  have traceI : InflateProtocolTrace 15 e.r (initHeap e.h₀ e.source) {} false := .init domain run
  have reachI : StreamReachable .inflate (initHeap e.h₀ e.source) e.r :=
    .inflateInit (preHeap_fresh fresh _) (preHeap_uniq fresh uniq _) globalsP (preHeap_stream e.h₀ e.source)
      ⟨Or.inl rfl, Or.inl rfl⟩ (version_value _) run
  have globalsI : LibraryGlobals (initHeap e.h₀ e.source) := by
    have := frameI.1
    simp only [LibraryGlobals] at globalsP ⊢
    rw [← this]; exact globalsP
  have ownI : ∀ b, InflateOwned (e.h₀.nextBlk + 2) sI b ↔ b = e.h₀.nextBlk + 2 := by
    intro b
    simp only [InflateOwned, winI]
    constructor
    · rintro (x | x)
      · exact x
      · cases x
    · exact Or.inl
  have rebuf := rebuffer_put (e := e) goodI globalsI (by rw [ownI, kk]; omega)
    (z₁ := boundStream e.h₀ e.source e.out0) (by simp [boundStream])
  have hzI : (initHeap e.h₀ e.source).streams e.h₀.nextBlk = some (initStreamRec e.h₀ e.source) :=
    initHeap_stream e.h₀ e.source
  have Seq : startHeap e.h₀ e.source e.out0 =
      { initHeap e.h₀ e.source with streams := upd (initHeap e.h₀ e.source).streams e.h₀.nextBlk (some (boundStream e.h₀ e.source e.out0)) } :=
    put_tab_eq hzI
  have getS : ∀ rr : BRef, Space.get (startHeap e.h₀ e.source e.out0) rr = Space.get (preHeap e.h₀ e.source) rr ∧
      Space.ro (startHeap e.h₀ e.source e.out0) rr = Space.ro (preHeap e.h₀ e.source) rr := by
    intro rr
    rw [Seq, (put_tab_get (H := initHeap e.h₀ e.source) (k := e.h₀.nextBlk) (boundStream e.h₀ e.source e.out0) rr).1,
      (put_tab_get (H := initHeap e.h₀ e.source) (k := e.h₀.nextBlk) (boundStream e.h₀ e.source e.out0) rr).2]
    exact ⟨(initHeap_get e.h₀ e.source rr).1, (initHeap_get e.h₀ e.source rr).2.1⟩
  have fitS : ZlibF.PlatformMemory.ByteObjectsFit (startHeap e.h₀ e.source e.out0) := by
    intro rr a g
    rw [(getS rr).1] at g
    exact preHeap_fit fresh fit e.source rr a g
  have reachS : StreamReachable .inflate (startHeap e.h₀ e.source e.out0) e.r :=
    .rebuffer reachI rebuf (fun _ => fitS)
  obtain ⟨i', z', s', g', d'⟩ := reach_invariant reachS
  have hzS : e.r.get (startHeap e.h₀ e.source e.out0) = some (boundStream e.h₀ e.source e.out0) := by
    rw [Seq]; simp [ZStreamRef.get, Env.r]
  have ez : z' = boundStream e.h₀ e.source e.out0 := Option.some.inj (g'.live.hz.symm.trans hzS)
  subst ez
  have ei : i' = e.h₀.nextBlk + 2 := by
    have := g'.live.zst
    simp only [boundStream] at this
    rw [goodI.live.zst] at this
    cases this; rfl
  subst ei
  have es : s' = sI := by
    have h1 := g'.live.hs
    rw [Seq] at h1
    dsimp only at h1
    have h2 := goodI.live.hs
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  subst es
  -- caller blocks are below the automatic objects
  have below : ∀ b, e.h₀.live b → b < e.h₀.nextBlk := by
    intro b live
    by_cases lt : b < e.h₀.nextBlk
    · exact lt
    · exact absurd live (fresh b (by omega))
  have sameS : ∀ b, b ≠ e.h₀.nextBlk → (preHeap e.h₀ e.source).live b → b ≠ e.h₀.nextBlk + 2 →
      SameAt (preHeap e.h₀ e.source) (startHeap e.h₀ e.source e.out0) b := by
    intro b ne live _
    have notRoot : ¬ StreamRoot (ZStreamRef.tab e.h₀.nextBlk) b := ne
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := frameI.2.2.2.2.2 b live notRoot
    rw [Seq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · exact x1
    · exact x2
    · rw [upd_ne _ _ _ _ ne]; exact x3
    · exact x4
    · exact x5
    · exact x6
    · exact x7
    · exact x8
  have preSame : ∀ b, b < e.h₀.nextBlk → SameAt e.h₀ (preHeap e.h₀ e.source) b := by
    intro b lt
    have n0 : b ≠ e.h₀.nextBlk := by omega
    have n1 : b ≠ e.h₀.nextBlk + 1 := by omega
    exact ⟨by simp [preHeap, localHeap, streamHeap, upd_ne _ _ _ _ n1], rfl,
      by simp [preHeap, localHeap, streamHeap, upd_ne _ _ _ _ n0], rfl, rfl, rfl, rfl,
      by simp [preHeap, localHeap, streamHeap, upd_ne _ _ _ _ n1]⟩
  have liveS : ∀ b, (startHeap e.h₀ e.source e.out0).live b ↔
      (e.h₀.live b ∨ b = e.h₀.nextBlk ∨ b = e.h₀.nextBlk + 1) ∨ b = e.h₀.nextBlk + 2 := by
    intro b
    rw [Seq, put_tab_live hzI, liveI b, preHeap_live]
    simp
  refine ⟨s', ?_⟩
  exact
    { trace := InflateProtocolTrace.caller traceI rebuf fitS
      single := rfl
      dict := rfl
      reach := reachS
      fit := fitS
      good := g'
      alloc := ⟨by simpa [boundStream] using zallocI, by simpa [boundStream] using zfreeI⟩
      noSync := by rw [modeI]; decide
      noMem := by rw [modeI]; decide
      head := headI
      globals := by
        rw [Seq]
        unfold LibraryGlobals at globalsI ⊢
        dsimp only
        rw [globalsI]
      inTake := rfl
      inCount := by
        simp only [List.length_nil, boundStream, (initStreamRec_fields e.h₀ e.source).2]
        simp; omega
      nextIn := by simp [boundStream, (initStreamRec_fields e.h₀ e.source).1, advance_zero]
      outCount := by simp [boundStream]; omega
      nextOut := by simp [boundStream, advance_zero]
      agree := by
        rw [writeOut_nil]
        refine ⟨fun b live => ?_, ?_, ?_, ?_, ?_⟩
        · have lt := below b live
          have n0 : b ≠ e.h₀.nextBlk := by omega
          have n2 : b ≠ e.h₀.nextBlk + 2 := by omega
          exact (preSame b lt).trans (sameS b n0 ((preHeap_live _ _ b).2 (Or.inl live)) n2)
        · rw [Seq]; dsimp only; rw [← frameI.1]; rfl
        · rw [Seq]; dsimp only; rw [← frameI.2.1]; rfl
        · rw [Seq]; dsimp only; rw [← frameI.2.2.1]; rfl
        · rw [Seq]; dsimp only; rw [(initHeap_get e.h₀ e.source (.blk 0)).2.2]; rfl
      notOwned := by
        intro b hb own
        rw [ownI] at own
        subst own
        rcases hb with x | x | x
        · have := below _ x; omega
        · simp [Env.k] at x
        · simp [Env.k] at x
      liveOnly := by
        intro b lb
        rcases (liveS b).1 lb with (x | x | x) | x
        · exact Or.inl x
        · exact Or.inr (Or.inl x)
        · exact Or.inr (Or.inr (Or.inl x))
        · exact Or.inr (Or.inr (Or.inr ((ownI b).2 x)))
      reservedBytes := by
        have sm := sameS (e.h₀.nextBlk + 1) (by omega) ((preHeap_live _ _ _).2 (Or.inr (Or.inr rfl))) (by omega)
        rw [kk, sm.1]
        simp [preHeap, localHeap]
      reservedRo := by
        have sm := sameS (e.h₀.nextBlk + 1) (by omega) ((preHeap_live _ _ _).2 (Or.inr (Or.inr rfl))) (by omega)
        rw [kk, sm.2.2.2.2.2.2.2]
        simp [preHeap, localHeap]
      noOver := by
        intro m o _ d
        refine ⟨List.nil_prefix, fun eq => ?_⟩
        have := zlib_decodes_long d
        rw [← eq] at this
        simp at this
      nalloc := by
        rw [Seq]
        dsimp only
        have := frameI.2.2.2.2.1
        have e0 : (preHeap e.h₀ e.source).nalloc = e.h₀.nalloc := rfl
        rw [e0] at this
        exact this }

end ZlibF.Spec.Public.Proofs.Uncompress
