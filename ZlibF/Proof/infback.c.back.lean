import ZlibF.Proof.«infback.c.callbacks»

/-!
# infback.c: `inflateBack`, the entry checks and the end-of-input exit

Proved here: the `Z_STREAM_ERROR` exits of the entry, and the exit when `in` has no input at the first `PULL`
(`Z_BUF_ERROR`, `next_in` is `NULL`, `avail_in` is 0, `out` is not called). The loop over the blocks is open (see
`docs/proof/callbacks.md`).
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The heap after the first two writes of `inflateBack`: `strm->msg = NULL`, and the state set to the start
(`mode = TYPE`, `last = 0`, `whave = 0`). -/
def backEntryHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (zs : Nat) (st : InflateState) : Heap :=
  setI (r.put h { z with msg := .null }) zs { st with mode := TYPE, last := 0, whave := 0 }

/-- The callback `in` never has input: whenever it is called under `R`, it returns the count 0. -/
def InEof (inCb : InCb) (inDesc : BPtr) (R : Heap → Prop) : Prop :=
  ∀ h nx, R h → ∃ nx' h', inCb inDesc nx h = .ok ((0, nx'), h')

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

theorem fuel_succ : ∃ n, fuel = n + 1 + 1 := ⟨fuel - 2, by unfold fuel; omega⟩

/-- A loop whose condition holds and whose body leaves (`goto inf_leave`) at the first trip leaves. -/
theorem xwhile_leave {cond : X Bool} {body : X Unit} {l l' : IL} {h h' : Heap}
    (hc : StateT.run (ExceptT.run cond) l h = .ok ((Except.ok true, l), h))
    (hb : StateT.run (ExceptT.run body) l h = .ok ((Except.error Ex.leave, l'), h')) :
    StateT.run (ExceptT.run (xwhile cond body)) l h = .ok ((Except.error Ex.leave, l'), h') := by
  unfold xwhile xwhileBrk cwhile
  obtain ⟨n, hn⟩ := fuel_succ
  rw [hn]
  simp [cwhile.go, ExceptT.run, ExceptT.mk, StateT.run, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, pure,
    ExceptT.pure, StateT.pure] at *
  erw [hc]
  simp only [↓reduceIte]
  erw [hb]
  simp [StateT.pure, cwhile.go]

/-! ### Running the monad `X` -/

theorem xrun_bind {α β : Type} (m : X α) (f : α → X β) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (m >>= f)) l h =
      match StateT.run (ExceptT.run m) l h with
      | .ok ((.ok a, l'), h') => StateT.run (ExceptT.run (f a)) l' h'
      | .ok ((.error e, l'), h') => .ok ((.error e, l'), h')
      | .error e => .error e := by
  cases hm : StateT.run (ExceptT.run m) l h with
  | error e => simp [bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, ExceptT.run, ExceptT.mk, StateT.run] at hm ⊢; simp [hm]
  | ok p =>
    obtain ⟨⟨r, l'⟩, h'⟩ := p
    cases r <;> simp [bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, ExceptT.run, ExceptT.mk, StateT.run, StateT.pure,
      pure, ExceptT.pure] at hm ⊢ <;> simp [hm, StateT.pure]

theorem xrun_get (l : IL) (h : Heap) : StateT.run (ExceptT.run (get : X IL)) l h = .ok ((.ok l, l), h) := rfl
theorem xrun_set (l l0 : IL) (h : Heap) : StateT.run (ExceptT.run (set l0 : X PUnit)) l h = .ok ((.ok ⟨⟩, l0), h) := rfl
theorem xrun_modify (f : IL → IL) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (modify f : X PUnit)) l h = .ok ((.ok ⟨⟩, f l), h) := rfl
theorem xrun_throw {α : Type} (e : Ex) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (throw e : X α)) l h = .ok ((.error e, l), h) := rfl
theorem xrun_pure {α : Type} (a : α) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (pure a : X α)) l h = .ok ((.ok a, l), h) := rfl
theorem xrun_lift {α : Type} (m : M α) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (liftM m : X α)) l h =
      match m h with | .ok (a, h') => .ok ((.ok a, l), h') | .error e => .error e := by
  cases hm : m h <;> simp [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, StateT.lift, ExceptT.run, ExceptT.mk,
    StateT.run, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure, StateT.pure, Functor.map, StateT.map, hm]

theorem PULL_eof {c : BCtx} {l : IL} {h h3 : Heap} {nx : BPtr} (h0 : l.have_ = 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h3)) :
    StateT.run (ExceptT.run (PULL c)) l h =
      .ok ((Except.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h3) := by
  simp [PULL, xrun_bind, xrun_get, xrun_set, xrun_throw, xrun_pure, xrun_lift, hin, h0]

theorem PULLBYTE_eof {c : BCtx} {l : IL} {h h3 : Heap} {nx : BPtr} (h0 : l.have_ = 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h3)) :
    StateT.run (ExceptT.run (PULLBYTE c)) l h =
      .ok ((Except.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h3) := by
  simp [PULLBYTE, xrun_bind, PULL_eof h0 hin]

theorem NEEDBITS_eof {c : BCtx} {l : IL} {h h3 : Heap} {nx : BPtr} {n : UInt32} (h0 : l.have_ = 0) (hb : l.bits < n)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h3)) :
    StateT.run (ExceptT.run (NEEDBITS c n)) l h =
      .ok ((Except.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h3) := by
  unfold NEEDBITS
  apply xwhile_leave
  · simp [xrun_bind, xrun_get, xrun_pure, hb]
  · exact PULLBYTE_eof h0 hin

theorem back_TYPE_eof {c : BCtx} {zs : Nat} {s : InflateState} {l : IL} {h h3 : Heap} {nx : BPtr}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hl : s.last = 0) (h0 : l.have_ = 0) (hb : l.bits < 3)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h3)) :
    StateT.run (ExceptT.run (back_TYPE c)) l h =
      .ok ((Except.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h3) := by
  have e : liftM (rdS c.st (·.last)) = (liftM (rdS c.st (·.last)) : X Int32) := rfl
  unfold back_TYPE
  simp [xrun_bind, xrun_lift, hc, rdI_eq, hs, hl, NEEDBITS_eof h0 hb hin]

theorem back_dispatch_eof {c : BCtx} {zs : Nat} {s : InflateState} {l : IL} {h h3 : Heap} {nx : BPtr}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hm : s.mode = TYPE) (hl : s.last = 0)
    (h0 : l.have_ = 0) (hb : l.bits < 3)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h3)) :
    StateT.run (ExceptT.run (back_dispatch c)) l h =
      .ok ((Except.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h3) := by
  unfold back_dispatch
  simp [xrun_bind, xrun_lift, hc, rdI_eq, hs, hm, back_TYPE_eof hc hs hl h0 hb hin]

/-- The registers of `inflateBack` right after its set-up. -/
def entryIL (next : BPtr) (have_ : UInt32) (window : BPtr) (wsize : UInt32) : IL :=
  { IL.init with next := next, have_ := have_, hold := 0, bits := 0, put := window, left := wsize }

/-- A null stream: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBack_nullstream (inCb : InCb) (inDesc : BPtr) (outCb : OutCb) (outDesc : BPtr) (h : Heap) :
    inflateBack none inCb inDesc outCb outDesc h = .ok (Z_STREAM_ERROR, h) := by
  simp [inflateBack]

/-- No state: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBack_nostate {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hno : z.state = none)
    (inCb : InCb) (inDesc : BPtr) (outCb : OutCb) (outDesc : BPtr) :
    inflateBack (some r) inCb inDesc outCb outDesc h = .ok (Z_STREAM_ERROR, h) := by
  isimp [inflateBack, hz, hno]

/-- **inflateBack, no input.** On a stream set up by `inflateBackInit_` with `next_in = NULL`, if `in` returns 0 when it
is first called (no input at all), the call returns `Z_BUF_ERROR`, calls `out` not at all, and leaves `next_in = NULL`,
`avail_in = 0` and `msg = NULL` (`zlib.h`: `Z_BUF_ERROR` if `in()` returned zero when input was needed). The call-backs
keep `CbContract`; `in` has no input (`InEof`). Everything else of the stream and of the heap is as `in` left it
(`CbFrame`). -/
theorem inflateBack_eof {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr} {win : Nat} {ownI ownO : Nat → Prop}
    {R : Heap → Prop}
    (hG : BackGood h r zs z st) (hni : z.next_in = .null)
    (hK : CbContract inCb inDesc outCb outDesc win ownI ownO R) (hEof : InEof inCb inDesc R) (hR : R h) :
    ∃ h3, C.run (inflateBack (some r) inCb inDesc outCb outDesc) h =
        .ok (Z_BUF_ERROR, r.put h3 { z with msg := .null, next_in := .null, avail_in := 0 }) ∧
      CbFrame ownI (backEntryHeap h r z zs st) h3 ∧ R h3 := by
  have hz := hG.hz
  have hs := hG.hs
  have hR2 : R (backEntryHeap h r z zs st) := by
    refine (hK.local_ h _ ?_).1 hR
    intro b _; simp [backEntryHeap]
  obtain ⟨n, nx', h3, he, fr, hR3, -⟩ := hK.inOk _ .null hR2
  obtain ⟨nx0, h30, he0⟩ := hEof _ .null hR2
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨⟨rfl, -⟩, rfl⟩ := he0
  refine ⟨h3, ?_, fr, hR3⟩
  have hdisp := back_dispatch_eof (c := ⟨some r, some (.tab zs), inCb, inDesc, outCb, outDesc⟩) (zs := zs)
      (s := { st with mode := TYPE, last := 0, whave := 0 })
      (l := entryIL .null 0 st.window st.wsize)
      (h := backEntryHeap h r z zs st) (h3 := h3) (nx := nx') rfl (by simp [backEntryHeap]) rfl rfl rfl (by show (0 : UInt32) < 3; decide) he
  have hloop := xwhile_leave (cond := pure true) (by simp [xrun_pure]) hdisp
  have hzst := hG.zst
  have hz3 : r.get h3 = some { z with msg := .null } := by
    rw [CbFrame.zget fr r]; simp [backEntryHeap, hz]
  clear hdisp
  obtain ⟨ni, ai, ti, no, ao, tout, msg, state, za, zf, op, dt, ad, rs⟩ := z
  simp only at hni hzst
  subst hni hzst
  rw [C.run]
  unfold inflateBack
  simp only [entryIL, backEntryHeap] at hloop
  have hi3 : h3.istates zs = some { st with mode := TYPE, last := 0, whave := 0 } := by
    rw [fr.istates zs]; simp [backEntryHeap]
  isimp [hz, hs, backEntryHeap, hloop, entryIL, hi3, hz3]

/-- **Witness for `inflateBack_eof`.** The hypotheses hold together on the heap that the real
`inflateBackInit_(strm, 8, window, "1.3.2", 112)` makes from `wit0`, with the call-backs `eofIn` and `okOut`: the run of
`inflateBack` is an actual run and returns `Z_BUF_ERROR`. -/
theorem inflateBack_eof_witness :
    ∃ h' h'', C.run (inflateBackInit_ (some (.tab 0)) 8 (.ref (.blk 1) 0) (.ref (.blk 2) 0) 112) wit0 = .ok (Z_OK, h') ∧
      C.run (inflateBack (some (.tab 0)) eofIn .null okOut .null) h' = .ok (Z_BUF_ERROR, h'') := by
  have hz : (ZStreamRef.tab 0).get wit0 = some ZStream.zeroed := by simp [ZStreamRef.get, wit0]
  have hwin : WindowOk wit0 (.ref (.blk 1) 0) (2 ^ (i2u 8).toNat) :=
    ⟨1, 0, Array.replicate 256 0, rfl, by simp [wit0], by simp [wit0, staticHeap, Heap.empty],
      by rw [Array.size_replicate]; decide⟩
  obtain ⟨h', hr, -, hG, -⟩ := inflateBackInit__ok (r := .tab 0) (z := ZStream.zeroed) (wb := 8) (window := .ref (.blk 1) 0)
    (version := .ref (.blk 2) 0) wit0_uniq wit0_fresh hz (by simp [wit0]) (Or.inl rfl) (Or.inl rfl) (by intro c; cases c)
    (by unfold OkOn; simp [index8, wit0]; rfl) (by decide) (by decide) hwin
  have hni : (initStream2 ZStream.zeroed wit0.nextBlk).next_in = .null := by
    simp [initStream2, initStream, ZStream.zeroed, ZStream.garbage, Junk.of]; rfl
  obtain ⟨h3, he, -⟩ := inflateBack_eof hG hni (cbContract_eof 1) (fun h nx _ => ⟨nx, h, rfl⟩) trivial
  exact ⟨h', _, hr, he⟩

end Zlib.Infback.Proofs
