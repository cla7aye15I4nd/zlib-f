import ZlibF.Proof.«infback.c.safety-dispatch»

/-!
# infback.c: one call of `inflateBack` on the invariant

`xwhileBrk_partial` is the loop rule without a measure: a run that returns has kept the invariant.
It serves a call whose input has no bound (a step of a reachable history). `loop_partial` is
the dispatch loop under it. `entry_p` is the prologue: the invariant holds on the heap after
`strm->msg = NULL` and the state reset. `PInv.putZ` moves the invariant over a write of the
stream record. `back_call_partial` (a call that returns) and `back_call_total` (a call returns, input below `2^48`) are one call: prologue, loop, the last partial window to `out`,
`next_in` and `avail_in`.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- The condition step of `xwhileBrk` over the loop-carried registers. -/
def xcF (cond : X Bool) : IL × Stop → M (Bool × (IL × Stop)) :=
  fun (l, s) => match s with
    | .go => do
      let (r, l') ← StateT.run (ExceptT.run cond) l
      pure (match r with
        | .ok b => (b, (l', Stop.go))
        | .error e => (false, (l', Stop.ex e)))
    | s => pure (false, (l, s))

/-- The body step of `xwhileBrk`. -/
def xbF (body : X Bool) : IL × Stop → M (IL × Stop) :=
  fun (l, _) => do
    let (r, l') ← StateT.run (ExceptT.run body) l
    pure (match r with
      | .ok b => (l', if b then Stop.brk else Stop.go)
      | .error e => (l', Stop.ex e))

theorem go_succ {σ : Type} (C : σ → M (Bool × σ)) (B : σ → M σ) (n : Nat) (x : σ) :
    cwhile.go C B (n + 1) x = (do let (c, x') ← C x; if c then cwhile.go C B n (← B x') else pure x') := rfl

/-- **Loop rule without a measure.** A run of the loop that returns ends with `Q`, when `Inv`
holds at the start and every trip either leaves with `Q`, breaks with `Q (ok ())`, or keeps
`Inv`. -/
theorem xwhileBrk_partial {cond : X Bool} {body : X Bool} (Inv : IL → Heap → Prop)
    (Q : Except Ex Unit → IL → Heap → Prop)
    (hstep : ∀ l h, Inv l h → ∃ l1 h1 b, runX cond l h = .ok ((.ok b, l1), h1) ∧
      (b = true → ∃ r l2 h2, runX body l1 h1 = .ok ((r, l2), h2) ∧
        (match r with
          | .ok true => Q (.ok ()) l2 h2
          | .ok false => Inv l2 h2
          | .error e => Q (.error e) l2 h2)) ∧
      (b = false → Q (.ok ()) l1 h1))
    {l : IL} {h : Heap} (hI : Inv l h) {r : Except Ex Unit} {l' : IL} {h' : Heap}
    (run : runX (xwhileBrk cond body) l h = .ok ((r, l'), h')) : Q r l' h' := by
  have key : ∀ n (l : IL) (h : Heap), Inv l h → ∀ (l' : IL) (s : Stop) (h' : Heap),
      (cwhile.go (σ := IL × Stop)
        (xcF cond) (xbF body) n (l, Stop.go)) h = .ok ((l', s), h') →
      (match s with
       | .ex e => Q (.error e) l' h'
       | _ => Q (.ok ()) l' h') := by
    intro n
    induction n with
    | zero =>
      intro l h _ l' s h' hr
      simp [cwhile.go] at hr
    | succ n ih =>
      intro l h hI l' s h' hr
      obtain ⟨l1, h1, b, hc, hT, hF⟩ := hstep l h hI
      have hc' : (StateT.run (ExceptT.run cond) l) h = .ok ((.ok b, l1), h1) := hc
      cases b
      · have e0 : cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) (n + 1) (l, Stop.go) h =
            .ok ((l1, Stop.go), h1) := by simp [cwhile.go, xcF, hc']
        rw [e0] at hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
        exact hF rfl
      · obtain ⟨r, l2, h2, hb, hQ⟩ := hT rfl
        have hb' : (StateT.run (ExceptT.run body) l1) h1 = .ok ((r, l2), h2) := hb
        rcases r with e | b2
        · cases n with
          | zero =>
            have e0 : cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) (0 + 1) (l, Stop.go) h =
                cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) 0 (l2, Stop.ex e) h2 := by
                rw [go_succ]; simp only [bind_app, xcF, xbF, hc', hb', pure_app, ↓reduceIte]
            rw [e0] at hr; simp [cwhile.go] at hr
          | succ k =>
            have e0 : cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) (k + 1 + 1) (l, Stop.go) h =
                .ok ((l2, Stop.ex e), h2) := by simp [cwhile.go, xcF, xbF, hc', hb', bind_app, pure_app]
            rw [e0] at hr
            simp only [Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
            exact hQ
        · cases b2
          · have step : (cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) (n + 1) (l, Stop.go)) h =
                (cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) n (l2, Stop.go)) h2 := by
              simp [cwhile.go, xcF, xbF, hc', hb', bind_app, pure_app]
            rw [step] at hr
            exact ih l2 h2 hQ l' s h' hr
          · cases n with
            | zero =>
              have e0 : cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) (0 + 1) (l, Stop.go) h =
                  cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) 0 (l2, Stop.brk) h2 := by
                rw [go_succ]; simp only [bind_app, xcF, xbF, hc', hb', pure_app, ↓reduceIte]
              rw [e0] at hr; simp [cwhile.go] at hr
            | succ k =>
              have e0 : cwhile.go (σ := IL × Stop) (xcF cond) (xbF body) (k + 1 + 1) (l, Stop.go) h =
                  .ok ((l2, Stop.brk), h2) := by simp [cwhile.go, xcF, xbF, hc', hb', bind_app, pure_app]
              rw [e0] at hr
              simp only [Except.ok.injEq, Prod.mk.injEq] at hr
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
              exact hQ
  cases hgo : (cwhile.go (σ := IL × Stop)
        (xcF cond) (xbF body) fuel (l, Stop.go)) h with
  | error e =>
    have hrun : runX (xwhileBrk cond body) l h = .error e := by
      unfold xwhileBrk runX
      simp only [ExceptT.run, StateT.run, ExceptT.mk, cwhile, bind_app] at hgo ⊢
      erw [hgo]
    rw [hrun] at run; cases run
  | ok v =>
    obtain ⟨⟨l1, s⟩, h1⟩ := v
    have hrun : runX (xwhileBrk cond body) l h = .ok ((Stop.toE s, l1), h1) := by
      unfold xwhileBrk runX
      simp only [ExceptT.run, StateT.run, ExceptT.mk, cwhile, bind_app] at hgo ⊢
      erw [hgo]
      cases s <;> rfl
    rw [hrun] at run
    simp only [Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
    have q := key fuel l h hI l1 s h1 hgo
    rcases s with _ | _ | e <;> exact q

/-- **The dispatch loop on the invariant, for a run that returns**: it left by `goto inf_leave`
with one of the three results, the invariant kept. No bound on the input is needed. -/
theorem loop_partial (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) (fast : LenFast c pr h0) (short : Short i l h)
    {res : Except Ex Unit} {l' : IL} {h' : Heap}
    (run : runX (xwhile (pure true) (back_dispatch c)) l h = .ok ((res, l'), h')) :
    res = .error Ex.leave ∧ ∃ log', PInv c pr h0 h' l' log' ∧
      (l'.ret = Z_STREAM_END ∨ l'.ret = Z_DATA_ERROR ∨ l'.ret = Z_BUF_ERROR) := by
  let Inv : IL → Heap → Prop := fun l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧ Short i l1 h1
  let Q : Except Ex Unit → IL → Heap → Prop := fun res l1 h1 => res = .error Ex.leave ∧
    ∃ log1, PInv c pr h0 h1 l1 log1 ∧ (l1.ret = Z_STREAM_END ∨ l1.ret = Z_DATA_ERROR ∨ l1.ret = Z_BUF_ERROR)
  exact xwhileBrk_partial (cond := pure true) (body := (do back_dispatch c; pure false : X Bool)) Inv Q
    (by
      intro l1 h1 ⟨log1, I1, s1⟩
      refine ⟨l1, h1, true, rfl, fun _ => ?_, fun x => (nomatch x)⟩
      obtain ⟨res, l2, h2, run2, log2, I2, alt, sh2⟩ := dispatch_p c pr I1 hw fast s1
      rcases alt with ⟨rfl, -⟩ | ⟨rfl, ret⟩
      · exact ⟨.ok false, l2, h2, by rw [runX_bind, run2]; rfl, log2, I2, sh2 rfl⟩
      · exact ⟨.error Ex.leave, l2, h2, by rw [runX_bind, run2], rfl, log2, I2, ret⟩)
    ⟨log, I, short⟩ run

/-- A byte view in the heap names no state record and no stream record. -/
theorem roots_of_get {h : Heap} {r : ZStreamRef} {z : ZStream} {i : Nat} {s : InflateState}
    (uniq : Zlib.Inflate.Spec.Uniq h) (hz : r.get h = some z) (hs : h.istates i = some s)
    {ref : BRef} {off : Nat} {a : Array UInt8} (get : Space.get h ref = some a) :
    ∀ b, ByteRoot (.ref ref off) b → b ≠ i ∧ ¬ StreamRoot r b := by
  intro b root
  have notRoot : h.streams b = none → h.gzstates b = none → ¬ StreamRoot r b := by
    intro st gz e
    cases r with
    | tab j =>
      change b = j at e; subst e
      change h.streams b = some z at hz
      rw [st] at hz; cases hz
    | in_gzstate_strm j =>
      change b = j at e; subst e
      change (h.gzstates b).map (·.strm) = some z at hz
      rw [gz] at hz; cases hz
  have other : ∀ (x : Nat), Zlib.Inflate.Spec.cnt (h.bytes x) + Zlib.Inflate.Spec.cnt (h.dstates x) ≥ 1 → b = x →
      b ≠ i ∧ ¬ StreamRoot r b := by
    intro x one e
    subst e
    have u := uniq b
    refine ⟨fun e => ?_, notRoot ?_ ?_⟩
    · subst e
      simp only [hs, Zlib.Inflate.Spec.cnt_some] at u
      omega
    · cases hx : h.streams b with
      | none => rfl
      | some _ => simp only [hx, Zlib.Inflate.Spec.cnt_some] at u; omega
    · cases hx : h.gzstates b with
      | none => rfl
      | some _ => simp only [hx, Zlib.Inflate.Spec.cnt_some] at u; omega
  cases ref with
  | blk x =>
    have hb : h.bytes x = some a := get
    exact other x (by simp [hb]) root
  | dstate_depth x =>
    cases hd : h.dstates x with
    | none => simp [Space.get, hd] at get
    | some d => exact other x (by simp [hd]) root
  | str _ => exact absurd root id
  | st_dist_code => exact absurd root id
  | st_length_code => exact absurd root id

/-- The registers of `inflateBack` after its set-up, for the stream `z` and the state `s`. -/
def entryRegs (z : ZStream) (s : InflateState) : IL :=
  { IL.init with next := z.next_in, have_ := if z.next_in != .null then z.avail_in else 0, hold := 0, bits := 0, put := s.window, left := s.wsize }

/-- The state after the set-up: `mode = TYPE`, `last = 0`, `whave = 0`. -/
def entryState (s : InflateState) : InflateState := { s with mode := TYPE, last := 0, whave := 0 }

/-- The log at the call: the caller's first chunk. -/
def entryLog (z : ZStream) (first : List UInt8) : BackLog :=
  { supplied := first, chunks := [], active := z.next_in, held := first }

theorem bytes_length {h : Heap} {p : BPtr} {k : Nat} {xs : List UInt8} (b : Bytes h p k xs) : xs.length = k := by
  rcases b with ⟨-, rfl, rfl⟩ | ⟨ref, off, a, -, -, room, rfl⟩
  · rfl
  · simp only [List.length_take, List.length_drop, Array.length_toList]; omega

/-- **The invariant before the stream write of the prologue**: on the heap with the state reset. -/
theorem entry_state_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (cs : c.strm = some r) (ct : c.st = some (.tab i))
    {h : Heap} {z : ZStream} {s : InflateState} (valid : BackValid h r i z s)
    (win : s.window = window) (size : s.wsize.toNat = n) {w woff : Nat} (hw : window = .ref (.blk w) woff)
    {first : List UInt8}
    (firstB : if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first)
    (sep : Separate z.next_in first.length window n)
    (inv0 : pr.invariant h (entryLog z first)) :
    PInv c pr h (setI h i (entryState s)) (entryRegs z s) (entryLog z first) := by
  have hs := valid.2.1
  have hz := valid.1
  have wf := valid.2.2.2.2.2.1
  have uniq := valid.2.2.2.2.2.2.2.2.2.2.2.2.1
  have wr := valid.2.2.2.2.2.2.2.2.2.2.1
  rw [win, size] at wr
  have winRoot : ∀ b, ByteRoot window b → b ≠ i ∧ ¬ StreamRoot r b := by
    rcases wr with ⟨null, -⟩ | ⟨ref, off, a, ptr, get, -, -⟩
    · intro b root; rw [null] at root; exact absurd root id
    · rw [ptr]; exact roots_of_get uniq hz hs get
  have firstLen : (if z.next_in != .null then z.avail_in else 0).toNat ≤ first.length ∧
      ((if z.next_in != .null then z.avail_in else 0) ≠ 0 →
        z.next_in = advance z.next_in (first.length - (if z.next_in != .null then z.avail_in else 0).toNat)) := by
    by_cases e : z.next_in = .null
    · simp [e]
    · rw [if_neg e] at firstB
      have len := bytes_length firstB
      have ne : (z.next_in != .null) = true := by simpa using e
      simp [ne, len, advance_zero]
  have held : ChunkOk (setI h i (entryState s)) r i window n z.next_in first := by
    intro ne
    by_cases e : z.next_in = .null
    · rw [if_pos e] at firstB; exact absurd firstB ne
    · rw [if_neg e] at firstB
      have len := bytes_length firstB
      refine ⟨?_, sep, ?_⟩
      · rw [len]
        rcases firstB with x | ⟨ref, off, a, ptr, g, room, xs⟩
        · exact Or.inl x
        · exact Or.inr ⟨ref, off, a, ptr, by rw [get_setI]; exact g, room, xs⟩
      · rcases firstB with ⟨null, -⟩ | ⟨ref, off, a, ptr, g, -, -⟩
        · exact absurd null e
        · rw [ptr]; exact roots_of_get uniq hz hs g
  exact
    { cstrm := cs, cst := ct,
      valid := ⟨z, entryState s, backValid_setI valid rfl rfl rfl (wf_with wf _ rfl rfl rfl), win, size⟩,
      winRoot := winRoot,
      put := ⟨by show s.window = advance window (n - s.wsize.toNat); rw [size, Nat.sub_self, advance_zero, win],
        by show s.wsize.toNat ≤ n; rw [size]; exact Nat.le_refl _⟩,
      chunk := firstLen, held := held,
      bits := ⟨by show (0 : UInt32).toNat ≤ 39; decide, by show (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat; decide⟩,
      proto := proto_setI pr _ inv0,
      frame := callbackFrame_setI _,
      live := fun b _ => live_setI hs _ b,
      mode := fun s1 g => by
        simp [setI] at g; subst g
        exact ⟨Or.inl rfl, fun e => absurd (show TYPE = LEN from e) (by decide)⟩ }

/-- A write of the state record and a write of the stream record commute. -/
theorem put_setI (h : Heap) (r : ZStreamRef) (z : ZStream) (i : Nat) (s : InflateState) :
    r.put (setI h i s) z = setI (r.put h z) i s := by
  cases r <;> simp only [ZStreamRef.put, setI] <;> split <;> rfl

/-- **A write of the stream record keeps `PInv`**, when it keeps `state`, `zalloc` and `zfree`. -/
theorem PInv.putZ {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {z : ZStream} (hz : r.get h = some z)
    (z' : ZStream) (st : z'.state = z.state) (za' : z'.zalloc = z.zalloc) (zf' : z'.zfree = z.zfree) :
    PInv c pr h0 (r.put h z') l log := by
  obtain ⟨z1, s, valid, win, sz⟩ := I.valid
  have e : z1 = z := Option.some.inj (valid.1.symm.trans hz)
  subst e
  have shape := Zlib.Inflate.Proofs.shape_put hz z'
  have ist : (r.put h z').istates = h.istates := Zlib.Inflate.Proofs.ZStreamRef.put_istates h r _
  obtain ⟨-, hs, zst, za, zf, wf, lo, hi, ws, nn, wr, fresh, uniq, globals⟩ := valid
  have valid' : BackValid (r.put h z') r i z' s := by
    refine ⟨Zlib.Inflate.Proofs.ZStreamRef.get_put_same hz _, by rw [ist]; exact hs, by rw [st]; exact zst,
      by rw [za']; exact za, by rw [zf']; exact zf, wf, lo, hi, ws, nn,
      ?_, ?_, Zlib.Inflate.Proofs.Shape.uniq shape uniq, ?_⟩
    · rcases wr with x | ⟨ref, off, a, ptr, get, ro, room⟩
      · exact Or.inl x
      · exact Or.inr ⟨ref, off, a, ptr, by rw [get_put]; exact get, by rw [ro_put]; exact ro, room⟩
    · exact Zlib.Inflate.Proofs.Shape.fresh shape (by cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl) fresh
    · unfold LibraryGlobals at globals ⊢
      rw [← globals]; cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  have proto' : pr.invariant (r.put h z') log := by
    refine (pr.local_ h _ log ?_).1 I.proto
    rw [restoreWindow_of_same (fun ref _ _ => get_put h r _ ref)]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun b own => ?_⟩
    all_goals cases r
    all_goals simp only [ZStreamRef.put]
    all_goals try (split <;> rfl)
    · have ne : b ≠ _ := fun e => pr.disjoint.2 b e own
      split <;> simp [upd_ne _ _ _ _ ne]
    · have ne : b ≠ _ := fun e => pr.disjoint.2 b e own
      split <;> simp [upd_ne _ _ _ _ ne]
  have writable : Writable h window n := by rw [win, sz] at wr; exact wr
  exact
    { cstrm := I.cstrm, cst := I.cst, valid := ⟨z', s, valid', win, sz⟩, winRoot := I.winRoot,
      put := I.put, chunk := I.chunk,
      held := by
        intro ne
        obtain ⟨bytes, sep, roots⟩ := I.held ne
        refine ⟨?_, sep, roots⟩
        rcases bytes with x | ⟨ref, off, a, ptr, g, room, xs⟩
        · exact Or.inl x
        · exact Or.inr ⟨ref, off, a, ptr, by rw [get_put]; exact g, room, xs⟩,
      bits := I.bits, proto := proto',
      frame := CallbackFrame.trans I.frame (callbackFrame_put _) (fun d => window_views writable I.winRoot d),
      live := fun b o => (Zlib.Inflate.Proofs.Shape.live shape b).trans (I.live b o),
      mode := fun s1 g => I.mode s1 (by rw [ist] at g; exact g) }

/-- The end of `inflateBack()` after the dispatch loop (`inf_leave:`). -/
def backTail (strm : ZStreamPtr) (st : InflateStatePtr) (outCb : OutCb) (out_desc : BPtr) (l : IL) : M Int32 := do
  let s ← ldInflateState st
  let mut ret := l.ret
  if l.left < s.wsize then
    if (← outCb out_desc s.window (s.wsize - l.left)) != 0 && ret == Z_STREAM_END then ret := Z_BUF_ERROR
  wrZ strm fun z => { z with next_in := l.next, avail_in := l.have_ }
  return ret

/-- `inflateBack()` on a stream pointer, with its end split off. -/
def backBody (strm : ZStreamPtr) (inCb : InCb) (in_desc : BPtr) (outCb : OutCb) (out_desc : BPtr) : M Int32 := do
  let z ← ldZStream strm
  if z.state == none then return Z_STREAM_ERROR
  let st ← castInflateState z.state
  wrZ strm fun z => { z with msg := .null }
  wrS st fun s => { s with mode := TYPE, last := 0, whave := 0 }
  let z ← ldZStream strm
  let s ← ldInflateState st
  let next := z.next_in
  let have_ := if next != .null then z.avail_in else 0
  let l0 : IL := { IL.init with next := next, have_ := have_, hold := 0, bits := 0, put := s.window, left := s.wsize }
  let c : BCtx := { strm, st, inCb, inDesc := in_desc, outCb, outDesc := out_desc }
  let (_, l) ← StateT.run (ExceptT.run (xwhile (pure true) (back_dispatch c))) l0
  backTail strm st outCb out_desc l

theorem inflateBack_eq (r : ZStreamRef) (inCb : InCb) (in_desc : BPtr) (outCb : OutCb) (out_desc : BPtr) :
    inflateBack (some r) inCb in_desc outCb out_desc = backBody (some r) inCb in_desc outCb out_desc := rfl

/-- The context of a call. -/
def callCtx (r : ZStreamRef) (i : Nat) (input : InCb) (inDesc : BPtr) (output : OutCb) (outDesc : BPtr) : BCtx :=
  ⟨some r, some (.tab i), input, inDesc, output, outDesc⟩

/-- The heap after the prologue. -/
def entryHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (i : Nat) (s : InflateState) : Heap :=
  setI (r.put h { z with msg := .null }) i (entryState s)

theorem bind_err {α β : Type} {m : M α} {f : α → M β} {h : Heap} {e : Fault} (hm : m h = .error e) :
    (m >>= f) h = .error e := by simp [hm]

/-- **The prologue and the loop**: the call runs as its end on what the loop leaves, or fails as the
loop fails. -/
theorem call_prologue {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState} (valid : BackValid h r i z s)
    (input : InCb) (inDesc : BPtr) (output : OutCb) (outDesc : BPtr) :
    inflateBack (some r) input inDesc output outDesc h =
      match runX (xwhile (pure true) (back_dispatch (callCtx r i input inDesc output outDesc))) (entryRegs z s)
          (entryHeap h r z i s) with
      | .ok ((_, l3), h3) => backTail (some r) (some (.tab i)) output outDesc l3 h3
      | .error e => .error e := by
  have hz := valid.1
  have hs := valid.2.1
  have zst := valid.2.2.1
  have hz2 : r.get (setI (r.put h { z with msg := .null }) i (entryState s)) = some { z with msg := .null } := by
    rw [← put_setI]; exact Zlib.Inflate.Proofs.ZStreamRef.get_put_same (by cases r <;> exact hz) _
  have hs1 : (r.put h { z with msg := .null }).istates i = some s := by
    rw [Zlib.Inflate.Proofs.ZStreamRef.put_istates]; exact hs
  rw [inflateBack_eq]
  unfold backBody
  rw [bind_ok (show ldZStream (some r) h = .ok (z, h) by rw [ldZ_eq, hz])]
  simp only [zst]
  rw [if_neg (by simp)]
  rw [bind_ok (show castInflateState (some (StateRef.inflate i)) h = .ok (some (.tab i), h) from castI)]
  rw [bind_ok (show wrZ (some r) (fun z => { z with msg := .null }) h = .ok ((), r.put h { z with msg := .null }) by
    rw [wrZ_eq, hz])]
  rw [bind_ok (show wrS (some (.tab i)) (fun s => { s with mode := TYPE, last := 0, whave := 0 })
    (r.put h { z with msg := .null }) = .ok ((), setI (r.put h { z with msg := .null }) i (entryState s)) by
    rw [wrI_eq, hs1]; rfl)]
  rw [bind_ok (show ldZStream (some r) (setI (r.put h { z with msg := .null }) i (entryState s)) =
    .ok ({ z with msg := .null }, setI (r.put h { z with msg := .null }) i (entryState s)) by rw [ldZ_eq, hz2])]
  rw [bind_ok (show ldInflateState (some (.tab i)) (setI (r.put h { z with msg := .null }) i (entryState s)) =
    .ok (entryState s, setI (r.put h { z with msg := .null }) i (entryState s)) by rw [ldI_eq]; simp [setI])]
  obtain ⟨v, hL⟩ : ∃ v, runX (xwhile (pure true) (back_dispatch (callCtx r i input inDesc output outDesc)))
      (entryRegs z s) (entryHeap h r z i s) = v := ⟨_, rfl⟩
  rw [hL]
  cases v with
  | error e => exact bind_err hL
  | ok v =>
    obtain ⟨⟨res, l3⟩, h3⟩ := v
    exact bind_ok hL

/-- A writable range is writable in any shorter length. -/
theorem writable_le {h : Heap} {p : BPtr} {n k : Nat} (w : Writable h p n) (le : k ≤ n) : Writable h p k := by
  rcases w with ⟨null, zero⟩ | ⟨ref, off, a, ptr, get, ro, room⟩
  · exact Or.inl ⟨null, by omega⟩
  · exact Or.inr ⟨ref, off, a, ptr, get, ro, by omega⟩

/-- What a call leaves: the clause of the goal. -/
def CallPost {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {input : InCb} {inDesc : BPtr} {output : OutCb}
    {outDesc : BPtr} (protocol : CallbackProtocol r i window n input inDesc output outDesc) (h : Heap)
    (s : InflateState) (rc : Int32) (after : Heap) : Prop :=
  ∃ z' s' log, BackValid after r i z' s' ∧ s'.window = window ∧ s'.wsize = s.wsize ∧
    protocol.invariant after log ∧
    (rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧
    CallbackFrame protocol.own h after r i window n ∧
    (∀ b, ¬ protocol.own b → (after.live b ↔ h.live b))

set_option maxRecDepth 100000 in
/-- **The end of a call on the invariant**: the last partial window to `out`, then `next_in` and
`avail_in`. -/
theorem tail_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    (ret : l.ret = Z_STREAM_END ∨ l.ret = Z_DATA_ERROR ∨ l.ret = Z_BUF_ERROR) {s0 : InflateState}
    (size0 : s0.wsize.toNat = n) :
    ∃ rc after, backTail c.strm c.st c.outCb c.outDesc l h = .ok (rc, after) ∧ CallPost pr h0 s0 rc after := by
  obtain ⟨z, s, valid, win, sz⟩ := I.valid
  have hs := valid.2.1
  have hz := valid.1
  have hld : ldInflateState c.st h = .ok (s, h) := by rw [I.cst, ldI_eq, hs]
  have final : ∀ {h4 : Heap} {log4 : BackLog} (I4 : PInv c pr h0 h4 l log4) (rc : Int32),
      (rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) →
      ∃ after, (do wrZ c.strm fun z => { z with next_in := l.next, avail_in := l.have_ }; return rc : M Int32) h4 =
        .ok (rc, after) ∧ CallPost pr h0 s0 rc after := by
    intro h4 log4 I4 rc hrc
    obtain ⟨z4, s4, valid4, -, -⟩ := I4.valid
    have hz4 := valid4.1
    have I5 := I4.putZ hz4 { z4 with next_in := l.next, avail_in := l.have_ } rfl rfl rfl
    obtain ⟨z5, s5, valid5, win5, sz5⟩ := I5.valid
    refine ⟨r.put h4 { z4 with next_in := l.next, avail_in := l.have_ }, ?_, z5, s5, log4, valid5, win5,
      UInt32.toNat_inj.mp (by rw [sz5, size0]), I5.proto, hrc, I5.frame, I5.live⟩
    rw [I.cstrm, bind_ok (show wrZ (some r) (fun z => { z with next_in := l.next, avail_in := l.have_ }) h4 =
      .ok ((), r.put h4 { z4 with next_in := l.next, avail_in := l.have_ }) by rw [wrZ_eq, hz4])]
    rfl
  by_cases lt : l.left < s.wsize
  · have wr := valid.2.2.2.2.2.2.2.2.2.2.1
    have ltN : l.left.toNat < s.wsize.toNat := UInt32.lt_iff_toNat_lt.mp lt
    have subN : (s.wsize - l.left).toNat = s.wsize.toNat - l.left.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    obtain ⟨xs, bytes⟩ := bytes_of_writable (writable_le wr (k := (s.wsize - l.left).toNat) (by omega))
    obtain ⟨rc, h4, run4, ext, winSame, held, inv'⟩ :=
      pr.outStep h log s.window (s.wsize - l.left) xs I.proto bytes (by rw [subN, ← sz]; omega)
    let log4 : BackLog := { log with chunks := log.chunks ++ [xs], failed := log.failed || rc != 0 }
    have I4 : PInv c pr h0 h4 l log4 := PInv.callback I ext winSame held inv' rfl rfl
    by_cases f : (rc != 0 && l.ret == Z_STREAM_END) = true
    · obtain ⟨after, run5, post⟩ := final I4 Z_BUF_ERROR (Or.inr (Or.inr rfl))
      refine ⟨Z_BUF_ERROR, after, ?_, post⟩
      unfold backTail
      rw [bind_ok hld]
      simp only [lt, ↓reduceIte]
      rw [bind_ok (show c.outCb c.outDesc s.window (s.wsize - l.left) h = .ok (rc, h4) from run4)]
      simp only [f, ↓reduceIte]
      exact run5
    · obtain ⟨after, run5, post⟩ := final I4 l.ret ret
      refine ⟨l.ret, after, ?_, post⟩
      unfold backTail
      rw [bind_ok hld]
      simp only [lt, ↓reduceIte]
      rw [bind_ok (show c.outCb c.outDesc s.window (s.wsize - l.left) h = .ok (rc, h4) from run4)]
      simp only [f, Bool.false_eq_true, ↓reduceIte]
      exact run5
  · obtain ⟨after, run5, post⟩ := final I l.ret ret
    refine ⟨l.ret, after, ?_, post⟩
    unfold backTail
    rw [bind_ok hld]
    simp only [lt, Bool.false_eq_true, ↓reduceIte]
    exact run5

/-- **The invariant after the prologue.** -/
theorem entry_p {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {z : ZStream} {s : InflateState}
    {input : InCb} {inDesc : BPtr} {output : OutCb} {outDesc : BPtr}
    (protocol : CallbackProtocol r i window n input inDesc output outDesc) {first : List UInt8}
    (valid : BackValid h r i z s) (win : s.window = window) (size : s.wsize.toNat = n)
    {w woff : Nat} (hw : window = .ref (.blk w) woff)
    (firstB : if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first)
    (sep : Separate z.next_in first.length window n)
    (inv0 : protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first }) :
    PInv (callCtx r i input inDesc output outDesc) protocol h (entryHeap h r z i s) (entryRegs z s)
      (entryLog z first) := by
  have I0 := entry_state_p (callCtx r i input inDesc output outDesc) protocol rfl rfl valid win size hw firstB sep inv0
  have hz : r.get (setI h i (entryState s)) = some z := by cases r <;> exact valid.1
  have I1 := I0.putZ hz { z with msg := .null } rfl rfl rfl
  unfold entryHeap
  rw [← put_setI]
  exact I1

/-- **One call that returns, on any protocol**: the clause of the goal. No bound on the input
is needed; `fast` is the fast path of `case LEN`. -/
theorem back_call_partial {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {z : ZStream}
    {s : InflateState} {input : InCb} {inDesc : BPtr} {output : OutCb} {outDesc : BPtr}
    (protocol : CallbackProtocol r i window n input inDesc output outDesc) {first : List UInt8}
    (valid : BackValid h r i z s) (win : s.window = window) (size : s.wsize.toNat = n)
    {w woff : Nat} (hw : window = .ref (.blk w) woff)
    (firstB : if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first)
    (sep : Separate z.next_in first.length window n)
    (inv0 : protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first })
    (fast : LenFast (callCtx r i input inDesc output outDesc) protocol h)
    {rc : Int32} {after : Heap}
    (run : C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after)) :
    CallPost protocol h s rc after := by
  have I0 := entry_p protocol valid win size hw firstB sep inv0
  unfold C.run at run
  rw [call_prologue valid] at run
  obtain ⟨v, hL⟩ : ∃ v, runX (xwhile (pure true) (back_dispatch (callCtx r i input inDesc output outDesc)))
      (entryRegs z s) (entryHeap h r z i s) = v := ⟨_, rfl⟩
  rw [hL] at run
  cases v with
  | error e => cases run
  | ok v =>
    obtain ⟨⟨res, l3⟩, h3⟩ := v
    obtain ⟨-, log3, I3, ret3⟩ := loop_partial (callCtx r i input inDesc output outDesc) protocol I0 hw fast (Short.of_bits (l := entryRegs z s) (show (0 : UInt32).toNat < 8 by decide)) hL
    obtain ⟨rc', after', run', post⟩ := tail_p (callCtx r i input inDesc output outDesc) protocol I3 ret3 size
    have e : backTail (some r) (some (.tab i)) output outDesc l3 h3 = .ok (rc', after') := run'
    simp only [] at run
    rw [e] at run
    simp only [Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact post

/-- **One call returns, for a protocol whose input is below `2^48` bytes.** -/
theorem back_call_total {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {z : ZStream}
    {s : InflateState} {input : InCb} {inDesc : BPtr} {output : OutCb} {outDesc : BPtr}
    (protocol : CallbackProtocol r i window n input inDesc output outDesc) {first : List UInt8}
    (valid : BackValid h r i z s) (win : s.window = window) (size : s.wsize.toNat = n)
    {w woff : Nat} (hw : window = .ref (.blk w) woff)
    (firstB : if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first)
    (sep : Separate z.next_in first.length window n)
    (inv0 : protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first })
    (fast : LenFast (callCtx r i input inDesc output outDesc) protocol h)
    (bound : protocol.inputBound < 2 ^ 48) :
    ∃ rc after, C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after) ∧
      CallPost protocol h s rc after := by
  have I0 := entry_p protocol valid win size hw firstB sep inv0
  obtain ⟨l3, h3, log3, hL, I3, ret3⟩ := loop_p (callCtx r i input inDesc output outDesc) protocol I0 hw fast (Short.of_bits (l := entryRegs z s) (show (0 : UInt32).toNat < 8 by decide)) bound
  obtain ⟨rc, after, run', post⟩ := tail_p (callCtx r i input inDesc output outDesc) protocol I3 ret3 size
  refine ⟨rc, after, ?_, post⟩
  unfold C.run
  rw [call_prologue valid, hL]
  exact run'

end Zlib.Infback.Safety
