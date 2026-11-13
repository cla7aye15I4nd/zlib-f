import ZlibF.Proof.«infback.c.safety-inv»
import ZlibF.Proof.«infback.c.room»

/-!
# infback.c: writes of the decoder on the loop invariant, and `ROOM()`

The decoder's own writes (here: the state record) keep `PInv`: they change neither the
call-backs' blocks nor the window, so the protocol's invariant holds again by its locality
(`local_`, with `restoreWindow` the identity on an unchanged window), the state stays valid,
and the call's frame and liveness ledger grow by a step that changes only the state record.
`ROOM_p`: with a full window, `whave = wsize` is stored and `out` gets the whole window (the
protocol's `outStep`).
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

theorem split3 {α : Type} (a : Array α) (off m : Nat) (hm : off ≤ m) :
    a.extract 0 off ++ a.extract off m ++ a.extract m a.size = a := by
  rw [Array.extract_append_extract, show min 0 off = 0 from Nat.zero_min _, show max off m = m from Nat.max_eq_right hm,
    Array.extract_append_extract, Nat.zero_min, Array.extract_eq_self_of_le (Nat.le_max_right _ _)]

/-- Putting back the array a view already holds changes nothing. -/
theorem put_self {h : Heap} {r : BRef} {a : Array UInt8} (get : Space.get h r = some a) : Space.put h r a = h := by
  cases r with
  | blk b =>
    change h.bytes b = some a at get
    show { h with bytes := upd h.bytes b (some a) } = h
    rw [upd_self h.bytes b a get]
  | dstate_depth b =>
    change (h.dstates b).map (·.depth) = some a at get
    show (match h.dstates b with
      | some s => { h with dstates := upd h.dstates b (some { s with depth := a }) }
      | none => h) = h
    cases present : h.dstates b with
    | none => rfl
    | some s =>
      rw [present] at get
      injection get with e
      subst e
      show { h with dstates := upd h.dstates b (some s) } = h
      rw [upd_self h.dstates b s present]
  | _ => rfl

/-- With the window's view unchanged, restoring the window slice is the identity. -/
theorem restoreWindow_of_same {h after : Heap} {window : BPtr} {cap : Nat}
    (same : ∀ r off, window = .ref r off → Space.get after r = Space.get h r) :
    restoreWindow h after window cap = after := by
  unfold restoreWindow
  cases window with
  | null => rfl
  | ref r off =>
    simp only []
    rw [same r off rfl]
    cases get : Space.get h r with
    | none => rfl
    | some old =>
      simp only []
      rw [split3 old off (off + cap) (Nat.le_add_right _ _)]
      exact put_self (by rw [same r off rfl]; exact get)

/-- A write of the state record leaves every byte view. -/
theorem get_setI (h : Heap) (i : Nat) (s : InflateState) (r : BRef) :
    (Space.get (setI h i s) r : Option (Array UInt8)) = Space.get h r := by
  cases r <;> rfl

/-- **The protocol invariant survives a write of the state record.** -/
theorem proto_setI {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} (pr : Proto c r i window n)
    {h : Heap} {log : BackLog} (s : InflateState) (inv : pr.invariant h log) : pr.invariant (setI h i s) log := by
  refine (pr.local_ h (setI h i s) log ?_).1 inv
  rw [restoreWindow_of_same (fun r off _ => get_setI h i s r)]
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun b own => ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩⟩
  have ne : b ≠ i := fun e => pr.disjoint.1 (e ▸ own)
  show h.istates b = (upd h.istates i (some s)) b
  rw [upd_ne _ _ _ _ ne]

/-- Liveness is kept by a write of a live state record. -/
theorem live_setI {h : Heap} {i : Nat} {s0 : InflateState} (get : h.istates i = some s0) (s : InflateState)
    (b : Nat) : (setI h i s).live b ↔ h.live b := by
  by_cases e : b = i
  · subst e
    constructor
    · intro _; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [get]; simp))))))
    · intro _; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [setI]))))))
  · unfold Heap.live
    simp only [setI, upd_ne _ _ _ _ e]

/-- A write of the state record is a frame of the call. -/
theorem callbackFrame_setI {own : Nat → Prop} {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (s : InflateState) : CallbackFrame own h (setI h i s) r i window n := by
  classical
  have frame : Frame h (setI h i s) (fun b => StreamRoot r b ∨ b = i ∨ own b) :=
    ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ outside => by
      have ne : b ≠ i := fun e => outside (Or.inr (Or.inl e))
      exact ⟨rfl, rfl, rfl, rfl, rfl, by show (upd h.istates i (some s)) b = h.istates b; rw [upd_ne _ _ _ _ ne],
        rfl, rfl⟩⟩
  refine ⟨Frame.mono frame (fun b x => by rcases x with x | x | x <;> simp [x]), fun _ => ?_⟩
  have restore : restoreRegions h (setI h i s) [⟨window, n⟩] = setI h i s := by
    simp only [restoreRegions, List.foldl]
    cases window with
    | null => rfl
    | ref ref off =>
      simp only []
      cases get : Space.get h ref with
      | none => rfl
      | some a => exact put_self (by rw [get_setI]; exact get)
  refine ⟨by rw [restore]; exact Frame.mono frame (fun b x => by rcases x with x | x | x <;> simp [x]), ?_⟩
  intro region _ ref off a _ get
  exact ⟨a, by rw [get_setI]; exact get, rfl, fun _ _ _ => rfl⟩

/-- A write of a live state record keeps a valid state valid, when it keeps the window, its size,
`wbits` and the array sizes. -/
theorem backValid_setI {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s s' : InflateState}
    (valid : BackValid h r i z s) (window : s'.window = s.window) (size : s'.wsize = s.wsize)
    (bits : s'.wbits = s.wbits) (wf : s'.WellFormed) : BackValid (setI h i s') r i z s' := by
  obtain ⟨hz, hs, zst, za, zf, -, lo, hi, ws, nn, wr, fresh, uniq, globals⟩ := valid
  refine ⟨?_, by simp [setI], zst, za, zf, wf, by rw [bits]; exact lo, by rw [bits]; exact hi,
    by rw [size, bits]; exact ws, by rw [window]; exact nn, ?_, ?_, ?_, globals⟩
  · cases r <;> exact hz
  · rw [window, size]
    rcases wr with ⟨null, zero⟩ | ⟨ref, off, a, ptr, get, ro, room⟩
    · exact Or.inl ⟨null, zero⟩
    · refine Or.inr ⟨ref, off, a, ptr, by rw [get_setI]; exact get, ?_, room⟩
      cases ref <;> exact ro
  · intro b le live
    exact fresh b le ((live_setI hs s' b).1 live)
  · intro b
    have u := uniq b
    by_cases e : b = i
    · subst e
      simp only [setI, upd_same]
      unfold Zlib.Inflate.Spec.cnt at u ⊢
      rw [hs] at u
      simpa using u
    · simp only [setI, upd_ne _ _ _ _ e]
      exact u

/-- **A write of the state record keeps `PInv`** (with the same registers and log). -/
theorem PInv.setState {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {s : InflateState}
    (get : h.istates i = some s) (s' : InflateState) (window' : s'.window = s.window) (size : s'.wsize = s.wsize)
    (bits : s'.wbits = s.wbits) (wf : s'.WellFormed) (mode' : ModeOk i s') : PInv c pr h0 (setI h i s') l log := by
  obtain ⟨z, s1, valid, win, sz⟩ := I.valid
  have e : s1 = s := Option.some.inj (valid.2.1.symm.trans get)
  subst e
  have w := valid.2.2.2.2.2.2.2.2.2.2.1
  rw [win, sz] at w
  have held' : ChunkOk (setI h i s') r i window n log.active log.held := by
    intro ne
    obtain ⟨bytes, sep, roots⟩ := I.held ne
    refine ⟨?_, sep, roots⟩
    rcases bytes with x | ⟨ref, off, a, ptr, g, room, xs⟩
    · exact Or.inl x
    · exact Or.inr ⟨ref, off, a, ptr, by rw [get_setI]; exact g, room, xs⟩
  have frame' : CallbackFrame pr.own h0 (setI h i s') r i window n :=
    CallbackFrame.trans I.frame (callbackFrame_setI s') (fun disjoint => window_views w I.winRoot disjoint)
  have live' : ∀ b, ¬ pr.own b → ((setI h i s').live b ↔ h0.live b) :=
    fun b o => (live_setI get s' b).trans (I.live b o)
  exact
    { cstrm := I.cstrm, cst := I.cst,
      valid := ⟨z, s', backValid_setI valid window' size bits wf, by rw [window', win], by rw [size, sz]⟩,
      winRoot := I.winRoot, put := I.put, chunk := I.chunk, held := held', bits := I.bits,
      proto := proto_setI pr s' I.proto, frame := frame', live := live',
      mode := fun s2 g => by simp [setI] at g; subst g; exact mode' }

/-- **An `out` step of the protocol keeps `PInv`**: same registers, the log with the chunk in use. -/
theorem PInv.callback {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h h' : Heap} {l : IL} {log log' : BackLog} (I : PInv c pr h0 h l log)
    (ext : ExternalFrame pr.own h h') (win : SameBytePrefix h h' window window n)
    (held : log.held ≠ [] → Bytes h' log.active log.held.length log.held)
    (inv' : pr.invariant h' log') (active : log'.active = log.active) (heldEq : log'.held = log.held) :
    PInv c pr h0 h' l log' := by
  obtain ⟨z, s, valid, w, sz⟩ := I.valid
  have valid' := backValid_callback valid ext pr.disjoint.1 pr.disjoint.2 (by rw [w, sz]; exact win)
  have writable : Writable h window n := by
    have x := valid.2.2.2.2.2.2.2.2.2.2.1; rw [w, sz] at x; exact x
  exact
    { cstrm := I.cstrm, cst := I.cst, valid := ⟨z, s, valid', w, sz⟩, winRoot := I.winRoot, put := I.put,
      chunk := by rw [active, heldEq]; exact I.chunk,
      held := by
        rw [active, heldEq]
        intro ne
        obtain ⟨-, sep, roots⟩ := I.held ne
        exact ⟨held ne, sep, roots⟩,
      bits := I.bits, proto := inv',
      frame := CallbackFrame.trans I.frame (callbackFrame_of_external ext writable)
        (fun disjoint => window_views writable I.winRoot disjoint),
      live := fun b o => (live_callback ext b o).trans (I.live b o),
      mode := fun s1 g => by
        rw [istates_frame ext.1 valid.2.1 pr.disjoint.1] at g; injection g with e; subst e; exact I.mode s valid.2.1 }

/-- The window is readable as `n` bytes. -/
theorem bytes_of_writable {h : Heap} {p : BPtr} {n : Nat} (w : Writable h p n) : ∃ xs, Bytes h p n xs := by
  rcases w with ⟨null, zero⟩ | ⟨ref, off, a, ptr, get, -, room⟩
  · exact ⟨[], Or.inl ⟨null, zero, rfl⟩⟩
  · exact ⟨(a.toList.drop off).take n, Or.inr ⟨ref, off, a, ptr, get, room, rfl⟩⟩

/-- `PInv` does not read `ret`. -/
theorem PInv.withRet {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) (v : Int32) :
    PInv c pr h0 h { l with ret := v } log :=
  ⟨I.cstrm, I.cst, I.valid, I.winRoot, I.put, I.chunk, I.held, I.bits, I.proto, I.frame, I.live, I.mode⟩

/-- **`ROOM()` on the invariant.** With room left nothing happens. With a full window, `whave =
wsize` is stored and `out` gets the whole window (`outStep`): on 0 the fill restarts at the window,
otherwise the call leaves with `Z_BUF_ERROR`. The input registers are untouched. -/
theorem ROOM_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog}
    (I : PInv c pr h0 h l log) :
    ∃ res l' h' log', runX (ROOM c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → l'.left ≠ 0) ∧ (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧
      l'.have_ = l.have_ ∧ l'.next = l.next ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧
      backMeasure pr h' l' log' ≤ backMeasure pr h l log := by
  by_cases hl : l.left = 0
  · obtain ⟨z, s, valid, win, sz⟩ := I.valid
    have hs := valid.2.1
    have hc := I.cst
    have wf := valid.2.2.2.2.2.1
    let s1 : InflateState := { s with whave := s.wsize }
    have I1 : PInv c pr h0 (setI h i s1) l log :=
      I.setState hs s1 rfl rfl rfl (wf_with wf s1 rfl rfl rfl) (I.mode s hs)
    let l1 : IL := { l with put := s.window, left := s.wsize }
    have I1' : PInv c pr h0 (setI h i s1) l1 log :=
      { I1 with put := ⟨by show s.window = advance window (n - s.wsize.toNat); rw [sz, Nat.sub_self, advance_zero, win],
          by show s.wsize.toNat ≤ n; rw [sz]; exact Nat.le_refl _⟩ }
    have writable : Writable (setI h i s1) window n := by
      obtain ⟨z1, s2, valid1, w1, sz1⟩ := I1.valid
      have x := valid1.2.2.2.2.2.2.2.2.2.2.1; rw [w1, sz1] at x; exact x
    obtain ⟨xs, bytes⟩ := bytes_of_writable writable
    obtain ⟨rc, after, run, ext, winSame, held, inv'⟩ :=
      pr.outStep (setI h i s1) log s.window s.wsize xs I1'.proto (by rw [win, sz]; exact bytes) (by rw [sz]; exact Nat.le_refl _)
    let log2 : BackLog := { log with chunks := log.chunks ++ [xs], failed := log.failed || rc != 0 }
    have I2 : PInv c pr h0 after l1 log2 := PInv.callback I1' ext winSame held inv' rfl rfl
    have hld : ldInflateState c.st h = .ok (s, h) := by rw [hc]; exact ldInflateState_tab hs
    have hwr : wrS c.st (fun s => { s with whave := s.wsize }) h = .ok ((), setI h i s1) := by
      rw [hc]; exact wrS_tab hs _
    have hb : (l.left == 0) = true := by simpa using hl
    have hcall : ∀ l2 : IL, runX (monadLift (c.outCb c.outDesc s.window s.wsize) : X Int32) l2 (setI h i s1) =
        .ok ((.ok rc, l2), after) := fun l2 => runX_lift_ok run l2
    have rank : (after.istates i).map (fun s => modeRank s.mode) = (h.istates i).map (fun s => modeRank s.mode) := by
      rw [rank_frame ext (show (setI h i s1).istates i = some s1 by simp [setI]) pr.disjoint.1, hs]
      simp [setI, s1]
    have wsNe : s.wsize ≠ 0 := by
      intro e
      have ws := valid.2.2.2.2.2.2.2.2.1
      rw [e] at ws
      have pos : 0 < 2 ^ s.wbits.toNat := Nat.two_pow_pos _
      simp at ws; omega
    have meas : backMeasure pr after l1 log2 ≤ backMeasure pr h l log := by
      unfold backMeasure; rw [rank]; exact Nat.le_refl _
    by_cases hr0 : rc = 0
    · refine ⟨.ok (), l1, after, log2, ?_, I2, fun _ => wsNe, fun e x => (nomatch x), rfl, rfl, rfl, rfl, meas⟩
      unfold ROOM
      simp [runX_bind, runX_get, hb, hl, runX_lift_ok hld, runX_set, runX_lift_ok hwr, hcall, hr0, runX_pure, l1]
    · refine ⟨.error Ex.leave, { l1 with ret := Z_BUF_ERROR }, after, log2, ?_, I2.withRet Z_BUF_ERROR,
        fun x => (nomatch x), fun e x => by injection x with x; subst x; exact ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, meas⟩
      unfold ROOM
      simp [runX_bind, runX_get, hb, hl, runX_lift_ok hld, runX_set, runX_lift_ok hwr, hcall, hr0, runX_modify,
        runX_throw, l1]
  · exact ⟨.ok (), l, h, log, ROOM_have c hl, I, fun _ => hl, fun e x => (nomatch x), rfl, rfl, rfl, rfl,
      Nat.le_refl _⟩

end Zlib.Infback.Safety
