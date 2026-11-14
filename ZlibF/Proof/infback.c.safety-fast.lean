import ZlibF.Proof.«infback.c.safety-reach»
import ZlibF.Proof.«inffast.c.consume»

/-!
# infback.c: the fast path of `case LEN`, and the sequence goal

`case LEN` calls `inflate_fast` when `have >= 6 && left >= 258`: `RESTORE()`, the call with
`start = state->wsize`, `LOAD()`. In `inflateBack()` the output is the window itself, so the call
runs on an `EnvG true` (`fast_env`): the window block is the output block, `wnext = 0`, and the
window ends where the output range ends. `fast_consumes` (`inffast.c.consume`) gives the run, its
frame and the strict consumption of input bits; `LEN_fast_p` turns them into one `Round` of the
dispatch loop.

`inflate_fast`'s entry takes output in a raw heap byte block, so the fast path is proved only at
such a window (`lenFast_of_blk`). The histories of the goal have their window there
(`back_reach_window`), and the composition below uses the fast path only at such windows.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
open Zlib.Inffast.Spec (LenTableSafe DistTableSafe LenLeavesPositive)
set_option autoImplicit false

set_option maxRecDepth 100000 in
/-- The literal/length table of a `LEN` state, with the positive leaves `inflate_fast` needs. -/
theorem lenTabPos {h : Heap} {i : Nat} {s : InflateState} (hs : h.istates i = some s) (tabs : TablesOk i s)
    (globals : LibraryGlobals h) :
    ∃ ref off ca, s.lencode = .ref ref off ∧ Space.get h ref = some ca ∧
      LenTableSafe ca off s.lenbits.toNat ∧ LenLeavesPositive ca off s.lenbits.toNat := by
  rcases tabs.1 with ⟨ol, lc, safe, pos, -⟩ | ⟨lc, lb⟩
  · exact ⟨.istate_codes i, ol, s.codes, lc, CodeRef.get_istate_codes hs, safe, pos⟩
  · have get : Space.get h CodeRef.st_lenfix = some Zlib.InffixedH.lenfix := by
      change some h.static.lenfix = some Zlib.InffixedH.lenfix
      rw [globals]
      rfl
    refine ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, lc, get, ?_, ?_⟩
    all_goals rw [lb]
    · exact Zlib.Inffast.Proofs.lenfix_tableSafe
    · exact Zlib.Inffast.Proofs.lenfix_leavesPositive

theorem rget_setI (h : Heap) (r : ZStreamRef) (i : Nat) (s : InflateState) : r.get (setI h i s) = r.get h := by
  cases r <;> rfl

theorem rget_winHeap (h : Heap) (r : ZStreamRef) (w : Nat) (a : Array UInt8) : r.get (winHeap h w a) = r.get h := by
  cases r <;> rfl

theorem modeOk_tb {i : Nat} {s : InflateState} (m : s.mode = TYPE ∨ s.mode = BAD) : ModeOk i s := by
  refine ⟨by rcases m with m | m <;> simp [m], fun e => ?_⟩
  exfalso
  rcases m with m | m <;> rw [m] at e <;> exact absurd e (by decide)

/-- `RESTORE()` on the records of the invariant. -/
theorem RESTORE_back_run {c : BCtx} {r : ZStreamRef} {i : Nat} {h : Heap} {z : ZStream} {s : InflateState}
    (cstrm : c.strm = some r) (cst : c.st = some (.tab i)) (hz : r.get h = some z) (hs : h.istates i = some s)
    (l : IL) :
    runX (RESTORE c.strm c.st) l h = .ok ((.ok (), l),
      setI (r.put h { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }) i
        { s with hold := l.hold, bits := l.bits }) := by
  unfold RESTORE
  have write : wrZ c.strm (fun z => { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }) h =
      .ok ((), r.put h { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }) := by
    simp only [cstrm, wrZ_eq, hz]
  have hs1 : (r.put h { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }).istates i =
      some s := by
    rw [Zlib.Inflate.Proofs.ZStreamRef.put_istates]; exact hs
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok write]
  simp only []
  rw [runX_lift_ok (wrS_ok cst hs1 _)]

/-- `LOAD()` on the records of the invariant. -/
theorem LOAD_back_run {c : BCtx} {r : ZStreamRef} {i : Nat} {h : Heap} {z : ZStream} {s : InflateState}
    (cstrm : c.strm = some r) (cst : c.st = some (.tab i)) (hz : r.get h = some z) (hs : h.istates i = some s)
    (l : IL) :
    runX (LOAD c.strm c.st) l h = .ok ((.ok (), { l with
        put := z.next_out, left := z.avail_out, next := z.next_in,
        have_ := z.avail_in, hold := s.hold, bits := s.bits }), h) := by
  unfold LOAD
  have hz' : ldZStream c.strm h = .ok (z, h) := by rw [cstrm]; exact ldZStream_ok hz
  have hs' : ldInflateState c.st h = .ok (s, h) := by rw [cst]; exact ldInflateState_tab hs
  rw [runX_bind, runX_lift_ok hz']
  simp only []
  rw [runX_bind, runX_lift_ok hs']
  rfl

/-- **`fast_env`.** After `RESTORE()` in `case LEN` with `have >= 6`, `left >= 258` and fewer than 8
bits held, the heap is the entry of an `EnvG true` with `start = wsize`: the input is the rest of
the chunk `in` returned, the output is the unwritten tail of the window, inside the window's own
block. Its literal/length table has positive leaves. -/
theorem fast_env (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {z : ZStream} {s : InflateState}
    (hz : r.get h = some z) (hs : h.istates i = some s) (mode : s.mode = LEN) (short : l.bits.toNat < 8)
    (fast : (l.have_ >= 6 && l.left >= 258) = true) :
    ∃ e : Zlib.Inffast.Proofs.EnvG true,
      e.h0 = setI (r.put h { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }) i
        { s with hold := l.hold, bits := l.bits } ∧
      e.strm = c.strm ∧ e.start = s.wsize ∧ e.r = r ∧ e.stid = i ∧
      e.sm0 = { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ } ∧
      e.s0 = { s with hold := l.hold, bits := l.bits } ∧ e.ob = w ∧ e.o0 = woff + (n - l.left.toNat) ∧
      l.next = .ref (.blk e.ib) e.i0 ∧ LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat := by
  have margins : 6 ≤ l.have_ ∧ 258 ≤ l.left := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.1
  have outputRoom : 258 ≤ l.left.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.2
  have hnz : l.have_ ≠ 0 := by intro e; rw [e] at inputRoom; exact absurd inputRoom (by decide)
  obtain ⟨z0, s0, valid, win, sz⟩ := I.valid
  have ez : z0 = z := Option.some.inj (valid.1.symm.trans hz)
  have es : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  rw [ez, es] at valid
  rw [es] at win sz
  obtain ⟨-, -, zst, -, -, -, -, hi, ws, -, wr, -, -, globals⟩ := valid
  have st : s.sane ≠ 0 ∧ s.wnext = 0 ∧ s.whave.toNat ≤ s.wsize.toNat := I.stOk s hs
  -- the window
  rw [win, sz, hw] at wr
  obtain ⟨wa, wget, wro, wroom⟩ : ∃ wa : Array UInt8, h.bytes w = some wa ∧ h.ro w = false ∧ woff + n ≤ wa.size := by
    rcases wr with ⟨null, -⟩ | ⟨ref, off, a, ptr, g, ro, rm⟩
    · cases null
    · injection ptr with e1 e2
      subst e1 e2
      exact ⟨a, g, ro, rm⟩
  have hput : l.put = .ref (.blk w) (woff + (n - l.left.toNat)) := by rw [I.put.1, hw]; rfl
  have hleft : l.left.toNat ≤ n := I.put.2
  -- the input
  have hheld : l.have_.toNat ≤ log.held.length := I.chunk.1
  have hne : log.held ≠ [] := by intro e; rw [e, List.length_nil] at hheld; omega
  have hnext := I.chunk.2 hnz
  obtain ⟨b, aoff, hact⟩ := I.chunkBlk hne
  obtain ⟨hbytes, hsep, -⟩ := I.held hne
  obtain ⟨ina, inget, inroom⟩ : ∃ a : Array UInt8, h.bytes b = some a ∧ aoff + log.held.length ≤ a.size := by
    rcases hbytes with ⟨null, -, -⟩ | ⟨ref, off, a, ptr, g, rm, -⟩
    · rw [hact] at null; cases null
    · rw [hact] at ptr
      injection ptr with e1 e2
      subst e1 e2
      exact ⟨a, g, rm⟩
  have hnext' : l.next = .ref (.blk b) (aoff + (log.held.length - l.have_.toNat)) := by rw [hnext, hact]; rfl
  have hsep2 : BRef.blk b ≠ BRef.blk w ∨ aoff + log.held.length ≤ woff ∨ woff + n ≤ aoff := by
    rw [hact, hw] at hsep
    rcases hsep with z1 | z1 | x
    · omega
    · omega
    · exact x
  have hsep' : b ≠ w ∨ (b = w ∧
      (aoff + (log.held.length - l.have_.toNat) + l.have_.toNat ≤ woff + (n - l.left.toNat) ∨
       woff + (n - l.left.toNat) + l.left.toNat ≤ aoff + (log.held.length - l.have_.toNat))) := by
    rcases hsep2 with ne | lt | gt
    · left; intro e; exact ne (by rw [e])
    · by_cases e : b = w
      · right; exact ⟨e, Or.inl (by omega)⟩
      · left; exact e
    · by_cases e : b = w
      · right; exact ⟨e, Or.inr (by omega)⟩
      · left; exact e
  have inbig : ina.size < 2 ^ 63 := by
    have x := I.fit (.blk b) ina inget
    unfold ZlibF.PlatformMemory.byteObjectLimit at x
    exact x
  have wbig : wa.size < 2 ^ 63 := by
    have x := I.fit (.blk w) wa wget
    unfold ZlibF.PlatformMemory.byteObjectLimit at x
    exact x
  have wsize32 : s.wsize.toNat ≤ 32768 := by
    have pow := Nat.pow_le_pow_right (by decide : 0 < 2) hi
    omega
  -- the heap after RESTORE
  let z1 : ZStream := { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }
  let s1 : InflateState := { s with hold := l.hold, bits := l.bits }
  have hsm1 : r.get (setI (r.put h z1) i s1) = some z1 := by
    rw [rget_setI]; exact Zlib.Inflate.Proofs.ZStreamRef.get_put_same hz z1
  have hs1 : (setI (r.put h z1) i s1).istates i = some s1 := by simp [setI]
  have hIN1 : (setI (r.put h z1) i s1).bytes b = some ina := by
    show (r.put h z1).bytes b = some ina
    rw [Zlib.Inffast.Proofs.put_bytes]; exact inget
  have hA1 : (setI (r.put h z1) i s1).bytes w = some wa := by
    show (r.put h z1).bytes w = some wa
    rw [Zlib.Inffast.Proofs.put_bytes]; exact wget
  have hro1 : (setI (r.put h z1) i s1).ro w = false := by
    show (r.put h z1).ro w = false
    rw [Zlib.Inffast.Proofs.put_ro]; exact wro
  have glob1 : LibraryGlobals (setI (r.put h z1) i s1) := by
    unfold LibraryGlobals at globals ⊢
    rw [← globals]
    exact Zlib.Inffast.Proofs.put_static r h z1
  have tabs1 : TablesOk i s1 := (I.mode s hs).2 mode
  obtain ⟨rl, ol, LCA, hlc, hLCA, hlt, hpos⟩ := lenTabPos hs1 tabs1 glob1
  obtain ⟨rd, od, DCA, -, -, hdc, -, hDCA, hdt, -⟩ := distTab hs1 tabs1 glob1
  let e : Zlib.Inffast.Proofs.EnvG true := {
    h0 := setI (r.put h z1) i s1, strm := c.strm, start := s.wsize, r := r, sm0 := z1, stid := i, s0 := s1,
    hstrm := I.cstrm, hsm := hsm1, hrw := by cases r <;> rfl, hstate := zst, hs0 := hs1,
    ib := b, i0 := aoff + (log.held.length - l.have_.toNat), IN := ina, hnin := hnext', hIN := hIN1,
    hai := inputRoom,
    hINsz := by
      change aoff + (log.held.length - l.have_.toNat) + l.have_.toNat ≤ ina.size
      omega,
    hINbig := inbig,
    ob := w, o0 := woff + (n - l.left.toNat), A0 := wa, hnout := hput, hA0 := hA1, hro := hro1,
    hao := outputRoom,
    hAsz := by
      change woff + (n - l.left.toNat) + l.left.toNat ≤ wa.size
      omega,
    hAbig := wbig,
    hstart := by change l.left.toNat ≤ s.wsize.toNat; omega,
    hbeg := by change s.wsize.toNat - l.left.toNat ≤ woff + (n - l.left.toNat); omega,
    hsep := hsep',
    hbits := short, hhold := I.bits.2, hsane := st.1, hws := wsize32, hwh := st.2.2,
    hwn := by change s.wnext.toNat ≤ s.wsize.toNat; rw [st.2.1]; exact Nat.zero_le _,
    wb := w, woff := woff, W := wa,
    hwin := fun _ => ⟨by change s.window = _; rw [win, hw],
      fun _ => ⟨st.2.1, by change woff + s.wsize.toNat ≤ woff + (n - l.left.toNat) + l.left.toNat; omega⟩,
      hA1, by change woff + s.wsize.toNat ≤ wa.size; omega⟩,
    rl := rl, ol := ol, LCA := LCA, hlc := hlc, hLCA := hLCA, hlt := hlt,
    rd := rd, od := od, DCA := DCA, hdc := hdc, hDCA := hDCA, hdt := hdt }
  exact ⟨e, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnext', hpos⟩

set_option maxHeartbeats 1000000 in
/-- **`LEN_fast_p`.** The fast path of `case LEN` on the invariant: `RESTORE()`, `inflate_fast`
with `start = wsize`, `LOAD()`, `break`. The invariant holds after; the measure falls, because the
call consumes input bits unless it ends the block (`TYPE`, lower rank) or fails (`BAD`, rank 0);
fewer than 8 bits stay held. -/
theorem LEN_fast_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (mode : s.mode = LEN) (short : l.bits.toNat < 8) (fast : (l.have_ >= 6 && l.left >= 258) = true) :
    ∃ res l' h', runX (back_LEN c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h' := by
  have margins : 6 ≤ l.have_ ∧ 258 ≤ l.left := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := by simpa [UInt32.le_iff_toNat_le] using margins.1
  have hnz : l.have_ ≠ 0 := by intro e; rw [e] at inputRoom; exact absurd inputRoom (by decide)
  obtain ⟨z, s0, valid, -, -⟩ := I.valid
  have es : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  rw [es] at valid
  have hz := valid.1
  have wf := valid.2.2.2.2.2.1
  have tabs : TablesOk i s := (I.mode s hs).2 mode
  have hleft : l.left.toNat ≤ n := I.put.2
  have hheld : l.have_.toNat ≤ log.held.length := I.chunk.1
  have hne : log.held ≠ [] := by intro e; rw [e, List.length_nil] at hheld; omega
  obtain ⟨e, eh0, estrm, estart, er, estid, esm0, es0, eob, eo0, enext, hpos⟩ :=
    fast_env c pr I hw hz hs mode short fast
  obtain ⟨after, call, post, -, cons⟩ := Zlib.Inffast.Proofs.fast_consumes e hpos
  obtain ⟨z1, hz1⟩ : ∃ z1 : ZStream,
      z1 = { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ } := ⟨_, rfl⟩
  obtain ⟨s1, hs1⟩ : ∃ s1 : InflateState, s1 = { s with hold := l.hold, bits := l.bits } := ⟨_, rfl⟩
  rw [← hz1, ← hs1] at eh0
  rw [← hz1] at esm0
  rw [← hs1] at es0
  have zi : z1.avail_in = l.have_ := by rw [hz1]
  have zo : z1.avail_out = l.left := by rw [hz1]
  -- the run
  have hR := RESTORE_back_run I.cstrm I.cst hz hs l
  rw [← hz1, ← hs1] at hR
  have hsB : (setI (r.put h z1) i s1).istates i = some s1 := by simp [setI]
  have hrd : rdS c.st (·.wsize) (setI (r.put h z1) i s1) = .ok (s.wsize, setI (r.put h z1) i s1) := by
    rw [rdS_ok I.cst hsB (·.wsize)]
    rw [hs1]
  have hexec : Zlib.Inffast.inflate_fast c.strm s.wsize (setI (r.put h z1) i s1) = .ok ((), after) := by
    rw [← estrm, ← estart, ← eh0]
    exact call
  -- the fast result
  obtain ⟨used, made, buf, bytes, msg, m2, b2, hd2, hused, -, hmade, hsize, hb2, hhd2, heap, frame, cls, -⟩ := post
  rw [eh0, er, estid, es0, esm0, eob, eo0] at heap
  rw [esm0] at hused hmade
  rw [eo0] at frame
  rw [es0, esm0] at cls
  have hA := e.hA0
  rw [eh0, eob] at hA
  rw [zi] at hused
  rw [zo] at hmade
  obtain ⟨s2, hs2⟩ : ∃ s2 : InflateState, s2 = { s1 with mode := m2, bits := b2, hold := hd2 } := ⟨_, rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ z2 : ZStream, z2 = { z1 with
      next_in := .ref (.blk e.ib) (e.i0 + used),
      next_out := .ref (.blk w) (woff + (n - l.left.toNat) + made),
      avail_in := UInt32.ofNat (z1.avail_in.toNat - used),
      avail_out := UInt32.ofNat (z1.avail_out.toNat - made), msg := msg } := ⟨_, rfl⟩
  have hafter : after = r.put (setI (winHeap (setI (r.put h z1) i s1) w bytes) i s2) z2 := by
    rw [heap, hs2, hz2]
    rfl
  -- the invariant through RESTORE, the window bytes, the state and the stream
  have IA := I.putZ hz z1 (by rw [hz1]) (by rw [hz1]) (by rw [hz1])
  have hsA : (r.put h z1).istates i = some s := by
    rw [Zlib.Inflate.Proofs.ZStreamRef.put_istates]; exact hs
  have wf1 : s1.WellFormed := wf_with wf s1 (by rw [hs1]) (by rw [hs1]) (by rw [hs1])
  have IB := IA.setState hsA s1 (by rw [hs1]) (by rw [hs1]) (by rw [hs1]) wf1
    (by rw [hs1]; exact I.mode s hs) (by rw [hs1]; exact ⟨rfl, rfl, Or.inl rfl⟩)
  have IC := IB.storeWindow hw hA hsize (fun j hj => frame j (by omega))
  have hsC : (winHeap (setI (r.put h z1) i s1) w bytes).istates i = some s1 := by simp [winHeap, setI]
  have tabs2 : TablesOk i s2 := by rw [hs2, hs1]; exact tabs
  have mode2 : ModeOk i s2 := by
    rcases cls with ⟨hm, -⟩ | ⟨hm, -⟩ | hm
    · refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ?_))), fun _ => tabs2⟩
      rw [hs2]; show m2 = LEN; rw [hm, hs1]; exact mode
    · exact modeOk_tb (Or.inl (by rw [hs2]; exact hm))
    · exact modeOk_tb (Or.inr (by rw [hs2]; exact hm))
  have ID := IC.setState hsC s2 (by rw [hs2]) (by rw [hs2]) (by rw [hs2])
    (wf_with wf1 s2 (by rw [hs2]) (by rw [hs2]) (by rw [hs2])) mode2 (by rw [hs2]; exact ⟨rfl, rfl, Or.inl rfl⟩)
  have hzD : r.get (setI (winHeap (setI (r.put h z1) i s1) w bytes) i s2) = some z1 := by
    rw [rget_setI, rget_winHeap, rget_setI]
    exact Zlib.Inflate.Proofs.ZStreamRef.get_put_same hz z1
  have IE := ID.putZ hzD z2 (by rw [hz2]) (by rw [hz2]) (by rw [hz2])
  rw [← hafter] at IE
  -- LOAD
  have hzE : r.get after = some z2 := by
    rw [hafter]; exact Zlib.Inflate.Proofs.ZStreamRef.get_put_same hzD z2
  have hsE : after.istates i = some s2 := by
    rw [hafter, Zlib.Inflate.Proofs.ZStreamRef.put_istates]; simp [setI]
  have hL := LOAD_back_run I.cstrm I.cst hzE hsE l
  have run : runX (back_LEN c) l h = .ok ((.ok (), { l with
      put := z2.next_out, left := z2.avail_out,
      next := z2.next_in, have_ := z2.avail_in, hold := s2.hold, bits := s2.bits }), after) := by
    rw [back_LEN_eq']
    simp only [runX_bind, runX_get, fast, ↓reduceIte, hR, runX_lift_ok hrd, runX_lift_ok hexec, hL, runX_pure]
  -- the counters
  have ain : (UInt32.ofNat (z1.avail_in.toNat - used)).toNat = l.have_.toNat - used := by
    rw [zi]
    exact UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; have := UInt32.toNat_lt l.have_; omega)
  have aout : (UInt32.ofNat (z1.avail_out.toNat - made)).toNat = l.left.toNat - made := by
    rw [zo]
    exact UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; have := UInt32.toNat_lt l.left; omega)
  have have2 : z2.avail_in.toNat = l.have_.toNat - used := by rw [hz2]; exact ain
  have left2 : z2.avail_out.toNat = l.left.toNat - made := by rw [hz2]; exact aout
  have bits2 : s2.bits = b2 := by rw [hs2]
  have hold2 : s2.hold = hd2 := by rw [hs2]
  refine ⟨.ok (), _, after, run, log, ?_, Or.inl ⟨rfl, ?_⟩, fun _ => Short.of_bits ?_⟩
  · refine { IE with put := ⟨?_, ?_⟩, chunk := ⟨?_, ?_⟩, bits := ⟨?_, ?_⟩ }
    · show z2.next_out = advance window (n - z2.avail_out.toNat)
      rw [left2, hz2, hw]
      show Ptr.ref (BRef.blk w) (woff + (n - l.left.toNat) + made) =
        Ptr.ref (BRef.blk w) (woff + (n - (l.left.toNat - made)))
      congr 1
      omega
    · show z2.avail_out.toNat ≤ n
      rw [left2]; omega
    · show z2.avail_in.toNat ≤ log.held.length
      rw [have2]; omega
    · intro _
      obtain ⟨b, aoff, hact⟩ := I.chunkBlk hne
      have hn := I.chunk.2 hnz
      rw [enext, hact] at hn
      have hn' : Ptr.ref (BRef.blk e.ib) e.i0 =
          Ptr.ref (BRef.blk b) (aoff + (log.held.length - l.have_.toNat)) := hn
      injection hn' with h1 h2
      show z2.next_in = advance log.active (log.held.length - z2.avail_in.toNat)
      rw [have2, hz2, hact]
      show Ptr.ref (BRef.blk e.ib) (e.i0 + used) =
        Ptr.ref (BRef.blk b) (aoff + (log.held.length - (l.have_.toNat - used)))
      rw [h1]
      congr 1
      omega
    · show s2.bits.toNat ≤ 39
      rw [bits2]; omega
    · show s2.hold.toNat < 2 ^ s2.bits.toNat
      rw [bits2, hold2]; exact hhd2
  · obtain ⟨st1, st2, g1, g2, le, lt⟩ := cons
    rw [er] at g1
    rw [estid] at g2
    have e1 : st1 = z2 := Option.some.inj (g1.symm.trans hzE)
    have e2 : st2 = s2 := Option.some.inj (g2.symm.trans hsE)
    rw [e1, e2, es0, esm0] at le lt
    have b1 : s1.bits = l.bits := by rw [hs1]
    rw [b1, zi] at le lt
    rw [backMeasure_of pr hsE, backMeasure_of pr hs, mode]
    unfold baseM
    show 4 * (s2.bits.toNat + 8 * z2.avail_in.toNat + 8 * (pr.inputBound - log.supplied.length)) +
        modeRank s2.mode < 4 * (l.bits.toNat + 8 * l.have_.toNat + 8 * (pr.inputBound - log.supplied.length)) +
        modeRank LEN
    have rLEN : modeRank LEN = 2 := by decide
    rw [rLEN]
    rcases cls with ⟨hm, -⟩ | ⟨hm, -⟩ | hm
    · have hm' : s2.mode = LEN := by rw [hs2]; show m2 = LEN; rw [hm, hs1]; exact mode
      have strict := lt (by rw [hm']; decide) (by rw [hm']; decide)
      rw [hm', rLEN]
      omega
    · have hm' : s2.mode = TYPE := by rw [hs2]; exact hm
      have rT : modeRank TYPE = 1 := by decide
      rw [hm', rT]
      omega
    · have hm' : s2.mode = BAD := by rw [hs2]; exact hm
      have rB : modeRank BAD = 0 := by decide
      rw [hm', rB]
      omega
  · show s2.bits.toNat < 8
    rw [bits2]; exact hb2

/-- The fast path of `case LEN` at a window in a heap byte block. -/
theorem lenFast_of_blk (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 : Heap) {w woff : Nat} (hw : window = .ref (.blk w) woff) :
    LenFast c pr h0 :=
  fun _ _ _ _ I hs mode short fast => LEN_fast_p c pr I hw hs mode short fast

/-- Every history leaves a valid state over the caller's window, with `sane ≠ 0` and `wnext = 0`. -/
theorem back_reach_st_blk {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (reach : BackSafeReachable h r i window n) :
    ∃ z s, BackValid h r i z s ∧ s.window = window ∧ s.wsize.toNat = n ∧ (s.sane ≠ 0 ∧ s.wnext = 0) := by
  induction reach with
  | init hd lo hi wr nn _ run =>
    obtain ⟨z, s, valid, win, size, st⟩ := reach_init hd lo hi wr nn run
    exact ⟨z, s, valid, win, size, st⟩
  | caller _ rebuf same ro ih =>
    obtain ⟨z, s, valid, win, size, st⟩ := ih
    obtain ⟨z', valid'⟩ := reach_caller valid win size rebuf same ro
    exact ⟨z', s, valid', win, size, st⟩
  | @step h after r i window n z input inDesc output outDesc first rc protocol reach hz firstB sep inv0 fit plat
      fc run ih =>
    obtain ⟨z0, s0, valid0, win0, size0, st0⟩ := ih
    have e : z0 = z := Option.some.inj (valid0.1.symm.trans hz)
    subst e
    obtain ⟨w, woff, hw⟩ := back_reach_window reach
    obtain ⟨z', s', log, valid', win', ws', st', -⟩ :=
      back_call_partial protocol valid0 win0 size0 hw firstB sep inv0 fit plat fc st0
        (lenFast_of_blk (callCtx r i input inDesc output outDesc) protocol h hw) run
    exact ⟨z', s', valid', win', by rw [ws']; exact size0, st'⟩

/-- Every history leaves a valid state over the caller's window (clause 2 of the goal). -/
theorem back_reach_valid_blk {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (reach : BackSafeReachable h r i window n) :
    ∃ z s, BackValid h r i z s ∧ s.window = window ∧ s.wsize.toNat = n := by
  obtain ⟨z, s, valid, win, size, -⟩ := back_reach_st_blk reach
  exact ⟨z, s, valid, win, size⟩

/-- `inflateBackEnd` on every history frees the state (clause 4 of the goal). -/
theorem back_end_blk {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (reach : BackSafeReachable h r i window n) :
    ∃ after z, C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some z ∧ z.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ b = i) ∧
      LiveChange h after (fun _ => False) (fun b => b = i) := by
  obtain ⟨z, s, valid, -, -⟩ := back_reach_valid_blk reach
  obtain ⟨after, run, get, live, frame, -, -⟩ :=
    ZlibF.Spec.Public.InflateBackEndProof.back_end_public.2.2 h r i z s valid
  exact ⟨after, { z with state := none }, run, get, rfl, frame, live⟩

/-- **`Goal.inflate_back_sequence_safety`**: `inflateBack` and its call sequence are safe on every
history of the goal. -/
theorem inflate_back_sequence_safety : Goal.inflate_back_sequence_safety := by
  refine ⟨back_null, fun h r i window n reach => back_reach_valid_blk reach, ?_,
    fun h r i window n reach => back_end_blk reach⟩
  intro h r i window n z s input inDesc output outDesc protocol first reach valid firstB sep inv0 bound fit plat fc
  obtain ⟨z0, s0, valid0, win0, size0, st0⟩ := back_reach_st_blk reach
  have es : s0 = s := Option.some.inj (valid0.2.1.symm.trans valid.2.1)
  subst es
  obtain ⟨w, woff, hw⟩ := back_reach_window reach
  obtain ⟨rc, after, run, z', s', log, valid', win', ws', -, inv', codes, frame, live⟩ :=
    back_call_total protocol valid win0 size0 hw firstB sep inv0 fit plat fc st0
      (lenFast_of_blk (callCtx r i input inDesc output outDesc) protocol h hw) bound
  exact ⟨rc, after, z', s', log, run, valid', win', ws', inv', codes, frame, live⟩

end Zlib.Infback.Safety
