import ZlibF.Proof.«infback.c.safety-sym»

/-!
# infback.c: the copy of a match inside the window

`case LEN` copies a match byte by byte, `*put++ = *from++`, with `from` and `put` both in the
window (the source may be ahead of `put`: the part of the window not yet rewritten in this cycle,
or behind it, overlapping the bytes being written). `mc_run`: `k ≥ 1` bytes inside the window's
block; only `[p, p + k)` changes.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- `*put++ = *from++;` -/
def mcBody : X Unit := do
  let l ← get
  let b ← load8 l.from_
  store8 l.put b
  let p ← l.put.add 1
  let f ← l.from_.add 1
  set { l with put := p, from_ := f }

/-- `while (--copy)` -/
def mcCond : X Bool := do
  let l ← get
  let n := l.copy - 1
  set { l with copy := n }
  return n != 0

/-- The match copy after the source pointer is chosen. -/
def lcTail (c : BCtx) (s : InflateState) (l : IL) (from_ : BPtr) (copy : UInt32) : X Unit := do
  let copy := if copy > s.length then s.length else copy
  wrS c.st fun s => { s with length := s.length - copy }
  set { l with copy := copy, from_ := from_, left := l.left - copy }
  xdoWhile mcBody mcCond

/-- One trip of the match copy loop. -/
def lcBody (c : BCtx) : X Unit := do
  ROOM c
  let s ← ldInflateState c.st
  let l ← get
  let copy := s.wsize - s.offset
  let (from_, copy) ← if copy < l.left then do
      pure (← l.put.add (copy.toNat : Int), l.left - copy)
    else do
      pure (← l.put.add (-(s.offset.toNat : Int)), l.left)
  lcTail c s l from_ copy

/-- `while (state->length != 0)` -/
def lcCond (c : BCtx) : X Bool := do return (← rdS c.st (·.length)) != 0

theorem lenCopy_eq (c : BCtx) : lenCopy c = (do
    let s ← ldInflateState c.st
    let l ← get
    if s.offset > s.wsize - (if s.whave < s.wsize then l.left else 0) then
      badMode c "invalid distance too far back"
      return
    xdoWhile (lcBody c) (lcCond c)) := rfl

theorem winHeap_winHeap (h : Heap) (w : Nat) (a1 a2 : Array UInt8) :
    winHeap (winHeap h w a1) w a2 = winHeap h w a2 := by
  simp [winHeap, upd_upd]

theorem winHeap_self {h : Heap} {w : Nat} {a : Array UInt8} (get : h.bytes w = some a) : winHeap h w a = h := by
  simp only [winHeap, upd_self h.bytes w a get]

/-- `*put++ = *from++;` inside the window's block. -/
theorem mcBody_run {H : Heap} {w : Nat} {a : Array UInt8} (get : H.bytes w = some a) (ro : H.ro w = false)
    {l : IL} {f p : Nat} (hf : l.from_ = .ref (.blk w) f) (hp : l.put = .ref (.blk w) p)
    (fl : f + 1 ≤ a.size) (pl : p + 1 ≤ a.size) :
    runX mcBody l H = .ok ((.ok (), { l with put := .ref (.blk w) (p + 1), from_ := .ref (.blk w) (f + 1) }),
      winHeap H w (a.set! p a[f])) := by
  have ld := load8_ok (h := H) get (show f < a.size by omega)
  have st := Ptr.store_ok (r := BRef.blk w) (off := p) (v := a[f]) (show (Space.get H (BRef.blk w) :
    Option (Array UInt8)) = some a from get) (show Space.ro H (BRef.blk w) = false from ro) (by omega)
  have getW : (Space.get (winHeap H w (a.set! p a[f])) (BRef.blk w) : Option (Array UInt8)) = some (a.set! p a[f]) := by
    simp [Space.get, winHeap]
  have szW : (a.set! p a[f]).size = a.size := by simp
  have addP : OkOn (winHeap H w (a.set! p a[f])) (Ptr.add (Ptr.ref (BRef.blk w) p) 1) (Ptr.ref (BRef.blk w) (p + 1)) :=
    Ptr.add_nat_ok (n := 1) (off := p) getW (by rw [szW]; omega)
  have addF : OkOn (winHeap H w (a.set! p a[f])) (Ptr.add (Ptr.ref (BRef.blk w) f) 1) (Ptr.ref (BRef.blk w) (f + 1)) :=
    Ptr.add_nat_ok (n := 1) (off := f) getW (by rw [szW]; omega)
  unfold mcBody
  simp only [runX_bind, runX_get, hf, hp, runX_lift_ok ld]
  rw [runX_lift_ok (show store8 (.ref (.blk w) p) a[f] H = .ok ((), winHeap H w (a.set! p a[f])) from st)]
  simp only [runX_lift_ok addP, runX_lift_ok addF, runX_set]

/-- The registers of the byte copy after `t` bytes. -/
def mcRegs (l : IL) (w p f t : Nat) (c : UInt32) : IL :=
  { l with put := .ref (.blk w) (p + t), from_ := .ref (.blk w) (f + t), copy := c }

/-- **The byte copy of a match**: `k ≥ 1` bytes from `from` to `put`, both in the window's
block; only `[p, p + k)` changes. -/
theorem mc_run {h : Heap} {w : Nat} {a : Array UInt8} (get : h.bytes w = some a) (ro : h.ro w = false)
    {l : IL} {f p k : Nat} (hk : 1 ≤ k) (hf : l.from_ = .ref (.blk w) f) (hp : l.put = .ref (.blk w) p)
    (hc : l.copy.toNat = k) (fr : f + k ≤ a.size) (pr : p + k ≤ a.size) :
    ∃ a', runX (xdoWhile mcBody mcCond) l h = .ok ((.ok (), mcRegs l w p f k 0), winHeap h w a') ∧
      a'.size = a.size ∧ ∀ j, (j < p ∨ p + k ≤ j) → a'[j]? = a[j]? := by
  have run0 := mcBody_run get ro hf hp (by omega) (by omega)
  have key := xwhileBrk_wf (cond := mcCond) (body := (do mcBody; pure false : X Bool))
    (fun l1 h1 => ∃ t a1 c1, 1 ≤ t ∧ t ≤ k ∧ l1 = mcRegs l w p f t c1 ∧
      c1.toNat = k - t + 1 ∧ h1 = winHeap h w a1 ∧ a1.size = a.size ∧ ∀ j, (j < p ∨ p + t ≤ j) → a1[j]? = a[j]?)
    (fun res l1 h1 => res = .ok () ∧ ∃ a1, l1 = mcRegs l w p f k 0 ∧
      h1 = winHeap h w a1 ∧ a1.size = a.size ∧ ∀ j, (j < p ∨ p + k ≤ j) → a1[j]? = a[j]?)
    (fun l1 _ => l1.copy.toNat)
    (fun l1 h1 hI => by
      obtain ⟨t, a1, c1, t1, tk, rfl, hc1, rfl, sz1, fr1⟩ := hI
      have hcond : runX mcCond (mcRegs l w p f t c1) (winHeap h w a1) =
          .ok ((.ok ((c1 - 1) != 0), mcRegs l w p f t (c1 - 1)), winHeap h w a1) := by
        unfold mcCond; simp only [runX_bind, runX_get, runX_set]; rfl
      have sub : (c1 - 1).toNat = k - t := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      refine ⟨_, _, _, hcond, fun hT => ?_, fun hF => ?_⟩
      · have ne : (c1 - 1) ≠ 0 := by simpa using hT
        have tk' : t < k := by
          have : (c1 - 1).toNat ≠ 0 := fun e => ne (UInt32.toNat_inj.mp (by rw [e]; rfl))
          omega
        have getW : (winHeap h w a1).bytes w = some a1 := by simp [winHeap]
        have roW : (winHeap h w a1).ro w = false := ro
        have run1 := mcBody_run getW roW (l := mcRegs l w p f t (c1 - 1)) rfl rfl (by omega) (by omega)
        refine ⟨.ok false, _, _, by rw [runX_bind, run1]; rfl, ⟨t + 1, a1.set! (p + t) a1[f + t], c1 - 1, by omega,
          by omega, rfl, by omega, winHeap_winHeap _ _ _ _, by simp [sz1], fun j hj => ?_⟩, ?_⟩
        · rw [Zlib.Inflate.Proofs.array_set!_getElem?_ne _ (by omega)]
          exact fr1 j (by omega)
        · show (c1 - 1).toNat < c1.toNat; omega
      · have z : (c1 - 1) = 0 := by simpa using hF
        have tk' : t = k := by
          have : (c1 - 1).toNat = 0 := by rw [z]; rfl
          omega
        subst tk'
        refine ⟨rfl, a1, ?_, rfl, sz1, fr1⟩
        rw [z])
    (l := mcRegs l w p f 1 l.copy) (h := winHeap h w (a.set! p a[f]))
    ⟨1, a.set! p a[f], l.copy, Nat.le_refl _, hk, rfl, by omega, rfl, by simp, fun j hj => by
      rw [Zlib.Inflate.Proofs.array_set!_getElem?_ne _ (by omega)]⟩
    (by show l.copy.toNat + 1 < fuel; have := UInt32.toNat_lt l.copy; unfold fuel; omega)
  obtain ⟨res, l', h', run, rfl, a', rfl, rfl, sz', fr'⟩ := key
  refine ⟨a', ?_, sz', fr'⟩
  unfold xdoWhile
  rw [runX_bind, run0]
  unfold xwhile
  exact run

/-- **Moving the output registers on by `k` bytes keeps `PInv`.** -/
theorem PInv.produce {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {l' : IL} (k : Nat)
    (left' : l'.left.toNat + k = l.left.toNat) (put' : l'.put = advance l.put k)
    (have_ : l'.have_ = l.have_) (next : l'.next = l.next) (bits : l'.bits = l.bits) (hold : l'.hold = l.hold) :
    PInv c pr h0 h l' log :=
  { I with
    put := by
      obtain ⟨p, le⟩ := I.put
      refine ⟨?_, by omega⟩
      rw [put', p, advance_advance]
      congr 1
      omega
    chunk := by rw [have_, next]; exact I.chunk
    bits := by rw [bits, hold]; exact I.bits }

set_option maxRecDepth 100000 in
/-- **The match copy after the source pointer, on the invariant**: `min(copy, length) ≥ 1` bytes
from `from` (inside the window) to `put`; `length` falls. -/
theorem lcTail_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    {f : Nat} {from_ : BPtr} (hfrom : from_ = .ref (.blk w) f) {cv1 : UInt32}
    (fk : f + cv1.toNat ≤ woff + n) (pos : 1 ≤ cv1.toNat) (cvleft : cv1.toNat ≤ l.left.toNat)
    (len1 : 1 ≤ s.length.toNat) :
    ∃ l' h', runX (lcTail c s l from_ cv1) l h = .ok ((.ok (), l'), h') ∧ PInv c pr h0 h' l' log ∧
      baseM pr l' log = baseM pr l log ∧ l'.bits = l.bits ∧
      ∃ s', h'.istates i = some s' ∧ s'.mode = s.mode ∧ s'.offset = s.offset ∧ s'.length.toNat < s.length.toNat := by
  obtain ⟨z, s0, valid, win, sz⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  have wf := valid.2.2.2.2.2.1
  have wr := valid.2.2.2.2.2.2.2.2.2.2.1
  rw [win, sz, hw] at wr
  obtain ⟨a, get, ro0, room⟩ : ∃ a, h.bytes w = some a ∧ h.ro w = false ∧ woff + n ≤ a.size := by
    rcases wr with ⟨null, -⟩ | ⟨ref, off, a0, ptr, g, ro, rm⟩
    · cases null
    · injection ptr with e1 e2; subst e1 e2; exact ⟨a0, g, ro, rm⟩
  obtain ⟨pput, lle⟩ := I.put
  have hput : l.put = .ref (.blk w) (woff + (n - l.left.toNat)) := by rw [pput, hw]; rfl
  obtain ⟨k, hk⟩ : ∃ k : UInt32, k = (if cv1 > s0.length then s0.length else cv1) := ⟨_, rfl⟩
  have kv : k.toNat = min cv1.toNat s0.length.toNat := by
    rw [hk]; split
    · next g => have := UInt32.lt_iff_toNat_lt.mp g; omega
    · next g =>
      have : ¬ s0.length.toNat < cv1.toNat := fun x => g (UInt32.lt_iff_toNat_lt.mpr x)
      omega
  let S3 : InflateState := { s0 with length := s0.length - k }
  have hs3 : (setI h i S3).istates i = some S3 := by simp [setI]
  have wrs : wrS c.st (fun s => { s with length := s.length - k }) h = .ok ((), setI h i S3) := wrS_ok I.cst hs _
  let l3 : IL := { l with copy := k, from_ := from_, left := l.left - k }
  have get3 : (setI h i S3).bytes w = some a := get
  have ro3 : (setI h i S3).ro w = false := ro0
  obtain ⟨a', run, size', frame'⟩ := mc_run get3 ro3 (l := l3) (f := f) (p := woff + (n - l.left.toNat))
    (k := k.toNat) (by omega) hfrom hput rfl (by omega) (by omega)
  have I3 := I.setState hs S3 rfl rfl rfl (wf_with wf _ rfl rfl rfl) (I.mode s0 hs)
  have I4 := I3.storeWindow hw get3 size' (fun j out => frame' j (by omega))
  have subL : (l.left - k).toNat = l.left.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have I5 := I4.produce (l' := mcRegs l3 w (woff + (n - l.left.toNat)) f k.toNat 0) k.toNat
    (by show (l.left - k).toNat + k.toNat = _; omega) (by rw [hput]; rfl) rfl rfl rfl rfl
  have subS : (s0.length - k).toNat = s0.length.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  refine ⟨_, _, ?_, I5, rfl, rfl, S3, by simp [winHeap, setI], rfl, rfl, by show (s0.length - k).toNat < _; omega⟩
  unfold lcTail
  rw [← hk]
  simp only [runX_bind, runX_lift_ok wrs, runX_set]
  exact run

set_option maxRecDepth 100000 in
/-- **One trip of the match copy loop on the invariant**: `ROOM()`, then the source inside the
window: ahead of `put` (`copy < left`: the part not yet rewritten in this cycle) or `offset`
behind it. Both ranges lie in the window slice when `offset ≤ wsize`. -/
theorem lcBody_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (off : s.offset.toNat ≤ s.wsize.toNat) (len1 : 1 ≤ s.length.toNat) :
    ∃ res l' h' log', runX (lcBody c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → baseM pr l' log' ≤ baseM pr l log ∧ l'.bits = l.bits ∧
        ∃ s', h'.istates i = some s' ∧ s'.mode = s.mode ∧ s'.offset = s.offset ∧
          s'.length.toNat < s.length.toNat) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  obtain ⟨res2, l2, h2, log2, run2, I2, ok2, err2, have2, next2, bits2, hold2, -, -, st2, meas2⟩ := ROOM_p c pr I
  have b2 := baseM_le meas2
  cases res2 with
  | error e =>
    obtain ⟨rfl, ret⟩ := err2 e rfl
    refine ⟨.error Ex.leave, l2, h2, log2, ?_, I2, fun x => (nomatch x), fun e x => ?_⟩
    · unfold lcBody; rw [runX_bind, run2]
    · injection x with x; subst x; exact ⟨rfl, ret⟩
  | ok u =>
    cases u
    have left2 := ok2 rfl
    obtain ⟨wv, hs2⟩ := st2 s hs
    obtain ⟨z2, S, valid2, win2, sz2⟩ := I2.valid
    have eS : S = { s with whave := wv } := Option.some.inj (valid2.2.1.symm.trans hs2)
    subst eS
    have nEq : n = s.wsize.toNat := sz2.symm
    have wr := valid2.2.2.2.2.2.2.2.2.2.2.1
    rw [win2, sz2, hw] at wr
    obtain ⟨a2, get2, room2⟩ : ∃ a, h2.bytes w = some a ∧ woff + n ≤ a.size := by
      rcases wr with ⟨null, -⟩ | ⟨ref, o, a0, ptr, g, -, rm⟩
      · cases null
      · injection ptr with e1 e2; subst e1 e2; exact ⟨a0, g, rm⟩
    obtain ⟨pput, lle⟩ := I2.put
    have hput : l2.put = .ref (.blk w) (woff + (n - l2.left.toNat)) := by rw [pput, hw]; rfl
    have lpos : 1 ≤ l2.left.toNat := Nat.pos_of_ne_zero (fun e => left2 (UInt32.toNat_inj.mp (by rw [e]; rfl)))
    have ld : ldInflateState c.st h2 = .ok ({ s with whave := wv }, h2) := by
      rw [I2.cst]; exact ldInflateState_tab hs2
    have cp0 : (s.wsize - s.offset).toNat = n - s.offset.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr off), nEq]
    have getP : (Space.get h2 (BRef.blk w) : Option (Array UInt8)) = some a2 := get2
    by_cases A : s.wsize - s.offset < l2.left
    · have A' : n - s.offset.toNat < l2.left.toNat := by rw [← cp0]; exact UInt32.lt_iff_toNat_lt.mp A
      have add : OkOn h2 (Ptr.add l2.put ((s.wsize - s.offset).toNat : Int))
          (Ptr.ref (BRef.blk w) (woff + (n - l2.left.toNat) + (s.wsize - s.offset).toNat)) := by
        rw [hput]; exact Ptr.add_nat_ok getP (by omega)
      have cv : (l2.left - (s.wsize - s.offset)).toNat = l2.left.toNat - (n - s.offset.toNat) := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), cp0]
      obtain ⟨l3, h3, run3, I3, b3, bits3, s3, hs3, m3, o3, lt3⟩ :=
        lcTail_p c pr I2 hw hs2 (f := woff + (n - l2.left.toNat) + (s.wsize - s.offset).toNat) rfl
          (cv1 := l2.left - (s.wsize - s.offset)) (by rw [cv]; omega) (by rw [cv]; omega) (by rw [cv]; omega) len1
      refine ⟨.ok (), l3, h3, log2, ?_, I3, fun _ => ⟨by omega, bits3.trans bits2, s3, hs3, m3, o3, lt3⟩,
        fun e x => (nomatch x)⟩
      unfold lcBody
      rw [runX_bind, run2]
      simp only [runX_bind, runX_lift_ok ld, runX_get, A, ↓reduceIte, runX_lift_ok add, runX_pure]
      exact run3
    · have A' : l2.left.toNat ≤ n - s.offset.toNat := by
        have hn : ¬ (s.wsize - s.offset).toNat < l2.left.toNat := fun x => A (UInt32.lt_iff_toNat_lt.mpr x)
        rw [cp0] at hn
        omega
      have add : OkOn h2 (Ptr.add l2.put (-(s.offset.toNat : Int)))
          (Ptr.ref (BRef.blk w) ((((woff + (n - l2.left.toNat) : Nat) : Int) + -(s.offset.toNat : Int)).toNat)) := by
        rw [hput]; exact Ptr.add_ok getP (by omega) (by omega)
      have fv : ((((woff + (n - l2.left.toNat) : Nat) : Int) + -(s.offset.toNat : Int)).toNat) =
          woff + (n - l2.left.toNat) - s.offset.toNat := by omega
      obtain ⟨l3, h3, run3, I3, b3, bits3, s3, hs3, m3, o3, lt3⟩ :=
        lcTail_p c pr I2 hw hs2 (f := woff + (n - l2.left.toNat) - s.offset.toNat) (by rw [← fv])
          (cv1 := l2.left) (by omega) lpos (Nat.le_refl _) len1
      refine ⟨.ok (), l3, h3, log2, ?_, I3, fun _ => ⟨by omega, bits3.trans bits2, s3, hs3, m3, o3, lt3⟩,
        fun e x => (nomatch x)⟩
      unfold lcBody
      rw [runX_bind, run2]
      simp only [runX_bind, runX_lift_ok ld, runX_get, A, ↓reduceIte, runX_lift_ok add, runX_pure]
      exact run3

theorem lit_too_far : "invalid distance too far back" ∈ strTable := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The match copy of `case LEN` on the invariant**: the distance check (`BAD`), then the copy
through the window until `length` is 0, or `Z_BUF_ERROR` when `out` refuses. The bits held do
not change; the input part of the measure does not grow. -/
theorem lenCopy_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (mode : s.mode = LEN) (len1 : 1 ≤ s.length.toNat) (short : l.bits.toNat < 8) {B : Nat}
    (lt : baseM pr l log + 2 < B) :
    ∃ res l' h', runX (lenCopy c) l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h' := by
  obtain ⟨z, s0, valid, win, sz⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  have ld : ldInflateState c.st h = .ok (s0, h) := by rw [I.cst]; exact ldInflateState_tab hs
  have lle := I.put.2
  by_cases far : s0.offset > s0.wsize - (if s0.whave < s0.wsize then l.left else 0)
  · obtain ⟨hb, runB, T⟩ := TRound.bad I "invalid distance too far back" lit_too_far (B := B) (by omega)
    refine ⟨.ok (), l, hb, ?_, T⟩
    rw [lenCopy_eq]
    simp only [runX_bind, runX_lift_ok ld, runX_get, far, ↓reduceIte, runX_lift_ok runB]
    rfl
  · have off : s0.offset.toNat ≤ n := by
      have hn : ¬ (s0.wsize - (if s0.whave < s0.wsize then l.left else 0)).toNat < s0.offset.toNat :=
        fun x => far (UInt32.lt_iff_toNat_lt.mpr x)
      split at hn
      · rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))] at hn; omega
      · simp at hn; omega
    have pre : runX (lenCopy c) l h = runX (xdoWhile (lcBody c) (lcCond c)) l h := by
      rw [lenCopy_eq]
      simp only [runX_bind, runX_lift_ok ld, runX_get, far, ↓reduceIte]
    obtain ⟨res1, l1, h1, log1, run1, I1, ok1, err1⟩ := lcBody_p c pr I hw hs (by omega) len1
    cases res1 with
    | error e =>
      obtain ⟨rfl, ret⟩ := err1 e rfl
      refine ⟨.error Ex.leave, l1, h1, ?_, TRound.leave I1 B ret⟩
      rw [pre]; unfold xdoWhile; rw [runX_bind, run1]
    | ok u =>
      cases u
      obtain ⟨b1, bits1, s1, hs1, m1, o1, -⟩ := ok1 rfl
      have key := xwhileBrk_wf (cond := lcCond c) (body := (do lcBody c; pure false : X Bool))
        (fun l2 h2 => ∃ log2 s2, PInv c pr h0 h2 l2 log2 ∧ h2.istates i = some s2 ∧ s2.mode = LEN ∧
          s2.offset.toNat ≤ n ∧ baseM pr l2 log2 ≤ baseM pr l log ∧ l2.bits = l.bits)
        (fun res l2 h2 => ∃ log2, PInv c pr h0 h2 l2 log2 ∧
          (res = .ok () → baseM pr l2 log2 ≤ baseM pr l log ∧ l2.bits = l.bits ∧
            ∃ s2, h2.istates i = some s2 ∧ s2.mode = LEN) ∧
          (∀ e, res = .error e → e = Ex.leave ∧ l2.ret = Z_BUF_ERROR))
        (fun _ h2 => stLen i h2)
        (fun l2 h2 hI => by
          obtain ⟨log2, s2, I2, hs2, m2, o2, b2, bb2⟩ := hI
          obtain ⟨z2, s2', valid2, -, sz2⟩ := I2.valid
          have e2 : s2' = s2 := Option.some.inj (valid2.2.1.symm.trans hs2)
          subst e2
          have hcond : runX (lcCond c) l2 h2 = .ok ((.ok (s2'.length != 0), l2), h2) := by
            unfold lcCond; rw [runX_bind, runX_lift_ok (rdS_ok I2.cst hs2 _)]; rfl
          refine ⟨l2, h2, _, hcond, fun hT => ?_, fun hF => ?_⟩
          · have ne : s2'.length ≠ 0 := by simpa using hT
            have pos : 1 ≤ s2'.length.toNat :=
              Nat.pos_of_ne_zero (fun e => ne (UInt32.toNat_inj.mp (by rw [e]; rfl)))
            obtain ⟨res3, l3, h3, log3, run3, I3, ok3, err3⟩ := lcBody_p c pr I2 hw hs2 (by omega) pos
            cases res3 with
            | ok u =>
              cases u
              obtain ⟨b3, bits3, s3, hs3, m3, o3, lt3⟩ := ok3 rfl
              refine ⟨.ok false, l3, h3, by rw [runX_bind, run3]; rfl,
                ⟨log3, s3, I3, hs3, by rw [m3, m2], by rw [o3]; exact o2, by omega, bits3.trans bb2⟩, ?_⟩
              show stLen i h3 < stLen i h2
              rw [stLen_of hs3, stLen_of hs2]; exact lt3
            | error e =>
              obtain ⟨rfl, ret⟩ := err3 e rfl
              exact ⟨.error Ex.leave, l3, h3, by rw [runX_bind, run3], log3, I3, fun x => (nomatch x),
                fun e x => by injection x with x; subst x; exact ⟨rfl, ret⟩⟩
          · exact ⟨log2, I2, fun _ => ⟨b2, bb2, s2', hs2, m2⟩, fun e x => (nomatch x)⟩)
        (l := l1) (h := h1) ⟨log1, s1, I1, hs1, by rw [m1, mode], by rw [o1]; exact off, b1, bits1⟩
        (by obtain ⟨-, s1', v1, -, -⟩ := I1.valid
            rw [stLen_of hs1]; have := UInt32.toNat_lt s1.length; unfold fuel; omega)
      obtain ⟨res, l', h', run, log', I', okc, errc⟩ := key
      have runAll : runX (lenCopy c) l h = .ok ((res, l'), h') := by
        rw [pre]; unfold xdoWhile; rw [runX_bind, run1]; unfold xwhile; exact run
      cases res with
      | error e =>
        obtain ⟨rfl, ret⟩ := errc e rfl
        exact ⟨.error Ex.leave, l', h', runAll, TRound.leave I' B ret⟩
      | ok u =>
        cases u
        obtain ⟨b', bits', s', hs', m'⟩ := okc rfl
        refine ⟨.ok (), l', h', runAll, log', I', Or.inl ⟨rfl, ?_⟩, fun _ => Short.of_bits (by rw [bits']; exact short)⟩
        rw [backMeasure_of pr hs', m', show modeRank LEN = 2 by decide]
        omega

end Zlib.Infback.Safety
