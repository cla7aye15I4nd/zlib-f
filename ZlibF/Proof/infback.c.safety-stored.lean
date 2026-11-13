import ZlibF.Proof.«infback.c.safety-window»
import ZlibF.Proof.«infback.c.stored»
import ZlibF.Proof.«inflate.c.gzip-header-modes»

/-!
# infback.c: `case STORED` on the loop invariant

`storedTail_p` is one copy of `min(length, have, left) ≥ 1` bytes from the input chunk into the
window. The chunk may lie in the window's block (it is only `Separate` from the window slice) or
in read-only memory; `memcpy` is checked with the general rule. `storedBody_p` is one trip of the
copy loop (`PULL()`, `ROOM()`, the copy), `storedLoop_p` the whole loop, measured by the state's
`length`. `STORED_p` is `case STORED`: the measure falls because the mode goes from `STORED`
(rank 2) to `TYPE` (rank 1) or `BAD` (rank 0), and no step adds input bits.

The window is a slice of a caller's byte block (`window = .ref (.blk w) woff`), the premise of
the public goal.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

theorem advance_advance (p : BPtr) (a b : Nat) : advance (advance p a) b = advance p (a + b) := by
  cases p <;> simp [advance, Nat.add_assoc]

/-- The input part of the measure: four times the input bits still readable. -/
def baseM {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (l : IL) (log : BackLog) : Nat :=
  4 * (l.bits.toNat + 8 * l.have_.toNat + 8 * (pr.inputBound - log.supplied.length))

theorem rank_getD_le (h : Heap) (i : Nat) : ((h.istates i).map (fun s => modeRank s.mode)).getD 0 ≤ 2 := by
  cases h.istates i with
  | none => simp
  | some s => simpa using modeRank_le s.mode

/-- The input part does not grow when the measure does not: the rank is below 4. -/
theorem baseM_le {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h h' : Heap} {l l' : IL} {log log' : BackLog} (le : backMeasure pr h' l' log' ≤ backMeasure pr h l log) :
    baseM pr l' log' ≤ baseM pr l log := by
  have r1 := rank_getD_le h i
  have r2 := rank_getD_le h' i
  unfold backMeasure at le
  unfold baseM
  omega

/-- **Moving the input and output registers on by `k` bytes keeps `PInv`.** -/
theorem PInv.consume {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {l' : IL} (k : Nat)
    (have' : l'.have_.toNat + k = l.have_.toNat) (left' : l'.left.toNat + k = l.left.toNat)
    (next' : l'.next = advance l.next k) (put' : l'.put = advance l.put k)
    (bits : l'.bits = l.bits) (hold : l'.hold = l.hold) : PInv c pr h0 h l' log :=
  { I with
    put := by
      obtain ⟨p, le⟩ := I.put
      refine ⟨?_, by omega⟩
      rw [put', p, advance_advance]
      congr 1
      omega
    chunk := by
      obtain ⟨le, nx⟩ := I.chunk
      refine ⟨by omega, fun ne => ?_⟩
      have p1 : l'.have_.toNat ≠ 0 := fun e => ne (UInt32.toNat_inj.mp (by rw [e]; rfl))
      have ne0 : l.have_ ≠ 0 := fun e => by
        have z : l.have_.toNat = 0 := by rw [e]; rfl
        omega
      rw [next', nx ne0, advance_advance]
      congr 1
      omega
    bits := by rw [bits, hold]; exact I.bits }

/-- The registers after a copy of `k` bytes. -/
def copyRegs (l : IL) (k : UInt32) (nx pt : BPtr) : IL :=
  { l with copy := k, have_ := l.have_ - k, next := nx, left := l.left - k, put := pt }

/-- The copy after `ROOM()`, given the runs of its memory operations. -/
theorem storedTail_gen (c : BCtx) {l : IL} {h h1 h2 : Heap} {nx pt : BPtr} (k : UInt32)
    (hk : clampCopy l.copy l.have_ l.left = k)
    (mc : memcpyB l.put l.next k.toNat h = .ok ((), h1))
    (a1 : OkOn h1 (l.next.add (k.toNat : Int)) nx) (a2 : OkOn h1 (l.put.add (k.toNat : Int)) pt)
    (wr : wrS c.st (fun s => { s with length := s.length - k }) h1 = .ok ((), h2)) :
    runX (storedTail c) l h = .ok ((.ok (), copyRegs l k nx pt), h2) := by
  subst hk
  unfold copyRegs
  obtain ⟨m, hm⟩ : ∃ m, m = clampCopy l.copy l.have_ l.left := ⟨_, rfl⟩
  rw [← hm] at mc a1 a2 wr ⊢
  unfold storedTail
  rw [runX_bind, runX_get]
  by_cases e1 : l.copy > l.have_
  · by_cases e2 : l.have_ > l.left
    · have hv : m = l.left := by rw [hm]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok mc, runX_lift_ok a1, runX_lift_ok a2, runX_set,
        runX_lift_ok wr]
    · have hv : m = l.have_ := by rw [hm]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok mc, runX_lift_ok a1, runX_lift_ok a2, runX_set,
        runX_lift_ok wr]
  · by_cases e2 : l.copy > l.left
    · have hv : m = l.left := by rw [hm]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok mc, runX_lift_ok a1, runX_lift_ok a2, runX_set,
        runX_lift_ok wr]
    · have hv : m = l.copy := by rw [hm]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok mc, runX_lift_ok a1, runX_lift_ok a2, runX_set,
        runX_lift_ok wr]

/-- **One copy of a stored block on the invariant.** With input, room and `copy ≠ 0`, at least one
byte moves from the chunk into the window slice; the chunk is outside the slice, so `memcpy` sees
no overlap. The state's `length` falls by the bytes copied. -/
theorem storedTail_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s0 : InflateState} (hs0 : h.istates i = some s0)
    (hcl : l.copy = s0.length) (hhave : l.have_ ≠ 0) (hleft : l.left ≠ 0) (hcopy : l.copy ≠ 0) :
    ∃ l' h', runX (storedTail c) l h = .ok ((.ok (), l'), h') ∧ PInv c pr h0 h' l' log ∧
      l'.have_.toNat < l.have_.toNat ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧
      ∃ s', h'.istates i = some s' ∧ s'.length.toNat < s0.length.toNat := by
  obtain ⟨z, s, valid, win, sz⟩ := I.valid
  have hs := valid.2.1
  have e0 : s = s0 := Option.some.inj (hs.symm.trans hs0)
  subst e0
  have wf := valid.2.2.2.2.2.1
  have wr := valid.2.2.2.2.2.2.2.2.2.2.1
  rw [win, sz, hw] at wr
  obtain ⟨a, get, ro0, room⟩ : ∃ a, h.bytes w = some a ∧ h.ro w = false ∧ woff + n ≤ a.size := by
    rcases wr with ⟨null, -⟩ | ⟨ref, off, a0, ptr, g, ro, rm⟩
    · cases null
    · injection ptr with e1 e2; subst e1 e2; exact ⟨a0, g, ro, rm⟩
  obtain ⟨hle, hnext⟩ := I.chunk
  obtain ⟨pput, lle⟩ := I.put
  have hv : 0 < l.have_.toNat := Nat.pos_of_ne_zero (fun e => hhave (UInt32.toNat_inj.mp (by rw [e]; rfl)))
  have hlf : 0 < l.left.toNat := Nat.pos_of_ne_zero (fun e => hleft (UInt32.toNat_inj.mp (by rw [e]; rfl)))
  have heldNe : log.held ≠ [] := fun e => by rw [e] at hle; simp at hle; omega
  obtain ⟨bytes, sep, -⟩ := I.held heldNe
  obtain ⟨ref, off, sa, pa, gs, rms⟩ : ∃ ref off sa, log.active = .ref ref off ∧
      (Space.get h ref : Option (Array UInt8)) = some sa ∧ off + log.held.length ≤ sa.size := by
    rcases bytes with ⟨_, len0, _⟩ | ⟨ref, off, sa, pa, gs, rms, -⟩
    · exact absurd (List.eq_nil_of_length_eq_zero len0) heldNe
    · exact ⟨ref, off, sa, pa, gs, rms⟩
  obtain ⟨k, hk⟩ : ∃ k, clampCopy l.copy l.have_ l.left = k := ⟨_, rfl⟩
  obtain ⟨k1, k2, k3⟩ := clampCopy_le l.copy l.have_ l.left
  have kne := clampCopy_pos _ _ _ hcopy hhave hleft
  rw [hk] at k1 k2 k3 kne
  have kpos : 0 < k.toNat := Nat.pos_of_ne_zero (fun e => kne (UInt32.toNat_inj.mp (by rw [e]; rfl)))
  have hput : l.put = .ref (.blk w) (woff + (n - l.left.toNat)) := by rw [pput, hw]; rfl
  have hnx : l.next = .ref ref (off + (log.held.length - l.have_.toNat)) := by rw [hnext hhave, pa]; rfl
  have dis : BRef.blk w ≠ ref ∨ woff + (n - l.left.toNat) + k.toNat ≤ off + (log.held.length - l.have_.toNat) ∨
      off + (log.held.length - l.have_.toNat) + k.toNat ≤ woff + (n - l.left.toNat) := by
    rw [pa, hw] at sep
    rcases sep with z0 | z0 | sep
    · exact absurd (List.eq_nil_of_length_eq_zero z0) heldNe
    · exfalso; omega
    · by_cases e : ref = BRef.blk w
      · subst e
        simp only [ne_eq, not_true_eq_false, false_or] at sep
        right
        omega
      · exact Or.inl (Ne.symm e)
  let a' := copyRange a sa (woff + (n - l.left.toNat)) (off + (log.held.length - l.have_.toNat)) k.toNat
  have size' : a'.size = a.size := size_copyRange _ _ _ _ _
  have mc : memcpyB l.put l.next k.toNat h = .ok ((), winHeap h w a') := by
    rw [hput, hnx]
    exact Ptr.memcpy_ok (rd := BRef.blk w) (rs := ref)
      (show (Space.get h (BRef.blk w) : Option (Array UInt8)) = some a from get) gs
      (show Space.ro h (BRef.blk w) = false from ro0) (by omega) (by omega) dis
  obtain ⟨sa2, gs2, sz2⟩ := get_after_put (a' := a') get size' gs
  obtain ⟨wa2, gw2, wz2⟩ := get_after_put (a' := a') get size'
    (show (Space.get h (BRef.blk w) : Option (Array UInt8)) = some a from get)
  have a1 : OkOn (winHeap h w a') (l.next.add (k.toNat : Int))
      (.ref ref (off + (log.held.length - l.have_.toNat) + k.toNat)) := by
    rw [hnx]; exact Ptr.add_nat_ok gs2 (by omega)
  have a2 : OkOn (winHeap h w a') (l.put.add (k.toNat : Int))
      (.ref (.blk w) (woff + (n - l.left.toNat) + k.toNat)) := by
    rw [hput]; exact Ptr.add_nat_ok gw2 (by omega)
  have hs1 : (winHeap h w a').istates i = some s := hs
  have wrs : wrS c.st (fun s => { s with length := s.length - k }) (winHeap h w a') =
      .ok ((), setI (winHeap h w a') i { s with length := s.length - k }) := wrS_ok I.cst hs1 _
  have run := storedTail_gen c k hk mc a1 a2 wrs
  have I1 := I.storeWindow hw get size' (fun j out =>
    copyRange_getElem?_outside _ _ _ _ _ _ (by omega))
  have subH : (l.have_ - k).toNat = l.have_.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr k2)
  have subL : (l.left - k).toNat = l.left.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr k3)
  have I2 := I1.consume (l' := copyRegs l k (.ref ref (off + (log.held.length - l.have_.toNat) + k.toNat))
      (.ref (.blk w) (woff + (n - l.left.toNat) + k.toNat))) k.toNat
    (by show (l.have_ - k).toNat + k.toNat = _; omega) (by show (l.left - k).toNat + k.toNat = _; omega)
    (by rw [hnx]; rfl) (by rw [hput]; rfl) rfl rfl
  have I3 := I2.setState hs1 { s with length := s.length - k } rfl rfl rfl (wf_with wf _ rfl rfl rfl) (I.mode s hs)
  refine ⟨_, _, run, I3, by show (l.have_ - k).toNat < _; omega, rfl, rfl, { s with length := s.length - k },
    by simp [setI], ?_⟩
  have kl : k.toNat ≤ s.length.toNat := by rw [← hcl]; exact k1
  have subS : (s.length - k).toNat = s.length.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr kl)
  show (s.length - k).toNat < _
  omega

theorem length_of_map {h h' : Heap} {i : Nat} {s : InflateState} (hs : h.istates i = some s)
    (e : (h'.istates i).map (·.length) = (h.istates i).map (·.length)) :
    ∃ s', h'.istates i = some s' ∧ s'.length = s.length := by
  rw [hs] at e
  cases g : h'.istates i with
  | none => rw [g] at e; cases e
  | some s' => rw [g] at e; exact ⟨s', rfl, Option.some.inj e⟩

/-- **One trip of the copy loop of `case STORED` on the invariant.** `PULL()`, `ROOM()`, then the
copy: either a call-back ended the call (`Z_BUF_ERROR`), or the state's `length` and the input
part of the measure both fell. -/
theorem storedBody_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (hlen : s.length ≠ 0) :
    ∃ res l' h' log', runX (storedBody c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → baseM pr l' log' < baseM pr l log ∧
        ∃ s', h'.istates i = some s' ∧ s'.length.toNat < s.length.toNat) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  have hld : ldInflateState c.st h = .ok (s, h) := by rw [I.cst]; exact ldInflateState_tab hs
  have I0 : PInv c pr h0 h { l with copy := s.length } log :=
    ⟨I.cstrm, I.cst, I.valid, I.winRoot, I.put, I.chunk, I.held, I.bits, I.proto, I.frame, I.live, I.mode⟩
  obtain ⟨res1, l1, h1, log1, run1, I1, ok1, err1, copy1, len1, meas1⟩ := PULL_p c pr I0
  have pre1 : runX (storedBody c) l h = runX (PULL c >>= fun _ => ROOM c >>= fun _ => storedTail c)
      { l with copy := s.length } h := by
    unfold storedBody
    rw [runX_bind, runX_lift_ok hld]; simp only []
    rw [runX_bind, runX_modify]
  cases res1 with
  | error e =>
    obtain ⟨rfl, ret⟩ := err1 e rfl
    refine ⟨.error Ex.leave, l1, h1, log1, ?_, I1, fun x => (nomatch x), fun e x => ?_⟩
    · rw [pre1, runX_bind, run1]
    · injection x with x; subst x; exact ⟨rfl, ret⟩
  | ok u =>
    cases u
    obtain ⟨have1, -, -, -, -, -, -⟩ := ok1 rfl
    obtain ⟨res2, l2, h2, log2, run2, I2, ok2, err2, have2, -, bits2, hold2, copy2, len2, meas2⟩ := ROOM_p c pr I1
    have pre2 : runX (storedBody c) l h = runX (ROOM c >>= fun _ => storedTail c) l1 h1 := by
      rw [pre1, runX_bind, run1]
    cases res2 with
    | error e =>
      obtain ⟨rfl, ret⟩ := err2 e rfl
      refine ⟨.error Ex.leave, l2, h2, log2, ?_, I2, fun x => (nomatch x), fun e x => ?_⟩
      · rw [pre2, runX_bind, run2]
      · injection x with x; subst x; exact ⟨rfl, ret⟩
    | ok u =>
      cases u
      have left2 := ok2 rfl
      obtain ⟨s2, hs2, l2s⟩ := length_of_map hs (len2.trans (by rw [len1]))
      have cl : l2.copy = s2.length := by rw [copy2, copy1, l2s]
      obtain ⟨l3, h3, run3, I3, lt3, bits3, -, s3, hs3, slt⟩ :=
        storedTail_p c pr I2 hw hs2 cl (by rw [have2]; exact have1) left2 (by rw [cl, l2s]; exact hlen)
      have b1 := baseM_le meas1
      have b2 := baseM_le meas2
      refine ⟨.ok (), l3, h3, log2, ?_, I3, fun _ => ⟨?_, s3, hs3, by rw [← l2s]; exact slt⟩,
        fun e x => (nomatch x)⟩
      · rw [pre2, runX_bind, run2]; exact run3
      · unfold baseM at b1 b2 ⊢
        rw [bits3]
        have e1 : ({ l with copy := s.length } : IL).bits = l.bits := rfl
        have e2 : ({ l with copy := s.length } : IL).have_ = l.have_ := rfl
        rw [e1, e2] at b1
        omega

/-- **The copy loop of `case STORED` on the invariant**, measured by the state's `length`. It ends
with `length = 0` or with a call-back's `Z_BUF_ERROR`; the input part of the measure does not
grow. -/
theorem storedLoop_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) :
    ∃ res l' h' log', runX (xwhile (storedCond c) (storedBody c)) l h = .ok ((res, l'), h') ∧
      PInv c pr h0 h' l' log' ∧ (res = .ok () → baseM pr l' log' ≤ baseM pr l log) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  obtain ⟨z0, s0, valid0, -, -⟩ := I.valid
  have key := xwhileBrk_wf (cond := storedCond c) (body := (do storedBody c; pure false : X Bool))
    (fun l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧ baseM pr l1 log1 ≤ baseM pr l log)
    (fun res l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧ (res = .ok () → baseM pr l1 log1 ≤ baseM pr l log) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l1.ret = Z_BUF_ERROR))
    (fun _ h1 => stLen i h1)
    (fun l1 h1 hI => by
      obtain ⟨log1, I1, b1⟩ := hI
      obtain ⟨z1, s1, valid1, -, -⟩ := I1.valid
      have hs1 := valid1.2.1
      have hcond : runX (storedCond c) l1 h1 = .ok ((.ok (s1.length != 0), l1), h1) := by
        unfold storedCond
        rw [runX_bind, runX_lift_ok (rdS_ok I1.cst hs1 _)]; rfl
      refine ⟨l1, h1, s1.length != 0, hcond, fun hT => ?_, fun hF => ?_⟩
      · have hne : s1.length ≠ 0 := by simpa using hT
        obtain ⟨res, l2, h2, log2, run2, I2, okc, errc⟩ := storedBody_p c pr I1 hw hs1 hne
        cases res with
        | ok u =>
          cases u
          obtain ⟨lt, s2, hs2, slt⟩ := okc rfl
          refine ⟨.ok false, l2, h2, ?_, ⟨log2, I2, by omega⟩, ?_⟩
          · rw [runX_bind, run2]; rfl
          · show stLen i h2 < stLen i h1
            rw [stLen_of hs2, stLen_of hs1]; exact slt
        | error e =>
          obtain ⟨rfl, ret⟩ := errc e rfl
          refine ⟨.error Ex.leave, l2, h2, ?_, log2, I2, fun x => (nomatch x), fun e x => ?_⟩
          · rw [runX_bind, run2]
          · injection x with x; subst x; exact ⟨rfl, ret⟩
      · exact ⟨log1, I1, fun _ => b1, fun e x => (nomatch x)⟩)
    (l := l) (h := h) ⟨log, I, Nat.le_refl _⟩
    (by rw [stLen_of valid0.2.1]; have := UInt32.toNat_lt s0.length; unfold fuel; omega)
  obtain ⟨res, l', h', hr, log', I', okc, errc⟩ := key
  exact ⟨res, l', h', log', by unfold xwhile; exact hr, I', okc, errc⟩

theorem modeRank_STORED : modeRank STORED = 2 := by decide
theorem modeRank_TYPE : modeRank TYPE = 1 := by decide
theorem modeRank_BAD : modeRank BAD = 0 := by decide

theorem backMeasure_of {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h : Heap} {s : InflateState} (hs : h.istates i = some s) (l : IL) (log : BackLog) :
    backMeasure pr h l log = baseM pr l log + modeRank s.mode := by
  unfold backMeasure baseM; rw [hs]; rfl

set_option maxRecDepth 100000 in
/-- **`case STORED` on the invariant**: the lengths are checked (`BAD` on a mismatch), then the
block is copied into the window through `PULL()` and `ROOM()`; the mode becomes `TYPE`. Or a
call-back ends the call with `Z_BUF_ERROR`. -/
theorem STORED_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff)
    {s : InflateState} (hs : h.istates i = some s) (mode : s.mode = STORED) :
    ∃ res l' h', runX (back_STORED c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h' := by
  have m0 : backMeasure pr h l log = baseM pr l log + 2 := by
    rw [backMeasure_of pr hs, mode, modeRank_STORED]
  obtain ⟨B1, -, -⟩ := BYTEBITS_inv (bitInv_of I)
  have hbl : (bytebits l).bits.toNat ≤ l.bits.toNat := by
    show (l.bits - (l.bits &&& 7)).toNat ≤ _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (and7_le l))]; omega
  have Ib := I.regs (l' := bytebits l) rfl rfl rfl rfl (by have := I.bits.1; omega) B1.hold_lt
  have bb : baseM pr (bytebits l) log ≤ baseM pr l log := by
    unfold baseM
    have : (bytebits l).have_ = l.have_ := rfl
    rw [this]; omega
  obtain ⟨res0, l1, h1, log1, run1, I1, okc, errc, -, meas1⟩ := NEEDBITS_p c pr 32 (by decide) Ib
  have b1 := baseM_le meas1
  cases res0 with
  | error e =>
    obtain ⟨rfl, ret⟩ := errc e rfl
    refine ⟨.error Ex.leave, l1, h1, ?_, log1, I1, Or.inr ⟨rfl, Or.inr (Or.inr ret)⟩⟩
    rw [back_STORED_eq]
    simp only [runX_bind, BYTEBITS_run, run1]
  | ok u =>
    cases u
    obtain ⟨-, -, -, -⟩ := okc rfl
    obtain ⟨z1, s1, valid1, -, -⟩ := I1.valid
    have hs1 := valid1.2.1
    have hz1 := valid1.1
    have wf1 := valid1.2.2.2.2.2.1
    by_cases hcond : ((l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨k, hbad⟩ := badMode_run c I1.cstrm I1.cst hz1 hs1 "invalid stored block lengths"
        Zlib.Inflate.Proofs.lit_invalid_stored
      have IB := I1.putMsg hz1 (.ref (.str k) 0)
      have hsB : (r.put h1 { z1 with msg := .ref (.str k) 0 }).istates i = some s1 := by simpa using hs1
      have IC := IB.setState hsB { s1 with mode := BAD } rfl rfl rfl (wf_with wf1 _ rfl rfl rfl)
        (modeOk_of (Or.inr (Or.inr (Or.inr rfl))))
      refine ⟨.ok (), l1, setI (r.put h1 { z1 with msg := .ref (.str k) 0 }) i { s1 with mode := BAD }, ?_, log1, IC,
        Or.inl ⟨rfl, ?_⟩⟩
      · rw [back_STORED_eq]
        simp only [runX_bind, BYTEBITS_run, run1, runX_get, hcond, ↓reduceIte, runX_lift_ok hbad]
        rfl
      · rw [backMeasure_of pr (s := { s1 with mode := BAD }) (by simp [setI]), m0]
        show baseM pr l1 log1 + modeRank BAD < _
        rw [modeRank_BAD]; omega
    · have hcond' : ((l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) = false := by
        simpa using hcond
      have IL := I1.setState hs1 { s1 with length := l1.hold.toUInt32 &&& 0xffff } rfl rfl rfl
        (wf_with wf1 _ rfl rfl rfl) (I1.mode s1 hs1)
      have IL' := IL.regs (l' := { l1 with hold := 0, bits := 0 }) rfl rfl rfl rfl (by show (0 : UInt32).toNat ≤ 39; decide)
        (by show (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat; decide)
      have hwr : wrS c.st (fun s => { s with length := l1.hold.toUInt32 &&& 0xffff }) h1 =
          .ok ((), setI h1 i { s1 with length := l1.hold.toUInt32 &&& 0xffff }) := wrS_ok I1.cst hs1 _
      have pre : runX (back_STORED c) l h = runX (xwhile (storedCond c) (storedBody c) >>= fun _ => setMode c.st TYPE)
          { l1 with hold := 0, bits := 0 } (setI h1 i { s1 with length := l1.hold.toUInt32 &&& 0xffff }) := by
        rw [back_STORED_eq]
        simp only [runX_bind, BYTEBITS_run, run1, runX_get, hcond', Bool.false_eq_true, ↓reduceIte,
          runX_lift_ok hwr, runX_INITBITS]
      have b0 : baseM pr { l1 with hold := 0, bits := 0 } log1 ≤ baseM pr l1 log1 := by
        unfold baseM
        show 4 * ((0 : UInt32).toNat + 8 * l1.have_.toNat + _) ≤ _
        simp only [UInt32.toNat_zero]; omega
      obtain ⟨res3, l3, h3, log3, run3, I3, ok3, err3⟩ := storedLoop_p c pr IL' hw
      cases res3 with
      | error e =>
        obtain ⟨rfl, ret⟩ := err3 e rfl
        refine ⟨.error Ex.leave, l3, h3, ?_, log3, I3, Or.inr ⟨rfl, Or.inr (Or.inr ret)⟩⟩
        rw [pre, runX_bind, run3]
      | ok u =>
        cases u
        have b3 := ok3 rfl
        obtain ⟨z3, s3, valid3, -, -⟩ := I3.valid
        have hs3 := valid3.2.1
        have wf3 := valid3.2.2.2.2.2.1
        have I4 := I3.setState hs3 { s3 with mode := TYPE } rfl rfl rfl (wf_with wf3 _ rfl rfl rfl)
          ⟨Or.inl rfl, fun e => absurd (e : TYPE = LEN) (by show TYPE ≠ LEN; decide)⟩
        refine ⟨.ok (), l3, setI h3 i { s3 with mode := TYPE }, ?_, log3, I4, Or.inl ⟨rfl, ?_⟩⟩
        · rw [pre, runX_bind, run3]
          simp only []
          rw [runX_lift_ok (setMode_ok I3.cst hs3 TYPE)]
        · rw [backMeasure_of pr (s := { s3 with mode := TYPE }) (by simp [setI]), m0]
          show baseM pr l3 log3 + modeRank TYPE < _
          rw [modeRank_TYPE]; omega

end Zlib.Infback.Safety
