import ZlibF.Proof.«inflate.c.misc2»
import ZlibF.Runtime.Pilot

/-!
# inflate.c: the ring buffer of `updatewindow`

The lemmas `cpy_step`, `cpy_step_off`, `initWin_inv`, `uw_big_ok`, `uw_small_ok` are migrated from the pilot
(`ZlibF.Runtime.Pilot`), with the window-size condition relaxed from `8 ≤ wbits ≤ 15` to `wbits ≤ 15`.
-/

namespace Zlib.Inflate.Proofs.W
open C


/-- `if (state->wsize == 0) { wsize = 1U << wbits; wnext = 0; whave = 0; }` -/
def initWin (st : InflateState) : InflateState :=
  if st.wsize == 0 then { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } else st

/-- `if (copy >= wsize)`: copy the last `wsize` bytes before `end` into the whole window. -/
def uw_big (ist : InflateStatePtr) (st : InflateState) (e : BPtr) : M UInt32 := do
  let src ← Pilot.psub e st.wsize.toNat
  memcpyB st.window src st.wsize.toNat
  stInflateState ist { st with wnext := 0, whave := st.wsize }
  return 0

/-- `else`: copy `copy` bytes into the ring buffer, in at most two pieces. -/
def uw_small (ist : InflateStatePtr) (st : InflateState) (e : BPtr) (copy : UInt32) : M UInt32 := do
  let dist : UInt32 := if st.wsize - st.wnext > copy then copy else st.wsize - st.wnext
  let dst ← Pilot.padd st.window st.wnext.toNat
  let src ← Pilot.psub e copy.toNat
  memcpyB dst src dist.toNat
  let copy' : UInt32 := copy - dist
  if copy' != 0 then
    let src2 ← Pilot.psub e copy'.toNat
    memcpyB st.window src2 copy'.toNat
    stInflateState ist { st with wnext := copy', whave := st.wsize }
    return 0
  else
    let wn : UInt32 := st.wnext + dist
    let wn : UInt32 := if wn == st.wsize then 0 else wn
    let wh : UInt32 := if st.whave < st.wsize then st.whave + dist else st.whave
    stInflateState ist { st with wnext := wn, whave := wh }
    return 0

/-- The part of `updatewindow(strm, end, copy)` after the window has been allocated. -/
def update2 (sr : Nat) (e : BPtr) (copy : UInt32) : M UInt32 := do
  let z ← ldZStream (some (.tab sr))
  let ist ← castInflateState z.state
  let st0 ← ldInflateState ist
  let st := initWin st0
  if copy ≥ st.wsize then uw_big ist st e else uw_small ist st e copy

/-- The window invariant W of `docs/proof/inflate.md`: the window is a writable byte block of `2^wbits` bytes. -/
structure WInv (h : Heap) (st : InflateState) : Prop where
  k : st.wbits.toNat ≤ 15
  win : ∃ w a, st.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧ a.size = 2 ^ st.wbits.toNat
  ws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat
  hv : st.whave.toNat ≤ st.wsize.toNat
  wn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0)
  eq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat

theorem shl_toNat (b : UInt32) (hb : b.toNat ≤ 15) : ((1 : UInt32) <<< b).toNat = 2 ^ b.toNat := by
  have h15 : 2 ^ b.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hb
  have e32 : b.toNat % 32 = b.toNat := Nat.mod_eq_of_lt (by omega)
  rw [UInt32.toNat_shiftLeft, e32]
  simp [Nat.shiftLeft_eq]
  omega

/-- After `initWin` the window is in use and the invariant still holds. -/
theorem initWin_inv {h : Heap} {st : InflateState} (hW : WInv h st) :
    WInv h (initWin st) ∧ 0 < (initWin st).wsize.toNat ∧ (initWin st).window = st.window ∧
    (initWin st).wbits = st.wbits := by
  obtain ⟨hk2, ⟨w, a, hw, ha, hro, hasz⟩, hws, hv, hwn, heq⟩ := hW
  have hpow : ((1 : UInt32) <<< st.wbits).toNat = 2 ^ st.wbits.toNat := shl_toNat _ hk2
  have hp : 0 < 2 ^ st.wbits.toNat := Nat.two_pow_pos _
  unfold initWin
  by_cases h0 : st.wsize == 0
  · have h0' : st.wsize = 0 := by simpa using h0
    have h00 : st.wsize.toNat = 0 := by rw [h0']; rfl
    simp only [h0, ite_true]
    refine ⟨⟨hk2, ⟨w, a, hw, ha, hro, hasz⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [hpow, hp]
  · have h0' : ¬ st.wsize = 0 := by simpa using h0
    have h00 : st.wsize.toNat ≠ 0 := fun h => h0' (UInt32.toNat_inj.mp (by simpa using h))
    have h0'' : (st.wsize == 0) = false := by simpa using h0
    simp only [h0'', Bool.false_eq_true, ite_false]
    refine ⟨⟨hk2, ⟨w, a, hw, ha, hro, hasz⟩, hws, hv, hwn, heq⟩, by omega, ?_⟩
    simp

/-- `zmemcpy(w + d, e - n, m)` on a window block `w` and a different block `eb`, then the rest `k`: the heap with the
window block replaced by a block of the same size. -/
theorem cpy_step {h : Heap} {w eb : Nat} {a ebytes : Array UInt8} {eo n m d : Nat}
    (ha : h.bytes w = some a) (hro : h.ro w = false) (heb : h.bytes eb = some ebytes) (hne : w ≠ eb)
    (hn : n ≤ eo) (hm : m ≤ n) (hoff : eo ≤ ebytes.size) (hd : d + m ≤ a.size) :
    ∃ A, (∀ {α : Type} (k : Unit → M α),
        (Pilot.psub (.ref (.blk eb) eo) n >>= fun src => (memcpyB (.ref (.blk w) d) src m >>= k)) h =
          k () { h with bytes := upd h.bytes w (some A) }) ∧ A.size = a.size := by
  refine ⟨copyRange a ebytes d (eo - n) m, ?_, size_copyRange ..⟩
  intro α k
  have h2 : eo - n + m ≤ ebytes.size := by omega
  simp only [bind_app, Pilot.psub_ok (r := BRef.blk eb) (by simpa using heb) hn hoff]
  simp only [bind_app, memcpyB_blk_ok ha heb hro hne hd h2]

/-- `zmemcpy(w + d, e - n, m)` where `w + d` is computed first (the first copy of `uw_small`). -/
theorem cpy_step_off {h : Heap} {w eb : Nat} {a ebytes : Array UInt8} {eo n m d : Nat}
    (ha : h.bytes w = some a) (hro : h.ro w = false) (heb : h.bytes eb = some ebytes) (hne : w ≠ eb)
    (hn : n ≤ eo) (hm : m ≤ n) (hoff : eo ≤ ebytes.size) (hd : d + m ≤ a.size) (hda : d ≤ a.size) :
    ∃ A, (∀ {α : Type} (k : Unit → M α),
        (Pilot.padd (.ref (.blk w) 0) d >>= fun dst => (Pilot.psub (.ref (.blk eb) eo) n >>= fun src =>
          (memcpyB dst src m >>= k))) h = k () { h with bytes := upd h.bytes w (some A) }) ∧ A.size = a.size := by
  obtain ⟨A, hA, hs⟩ := cpy_step (d := 0 + d) ha hro heb hne hn hm hoff (by omega)
  refine ⟨A, fun {α} k => ?_, hs⟩
  rw [bind_ok (Pilot.padd_ok (r := BRef.blk w) (a := a) (off := 0) (n := d) (by simpa using ha) (by omega))]
  exact hA k

/-- The tables other than `bytes` and `istates` are unchanged, and so are the read-only flags and the block counter. -/
def Same (h h' : Heap) : Prop :=
  h'.words = h.words ∧ h'.dstates = h.dstates ∧ h'.gzheaders = h.gzheaders ∧ h'.gzstates = h.gzstates ∧
    h'.streams = h.streams ∧ h'.ro = h.ro ∧ h'.nextBlk = h.nextBlk

/-- What the two branches of `updatewindow` establish. -/
def UwPost (h h' : Heap) (zs w : Nat) (st' : InflateState) : Prop :=
  h'.istates zs = some st' ∧ WInv h' st' ∧ (∀ r, r ≠ zs → h'.istates r = h.istates r) ∧
    Same h h' ∧ (∀ b, b ≠ w → h'.bytes b = h.bytes b) ∧ st'.window = .ref (.blk w) 0

/-- The branch `copy ≥ wsize` of `updatewindow` never faults and establishes the window invariant. -/
theorem uw_big_ok {h : Heap} {zs w eb eo : Nat} {st : InflateState} {ebytes : Array UInt8}
    (hW : WInv h st) (hw : st.window = .ref (.blk w) 0) (hpos : 0 < st.wsize.toNat)
    (hex : ∃ s, h.istates zs = some s) (heb : h.bytes eb = some ebytes) (hne : w ≠ eb)
    (hc : st.wsize.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ h' st', uw_big (some (.tab zs)) st (.ref (.blk eb) eo) h = .ok (0, h') ∧ UwPost h h' zs w st' := by
  obtain ⟨hk2, ⟨w', a, hw', ha, hro, hasz⟩, hws, hv, hwn, heq⟩ := hW
  have hww : w' = w := by rw [hw] at hw'; exact (Ptr.ref.inj hw').1 |> BRef.blk.inj |>.symm
  subst hww
  have hsz : st.wsize.toNat = 2 ^ st.wbits.toNat := by omega
  obtain ⟨A, hstep, hAsz⟩ :=
    cpy_step (h := h) (w := w') (eb := eb) (a := a) (ebytes := ebytes) (eo := eo) (n := st.wsize.toNat)
      (m := st.wsize.toNat) (d := 0) ha hro heb hne hc (Nat.le_refl _) hoff (by omega)
  obtain ⟨s0, hs0⟩ := hex
  have hs0' : ({ h with bytes := upd h.bytes w' (some A) } : Heap).istates zs = some s0 := hs0
  refine ⟨{ { h with bytes := upd h.bytes w' (some A) } with
      istates := upd h.istates zs (some { st with wnext := 0, whave := st.wsize }) },
    { st with wnext := 0, whave := st.wsize }, ?_, ?_⟩
  · simp only [uw_big, hw, hstep, bind_app, stInflateState_tab hs0', pure_app]
  · refine ⟨by simp, ⟨hk2, ⟨w', A, hw, by simp, by simpa using hro, hAsz.trans hasz⟩, hws, ?_, ?_, ?_⟩,
      fun r hr => by simp [upd_ne _ _ _ _ hr], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun b hb => by simp [upd_ne _ _ _ _ hb], hw⟩
    · show st.wsize.toNat ≤ st.wsize.toNat
      exact Nat.le_refl _
    · exact Or.inl (by show 0 < st.wsize.toNat; exact hpos)
    · intro hh; exact absurd hh (Nat.lt_irrefl _)

theorem uadd (a b : UInt32) (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

/-- The branch `copy < wsize` of `updatewindow` (one or two pieces) never faults and keeps the window invariant. -/
theorem uw_small_ok {h : Heap} {zs w eb eo : Nat} {st : InflateState} {copy : UInt32} {ebytes : Array UInt8}
    (hW : WInv h st) (hw : st.window = .ref (.blk w) 0) (hpos : 0 < st.wsize.toNat)
    (hex : ∃ s, h.istates zs = some s) (heb : h.bytes eb = some ebytes) (hne : w ≠ eb)
    (hc : copy.toNat ≤ eo) (hlt : copy.toNat < st.wsize.toNat) (hoff : eo ≤ ebytes.size) :
    ∃ h' st', uw_small (some (.tab zs)) st (.ref (.blk eb) eo) copy h = .ok (0, h') ∧ UwPost h h' zs w st' := by
  obtain ⟨hk2, ⟨w', a, hw', ha, hro, hasz⟩, hws, hv, hwn, heq⟩ := hW
  have hww : w' = w := by rw [hw] at hw'; exact (BRef.blk.inj (Ptr.ref.inj hw').1).symm
  subst hww
  have hsz : st.wsize.toNat = 2 ^ st.wbits.toNat := by omega
  have hwn' : st.wnext.toNat < st.wsize.toNat := by omega
  have h15 : 2 ^ st.wbits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hk2
  obtain ⟨dist, hdist⟩ : ∃ d : UInt32, d = (if st.wsize - st.wnext > copy then copy else st.wsize - st.wnext) := ⟨_, rfl⟩
  have hsub : (st.wsize - st.wnext).toNat = st.wsize.toNat - st.wnext.toNat :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  have hdn : (dist.toNat = copy.toNat ∧ copy.toNat < st.wsize.toNat - st.wnext.toNat) ∨
      (dist.toNat = st.wsize.toNat - st.wnext.toNat ∧ ¬ copy.toNat < st.wsize.toNat - st.wnext.toNat) := by
    rw [hdist]
    by_cases hc' : st.wsize - st.wnext > copy
    · left; rw [if_pos hc']; have := UInt32.lt_iff_toNat_lt.mp hc'; omega
    · right; rw [if_neg hc']; refine ⟨hsub, fun hh => hc' (UInt32.lt_iff_toNat_lt.mpr (by omega))⟩
  have hd1 : dist.toNat ≤ copy.toNat := by omega
  have hd2 : dist.toNat ≤ st.wsize.toNat - st.wnext.toNat := by omega
  obtain ⟨A1, hstep1, hA1sz⟩ :=
    cpy_step_off (h := h) (w := w') (eb := eb) (a := a) (ebytes := ebytes) (eo := eo) (n := copy.toNat) (m := dist.toNat)
      (d := st.wnext.toNat) ha hro heb hne hc hd1 hoff (by omega) (by omega)
  obtain ⟨s0, hs0⟩ := hex
  have hcsub : (copy - dist).toNat = copy.toNat - dist.toNat := UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  by_cases hcp : (copy - dist != 0) = true
  · -- the window wraps: a second piece goes to the start
    have hcn : 0 < (copy - dist).toNat := by
      have : copy - dist ≠ 0 := by simpa using hcp
      have h0 : (copy - dist).toNat ≠ 0 := fun hh => this (UInt32.toNat_inj.mp (by simpa using hh))
      omega
    obtain ⟨A2, hstep2, hA2sz⟩ :=
      cpy_step (h := { h with bytes := upd h.bytes w' (some A1) }) (w := w') (eb := eb) (a := A1) (ebytes := ebytes)
        (eo := eo) (n := (copy - dist).toNat) (m := (copy - dist).toNat) (d := 0) (by simp) (by simpa using hro)
        (by simp [upd_ne _ _ _ _ hne.symm, heb]) hne (by omega) (Nat.le_refl _) hoff (by omega)
    have hs0' : ({ { h with bytes := upd h.bytes w' (some A1) } with
        bytes := upd (upd h.bytes w' (some A1)) w' (some A2) } : Heap).istates zs = some s0 := hs0
    refine ⟨{ { { h with bytes := upd h.bytes w' (some A1) } with
        bytes := upd (upd h.bytes w' (some A1)) w' (some A2) } with
        istates := upd h.istates zs (some { st with wnext := copy - dist, whave := st.wsize }) },
      { st with wnext := copy - dist, whave := st.wsize }, ?_, ?_⟩
    · simp only [uw_small, hw, ← hdist, hstep1, hcp, ite_true, hstep2]
      simp only [bind_app, stInflateState_tab hs0', pure_app]
    · refine ⟨by simp, ⟨hk2, ⟨w', A2, hw, by simp, by simpa using hro, by show A2.size = 2 ^ st.wbits.toNat; omega⟩,
          hws, ?_, ?_, ?_⟩,
        fun r hr => by simp [upd_ne _ _ _ _ hr], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun b hb => by simp [upd_ne _ _ _ _ hb], hw⟩
      · show st.wsize.toNat ≤ st.wsize.toNat
        exact Nat.le_refl _
      · exact Or.inl (by show (copy - dist).toNat < st.wsize.toNat; omega)
      · intro hh; exact absurd hh (Nat.lt_irrefl _)
  · -- everything fits before the end of the window
    have hcp' : (copy - dist != 0) = false := by simpa using hcp
    have hc0 : copy.toNat = dist.toNat := by
      have : copy - dist = 0 := by simpa using hcp'
      have : (copy - dist).toNat = 0 := by rw [this]; rfl
      omega
    have hwd : st.wnext.toNat + dist.toNat ≤ st.wsize.toNat := by omega
    have hadd : (st.wnext + dist).toNat = st.wnext.toNat + dist.toNat := uadd _ _ (by omega)
    obtain ⟨wn, hwn_def⟩ : ∃ x : UInt32, x = (if st.wnext + dist == st.wsize then 0 else st.wnext + dist) := ⟨_, rfl⟩
    obtain ⟨wh, hwh_def⟩ : ∃ x : UInt32, x = (if st.whave < st.wsize then st.whave + dist else st.whave) := ⟨_, rfl⟩
    have hwn_nat : (wn.toNat = 0 ∧ st.wnext.toNat + dist.toNat = st.wsize.toNat) ∨
        (wn.toNat = st.wnext.toNat + dist.toNat ∧ st.wnext.toNat + dist.toNat < st.wsize.toNat) := by
      rw [hwn_def]
      by_cases hq : st.wnext + dist == st.wsize
      · left; rw [if_pos hq]
        have := UInt32.toNat_inj.mpr (beq_iff_eq.mp hq)
        refine ⟨rfl, by omega⟩
      · right; rw [if_neg hq]
        have hne' : ¬ (st.wnext + dist = st.wsize) := fun hh => hq (beq_iff_eq.mpr hh)
        have : st.wnext.toNat + dist.toNat ≠ st.wsize.toNat := fun hh =>
          hne' (UInt32.toNat_inj.mp (by omega))
        exact ⟨hadd, by omega⟩
    have hwh_nat : (st.whave.toNat < st.wsize.toNat ∧ wh.toNat = st.whave.toNat + dist.toNat) ∨
        (¬ st.whave.toNat < st.wsize.toNat ∧ wh.toNat = st.whave.toNat) := by
      rw [hwh_def]
      by_cases hl : st.whave < st.wsize
      · left; rw [if_pos hl]
        have hl' := UInt32.lt_iff_toNat_lt.mp hl
        have := heq hl'
        exact ⟨hl', uadd _ _ (by omega)⟩
      · right; rw [if_neg hl]; exact ⟨fun hh => hl (UInt32.lt_iff_toNat_lt.mpr hh), rfl⟩
    have hs0' : ({ h with bytes := upd h.bytes w' (some A1) } : Heap).istates zs = some s0 := hs0
    refine ⟨{ { h with bytes := upd h.bytes w' (some A1) } with
        istates := upd h.istates zs (some { st with wnext := wn, whave := wh }) },
      { st with wnext := wn, whave := wh }, ?_, ?_⟩
    · simp only [uw_small, hw, ← hdist, hstep1, hcp', Bool.false_eq_true, ite_false, ← hwn_def, ← hwh_def]
      simp only [bind_app, stInflateState_tab hs0', pure_app]
    · refine ⟨by simp, ⟨hk2, ⟨w', A1, hw, by simp, by simpa using hro, by show A1.size = 2 ^ st.wbits.toNat; omega⟩,
          hws, ?_, ?_, ?_⟩,
        fun r hr => by simp [upd_ne _ _ _ _ hr], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun b hb => by simp [upd_ne _ _ _ _ hb], hw⟩
      · show wh.toNat ≤ st.wsize.toNat
        omega
      · show wn.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ wn.toNat = 0)
        omega
      · show wh.toNat < st.wsize.toNat → wn.toNat = wh.toNat
        omega


end Zlib.Inflate.Proofs.W
