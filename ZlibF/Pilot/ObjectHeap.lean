import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables

/-!
# Pilot on the runtime: `flush_pending`, `updatewindow`, `slide_hash`, `fillC`, `inflateCopy`

The experiment that decided the object heap (decision D1, `docs/pilot.md`), now on the real runtime and the real
structs of the schema: the records are `ZStream`, `DeflateState`, `InflateState` and `Code`, the pointers are `BPtr`,
`WPtr` and `CodePtr`, and the heap is `C.Heap`. The functions are the pilot's simplified versions of the C
(`flush_pending` without `_tr_flush_bits`; `updatewindow` with the default allocator only; the fill loop of
`inflate_table`; the pointer fix-up of `inflateCopy`). See `docs/pilot.md` for what each one leaves out.
-/

namespace Pilot
open C

/-- `p + n` for a pointer into an array. -/
def padd {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (n : Int)
/-- `p - n` for a pointer into an array. -/
def psub {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (-(n : Int))

theorem padd_ok {R T : Type} [Space Heap R T] {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (hn : off + n ≤ a.size) : padd (.ref r off) n h = .ok (.ref r (off + n), h) :=
  Ptr.add_nat_ok hg hn
theorem psub_ok {R T : Type} [Space Heap R T] {h : Heap} {r : R} {a : Array T} {off n : Nat}
    (hg : Space.get h r = some a) (h1 : n ≤ off) (h2 : off ≤ a.size) :
    psub (.ref r off) n h = .ok (.ref r (off - n), h) :=
  Ptr.sub_nat_ok hg h1 h2

/-- `local void flush_pending(z_streamp strm)` (the call of `_tr_flush_bits` is left out). -/
def flush_pending (sr : Nat) : M Unit := do
  let z ← ldZStream (some (.tab sr))
  let ds ← castDeflateState z.state
  let d ← ldDeflateState ds
  let len : UInt32 := d.pending.toUInt32
  let len : UInt32 := if len > z.avail_out then z.avail_out else len
  if len == 0 then return
  memcpyB z.next_out d.pending_out len.toNat
  let no ← padd z.next_out len.toNat
  let po ← padd d.pending_out len.toNat
  stZStream (some (.tab sr)) { z with next_out := no, total_out := z.total_out + len.toUInt64, avail_out := z.avail_out - len }
  let pend := d.pending - len.toUInt64
  stDeflateState ds { d with pending := pend, pending_out := if pend == 0 then d.pending_buf else po }

/-- What `flush_pending` needs from the heap, for a stream `z` and its state `d`: the output range is inside a
writable byte block, the pending range is inside the block of `pending_buf`, `pending_out` and `pending_buf` point
into the same block, and the two blocks are different. -/
def Inv (h : Heap) (z : ZStream) (d : DeflateState) : Prop :=
  ∃ nb no ob pb po bo pbuf,
    z.next_out = .ref (.blk nb) no ∧ h.bytes nb = some ob ∧ h.ro nb = false ∧ no + z.avail_out.toNat ≤ ob.size ∧
    d.pending_out = .ref (.blk pb) po ∧ d.pending_buf = .ref (.blk pb) bo ∧ h.bytes pb = some pbuf ∧
    po + d.pending.toNat ≤ pbuf.size ∧ bo ≤ pbuf.size ∧ nb ≠ pb

/-- `flush_pending` never faults when the stream, its state and the two buffers satisfy `Inv`. Afterwards `Inv` holds
again, and only the stream record, the state record and the output block changed (the heap's other tables, the
read-only flags and the allocation counters are the same). Compared with the pilot on the first heap, `Inv` also asks
that the output block be writable, which a store needs. -/
theorem flush_pending_ok {h : Heap} {sr ds : Nat} {z : ZStream} {d : DeflateState}
    (hz : h.streams sr = some z) (hs : z.state = some (.deflate ds)) (hd : h.dstates ds = some d) (hI : Inv h z d) :
    ∃ h' z' d', flush_pending sr h = .ok ((), h') ∧ h'.streams sr = some z' ∧
      h'.dstates ds = some d' ∧ Inv h' z' d' ∧
      (∀ r, r ≠ sr → h'.streams r = h.streams r) ∧
      (∀ r, r ≠ ds → h'.dstates r = h.dstates r) ∧
      (∀ b, (∀ off, z.next_out ≠ .ref (.blk b) off) → h'.bytes b = h.bytes b) ∧
      h'.words = h.words ∧ h'.ro = h.ro ∧ h'.istates = h.istates ∧ h'.nextBlk = h.nextBlk := by
  obtain ⟨nb, no, ob, pb, po, bo, pbuf, hno, hob, hro, hout, hpo, hbo, hpb, hpend, hboff, hdisj⟩ := hI
  have hld : ldZStream (some (.tab sr)) h = .ok (z, h) := ldZStream_tab hz
  have hcast : castDeflateState z.state h = .ok (some (.tab ds), h) := by rw [hs]; exact castDeflateState_ok
  have hldd : ldDeflateState (some (.tab ds)) h = .ok (d, h) := ldDeflateState_tab hd
  obtain ⟨len, hlen⟩ : ∃ len : UInt32,
      len = (if d.pending.toUInt32 > z.avail_out then z.avail_out else d.pending.toUInt32) := ⟨_, rfl⟩
  have hl1 : len.toNat ≤ z.avail_out.toNat := by
    rw [hlen]; split <;> simp_all [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le] <;> omega
  have hl2 : len.toNat ≤ d.pending.toNat := by
    rw [hlen]; split <;> simp_all [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le] <;> omega
  by_cases h0 : len = 0
  · refine ⟨h, z, d, ?_, hz, hd, ⟨nb, no, ob, pb, po, bo, pbuf, hno, hob, hro, hout, hpo, hbo, hpb, hpend, hboff, hdisj⟩,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    simp [flush_pending, hld, hcast, hldd, ← hlen, h0]
  · have hn : (len == 0) = false := by simpa using h0
    -- the copy
    obtain ⟨newOut, hnew⟩ : ∃ a : Array UInt8, a = copyRange ob pbuf no po len.toNat := ⟨_, rfl⟩
    obtain ⟨h1, hh1⟩ : ∃ h1 : Heap, h1 = { h with bytes := upd h.bytes nb (some newOut) } := ⟨_, rfl⟩
    have s1 : memcpyB z.next_out d.pending_out len.toNat h = .ok ((), h1) := by
      rw [hno, hpo, hh1, hnew]; exact memcpyB_blk_ok hob hpb hro hdisj (by omega) (by omega)
    have hb1 : h1.bytes nb = some newOut := by simp [hh1]
    have hb2 : h1.bytes pb = some pbuf := by simp [hh1, upd_ne _ _ _ _ hdisj.symm, hpb]
    have hsz : newOut.size = ob.size := by rw [hnew]; exact size_copyRange _ _ _ _ _
    have s2 : padd z.next_out len.toNat h1 = .ok (.ref (.blk nb) (no + len.toNat), h1) := by
      rw [hno]; exact padd_ok (r := BRef.blk nb) (by simpa using hb1) (by omega)
    have s3 : padd d.pending_out len.toNat h1 = .ok (.ref (.blk pb) (po + len.toNat), h1) := by
      rw [hpo]; exact padd_ok (r := BRef.blk pb) (by simpa using hb2) (by omega)
    have hz1 : h1.streams sr = some z := by simp [hh1, hz]
    have hd1 : h1.dstates ds = some d := by simp [hh1, hd]
    obtain ⟨z', hz'⟩ : ∃ z' : ZStream, z' = { z with next_out := .ref (.blk nb) (no + len.toNat), total_out := z.total_out + len.toUInt64, avail_out := z.avail_out - len } := ⟨_, rfl⟩
    obtain ⟨h2, hh2⟩ : ∃ h2 : Heap, h2 = { h1 with streams := upd h1.streams sr (some z') } := ⟨_, rfl⟩
    have s4 : stZStream (some (.tab sr)) z' h1 = .ok ((), h2) := by rw [hh2]; exact stZStream_tab hz1
    have hd2 : h2.dstates ds = some d := by simp [hh2, hd1]
    obtain ⟨po', hpo'⟩ : ∃ p : BPtr, p = (if d.pending - len.toUInt64 == 0 then d.pending_buf else .ref (.blk pb) (po + len.toNat)) := ⟨_, rfl⟩
    obtain ⟨d', hd'⟩ : ∃ d' : DeflateState, d' = { d with pending := d.pending - len.toUInt64, pending_out := po' } := ⟨_, rfl⟩
    obtain ⟨h3, hh3⟩ : ∃ h3 : Heap, h3 = { h2 with dstates := upd h2.dstates ds (some d') } := ⟨_, rfl⟩
    have s5 : stDeflateState (some (.tab ds)) d' h2 = .ok ((), h3) := by rw [hh3]; exact stDeflateState_tab hd2
    have hsub : (d.pending - len.toUInt64).toNat = d.pending.toNat - len.toNat := by
      rw [UInt64.toNat_sub_of_le] <;> simp [UInt64.le_iff_toNat_le] <;> omega
    have hasub : (z.avail_out - len).toNat = z.avail_out.toNat - len.toNat := by
      rw [UInt32.toNat_sub_of_le]; simp [UInt32.le_iff_toNat_le]; omega
    refine ⟨h3, z', d', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · subst hz' hd' hpo'
      simp only [flush_pending, bind_app, hld, hcast, hldd, ← hlen, hn, Bool.false_eq_true, ite_false, ↓reduceIte, s1, s2, s3, s4, s5]
    · simp [hh3, hh2, hz']
    · simp [hh3, hd']
    · -- the invariant
      have hbytes : h3.bytes = h1.bytes := by simp [hh3, hh2]
      have hro3 : h3.ro nb = false := by simp [hh3, hh2, hh1, hro]
      by_cases hz0 : (d.pending - len.toUInt64 == 0) = true
      · have hz00 : d.pending - len.toUInt64 = 0 := by simpa using hz0
        refine ⟨nb, no + len.toNat, newOut, pb, bo, bo, pbuf, by simp [hz'], by simp [hbytes, hb1], hro3, ?_,
          by simp [hd', hpo', hz0, hbo], by simp [hd', hbo], by simp [hbytes, hb2], ?_, hboff, hdisj⟩
        · simp [hz', hsz, hasub]; omega
        · simp [hd', hz00]; omega
      · have hz0' : (d.pending - len.toUInt64 == 0) = false := by simpa using hz0
        refine ⟨nb, no + len.toNat, newOut, pb, po + len.toNat, bo, pbuf, by simp [hz'], by simp [hbytes, hb1], hro3, ?_,
          by simp [hd', hpo', hz0'], by simp [hd', hbo], by simp [hbytes, hb2], ?_, hboff, hdisj⟩
        · simp [hz', hsz, hasub]; omega
        · simp [hd', hsub]; omega
    · intro r hr; simp [hh3, hh2, hh1, hr]
    · intro r hr; simp [hh3, hh2, hh1, hr]
    · intro b hb
      have hbn : b ≠ nb := fun e => hb no (by rw [hno, e])
      simp [hh3, hh2, hh1, hbn]
    · simp [hh3, hh2, hh1]
    · simp [hh3, hh2, hh1]
    · simp [hh3, hh2, hh1]
    · simp [hh3, hh2, hh1]


/-! ## `updatewindow`: the ring buffer -/

/-- `if (state->wsize == 0) { wsize = 1U << wbits; wnext = 0; whave = 0; }` -/
def initWin (st : InflateState) : InflateState :=
  if st.wsize == 0 then { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } else st

/-- `if (copy >= wsize)`: copy the last `wsize` bytes before `end` into the whole window. -/
def uw_big (ist : InflateStatePtr) (st : InflateState) (e : BPtr) : M UInt32 := do
  let src ← psub e st.wsize.toNat
  memcpyB st.window src st.wsize.toNat
  stInflateState ist { st with wnext := 0, whave := st.wsize }
  return 0

/-- `else`: copy `copy` bytes into the ring buffer, in at most two pieces. -/
def uw_small (ist : InflateStatePtr) (st : InflateState) (e : BPtr) (copy : UInt32) : M UInt32 := do
  let dist : UInt32 := if st.wsize - st.wnext > copy then copy else st.wsize - st.wnext
  let dst ← padd st.window st.wnext.toNat
  let src ← psub e copy.toNat
  memcpyB dst src dist.toNat
  let copy' : UInt32 := copy - dist
  if copy' != 0 then
    let src2 ← psub e copy'.toNat
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
  k : 8 ≤ st.wbits.toNat ∧ st.wbits.toNat ≤ 15
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
  obtain ⟨⟨hk1, hk2⟩, ⟨w, a, hw, ha, hro, hasz⟩, hws, hv, hwn, heq⟩ := hW
  have hpow : ((1 : UInt32) <<< st.wbits).toNat = 2 ^ st.wbits.toNat := shl_toNat _ hk2
  have hp : 0 < 2 ^ st.wbits.toNat := Nat.two_pow_pos _
  unfold initWin
  by_cases h0 : st.wsize == 0
  · have h0' : st.wsize = 0 := by simpa using h0
    have h00 : st.wsize.toNat = 0 := by rw [h0']; rfl
    simp only [h0, ite_true]
    refine ⟨⟨⟨hk1, hk2⟩, ⟨w, a, hw, ha, hro, hasz⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [hpow, hp]
  · have h0' : ¬ st.wsize = 0 := by simpa using h0
    have h00 : st.wsize.toNat ≠ 0 := fun h => h0' (UInt32.toNat_inj.mp (by simpa using h))
    have h0'' : (st.wsize == 0) = false := by simpa using h0
    simp only [h0'', Bool.false_eq_true, ite_false]
    refine ⟨⟨⟨hk1, hk2⟩, ⟨w, a, hw, ha, hro, hasz⟩, hws, hv, hwn, heq⟩, by omega, ?_⟩
    simp

/-- `zmemcpy(w + d, e - n, m)` on a window block `w` and a different block `eb`, then the rest `k`: the heap with the
window block replaced by a block of the same size. -/
theorem cpy_step {h : Heap} {w eb : Nat} {a ebytes : Array UInt8} {eo n m d : Nat}
    (ha : h.bytes w = some a) (hro : h.ro w = false) (heb : h.bytes eb = some ebytes) (hne : w ≠ eb)
    (hn : n ≤ eo) (hm : m ≤ n) (hoff : eo ≤ ebytes.size) (hd : d + m ≤ a.size) :
    ∃ A, (∀ {α : Type} (k : Unit → M α),
        (psub (.ref (.blk eb) eo) n >>= fun src => (memcpyB (.ref (.blk w) d) src m >>= k)) h =
          k () { h with bytes := upd h.bytes w (some A) }) ∧ A.size = a.size := by
  refine ⟨copyRange a ebytes d (eo - n) m, ?_, size_copyRange ..⟩
  intro α k
  have h2 : eo - n + m ≤ ebytes.size := by omega
  simp only [bind_app, psub_ok (r := BRef.blk eb) (by simpa using heb) hn hoff]
  simp only [bind_app, memcpyB_blk_ok ha heb hro hne hd h2]

/-- `zmemcpy(w + d, e - n, m)` where `w + d` is computed first (the first copy of `uw_small`). -/
theorem cpy_step_off {h : Heap} {w eb : Nat} {a ebytes : Array UInt8} {eo n m d : Nat}
    (ha : h.bytes w = some a) (hro : h.ro w = false) (heb : h.bytes eb = some ebytes) (hne : w ≠ eb)
    (hn : n ≤ eo) (hm : m ≤ n) (hoff : eo ≤ ebytes.size) (hd : d + m ≤ a.size) (hda : d ≤ a.size) :
    ∃ A, (∀ {α : Type} (k : Unit → M α),
        (padd (.ref (.blk w) 0) d >>= fun dst => (psub (.ref (.blk eb) eo) n >>= fun src =>
          (memcpyB dst src m >>= k))) h = k () { h with bytes := upd h.bytes w (some A) }) ∧ A.size = a.size := by
  obtain ⟨A, hA, hs⟩ := cpy_step (d := 0 + d) ha hro heb hne hn hm hoff (by omega)
  refine ⟨A, fun {α} k => ?_, hs⟩
  rw [bind_ok (padd_ok (r := BRef.blk w) (a := a) (off := 0) (n := d) (by simpa using ha) (by omega))]
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
  obtain ⟨⟨hk1, hk2⟩, ⟨w', a, hw', ha, hro, hasz⟩, hws, hv, hwn, heq⟩ := hW
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
  · refine ⟨by simp, ⟨⟨hk1, hk2⟩, ⟨w', A, hw, by simp, by simpa using hro, hAsz.trans hasz⟩, hws, ?_, ?_, ?_⟩,
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
  obtain ⟨⟨hk1, hk2⟩, ⟨w', a, hw', ha, hro, hasz⟩, hws, hv, hwn, heq⟩ := hW
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
    · refine ⟨by simp, ⟨⟨hk1, hk2⟩, ⟨w', A2, hw, by simp, by simpa using hro, by show A2.size = 2 ^ st.wbits.toNat; omega⟩,
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
    · refine ⟨by simp, ⟨⟨hk1, hk2⟩, ⟨w', A1, hw, by simp, by simpa using hro, by show A1.size = 2 ^ st.wbits.toNat; omega⟩,
          hws, ?_, ?_, ?_⟩,
        fun r hr => by simp [upd_ne _ _ _ _ hr], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun b hb => by simp [upd_ne _ _ _ _ hb], hw⟩
      · show wh.toNat ≤ st.wsize.toNat
        omega
      · show wn.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ wn.toNat = 0)
        omega
      · show wh.toNat < st.wsize.toNat → wn.toNat = wh.toNat
        omega


/-- The ring-buffer part of `updatewindow` never faults and keeps the window invariant W.
The caller's buffer (the block `eb`) is a different block from the window. -/
theorem update2_ok {h : Heap} {sr zs eb eo : Nat} {z : ZStream} {st0 : InflateState} {copy : UInt32}
    {ebytes : Array UInt8}
    (hz : h.streams sr = some z) (hs : z.state = some (.inflate zs)) (hi : h.istates zs = some st0)
    (hW : WInv h st0) (heb : h.bytes eb = some ebytes) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hdisj : ∀ w, st0.window = .ref (.blk w) 0 → eb ≠ w) :
    ∃ w h' st', st0.window = .ref (.blk w) 0 ∧ update2 sr (.ref (.blk eb) eo) copy h = .ok (0, h') ∧
      UwPost h h' zs w st' := by
  obtain ⟨hW1, hpos, hwin1, hwb1⟩ := initWin_inv hW
  obtain ⟨-, ⟨w, a, hw, ha, hro, hasz⟩, -⟩ := hW
  have hw1 : (initWin st0).window = .ref (.blk w) 0 := by rw [hwin1]; exact hw
  have hne : w ≠ eb := (hdisj w hw).symm
  have hcast : castInflateState z.state h = .ok (some (.tab zs), h) := by rw [hs]; exact castInflateState_ok
  by_cases hcopy : copy ≥ (initWin st0).wsize
  · have hc1 : (initWin st0).wsize.toNat ≤ eo := by
      have := UInt32.le_iff_toNat_le.mp hcopy; omega
    obtain ⟨h', st', hrun, hpost⟩ := uw_big_ok hW1 hw1 hpos ⟨st0, hi⟩ heb hne hc1 hoff
    refine ⟨w, h', st', hw, ?_, hpost⟩
    simp only [update2, bind_app, ldZStream_tab hz, hcast, ldInflateState_tab hi, hcopy, ite_true]
    exact hrun
  · have hlt : copy.toNat < (initWin st0).wsize.toNat := by
      have h1 : ¬ (initWin st0).wsize.toNat ≤ copy.toNat := fun hh => hcopy (UInt32.le_iff_toNat_le.mpr hh)
      omega
    obtain ⟨h', st', hrun, hpost⟩ := uw_small_ok hW1 hw1 hpos ⟨st0, hi⟩ heb hne hc hlt hoff
    refine ⟨w, h', st', hw, ?_, hpost⟩
    simp only [update2, bind_app, ldZStream_tab hz, hcast, ldInflateState_tab hi, hcopy, ite_false]
    exact hrun


/-! ## `updatewindow`: the allocation of the window -/

/-- `local int updatewindow(z_streamp strm, const Bytef *end, unsigned copy)` with the default allocator. -/
def updatewindow (sr : Nat) (e : BPtr) (copy : UInt32) : M UInt32 := do
  let z ← ldZStream (some (.tab sr))
  let ist ← castInflateState z.state
  let st ← ldInflateState ist
  if st.window == .null then
    let w ← allocB ((1 : UInt32) <<< st.wbits).toNat
    stInflateState ist { st with window := w }
    if w == .null then return 1
  update2 sr e copy

/-- The window invariant before the window exists (`window = NULL`, nothing in use) or after. -/
def WInv0 (h : Heap) (st : InflateState) : Prop :=
  (8 ≤ st.wbits.toNat ∧ st.wbits.toNat ≤ 15) ∧
  ((st.window = .null ∧ st.wsize.toNat = 0 ∧ st.whave.toNat = 0 ∧ st.wnext.toNat = 0) ∨ WInv h st)

/-- `updatewindow` never faults, with or without an existing window and whether or not the allocation succeeds; it
keeps the window invariant and the freshness of block numbers, and a failed allocation leaves the state unchanged. -/
theorem updatewindow_ok {h : Heap} {sr zs eb eo : Nat} {z : ZStream} {st0 : InflateState} {copy : UInt32}
    {ebytes : Array UInt8}
    (hz : h.streams sr = some z) (hs : z.state = some (.inflate zs)) (hi : h.istates zs = some st0)
    (hW : WInv0 h st0) (hF : Fresh h)
    (heb : h.bytes eb = some ebytes) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size)
    (hdisj : ∀ w, st0.window = .ref (.blk w) 0 → eb ≠ w) :
    ∃ r h' st', updatewindow sr (.ref (.blk eb) eo) copy h = .ok (r, h') ∧ h'.istates zs = some st' ∧
      WInv0 h' st' ∧ Fresh h' ∧ (r = 1 → st' = st0) ∧ h'.streams = h.streams ∧
      (∀ x, x ≠ zs → h'.istates x = h.istates x) ∧
      (∀ b, b < h.nextBlk → (∀ w, st'.window = .ref (.blk w) 0 → b ≠ w) → h'.bytes b = h.bytes b) := by
  have hek : eb < h.nextBlk := hF.lt (Or.inl (by simp [heb]))
  have hzk : zs < h.nextBlk := hF.lt (by unfold Heap.live; simp [hi])
  have hcast : castInflateState z.state h = .ok (some (.tab zs), h) := by rw [hs]; exact castInflateState_ok
  unfold WInv0 at hW
  obtain ⟨hk, hcase⟩ := hW
  rcases hcase with ⟨hnone, hws0, hwh0, hwn0⟩ | hW1
  · by_cases hok : h.allocOk h.nalloc = true
    · -- the allocation succeeds
      obtain ⟨n, hn⟩ : ∃ n, n = ((1 : UInt32) <<< st0.wbits).toNat := ⟨_, rfl⟩
      have hn2 : n = 2 ^ st0.wbits.toNat := by rw [hn]; exact shl_toNat _ hk.2
      obtain ⟨A0, hA0⟩ : ∃ A0 : Array UInt8, A0 = Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val) := ⟨_, rfl⟩
      have hA0sz : A0.size = n := by rw [hA0]; simp
      obtain ⟨h1, hh1⟩ : ∃ x : Heap, x = { h with bytes := upd h.bytes h.nextBlk (some A0), ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 } := ⟨_, rfl⟩
      have hA : allocB n h = .ok (.ref (.blk h.nextBlk) 0, h1) := by rw [hh1, hA0]; exact allocB_some n hok
      obtain ⟨st1, hst1⟩ : ∃ s : InflateState, s = { st0 with window := .ref (.blk h.nextBlk) 0 } := ⟨_, rfl⟩
      obtain ⟨h2, hh2⟩ : ∃ x : Heap, x = { h1 with istates := upd h1.istates zs (some st1) } := ⟨_, rfl⟩
      have hs1 : h1.istates zs = some st0 := by rw [hh1]; exact hi
      have hS : stInflateState (some (.tab zs)) st1 h1 = .ok ((), h2) := by rw [hh2]; exact stInflateState_tab hs1
      have h2b : ∀ x, x ≠ h.nextBlk → h2.bytes x = h.bytes x := by
        intro x hx; rw [hh2, hh1]; exact upd_ne _ _ _ _ hx
      have h2bn : h2.bytes h.nextBlk = some A0 := by rw [hh2, hh1]; simp
      have h2ro : h2.ro h.nextBlk = false := by rw [hh2, hh1]; simp
      have hW2 : WInv h2 st1 := by
        refine ⟨by simpa [hst1] using hk, ⟨h.nextBlk, A0, by simp [hst1], h2bn, h2ro, by simp [hst1, hA0sz, hn2]⟩,
          Or.inl (by simp [hst1, hws0]), by simp [hst1, hws0, hwh0], Or.inr ⟨by simp [hst1, hws0], by simp [hst1, hwn0]⟩, ?_⟩
        intro hh; simp [hst1, hws0, hwh0] at hh
      have hz2 : h2.streams sr = some z := by rw [hh2, hh1]; exact hz
      have hs2 : h2.istates zs = some st1 := by rw [hh2]; simp
      have heb2 : h2.bytes eb = some ebytes := by rw [h2b _ (by omega)]; exact heb
      have hdisj2 : ∀ w, st1.window = .ref (.blk w) 0 → eb ≠ w := by
        intro w hw; simp [hst1] at hw; omega
      obtain ⟨w, h', st', hw', hrun, hpost⟩ := update2_ok hz2 hs hs2 hW2 heb2 hc hoff hdisj2
      obtain ⟨hi', hWn, hfi, ⟨hSw, hSd, hSg, hSgz, hSs, hSro, hSnb⟩, hfr, hwin⟩ := hpost
      have hwn : w = h.nextBlk := by simp [hst1] at hw'; omega
      have hnb' : h'.nextBlk = h.nextBlk + 1 := by rw [hSnb, hh2, hh1]
      have hbn : (Ptr.ref (BRef.blk h.nextBlk) 0 == (Ptr.null : BPtr)) = false := by simp
      refine ⟨0, h', st', ?_, hi', ⟨hWn.k, Or.inr hWn⟩, ?_, fun hh => absurd hh (by decide), ?_, ?_, ?_⟩
      · subst hst1
        simp only [updatewindow, bind_app, ldZStream_tab hz, hcast, ldInflateState_tab hi, hnone, ← hn, beq_self_eq_true,
          ite_true, hA, hbn, Bool.false_eq_true, ite_false, pure_app, hS, hrun]
        done
      · refine hF.mono (by omega) ?_
        intro x hx
        have hx' : h.nextBlk + 1 ≤ x := by rw [hnb'] at hx; exact hx
        have hxw : x ≠ w := by omega
        have hxz : x ≠ zs := by omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfr x hxw, h2b x (by omega)]
        · simp [hSw, hh2, hh1]
        · simp [hSs, hh2, hh1]
        · simp [hSg, hh2, hh1]
        · simp [hSd, hh2, hh1]
        · rw [hfi x hxz, hh2, hh1]; exact upd_ne _ _ _ _ hxz
        · simp [hSgz, hh2, hh1]
      · rw [hSs, hh2, hh1]
      · intro x hx; rw [hfi x hx, hh2, hh1]; exact upd_ne _ _ _ _ hx
      · intro b hb hfun
        have hbw : b ≠ w := hfun w hwin
        rw [hfr b hbw, h2b b (by omega)]
    · -- the allocation fails: the function returns 1 and nothing else changes
      have hst0 : ({ st0 with window := Ptr.null } : InflateState) = st0 := by rw [← hnone]
      obtain ⟨h1, hh1⟩ : ∃ x : Heap, x = { h with nalloc := h.nalloc + 1 } := ⟨_, rfl⟩
      have hs1 : h1.istates zs = some st0 := by rw [hh1]; exact hi
      have hA : allocB ((1 : UInt32) <<< st0.wbits).toNat h = .ok (.null, h1) := by
        rw [hh1]; exact allocB_none _ hok
      refine ⟨1, { h1 with istates := upd h1.istates zs (some { st0 with window := Ptr.null }) },
        { st0 with window := Ptr.null }, ?_, by simp, ⟨hk, Or.inl ⟨rfl, hws0, hwh0, hwn0⟩⟩, ?_, fun _ => hst0, ?_, ?_, ?_⟩
      · simp only [updatewindow, bind_app, ldZStream_tab hz, hcast, ldInflateState_tab hi, hnone, beq_self_eq_true,
          ite_true, hA, stInflateState_tab hs1, pure_app]
      · refine hF.mono (by simp [hh1]) ?_
        intro x hx
        have hxz : x ≠ zs := by simp [hh1] at hx; omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hh1, upd_ne _ _ _ _ hxz]
      · simp [hh1]
      · intro x hx; simp [upd_ne _ _ _ _ hx, hh1]
      · intro b _ _; simp [hh1]
  · -- the window exists already
    have hW1c := hW1
    obtain ⟨-, ⟨w, a, hw, ha, hro, hasz⟩, -⟩ := hW1c
    obtain ⟨w', h', st', hw', hrun, hpost⟩ := update2_ok hz hs hi hW1 heb hc hoff hdisj
    obtain ⟨hi', hWn, hfi, ⟨hSw, hSd, hSg, hSgz, hSs, hSro, hSnb⟩, hfr, hwin⟩ := hpost
    have hww : w' = w := by rw [hw'] at hw; exact (BRef.blk.inj (Ptr.ref.inj hw).1)
    have hwlt : w' < h.nextBlk := hF.lt (Or.inl (by rw [hww]; simp [ha]))
    have hnn : (st0.window == (Ptr.null : BPtr)) = false := by rw [hw]; simp
    refine ⟨0, h', st', ?_, hi', ⟨hWn.k, Or.inr hWn⟩, ?_, fun hh => absurd hh (by decide), hSs, hfi, ?_⟩
    · simp only [updatewindow, bind_app, ldZStream_tab hz, hcast, ldInflateState_tab hi, hnn, Bool.false_eq_true,
        ite_false, pure_app, hrun]
    · refine hF.mono (by omega) ?_
      intro x hx
      have hxw : x ≠ w' := by omega
      have hxz : x ≠ zs := by omega
      exact ⟨hfr x hxw, by rw [hSw], by rw [hSs], by rw [hSg], by rw [hSd], hfi x hxz, by rw [hSgz]⟩
    · intro b hb hfun
      exact hfr b (hfun w' hwin)


/-! ## `slide_hash`: a loop over an array of any content -/

/-- `(Pos)(m >= wsize ? m - wsize : NIL)` -/
def slideF (wsize : UInt32) (m : UInt16) : UInt16 :=
  if m.toUInt32 ≥ wsize then (m.toUInt32 - wsize).toUInt16 else 0

/-- `do { m = *--p; *p = ...; } while (--n)` from the entry before `p` down to the first, `n` entries. (The C loop is
a `do ... while`: for `n = 0` it wraps; here `n = 0` does nothing. `hash_size` and `w_size` are never 0.) -/
def slideArr (wsize : UInt32) (p : WPtr) : Nat → M Unit
  | 0 => pure ()
  | k + 1 => do
    let p ← psub p 1
    let m ← Ptr.load p
    Ptr.store p (slideF wsize m)
    slideArr wsize p k

/-- For every content of the array, `slide_hash` on the first `n` entries does not fault, keeps the size, applies
`slideF` to the first `n` entries and leaves the others alone. -/
theorem slideArr_ok (b : Nat) (wsize : UInt32) :
    ∀ (n : Nat) (h : Heap) (a : Array UInt16), h.words b = some a → n ≤ a.size →
    ∃ a' : Array UInt16, slideArr wsize (.ref (.blk b) n) n h = .ok ((), { h with words := upd h.words b (some a') }) ∧
      a'.size = a.size ∧ ∀ i, a'[i]? = if i < n then a[i]?.map (slideF wsize) else a[i]? := by
  intro n
  induction n with
  | zero =>
    intro h a ha hn
    refine ⟨a, ?_, rfl, fun i => by simp⟩
    simp [slideArr, pure_app, upd_self _ _ _ ha]
  | succ k ih =>
    intro h a ha hn
    have hk : k < a.size := by omega
    have hg : Space.get h (WRef.blk b) = some a := ha
    have hp : psub (Ptr.ref (WRef.blk b) (k + 1)) 1 h = .ok (.ref (.blk b) k, h) := by
      have := psub_ok (off := k + 1) (n := 1) hg (by omega) (by omega)
      simpa using this
    have hld : Ptr.load (Ptr.ref (WRef.blk b) k) h = .ok (a[k], h) := Ptr.load_ok hg hk
    have hst : Ptr.store (Ptr.ref (WRef.blk b) k) (slideF wsize a[k]) h =
        .ok ((), { h with words := upd h.words b (some (a.set! k (slideF wsize a[k]))) }) :=
      Ptr.store_ok hg (by simp) hk
    obtain ⟨a', hrun, hsz, hent⟩ := ih { h with words := upd h.words b (some (a.set! k (slideF wsize a[k]))) }
      (a.set! k (slideF wsize a[k])) (by simp) (by simp; omega)
    refine ⟨a', ?_, by simpa using hsz, ?_⟩
    · simp only [slideArr, bind_app, hp, hld, hst, hrun, upd_upd]
    · intro i
      rw [hent i]
      rcases Nat.lt_trichotomy i k with h1 | h1 | h1
      · have : i ≠ k := by omega
        simp [h1, show i < k + 1 by omega, Array.getElem?_setIfInBounds, this, this.symm]
      · subst h1; simp [Array.getElem?_setIfInBounds, hk]
      · have : i ≠ k := by omega
        simp [show ¬ i < k by omega, show ¬ i < k + 1 by omega, Array.getElem?_setIfInBounds, this, this.symm]

/-- `local void slide_hash(deflate_state *s)` -/
def slide_hash (sr : Nat) : M Unit := do
  let d ← ldDeflateState (some (.tab sr))
  let p ← padd d.head d.hash_size.toNat
  slideArr d.w_size p d.hash_size.toNat
  let q ← padd d.prev d.w_size.toNat
  slideArr d.w_size q d.w_size.toNat
  stDeflateState (some (.tab sr)) { d with slid := 1 }

/-- `slide_hash` never faults, whatever the entries of `head` and `prev` hold (they may be garbage: `prev` is never
cleared). It changes only the two arrays and the field `slid`. -/
theorem slide_hash_ok {h : Heap} {sr hb pb : Nat} {d : DeflateState} {ah ap : Array UInt16}
    (hd : h.dstates sr = some d) (hhead : d.head = .ref (.blk hb) 0) (hprev : d.prev = .ref (.blk pb) 0)
    (hh : h.words hb = some ah) (hp : h.words pb = some ap)
    (hne : hb ≠ pb) (h1 : d.hash_size.toNat ≤ ah.size) (h2 : d.w_size.toNat ≤ ap.size) :
    ∃ h', slide_hash sr h = .ok ((), h') ∧ h'.dstates sr = some { d with slid := 1 } ∧
      (∀ x, x ≠ sr → h'.dstates x = h.dstates x) ∧ h'.bytes = h.bytes ∧ h'.streams = h.streams ∧
      (∀ b, b ≠ hb → b ≠ pb → h'.words b = h.words b) := by
  obtain ⟨a1, hr1, hs1, he1⟩ := slideArr_ok hb d.w_size d.hash_size.toNat h ah hh h1
  obtain ⟨H1, hH1⟩ : ∃ x : Heap, x = { h with words := upd h.words hb (some a1) } := ⟨_, rfl⟩
  rw [← hH1] at hr1
  have hp1 : H1.words pb = some ap := by rw [hH1]; simp [upd_ne _ _ _ _ hne.symm, hp]
  obtain ⟨a2, hr2, hs2, he2⟩ := slideArr_ok pb d.w_size d.w_size.toNat H1 ap hp1 h2
  obtain ⟨H2, hH2⟩ : ∃ x : Heap, x = { H1 with words := upd H1.words pb (some a2) } := ⟨_, rfl⟩
  rw [← hH2] at hr2
  have hd2 : H2.dstates sr = some d := by rw [hH2, hH1]; exact hd
  have e1 : padd d.head d.hash_size.toNat h = .ok (.ref (.blk hb) d.hash_size.toNat, h) := by
    rw [hhead]; simpa using padd_ok (r := WRef.blk hb) (a := ah) (off := 0) (n := d.hash_size.toNat) hh (by omega)
  have e2 : padd d.prev d.w_size.toNat H1 = .ok (.ref (.blk pb) d.w_size.toNat, H1) := by
    rw [hprev]; simpa using padd_ok (r := WRef.blk pb) (a := ap) (off := 0) (n := d.w_size.toNat) hp1 (by omega)
  refine ⟨{ H2 with dstates := upd H2.dstates sr (some { d with slid := 1 }) }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [slide_hash, bind_app, ldDeflateState_tab hd, e1, hr1, e2, hr2, stDeflateState_tab hd2, pure_app]
  · simp
  · intro x hx; simp [upd_ne _ _ _ _ hx, hH2, hH1]
  · simp [hH2, hH1]
  · simp [hH2, hH1]
  · intro b hb1 hb2; simp [hH2, hH1, upd_ne _ _ _ _ hb2, upd_ne _ _ _ _ hb1]


/-! ## Pointers into a struct, and copying a struct -/

/-- Write `c` to the `n` entries `p[0 .. n-1]` of a `code` array: the shape of the replicate loop of
`inflate_table`. -/
def fillC (p : CodePtr) (c : Code) : Nat → M Unit
  | 0 => pure ()
  | k + 1 => do
    let q ← padd p k
    Ptr.store q c
    fillC p c k

/-- Writing `n` entries inside the array of the state never faults, changes only those entries of that array, and
leaves the rest of the state, all other states and everything else alone. -/
theorem fillC_ok (r i : Nat) (c : Code) :
    ∀ (n : Nat) (h : Heap) (s : InflateState), h.istates r = some s → i + n ≤ s.codes.size →
    ∃ a : Array Code, fillC (.ref (.istate_codes r) i) c n h =
        .ok ((), { h with istates := upd h.istates r (some { s with codes := a }) }) ∧
      a.size = s.codes.size ∧ ∀ j, a[j]? = if i ≤ j ∧ j < i + n then (if j < s.codes.size then some c else none) else s.codes[j]? := by
  intro n
  induction n with
  | zero =>
    intro h s hs hn
    refine ⟨s.codes, ?_, rfl, fun j => by simp; intros; omega⟩
    simp [fillC, pure_app, upd_self _ _ _ hs]
  | succ k ih =>
    intro h s hs hn
    have hk : i + k < s.codes.size := by omega
    have hg : Space.get h (CodeRef.istate_codes r) = some s.codes := CodeRef.get_istate_codes hs
    have hc : padd (Ptr.ref (CodeRef.istate_codes r) i) k h = .ok (.ref (.istate_codes r) (i + k), h) :=
      padd_ok hg (by omega)
    have hst : Ptr.store (Ptr.ref (CodeRef.istate_codes r) (i + k)) c h =
        .ok ((), { h with istates := upd h.istates r (some { s with codes := s.codes.set! (i + k) c }) }) := by
      rw [Ptr.store_ok hg (by simp) hk, CodeRef.put_istate_codes hs]
    obtain ⟨a, hrun, hsz, hent⟩ := ih { h with istates := upd h.istates r (some { s with codes := s.codes.set! (i + k) c }) }
      { s with codes := s.codes.set! (i + k) c } (by simp) (by simp; omega)
    refine ⟨a, ?_, by simpa using hsz, ?_⟩
    · simp only [fillC, bind_app, hc, hst, hrun, upd_upd]
    · intro j
      rw [hent j]
      rcases Nat.lt_trichotomy j (i + k) with h1 | h1 | h1
      · have : j ≠ i + k := by omega
        by_cases hj : i ≤ j
        · simp [hj, h1, show j < i + (k + 1) by omega, Array.getElem?_setIfInBounds, this, this.symm]
        · simp [hj, Array.getElem?_setIfInBounds, this, this.symm]
      · subst h1; simp [Array.getElem?_setIfInBounds, hk, show i ≤ i + k by omega]
      · have : j ≠ i + k := by omega
        simp [show ¬ j < i + k + 1 by omega, show ¬ j < i + k by omega, Array.getElem?_setIfInBounds, this, this.symm]
        intros; omega

/-- The fix-up in `inflateCopy`: a pointer into `src`'s `codes` becomes the same entry of `dst`'s `codes`; a pointer to a
static table stays. -/
def rebase (src dst : Nat) : CodePtr → CodePtr
  | .ref (.istate_codes r) i => if r = src then .ref (.istate_codes dst) i else .ref (.istate_codes r) i
  | p => p

/-- The copy of a state: the struct is copied as a value (the array `codes` with it), then `lencode`, `distcode` and
`next` are moved into the copy. -/
def copyOf (src dst : Nat) (s : InflateState) : InflateState :=
  { s with lencode := rebase src dst s.lencode, distcode := rebase src dst s.distcode, next := rebase src dst s.next }

/-- `zmemcpy(copy, state, sizeof(struct inflate_state))`, then the fix-up of the three pointers (the pilot leaves out
the window and the reset of `strm`). -/
def inflateCopy (src dst : Nat) : M Unit := do
  let s ← ldInflateState (some (.tab src))
  stInflateState (some (.tab dst)) (copyOf src dst s)

/-- Reading the entry `k` after `p`, without running anything (used to state what a copy preserves). -/
def derefAt (h : Heap) : CodePtr → Nat → Option Code
  | .null, _ => none
  | .ref r i, k => (Space.get h r).bind (fun a => a[i + k]?)

/-- A table pointer of state `src` points to a static table, or into `src`'s own array, or is null. This is a clause of
the representation invariant of an inflate state. -/
def PtrOk (src : Nat) (p : CodePtr) : Prop :=
  p = .null ∨ (∃ i, p = .ref (.istate_codes src) i) ∨ (∃ i, p = .ref .st_lenfix i) ∨ (∃ i, p = .ref .st_distfix i)

theorem rebase_ok {src dst : Nat} {p : CodePtr} (hp : PtrOk src p) : PtrOk dst (rebase src dst p) := by
  rcases hp with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp [rebase, PtrOk]

theorem derefAt_rebase {h h' : Heap} {src dst : Nat} {s s' : InflateState} (hs : h.istates src = some s)
    (hs' : h'.istates dst = some s') (hc : s'.codes = s.codes) (hstat : h'.static = h.static)
    {p : CodePtr} (hp : PtrOk src p) (k : Nat) :
    derefAt h' (rebase src dst p) k = derefAt h p k := by
  rcases hp with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rfl
  · simp [rebase, derefAt, CodeRef.get_istate_codes hs, CodeRef.get_istate_codes hs', hc]
  · simp [rebase, derefAt, hstat]
  · simp [rebase, derefAt, hstat]

/-- `inflateCopy` never faults; the copy has the same table, its pointers point into its own table, and reading through
them gives exactly what reading through the original pointers gives. The original and all other states are unchanged. -/
theorem inflateCopy_ok {h : Heap} {src dst : Nat} {s d : InflateState}
    (hs : h.istates src = some s) (hd : h.istates dst = some d) (hne : src ≠ dst)
    (hl : PtrOk src s.lencode) (hdc : PtrOk src s.distcode) (hn : PtrOk src s.next) :
    ∃ h' s', inflateCopy src dst h = .ok ((), h') ∧ h'.istates dst = some s' ∧ s'.codes = s.codes ∧
      h'.istates src = some s ∧ (∀ x, x ≠ dst → h'.istates x = h.istates x) ∧
      h'.bytes = h.bytes ∧ h'.streams = h.streams ∧ h'.dstates = h.dstates ∧ h'.words = h.words ∧
      PtrOk dst s'.lencode ∧ PtrOk dst s'.distcode ∧ PtrOk dst s'.next ∧
      (∀ k, derefAt h' s'.lencode k = derefAt h s.lencode k) ∧
      (∀ k, derefAt h' s'.distcode k = derefAt h s.distcode k) ∧
      (∀ k, derefAt h' s'.next k = derefAt h s.next k) := by
  have hs' : ({ h with istates := upd h.istates dst (some (copyOf src dst s)) } : Heap).istates dst =
      some (copyOf src dst s) := by simp
  refine ⟨{ h with istates := upd h.istates dst (some (copyOf src dst s)) }, copyOf src dst s,
    ?_, ?_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rebase_ok hl, rebase_ok hdc, rebase_ok hn, ?_, ?_, ?_⟩
  · simp only [inflateCopy, bind_app, ldInflateState_tab hs, stInflateState_tab hd]
  · simp
  · simp [upd_ne _ _ _ _ hne]; exact hs
  · intro x hx; simp [upd_ne _ _ _ _ hx]
  · intro k; exact derefAt_rebase (s' := copyOf src dst s) hs hs' rfl rfl hl k
  · intro k; exact derefAt_rebase (s' := copyOf src dst s) hs hs' rfl rfl hdc k
  · intro k; exact derefAt_rebase (s' := copyOf src dst s) hs hs' rfl rfl hn k

end Pilot
