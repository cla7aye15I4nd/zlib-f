import ZlibF.Proof.«inflate.c.sync3»

/-!
# inflate.c: `inflateSync`, the first call (restore of the bit buffer)

On the first call (`mode != SYNC`) the whole bytes of the bit buffer are moved to `buf` and searched first.
-/

namespace Zlib.Inflate.Spec
open C

/-- `x >> (8 n)`, as the restore loop computes it: `n` shifts by 8. -/
def shr8N : Nat → UInt64 → UInt64
  | 0, x => x
  | n + 1, x => shr8N n x >>> 8

/-- The array `buf` after the restore loop has stored the low bytes of `x`, `i` times. -/
def fillBuf (A : Array UInt8) (x : UInt64) : Nat → Array UInt8
  | 0 => A
  | i + 1 => (fillBuf A x i).set! i (shr8N i x).toUInt8

/-- The bit buffer after its partial byte (`bits & 7` bits) is dropped. -/
def syncHold0 (st : InflateState) : UInt64 := st.hold >>> (st.bits &&& 7).toUInt64

/-- The number of whole bytes in the bit buffer. -/
def syncNB (st : InflateState) : Nat := (st.bits.toNat) / 8

/-- The bytes `inflateSync` moves out of the bit buffer, in the order they were read from the input (low byte first). -/
def syncRestore (st : InflateState) : List UInt8 :=
  (List.range (syncNB st)).map fun j => (shr8N j (syncHold0 st)).toUInt8

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate _root_.Zlib.Inflate.Spec

theorem sync_and7_toNat (x : UInt32) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [UInt32.toNat_and]
  have : (7 : UInt32).toNat = 2 ^ 3 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem bitsDrop_toNat (b : UInt32) (hb : b.toNat ≤ 39) :
    (b - (b &&& 7)) = UInt32.ofNat (8 * (b.toNat / 8)) := by
  apply UInt32.toNat_inj.mp
  have h7 := sync_and7_toNat b
  have hle : (b &&& 7) ≤ b := by
    rw [UInt32.le_iff_toNat_le, h7]; omega
  rw [UInt32.toNat_sub_of_le _ _ hle, h7, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
  omega

theorem sync_shr64_run (h : Heap) (x : UInt64) (n : UInt32) (hn : n < 64) : shr64 x n h = .ok (x >>> n.toUInt64, h) := by
  simp [shr64, hn]

theorem fillBuf_size (A : Array UInt8) (x : UInt64) (i : Nat) : (fillBuf A x i).size = A.size := by
  induction i with
  | zero => rfl
  | succ i ih => simp [fillBuf, ih]

/-- The heap after `i` iterations of the restore loop. -/
def restoreHeap (H0 : Heap) (zs nb : Nat) (s0 : InflateState) (A : Array UInt8) (n i : Nat) : Heap :=
  { H0 with
    istates := upd H0.istates zs (some { s0 with hold := shr8N i s0.hold, bits := UInt32.ofNat (8 * (n - i)) }),
    bytes := upd H0.bytes nb (some (fillBuf A s0.hold i)) }

/-- **The restore loop.** `cond` and `body` are the loop of `inflateSync`; the hypotheses say what they do on the heap
`restoreHeap ... i`: the test is `bits >= 8`, the body stores the low byte of `hold` at `buf[len]`, shifts the buffer and
counts. -/
theorem restore_loop {cond : UInt32 → M (Bool × UInt32)} {body : UInt32 → M UInt32} {H0 : Heap} {zs nb : Nat}
    {s0 : InflateState} {A : Array UInt8} (n : Nat) (hn : n ≤ 4)
    (hc : ∀ i len, len = UInt32.ofNat i → i ≤ n → cond len (restoreHeap H0 zs nb s0 A n i) =
      .ok ((decide (i < n), len), restoreHeap H0 zs nb s0 A n i))
    (hb : ∀ i len, len = UInt32.ofNat i → i < n → body len (restoreHeap H0 zs nb s0 A n i) =
      .ok (len + 1, restoreHeap H0 zs nb s0 A n (i + 1))) :
    cwhile cond body 0 (restoreHeap H0 zs nb s0 A n 0) = .ok (UInt32.ofNat n, restoreHeap H0 zs nb s0 A n n) := by
  have key := cwhile_run (cond := cond) (body := body)
    (fun k len H => ∃ i, i + k = n ∧ len = UInt32.ofNat i ∧ H = restoreHeap H0 zs nb s0 A n i)
    (fun len H => len = UInt32.ofNat n ∧ H = restoreHeap H0 zs nb s0 A n n) ?_ ?_
    (k := n) (s := 0) (h := restoreHeap H0 zs nb s0 A n 0) ⟨0, by omega, rfl, rfl⟩ (by unfold fuel; omega)
  · obtain ⟨s', h', hh, hq1, hq2⟩ := key
    rw [hh, hq1, hq2]
  · intro k len H ⟨i, hi, hl, hH⟩
    subst hl; subst hH
    refine ⟨_, _, _, _, ?_, hb i _ rfl (by omega), i + 1, by omega, ?_, rfl⟩
    · rw [hc i _ rfl (by omega)]
      simp [show i < n by omega]
    · have : (UInt32.ofNat i + 1) = UInt32.ofNat (i + 1) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega),
          UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        simp; omega
      exact this
  · intro len H ⟨i, hi, hl, hH⟩
    subst hl; subst hH
    have : i = n := by omega
    subst this
    refine ⟨_, _, ?_, rfl, rfl⟩
    rw [hc i _ rfl (Nat.le_refl _)]
    simp

end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Spec
open C
/-- The state after the restore and the search of its bytes. -/
def syncFirstState (st : InflateState) : InflateState :=
  { st with «have» := (syncScan 0 (syncRestore st)).1, mode := SYNC, hold := shr8N (syncNB st) (syncHold0 st), bits := 0 }

/-- The heap after the restore and the search of its bytes (`buf` is the block `nb` with content `A`). -/
def syncFirstHeap (H0 : Heap) (zs nb : Nat) (st : InflateState) (A : Array UInt8) : Heap :=
  { H0 with bytes := upd H0.bytes nb (some (fillBuf A (syncHold0 st) (syncNB st))), istates := upd H0.istates zs (some (syncFirstState st)) }
end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate _root_.Zlib.Inflate.Spec

theorem syncHold0_eq (st : InflateState) : syncHold0 st = st.hold >>> (st.bits.toUInt64 &&& 7) := by
  unfold syncHold0
  congr 1

theorem fillBuf_get (A : Array UInt8) (x : UInt64) : ∀ i j, j < i → i ≤ A.size →
    (fillBuf A x i)[j]? = some (shr8N j x).toUInt8 := by
  intro i
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    intro j hj hi
    have hs := fillBuf_size A x i
    simp only [fillBuf, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hji : j = i
    · subst hji; simp [hs]; omega
    · have := ih j (by omega) (by omega)
      have hij : ¬ i = j := fun h => hji h.symm
      simpa [hij] using this

theorem syncBytes_fillBuf (A : Array UInt8) (x : UInt64) (n : Nat) (hn : n ≤ 4) (hA : A.size = 4) :
    syncBytes (fillBuf A x n) 0 (UInt32.ofNat n) = (List.range n).map fun j => (shr8N j x).toUInt8 := by
  have hs := fillBuf_size A x n
  unfold syncBytes
  rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · have := fillBuf_get A x n j hj (by omega)
    simp [List.getElem?_take, hj, List.getElem?_range]
    simpa using this
  · simp [List.getElem?_take, hj, List.getElem?_range]

theorem dec8 (m : Nat) (hm : m ≤ 4) : decide (8 ≤ UInt32.ofNat (8 * m)) = decide (0 < m) := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem ofNat_sub8 (m : Nat) (hm : m ≤ 4) (h1 : 1 ≤ m) : UInt32.ofNat (8 * m) - 8 = UInt32.ofNat (8 * (m - 1)) := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> first | (exfalso; omega) | decide

theorem bits_step (m : Nat) (hm : m ≤ 4) (h1 : 1 ≤ m) : 8 * UInt32.ofNat m - 8 = 8 * UInt32.ofNat (m - 1) := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> first | (exfalso; omega) | decide

theorem ofNat_succ (i : Nat) (hi : i ≤ 4) : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem syncFirst_run {H0 : Heap} {zs nb : Nat} {st : InflateState} {A : Array UInt8}
    (hs : H0.istates zs = some st) (hA : H0.bytes nb = some A) (hAs : A.size = 4) (hro : H0.ro nb = false)
    (hb39 : st.bits.toNat ≤ 39) :
    syncFirst (some (.tab zs)) (.ref (.blk nb) 0) st H0 = .ok ((), syncFirstHeap H0 zs nb st A) := by
  have h7 : (st.bits &&& 7) < 64 := by
    rw [UInt32.lt_iff_toNat_lt, sync_and7_toNat]; simp; omega
  have hbd := bitsDrop_toNat st.bits hb39
  unfold syncFirst
  isimp [hs, sync_shr64_run H0 _ _ h7]
  have hn4 : syncNB st ≤ 4 := by unfold syncNB; omega
  have hs0 : (setI H0 zs { st with mode := SYNC, hold := st.hold >>> (st.bits.toUInt64 &&& 7), bits := st.bits - (st.bits &&& 7) }) = restoreHeap H0 zs nb { st with mode := SYNC, hold := st.hold >>> (st.bits.toUInt64 &&& 7), bits := st.bits - (st.bits &&& 7) } A (syncNB st) 0 := by
    have hb8 : UInt32.ofNat (8 * syncNB st) = st.bits - (st.bits &&& 7) := by rw [hbd]; rfl
    unfold restoreHeap setI
    simp only [shr8N, Nat.sub_zero, fillBuf, upd_self _ _ _ hA, hb8]
  rw [hs0]
  rw [restore_loop (n := syncNB st) hn4 ?hc ?hb]
  case hc =>
    intro i len hl hi
    have hlt : decide (8 ≤ UInt32.ofNat (8 * (syncNB st - i))) = decide (i < syncNB st) := by
      rw [dec8 _ (by omega)]; simp; omega
    have hi : (restoreHeap H0 zs nb { st with mode := SYNC, hold := st.hold >>> (st.bits.toUInt64 &&& 7), bits := st.bits - (st.bits &&& 7) } A (syncNB st) i).istates zs = some { st with mode := SYNC, hold := shr8N i (st.hold >>> (st.bits.toUInt64 &&& 7)), bits := UInt32.ofNat (8 * (syncNB st - i)) } := by
      simp [restoreHeap]
    simp only [bind_app, pure_app, rdI_eq, hi, hlt]
  case hb =>
    intro i len hl hi
    have hlen : len.toNat = i := by rw [hl, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
    have hg : Space.get (restoreHeap H0 zs nb { st with mode := SYNC, hold := st.hold >>> (st.bits.toUInt64 &&& 7), bits := st.bits - (st.bits &&& 7) } A (syncNB st) i) (BRef.blk nb) = some (fillBuf A (st.hold >>> (st.bits.toUInt64 &&& 7)) i) := by
      simp [Space.get, restoreHeap]
    have hsz : (fillBuf A (st.hold >>> (st.bits.toUInt64 &&& 7)) i).size = 4 := by rw [fillBuf_size]; exact hAs
    have hadd := Ptr.add_nat_ok (r := BRef.blk nb) (off := 0) (n := i) hg (by omega)
    have hro' : Space.ro (restoreHeap H0 zs nb { st with mode := SYNC, hold := st.hold >>> (st.bits.toUInt64 &&& 7), bits := st.bits - (st.bits &&& 7) } A (syncNB st) i) (BRef.blk nb) = false := by
      simpa [Space.ro, restoreHeap] using hro
    have hstore := fun v => Ptr.store_ok (r := BRef.blk nb) (off := i) (v := v) hg hro' (by omega)
    have hi : (restoreHeap H0 zs nb { st with mode := SYNC, hold := st.hold >>> (st.bits.toUInt64 &&& 7), bits := st.bits - (st.bits &&& 7) } A (syncNB st) i).istates zs = some { st with mode := SYNC, hold := shr8N i (st.hold >>> (st.bits.toUInt64 &&& 7)), bits := UInt32.ofNat (8 * (syncNB st - i)) } := by
      simp [restoreHeap]
    have hsub := ofNat_sub8 (syncNB st - i) (by omega) (by omega)
    have hsu := ofNat_succ i (by omega)
    have hadd' := hadd
    unfold OkOn at hadd'
    simp only [Nat.zero_add] at hadd'
    simp only [bind_app, pure_app, ldI_eq, hi, hlen, hadd', store8, hstore, wrI_eq, Space.put]
    simp [restoreHeap, setI, upd_upd, fillBuf, shr8N, hsub, hsu, hsub, Nat.sub_sub]
    have e1 : 8 * UInt32.ofNat (syncNB st - i) - 8 = 8 * UInt32.ofNat (syncNB st - (i + 1)) := by
      rw [bits_step (syncNB st - i) (by omega) (by omega)]
      congr 2
    rw [e1]
  have hist : (restoreHeap H0 zs nb { st with mode := SYNC, hold := st.hold >>> (st.bits.toUInt64 &&& 7), bits := st.bits - (st.bits &&& 7) } A (syncNB st) (syncNB st)).istates zs = some { st with mode := SYNC, hold := shr8N (syncNB st) (st.hold >>> (st.bits.toUInt64 &&& 7)), bits := UInt32.ofNat (8 * (syncNB st - syncNB st)) } := by
    simp [restoreHeap]
  simp only [bind_app, pure_app, ldI_eq, hist, wrI_eq]
  have hsz : (fillBuf A (st.hold >>> (st.bits.toUInt64 &&& 7)) (syncNB st)).size = 4 := by rw [fillBuf_size]; exact hAs
  have hnn : (UInt32.ofNat (syncNB st)).toNat = syncNB st := UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  rw [syncsearch_run (r := BRef.blk nb) (a := fillBuf A (st.hold >>> (st.bits.toUInt64 &&& 7)) (syncNB st)) (o := 0)
    (len := UInt32.ofNat (syncNB st)) 0 (by simp [Space.get, restoreHeap, setI]) (by rw [hnn, hsz]; omega)]
  have hR : syncBytes (fillBuf A (st.hold >>> (st.bits.toUInt64 &&& 7)) (syncNB st)) 0 (UInt32.ofNat (syncNB st)) = syncRestore st := by
    rw [syncBytes_fillBuf _ _ _ hn4 hAs]
    unfold syncRestore; rw [syncHold0_eq]
  rw [hR]
  simp only [bind_app, pure_app, ldI_eq, setI_istates_same]
  simp [setI, restoreHeap, syncFirstHeap, syncFirstState, upd_upd, Nat.sub_self, syncHold0_eq]

theorem good_setBuf {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {nb : Nat} {a0 : Array UInt8}
    (hG : Good H r zs z st) (e : H.bytes nb = some a0) (hn : ∀ w, st.window = .ref (.blk w) 0 → w ≠ nb)
    (A : Array UInt8) : Good { H with bytes := upd H.bytes nb (some A) } r zs z st := by
  have hS := shape_setB e A
  obtain ⟨⟨hz, hs, zst, back, hm, za, zf⟩, ⟨wf, win, rq, bits, ptr⟩, hU, hF⟩ := hG
  refine ⟨⟨hz, hs, zst, back, hm, za, zf⟩, ⟨wf, ?_, rq, bits, ptr⟩, hS.uniq hU, hS.fresh rfl hF⟩
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with h0 | ⟨w, a, hw, ha, hro, hsz⟩
  · exact Or.inl h0
  · exact Or.inr ⟨w, a, hw, by rw [upd_ne _ _ _ _ (hn w hw)]; exact ha, hro, hsz⟩

theorem good_firstState {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {nb : Nat} {A : Array UInt8}
    (hG : Good H r zs z st) (e : H.bytes nb = some A) (hn : ∀ w, st.window = .ref (.blk w) 0 → w ≠ nb) :
    Good (syncFirstHeap H zs nb st A) r zs z (syncFirstState st) := by
  have h1 := good_setBuf hG e hn (fillBuf A (syncHold0 st) (syncNB st))
  have h2 := good_state h1 (st' := syncFirstState st) rfl (by simp [syncFirstState]; decide)
    (h1.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp [syncFirstState]) rfl rfl rfl)
  exact h2

theorem syncIn_first {h : Heap} (hF : Fresh h) {zs : Nat} {st : InflateState} {A : Array UInt8}
    {p : BPtr} {len : UInt32} {bs : List UInt8} (I : SyncIn h p len bs) :
    SyncIn (syncFirstHeap (syncAlloc h) zs h.nextBlk st A) p len bs := by
  rcases I with ⟨b, a, o, rfl, hg, hl, rfl⟩ | h2
  · have hb : b ≠ h.nextBlk := by
      intro hh; subst hh
      obtain ⟨e0, -⟩ := fresh_dead hF (Nat.le_refl _)
      rw [hg] at e0; cases e0
    exact Or.inl ⟨b, a, o, rfl, by simp [syncFirstHeap, syncAlloc, upd_ne _ _ _ _ hb, hg], hl, rfl⟩
  · exact Or.inr h2

theorem syncAt_restore (st : InflateState) : SyncAt (syncScan 0 (syncRestore st)).1 (syncRestore st) := by
  obtain ⟨-, h2, h3⟩ := syncScan_spec syncSt_zero (syncRestore st) rfl
  by_cases h4 : (syncScan 0 (syncRestore st)).1 = 4
  · right
    refine ⟨h4, ?_⟩
    obtain ⟨-, a, -⟩ := h2 h4
    have hin : [] ++ (syncRestore st).take (syncScan 0 (syncRestore st)).2 <:+: syncRestore st :=
      ⟨[], (syncRestore st).drop (syncScan 0 (syncRestore st)).2, by simp⟩
    exact (List.IsSuffix.isInfix a).trans (by simpa using hin)
  · left
    simpa using (h3 h4).2

/-- **inflateSync, first call** (`mode != SYNC`). The whole bytes of the bit buffer (`syncRestore st`: the bits below the next
byte boundary are dropped; at most 4 bytes, as the bit buffer holds at most 39 bits) are searched first, then the input
`next_in[0 .. avail_in)` (`SyncIn`), in the same state machine, so the pattern `00 00 FF FF` is found if it occurs in
`restore ++ input` (`syncScan_spec`; the search stops after its first occurrence and `N` counts input bytes only, 0 if the
pattern lies in the restored bytes). The state gets `mode = SYNC`, the bit buffer emptied (`hold` shifted, `bits = 0`) and `have`
set; the stream consumes `N` bytes. Not found (`G ≠ 4`): `Z_DATA_ERROR`, all input consumed. Found: `Z_OK` with the heap
`syncOkHeap` (reset, totals kept, mode `TYPE`). There must be input or a whole byte in the bit buffer (else `Z_BUF_ERROR`,
`inflateSync_buf_error`). The local array is made and freed. Default `zfree` only. -/
theorem inflateSync_first {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {bs : List UInt8}
    (hG : Good h r zs z st) (hf : z.zfree = .fn "zcfree") (hmode : st.mode ≠ SYNC)
    (hprog : ¬ (z.avail_in = 0 ∧ st.bits < 8)) (hI : SyncIn h z.next_in z.avail_in bs) :
    ∃ N G, N.toNat ≤ z.avail_in.toNat ∧
      (G = 4 → syncPat <:+: syncRestore st ++ bs.take N.toNat ∧ ∀ L', L' < N.toNat → ¬ syncPat <:+: syncRestore st ++ bs.take L') ∧
      (G ≠ 4 → N = z.avail_in ∧ SyncSt G (syncRestore st ++ bs)) ∧
      (G ≠ 4 → ∃ h', C.run (inflateSync (some r)) h = .ok (Z_DATA_ERROR, h') ∧
        h' = freeWin (setI (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk st (syncJunk h)) (syncAdvance z N)) zs
          (syncHave (syncFirstState st) G)) (syncBuf h) ∧
        Good h' r zs (syncAdvance z N) (syncHave (syncFirstState st) G)) ∧
      (G = 4 → ∃ h', C.run (inflateSync (some r)) h = .ok (Z_OK, h') ∧
        h' = freeWin (syncOkHeap (setI (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk st (syncJunk h)) (syncAdvance z N)) zs
          (syncHave (syncFirstState st) G)) r zs (syncAdvance z N) (syncHave (syncFirstState st) G)) (syncBuf h) ∧
        Good h' r zs (syncOkStream (syncAdvance z N) (syncHave (syncFirstState st) G))
          (syncOkState zs (syncHave (syncFirstState st) G))) := by
  have hF := hG.fresh
  have hG0 := good_syncAlloc hG
  have hwn := win_ne_buf hF hG.inv.win
  have hbb : (syncAlloc h).bytes h.nextBlk = some (syncJunk h) := syncAlloc_bytes_buf h
  have hAs : (syncJunk h).size = 4 := by simp [syncJunk]
  have hGf := good_firstState hG0 hbb hwn
  have hIf := syncIn_first (zs := zs) (st := st) (A := syncJunk h) hF hI
  have hL0 := hG0.live
  have hrun1 := syncFirst_run (H0 := syncAlloc h) (zs := zs) (nb := h.nextBlk) (st := st) (A := syncJunk h)
    (by simpa using hG.live.hs) hbb hAs (syncAlloc_ro_buf h) hG.inv.bits
  obtain ⟨N, G, hN, h4, h3, hG1, hne, he⟩ := syncTail_run hGf hf hIf (syncAt_restore st)
  have hnbf : (syncFirstHeap (syncAlloc h) zs h.nextBlk st (syncJunk h)).bytes h.nextBlk =
      some (fillBuf (syncJunk h) (syncHold0 st) (syncNB st)) := by simp [syncFirstHeap]
  have hrof : (syncFirstHeap (syncAlloc h) zs h.nextBlk st (syncJunk h)).ro h.nextBlk = false := by
    simp [syncFirstHeap, syncAlloc_ro_buf]
  refine ⟨N, G, hN, h4, h3, fun hG4 => ?_, fun hG4 => ?_⟩
  · refine ⟨_, ?_, rfl, ?_⟩
    · show inflateSync (some r) h = _
      rw [inflateSync_split]
      isimp [allocLocalB_run h hF, stateCheck_live hL0, hL0.zst, hG.live.hz, hG.live.hs, hprog, hmode, syncBuf, hrun1,
        hne hG4, freeBuf_run (H := setI (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk st (syncJunk h)) (syncAdvance z N)) zs
          (syncHave (syncFirstState st) G)) (nb := h.nextBlk) (a := fillBuf (syncJunk h) (syncHold0 st) (syncNB st))
          (by simpa using hnbf) (by simpa using hrof)]
    · exact good_freeBuf (nb := h.nextBlk) hG1 (fun w hw => hwn w (by simpa [syncHave, syncFirstState] using hw))
  · refine ⟨_, ?_, rfl, ?_⟩
    · have hbn : ∀ w', (syncHave (syncFirstState st) G).window = .ref (.blk w') 0 → w' ≠ h.nextBlk :=
        fun w' hw' => hwn w' (by simpa [syncHave, syncFirstState] using hw')
      have hby := syncOkHeap_bytes_ne (setI (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk st (syncJunk h)) (syncAdvance z N)) zs
        (syncHave (syncFirstState st) G)) r zs (syncAdvance z N) (syncHave (syncFirstState st) G) hbn
      show inflateSync (some r) h = _
      rw [inflateSync_split]
      isimp [allocLocalB_run h hF, stateCheck_live hL0, hL0.zst, hG.live.hz, hG.live.hs, hprog, hmode, syncBuf, hrun1,
        he hG4, freeBuf_run (H := syncOkHeap (setI (r.put (syncFirstHeap (syncAlloc h) zs h.nextBlk st (syncJunk h)) (syncAdvance z N)) zs
          (syncHave (syncFirstState st) G)) r zs (syncAdvance z N) (syncHave (syncFirstState st) G)) (nb := h.nextBlk)
          (a := fillBuf (syncJunk h) (syncHold0 st) (syncNB st))
          (by rw [hby.1]; simpa using hnbf) (by rw [hby.2]; simpa using hrof)]
    · have hGd := (syncDone_good hG1).1
      exact good_freeBuf (nb := h.nextBlk) hGd (fun w hw => hwn w (by simpa [syncHave, syncFirstState] using syncOkState_window_ref hw))

end Zlib.Inflate.Proofs
