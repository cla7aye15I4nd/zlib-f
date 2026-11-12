import ZlibF.Proof.«deflate.c.universal-ops-dispatch»
import ZlibF.Proof.«deflate.c.init.general-alloc»
import ZlibF.Proof.«deflate.c.engine.lminner»

/-!
# deflate.c: `deflateCopy` gives the destination the invariant (`copy_inv`)

A `deflateCopy` that returns `Z_OK` has run its success path: the state record and the four
buffers were allocated, the record and the stream were copied, the window up to `high_water`,
the first `cnt` slots of `prev`, all of `head`, the pending bytes and the symbol bytes were
copied, and the tree descriptors point to the new record. The failure paths return
`Z_STREAM_ERROR` or `Z_MEM_ERROR`, so `copy_inv` (which assumes `Z_OK`) does not meet them, and
`operation_step` has no `deflateCopy` case (`StreamOperation` does not contain it).

`prev` is copied only in part: `cnt = (slid || strstart - insert > w_size) ? w_size :
strstart - insert` slots. Every chain node the invariant follows lies below `chainTop ≤
strstart - insert`, so its slot is a copied one (`chains_copy`). Tested on the real C before the
proof: 21005 copies after histories with every level, window size, memory level and strategy,
slid and unslid windows, `insert > 0`, `deflateParams`, `deflateReset` and
`deflateSetDictionary`; no followed slot lay outside the copied part.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
open Zlib.Trees.Proofs.Out (setB)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The program in parts -/

/-- The four buffer requests of `deflateCopy` and their stores. -/
def copyBuffers (source : ZStreamPtr) (ds : DeflateStatePtr) (dd : DeflateState) :
    M (BPtr × WPtr × WPtr × BPtr) := do
  let window ← ZALLOC_bytes source dd.w_size 2
  wr ds (fun d => { d with window })
  let prev ← ZALLOC_words source dd.w_size
  wr ds (fun d => { d with prev })
  let head ← ZALLOC_words source dd.hash_size
  wr ds (fun d => { d with head })
  let pending_buf ← ZALLOC_bytes source dd.lit_bufsize 4
  wr ds (fun d => { d with pending_buf })
  pure (window, prev, head, pending_buf)

/-- The number of `prev` slots `deflateCopy` copies. -/
def copyCnt (sd dd : DeflateState) : UInt32 :=
  if sd.slid != 0 || sd.strstart - sd.insert > dd.w_size then dd.w_size else sd.strstart - sd.insert

/-- The success path after the buffer requests. -/
def copyTail (dest source : ZStreamPtr) (ss ds : DeflateStatePtr) (dd : DeflateState)
    (window : BPtr) (prev head : WPtr) (pending_buf : BPtr) : M Int32 := do
  copyZStream dest source
  zwr dest (fun z => { z with state := StateRef.ofDeflateState ds })
  wr ds (fun d => { d with strm := dest })
  let sd ← ldDeflateState ss
  memcpyB window sd.window sd.high_water.toNat
  let cnt : UInt32 := copyCnt sd dd
  Ptr.memcpy prev sd.prev cnt.toNat
  Ptr.memcpy head sd.head dd.hash_size.toNat
  let off ← Ptr.diff sd.pending_out sd.pending_buf
  let pending_out ← Ptr.add pending_buf off.toInt
  wr ds (fun d => { d with pending_out })
  memcpyB pending_out sd.pending_out sd.pending.toNat
  let sym_buf ← padd pending_buf dd.lit_bufsize.toNat
  wr ds (fun d => { d with sym_buf })
  memcpyB sym_buf sd.sym_buf sd.sym_next.toNat
  match ds with
  | none => ub "null deflate_state"
  | some (.tab id) =>
    wr ds (fun d => { d with l_desc := { d.l_desc with dyn_tree := .ref (.dstate_dyn_ltree id) 0 }, d_desc := { d.d_desc with dyn_tree := .ref (.dstate_dyn_dtree id) 0 }, bl_desc := { d.bl_desc with dyn_tree := .ref (.dstate_bl_tree id) 0 } })
  return Z_OK

/-- The null test and the cleanup after the buffer requests. -/
def copyFinish (dest source : ZStreamPtr) (ss ds : DeflateStatePtr) (dd : DeflateState)
    (ps : BPtr × WPtr × WPtr × BPtr) : M Int32 := do
  let (window, prev, head, pending_buf) := ps
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    if pending_buf != .null then ZFREE_bytes source pending_buf
    if head != .null then ZFREE_words source head
    if prev != .null then ZFREE_words source prev
    if window != .null then ZFREE_bytes source window
    zfree_default source
    freeDeflateState ds
    zwr dest (fun z => { z with state := none })
    return Z_MEM_ERROR
  copyTail dest source ss ds dd window prev head pending_buf

/-! ## Results other than `Z_OK` -/

/-- A computation that never returns `Z_OK`. -/
def NotOk (m : M Int32) : Prop := ∀ h H, m h ≠ .ok (Z_OK, H)

theorem notOk_pure {v : Int32} (ne : v ≠ Z_OK) : NotOk (pure v) := by
  intro h H e
  simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at e
  exact ne e.1

theorem notOk_bind {α : Type} {m : M α} {f : α → M Int32} (hf : ∀ a, NotOk (f a)) : NotOk (m >>= f) := by
  intro h H e
  rw [bind_app] at e
  split at e
  · exact hf _ _ _ e
  · cases e

theorem notOk_ite {c : Prop} [Decidable c] {a b : M Int32} (ha : NotOk a) (hb : NotOk b) :
    NotOk (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-! ## The buffer requests -/

def copyW (H : Heap) (d : DeflateState) : Heap := byteResult H (d.w_size * 2).toNat
def copyP (H : Heap) (d : DeflateState) : Heap := wordResult (copyW H d) ((d.w_size * 2).toNat / 2)
def copyQ (H : Heap) (d : DeflateState) : Heap := wordResult (copyP H d) ((d.hash_size * 2).toNat / 2)
def copyB (H : Heap) (d : DeflateState) : Heap := byteResult (copyQ H d) ((d.lit_bufsize * 4).toNat)

def copyBufState (H : Heap) (d : DeflateState) : DeflateState :=
  { d with window := bytePtr H, prev := wordPtr (copyW H d), head := wordPtr (copyP H d), pending_buf := bytePtr (copyQ H d) }

/-- Each of the four buffer requests executes even if an earlier one fails. -/
theorem copy_buffers_run {H : Heap} {r : ZStreamRef} {z : ZStream} {n : Nat} {d : DeflateState}
    (hf : Fresh H) (hz : r.get H = some z) (ha : z.zalloc = .fn "zcalloc")
    (hs : H.dstates n = some d) (hn : n < H.nextBlk) :
    copyBuffers (some r) (some (.tab n)) d H =
      .ok ((bytePtr H, wordPtr (copyW H d), wordPtr (copyP H d), bytePtr (copyQ H d)),
        setD (copyB H d) n (copyBufState H d)) := by
  let d1 := { d with window := bytePtr H }
  let H1 := setD (copyW H d) n d1
  let d2 := { d1 with prev := wordPtr (copyW H d) }
  let H2 := setD (copyP H d) n d2
  let d3 := { d2 with head := wordPtr (copyP H d) }
  let H3 := setD (copyQ H d) n d3
  have fW := fresh_byteResult hf ((d.w_size * 2).toNat)
  have fP := fresh_wordResult fW ((d.w_size * 2).toNat / 2)
  have fQ := fresh_wordResult fP ((d.hash_size * 2).toNat / 2)
  have pW := byteResult_next H ((d.w_size * 2).toNat)
  have pP := wordResult_next (copyW H d) ((d.w_size * 2).toNat / 2)
  have pQ := wordResult_next (copyP H d) ((d.hash_size * 2).toNat / 2)
  have hf1 : Fresh H1 := fresh_setD_below fW n (by dsimp only [copyW] at *; omega) d1
  have hf2 : Fresh H2 := fresh_setD_below fP n (by dsimp only [copyP, copyW] at *; omega) d2
  have hf3 : Fresh H3 := fresh_setD_below fQ n (by dsimp only [copyQ, copyP, copyW] at *; omega) d3
  have runW := bytes_run hf hz ha d.w_size 2
  have runP := words_run hf1 (r := r) (z := z) (by simpa [H1, copyW] using hz) ha d.w_size
  have runQ := words_run hf2 (r := r) (z := z) (by simpa [H2, copyP, copyW] using hz) ha d.hash_size
  have runB := bytes_run hf3 (r := r) (z := z) (by simpa [H3, copyQ, copyP, copyW] using hz) ha d.lit_bufsize 4
  change ZALLOC_bytes (some r) d.w_size 2 H = .ok (bytePtr H, copyW H d) at runW
  simp only [H1, H2, H3, copyP, copyQ, copyB, copyW, wordPtr_setD, bytePtr_setD, wordResult_setD,
    byteResult_setD] at runP runQ runB
  dsimp only [d1, d2, d3, copyP, copyQ, copyW] at runP runQ runB
  unfold copyBuffers
  rw [bind_app, runW]
  simp only [bind_app, wrD_eq, copyW, byteResult_dstates, hs, d1, d2, d3]
  rw [runP]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, d1, d2, d3]
  rw [runQ]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, d1, d2, d3]
  rw [runB]
  simp only [bind_app, wrD_eq, setD_dstates_same, setD_setD, pure_app, copyB, copyQ, copyP, copyW, copyBufState]

/-- The buffer requests inside `deflateCopy`, as `copyBuffers` followed by the rest. -/
theorem copyBuffers_bind (source : ZStreamPtr) (ds : DeflateStatePtr) (dd : DeflateState)
    (k : BPtr → WPtr → WPtr → BPtr → M Int32) :
    (do
      let window ← ZALLOC_bytes source dd.w_size 2
      wr ds (fun d => { d with window })
      let prev ← ZALLOC_words source dd.w_size
      wr ds (fun d => { d with prev })
      let head ← ZALLOC_words source dd.hash_size
      wr ds (fun d => { d with head })
      let pending_buf ← ZALLOC_bytes source dd.lit_bufsize 4
      wr ds (fun d => { d with pending_buf })
      k window prev head pending_buf) =
    (copyBuffers source ds dd >>= fun ps => k ps.1 ps.2.1 ps.2.2.1 ps.2.2.2) := by
  simp only [copyBuffers, C.M_bind_assoc, C.M_pure_bind]

/-! ## The partial copy of `prev` keeps the chains -/

/-- The chains survive new tables that agree with the old on every `head` entry, on the `prev`
slots below `cnt`, and on the window below `lim`, when every chain node below `top` has its slot
below `cnt`. -/
theorem chains_copy {h1 p1 h2 p2 : Nat → UInt16} {w1 w2 : Nat → UInt8} {n hsh hm : UInt32}
    {ws top lim cnt : Nat} (hc : HashChains h1 p1 w1 n hsh hm ws top lim)
    (heads : ∀ k, k < n.toNat → h2 k = h1 k)
    (slots : ∀ p, p < top → p &&& (ws - 1) < cnt)
    (prevs : ∀ i, i < cnt → p2 i = p1 i)
    (win : ∀ i, i < lim → w2 i = w1 i) : HashChains h2 p2 w2 n hsh hm ws top lim := by
  have back : ∀ k p, k < n.toNat → Reach h2 p2 ws top k p → Reach h1 p1 ws top k p := by
    intro k p hk hr
    induction hr with
    | head => rw [heads k hk]; exact Reach.head
    | step r hp ht ih =>
      obtain ⟨below, -, -, -⟩ := hc.node k _ hk ih hp ht
      rw [prevs _ (slots _ below)]
      exact Reach.step ih hp ht
  refine ⟨fun k p hk hr hp ht => ?_⟩
  have r1 := back k p hk hr
  obtain ⟨a1, a2, a3, a4⟩ := hc.node k p hk r1 hp ht
  refine ⟨a1, a2, ?_, by rw [prevs _ (slots _ a1)]; exact a4⟩
  rw [hkey_congr (w := w1) (p := p) (fun j hj => win _ (by omega))]
  exact a3

/-- The slot of a position below `cnt`, for both values of `cnt`. -/
theorem copy_slots {ws strstart insert top b : Nat} (pow : ws = 2 ^ b) (slid : Bool)
    (le : top ≤ strstart - insert) :
    ∀ p, p < top → p &&& (ws - 1) <
      (if slid ∨ ws < strstart - insert then ws else strstart - insert) := by
  intro p hp
  have mod : p &&& (ws - 1) = p % ws := by rw [pow, Nat.and_two_pow_sub_one_eq_mod]
  rw [mod]
  split
  · exact Nat.mod_lt _ (by rw [pow]; exact Nat.two_pow_pos b)
  · have := Nat.mod_le p ws; omega

/-! ## From `Z_OK` to the success path -/

theorem bind_ok {α β : Type} {m : M α} {f : α → M β} {h H : Heap} {v : β}
    (e : (m >>= f) h = .ok (v, H)) : ∃ a h1, m h = .ok (a, h1) ∧ f a h1 = .ok (v, H) := by
  rw [bind_app] at e
  cases hm : m h with
  | error err => rw [hm] at e; cases e
  | ok p => obtain ⟨a, h1⟩ := p; rw [hm] at e; exact ⟨a, h1, rfl, e⟩

/-- The heap after the state allocation and the record copy. -/
def copyH0 (h : Heap) (d : DeflateState) : Heap :=
  setD (stateHeap h (DeflateState.garbage (h.garbage h.nalloc))) h.nextBlk d

/-- **A `deflateCopy` that returns `Z_OK` ran its success path**: every allocation succeeded and
the tail ran from the heap after the buffer requests. -/
theorem copy_cut {h after : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (run : C.run (deflateCopy (some dest) (some source)) h = .ok (Z_OK, after)) :
    h.allocOk h.nalloc = true ∧ bytePtr (copyH0 h d) ≠ .null ∧ wordPtr (copyW (copyH0 h d) d) ≠ .null ∧
      wordPtr (copyP (copyH0 h d) d) ≠ .null ∧ bytePtr (copyQ (copyH0 h d) d) ≠ .null ∧
      copyTail (some dest) (some source) (some (.tab ds)) (some (.tab h.nextBlk)) d (bytePtr (copyH0 h d))
        (wordPtr (copyW (copyH0 h d) d)) (wordPtr (copyP (copyH0 h d) d)) (bytePtr (copyQ (copyH0 h d) d))
        (setD (copyB (copyH0 h d) d) h.nextBlk (copyBufState (copyH0 h d) d)) = .ok (Z_OK, after) := by
  have good := inv.good
  have hL := good.live
  have fresh := good.fresh
  rw [C.run] at run
  unfold deflateCopy at run
  simp only [show (some dest == (none : ZStreamPtr)) = false from rfl, Bool.false_eq_true, ↓reduceIte] at run
  obtain ⟨c, h1, e1, run⟩ := bind_ok run
  rw [stateCheck_live hL] at e1
  cases e1
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
  obtain ⟨st, h2, e2, run⟩ := bind_ok run
  rw [zrd_eq, hL.hz] at e2
  cases e2
  obtain ⟨ss, h3, e3, run⟩ := bind_ok run
  rw [hL.zst, castD] at e3
  cases e3
  obtain ⟨u, h4, e4, run⟩ := bind_ok run
  rw [allocator_run hL.hz inv.alloc.1] at e4
  cases e4
  obtain ⟨sp, h5, e5, run⟩ := bind_ok run
  by_cases ho : h.allocOk h.nalloc = true
  · rw [allocDeflateState_some ho (Heap.slotUsed_eq_false.mpr (fresh _ (Nat.le_refl _)))] at e5
    cases e5
    simp only [show (some (DeflateStateRef.tab h.nextBlk) == none) = false from rfl, Bool.false_eq_true,
      ↓reduceIte] at run
    obtain ⟨u, h6, e6, run⟩ := bind_ok run
    have dsLt : ds < h.nextBlk := by
      rcases Nat.lt_or_ge ds h.nextBlk with lt | ge
      · exact lt
      · exact absurd (owned_live good (Or.inl rfl)) (fresh ds ge)
    have ne : h.nextBlk ≠ ds := by omega
    have e6' : copyDeflateState (some (.tab h.nextBlk)) (some (.tab ds))
        (stateHeap h (DeflateState.garbage (h.garbage h.nalloc))) = .ok ((), copyH0 h d) := by
      simp [copyDeflateState, ne, bind_app, ldD_eq, stD_eq, stateHeap, upd_ne _ _ _ _ (Ne.symm ne), hL.hs, copyH0, setD]
    rw [show ({ h with dstates := upd h.dstates h.nextBlk (some (DeflateState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 } : Heap) = stateHeap h (DeflateState.garbage (h.garbage h.nalloc)) from rfl, e6'] at e6
    cases e6
    obtain ⟨dd, h7, e7, run⟩ := bind_ok run
    have hs7 : (copyH0 h d).dstates h.nextBlk = some d := by simp [copyH0]
    rw [ldD_eq, hs7] at e7
    cases e7
    rw [copyBuffers_bind] at run
    obtain ⟨ps, h8, e8, run⟩ := bind_ok run
    have freshH : Fresh (copyH0 h d) :=
      fresh_setD_below (fresh_stateHeap fresh _) h.nextBlk (by simp [stateHeap]) d
    have hzH : source.get (copyH0 h d) = some z := by simp [copyH0, hL.hz]
    have hsH : (copyH0 h d).dstates h.nextBlk = some d := by simp [copyH0]
    rw [copy_buffers_run freshH hzH inv.alloc.1 hsH (by simp [copyH0, stateHeap])] at e8
    cases e8
    simp only at run
    split at run
    · exfalso
      refine (?_ : NotOk _) _ _ run
      repeat' (first | exact notOk_pure (by decide) | apply notOk_ite | (apply notOk_bind; intro))
    · rename_i nonnull
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at nonnull
      obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := nonnull
      exact ⟨ho, n1, n2, n3, n4, run⟩
  · exfalso
    rw [allocDeflateState_none ho] at e5
    cases e5
    simp only [show (none == (none : DeflateStatePtr)) = true from rfl, ↓reduceIte] at run
    refine (?_ : NotOk _) _ _ run
    repeat' (first | exact notOk_pure (by decide) | apply notOk_ite | (apply notOk_bind; intro))

/-! ## The success path after the buffer requests -/

/-- The state record of the copy. -/
def copyState (d : DeflateState) (dest : ZStreamRef) (n W P Q B off : Nat) : DeflateState :=
  { d with window := .ref (.blk W) 0, prev := .ref (.blk P) 0, head := .ref (.blk Q) 0, pending_buf := .ref (.blk B) 0, strm := some dest, pending_out := .ref (.blk B) off, sym_buf := .ref (.blk B) d.lit_bufsize.toNat, l_desc := { d.l_desc with dyn_tree := .ref (.dstate_dyn_ltree n) 0 }, d_desc := { d.d_desc with dyn_tree := .ref (.dstate_dyn_dtree n) 0 }, bl_desc := { d.bl_desc with dyn_tree := .ref (.dstate_bl_tree n) 0 } }

/-- The window of the copy. -/
def copyWin (aW wa : Array UInt8) (d : DeflateState) : Array UInt8 := copyRange aW wa 0 0 d.high_water.toNat
/-- The `prev` table of the copy. -/
def copyPrev (aP pa : Array UInt16) (d : DeflateState) : Array UInt16 := copyRange aP pa 0 0 (copyCnt d d).toNat
/-- The `head` table of the copy. -/
def copyHead (aQ qa : Array UInt16) (d : DeflateState) : Array UInt16 := copyRange aQ qa 0 0 d.hash_size.toNat
/-- The pending buffer of the copy: the pending bytes, then the symbols. -/
def copyPend (aB ba : Array UInt8) (d : DeflateState) (off : Nat) : Array UInt8 :=
  copyRange (copyRange aB ba off off d.pending.toNat) ba d.lit_bufsize.toNat d.lit_bufsize.toNat d.sym_next.toNat

/-- The heap after the success path. -/
def copyFinal (T0 : Heap) (dest : ZStreamRef) (z : ZStream) (d : DeflateState) (n W P Q B off : Nat)
    (aW wa aB ba : Array UInt8) (aP pa aQ qa : Array UInt16) : Heap :=
  setD (setB (setW (setW (setB (dest.put T0 { z with state := StateRef.ofDeflateState (some (.tab n)) }) W (copyWin aW wa d)) P (copyPrev aP pa d)) Q (copyHead aQ qa d)) B (copyPend aB ba d off)) n (copyState d dest n W P Q B off)

theorem copyCnt_le (d : DeflateState) (le : d.insert.toNat ≤ d.strstart.toNat) :
    (copyCnt d d).toNat ≤ d.w_size.toNat := by
  unfold copyCnt
  split
  · exact Nat.le_refl _
  · rename_i c
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, Decidable.not_not] at c
    have c2 : ¬ (d.w_size < d.strstart - d.insert) := c.2
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr le)] at c2
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr le)]
    omega

set_option maxRecDepth 20000 in
/-- **The success path** from the heap after the buffer requests. -/
theorem copy_tail_run {T0 : Heap} {source dest : ZStreamRef} {z zd : ZStream} {ds n w p q b W P Q B off : Nat}
    {d : DeflateState} {wa ba aW aB : Array UInt8} {pa qa aP aQ : Array UInt16}
    (hne : dest ≠ source) (hz : source.get T0 = some z) (hzd : dest.get T0 = some zd)
    (hsd : T0.dstates ds = some d) (dsn : ds ≠ n)
    (hsn : T0.dstates n = some { d with window := .ref (.blk W) 0, prev := .ref (.blk P) 0, head := .ref (.blk Q) 0, pending_buf := .ref (.blk B) 0 })
    (win : d.window = .ref (.blk w) 0) (prv : d.prev = .ref (.blk p) 0) (hd : d.head = .ref (.blk q) 0)
    (pb : d.pending_buf = .ref (.blk b) 0) (pout : d.pending_out = .ref (.blk b) off)
    (sym : d.sym_buf = .ref (.blk b) d.lit_bufsize.toNat)
    (gw : T0.bytes w = some wa) (gp : T0.words p = some pa) (gq : T0.words q = some qa) (gb : T0.bytes b = some ba)
    (gW : T0.bytes W = some aW) (gP : T0.words P = some aP) (gQ : T0.words Q = some aQ) (gB : T0.bytes B = some aB)
    (roW : T0.ro W = false) (roB : T0.ro B = false)
    (Ww : W ≠ w) (Wb : W ≠ b) (WB : W ≠ B) (Bb : B ≠ b) (Pp : P ≠ p) (Pq : P ≠ q) (PQ : P ≠ Q) (Qq : Q ≠ q)
    (sW : d.high_water.toNat ≤ aW.size) (sw : d.high_water.toNat ≤ wa.size)
    (sP : (copyCnt d d).toNat ≤ aP.size) (sp : (copyCnt d d).toNat ≤ pa.size)
    (sQ : d.hash_size.toNat ≤ aQ.size) (sq : d.hash_size.toNat ≤ qa.size)
    (sB1 : off + d.pending.toNat ≤ aB.size) (sb1 : off + d.pending.toNat ≤ ba.size)
    (sB2 : d.lit_bufsize.toNat + d.sym_next.toNat ≤ aB.size) (sb2 : d.lit_bufsize.toNat + d.sym_next.toNat ≤ ba.size)
    (offLt : off < 2 ^ 62) :
    copyTail (some dest) (some source) (some (.tab ds)) (some (.tab n)) d (.ref (.blk W) 0) (.ref (.blk P) 0)
      (.ref (.blk Q) 0) (.ref (.blk B) 0) T0 =
      .ok (Z_OK, copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa) := by
  have nd : n ≠ ds := Ne.symm dsn
  unfold copyTail
  -- copyZStream
  have s1 : copyZStream (some dest) (some source) T0 = .ok ((), dest.put T0 z) := by
    simp [copyZStream, hne, bind_app, ldZ_eq, stZ_eq, hz, hzd]
  rw [bind_app, s1]
  simp only []
  -- the state pointer of the destination
  rw [bind_app, zwr_eq, ZStreamRef.get_put_same hzd]
  simp only [ZStreamRef.put_put]
  -- strm
  rw [bind_app, wrD_eq]
  simp only [ZStreamRef.put_dstates, hsn]
  -- sd
  rw [bind_app, ldD_eq]
  simp only [setD_dstates_ne _ _ _ _ dsn, ZStreamRef.put_dstates, hsd]
  -- the window
  rw [bind_app, win]
  rw [memcpyB_blk_ok (ob := aW) (pbuf := wa) (by simp [setD, gW]) (by simp [setD, gw]) (by simp [setD, roW]) Ww
    (by simpa using sW) (by simpa using sw)]
  simp only []
  -- prev
  rw [bind_app, prv]
  rw [Ptr.memcpy_ok (rd := WRef.blk P) (rs := WRef.blk p) (da := aP) (sa := pa)
    (by show (_ : Heap).words P = _; simp [setD, gP]) (by show (_ : Heap).words p = _; simp [setD, gp]) rfl
    (by simpa using sP) (by simpa using sp) (Or.inl (fun e => Pp (WRef.blk.inj e)))]
  simp only []
  -- head
  rw [bind_app, hd]
  rw [Ptr.memcpy_ok (rd := WRef.blk Q) (rs := WRef.blk q) (da := aQ) (sa := qa)
    (by show (_ : Heap).words Q = _; simp [setD, Space_put_words, setW, upd_ne _ _ _ _ (Ne.symm PQ), gQ])
    (by show (_ : Heap).words q = _; simp [setD, Space_put_words, setW, upd_ne _ _ _ _ (Ne.symm Pq), gq]) rfl
    (by simpa using sQ) (by simpa using sq) (Or.inl (fun e => Qq (WRef.blk.inj e)))]
  simp only []
  -- the offset of pending_out
  rw [bind_app, pout, pb]
  rw [Ptr.diff_ok (r := BRef.blk b) (a := ba)
    (by show (_ : Heap).bytes b = _; simp [setD, Space_put_words, setW, upd_ne _ _ _ _ (Ne.symm Wb), gb])
    (by omega) (by omega) (by omega)]
  simp only []
  rw [bind_app]
  have offInt : (Int64.ofInt ((off : Int) - ((0 : Nat) : Int))).toInt = (off : Int) := by
    rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]; omega
  rw [offInt, Ptr.add_ok (r := BRef.blk B) (a := aB)
    (by show (_ : Heap).bytes B = _; simp [setD, Space_put_words, setW, upd_ne _ _ _ _ (Ne.symm WB), gB])
    (by omega) (by omega)]
  simp only [show ((0 : Nat) : Int) + (off : Int) = (off : Int) by omega, Int.toNat_natCast]
  -- pending_out
  rw [bind_app, wrD_eq]
  simp only [Space_put_words, setW_dstates, setD_dstates_same]
  -- the pending bytes
  try rw [bind_app]
  rw [memcpyB_blk_ok (ob := aB) (pbuf := ba)
    (by simp [setD, Space_put_words, setW, upd_ne _ _ _ _ (Ne.symm WB), gB])
    (by simp [setD, Space_put_words, setW, upd_ne _ _ _ _ (Ne.symm Wb), gb])
    (by simp [setD, Space_put_words, setW, roB]) Bb (by omega) (by omega)]
  simp only []
  -- sym_buf
  have sizeB1 : (copyRange aB ba off off d.pending.toNat).size = aB.size := size_copyRange _ _ _ _ _
  have hpadd : ∀ X : Heap, X.bytes B = some (copyRange aB ba off off d.pending.toNat) →
      padd (.ref (.blk B) 0 : BPtr) d.lit_bufsize.toNat X = .ok (.ref (.blk B) d.lit_bufsize.toNat, X) := by
    intro X hX
    have := Ptr.add_nat_ok (r := BRef.blk B) (a := copyRange aB ba off off d.pending.toNat) (off := 0)
      (n := d.lit_bufsize.toNat) (h := X) hX (by omega)
    simpa [padd, OkOn] using this
  try rw [bind_app]
  rw [hpadd _ (by simp [setD])]
  simp only []
  try rw [bind_app]
  rw [wrD_eq]
  simp only [setD_dstates_same]
  -- the symbols
  try rw [bind_app]
  rw [sym]
  rw [memcpyB_blk_ok (ob := copyRange aB ba off off d.pending.toNat) (pbuf := ba)
    (by simp [setD]) (by simp [setD, Space_put_words, setW, upd_ne _ _ _ _ (Ne.symm Bb), upd_ne _ _ _ _ (Ne.symm Wb), gb])
    (by simp [setD, Space_put_words, setW, roB]) Bb (by omega) (by omega)]
  simp only []
  -- the tree descriptors
  try rw [bind_app]
  rw [wrD_eq]
  simp only [setD_dstates_same, pure_app]
  simp only [copyFinal, copyState, copyWin, copyPrev, copyHead, copyPend, setD, setB, setW, Space_put_words,
    upd_upd, copyCnt]


/-! ## Array facts of the copies -/

theorem getD_copy_in {T : Type} [Inhabited T] (a s : Array T) (o n i : Nat) (z0 : T) (hi1 : o ≤ i)
    (hi2 : i < o + n) (ha : o + n ≤ a.size) (hs : o + n ≤ s.size) :
    (copyRange a s o o n).getD i z0 = s.getD i z0 := by
  have e : o + (i - o) = i := by omega
  simp only [Array.getD_eq_getD_getElem?, getElem?_copyRange _ _ _ _ _ _ ha, if_pos (And.intro hi1 hi2), e,
    Array.getElem?_eq_getElem (show i < s.size by omega), Option.getD_some]
  all_goals exact getElem!_pos s i (by omega)

theorem getD_copy_out {T : Type} [Inhabited T] (a s : Array T) (o n i : Nat) (z0 : T)
    (hi : i < o ∨ o + n ≤ i) (ha : o + n ≤ a.size) :
    (copyRange a s o o n).getD i z0 = a.getD i z0 := by
  simp only [Array.getD_eq_getD_getElem?, getElem?_copyRange _ _ _ _ _ _ ha, if_neg (show ¬ (o ≤ i ∧ i < o + n) by omega)]

theorem get_setB' (X : Heap) (r : ZStreamRef) (b : Nat) (a : Array UInt8) : r.get (setB X b a) = r.get X := by
  cases r <;> rfl
theorem get_setW' (X : Heap) (r : ZStreamRef) (q : Nat) (a : Array UInt16) : r.get (setW X q a) = r.get X := by
  cases r <;> rfl

/-- `copyCnt` covers every chain node below the insertion frontier. -/
theorem copyCnt_cover (d : DeflateState) (le : d.insert.toNat ≤ d.strstart.toNat) :
    (copyCnt d d).toNat = d.w_size.toNat ∨ d.strstart.toNat - d.insert.toNat ≤ (copyCnt d d).toNat := by
  unfold copyCnt
  split
  · exact Or.inl rfl
  · right
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr le)]
    exact Nat.le_refl _

theorem slots_of_cover {ws b top cnt : Nat} (pow : ws = 2 ^ b)
    (cover : cnt = ws ∨ top ≤ cnt) : ∀ p, p < top → p &&& (ws - 1) < cnt := by
  intro p hp
  have mod : p &&& (ws - 1) = p % ws := by rw [pow, Nat.and_two_pow_sub_one_eq_mod]
  rw [mod]
  rcases cover with e | le
  · rw [e]; exact Nat.mod_lt _ (by rw [pow]; exact Nat.two_pow_pos b)
  · have := Nat.mod_le p ws; omega

/-- **The invariant of the copy**, from the heap after the buffer requests. -/
theorem copy_final_inv {h T0 : Heap} {source dest : ZStreamRef} {ds n w p q b W P Q B off : Nat}
    {z zd : ZStream} {d : DeflateState} {wa ba aW aB : Array UInt8} {pa qa aP aQ : Array UInt16}
    (inv : DInv h source ds z d) (blocks : DBlocks h d w p q b)
    (gw : h.bytes w = some wa) (gp : h.words p = some pa) (gq : h.words q = some qa) (gb : h.bytes b = some ba)
    (pout : d.pending_out = .ref (.blk b) off) (offFit : off + d.pending.toNat ≤ d.pending_buf_size.toNat)
    (fT0 : Fresh T0) (uT0 : Uniq T0) (stT0 : T0.static = h.static) (hzd0 : dest.get T0 = some zd)
    {d0 : DeflateState} (hsn0 : T0.dstates n = some d0)
    (gW : T0.bytes W = some aW) (gP : T0.words P = some aP) (gQ : T0.words Q = some aQ) (gB : T0.bytes B = some aB)
    (roW : T0.ro W = false) (roB : T0.ro B = false)
    (sAW : aW.size = 2 * d.w_size.toNat) (sAP : aP.size = d.w_size.toNat) (sAQ : aQ.size = d.hash_size.toNat)
    (sAB : aB.size = 4 * d.lit_bufsize.toNat) (WB : W ≠ B) (PQ : P ≠ Q) :
    DInv (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa) dest n
      { z with state := StateRef.ofDeflateState (some (.tab n)) } (copyState d dest n W P Q B off) := by
  have good := inv.good
  have hL := good.live
  have I := good.inv
  obtain ⟨tb, tbuf, tree⟩ : ∃ tb tbuf, Zlib.Trees.Proofs.Out.TreesInvAt h ds d tb tbuf := by
    obtain ⟨d0, tb, tbuf, t⟩ := good.trees
    have e0 : d0 = d := Option.some.inj (t.base.dstate.symm.trans hL.hs)
    subst e0
    exact ⟨tb, tbuf, t⟩
  have swa := blocks.wa
  obtain ⟨wa', gw', swa⟩ := swa
  rw [gw] at gw'; cases gw'
  obtain ⟨pa', gp', spa⟩ := blocks.pa
  rw [gp] at gp'; cases gp'
  obtain ⟨qa', gq', sqa⟩ := blocks.qa
  rw [gq] at gq'; cases gq'
  obtain ⟨ba', gb', sba⟩ := blocks.ba
  rw [gb] at gb'; cases gb'
  have wsz : d.w_size.toNat ≤ 32768 := by
    have := I.wsize
    have : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) I.wbits_hi
    omega
  have litHi := tree.base.lit_hi
  have symEnd := tree.base.sym_end
  obtain ⟨-, -, symLe, symMod⟩ := I.sym
  have psz := blocks.psize
  have insLe := inv.shape.insert
  have cntLe := copyCnt_le d insLe
  have hwLe : d.high_water.toNat ≤ 2 * d.w_size.toNat := by have := I.hw; have := I.wsz; omega
  have winInit := inv.shape.windowInit
  -- the arrays of the copy
  have sWin : (copyWin aW wa d).size = 2 * d.w_size.toNat := by simp [copyWin, size_copyRange, sAW]
  have sPrev : (copyPrev aP pa d).size = d.w_size.toNat := by simp [copyPrev, size_copyRange, sAP]
  have sHead : (copyHead aQ qa d).size = d.hash_size.toNat := by simp [copyHead, size_copyRange, sAQ]
  have sPend : (copyPend aB ba d off).size = 4 * d.lit_bufsize.toNat := by simp [copyPend, size_copyRange, sAB]
  have win : ∀ i, i < d.high_water.toNat → bfn (copyWin aW wa d) i = bfn wa i := by
    intro i hi
    exact getD_copy_in aW wa 0 _ i 0 (Nat.zero_le _) (by omega) (by omega) (by omega)
  have prevs : ∀ i, i < (copyCnt d d).toNat → wfn (copyPrev aP pa d) i = wfn pa i := by
    intro i hi
    exact getD_copy_in aP pa 0 _ i 0 (Nat.zero_le _) (by omega) (by omega) (by omega)
  have heads : ∀ k, k < d.hash_size.toNat → wfn (copyHead aQ qa d) k = wfn qa k := by
    intro k hk
    exact getD_copy_in aQ qa 0 _ k 0 (Nat.zero_le _) (by omega) (by omega) (by omega)
  have syms : ∀ i, d.lit_bufsize.toNat ≤ i → i < d.lit_bufsize.toNat + d.sym_next.toNat →
      bfn (copyPend aB ba d off) i = bfn ba i := by
    intro i h1 h2
    exact getD_copy_in _ ba _ _ i 0 h1 h2 (by rw [size_copyRange]; omega) (by omega)
  -- the heap of the copy
  have zF : dest.get (dest.put T0 { z with state := StateRef.ofDeflateState (some (.tab n)) }) =
      some { z with state := StateRef.ofDeflateState (some (.tab n)) } := ZStreamRef.get_put_same hzd0 _
  have hz : dest.get (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa) =
      some { z with state := StateRef.ofDeflateState (some (.tab n)) } := by
    simp only [copyFinal, ZStreamRef.get_setD, get_setB', get_setW', zF]
  have hs : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).dstates n =
      some (copyState d dest n W P Q B off) := by simp [copyFinal]
  have hW : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).bytes W = some (copyWin aW wa d) := by
    simp [copyFinal, setD, setB, setW, upd_ne _ _ _ _ WB]
  have hP : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).words P = some (copyPrev aP pa d) := by
    simp [copyFinal, setD, setB, setW, upd_ne _ _ _ _ PQ]
  have hQ : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).words Q = some (copyHead aQ qa d) := by
    simp [copyFinal, setD, setB, setW]
  have hB : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).bytes B = some (copyPend aB ba d off) := by
    simp [copyFinal, setD, setB, setW]
  have rW : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).ro W = false := by
    simp [copyFinal, setD, setB, setW, roW]
  have rB : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).ro B = false := by
    simp [copyFinal, setD, setB, setW, roB]
  have st : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).static = h.static := by
    simp [copyFinal, setD, setB, setW, stT0]
  have shape : Zlib.Deflate.Proofs.Shape T0 (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa) := by
    have s1 := shape_put hzd0 { z with state := StateRef.ofDeflateState (some (.tab n)) }
    have s2 := shape_setB (h := dest.put T0 { z with state := StateRef.ofDeflateState (some (.tab n)) })
      (w := W) (a0 := aW) (by simpa using gW) (copyWin aW wa d)
    have s3 := shape_setW (h := setB (dest.put T0 { z with state := StateRef.ofDeflateState (some (.tab n)) }) W
      (copyWin aW wa d)) (w := P) (a0 := aP) (by simpa [setB] using gP) (copyPrev aP pa d)
    have s4 := shape_setW (h := setW (setB (dest.put T0 { z with state := StateRef.ofDeflateState (some (.tab n)) }) W
      (copyWin aW wa d)) P (copyPrev aP pa d)) (w := Q) (a0 := aQ) (by simpa [setB, setW, upd_ne _ _ _ _ (Ne.symm PQ)] using gQ)
      (copyHead aQ qa d)
    have s5 := shape_setB (h := setW (setW (setB (dest.put T0 { z with state := StateRef.ofDeflateState (some (.tab n)) }) W
      (copyWin aW wa d)) P (copyPrev aP pa d)) Q (copyHead aQ qa d))
      (w := B) (a0 := aB) (by simpa [setB, setW, upd_ne _ _ _ _ (Ne.symm WB)] using gB) (copyPend aB ba d off)
    have s6 := shape_setD (h := setB (setW (setW (setB (dest.put T0 { z with state := StateRef.ofDeflateState (some (.tab n)) }) W
      (copyWin aW wa d)) P (copyPrev aP pa d)) Q (copyHead aQ qa d)) B (copyPend aB ba d off))
      (by simpa [setB, setW] using hsn0) (copyState d dest n W P Q B off)
    exact ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6
  have nb : (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa).nextBlk = T0.nextBlk := by
    simp [copyFinal, setD, setB, setW]
  have blocksF : DBlocks (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa)
      (copyState d dest n W P Q B off) W P Q B :=
    { win := rfl, prev := rfl, head := rfl, pbuf := rfl, wa := ⟨_, hW, sWin⟩, wro := rW,
      pa := ⟨_, hP, sPrev⟩, qa := ⟨_, hQ, sHead⟩, ba := ⟨_, hB, sPend⟩, bro := rB, psize := psz,
      wb := WB, pq := PQ, pout := ⟨off, rfl, offFit⟩ }
  have treesF : Zlib.Trees.Proofs.Out.TreesInvAt (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa) n
      (copyState d dest n W P Q B off) B (copyPend aB ba d off) :=
    ⟨{ dstate := hs, wf := I.wf, static := by rw [st]; exact tree.base.static, pbuf := rfl, bytes := hB,
        rw := rB, size := sPend, psize := by rw [sPend]; exact psz, sym := rfl, lit_lo := tree.base.lit_lo,
        lit_hi := tree.base.lit_hi, sym_end := tree.base.sym_end, pending_le := tree.base.pending_le },
      { ldyn := rfl, lstat := tree.run.lstat, ddyn := rfl, dstat := tree.run.dstat, bldyn := rfl,
        blstat := tree.run.blstat, bi_lo := tree.run.bi_lo, bi_hi := tree.run.bi_hi, bi_buf := tree.run.bi_buf,
        sym_next_le := tree.run.sym_next_le, sym_next_mod := tree.run.sym_next_mod }⟩
  have goodF : DGood (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa) dest n
      { z with state := StateRef.ofDeflateState (some (.tab n)) } (copyState d dest n W P Q B off) :=
    ⟨⟨hz, hs, rfl, rfl, hL.status, hL.zalloc, hL.zfree⟩,
      { I with blocks := ⟨W, P, Q, B, blocksF⟩, sym := ⟨⟨B, rfl, rfl⟩, I.sym.2.1, symLe, symMod⟩, gz := gzOk_any _ _ },
      shape.uniq uT0, shape.fresh nb fT0, ⟨_, B, _, treesF⟩⟩
  -- the chains
  have cover := copyCnt_cover d insLe
  have pow := I.wsize
  refine ⟨goodF, inv.alloc, by unfold LibraryGlobals at *; rw [st]; exact inv.globals,
    { inv.shape with cursor := fun hp => ?_ }, ⟨fun zero => ?_, fun one => ?_, fun s2 s3 three => ?_⟩, ?_⟩
  · have c := inv.shape.cursor hp
    rw [pout, blocks.pbuf] at c
    cases c
    rfl
  · obtain ⟨w', p', q', wa', pa', qa', ew, ep, eq, hw, hp, hq, H⟩ := inv.hashing.chains zero
    rw [blocks.win] at ew; cases ew
    rw [blocks.prev] at ep; cases ep
    rw [blocks.head] at eq; cases eq
    rw [gw] at hw; cases hw
    rw [gp] at hp; cases hp
    rw [gq] at hq; cases hq
    refine ⟨W, P, Q, _, _, _, rfl, rfl, rfl, hW, hP, hQ, chains_copy H heads ?_ prevs ?_⟩
    · exact slots_of_cover pow (cover.imp id (fun le => Nat.le_trans (chainTop_le d) le))
    · intro i hi; exact win i (by simp only [copyState] at hi; omega)
  · obtain ⟨w', p', q', wa', pa', qa', ew, ep, eq, hw, hp, hq, H⟩ := inv.hashing.slid one
    rw [blocks.win] at ew; cases ew
    rw [blocks.prev] at ep; cases ep
    rw [blocks.head] at eq; cases eq
    rw [gw] at hw; cases hw
    rw [gp] at hp; cases hp
    rw [gq] at hq; cases hq
    refine ⟨W, P, Q, _, _, _, rfl, rfl, rfl, hW, hP, hQ, chains_copy H ?_ (slots_of_cover pow cover) ?_ ?_⟩
    · intro k hk; show slideVal _ (wfn _ k) = slideVal _ (wfn _ k); rw [heads k hk]; rfl
    · intro i hi; show slideVal _ (wfn _ i) = slideVal _ (wfn _ i); rw [prevs i hi]; rfl
    · intro i hi; exact win i (by simp only [copyState] at hi; omega)
  · obtain ⟨w', wa', ew, hw, form⟩ := inv.hashing.rolling s2 s3 three
    rw [blocks.win] at ew; cases ew
    rw [gw] at hw; cases hw
    refine ⟨W, _, rfl, hW, ?_⟩
    simp only [copyState] at three
    obtain ⟨y, e⟩ := form
    refine ⟨y, ?_⟩
    simp only [copyState]
    rw [win _ (by omega), win _ (by omega)]
    exact e
  · obtain ⟨⟨xs, ⟨b', a', pb', hb', ledger⟩, dist⟩, clear, below⟩ := inv.symbols
    rw [blocks.pbuf] at pb'; cases pb'
    rw [gb] at hb'; cases hb'
    refine ⟨⟨xs, ⟨B, _, rfl, hB, ⟨ledger.count, ledger.valid, ?_, ledger.literal, ledger.distance⟩⟩, dist⟩,
      ⟨clear.bl, clear.opt, clear.fixed⟩, fun b'' o e nz => ?_⟩
    · intro i s sel
      simp only [copyState]
      have lt : i < xs.length := by
        rcases Nat.lt_or_ge i xs.length with lt | ge
        · exact lt
        · simp [List.getElem?_eq_none ge] at sel
      have cnt := ledger.count
      obtain ⟨e1, e2, e3⟩ := ledger.packed i s sel
      refine ⟨?_, ?_, ?_⟩
      · rw [syms _ (by omega) (by omega)]; exact e1
      · rw [syms _ (by omega) (by omega)]; exact e2
      · rw [syms _ (by omega) (by omega)]; exact e3
    · cases e
      exact below b off pout nz

/-! ## The invariant of the copy -/

/-- `deflateCopy` into a distinct destination establishes the invariant there, for a state record
with the status, the symbol count and the header record of the source. -/
theorem copy_result {h after : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (run : C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h = .ok (Z_OK, after)) :
    ∃ ds' z' d', DInv after dest ds' z' d' ∧ d'.status = d.status ∧ d'.sym_next = d.sym_next ∧
      d'.gzhead = d.gzhead := by
  obtain ⟨ho, n1, n2, n3, n4, tail⟩ := copy_cut inv distinct get run
  have good := inv.good
  have hL := good.live
  have fresh := good.fresh
  have I := good.inv
  obtain ⟨w, p, q, b, blocks⟩ := I.blocks
  obtain ⟨wa, gw, swa⟩ := blocks.wa
  obtain ⟨pa, gp, spa⟩ := blocks.pa
  obtain ⟨qa, gq, sqa⟩ := blocks.qa
  obtain ⟨ba, gb, sba⟩ := blocks.ba
  obtain ⟨off, pout, offFit⟩ := blocks.pout
  have psz := blocks.psize
  have below : ∀ x, h.live x → x < h.nextBlk := fun x l => by
    rcases Nat.lt_or_ge x h.nextBlk with lt | ge
    · exact lt
    · exact absurd l (fresh x ge)
  have wlt := below w (owned_live good (Or.inr (Or.inl blocks.win)))
  have plt := below p (owned_live good (Or.inr (Or.inr (Or.inl blocks.prev))))
  have qlt := below q (owned_live good (Or.inr (Or.inr (Or.inr (Or.inl blocks.head)))))
  have blt := below b (owned_live good (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf)))))
  have dslt := below ds (owned_live good (Or.inl rfl))
  -- the sizes
  have wsz : d.w_size.toNat ≤ 32768 := by
    have := I.wsize; have := I.wbits_hi
    have : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) I.wbits_hi
    omega
  have hsz : d.hash_size.toNat ≤ 65536 := by
    have := I.hsize
    have : 2 ^ d.hash_bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) I.hbits_hi
    omega
  obtain ⟨tb, tbuf, tbase⟩ : ∃ tb tbuf, Zlib.Trees.Proofs.Out.TreesInvAt h ds d tb tbuf := by
    obtain ⟨d0, tb, tbuf, t⟩ := good.trees
    have e0 : d0 = d := Option.some.inj (t.base.dstate.symm.trans hL.hs)
    subst e0
    exact ⟨tb, tbuf, t⟩
  have litHi := tbase.base.lit_hi
  have litLo := tbase.base.lit_lo
  have symEnd := tbase.base.sym_end
  obtain ⟨-, -, symLe, symMod⟩ := I.sym
  have mW : (d.w_size * 2).toNat = 2 * d.w_size.toNat := by
    rw [UInt32.toNat_mul]; simp; omega
  have mP : (d.w_size * 2).toNat / 2 = d.w_size.toNat := by omega
  have mQ : (d.hash_size * 2).toNat / 2 = d.hash_size.toNat := by
    rw [UInt32.toNat_mul]; simp; omega
  have mB : (d.lit_bufsize * 4).toNat = 4 * d.lit_bufsize.toNat := by
    rw [UInt32.toNat_mul]; simp; omega
  -- the allocations
  have okW : (copyH0 h d).allocOk (copyH0 h d).nalloc = true := by
    unfold bytePtr at n1; split at n1
    · assumption
    · exact absurd rfl n1
  have okP : (copyW (copyH0 h d) d).allocOk (copyW (copyH0 h d) d).nalloc = true := by
    unfold wordPtr at n2; split at n2
    · assumption
    · exact absurd rfl n2
  have okQ : (copyP (copyH0 h d) d).allocOk (copyP (copyH0 h d) d).nalloc = true := by
    unfold wordPtr at n3; split at n3
    · assumption
    · exact absurd rfl n3
  have okB : (copyQ (copyH0 h d) d).allocOk (copyQ (copyH0 h d) d).nalloc = true := by
    unfold bytePtr at n4; split at n4
    · assumption
    · exact absurd rfl n4
  have eW : copyW (copyH0 h d) d = byteHeap (copyH0 h d) (d.w_size * 2).toNat := by
    simp [copyW, byteResult, okW]
  have eP : copyP (copyH0 h d) d = wordHeap (copyW (copyH0 h d) d) ((d.w_size * 2).toNat / 2) := by
    simp [copyP, wordResult, okP]
  have eQ : copyQ (copyH0 h d) d = wordHeap (copyP (copyH0 h d) d) ((d.hash_size * 2).toNat / 2) := by
    simp [copyQ, wordResult, okQ]
  have eB : copyB (copyH0 h d) d = byteHeap (copyQ (copyH0 h d) d) (d.lit_bufsize * 4).toNat := by
    simp [copyB, byteResult, okB]
  have nH : (copyH0 h d).nextBlk = h.nextBlk + 1 := by simp [copyH0, stateHeap, setD]
  have nW : (copyW (copyH0 h d) d).nextBlk = h.nextBlk + 2 := by
    rw [eW]; simp [byteHeap, Zlib.Zutil.Proofs.allocHeap, nH]
  have nP : (copyP (copyH0 h d) d).nextBlk = h.nextBlk + 3 := by rw [eP]; simp [wordHeap, nW]
  have nQ : (copyQ (copyH0 h d) d).nextBlk = h.nextBlk + 4 := by rw [eQ]; simp [wordHeap, nP]
  have pW : bytePtr (copyH0 h d) = .ref (.blk (h.nextBlk + 1)) 0 := by simp [bytePtr, okW, nH]
  have pP : wordPtr (copyW (copyH0 h d) d) = .ref (.blk (h.nextBlk + 2)) 0 := by simp [wordPtr, okP, nW]
  have pQ : wordPtr (copyP (copyH0 h d) d) = .ref (.blk (h.nextBlk + 3)) 0 := by simp [wordPtr, okQ, nP]
  have pB : bytePtr (copyQ (copyH0 h d) d) = .ref (.blk (h.nextBlk + 4)) 0 := by simp [bytePtr, okB, nQ]
  simp only [copyBufState, pW, pP, pQ, pB] at tail
  -- the blocks of the source are kept by the allocations
  have dsn : ds ≠ h.nextBlk := by omega
  have old : ∀ x, x < h.nextBlk → SlotSame h (copyB (copyH0 h d) d) x := by
    intro x hx
    have ne : x ≠ h.nextBlk := by omega
    have s0 : SlotSame h (copyH0 h d) x := by
      simp [SlotSame, copyH0, stateHeap, setD, upd_ne _ _ _ _ ne]
    have s1 := byteResult_old (copyH0 h d) ((d.w_size * 2).toNat) x (by rw [nH]; omega)
    have s2 := wordResult_old (copyW (copyH0 h d) d) ((d.w_size * 2).toNat / 2) x (by rw [nW]; omega)
    have s3 := wordResult_old (copyP (copyH0 h d) d) ((d.hash_size * 2).toNat / 2) x (by rw [nP]; omega)
    have s4 := byteResult_old (copyQ (copyH0 h d) d) ((d.lit_bufsize * 4).toNat) x (by rw [nQ]; omega)
    exact (((s0.trans s1).trans s2).trans s3).trans s4
  -- the new blocks
  have gW : (copyB (copyH0 h d) d).bytes (h.nextBlk + 1) = some (Array.ofFn (n := (d.w_size * 2).toNat)
      fun i => Junk.of ((copyH0 h d).garbage (copyH0 h d).nalloc i.val)) := by
    rw [eB, eQ, eP, eW]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, nH, nW, nP, nQ]
  have roW : (copyB (copyH0 h d) d).ro (h.nextBlk + 1) = false := by
    rw [eB, eQ, eP, eW]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, nH, nW, nP, nQ]
  have gP : (copyB (copyH0 h d) d).words (h.nextBlk + 2) = some (Array.ofFn (n := (d.w_size * 2).toNat / 2)
      fun i => Junk.of ((copyW (copyH0 h d) d).garbage (copyW (copyH0 h d) d).nalloc i.val)) := by
    rw [eB, eQ, eP]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, nH, nW, nP, nQ]
  have gQ : (copyB (copyH0 h d) d).words (h.nextBlk + 3) = some (Array.ofFn (n := (d.hash_size * 2).toNat / 2)
      fun i => Junk.of ((copyP (copyH0 h d) d).garbage (copyP (copyH0 h d) d).nalloc i.val)) := by
    rw [eB, eQ]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, nH, nW, nP, nQ]
  have gB : (copyB (copyH0 h d) d).bytes (h.nextBlk + 4) = some (Array.ofFn (n := (d.lit_bufsize * 4).toNat)
      fun i => Junk.of ((copyQ (copyH0 h d) d).garbage (copyQ (copyH0 h d) d).nalloc i.val)) := by
    rw [eB]
    simp [byteHeap, Zlib.Zutil.Proofs.allocHeap, nQ]
  have roB : (copyB (copyH0 h d) d).ro (h.nextBlk + 4) = false := by
    rw [eB]
    simp [byteHeap, Zlib.Zutil.Proofs.allocHeap, nQ]
  -- the source state, the streams and the state slot
  have hsX : (copyB (copyH0 h d) d).dstates ds = some d := by
    rw [(old ds dslt).2.2.2.2.1]; exact hL.hs
  have hsN : (copyB (copyH0 h d) d).dstates h.nextBlk = some d := by
    simp [copyB, copyQ, copyP, copyW, copyH0]
  have hzX : source.get (copyB (copyH0 h d) d) = some z := by
    simp [copyB, copyQ, copyP, copyW, copyH0, hL.hz]
  have hzdX : dest.get (copyB (copyH0 h d) d) = some zd := by
    simp [copyB, copyQ, copyP, copyW, copyH0, get]
  have sym : d.sym_buf = .ref (.blk b) d.lit_bufsize.toNat := by
    obtain ⟨⟨b', e1, e2⟩, -⟩ := I.sym
    rw [blocks.pbuf] at e1
    cases e1
    exact e2
  have hwOld := old w wlt
  have hpOld := old p plt
  have hqOld := old q qlt
  have hbOld := old b blt
  have insLe := inv.shape.insert
  have cntLe := copyCnt_le d insLe
  have hwLe : d.high_water.toNat ≤ 2 * d.w_size.toNat := by have := I.hw; have := I.wsz; omega
  have runT := copy_tail_run (W := h.nextBlk + 1) (P := h.nextBlk + 2) (Q := h.nextBlk + 3) (B := h.nextBlk + 4) (T0 := setD (copyB (copyH0 h d) d) h.nextBlk { d with window := .ref (.blk (h.nextBlk + 1)) 0, prev := .ref (.blk (h.nextBlk + 2)) 0, head := .ref (.blk (h.nextBlk + 3)) 0, pending_buf := .ref (.blk (h.nextBlk + 4)) 0 })
    (Ne.symm distinct) (by simpa using hzX) (by simpa using hzdX) (by simp [setD_dstates_ne _ _ _ _ dsn, hsX]) dsn
    (by simp) blocks.win blocks.prev blocks.head blocks.pbuf pout sym
    (by simp [setD]; rw [hwOld.1]; exact gw) (by simp [setD]; rw [hpOld.2.1]; exact gp)
    (by simp [setD]; rw [hqOld.2.1]; exact gq) (by simp [setD]; rw [hbOld.1]; exact gb)
    (by simpa [setD] using gW) (by simpa [setD] using gP) (by simpa [setD] using gQ) (by simpa [setD] using gB)
    (by simpa [setD] using roW) (by simpa [setD] using roB)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp [mW]; omega) (by omega) (by simp [mP]; omega) (by omega) (by simp only [Array.size_ofFn, mQ, Nat.le_refl]) (by omega)
    (by simp [mB]; omega) (by omega) (by simp [mB]; omega) (by omega) (by omega)
  rw [runT] at tail
  cases tail
  -- the heap of the allocations
  have freshH : Fresh (copyH0 h d) :=
    fresh_setD_below (fresh_stateHeap fresh _) h.nextBlk (by simp [stateHeap]) d
  have uniqH : Uniq (copyH0 h d) :=
    (shape_setD (stateHeap_dstates_same h _) d).uniq (uniq_stateHeap good.uniq fresh _)
  have fW := fresh_byteResult freshH ((d.w_size * 2).toNat)
  have fP := fresh_wordResult fW ((d.w_size * 2).toNat / 2)
  have fQ := fresh_wordResult fP ((d.hash_size * 2).toNat / 2)
  have fX : Fresh (copyB (copyH0 h d) d) := fresh_byteResult fQ _
  have uX : Uniq (copyB (copyH0 h d) d) :=
    uniq_byteResult (uniq_wordResult (uniq_wordResult (uniq_byteResult uniqH freshH _) fW _) fP _) fQ _
  have stX : (copyB (copyH0 h d) d).static = h.static := by
    rw [eB, eQ, eP, eW]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, copyH0, stateHeap, setD]
  have nX : (copyB (copyH0 h d) d).nextBlk = h.nextBlk + 5 := by
    rw [eB]; simp [byteHeap, Zlib.Zutil.Proofs.allocHeap, nQ]
  exact ⟨_, _, _, copy_final_inv inv blocks gw gp gq gb pout offFit
    (fresh_setD_below fX _ (by omega) _) ((shape_setD hsN _).uniq uX) (by simp [setD, stX])
    (by simpa using hzdX) (setD_dstates_same _ _ _)
    (by simpa [setD] using gW) (by simpa [setD] using gP) (by simpa [setD] using gQ) (by simpa [setD] using gB)
    (by simpa [setD] using roW) (by simpa [setD] using roB)
    (by simp only [Array.size_ofFn, mW]) (by simp only [Array.size_ofFn, mP]) (by simp only [Array.size_ofFn, mQ])
    (by simp only [Array.size_ofFn, mB]) (by omega) (by omega),
    rfl, rfl, rfl⟩

/-- **`deflateCopy` into a distinct destination establishes the invariant there** (skeleton lemma
`copy_inv`). -/
theorem copy_inv {h after : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (run : C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h = .ok (Z_OK, after)) :
    ∃ ds' z' d', DInv after dest ds' z' d' := by
  obtain ⟨ds', z', d', inv', -⟩ := copy_result inv distinct get run
  exact ⟨ds', z', d', inv'⟩

/-- **`deflateCopy` copies the state record, so the header facts hold in the copy** (skeleton lemma
`copy_header`). -/
theorem copy_header {h after : Heap} {source dest : ZStreamRef} {ds ds' : Nat} {z zd z' : ZStream}
    {d d' : DeflateState}
    (inv : DInv h source ds z d) (header : HeaderInv d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (run : C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h = .ok (Z_OK, after))
    (invAfter : DInv after dest ds' z' d') : HeaderInv d' := by
  obtain ⟨ds'', z'', d'', inv'', st, sy, gz⟩ := copy_result inv distinct get run
  obtain ⟨-, -, e⟩ := inv''.unique invAfter.good
  rw [e]
  exact header.keep st sy gz

end Zlib.Deflate.Universal
