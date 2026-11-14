import ZlibF.Proof.«deflate.c.universal-ops-copy»
import ZlibF.Spec.Public.Copy

/-!
# deflate.c: the success clauses of `deflateCopy` (`copy_success`)

When the state allocation and the four buffer allocations all succeed, `deflateCopy` runs its
success path to the explicit heap `copyFinal` of `deflate.c.universal-ops-copy`. This file proves
the success clauses of `Goal.deflateCopy` from that heap: the source stream and state are kept,
the frame is the destination stream root, the copy satisfies the invariant, its state record is
the relocated source record, the window, `head`, `prev`, pending and symbol prefixes are copied,
and the five new blocks are exactly the new live blocks.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
open Zlib.Trees.Proofs.Out (setB)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Heap helpers -/

theorem copyS_get_put_ne {h : Heap} {r r' : ZStreamRef} (e : r' ≠ r) (v : ZStream) :
    r'.get (r.put h v) = r'.get h := by
  cases r with
  | tab i =>
    cases r' with
    | tab j =>
      have hji : j ≠ i := fun x => e (by rw [x])
      simp only [ZStreamRef.put]
      split <;> simp [ZStreamRef.get, upd_ne _ _ _ _ hji]
    | in_gzstate_strm j =>
      simp only [ZStreamRef.put]
      split <;> rfl
  | in_gzstate_strm i =>
    cases r' with
    | tab j =>
      simp only [ZStreamRef.put]
      split <;> rfl
    | in_gzstate_strm j =>
      have hji : j ≠ i := fun x => e (by rw [x])
      simp only [ZStreamRef.put]
      split <;> simp [ZStreamRef.get, upd_ne _ _ _ _ hji]

/-- A stream write changes no block other than the stream root. -/
theorem copyS_put_other (h : Heap) (dest : ZStreamRef) (v : ZStream) {b : Nat}
    (root : ¬ StreamRoot dest b) :
    (dest.put h v).streams b = h.streams b ∧ (dest.put h v).gzstates b = h.gzstates b := by
  cases dest with
  | tab k =>
    have ne : b ≠ k := fun e => root (by simp [StreamRoot, e])
    simp only [ZStreamRef.put]
    split <;> simp [upd_ne _ _ _ _ ne]
  | in_gzstate_strm k =>
    have ne : b ≠ k := fun e => root (by simp [StreamRoot, e])
    simp only [ZStreamRef.put]
    split <;> simp [upd_ne _ _ _ _ ne]

/-- A stream reference that resolves names a live block. -/
theorem copyS_root_live {h : Heap} {dest : ZStreamRef} {z : ZStream} (get : dest.get h = some z)
    {b : Nat} (root : StreamRoot dest b) : h.live b := by
  cases dest with
  | tab k =>
    simp only [StreamRoot] at root
    subst root
    have e : h.streams b = some z := get
    simp [Heap.live, e]
  | in_gzstate_strm k =>
    simp only [StreamRoot] at root
    subst root
    cases e : h.gzstates b with
    | none => simp [ZStreamRef.get, e] at get
    | some g => simp [Heap.live, e]

theorem copyS_slot_live {h g : Heap} {x : Nat} (s : SlotSame h g x) : g.live x ↔ h.live x := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ := s
  simp only [Heap.live, e1, e2, e3, e4, e5, e6, e7]

/-- Pointwise form of `copyRange`. -/
theorem copyS_at {T : Type} [Inhabited T] (a s : Array T) (o n i : Nat) (ha : o + n ≤ a.size)
    (hs : o + n ≤ s.size) :
    (copyRange a s o o n)[i]? = if o ≤ i ∧ i < o + n then s[i]? else a[i]? := by
  rw [getElem?_copyRange _ _ _ _ _ _ ha]
  by_cases c : o ≤ i ∧ i < o + n
  · rw [if_pos c, if_pos c, show o + (i - o) = i by omega,
      Array.getElem?_eq_getElem (show i < s.size by omega)]
    exact congrArg some (getElem!_pos s i (by omega))
  · rw [if_neg c, if_neg c]

/-- Two arrays that agree on a range give the same prefix lists. -/
theorem copyS_prefix {T : Type} (x y : Array T) (o n : Nat)
    (agree : ∀ i, o ≤ i → i < o + n → x[i]? = y[i]?) :
    (x.toList.drop o).take n = (y.toList.drop o).take n := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]
  by_cases small : j < n
  · simp only [small, if_true]
    exact agree _ (by omega) (by omega)
  · simp [small]

/-- The success heap changes no old block except the stream root. -/
theorem copyS_final_slot {T0 : Heap} {dest : ZStreamRef} {z : ZStream} {d : DeflateState}
    {n W P Q B off x : Nat} {aW wa aB ba : Array UInt8} {aP pa aQ qa : Array UInt16}
    (xn : x ≠ n) (xW : x ≠ W) (xP : x ≠ P) (xQ : x ≠ Q) (xB : x ≠ B) (root : ¬ StreamRoot dest x) :
    SlotSame T0 (copyFinal T0 dest z d n W P Q B off aW wa aB ba aP pa aQ qa) x := by
  have po := copyS_put_other T0 dest { z with state := StateRef.ofDeflateState (some (.tab n)) } root
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [copyFinal, setD, setB, setW, upd_ne _ _ _ _ xn, upd_ne _ _ _ _ xW, upd_ne _ _ _ _ xP,
      upd_ne _ _ _ _ xQ, upd_ne _ _ _ _ xB, po.1, po.2]

/-! ## The success path is reached -/

/-- **When every allocation succeeds, `deflateCopy` reaches its success tail.** -/
theorem copy_reach {h : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (get : dest.get h = some zd)
    (ok : h.allocOk h.nalloc = true ∧ bytePtr (copyH0 h d) ≠ .null ∧ wordPtr (copyW (copyH0 h d) d) ≠ .null ∧
      wordPtr (copyP (copyH0 h d) d) ≠ .null ∧ bytePtr (copyQ (copyH0 h d) d) ≠ .null) :
    C.run (deflateCopy (some dest) (some source)) h =
      copyTail (some dest) (some source) (some (.tab ds)) (some (.tab h.nextBlk)) d (bytePtr (copyH0 h d))
        (wordPtr (copyW (copyH0 h d) d)) (wordPtr (copyP (copyH0 h d) d)) (bytePtr (copyQ (copyH0 h d) d))
        (setD (copyB (copyH0 h d) d) h.nextBlk (copyBufState (copyH0 h d) d)) := by
  obtain ⟨ho, n1, n2, n3, n4⟩ := ok
  have good := inv.good
  have hL := good.live
  have fresh := good.fresh
  have dsLt : ds < h.nextBlk := by
    rcases Nat.lt_or_ge ds h.nextBlk with lt | ge
    · exact lt
    · exact absurd (owned_live good (Or.inl rfl)) (fresh ds ge)
  have ne : h.nextBlk ≠ ds := by omega
  have e2 : zrd (some source) (fun z => z.state) h = .ok (some (.deflate ds), h) := by
    rw [zrd_eq, hL.hz]; simp [hL.zst]
  have e5 := allocDeflateState_some ho (Heap.slotUsed_eq_false.mpr (fresh _ (Nat.le_refl _)))
  have e6' : copyDeflateState (some (.tab h.nextBlk)) (some (.tab ds))
      (stateHeap h (DeflateState.garbage (h.garbage h.nalloc))) = .ok ((), copyH0 h d) := by
    simp [copyDeflateState, ne, bind_app, ldD_eq, stD_eq, stateHeap, upd_ne _ _ _ _ (Ne.symm ne), hL.hs, copyH0, setD]
  have e6 : copyDeflateState (some (.tab h.nextBlk)) (some (.tab ds))
      ({ h with dstates := upd h.dstates h.nextBlk (some (DeflateState.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 } : Heap) = .ok ((), copyH0 h d) := e6'
  have hs7 : (copyH0 h d).dstates h.nextBlk = some d := by simp [copyH0]
  have e7 : ldDeflateState (some (.tab h.nextBlk)) (copyH0 h d) = .ok (d, copyH0 h d) := by
    rw [ldD_eq, hs7]
  have freshH : Fresh (copyH0 h d) :=
    fresh_setD_below (fresh_stateHeap fresh _) h.nextBlk (by simp [stateHeap]) d
  have hzH : source.get (copyH0 h d) = some z := by simp [copyH0, hL.hz]
  have e8 := copy_buffers_run freshH hzH inv.alloc.1 hs7 (by simp [copyH0, stateHeap])
  have c : (bytePtr (copyH0 h d) == .null || wordPtr (copyW (copyH0 h d) d) == .null ||
      wordPtr (copyP (copyH0 h d) d) == .null || bytePtr (copyQ (copyH0 h d) d) == .null) = false := by
    simp [n1, n2, n3, n4]
  rw [C.run]
  unfold deflateCopy
  simp only [show (some dest == (none : ZStreamPtr)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  simp only [C.bind_ok (stateCheck_live hL), bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [C.bind_ok e2, C.bind_ok (castD (h := h) (ds := ds))]
  simp only [C.bind_ok (allocator_run hL.hz inv.alloc.1)]
  simp only [C.bind_ok e5, show (some (DeflateStateRef.tab h.nextBlk) == none) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  simp only [C.bind_ok e6]
  simp only [C.bind_ok e7]
  rw [copyBuffers_bind]
  simp only [C.bind_ok e8]
  simp only [c, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## The success heap, with its parts named -/

set_option maxRecDepth 20000 in
/-- **The success run, with its heap in parts.** `copyFinal` over the heap `T0` after the buffer
requests; the five new blocks are `h.nextBlk` to `h.nextBlk + 4`. -/
theorem copy_pack {h : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (ok : h.allocOk h.nalloc = true ∧ bytePtr (copyH0 h d) ≠ .null ∧ wordPtr (copyW (copyH0 h d) d) ≠ .null ∧
      wordPtr (copyP (copyH0 h d) d) ≠ .null ∧ bytePtr (copyQ (copyH0 h d) d) ≠ .null) :
    ∃ (T0 : Heap) (aW aB wa ba : Array UInt8) (aP aQ pa qa : Array UInt16) (w p q b off : Nat),
      C.run (deflateCopy (some dest) (some source)) h =
        .ok (Z_OK, copyFinal T0 dest z d h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
          (h.nextBlk + 4) off aW wa aB ba aP pa aQ qa) ∧
      DInv (copyFinal T0 dest z d h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
          (h.nextBlk + 4) off aW wa aB ba aP pa aQ qa) dest h.nextBlk
        { z with state := StateRef.ofDeflateState (some (.tab h.nextBlk)) }
        (copyState d dest h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) off) ∧
      d.window = .ref (.blk w) 0 ∧ d.prev = .ref (.blk p) 0 ∧ d.head = .ref (.blk q) 0 ∧
      d.pending_buf = .ref (.blk b) 0 ∧ d.pending_out = .ref (.blk b) off ∧
      d.sym_buf = .ref (.blk b) d.lit_bufsize.toNat ∧
      h.bytes w = some wa ∧ h.words p = some pa ∧ h.words q = some qa ∧ h.bytes b = some ba ∧
      T0.bytes (h.nextBlk + 1) = some aW ∧ T0.words (h.nextBlk + 2) = some aP ∧
      T0.words (h.nextBlk + 3) = some aQ ∧ T0.bytes (h.nextBlk + 4) = some aB ∧
      aW.size = 2 * d.w_size.toNat ∧ aP.size = d.w_size.toNat ∧ aQ.size = d.hash_size.toNat ∧
      aB.size = 4 * d.lit_bufsize.toNat ∧
      wa.size = 2 * d.w_size.toNat ∧ pa.size = d.w_size.toNat ∧ qa.size = d.hash_size.toNat ∧
      ba.size = 4 * d.lit_bufsize.toNat ∧
      d.high_water.toNat ≤ 2 * d.w_size.toNat ∧ (copyCnt d d).toNat ≤ d.w_size.toNat ∧
      off + d.pending.toNat ≤ 4 * d.lit_bufsize.toNat ∧
      d.lit_bufsize.toNat + d.sym_next.toNat ≤ 4 * d.lit_bufsize.toNat ∧
      (∀ x, x < h.nextBlk → SlotSame h T0 x) ∧
      T0.static = h.static ∧ T0.allocOk = h.allocOk ∧ T0.garbage = h.garbage ∧
      T0.nextBlk = h.nextBlk + 5 ∧ h.nalloc ≤ T0.nalloc ∧
      source.get T0 = some z ∧ T0.dstates ds = some d ∧ ds < h.nextBlk := by
  have reach := copy_reach inv get ok
  obtain ⟨ho, n1, n2, n3, n4⟩ := ok
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
  simp only [copyBufState, pW, pP, pQ, pB] at reach
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
  rw [runT] at reach
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
  have okX : (copyB (copyH0 h d) d).allocOk = h.allocOk := by
    rw [eB, eQ, eP, eW]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, copyH0, stateHeap, setD]
  have gaX : (copyB (copyH0 h d) d).garbage = h.garbage := by
    rw [eB, eQ, eP, eW]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, copyH0, stateHeap, setD]
  have naX : h.nalloc ≤ (copyB (copyH0 h d) d).nalloc := by
    rw [eB, eQ, eP, eW]
    simp [byteHeap, wordHeap, Zlib.Zutil.Proofs.allocHeap, copyH0, stateHeap, setD]
    omega
  have nX : (copyB (copyH0 h d) d).nextBlk = h.nextBlk + 5 := by
    rw [eB]; simp [byteHeap, Zlib.Zutil.Proofs.allocHeap, nQ]
  have invF := copy_final_inv (T0 := setD (copyB (copyH0 h d) d) h.nextBlk { d with window := .ref (.blk (h.nextBlk + 1)) 0, prev := .ref (.blk (h.nextBlk + 2)) 0, head := .ref (.blk (h.nextBlk + 3)) 0, pending_buf := .ref (.blk (h.nextBlk + 4)) 0 })
    (dest := dest) (n := h.nextBlk) (W := h.nextBlk + 1) (P := h.nextBlk + 2) (Q := h.nextBlk + 3)
    (B := h.nextBlk + 4) inv blocks gw gp gq gb pout offFit
    (fresh_setD_below fX _ (by omega) _) ((shape_setD hsN _).uniq uX) (by simp [setD, stX])
    (by simpa using hzdX) (setD_dstates_same _ _ _)
    (by simpa [setD] using gW) (by simpa [setD] using gP) (by simpa [setD] using gQ) (by simpa [setD] using gB)
    (by simpa [setD] using roW) (by simpa [setD] using roB)
    (by simp only [Array.size_ofFn, mW]) (by simp only [Array.size_ofFn, mP]) (by simp only [Array.size_ofFn, mQ])
    (by simp only [Array.size_ofFn, mB]) (by omega) (by omega)
  refine ⟨_, _, _, wa, ba, _, _, pa, qa, w, p, q, b, off, reach, invF, blocks.win, blocks.prev, blocks.head,
    blocks.pbuf, pout, sym, gw, gp, gq, gb,
    by simpa [setD] using gW, by simpa [setD] using gP, by simpa [setD] using gQ, by simpa [setD] using gB,
    by simp only [Array.size_ofFn, mW], by simp only [Array.size_ofFn, mP], by simp only [Array.size_ofFn, mQ],
    by simp only [Array.size_ofFn, mB], swa, spa, sqa, sba, hwLe, cntLe, by omega, by omega, ?_,
    by simp [setD, stX], by simp [setD, okX], by simp [setD, gaX], by simp [setD, nX], by simp [setD]; exact naX,
    by simpa using hzX, by simp [setD_dstates_ne _ _ _ _ dsn, hsX], dslt⟩
  intro x hx
  have ne : x ≠ h.nextBlk := by omega
  refine (old x hx).trans ?_
  simp [SlotSame, setD, upd_ne _ _ _ _ ne]

/-! ## Prefixes -/

theorem copyS_same_bytes {before after : Heap} {x y o n : Nat} {a a' : Array UInt8}
    (ga : before.bytes x = some a) (ga' : after.bytes y = some a') (s : o + n ≤ a.size) (s' : o + n ≤ a'.size)
    (agree : ∀ i, o ≤ i → i < o + n → a'[i]? = a[i]?) :
    SameBytePrefix before after (.ref (.blk x) o) (.ref (.blk y) o) n :=
  ⟨(a.toList.drop o).take n, Or.inr ⟨.blk x, o, a, rfl, by rw [BRef.get_blk]; exact ga, s, rfl⟩,
    Or.inr ⟨.blk y, o, a', rfl, by rw [BRef.get_blk]; exact ga', s', (copyS_prefix a' a o n agree).symm⟩⟩

theorem copyS_same_words {before after : Heap} {x y n : Nat} {a a' : Array UInt16}
    (ga : before.words x = some a) (ga' : after.words y = some a') (s : n ≤ a.size) (s' : n ≤ a'.size)
    (agree : ∀ i, i < n → a'[i]? = a[i]?) :
    SameWordPrefix before after (.ref (.blk x) 0) (.ref (.blk y) 0) n :=
  ⟨.blk x, 0, a, .blk y, 0, a', rfl, rfl, by rw [WRef.get_blk]; exact ga, by rw [WRef.get_blk]; exact ga',
    by omega, by omega, copyS_prefix a a' 0 n (fun i _ h2 => (agree i (by omega)).symm)⟩

/-! ## The success clauses -/

/-- **The success clauses of `Goal.deflateCopy`.** When the state allocation and the four buffer
allocations succeed, `deflateCopy` returns `Z_OK`, keeps the source, changes no old block but the
destination stream root, and builds a copy with the invariant, the relocated record, the copied
prefixes and exactly five new live blocks. -/
theorem copy_success {h : Heap} {source dest : ZStreamRef} {ds : Nat} {z zd : ZStream} {d : DeflateState}
    (inv : DInv h source ds z d) (distinct : source ≠ dest) (get : dest.get h = some zd)
    (ok : h.allocOk h.nalloc = true ∧ bytePtr (copyH0 h d) ≠ .null ∧ wordPtr (copyW (copyH0 h d) d) ≠ .null ∧
      wordPtr (copyP (copyH0 h d) d) ≠ .null ∧ bytePtr (copyQ (copyH0 h d) d) ≠ .null) :
    ∃ after, C.run (deflateCopy (some dest) (some source)) h = .ok (Z_OK, after) ∧
      source.get after = some z ∧ after.dstates ds = some d ∧
      ZlibF.Spec.Public.Frame h after (ZlibF.Spec.Public.StreamRoot dest) ∧
      ∃ copied,
        Zlib.Deflate.Spec.DGood after dest h.nextBlk { z with state := some (.deflate h.nextBlk) } copied ∧
        copied = ZlibF.Spec.Public.copiedDeflate dest h.nextBlk d copied ∧
        ZlibF.Spec.Public.SameBytePrefix h after d.window copied.window d.high_water.toNat ∧
        ZlibF.Spec.Public.SameWordPrefix h after d.head copied.head d.hash_size.toNat ∧
        ZlibF.Spec.Public.SameWordPrefix h after d.prev copied.prev
          (if d.slid ≠ 0 ∨ d.strstart - d.insert > d.w_size then d.w_size.toNat
           else (d.strstart - d.insert).toNat) ∧
        ZlibF.Spec.Public.SameBytePrefix h after d.pending_out copied.pending_out d.pending.toNat ∧
        ZlibF.Spec.Public.SameBytePrefix h after d.sym_buf copied.sym_buf d.sym_next.toNat ∧
        (∀ b, ZlibF.Spec.Public.DeflateOwned h.nextBlk copied b ↔ h.nextBlk ≤ b ∧ b < h.nextBlk + 5) ∧
        ZlibF.Spec.Public.LiveChange h after (ZlibF.Spec.Public.DeflateOwned h.nextBlk copied) (fun _ => False) := by
  obtain ⟨T0, aW, aB, wa, ba, aP, aQ, pa, qa, w, p, q, b, off, run, invF, ew, ep, eq, eb, pout, sym,
    gw, gp, gq, gb, gW, gP, gQ, gB, sAW, sAP, sAQ, sAB, swa, spa, sqa, sba, hwLe, cntLe, pendLe, symLe,
    old, st0, ok0, ga0, nb0, na0, hz0, hs0, dslt⟩ := copy_pack inv distinct get ok
  have fresh := inv.good.fresh
  obtain ⟨F, hF⟩ : ∃ F, F = copyFinal T0 dest z d h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3)
      (h.nextBlk + 4) off aW wa aB ba aP pa aQ qa := ⟨_, rfl⟩
  rw [← hF] at run invF
  have dsn : ds ≠ h.nextBlk := by omega
  have WB : h.nextBlk + 1 ≠ h.nextBlk + 4 := by omega
  have PQ : h.nextBlk + 2 ≠ h.nextBlk + 3 := by omega
  -- the success heap
  have hzF : source.get F = some z := by
    rw [hF]
    simp only [copyFinal, ZStreamRef.get_setD, get_setB', get_setW']
    rw [copyS_get_put_ne distinct]
    exact hz0
  have hsF : F.dstates ds = some d := by
    rw [hF]; simp [copyFinal, setD, setB, setW, upd_ne _ _ _ _ dsn, hs0]
  have hWF : F.bytes (h.nextBlk + 1) = some (copyWin aW wa d) := by
    rw [hF]; simp [copyFinal, setD, setB, setW, upd_ne _ _ _ _ WB]
  have hPF : F.words (h.nextBlk + 2) = some (copyPrev aP pa d) := by
    rw [hF]; simp [copyFinal, setD, setB, setW, upd_ne _ _ _ _ PQ]
  have hQF : F.words (h.nextBlk + 3) = some (copyHead aQ qa d) := by
    rw [hF]; simp [copyFinal, setD, setB, setW]
  have hBF : F.bytes (h.nextBlk + 4) = some (copyPend aB ba d off) := by
    rw [hF]; simp [copyFinal, setD, setB, setW]
  have stF : F.static = T0.static := by rw [hF]; simp [copyFinal, setD, setB, setW]
  have okF : F.allocOk = T0.allocOk := by rw [hF]; simp [copyFinal, setD, setB, setW]
  have gaF : F.garbage = T0.garbage := by rw [hF]; simp [copyFinal, setD, setB, setW]
  have nbF : F.nextBlk = T0.nextBlk := by rw [hF]; simp [copyFinal, setD, setB, setW]
  have naF : F.nalloc = T0.nalloc := by rw [hF]; simp [copyFinal, setD, setB, setW]
  have oldF : ∀ x, x < h.nextBlk → ¬ StreamRoot dest x → SlotSame h F x := by
    intro x hx root
    rw [hF]
    exact (old x hx).trans (copyS_final_slot (by omega) (by omega) (by omega) (by omega) (by omega) root)
  -- the frame
  have frame : Frame h F (StreamRoot dest) := by
    refine ⟨by rw [stF, st0], by rw [okF, ok0], by rw [gaF, ga0], by rw [nbF, nb0]; omega,
      by rw [naF]; exact na0, ?_⟩
    intro x live root
    have lt : x < h.nextBlk := by
      rcases Nat.lt_or_ge x h.nextBlk with lt | ge
      · exact lt
      · exact absurd live (fresh x ge)
    exact oldF x lt root
  -- the ownership of the copy
  have owned : ∀ x, ZlibF.Spec.Public.DeflateOwned h.nextBlk
      (copyState d dest h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) off) x ↔
      h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
    intro x
    simp only [ZlibF.Spec.Public.DeflateOwned, copyState]
    constructor
    · intro hx
      rcases hx with e | e | e | e | e
      · omega
      all_goals (cases e; omega)
    · intro hx
      have : x = h.nextBlk ∨ x = h.nextBlk + 1 ∨ x = h.nextBlk + 2 ∨ x = h.nextBlk + 3 ∨ x = h.nextBlk + 4 := by
        omega
      rcases this with e | e | e | e | e <;> subst e <;> simp
  -- the live blocks
  have ledger : LiveChange h F (ZlibF.Spec.Public.DeflateOwned h.nextBlk
      (copyState d dest h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) off))
      (fun _ => False) := by
    intro x
    rw [owned x]
    rcases Nat.lt_or_ge x h.nextBlk with lt | ge
    · have hl : F.live x ↔ h.live x := by
        by_cases root : StreamRoot dest x
        · exact iff_of_true (copyS_root_live invF.good.live.hz root) (copyS_root_live get root)
        · exact copyS_slot_live (oldF x lt root)
      rw [hl]
      constructor
      · intro l; exact Or.inl ⟨l, id⟩
      · rintro (⟨l, -⟩ | ⟨h1, -⟩)
        · exact l
        · omega
    · rcases Nat.lt_or_ge x (h.nextBlk + 5) with lt5 | ge5
      · refine iff_of_true ?_ (Or.inr ⟨ge, lt5⟩)
        have : x = h.nextBlk ∨ x = h.nextBlk + 1 ∨ x = h.nextBlk + 2 ∨ x = h.nextBlk + 3 ∨ x = h.nextBlk + 4 := by
          omega
        rcases this with e | e | e | e | e <;> subst e
        · simp [Heap.live, invF.good.live.hs]
        · simp [Heap.live, hWF]
        · simp [Heap.live, hPF]
        · simp [Heap.live, hQF]
        · simp [Heap.live, hBF]
      · refine iff_of_false (invF.good.fresh x (by rw [nbF, nb0]; exact ge5)) ?_
        rintro (⟨l, -⟩ | ⟨-, h2⟩)
        · exact fresh x ge l
        · omega
  -- the count of `prev`
  have cntEq : (if d.slid ≠ 0 ∨ d.strstart - d.insert > d.w_size then d.w_size.toNat
      else (d.strstart - d.insert).toNat) = (copyCnt d d).toNat := by
    unfold copyCnt
    by_cases c1 : d.slid = 0 <;> by_cases c2 : d.strstart - d.insert > d.w_size <;> simp [c1, c2]
  refine ⟨F, run, hzF, hsF, frame,
    copyState d dest h.nextBlk (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) off,
    invF.good, ?_, ?_, ?_, ?_, ?_, ?_, owned, ledger⟩
  · simp [copiedDeflate, copyState, relocateByte, advance, eb, pout]
  · rw [ew]
    refine copyS_same_bytes gw hWF (by omega) (by simp [copyWin, size_copyRange]; omega) ?_
    intro i _ h2
    simp only [copyWin]
    rw [copyS_at aW wa 0 _ i (by omega) (by omega), if_pos ⟨by omega, h2⟩]
  · rw [eq]
    refine copyS_same_words gq hQF (by omega) (by simp [copyHead, size_copyRange]; omega) ?_
    intro i h2
    simp only [copyHead]
    rw [copyS_at aQ qa 0 _ i (by omega) (by omega), if_pos ⟨by omega, by omega⟩]
  · rw [ep, cntEq]
    refine copyS_same_words gp hPF (by omega) (by simp [copyPrev, size_copyRange]; omega) ?_
    intro i h2
    simp only [copyPrev]
    rw [copyS_at aP pa 0 _ i (by omega) (by omega), if_pos ⟨by omega, by omega⟩]
  · rw [pout]
    refine copyS_same_bytes gb hBF (by omega) (by simp [copyPend, size_copyRange]; omega) ?_
    intro i h1 h2
    simp only [copyPend]
    rw [copyS_at _ ba _ _ i (by rw [size_copyRange]; omega) (by omega)]
    split
    · rfl
    · rw [copyS_at aB ba off _ i (by omega) (by omega), if_pos ⟨h1, h2⟩]
  · rw [sym]
    refine copyS_same_bytes gb hBF (by omega) (by simp [copyPend, size_copyRange]; omega) ?_
    intro i h1 h2
    simp only [copyPend]
    rw [copyS_at _ ba _ _ i (by rw [size_copyRange]; omega) (by omega), if_pos ⟨h1, h2⟩]

#print axioms Zlib.Deflate.Universal.copy_success

end Zlib.Deflate.Universal
