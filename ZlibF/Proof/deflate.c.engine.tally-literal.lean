import ZlibF.Proof.«deflate.c.engine.initial»
import ZlibF.Proof.«trees.c.tally»

/-! # The actual inline literal tally used by the strategies

This proves tally_lit itself. The translation does not call _tr_tally;
the two implementations write their intermediate fields differently.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase TreesInvAt TreesRun bumpFc)
set_option autoImplicit false

def literalBytes (buf : Array UInt8) (d : DeflateState) (c : UInt8) : Array UInt8 :=
  ((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) 0).set!
    (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) 0).set!
    (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) c

def literalState (d : DeflateState) (c : UInt8) : DeflateState :=
  { d with sym_next := d.sym_next + 3, dyn_ltree := bumpFc d.dyn_ltree c.toNat }

/-- Exact symbol contents and the unchanged prefix/suffix. This is the
byte-level input required later by the payload encoder's overlay proof. -/
theorem literal_bytes_view (buf : Array UInt8) (d : DeflateState) (c : UInt8)
    (fit : d.lit_bufsize.toNat + d.sym_next.toNat + 2 < buf.size) (i : Nat) :
    bfn (literalBytes buf d c) i =
      if i = d.lit_bufsize.toNat + d.sym_next.toNat + 2 then c
      else if i = d.lit_bufsize.toNat + d.sym_next.toNat + 1 then 0
      else if i = d.lit_bufsize.toNat + d.sym_next.toNat then 0
      else bfn buf i := by
  unfold literalBytes
  rw [bfn_set _ _ _ (by simp; omega)]
  rw [bfn_set _ _ _ (by simp; omega)]
  rw [bfn_set _ _ _ (by omega)]
  simp only [Nat.add_assoc]

theorem store_symbol_byte {h : Heap} {b off i : Nat} {buf : Array UInt8} (v : UInt8)
    (get : h.bytes b = some buf) (rw : h.ro b = false) (bound : off + i < buf.size) :
    store_at (.ref (.blk b) off) i v h =
      .ok ((), Zlib.Trees.Proofs.Out.setB h b (buf.set! (off + i) v)) := by
  have add : padd (.ref (.blk b) off : BPtr) i h = .ok (.ref (.blk b) (off + i), h) :=
    Ptr.add_nat_ok (off := off) (n := i) (show Space.get h (BRef.blk b) = some buf from get) (by omega)
  have put := Ptr.store_ok (r := BRef.blk b) (T := UInt8) (a := buf) (off := off + i) (v := v)
    get rw bound
  unfold store_at
  rw [bind_app, add]
  exact put

theorem increment_literal_frequency {h : Heap} {ds : Nat} {d : DeflateState} {i : Nat}
    (state : h.dstates ds = some d) (bound : i < d.dyn_ltree.size) :
    freq_inc (.dstate_dyn_ltree ds) i h =
      .ok ((), setD h ds { d with dyn_ltree := bumpFc d.dyn_ltree i }) := by
  have get := CtDataRef.get_dstate_dyn_ltree state
  have add : padd (.ref (.dstate_dyn_ltree ds) 0 : CtDataPtr) i h =
      .ok (.ref (.dstate_dyn_ltree ds) i, h) := by
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := i) get (by omega)
  have load := Ptr.load_ok (off := i) get bound
  have put := Ptr.store_ok (off := i) (v := { d.dyn_ltree[i] with fc := d.dyn_ltree[i].fc + 1 })
    get (by rfl) bound
  unfold freq_inc
  rw [bind_app, add]
  simp only [Nat.zero_add]
  rw [bind_app, load]
  simp only []
  rw [put, CtDataRef.put_dstate_dyn_ltree state]
  simp [setD, bumpFc, bound]

/-- `_tr_tally_lit(s, c, flush)`.
The actual inline macro writes the three symbol bytes, advances sym_next
once by three, increments the literal frequency and returns the full flag.
Room follows from the strategy's strict symbol-count invariant. -/
theorem tally_literal_run {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (base : TreesBase h ds d b buf) (c : UInt8)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end,
      setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)) := by
  let h0 := Zlib.Trees.Proofs.Out.setB h b (buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) 0)
  let h1 := Zlib.Trees.Proofs.Out.setB h b ((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) 0).set!
    (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) 0)
  let hb := Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)
  let dn := { d with sym_next := d.sym_next + 3 }
  let hn := setD hb ds dn
  have cap := base.size
  have end_ := base.sym_end
  have litMax := base.lit_hi
  have one : (d.sym_next + 1).toNat = d.sym_next.toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have two : (d.sym_next + 2).toNat = d.sym_next.toNat + 2 := by
    rw [UInt32.toNat_add]
    simp only [show (2 : UInt32).toNat = 2 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have first := store_symbol_byte (h := h) (off := d.lit_bufsize.toNat) (i := d.sym_next.toNat)
    0 base.bytes base.rw (by omega)
  have second := store_symbol_byte (h := h0) (b := b)
    (buf := buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) 0)
    (off := d.lit_bufsize.toNat) (i := d.sym_next.toNat + 1)
    0 (by simp [h0]) (by simpa [h0] using base.rw) (by simp; omega)
  have third := store_symbol_byte (h := h1) (b := b)
    (buf := (buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) 0).set! (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) 0)
    (off := d.lit_bufsize.toNat) (i := d.sym_next.toNat + 2)
    c (by simp [h1]) (by simpa [h1] using base.rw) (by simp; omega)
  have state : hb.dstates ds = some d := by simpa [hb] using base.dstate
  have write : stDeflateState (some (.tab ds)) dn hb = .ok ((), hn) :=
    stDeflateState_tab state
  have inc := increment_literal_frequency (h := hn) (ds := ds) (d := dn) (i := c.toNat)
    (by simp [hn]) (by change c.toNat < d.dyn_ltree.size; rw [base.wf.1]; have := c.toNat_lt; omega)
  have first' : store_at d.sym_buf d.sym_next.toNat 0 h = .ok ((), h0) := by rw [base.sym]; exact first
  have second' : store_at d.sym_buf (d.sym_next.toNat + 1) 0 h0 = .ok ((), h1) := by
    rw [base.sym]
    simpa only [h0, h1, Zlib.Trees.Proofs.Out.setB_setB] using second
  have third' : store_at d.sym_buf (d.sym_next.toNat + 2) c h1 = .ok ((), hb) := by
    rw [base.sym]
    simpa only [h1, hb, literalBytes, Zlib.Trees.Proofs.Out.setB_setB] using third
  unfold tally_lit
  rw [bind_app, ldDeflateState_tab base.dstate]
  simp only [one, two, bind_app, first']
  change (do
    store_at d.sym_buf (d.sym_next.toNat + 1) 0
    store_at d.sym_buf (d.sym_next.toNat + 2) c
    stDeflateState (some (.tab ds)) dn
    freq_inc (.dstate_dyn_ltree ds) c.toNat
    let d ← ldDeflateState (some (.tab ds))
    pure (d.sym_next == d.sym_end)) h0 = _
  rw [bind_app, second']
  simp only [Zlib.Trees.Proofs.Out.setB_setB]
  change (do
    store_at d.sym_buf (d.sym_next.toNat + 2) c
    stDeflateState (some (.tab ds)) dn
    freq_inc (.dstate_dyn_ltree ds) c.toNat
    let d ← ldDeflateState (some (.tab ds))
    pure (d.sym_next == d.sym_end)) h1 = _
  rw [bind_app, third']
  simp only [Zlib.Trees.Proofs.Out.setB_setB]
  change (do
    stDeflateState (some (.tab ds)) dn
    freq_inc (.dstate_dyn_ltree ds) c.toNat
    let d ← ldDeflateState (some (.tab ds))
    pure (d.sym_next == d.sym_end)) hb = _
  rw [bind_app, write]
  simp only []
  rw [bind_app, inc]
  simp only [bind_app, ldDeflateState_tab (setD_dstates_same _ _ _)]
  simp [hn, hb, dn, literalState, setD_setD]

theorem literalState_tally (d : DeflateState) (c : UInt8) :
    literalState d c = Zlib.Trees.Proofs.Out.tallyRec d 0 c.toUInt32 := by
  have three : d.sym_next + 1 + 1 + 1 = d.sym_next + 3 := by
    rw [UInt32.add_assoc, UInt32.add_assoc]
    rfl
  simp only [literalState, Zlib.Trees.Proofs.Out.tallyRec, if_pos rfl, ite_true, three, UInt8.toNat_toUInt32]

/-- The strategy's strict, aligned symbol count supplies room for the
three actual stores. It does not assume output space for tree emission. -/
theorem literal_room {h : Heap} {ds : Nat} {d : DeflateState}
    (inv : DStInv h ds d) (strict : d.sym_next.toNat < d.sym_end.toNat) :
    d.sym_next.toNat + 3 ≤ d.sym_end.toNat := by
  have aligned := inv.sym.2.2.2
  have endAligned : d.sym_end.toNat % 3 = 0 := by rw [inv.sym.2.1]; omega
  omega

/-- The inline literal tally establishes its updated tree invariant on
the actual returned heap. This uses the proved mathematical tree-field
update, not an assumed call to _tr_tally. -/
theorem tally_literal_trees {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d b buf) (c : UInt8)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
      ds (literalState d c) b (literalBytes buf d c) := by
  have wf : (literalState d c).WellFormed := by
    rw [literalState_tally]
    exact Zlib.Trees.Proofs.Out.tallyRec_wf trees.base.wf _ _
  have base := trees.base.step (literalBytes buf d c) (by simp [literalBytes]) (literalState d c)
    wf rfl rfl rfl rfl rfl trees.base.pending_le
  have run : TreesRun ds (literalState d c) := by
    rw [literalState_tally]
    apply Zlib.Trees.Proofs.Out.tallyRec_run trees.run room trees.run.sym_next_mod
    have end_ := trees.base.sym_end
    have cap := trees.base.lit_hi
    omega
  exact ⟨base, run⟩

/-- `_tr_tally_lit(s, c, flush)` preserves DGood as well as the actual
tree invariant. A source-returned true flag marks exactly the full buffer. -/
theorem literal_good_after {h : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} (good : DGood h r ds z d)
    (trees : TreesInvAt h ds d b buf) (c : UInt8) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    DGood (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
      r ds z (literalState d c) := by
  have treeResult := tally_literal_trees trees c room
  let hb := Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)
  let dt := literalState d c
  have goodB : DGood hb r ds z d := good.bytes_set b (literalBytes buf d c) buf trees.base.bytes
    (by simp [literalBytes])
  have inv : DStInv hb ds dt :=
    { goodB.inv with
      wf := treeResult.base.wf
      blocks := goodB.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sym := ⟨goodB.inv.sym.1, goodB.inv.sym.2.1, treeResult.run.sym_next_le, treeResult.run.sym_next_mod⟩ }
  have shape := shape_setD goodB.live.hs dt
  refine ⟨?_, DStInv.congr (h := hb) (h' := setD hb ds dt) rfl rfl rfl rfl inv,
    shape.uniq goodB.uniq, shape.fresh rfl goodB.fresh, ⟨dt, b, literalBytes buf d c, treeResult⟩⟩
  exact ⟨by simpa only [ZStreamRef.get_setD] using goodB.live.hz, by simp [dt], good.live.zst,
    good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩

theorem tally_literal_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (c : UInt8) (strict : d.sym_next.toNat < d.sym_end.toNat) :
    ∃ b buf, h.bytes b = some buf ∧
      tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end,
        setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)) ∧
      DGood (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
        r ds z (literalState d c) := by
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have eq : d0 = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst d0
  have room := literal_room good.inv strict
  exact ⟨b, buf, trees.base.bytes, tally_literal_run trees.base c room, literal_good_after good trees c room⟩

theorem pending_write_chains {h : Heap} {r : ZStreamRef} {ds top b : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (chains : HeapChains h d top)
    (pending : d.pending_buf = .ref (.blk b) 0) (buf : Array UInt8) (c : UInt8) :
    HeapChains (setD (Zlib.Trees.Proofs.Out.setB h b buf) ds (literalState d c)) (literalState d c) top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have be : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  exact ⟨w, p, q, wa, pa, qa, win, prev, head,
    by simpa [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ blocks.wb] using hw,
    hp, hq, H⟩

theorem literal_count {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (base : TreesBase h ds d b buf) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) (c : UInt8) :
    (literalState d c).sym_next.toNat = d.sym_next.toNat + 3 := by
  have end_ := base.sym_end
  have cap := base.lit_hi
  change (d.sym_next + 3).toNat = _
  rw [UInt32.toNat_add]
  simp only [show (3 : UInt32).toNat = 3 from rfl]
  exact Nat.mod_eq_of_lt (by omega)

/-- A false full flag gives the strict symbol-count invariant needed by
the next actual tally. The true branch still needs real block emission. -/
theorem literal_not_full {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d b buf) (c : UInt8)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat)
    (flag : (d.sym_next + 3 == d.sym_end) = false) :
    (literalState d c).sym_next.toNat < (literalState d c).sym_end.toNat := by
  have next := literal_count trees.base room c
  have neq : d.sym_next + 3 ≠ d.sym_end := by simpa using flag
  have ne : (literalState d c).sym_next.toNat ≠ d.sym_end.toNat := by
    intro eq
    apply neq
    exact UInt32.toNat_inj.mp eq
  change (literalState d c).sym_next.toNat < d.sym_end.toNat
  omega

/-- The actual inline literal tally preserves representation and H on
the same result heap. Only its pending/symbol byte block and state change.
Room is derived from the aligned strict entry symbol count. -/
theorem tally_literal_good_chains {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d)
    (chains : HeapChains h d top) (c : UInt8) (strict : d.sym_next.toNat < d.sym_end.toNat) :
    ∃ b buf, h.bytes b = some buf ∧
      tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end,
        setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)) ∧
      DGood (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
        r ds z (literalState d c) ∧
      HeapChains (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
        (literalState d c) top ∧
      ((d.sym_next + 3 == d.sym_end) = false →
        (literalState d c).sym_next.toNat < (literalState d c).sym_end.toNat) := by
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have eq : d0 = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst d0
  have room := literal_room good.inv strict
  exact ⟨b, buf, trees.base.bytes, tally_literal_run trees.base c room, literal_good_after good trees c room,
    pending_write_chains good chains trees.base.pbuf _ _, literal_not_full trees c room⟩

end Zlib.Deflate.Engine.Proofs
