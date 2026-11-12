import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Proof.«deflate.c.engine.rebuffer»

/-!
# deflate.c: the invariant across the caller's part of the history

Batch A of the deflate skeleton: `DInv.owned` (the blocks the history owns are the five blocks of
the state) and `DInv.rebuffer` (caller rebuffering keeps the invariant). Rebuffering may change
every block the stream does not own and the four buffer fields of the stream record; the
invariant reads only the owned blocks, the static tables and the other fields of the record.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The owned blocks of the invariant are the owned blocks of the history. -/
theorem DInv.owned {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (b : Nat) : StreamOwned h r b ↔ DeflateOwned ds d b := by
  have live := inv.good.live
  constructor
  · rintro ⟨z', get, (⟨i, s, state, _, _⟩ | ⟨i, s, state, dstate, owned⟩)⟩
    · have same : z' = z := Option.some.inj (get.symm.trans live.hz)
      subst same
      rw [live.zst] at state
      cases state
    · have same : z' = z := Option.some.inj (get.symm.trans live.hz)
      subst same
      rw [live.zst] at state
      cases state
      have sd : s = d := Option.some.inj (dstate.symm.trans live.hs)
      subst sd
      exact owned
  · intro owned
    exact ⟨z, live.hz, Or.inr ⟨ds, d, live.zst, live.hs, owned⟩⟩

/-- Rebuffering keeps `DGood`, for every gzip header pointer (`GzOk` reads only the pointer). -/
theorem rebuffer_good {h g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (edit : Rebuffer h g r) :
    ∃ z', r.get g = some z' ∧
      z' = { z with
        next_in := z'.next_in, avail_in := z'.avail_in,
        next_out := z'.next_out, avail_out := z'.avail_out } ∧ DGood g r ds z' d := by
  have edits := edit
  obtain ⟨fresh, uniq, globals, frame, old, new, oldGet, newGet, changed⟩ := edits
  have zeq : old = z := Option.some.inj (oldGet.symm.trans good.live.hz)
  subst old
  have slot := rebuffer_owned good edit (x := ds) (Or.inl rfl)
  have state : g.dstates ds = some d := slot.2.2.2.2.1.trans good.live.hs
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have sw := rebuffer_owned good edit (x := w) (Or.inr (Or.inl blocks.win))
  have sp := rebuffer_owned good edit (x := p) (Or.inr (Or.inr (Or.inl blocks.prev)))
  have sq := rebuffer_owned good edit (x := q) (Or.inr (Or.inr (Or.inr (Or.inl blocks.head))))
  have sb := rebuffer_owned good edit (x := b) (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf))))
  have buffer : DBlocks g d w p q b := by
    refine { blocks with
      wa := ?_, wro := sw.2.2.2.2.2.2.2.trans blocks.wro,
      pa := ?_, qa := ?_, ba := ?_, bro := sb.2.2.2.2.2.2.2.trans blocks.bro }
    · simpa only [sw.1] using blocks.wa
    · simpa only [sp.2.1] using blocks.pa
    · simpa only [sq.2.1] using blocks.qa
    · simpa only [sb.1] using blocks.ba
  have inv : DStInv g ds d := { good.inv with blocks := ⟨w, p, q, b, buffer⟩, gz := good.inv.gz }
  have trees : Zlib.Trees.Proofs.Out.TreesInv g ds := by
    obtain ⟨d0, tb, bytes, base, run⟩ := good.trees
    have eq : d0 = d := Option.some.inj (base.dstate.symm.trans good.live.hs)
    subst d0
    have st := rebuffer_owned good edit (x := tb) (Or.inr (Or.inr (Or.inr (Or.inr base.pbuf))))
    exact ⟨d, tb, bytes, { base with
      dstate := state,
      static := by rw [← frame.1]; exact base.static,
      bytes := st.1.trans base.bytes, rw := st.2.2.2.2.2.2.2.trans base.rw }, run⟩
  refine ⟨new, newGet, changed, ⟨?_, inv, uniq, fresh, trees⟩⟩
  refine ⟨newGet, state, ?_, good.live.back, good.live.status, ?_, ?_⟩
  all_goals rw [changed]
  · exact good.live.zst
  · exact good.live.zalloc
  · exact good.live.zfree

/-- Caller rebuffering keeps the invariant. -/
theorem DInv.rebuffer {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (rebuffer : Rebuffer h after r) :
    ∃ z', r.get after = some z' ∧ DInv after r ds z' d := by
  have good := inv.good
  obtain ⟨z', get, changed, good'⟩ := rebuffer_good good rebuffer
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have sw := rebuffer_owned good rebuffer (x := w) (Or.inr (Or.inl blocks.win))
  have sp := rebuffer_owned good rebuffer (x := p) (Or.inr (Or.inr (Or.inl blocks.prev)))
  have sq := rebuffer_owned good rebuffer (x := q) (Or.inr (Or.inr (Or.inr (Or.inl blocks.head))))
  have sb := rebuffer_owned good rebuffer (x := b) (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf))))
  refine ⟨z', get, good', ?_, rebuffer.2.2.1, inv.shape, ?_, ?_⟩
  · rw [changed]; exact inv.alloc
  · refine ⟨fun zero => ?_, fun one => ?_⟩
    · obtain ⟨w', p', q', wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := inv.hashing.chains zero
      have ew : w' = w := by rw [blocks.win] at win; cases win; rfl
      have ep : p' = p := by rw [blocks.prev] at prev; cases prev; rfl
      have eq : q' = q := by rw [blocks.head] at head; cases head; rfl
      subst ew ep eq
      exact ⟨w', p', q', wa, pa, qa, win, prev, head, sw.1.trans hw, sp.2.1.trans hp, sq.2.1.trans hq, H⟩
    · obtain ⟨w', p', q', wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := inv.hashing.slid one
      have ew : w' = w := by rw [blocks.win] at win; cases win; rfl
      have ep : p' = p := by rw [blocks.prev] at prev; cases prev; rfl
      have eq : q' = q := by rw [blocks.head] at head; cases head; rfl
      subst ew ep eq
      exact ⟨w', p', q', wa, pa, qa, win, prev, head, sw.1.trans hw, sp.2.1.trans hp, sq.2.1.trans hq, H⟩
  · refine ⟨?_, inv.symbols.clear, inv.symbols.below⟩
    obtain ⟨xs, ⟨b', a, pbuf, bytes, ledger⟩, near⟩ := inv.symbols.recorded
    have eb : b' = b := by rw [blocks.pbuf] at pbuf; cases pbuf; rfl
    subst eb
    exact ⟨xs, ⟨b', a, pbuf, sb.1.trans bytes, ledger⟩, near⟩

end Zlib.Deflate.Universal

#print axioms Zlib.Deflate.Universal.DInv.owned
#print axioms Zlib.Deflate.Universal.DInv.rebuffer
