import ZlibF.Proof.«deflate.c.engine.initial»

/-! # Caller rebuffering preserves the default engine's private state

The caller may change every unowned allocation. The proof uses only the
public frame for the five owned objects, not whole-heap equality.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

theorem owned_live {h : Heap} {r : ZStreamRef} {ds x : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (owned : DeflateOwned ds d x) : h.live x := by
  apply DOwned.live good
  rcases owned with eq | win | prev | head | pending
  · exact Or.inl eq
  · exact Or.inr (Or.inl ⟨x, win, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, prev, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, head, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, pending, rfl⟩)))

theorem rebuffer_owned {h g : Heap} {r : ZStreamRef} {ds x : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (edit : Rebuffer h g r) (owned : DeflateOwned ds d x) :
    SlotSame h g x := by
  have streamOwn : StreamOwned h r x :=
    ⟨z, good.live.hz, Or.inr ⟨ds, d, good.live.zst, good.live.hs, owned⟩⟩
  exact edit.2.2.2.1.2.2.2.2.2 x (owned_live good owned) (by simpa using streamOwn)

/-- Rebuffering preserves DGood when there is no registered gzip header.
The default engine starts with no header. General gzip-header lifetime
needs its separate public memory condition. -/
theorem rebuffer_good_no_header {h g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (edit : Rebuffer h g r) (header : d.gzhead = none) :
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
  have inv : DStInv g ds d := { good.inv with blocks := ⟨w, p, q, b, buffer⟩, gz := Or.inl header }
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

theorem rebuffer_chains {h g : Heap} {r : ZStreamRef} {ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (edit : Rebuffer h g r) (chains : HeapChains h d top) :
    HeapChains g d top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  have sw := rebuffer_owned good edit (x := w) (Or.inr (Or.inl win))
  have sp := rebuffer_owned good edit (x := p) (Or.inr (Or.inr (Or.inl prev)))
  have sq := rebuffer_owned good edit (x := q) (Or.inr (Or.inr (Or.inr (Or.inl head))))
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, sw.1.trans hw, sp.2.1.trans hp, sq.2.1.trans hq, H⟩

/-- Caller input/output replacement preserves the default first-entry
facts. This includes arbitrary changes to other unowned allocations. -/
theorem rebuffer_engine_start {h g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', EngineStart g r ds z' d := by
  obtain ⟨z', _, changed, good⟩ := rebuffer_good_no_header start.good edit header
  refine ⟨z', { start with
    good := good, chains := rebuffer_chains start.good edit start.chains, adler := ?_ }⟩
  rw [changed]
  exact start.adler

/-- The public initialization relation identifies the same state record
as the engine boundary, so its no-header fact is available for rebuffering. -/
theorem initial_no_header {h g : Heap} {r : ZStreamRef} {z : ZStream} {d : DeflateState}
    {p : ZlibF.Spec.Api.DeflParams} (start : EngineStart g r h.nextBlk z d)
    (initial : DeflateInitial h g r p) : d.gzhead = none := by
  obtain ⟨zi, si, good, _, _, _, _, _, _, _, _, _, _, _, header, _⟩ := initial
  have eq : d = si := Option.some.inj (start.good.live.hs.symm.trans good.live.hs)
  rw [eq]
  exact header

/-- Successful default initialization followed by an arbitrary legal
caller buffer replacement reaches the engine with its established
representation and hash invariant. No engine invariant is a premise. -/
theorem default_engine_rebuffered {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (allocators : DefaultOrNull z) (versionValue : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ after zf sf, C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ StreamReachable .deflate after r ∧
      ∀ g, Rebuffer after g r → ∃ zg, EngineStart g r h.nextBlk zg sf ∧ StreamReachable .deflate g r := by
  obtain ⟨after, zf, sf, run, start, initial, reachable⟩ :=
    default_initialization_engine hf hu hg hz allocators versionValue params alloc
  refine ⟨after, zf, sf, run, start, reachable, ?_⟩
  intro g edit
  obtain ⟨zg, next⟩ := rebuffer_engine_start start edit (initial_no_header start initial)
  exact ⟨zg, next, StreamReachable.rebuffer reachable edit⟩

end Zlib.Deflate.Engine.Proofs
