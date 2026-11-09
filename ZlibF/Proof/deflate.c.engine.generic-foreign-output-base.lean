import ZlibF.Proof.«deflate.c.engine.caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.pending-bits»

/-! Foreign embedded-depth output adapters. These lemmas do not change the public buffer domain. -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem writable_reference_cases {h : Heap} {ref : BRef} {off n : Nat}
    (writable : Writable h (.ref ref off) n) :
    (∃ b, ref = .blk b) ∨ (∃ owner, ref = .dstate_depth owner) := by
  rcases writable with impossible | ⟨r, i, a, pointer, get, ro, bound⟩
  · cases impossible.1
  · have same : r = ref := (Ptr.ref.inj pointer).1.symm
    subst r
    cases ref <;> simp_all [Space.ro]

theorem foreign_depth_owner_before_frontier {h : Heap} {owner : Nat} {foreign : DeflateState}
    (fresh : Fresh h) (get : h.dstates owner = some foreign) : owner < h.nextBlk := by
  by_cases before : owner < h.nextBlk
  · exact before
  · exact False.elim (fresh owner (by omega) (by simp [Heap.live, get]))

theorem foreign_depth_owner_not_private {h : Heap} {r : ZStreamRef} {ds owner off n : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d)
    (caller : CallerRange h r (.ref (.dstate_depth owner) off) n true) : owner ≠ ds := by
  rcases caller with impossible | ⟨_, _, outside⟩
  · cases impossible
  · intro same
    exact outside owner rfl ((stream_owned_deflate good owner).mpr (Or.inl same))

theorem foreign_depth_put_exact {h : Heap} {owner : Nat} {foreign : DeflateState}
    (get : h.dstates owner = some foreign) (next : Array UInt8) :
    Space.put h (BRef.dstate_depth owner) next = setD h owner { foreign with depth := next } := by
  exact BRef.put_dstate_depth get next

theorem foreign_depth_write_good {h : Heap} {r : ZStreamRef} {ds owner : Nat}
    {z : ZStream} {d foreign : DeflateState} (good : DGood h r ds z d)
    (get : h.dstates owner = some foreign) (different : ds ≠ owner) (next : Array UInt8) :
    DGood (setD h owner { foreign with depth := next }) r ds z d := by
  let after := setD h owner { foreign with depth := next }
  have state : after.dstates ds = some d := by
    simpa only [after, setD, upd_ne _ _ _ _ different] using good.live.hs
  have shape := shape_setD get { foreign with depth := next }
  exact ⟨{ good.live with hz := by simpa using good.live.hz, hs := state },
    DStInv.congr (h := h) (h' := after) rfl rfl rfl rfl good.inv,
    shape.uniq good.uniq, shape.fresh rfl good.fresh,
    TreesInv.keep good.trees good.live.hs rfl rfl rfl state good.inv.wf (by trkeep) good.inv.pending_le⟩

theorem foreign_depth_copy_buffer_frame {h : Heap} {owner off sourceOff n : Nat}
    {foreign : DeflateState} (get : h.dstates owner = some foreign) (source : Array UInt8)
    (bound : off + n ≤ foreign.depth.size) :
    BufferFrame h (setD h owner { foreign with depth := copyRange foreign.depth source off sourceOff n })
      (fun _ => False) [⟨.ref (.dstate_depth owner) off, n⟩] := by
  let next := copyRange foreign.depth source off sourceOff n
  let after := setD h owner { foreign with depth := next }
  have restored : restoreRegions h after [⟨.ref (.dstate_depth owner) off, n⟩] = h := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil, BRef.get_dstate_depth get]
    rw [foreign_depth_put_exact (foreign := { foreign with depth := next }) (by simp [after])]
    simp only [after, setD_setD]
    exact setD_self get
  refine ⟨?_, ?_⟩
  · rw [restored]
    exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  · intro region mem ref i a pointer old
    simp only [List.mem_singleton] at mem
    subst region
    have eqs := Ptr.ref.inj pointer
    cases eqs.1
    cases eqs.2
    have equal : a = foreign.depth := Option.some.inj (old.symm.trans (BRef.get_dstate_depth get))
    subst a
    refine ⟨next, BRef.get_dstate_depth (show after.dstates owner = some { foreign with depth := next } from by simp [after]), size_copyRange _ _ _ _ _, ?_⟩
    intro j _ outside
    rw [getElem?_copyRange _ _ _ _ _ _ bound]
    have apart : ¬ (off ≤ j ∧ j < off + n) := by
      intro inside
      apply outside
      exact ⟨⟨.ref (.dstate_depth owner) off,n⟩, by simp, off,rfl,inside⟩
    simp only [apart, ite_false]

end Zlib.Deflate.Engine.Proofs
