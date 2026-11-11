import ZlibF.Proof.«inflate.c.default-local»
import ZlibF.Proof.«inflate.c.gzip-dispatch-state»

/-!
# inflate.c: the per-call header facts at public entry

The public call declares the local array `hbuf[4]` (`syncAlloc`). The gzip
header modes need, besides the representation, the attached header record's
caller memory, its `extra` buffer apart from the unread input, and in `EXTRA`
the length `EXLEN` stored. These are caller facts on the heap before the call
(`EntryHeaderFacts`). This file shows they give `HeaderLocal` at the start of
the body. With no header record they hold trivially.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The caller facts about the attached gzip header record at a public call. -/
structure EntryHeaderCore (h : Heap) (r : ZStreamRef) (s : InflateState) (z : ZStream) : Prop where
  record : HeaderMemory h r s.head true
  extraApart : ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
    Separate g.extra g.extra_max.toNat z.next_in z.avail_in.toNat
  extraLen : s.mode = EXTRA → ∀ i g, s.head = some (.tab i) → h.gzheaders i = some g →
    s.length ≤ g.extra_len

/-- The caller premise on the gzip header gives the attached record's memory. -/
theorem ActiveHeader.record {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (header : ActiveHeader h r) (live : Live h r zs z s) : HeaderMemory h r s.head true := by
  obtain ⟨z', get, inflate, _⟩ := header
  have same : z' = z := Option.some.inj (get.symm.trans live.hz)
  subst same
  exact inflate zs s live.zst live.hs

/-- The caller header facts are needed only when the call starts in `HEAD` .. `HCRC`. -/
def EntryHeaderFacts (h : Heap) (r : ZStreamRef) (s : InflateState) (z : ZStream) : Prop :=
  HEAD ≤ s.mode → s.mode ≤ HCRC → EntryHeaderCore h r s z

/-- Past the header modes the entry facts are vacuous. -/
theorem EntryHeaderFacts.of_mode {h : Heap} {r : ZStreamRef} {s : InflateState} {z : ZStream}
    (high : DICTID ≤ s.mode) : EntryHeaderFacts h r s z := by
  intro _ low
  rw [UInt32.le_iff_toNat_le] at high low
  change 16189 ≤ s.mode.toNat at high
  change s.mode.toNat ≤ 16188 at low
  omega

/-- With no header record the entry facts hold. -/
theorem EntryHeaderFacts.of_none {h : Heap} {r : ZStreamRef} {s : InflateState} {z : ZStream}
    (none : s.head = none) : EntryHeaderFacts h r s z := by
  intro _ _
  refine ⟨Or.inl none, ?_, ?_⟩
  · intro i g attached
    rw [none] at attached
    cases attached
  · intro _ i g attached
    rw [none] at attached
    cases attached

/-- A stream that does not accept gzip has no header record. -/
theorem EntryHeaderFacts.of_zlib {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (wrap : s.wrap = 1 ∨ s.wrap = 5) : EntryHeaderFacts h r s z :=
  EntryHeaderFacts.of_none (invariant.head_none wrap)

/-- A non-null pointer of a caller range names a live object of the heap. -/
theorem callerRange_live_ref {h : Heap} {r : ZStreamRef} {pointer : BPtr} {size : Nat} {writing : Bool}
    (range : CallerRange h r pointer size writing) (nonnull : pointer ≠ .null)
    {ref : BRef} {off : Nat} (at_ : pointer = .ref ref off) : ∃ a, Space.get h ref = some a := by
  rcases range with null | ⟨⟨_, readable⟩, _, _⟩
  · exact absurd null nonnull
  · rcases readable with ⟨null, _, _⟩ | ⟨ref', off', a, pointerEq, get, _, _⟩
    · exact absurd null nonnull
    · rw [at_] at pointerEq
      cases pointerEq
      exact ⟨a, get⟩

/-- A fresh block is not a live byte object. -/
theorem fresh_ref_ne {h : Heap} (fresh : Fresh h) {ref : BRef} {a : Array UInt8}
    (get : Space.get h ref = some a) : ref ≠ .blk h.nextBlk := by
  intro same
  subst ref
  have absent := (fresh_dead fresh (Nat.le_refl h.nextBlk)).1
  change h.bytes h.nextBlk = some a at get
  rw [get] at absent
  cases absent

/-- The header record's caller regions do not name the new local array. -/
theorem hbufApart_syncAlloc {c : Ctx} {h : Heap} {r : ZStreamRef} {head : GzHeaderPtr}
    (buf : c.hbuf = syncBuf h) (fresh : Fresh h) (record : HeaderMemory h r head true) :
    HbufApart c (syncAlloc h) head := by
  intro b at_ region member ref off pointer
  rw [buf] at at_
  unfold syncBuf at at_
  cases at_
  rw [HeaderRegions.of_headers head (syncAlloc_gzheaders h)] at member
  rcases record with none | ⟨i, g, attached, get, _, extra, name, comment⟩
  · rw [none] at member
    simp [HeaderRegions] at member
  · rw [attached] at member
    simp only [HeaderRegions, get, List.mem_cons, List.not_mem_nil, or_false] at member
    have nonnull : region.pointer ≠ .null := by rw [pointer]; intro e; cases e
    rcases member with rfl | rfl | rfl
    · obtain ⟨a, live⟩ := callerRange_live_ref (extra nonnull) nonnull pointer
      exact fresh_ref_ne fresh live
    · have range := name nonnull
      simp only [ite_true] at range
      obtain ⟨a, live⟩ := callerRange_live_ref range nonnull pointer
      exact fresh_ref_ne fresh live
    · have range := comment nonnull
      simp only [ite_true] at range
      obtain ⟨a, live⟩ := callerRange_live_ref range nonnull pointer
      exact fresh_ref_ne fresh live

/-- The header record's caller memory survives the local declaration. -/
theorem headerMemory_syncAlloc {h : Heap} {r : ZStreamRef} {head : GzHeaderPtr}
    (fresh : Fresh h) (record : HeaderMemory h r head true) : HeaderMemory (syncAlloc h) r head true := by
  rcases record with none | ⟨i, g, attached, get, notOwned, extra, name, comment⟩
  · exact Or.inl none
  refine Or.inr ⟨i, g, attached, get, ?_, ?_, ?_, ?_⟩
  · intro owned
    exact notOwned ((streamOwned_syncAlloc h r i).mp owned)
  · intro nonnull
    exact callerRange_syncAlloc fresh (extra nonnull)
  · intro nonnull
    have range := name nonnull
    simp only [ite_true] at range ⊢
    exact callerRange_syncAlloc fresh range
  · intro nonnull
    have range := comment nonnull
    simp only [ite_true] at range ⊢
    exact callerRange_syncAlloc fresh range

/-- The caller's header facts give the per-call header facts at the start of
the public body, on the heap with the local array declared. -/
theorem entry_header_local {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (fresh : Fresh h) (entry : EntryHeaderFacts h r s z) (flush : Int32) :
    HeaderLocal ⟨some r, some (.tab zs), syncBuf h, flush⟩ (syncAlloc h) r s (dispatchRegs z s) := by
  intro low high
  have entry := entry low high
  refine ⟨⟨h.nextBlk, syncJunk h, rfl, syncAlloc_bytes_buf h,
      by simp only [syncJunk, Array.size_ofFn], syncAlloc_ro_buf h⟩,
    hbufApart_syncAlloc rfl fresh entry.record,
    headerMemory_syncAlloc fresh entry.record, ?_, ?_⟩
  · intro i g attached get
    exact entry.extraApart i g attached get
  · intro extra i g attached get
    exact entry.extraLen extra i g attached get

#print axioms entry_header_local
end Zlib.Inflate.Proofs
