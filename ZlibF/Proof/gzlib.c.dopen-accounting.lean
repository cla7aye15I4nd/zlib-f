import ZlibF.Proof.«gzlib.c.dopen-entry»

/-!
# gzlib.c: removal of the actual descriptor temporary

The helpers transfer initialized open-state facts to the same wrapper heap
after its final free. Existing public goals and their domains remain unchanged.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Freeing one known byte block cannot introduce a new live identity. -/
theorem descriptorReleased_fresh (h : Heap) (d : Nat) (a : Array UInt8)
    (hd : h.bytes d = some a) (hf : Fresh h) : Fresh (descriptorReleased h d) := by
  intro b hb hLive
  apply hf b hb
  by_cases he : b = d
  · subst b
    exact Or.inl (by simp [hd])
  · simpa [descriptorReleased, he, Heap.live] using hLive

/-- Freeing the byte table entry preserves uniqueness of every object kind. -/
theorem descriptorReleased_uniq (h : Heap) (d : Nat) (hu : Uniq h) :
    Uniq (descriptorReleased h d) := by
  intro b
  have hb := hu b
  by_cases he : b = d
  · subst b
    simp only [descriptorReleased, upd_same, cnt_none]
    omega
  · simpa [descriptorReleased, he] using hb

/-- The exact free changes only its old block and removes exactly that identity. -/
theorem descriptorReleased_ledger (h : Heap) (d : Nat) (a : Array UInt8)
    (hd : h.bytes d = some a) (hu : Uniq h) :
    ZlibF.Spec.Public.Frame h (descriptorReleased h d) (fun b => b = d) ∧
    ZlibF.Spec.Public.LiveChange h (descriptorReleased h d) (fun _ => False) (fun b => b = d) := by
  have honly := writerPath_only h d a hu hd
  constructor
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    simp [descriptorReleased, hb]
  · intro b
    by_cases he : b = d
    · subst b
      simp [descriptorReleased, Heap.live, honly.1, honly.2.1, honly.2.2.1,
        honly.2.2.2.1, honly.2.2.2.2.1, honly.2.2.2.2.2]
    · simp [descriptorReleased, Heap.live, he]

/-- Removing another block retains an actual terminated byte view. -/
theorem descriptorReleased_cstring (h : Heap) (d pb off : Nat) (name : List UInt8)
    (hpb : pb ≠ d) (hc : ZlibF.Spec.Public.CString h (.ref (.blk pb) off) name) :
    ZlibF.Spec.Public.CString (descriptorReleased h d) (.ref (.blk pb) off) name := by
  rcases hc with ⟨hb, hn, hl⟩
  refine ⟨?_, hn, hl⟩
  rcases hb with hz | ⟨r, bo, a, hp, hg, hbound, he⟩
  · simp at hz
  · cases hp
    exact Or.inr ⟨.blk pb, off, a, rfl, by simpa [descriptorReleased, hpb] using hg, hbound, he⟩

/-- A successful initialized open state remains valid after freeing its
separate descriptor temporary. Separation concerns the actual path identity.
No unwritten pointer is initialized by this operation. -/
theorem descriptorReleased_OpenState (h : Heap) (i d : Nat) (s : GzState)
    (mode : ZlibF.Spec.Api.GzMode) (level : Int) (strategy : Nat) (direct : Int)
    (fd : Int32) (name : List UInt8) (a : Array UInt8)
    (ho : ZlibF.Spec.Public.OpenState h i s mode level strategy direct fd name)
    (hd : h.bytes d = some a) (hsep : s.path ≠ .ref (.blk d) 0) :
    ZlibF.Spec.Public.OpenState (descriptorReleased h d) i s mode level strategy direct fd name := by
  rcases ho with ⟨hv, hm, hfd, hpath, hlevel, hstrategy, hdir, hsize, hwant,
    herr, hmsg, hhave, hpos, hpast, hagain, hskip, havail, hread⟩
  rcases hv with ⟨hstate, hmode, hf, hu, hg, hprivate, _, _, hwmin, hwmax, _, _⟩
  obtain ⟨privateName, hc, hbuf⟩ := hprivate
  obtain ⟨pb, bytes, hptr, hbytes, hro, hcap⟩ := hbuf
  have hpb : pb ≠ d := by
    intro he
    subst pb
    exact hsep hptr
  have hc' : ZlibF.Spec.Public.CString (descriptorReleased h d) s.path privateName := by
    rw [hptr] at hc ⊢
    exact descriptorReleased_cstring h d pb 0 privateName hpb hc
  have hp' : ZlibF.Spec.Public.CString (descriptorReleased h d) s.path name := by
    rw [hptr] at hpath ⊢
    exact descriptorReleased_cstring h d pb 0 name hpb hpath
  have hv' : ZlibF.Spec.Public.GzValid (descriptorReleased h d) i s := by
    refine ⟨hstate, hmode, descriptorReleased_fresh h d a hd hf,
      descriptorReleased_uniq h d hu, hg, ⟨privateName, hc', ?_⟩,
      Or.inl hmsg, fun _ => hmsg, hwmin, hwmax, ?_, ?_⟩
    · refine ⟨pb, bytes, hptr, ?_, hro, hcap⟩
      simpa [descriptorReleased, hpb] using hbytes
    · intro hz
      exact False.elim (hz hsize)
    · intro hz
      exact False.elim (hz hhave)
  exact ⟨hv', hm, hfd, hp', hlevel, hstrategy, hdir, hsize, hwant,
    herr, hmsg, hhave, hpos, hpast, hagain, hskip, havail, hread⟩

/-- The successful open's inactive buffers do not make ownership depend on
the removed temporary or on an otherwise changed heap. -/
theorem descriptorOwned_zero_heap (h h' : Heap) (i : Nat) (s : GzState)
    (hs : s.size = 0) (b : Nat) :
    ZlibF.Spec.Public.GzOwned h i s b ↔ ZlibF.Spec.Public.GzOwned h' i s b := by
  simp [ZlibF.Spec.Public.GzOwned, hs]

/-- The wrapper's first real allocation adds exactly its temporary path. -/
theorem descriptorAllocated_ledger (h : Heap) (hf : Fresh h) :
    ZlibF.Spec.Public.Frame h (descriptorAllocatedHeap h) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (descriptorAllocatedHeap h)
      (fun b => b = h.nextBlk) (fun _ => False) := by
  constructor
  · refine ⟨rfl, rfl, rfl, by simp [descriptorAllocatedHeap], by simp [descriptorAllocatedHeap], ?_⟩
    intro b hl _
    have hb : b ≠ h.nextBlk := fun he => hf h.nextBlk (Nat.le_refl _) (he ▸ hl)
    simp [descriptorAllocatedHeap, hb]
  · intro b
    by_cases he : b = h.nextBlk
    · subst b
      simp [descriptorAllocatedHeap, Heap.live]
    · simp [descriptorAllocatedHeap, Heap.live, he]

/-- Caller objects survive the complete allocation/format prefix, and the
only newly live object is the actual descriptor temporary. -/
theorem descriptorEntry_ledger (h : Heap) (fd : Int32) (hf : Fresh h) :
    ZlibF.Spec.Public.Frame h (descriptorEntryHeap h fd) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (descriptorEntryHeap h fd)
      (fun b => b = h.nextBlk) (fun _ => False) := by
  have ha := descriptorAllocated_ledger h hf
  have ht := descriptorFormatted_ledger (descriptorAllocatedHeap h) h.nextBlk
    (descriptorAllocatedBytes h) fd (by simp [descriptorAllocatedHeap])
    (Fresh.slotUsed_next (descriptorAllocated_fresh h hf))
  constructor
  · obtain ⟨s1, o1, g1, n1, a1, f1⟩ := ha.1
    obtain ⟨s2, o2, g2, n2, a2, f2⟩ := ht.1
    refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2,
      Nat.le_trans a1 a2, ?_⟩
    intro b hl _
    have hbd : b ≠ h.nextBlk := fun he => hf h.nextBlk (Nat.le_refl _) (he ▸ hl)
    have hmid : (descriptorAllocatedHeap h).live b := (ha.2 b).2 (Or.inl ⟨hl, by simp⟩)
    obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hl (by simp)
    obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hmid hbd
    exact ⟨b2.trans b1, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
      i2.trans i1, s2.trans s1, r2.trans r1⟩
  · intro b
    exact (ht.2.1 b).trans (by simpa using ha.2 b)

/-- The complete actual wrapper preserves every original caller allocation,
including after its temporary-path free. The inner frame is a proved heap fact. -/
theorem descriptorCaller_frame (h : Heap) (fd : Int32) (inner : Heap) (hf : Fresh h)
    (hi : ZlibF.Spec.Public.Frame (descriptorEntryHeap h fd) inner (fun _ => False)) :
    ZlibF.Spec.Public.Frame h (descriptorReleased inner h.nextBlk) (fun _ => False) := by
  have he := descriptorEntry_ledger h fd hf
  obtain ⟨s1, o1, g1, n1, a1, f1⟩ := he.1
  obtain ⟨s2, o2, g2, n2, a2, f2⟩ := hi
  refine ⟨s1.trans s2, o1.trans o2, g1.trans g2, Nat.le_trans n1 n2,
    Nat.le_trans a1 a2, ?_⟩
  intro b hl _
  have hbd : b ≠ h.nextBlk := fun hb => hf h.nextBlk (Nat.le_refl _) (hb ▸ hl)
  have hmid : (descriptorEntryHeap h fd).live b := (he.2 b).2 (Or.inl ⟨hl, by simp⟩)
  obtain ⟨b1, w1, z1, g1, d1, i1, s1, r1⟩ := f1 b hl (by simp)
  obtain ⟨b2, w2, z2, g2, d2, i2, s2, r2⟩ := f2 b hmid (by simp)
  refine ⟨?_, w2.trans w1, z2.trans z1, g2.trans g1, d2.trans d1,
    i2.trans i1, s2.trans s1, r2.trans r1⟩
  simpa [descriptorReleased, hbd] using b2.trans b1

/-- The preserved caller temporary has no object of another kind; its final
free removes exactly that identity even without a global inner-state invariant. -/
theorem descriptor_temp_release_ledger (h : Heap) (fd : Int32) (inner : Heap)
    (hu : Uniq (descriptorEntryHeap h fd))
    (hi : ZlibF.Spec.Public.Frame (descriptorEntryHeap h fd) inner (fun _ => False)) :
    ZlibF.Spec.Public.LiveChange inner (descriptorReleased inner h.nextBlk)
      (fun _ => False) (fun b => b = h.nextBlk) := by
  have hb := (descriptorEntry_temp h fd).1
  have hl : (descriptorEntryHeap h fd).live h.nextBlk := Or.inl (by simp [hb])
  have honly := writerPath_only _ h.nextBlk _ hu hb
  obtain ⟨_, hw, hz, hg, hd, hi', hs, _⟩ := hi.2.2.2.2.2 h.nextBlk hl (by simp)
  intro b
  by_cases he : b = h.nextBlk
  · subst b
    simp [descriptorReleased, Heap.live, hw, hz, hg, hd, hi', hs,
      honly.1, honly.2.1, honly.2.2.1, honly.2.2.2.1, honly.2.2.2.2.1, honly.2.2.2.2.2]
  · simp [descriptorReleased, Heap.live, he]

/-- The wrapper prefix and final free cancel their actual temporary in the
ledger. All remaining new identities are exactly those created by inner open. -/
theorem descriptorCaller_ledger (h : Heap) (fd : Int32) (inner : Heap) (created : Nat → Prop)
    (hf : Fresh h) (hu : Uniq (descriptorEntryHeap h fd))
    (hi : ZlibF.Spec.Public.Frame (descriptorEntryHeap h fd) inner (fun _ => False))
    (hl : ZlibF.Spec.Public.LiveChange (descriptorEntryHeap h fd) inner created (fun _ => False))
    (hno : ¬ created h.nextBlk) :
    ZlibF.Spec.Public.LiveChange h (descriptorReleased inner h.nextBlk) created (fun _ => False) := by
  have he := (descriptorEntry_ledger h fd hf).2
  have hr := descriptor_temp_release_ledger h fd inner hu hi
  intro b
  rw [hr b, hl b, he b]
  by_cases hb : b = h.nextBlk
  · subst b
    have hn := hf h.nextBlk (Nat.le_refl _)
    simp [hn, hno]
  · simp [hb]

/-- An actual inner allocation failure is still an actual allocation failure
of the wrapper, using the original oracle and final allocation counter. -/
theorem descriptorCaller_allocation_failed (h : Heap) (fd : Int32) (inner : Heap)
    (ha : ZlibF.Spec.Public.AllocationFailed (descriptorEntryHeap h fd) inner) :
    ZlibF.Spec.Public.AllocationFailed h (descriptorReleased inner h.nextBlk) := by
  obtain ⟨n, hlo, hhi, he⟩ := ha
  refine ⟨n, ?_, hhi, ?_⟩
  · rw [(descriptorEntry_counts h fd).2.1] at hlo
    omega
  · simpa only [(descriptorEntry_counts h fd).2.2] using he

#print axioms descriptorCaller_allocation_failed
#print axioms descriptorEntry_ledger
#print axioms descriptorCaller_frame
#print axioms descriptorCaller_ledger
#print axioms descriptorReleased_fresh
#print axioms descriptorReleased_uniq
#print axioms descriptorReleased_ledger
#print axioms descriptorReleased_cstring
#print axioms descriptorReleased_OpenState
#print axioms descriptorOwned_zero_heap
end Zlib.Gzlib.Proofs
