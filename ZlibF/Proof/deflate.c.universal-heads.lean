import ZlibF.Proof.«deflate.c.universal-invariant»

/-!
# deflate.c: no chain head waits for insertion

Between calls, every nonzero `head` entry is below the insertion frontier `strstart - insert`
(through one pending slide at level 0 after one stored slide). So a position that waits for
`fill_window` to insert it is never a chain head, and `deflateCopy`, which copies `prev` only
below the frontier, copies the `prev` slot of every position a walk can reach. A direct
`deflateResetKeep` breaks this (`docs/findings/deflate-copy-pending-prev`); it is outside the
deflate stream domain (`docs/deviations.md`).
-/

namespace Zlib.Deflate.Universal
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- **Every chain head is inserted** (tables as they are). -/
theorem DInv.heads_inserted {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (zero : d.«matches» = 0) :
    ∃ q qa, d.head = .ref (.blk q) 0 ∧ h.words q = some qa ∧
      ∀ k, k < d.hash_size.toNat → (wfn qa k).toNat ≠ 0 →
        (wfn qa k).toNat < d.strstart.toNat - d.insert.toNat := by
  obtain ⟨_, _, q, _, _, qa, _, _, head, _, _, hq, H⟩ := inv.hashing.chains zero
  exact ⟨q, qa, head, hq, fun k hk nz => Nat.lt_of_lt_of_le (head_lt H hk nz) (chainTop_le d)⟩

/-- **Every chain head is inserted**, at level 0 with one pending slide: read through the slide
that `slide_hash` will apply. -/
theorem DInv.slid_heads_inserted {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (one : d.«matches» = 1) :
    ∃ q qa, d.head = .ref (.blk q) 0 ∧ h.words q = some qa ∧
      ∀ k, k < d.hash_size.toNat → (slideVal d.w_size (wfn qa k)).toNat ≠ 0 →
        (slideVal d.w_size (wfn qa k)).toNat < d.strstart.toNat - d.insert.toNat := by
  obtain ⟨_, _, q, _, _, qa, _, _, head, _, _, hq, H⟩ := inv.hashing.slid one
  exact ⟨q, qa, head, hq, fun k hk nz =>
    Nat.lt_of_lt_of_le (head_lt (h1 := fun i => slideVal d.w_size (wfn qa i)) H hk nz) (chainTop_le d)⟩

end Zlib.Deflate.Universal
