import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«inflate.c.base»
import ZlibF.Spec.Public.History

/-!
# The codec of a gz handle owns no part of the gz record's block

`GzCommon.recordFree : ¬ StreamOwned h (gzStrm i) i` after every codec step. It needs no new fact of the codec:
the gz record is the object of the `gzstates` table at block `i`, the codec's blocks are objects of other tables
(the deflate state in `dstates`, its window and `pending_buf` in `bytes`, `prev` and `head` in `words`; the
inflate state in `istates`, its window in `bytes`), and `Uniq` allows one object per block number over the seven
tables.
-/

namespace ZlibF.Spec.Public.GzRecordFree
open C ZlibF.Spec.Public
set_option autoImplicit false

/-- A block number with a gz record holds no deflate state, byte block or word block. -/
theorem deflate_tables {h : Heap} {i : Nat} {s : GzState} (uniq : Zlib.Deflate.Spec.Uniq h)
    (rec : h.gzstates i = some s) :
    h.dstates i = none ∧ h.bytes i = none ∧ h.words i = none := by
  have u := uniq i
  rw [rec] at u
  refine ⟨?_, ?_, ?_⟩
  · cases e : h.dstates i with
    | none => rfl
    | some _ => rw [e] at u; simp at u
  · cases e : h.bytes i with
    | none => rfl
    | some _ => rw [e] at u; simp at u
  · cases e : h.words i with
    | none => rfl
    | some _ => rw [e] at u; simp at u

/-- **A deflate stream owns no part of a gz record's block.** -/
theorem deflate_not_record {h : Heap} {r : ZStreamRef} {k : Nat} {z : ZStream} {d : DeflateState} {i : Nat}
    {s : GzState} (good : Zlib.Deflate.Spec.DGood h r k z d) (rec : h.gzstates i = some s) :
    ¬ StreamOwned h r i := by
  rintro ⟨z1, hz1, own⟩
  have zz : z1 = z := Option.some.inj (hz1.symm.trans good.live.hz)
  subst zz
  obtain ⟨hd, hb, hw⟩ := deflate_tables good.uniq rec
  rcases own with ⟨k', s', hst, _, _⟩ | ⟨k', s', hst, hs', own⟩
  · rw [good.live.zst] at hst; cases hst
  · rw [good.live.zst] at hst
    cases hst
    have ss : s' = d := Option.some.inj (hs'.symm.trans good.live.hs)
    subst ss
    obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
    rcases own with e | e | e | e | e
    · subst e; rw [hd] at hs'; cases hs'
    · rw [blocks.win] at e; cases e
      obtain ⟨a, ga, _⟩ := blocks.wa; rw [hb] at ga; cases ga
    · rw [blocks.prev] at e; cases e
      obtain ⟨a, ga, _⟩ := blocks.pa; rw [hw] at ga; cases ga
    · rw [blocks.head] at e; cases e
      obtain ⟨a, ga, _⟩ := blocks.qa; rw [hw] at ga; cases ga
    · rw [blocks.pbuf] at e; cases e
      obtain ⟨a, ga, _⟩ := blocks.ba; rw [hb] at ga; cases ga

/-- **An inflate stream owns no part of a gz record's block.** -/
theorem inflate_not_record {h : Heap} {r : ZStreamRef} {k : Nat} {z : ZStream} {st : InflateState} {i : Nat}
    {s : GzState} (good : Zlib.Inflate.Spec.Good h r k z st) (rec : h.gzstates i = some s) :
    ¬ StreamOwned h r i := by
  rintro ⟨z1, hz1, own⟩
  have zz : z1 = z := Option.some.inj (hz1.symm.trans good.live.hz)
  subst zz
  have u := good.uniq i
  rw [rec] at u
  have hi : h.istates i = none := by
    cases e : h.istates i with
    | none => rfl
    | some _ => rw [e] at u; simp at u
  have hb : h.bytes i = none := by
    cases e : h.bytes i with
    | none => rfl
    | some _ => rw [e] at u; simp at u
  rcases own with ⟨k', s', hst, hs', own⟩ | ⟨k', s', hst, _, _⟩
  · rw [good.live.zst] at hst
    cases hst
    have ss : s' = st := Option.some.inj (hs'.symm.trans good.live.hs)
    subst ss
    rcases own with e | e
    · subst e; rw [hi] at hs'; cases hs'
    · rcases good.inv.win.block with n | ⟨w, a, hwin, ga, _, _⟩
      · rw [n] at e; cases e
      · rw [hwin] at e; cases e; rw [hb] at ga; cases ga
  · rw [good.live.zst] at hst; cases hst

end ZlibF.Spec.Public.GzRecordFree
