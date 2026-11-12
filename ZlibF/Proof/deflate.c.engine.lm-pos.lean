import ZlibF.Proof.«deflate.c.engine.lm-safe»
import ZlibF.Proof.«deflate.c.engine.pos-chains»
import ZlibF.Proof.«deflate.c.engine.short-search»

/-! # `longest_match` on the heap from the walk fact

`match_environment_walk` and `longest_match_walk_room` are `match_environment_room` and
`longest_match_chains_room` with the chain premise replaced by the walk fact that safety needs: every position on
the chain from the candidate is in `[1, strstart)` (`chain_pos_ok` gives it from positional chains). The match is
a `SafeMatch`. `LMEnv.toS`: the exact environment gives the positional one.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The exact environment gives the positional one. -/
theorem LMEnv.toS {h0 : Heap} {sr wb pb : Nat} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16} {c : UInt32}
    (E : LMEnv h0 sr d wb pb wa pa c) : LMEnvS h0 sr d wb pb wa pa c :=
  ⟨E.hd, E.win, E.wbytes, E.prevp, E.pwords, E.wsb, E.wmask, E.psize, E.asize, E.room, E.lale, E.plle, E.c1,
    E.clt, E.cdist, fun p hp => ⟨(E.chain p hp).1, (E.chain p hp).2.1⟩⟩

theorem match_environment_walk {h : Heap} {r : ZStreamRef} {ds w p : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16}
    {candidate : UInt32}
    (good : DGood h r ds z d)
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa)
    (walk : ∀ p, Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262))
      candidate.toNat p → 1 ≤ p ∧ p < d.strstart.toNat)
    (nonzero : 1 ≤ candidate.toNat) (older : candidate.toNat < d.strstart.toNat)
    (distance : d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258) :
    LMEnvS h ds d w p wa pa candidate := by
  obtain ⟨w0, p0, q0, b, blocks⟩ := good.inv.blocks
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pe : p0 = p := by simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.prev.symm
  subst w0 p0
  obtain ⟨wa0, getW, sizeW⟩ := blocks.wa
  obtain ⟨pa0, getP, sizeP⟩ := blocks.pa
  have eqW : wa0 = wa := Option.some.inj (getW.symm.trans hw)
  have eqP : pa0 = pa := Option.some.inj (getP.symm.trans hp)
  subst wa0 pa0
  have window : d.strstart.toNat + d.lookahead.toNat ≤ 2 * d.w_size.toNat := by
    simpa only [good.inv.wsz] using range
  have physical : d.strstart.toNat + 262 ≤ 2 * d.w_size.toNat := by
    simpa only [good.inv.wsz] using room
  refine ⟨good.live.hs, win, hw, prev, hp,
    ⟨d.w_bits.toNat, good.inv.wsize, good.inv.wbits_lo, good.inv.wbits_hi⟩, ?_,
    by omega, by omega, by omega, by omega, previous, nonzero, older, distance, ?_⟩
  · apply UInt32.toNat_inj.mp
    rw [good.inv.wmask]
    have positive : 1 ≤ d.w_size.toNat := by
      rw [good.inv.wsize]
      have := Nat.two_pow_pos d.w_bits.toNat
      omega
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using positive)]
    rfl
  · exact walk

theorem longest_match_walk_room {h : Heap} {r : ZStreamRef} {ds w p : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa : Array UInt16}
    {candidate : UInt32}
    (good : DGood h r ds z d)
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa)
    (walk : ∀ p, Chain (wfn pa) (d.w_size.toNat - 1) (lmLimit d.strstart.toNat (d.w_size.toNat - 262))
      candidate.toNat p → 1 ≤ p ∧ p < d.strstart.toNat)
    (nonzero : 1 ≤ candidate.toNat) (older : candidate.toNat < d.strstart.toNat)
    (distance : d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258) :
    ∃ (len ms : UInt32) (best : Nat),
      longest_match (some (.tab ds)) candidate h = .ok (len, hAt h ds d ms) ∧
      len = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
        (d.prev_length.toNat < best ∧ SafeMatch d.strstart.toNat d.w_size.toNat ms.toNat best)) ∧
      DGood (hAt h ds d ms) r ds z { d with match_start := ms } := by
  have env := match_environment_walk good win prev hw hp walk nonzero older distance range room previous
  obtain ⟨len, after, ms, best, run, result, eq, lower, upper, matching⟩ := longest_match_safe env
  subst after
  have inv : DStInv h ds { d with match_start := ms } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have kept := good.setD' (d' := { d with match_start := ms }) rfl good.live.status inv (by trkeep)
  exact ⟨len, ms, best, run, result, lower, upper, matching, kept⟩

end Zlib.Deflate.Engine.Proofs
