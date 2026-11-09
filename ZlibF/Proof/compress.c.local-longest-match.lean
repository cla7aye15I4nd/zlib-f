import ZlibF.Proof.«compress.c.local-hash»
import ZlibF.Proof.«deflate.c.engine.short-search»
import ZlibF.Proof.«deflate.c.engine.full-storage»

/-! # Actual longest-match execution with local private representation

Physical comparison room and the real published hash-chain link construct
LMEnv. The existing actual matcher proof supplies its clipped match and
exact state-only result heap. Caller typed-table collisions remain admitted.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalLongestMatch
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The matcher reads only actual state, window and chain arrays. Global
uniqueness is not needed to construct its physical comparison environment. -/
theorem local_match_environment_room {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {key : Nat} {candidate : UInt32}
    (good : LocalState h cutoff r ds z d)
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (head : d.head = .ref (.blk q) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa) (hq : h.words q = some qa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat))
    (hash : (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat = key)
    (keyBound : key < d.hash_size.toNat) (published : (wfn qa key).toNat = d.strstart.toNat)
    (link : (wfn pa (d.strstart.toNat &&& (d.w_size.toNat - 1))).toNat = candidate.toNat)
    (nonzero : 1 ≤ candidate.toNat) (older : candidate.toNat < d.strstart.toNat)
    (distance : d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258) :
    LMEnv h ds d w p wa pa candidate := by
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
  · exact chain_ok_of_chains (hash_parameters good.inv) chains hash keyBound published link nonzero older distance

/-- `local uInt longest_match(deflate_state *s, IPos cur_match)`.
The general matcher theorem already handles clipping to short lookahead.
This heap bridge obtains its comparison room from the explicit physical
window bound, rather than assuming at least 262 real input bytes. -/
theorem local_longest_match_chains_room {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {key : Nat} {candidate : UInt32}
    (good : LocalState h cutoff r ds z d) (heapChains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (head : d.head = .ref (.blk q) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa) (hq : h.words q = some qa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat))
    (hash : (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat = key)
    (keyBound : key < d.hash_size.toNat) (published : (wfn qa key).toNat = d.strstart.toNat)
    (link : (wfn pa (d.strstart.toNat &&& (d.w_size.toNat - 1))).toNat = candidate.toNat)
    (nonzero : 1 ≤ candidate.toNat) (older : candidate.toNat < d.strstart.toNat)
    (distance : d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258) :
    ∃ (len ms : UInt32) (best : Nat),
      longest_match (some (.tab ds)) candidate h = .ok (len, hAt h ds d ms) ∧
      len = UInt32.ofNat (lmResult best d.lookahead.toNat) ∧
      d.prev_length.toNat ≤ best ∧ best ≤ 258 ∧
      ((best = d.prev_length.toNat ∧ ms = d.match_start) ∨
        (d.prev_length.toNat < best ∧ GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat best)) ∧
      LocalState (hAt h ds d ms) cutoff r ds z { d with match_start := ms } ∧
      HeapChains (hAt h ds d ms) { d with match_start := ms } (d.strstart.toNat + 1) ∧
      SlowRecordFrame d { d with match_start := ms } ∧
      Shape h (hAt h ds d ms) ∧ Frame h (hAt h ds d ms) (fun owner => owner = ds) ∧
      LiveChange h (hAt h ds d ms) (fun _ => False) (fun _ => False) ∧
      (hAt h ds d ms).nalloc = h.nalloc ∧ (hAt h ds d ms).nextBlk = h.nextBlk := by
  have env := local_match_environment_room good win prev head hw hp hq chains hash keyBound published
    link nonzero older distance range room previous
  obtain ⟨len, after, ms, best, run, result, eq, lower, upper, matching⟩ := longest_match_ok env
  subst after
  have inv : DStInv h ds { d with match_start := ms } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have kept := ZlibF.Spec.Public.Proofs.CompressLocalHash.local_state_setD good (d' := { d with match_start := ms }) rfl good.live.status inv (by trkeep)
  have shape : Shape h (hAt h ds d ms) := shape_setD good.live.hs _
  refine ⟨len, ms, best, run, result, lower, upper, matching, kept, ?_, rfl, shape,
    state_store_full_frame h ds _, full_shape_live_change shape, rfl, rfl⟩
  simpa only [HeapChains, hAt, setD] using heapChains

end ZlibF.Spec.Public.Proofs.CompressLocalLongestMatch
