import ZlibF.Proof.«deflate.c.engine.loop-phase»
import ZlibF.Proof.«deflate.c.engine.short-search»

/-! # The fast matcher selects a current-position byte witness, including at EOF -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast match-search call followed by its length store
produces a current-position match witness whenever length is at least
three. The initialized previous-length floor excludes stale positions.
The physical comparison room, not a 262-byte input minimum, admits EOF.
Insertion supplies the published chain premises before this source cut;
no longest_match execution contract is assumed. -/
theorem fast_matcher_current_position {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {key : Nat} {candidate : UInt32}
    (good : DGood h r ds z d) (heapChains : HeapChains h d (d.strstart.toNat + 1))
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
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length = 2) :
    ∃ len ms,
      (do let matched ← longest_match (some (.tab ds)) candidate
          wr (some (.tab ds)) (fun d => {d with match_length := matched})) h =
        .ok ((), setD h ds (matchState d ms len)) ∧
      DGood (setD h ds (matchState d ms len)) r ds z (matchState d ms len) ∧
      HeapChains (setD h ds (matchState d ms len)) (matchState d ms len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 ∧ len.toNat ≤ d.lookahead.toNat ∧
      (3 ≤ len.toNat → GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat len.toNat) ∧
      ConfigFrame d (matchState d ms len) := by
  obtain ⟨len, ms, best, run, lenEq, lower, upper, matching, _goodA, _chainsA⟩ :=
    longest_match_chains_room good heapChains win prev head hw hp hq chains hash keyBound published link
      nonzero older distance range room (by rw [previous]; decide)
  have clipped : lmResult best d.lookahead.toNat ≤ best := by unfold lmResult; split <;> omega
  have count : len.toNat = lmResult best d.lookahead.toNat := by
    rw [lenEq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have bestBound : len.toNat ≤ best := by rw [count]; exact clipped
  have lookBound : len.toNat ≤ d.lookahead.toNat := by rw [count]; unfold lmResult; split <;> omega
  have evidence : 3 ≤ len.toNat → GoodMatch wa d.strstart.toNat d.w_size.toNat ms.toNat len.toNat := by
    intro long
    rcases matching with same | improved
    · have equal : best = 2 := by simpa only [previous, show (2 : UInt32).toNat = 2 from rfl] using same.1
      omega
    · exact improved.2.take bestBound
  have safe := matchState_good good heapChains ms len
  refine ⟨len, ms, ?_, safe.1, safe.2, by omega, lookBound, evidence, rfl⟩
  rw [bind_app, run]
  simp [wrD_eq, hAt, matchState, setD, upd_upd]

end Zlib.Deflate.Engine.Proofs
