import ZlibF.Proof.«deflate.c.engine.slow-source»

/-! # The slow strategy's actual conditional match search -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def matchState (d : DeflateState) (pos len : UInt32) : DeflateState :=
  { d with match_start := pos, match_length := len }

theorem matchState_good {h : Heap} {r : ZStreamRef} {ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top) (pos len : UInt32) :
    DGood (setD h ds (matchState d pos len)) r ds z (matchState d pos len) ∧
      HeapChains (setD h ds (matchState d pos len)) (matchState d pos len) top := by
  have inv : DStInv h ds (matchState d pos len) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨good.setD' rfl good.live.status inv (by trkeep), by simpa only [HeapChains, matchState, setD] using chains⟩

def rejectShort (d : DeflateState) : Bool :=
  d.match_length ≤ 5 && (d.strategy == Z_FILTERED ||
    (d.match_length == MIN_MATCH_u && d.strstart - d.match_start > TOO_FAR))

/-- The source guard's unsigned distance has its mathematical meaning
once the actual old-head proof has established candidate < strstart. -/
theorem machine_distance {d : DeflateState} {candidate : UInt32}
    (older : candidate.toNat < d.strstart.toNat) (window : 262 ≤ d.w_size.toNat)
    (guard : d.strstart - candidate ≤ d.w_size - MIN_LOOKAHEAD_u) :
    d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262 := by
  rw [UInt32.le_iff_toNat_le,
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega),
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact window)] at guard
  exact guard

/-- A failed search may retain its input match. A search that does not
improve the previous lazy length may retain a stale position. A selected
improvement has a real matching-byte witness. The short filter may reduce
the length below MIN_MATCH.
-/
def SearchEvidence (d : DeflateState) (wa : Array UInt8) (pos len : UInt32) : Prop :=
  (len = d.match_length ∧ pos = d.match_start) ∨
    len.toNat ≤ d.prev_length.toNat ∨ len.toNat < 3 ∨
      GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat

/-- The actual matcher guard and short-match filter preserve the
representation and hash invariant. This is the source fragment of
slow_body_source, with all reads backed by the published heap arrays. -/
theorem slow_find_evidence {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
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
    (older : candidate ≠ 0 → candidate.toNat < d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat) (previous : d.prev_length.toNat ≤ 258)
    (oldLength : d.match_length.toNat ≤ 258) :
    ∃ after pos len, slowFind (some (.tab ds)) candidate h = .ok ((), after) ∧
      DGood after r ds z (matchState d pos len) ∧
      HeapChains after (matchState d pos len) (d.strstart.toNat + 1) ∧ len.toNat ≤ 258 ∧ SearchEvidence d wa pos len := by
  by_cases active : (candidate != 0 && d.prev_length < d.max_lazy_match &&
      d.strstart - candidate ≤ d.w_size - MIN_LOOKAHEAD_u) = true
  · have conditions := active
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at conditions
    have nz : candidate ≠ 0 := conditions.1.1
    have nonzero : 1 ≤ candidate.toNat := by
      have ne : candidate.toNat ≠ 0 := by intro eq; exact nz (UInt32.toNat_inj.mp eq)
      omega
    have wsize : 262 ≤ d.w_size.toNat := by
      rw [good.inv.wsize]
      have pow := Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_lo
      change 512 ≤ 2 ^ d.w_bits.toNat at pow
      omega
    have distance := machine_distance (older nz) wsize conditions.2
    obtain ⟨len, ms, best, run, lenEq, lower, upper, matching, _, _⟩ := longest_match_chains
      good heapChains win prev head hw hp hq chains hash keyBound published link nonzero (older nz)
      distance range lookahead previous
    have length : len.toNat ≤ 258 := by
      rw [lenEq]
      unfold lmResult
      rw [if_pos (by omega)]
      simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show best < 2 ^ 32 by omega)]
      exact upper
    have exactLength : len.toNat = best := by
      rw [lenEq]
      unfold lmResult
      rw [if_pos (by omega)]
      simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show best < 2 ^ 32 by omega)]
    have evidence : SearchEvidence d wa ms len := by
      rcases matching with same | improved
      · exact Or.inr (Or.inl (by rw [exactLength]; omega))
      · exact Or.inr (Or.inr (Or.inr (by rw [exactLength]; exact improved.2)))
    let dm := matchState d ms len
    let hm := setD h ds dm
    have write : wr (some (.tab ds)) (fun d => { d with match_length := len }) (hAt h ds d ms) =
        .ok ((), hm) := by simp [wrD_eq, hAt, hm, dm, matchState, setD, upd_upd]
    have state : hm.dstates ds = some dm := by simp [hm]
    by_cases reject : rejectShort dm = true
    · let df := matchState d ms 2
      have goodResult := matchState_good good heapChains ms 2
      refine ⟨setD h ds df, ms, 2, ?_, goodResult.1, goodResult.2, by decide, Or.inr (Or.inr (Or.inl (by decide)))⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [if_pos reject]
      simp [wrD_eq, state, hm, df, dm, matchState, setD_setD, MIN_MATCH_u]
    · have goodResult := matchState_good good heapChains ms len
      refine ⟨hm, ms, len, ?_, goodResult.1, goodResult.2, length, evidence⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [if_neg reject]
      rfl
  · refine ⟨h, d.match_start, d.match_length, ?_, ?_, ?_, oldLength, Or.inl ⟨rfl, rfl⟩⟩
    · unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs]
      rw [if_neg active]
      rfl
    · simpa only [matchState] using good
    · simpa only [matchState] using heapChains

theorem slow_find_preserves {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
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
    (older : candidate ≠ 0 → candidate.toNat < d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat) (previous : d.prev_length.toNat ≤ 258)
    (oldLength : d.match_length.toNat ≤ 258) :
    ∃ after pos len, slowFind (some (.tab ds)) candidate h = .ok ((), after) ∧
      DGood after r ds z (matchState d pos len) ∧
      HeapChains after (matchState d pos len) (d.strstart.toNat + 1) ∧ len.toNat ≤ 258 := by
  obtain ⟨after, pos, len, run, goodA, chainsA, length, _⟩ :=
    slow_find_evidence good heapChains win prev head hw hp hq chains hash keyBound published link
      older range lookahead previous oldLength
  exact ⟨after, pos, len, run, goodA, chainsA, length⟩

end Zlib.Deflate.Engine.Proofs
