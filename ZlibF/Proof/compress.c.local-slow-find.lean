import ZlibF.Proof.«compress.c.local-longest-match»

/-! # Actual conditional search and short filtering with local private storage -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalSlowFind
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalLongestMatch
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Private scalar updates retain the local representation and hash
chains without constraining any old caller typed-table occupancy. -/
theorem local_match_state {h : Heap} {r : ZStreamRef} {cutoff ds top : Nat}
    {z : ZStream} {d : DeflateState} (good : LocalState h cutoff r ds z d)
    (chains : HeapChains h d top) (pos len : UInt32) :
    LocalState (setD h ds (matchState d pos len)) cutoff r ds z (matchState d pos len) ∧
      HeapChains (setD h ds (matchState d pos len)) (matchState d pos len) top := by
  have inv : DStInv h ds (matchState d pos len) :=
    {good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl}
  exact ⟨local_state_setD good rfl good.live.status inv (by trkeep),
    by simpa only [HeapChains,matchState,setD] using chains⟩

/-- Actual guarded matching, including nonzero candidates and the real
short-match rejection, preserves all typed slots outside the private
state record. Physical comparison room is explicit. -/
theorem local_slow_find_room {h : Heap} {r : ZStreamRef} {cutoff ds w p q : Nat}
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
    (older : candidate ≠ 0 → candidate.toNat < d.strstart.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat) (previous : d.prev_length.toNat ≤ 258)
    (oldLength : d.match_length.toNat ≤ 258) :
    ∃ after pos len, slowFind (some (.tab ds)) candidate h = .ok ((), after) ∧
      LocalState after cutoff r ds z (matchState d pos len) ∧
      HeapChains after (matchState d pos len) (d.strstart.toNat + 1) ∧ len.toNat ≤ 258 ∧ SearchEvidence d wa pos len ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      (3 ≤ d.lookahead.toNat → d.match_length.toNat ≤ d.lookahead.toNat → len.toNat ≤ d.lookahead.toNat) ∧
      Shape h after ∧ Frame h after (fun b => b = ds) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
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
    obtain ⟨len, ms, best, run, lenEq, lower, upper, matching, _local, _chains, _record, _shape, _frame, _live, _alloc, _next⟩ := local_longest_match_chains_room
      good heapChains win prev head hw hp hq chains hash keyBound published link nonzero (older nz)
      distance range room previous
    have clippedBound : lmResult best d.lookahead.toNat ≤ best := by
      unfold lmResult
      split <;> omega
    have count : len.toNat = lmResult best d.lookahead.toNat := by
      rw [lenEq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have bestBound : len.toNat ≤ best := by rw [count]; exact clippedBound
    have lookBound : len.toNat ≤ d.lookahead.toNat := by rw [count]; unfold lmResult; split <;> omega
    have length : len.toNat ≤ 258 := Nat.le_trans bestBound upper
    have evidence : SearchEvidence d wa ms len := by
      rcases matching with same | improved
      · exact Or.inr (Or.inl (by rw [same.1] at bestBound; exact bestBound))
      · exact Or.inr (Or.inr (Or.inr (improved.2.take bestBound)))
    let dm := matchState d ms len
    let hm := setD h ds dm
    have write : wr (some (.tab ds)) (fun d => { d with match_length := len }) (hAt h ds d ms) =
        .ok ((), hm) := by simp [wrD_eq, hAt, hm, dm, matchState, setD, upd_upd]
    have state : hm.dstates ds = some dm := by simp [hm]
    by_cases reject : rejectShort dm = true
    · let df := matchState d ms 2
      have goodResult := local_match_state good heapChains ms 2
      refine ⟨setD h ds df, ms, 2, ?_, goodResult.1, goodResult.2, by decide, Or.inr (Or.inr (Or.inl (by decide))), rfl, byte_frame_setD h ds df, (fun enough _ => by change 2 ≤ d.lookahead.toNat; omega), state_store_full_storage good.live.hs df⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, ite_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [ite_eq_left reject]
      simp [wrD_eq, hm, df, dm, matchState, setD_setD, MIN_MATCH_u]
    · have goodResult := local_match_state good heapChains ms len
      refine ⟨hm, ms, len, ?_, goodResult.1, goodResult.2, length, evidence, rfl, byte_frame_setD h ds dm, (fun _ _ => lookBound), state_store_full_storage good.live.hs dm⟩
      unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, ite_true, run, write,
        ldDeflateState_tab state]
      change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
        else pure ()) hm = _
      rw [ite_eq_right reject]
      rfl
  · refine ⟨h, d.match_start, d.match_length, ?_, ?_, ?_, oldLength, Or.inl ⟨rfl, rfl⟩, rfl, ByteFrame.refl h _, (fun _ oldBound => oldBound), full_storage_refl h _⟩
    · unfold slowFind
      simp only [bind_app, ldDeflateState_tab good.live.hs]
      rw [ite_eq_right active]
      rfl
    · simpa only [matchState] using good
    · simpa only [matchState] using heapChains


end ZlibF.Spec.Public.Proofs.CompressLocalSlowFind
