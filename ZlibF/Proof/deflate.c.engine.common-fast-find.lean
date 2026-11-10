import ZlibF.Proof.«deflate.c.engine.common-fast-match»
import ZlibF.Proof.«deflate.c.engine.search-full-storage»

/-! # Actual guarded fast matching preserves the current-position witness -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The fast search guard and its actual length store. -/
def fastFind (s : DeflateStatePtr) (candidate : UInt32) : M Unit := do
  let d ← ldDeflateState s
  if candidate != 0 && d.strstart - candidate ≤ d.w_size - MIN_LOOKAHEAD_u then
    let length ← longest_match s candidate
    wr s (fun d => {d with match_length := length})

/-- Actual guarded fast matching uses the initialized previous-length floor.
A selected length of at least three has a current-position byte witness.
An inactive guard retains the old short length. Physical comparison room
admits short EOF input; no successful matcher contract is assumed. -/
theorem fast_find_room_full_storage {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
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
    (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (previous : d.prev_length = 2) (short : d.match_length.toNat ≤ 2) :
    ∃ after pos len,
      fastFind (some (.tab ds)) candidate h = .ok ((), after) ∧
      DGood after r ds z (matchState d pos len) ∧
      HeapChains after (matchState d pos len) (d.strstart.toNat + 1) ∧
      len.toNat ≤ 258 ∧
      (3 ≤ len.toNat → len.toNat ≤ d.lookahead.toNat ∧
        GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat) ∧
      after.bytes = h.bytes ∧ after.words = h.words ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => b = ds) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases active : (candidate != 0 && d.strstart - candidate ≤ d.w_size - MIN_LOOKAHEAD_u) = true
  · have conditions := active
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at conditions
    have nz : candidate ≠ 0 := conditions.1
    have nonzero : 1 ≤ candidate.toNat := by
      have ne : candidate.toNat ≠ 0 := by intro eq; exact nz (UInt32.toNat_inj.mp eq)
      omega
    have window : 262 ≤ d.w_size.toNat := by
      rw [good.inv.wsize]
      have pow := Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_lo
      change 512 ≤ 2 ^ d.w_bits.toNat at pow
      omega
    have distance := machine_distance (older nz) window conditions.2
    obtain ⟨len, pos, run, goodA, chainsA, bound, clipped, matching, _⟩ :=
      fast_matcher_current_position good heapChains win prev head hw hp hq chains hash keyBound
        published link nonzero (older nz) distance range room previous
    refine ⟨setD h ds (matchState d pos len), pos, len, ?_, goodA, chainsA, bound,
      (fun large => ⟨clipped, matching large⟩), rfl, rfl, byte_frame_setD h ds _,
      state_store_full_storage good.live.hs _⟩
    unfold fastFind
    simp only [bind_app, ldDeflateState_tab good.live.hs, active, ite_true]
    exact run
  · refine ⟨h, d.match_start, d.match_length, ?_, ?_, ?_, by omega,
      (fun large => by omega), rfl, rfl, ByteFrame.refl h _, full_storage_refl h _⟩
    · unfold fastFind
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, ite_false]
      rfl
    · simpa only [matchState] using good
    · simpa only [matchState] using heapChains

end Zlib.Deflate.Engine.Proofs
