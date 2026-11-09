import ZlibF.Proof.«compress.c.local-search»

/-! # Local saved-endpoint representation for actual match consumption -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalMatchEndpoint
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalSearch
set_option autoImplicit false
set_option maxRecDepth 100000
variable {cutoff : Nat}

/-- These internal saved-endpoint producers retain old caller typed
collisions. The real insertion and scalar writes use the private local
representation, without changing the old global DGood interfaces. -/
theorem local_heap_chains_at_environment {h : Heap} {r : ZStreamRef} {ds top validEnd : Nat}
    {z : ZStream} {d : DeflateState} (good : LocalState h cutoff r ds z d) (chains : HeapChainsAt h d top validEnd) :
    ∃ w p q wa pa qa, HashEnv h d w q p wa qa pa ∧
      HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
        d.w_size.toNat top validEnd := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  obtain ⟨w0, p0, q0, b, blocks⟩ := good.inv.blocks
  have we : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pe : p0 = p := by
    simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.prev.symm
  have qe : q0 = q := by
    simpa only [head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  subst w0 p0 q0
  have hsize : d.hash_size.toNat ≤ qa.size := by
    obtain ⟨qa0, get, size⟩ := blocks.qa
    have eq : qa0 = qa := Option.some.inj (get.symm.trans hq)
    subst qa0
    omega
  have psize : d.w_size.toNat ≤ pa.size := by
    obtain ⟨pa0, get, size⟩ := blocks.pa
    have eq : pa0 = pa := Option.some.inj (get.symm.trans hp)
    subst pa0
    omega
  have mask : d.w_mask.toNat < d.w_size.toNat := by
    have pos : 0 < d.w_size.toNat := by rw [good.inv.wsize]; exact Nat.two_pow_pos _
    rw [good.inv.wmask]
    omega
  exact ⟨w, p, q, wa, pa, qa, ⟨win, hw, blocks.wro, head, hq, prev, hp,
    blocks.pq.symm, hsize, psize, mask, hash_parameters good.inv⟩, H⟩

theorem local_insert_string_good_chains_at {h : Heap} {r : ZStreamRef} {sr wb hb pb top bits validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {ha pa : Array UInt16}
    (good : LocalState h cutoff r sr z d) (env : HashEnv h d wb hb pb wa ha pa)
    (chains : HashChains (wfn ha) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top validEnd)
    (str : UInt32) (ws : d.w_size.toNat = 2 ^ bits)
    (mask : d.w_mask.toNat = d.w_size.toNat - 1)
    (ordered : top ≤ str.toNat)
    (data : str.toNat + 3 ≤ validEnd)
    (window : validEnd ≤ wa.size)
    (position : str.toNat < 65536)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ key after, INSERT_STRING (some (.tab sr)) str h =
        .ok ((wfn ha key.toNat).toUInt32, after) ∧
      LocalState after cutoff r sr z { d with ins_h := key } ∧
      HeapChainsAt after { d with ins_h := key } (str.toNat + 1) validEnd ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (str.toNat + 1) key := by
  obtain ⟨key, run, H, primed⟩ := insert_string_chains_at good.live.hs env chains str ws mask
    ordered data window position form
  let pa' := pa.set! (str &&& d.w_mask).toNat (wfn ha key.toNat)
  let ha' := ha.set! key.toNat str.toUInt16
  have prevGood := local_words_set good pb pa' pa env.pwords (by simp [pa'])
  have headGood := local_words_set prevGood hb ha' ha
    (by simpa [env.hne] using env.hwords) (by simp [ha'])
  have inv : DStInv _ sr { d with ins_h := key } :=
    { headGood.inv with blocks := headGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have updated := local_state_setD headGood (d' := { d with ins_h := key }) rfl good.live.status inv (by trkeep)
  refine ⟨key, _, run, ?_, H, primed⟩
  exact updated


theorem local_current_insert_storage_at {h : Heap} {r : ZStreamRef} {ds w top validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChainsAt h d top validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (ordered : top ≤ d.strstart.toNat)
    (range : validEnd ≤ d.window_size.toNat)
    (data : d.strstart.toNat + 3 ≤ validEnd)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h) :
    ∃ key candidate after,
      INSERT_STRING (some (.tab ds)) d.strstart h = .ok (candidate, after) ∧
      LocalState after cutoff r ds z { d with ins_h := key } ∧
      HeapChainsAt after { d with ins_h := key } (d.strstart.toNat + 1) validEnd ∧
      after.bytes = h.bytes ∧
      InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) key ∧ ByteFrame h after (fun i => i = ds) := by
  obtain ⟨w0, p, q, bytes, prev, head, env, H⟩ := local_heap_chains_at_environment good chains
  have wid : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win.symm
  subst w0
  have array : bytes = wa := Option.some.inj (env.wbytes.symm.trans get)
  subst bytes
  have extent := local_window_extent good win get
  have room : validEnd ≤ wa.size := by omega
  have bound : d.strstart.toNat < 65536 := by omega
  obtain ⟨key, after, run, goodA, chainsA, primed⟩ := local_insert_string_good_chains_at good env H d.strstart
    good.inv.wsize good.inv.wmask ordered (by omega) room bound form
  obtain ⟨other, _, _, exactRun⟩ := INSERT_STRING_ok good.live.hs env d.strstart (by omega) (by omega)
  have pair := Except.ok.inj (run.symm.trans exactRun)
  have frame : after.bytes = h.bytes := congrArg (fun x => x.2.bytes) pair
  exact ⟨key, _, after, run, goodA, chainsA, frame, primed,
    insert_string_byte_frame good.live.hs env d.strstart (by omega) (by omega) run⟩


theorem local_prepare_match_good_at {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (good : LocalState h cutoff r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (previous : 3 ≤ d.prev_length.toNat) (length : d.prev_length.toNat ≤ 258)
    (available : d.prev_length.toNat - 1 ≤ d.lookahead.toNat) :
    LocalState (setD h ds (prepareMatch d)) cutoff r ds z (prepareMatch d) ∧
      HeapChainsAt (setD h ds (prepareMatch d)) (prepareMatch d)
        (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat) ∧
      1 ≤ (prepareMatch d).prev_length.toNat ∧ (prepareMatch d).prev_length.toNat ≤ 256 ∧
      (prepareMatch d).strstart.toNat + (prepareMatch d).prev_length.toNat + 1 +
        (prepareMatch d).lookahead.toNat = d.strstart.toNat + d.lookahead.toNat := by
  have counts := prepare_match_counts_bounded d previous length available
  have inv : DStInv h ds (prepareMatch d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨local_state_setD good (d' := prepareMatch d) rfl good.live.status inv (by trkeep),
    chains.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    counts.2.2.1, counts.2.2.2.1, counts.2.2.2.2⟩

theorem local_bump_start_good_at {h : Heap} {r : ZStreamRef} {ds w top validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (chains : HeapChainsAt h d top validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat) :
    (bumpStart d).strstart.toNat = d.strstart.toNat + 1 ∧
      LocalState (setD h ds (bumpStart d)) cutoff r ds z (bumpStart d) ∧
      HeapChainsAt (setD h ds (bumpStart d)) (bumpStart d) top validEnd := by
  have extent := local_window_extent good win get
  have ss : (bumpStart d).strstart.toNat = d.strstart.toNat + 1 := by
    change (d.strstart + 1).toNat = _
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have inv : DStInv h ds (bumpStart d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨ss, local_state_setD good (d' := bumpStart d) rfl good.live.status inv (by trkeep),
    chains.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem local_count_down_good_at {h : Heap} {r : ZStreamRef} {ds top validEnd : Nat}
    {z : ZStream} {d : DeflateState}
    (good : LocalState h cutoff r ds z d) (chains : HeapChainsAt h d top validEnd) :
    LocalState (setD h ds (countDown d)) cutoff r ds z (countDown d) ∧
      HeapChainsAt (setD h ds (countDown d)) (countDown d) top validEnd := by
  have inv : DStInv h ds (countDown d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨local_state_setD good (d' := countDown d) rfl good.live.status inv (by trkeep),
    chains.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem local_finish_match_good_at {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d)
    (chains : HeapChainsAt h d (d.strstart.toNat + 1) validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (endpoint : validEnd = d.strstart.toNat + 1 + d.lookahead.toNat) :
    (finishMatch d).strstart.toNat = d.strstart.toNat + 1 ∧
      LocalState (setD h ds (finishMatch d)) cutoff r ds z (finishMatch d) ∧
      HeapChains (setD h ds (finishMatch d)) (finishMatch d) (finishMatch d).strstart.toNat ∧
      (finishMatch d).strstart.toNat + (finishMatch d).lookahead.toNat ≤ (finishMatch d).window_size.toNat := by
  have bumped := local_bump_start_good_at good chains win get room
  have inv : DStInv h ds (finishMatch d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have ss : (finishMatch d).strstart.toNat = d.strstart.toNat + 1 := bumped.1
  have saved : HeapChainsAt (setD h ds (finishMatch d)) (finishMatch d)
      (d.strstart.toNat + 1) validEnd := chains.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨ss, local_state_setD good (d' := finishMatch d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · rw [ss]
    exact saved.collapse (by change validEnd = (finishMatch d).strstart.toNat + d.lookahead.toNat; rw [ss]; exact endpoint)
  · change (finishMatch d).strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
    rw [ss]; exact room

theorem local_max_insert_nat_bounded {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (nonempty : 3 ≤ d.strstart.toNat + d.lookahead.toNat) :
    (d.strstart + d.lookahead - MIN_MATCH_u).toNat = d.strstart.toNat + d.lookahead.toNat - 3 := by
  have extent := local_window_extent good win get
  have sum : (d.strstart + d.lookahead).toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sum]; change 3 ≤ _; omega), sum]
  rfl

end ZlibF.Spec.Public.Proofs.CompressLocalMatchEndpoint
