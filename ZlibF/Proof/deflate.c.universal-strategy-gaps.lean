import ZlibF.Proof.«deflate.c.universal-call-tail»

/-!
# deflate.c: the strategy facts `deflate_call` uses (batch B)

The exports of the strategy specs that `tail_step` takes as `StrategyGaps`:
the dispatch with any output room, including a full output after the header phase (M19), and
the meaning of the returned block state for the state after the strategy: no symbol after a block
or a finishing return (M6), no lazy literal and nothing pending after `block_done`, which comes
only without `Z_FINISH` (M9, M13, M20), and no lookahead after a finishing return (M14).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- **The dispatch keeps the invariant with any output room**: `dispatch_spec` from `StratIn`
(the checks of `deflate` without `avail_out ≠ 0`). -/
theorem dispatch_spec_in (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (inv : DInv h r ds z d) (entry : StratIn h r z d) (flush : Int32) :
    DispatchOut h r ds z d flush (dispatch (some (.tab ds)) flush d h) := by
  have safe : FlushSafeAt d.lit_bufsize.toNat := Block.flushSafeAt_of (tiny.at _)
  have lo := inv.good.inv.level_lo
  have hi := inv.good.inv.level_hi
  by_cases l0 : d.level = 0
  · obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := stored_spec_of inv entry flush l0
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inl ⟨l0, m⟩⟩
    simp only [C.run] at run
    simp [dispatch, l0, run]
  have l0' : (d.level == 0) = false := by simp [l0]
  by_cases hf : d.strategy = Z_HUFFMAN_ONLY
  · have s2 : d.strategy.toInt = 2 := by rw [hf]; rfl
    obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := huff_spec_of safe inv entry flush l0 s2
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf, run]
  have hf' : (d.strategy == Z_HUFFMAN_ONLY) = false := by simp [hf]
  have s2 : d.strategy.toInt ≠ 2 := fun e => hf (Int32.toInt_inj.mp (by rw [e]; rfl))
  by_cases rl : d.strategy = Z_RLE
  · have s3 : d.strategy.toInt = 3 := by rw [rl]; rfl
    obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := rle_spec_of safe inv entry flush l0 s3
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    simp [dispatch, l0', hf', rl, run, show Z_RLE ≠ Z_HUFFMAN_ONLY by decide]
  have rl' : (d.strategy == Z_RLE) = false := by simp [rl]
  have s3 : d.strategy.toInt ≠ 3 := fun e => rl (Int32.toInt_inj.mp (by rw [e]; rfl))
  have nz : d.level.toInt ≠ 0 := fun e => l0 (Int32.toInt_inj.mp (by simpa using e))
  by_cases fast : d.level.toInt ≤ 3
  · obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := fast_spec_of safe inv entry flush ⟨by omega, fast, s2, s3⟩
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    have values : d.level = 1 ∨ d.level = 2 ∨ d.level = 3 := by
      have : d.level.toInt = 1 ∨ d.level.toInt = 2 ∨ d.level.toInt = 3 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run
  · obtain ⟨b, a, z', d', run, i', bu, fr, m⟩ := slow_spec_of safe inv entry flush ⟨by omega, s2, s3⟩
    refine ⟨b, a, z', d', ?_, i', bu, fr, Or.inr ⟨l0, m⟩⟩
    simp only [C.run] at run
    have values : d.level = 4 ∨ d.level = 5 ∨ d.level = 6 ∨ d.level = 7 ∨ d.level = 8 ∨ d.level = 9 := by
      have : d.level.toInt = 4 ∨ d.level.toInt = 5 ∨ d.level.toInt = 6 ∨ d.level.toInt = 7 ∨
          d.level.toInt = 8 ∨ d.level.toInt = 9 := by omega
      simp only [← Int32.toInt_inj]; exact this
    unfold dispatch
    rcases values with e | e | e | e | e | e <;>
      simp [l0', hf', rl', e, config_at, configuration_table, bind_app, pure_app] <;> exact run

/-- **M19**: the dispatch with a full output, in the form of `StrategyGaps.noRoom`. -/
theorem gaps_noRoom (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (flush : Int32) (inv : DInv h r ds z d) (buffers : StreamBuffers h r)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (_full : z.avail_out = 0)
    (pend : d.pending = 0) (_busy : d.status = BUSY_STATE ∨ d.status = FINISH_STATE) :
    DispatchOut h r ds z d flush (dispatch (some (.tab ds)) flush d h) :=
  dispatch_spec_in tiny inv ⟨buffers, out, input, pend⟩ flush

/-- **M6, M9, M13, M20, M14**: what the returned block state says about the state after the
dispatch, for every run from the checks of `deflate` (any output room). -/
theorem gaps_facts (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {flush : Int32} {bstate : block_state} {after : Heap} {z' : ZStream} {d' : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pend : d.pending = 0)
    (run : dispatch (some (.tab ds)) flush d h = .ok (bstate, after))
    (hz : r.get after = some z') (hs : after.dstates ds = some d') :
    (bstate = block_done ∨ bstate = finish_started ∨ bstate = finish_done → d'.sym_next = 0) ∧
    (bstate = block_done → d'.match_available = 0 ∧ d'.pending = 0 ∧ flush ≠ Z_FINISH) ∧
    (bstate = finish_started ∨ bstate = finish_done → d'.lookahead = 0) := by
  obtain ⟨b, a, z1, d1, run1, inv1, _, fr, meaning⟩ := dispatch_spec_in tiny inv ⟨buffers, out, input, pend⟩ flush
  have e := Except.ok.inj (run.symm.trans run1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have zEq : z1 = z' := Option.some.inj (inv1.good.live.hz.symm.trans hz)
  have dEq : d1 = d' := Option.some.inj (inv1.good.live.hs.symm.trans hs)
  subst zEq dEq
  have shape := inv1.shape
  rcases meaning with ⟨l0, m⟩ | ⟨_, m⟩
  · have lv : d1.level = 0 := fr.2.level.trans l0
    have zero := shape.levelZero lv
    have idle : d1.match_available = 0 := by
      by_cases a0 : d1.match_available = 0
      · exact a0
      · have := (shape.lazyAvail a0).1; rw [lv] at this; exact absurd this (by decide)
    exact ⟨fun _ => zero.2.2, fun bd => ⟨idle, (m.blockDone bd).1, (m.blockDone bd).2⟩, fun _ => zero.2.1⟩
  · refine ⟨fun c => ?_, fun bd => ?_, m.finishLook⟩
    · rcases c with c | c | c
      · exact m.empty (Or.inl c)
      · exact m.startedEmpty c
      · exact m.empty (Or.inr c)
    · obtain ⟨p, a0, f⟩ := m.blockDone bd
      exact ⟨a0, p, f⟩

/-- **For M18**: a finishing return of the dispatch leaves no bits (the last block was flushed with
its windup), so `FINISH_STATE`, which `deflate` sets on such a return, starts with `bi_valid = 0`. -/
theorem gaps_finishBits (tiny : Block.TinyOverlay) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {flush : Int32} {bstate : block_state} {after : Heap} {d' : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pend : d.pending = 0)
    (run : dispatch (some (.tab ds)) flush d h = .ok (bstate, after)) (hs : after.dstates ds = some d')
    (finishing : bstate = finish_started ∨ bstate = finish_done) : d'.bi_valid = 0 := by
  obtain ⟨b, a, z1, d1, run1, inv1, _, _, meaning⟩ := dispatch_spec_in tiny inv ⟨buffers, out, input, pend⟩ flush
  have e := Except.ok.inj (run.symm.trans run1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have dEq : d1 = d' := Option.some.inj (inv1.good.live.hs.symm.trans hs)
  subst dEq
  have bits : d1.bi_valid.toInt = 0 := by
    rcases meaning with ⟨_, m⟩ | ⟨_, m⟩
    · exact m.finishBits finishing
    · exact m.finishBits finishing
  exact Int32.toInt_inj.mp (by rw [bits]; rfl)

end Zlib.Deflate.Universal.Call
