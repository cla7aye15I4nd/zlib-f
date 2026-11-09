import ZlibF.Proof.«deflate.c.engine.short-match-budget»
import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»
import ZlibF.Proof.«deflate.c.engine.strategy-boundary»

/-! # Actual refill preserves the cost facts needed by unavailable stored blocks -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The pending lazy candidate passed the real distance-three filter. -/
def ShortCandidateQuality (d : DeflateState) : Prop :=
  d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR

/-- A lost stored source can only persist beyond the default slide floor. -/
def StoredSourceFloor (d : DeflateState) : Prop :=
  d.block_start.toInt < 0 → 32506 ≤ d.strstart.toNat

/-- Actual default initialization establishes both added size facts and
the existing strategy boundary on the same heap. They are not assumed
public caller restrictions. Compression level keeps the original init
parameter domain; the subsequent slow-strategy proof selects its levels. -/
theorem default_initialization_size_facts {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h) (get : r.get h = some z)
    (allocator : DefaultOrNull z) (versionValue : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after z' result,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk z' result ∧
      StrategyBoundary after r h.nextBlk z' result input 0 0 [] (engineConfig result) ∧
      ShortCandidateQuality result ∧ StoredSourceFloor result ∧ result.w_size.toNat = 32768 := by
  obtain ⟨after, z', result, run, start, state, _initial, _reachable⟩ :=
    default_initialization_strategy_boundary fresh unique globals get allocator versionValue params allocations input
  refine ⟨after, z', result, run, start, state, ?_, ?_, ?_⟩
  · intro impossible
    rw [start.matchLength] at impossible
    exact False.elim ((by decide +kernel : (2 : UInt32) ≠ 3) impossible)
  · intro negative
    rw [start.blockStart] at negative
    change (0 : Int) < 0 at negative
    omega
  · rw [start.good.inv.wsize, start.windowBits]
    rfl

/-- The real refill can leave a retained candidate unchanged or slide both
its positions by the same window. Every taken default slide establishes
the source-position floor independently of its old block start. Read,
priming and padding preserve these same fields. This successful-run
observer composes the existing proved actual executions; it does not
assume a refill contract or claim complete size-history closure. -/
theorem fill_window_run_size_facts {h after : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8}
    {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (window : d.w_size.toNat = 32768)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (observed : fill_window (some (.tab ds)) h = .ok ((), after))
    (live : after.dstates ds = some result) : ShortCandidateQuality result ∧ StoredSourceFloor result := by
  have identify (computed : Heap) (state : DeflateState)
      (run : fill_window (some (.tab ds)) h = .ok ((), computed))
      (get : computed.dstates ds = some state)
      (facts : ShortCandidateQuality state ∧ StoredSourceFloor state) :
      ShortCandidateQuality result ∧ StoredSourceFloor result := by
    have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (run.symm.trans observed))).2
    rw [heaps] at get
    have same : state = result := Option.some.inj (get.symm.trans live)
    exact same ▸ facts
  by_cases empty : z.avail_in = 0
  · by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨computed, run, state⟩ := fill_window_slide_empty_pending_boundary boundary empty taken
      apply identify _ _ run state.good.live.hs
      have quality := slide_short_candidate_quality d candidate
      have lower := default_slide_start_floor boundary.good window taken
      exact ⟨quality, fun _ => lower⟩
    · obtain ⟨computed, run, state⟩ := fill_window_empty_pending_boundary boundary empty taken
      exact identify _ _ run state.good.live.hs ⟨candidate, floor⟩
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨used, computed, z', state, extended, run, boundaryA, _account, _start, _look,
        _insert, _wrap, _prefix, _stop, fields⟩ :=
        fill_window_slide_pending_boundary boundary short taken wrap buffers pointer empty
      apply identify _ _ run boundaryA.good.live.hs
      have quality := slide_short_candidate_quality d candidate
      have lower := default_slide_start_floor boundary.good window taken
      rw [fields]
      exact ⟨quality, fun _ => lower⟩
    · obtain ⟨used, computed, z', state, extended, run, boundaryA, _account, _start, _look,
        _insert, _wrap, _prefix, _stop, fields⟩ :=
        fill_window_pending_boundary boundary short taken wrap buffers pointer empty
      apply identify _ _ run boundaryA.good.live.hs
      rw [fields]
      exact ⟨candidate, floor⟩

end Zlib.Deflate.Engine.Proofs
