import ZlibF.Proof.«deflate.c.engine.common-initial-protocol»
import ZlibF.Proof.«deflate.c.engine.common-finish-completes»

/-! # Actual common-level initialization reaches finite FINISH completion -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual one-byte header call preserves library tables and enters
BUSY, at every admitted standard compression level. -/
theorem first_common_finish_one_world {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d result : DeflateState}
    (initial : EngineStart h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (globals : LibraryGlobals h)
    (actual : deflate (some r) Z_FINISH h = .ok (Z_OK, after))
    (get : after.dstates ds = some result) : LibraryGlobals after ∧ result.status = BUSY_STATE := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have extent := trees.base.size; have lower := trees.base.lit_lo; omega
  have canonical := first_common_finish_one_source initial trees.base.pbuf trees.base.bytes room
    trees.base.rw pointer outGet outRw separate outBound one valid
  have heaps : after = levelHeaderOneHeap h r ds pb ob oo z d buf output :=
    (Prod.mk.inj (Except.ok.inj (actual.symm.trans canonical))).2
  have statics : after.static = h.static := by
    rw [heaps]
    simp only [levelHeaderOneHeap, levelHeaderOneBytes, setD_static, ZStreamRef.put_static]
  have states : result = headerOneState d pb := by
    rw [heaps] at get
    simp only [levelHeaderOneHeap, setD_dstates_same] at get
    exact Option.some.inj get.symm
  exact ⟨statics.trans globals, by rw [states]; rfl⟩

/-- Actual initialization at every slow standard level and a legal split
header establish finite completion for any fixed remaining readable input.
All subsequent calls and buffer replacements are real executions; the
source is consumed completely before STREAM_END. This FINISH-only result
does not establish ordinary all-flush encoded-history correctness. -/
theorem common_initialization_then_finite_finish {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (low : 4 ≤ p.level) (high : p.level ≤ 9)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) :
    ∃ initialized config,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, initialized) ∧
      DeflateInitial h initialized r p ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → zg.avail_out = 1 → StreamBuffers g r →
          (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∃ after z' result,
            C.run (deflate (some r) Z_FINISH) g = .ok (Z_OK, after) ∧
            CommonSlowFinishBoundary after r h.nextBlk z' result config ∧
            StreamBuffers after r ∧ StreamAccounting zg z' 0 1 ∧
            ∀ input, Bytes after z'.next_in z'.avail_in.toNat input → ∀ log : DataLog,
              ∃ final finalLog, DeflateCore.FinishContinuation r log.input input after log final finalLog ∧
                finalLog.input = log.input ++ input ∧ finalLog.result = Z_STREAM_END := by
  obtain ⟨initialized, zf, sf, initRun, start, initial, first⟩ :=
    common_initialization_split_finish_boundary hf hu hg hz ha hv params low high alloc
  have allocatorsF : DefAlloc zf := by
    obtain ⟨zi, _si, goodI, allocI, freeI, _rest⟩ := initial
    have streams : zi = zf := Option.some.inj (goodI.live.hz.symm.trans start.good.live.hz)
    exact ⟨by rw [← streams]; exact allocI, by rw [← streams]; exact freeI⟩
  have header := initial_no_header start initial
  refine ⟨initialized, engineConfig sf, initRun, initial, ?_⟩
  intro g edit
  obtain ⟨zg, getG, firstG⟩ := first g edit
  obtain ⟨otherZ, startG⟩ := rebuffer_engine_start start edit header
  have streams : otherZ = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
  subst otherZ
  have globalsG : LibraryGlobals g := edit.2.2.1
  have allocatorsG : DefAlloc zg := by
    obtain ⟨_fresh, _unique, _globals, _frame, old, next, oldGet, nextGet, fields⟩ := edit
    have oldSame : old = zf := Option.some.inj (oldGet.symm.trans start.good.live.hz)
    have nextSame : next = zg := Option.some.inj (nextGet.symm.trans getG)
    subst old next
    rw [fields]
    exact allocatorsF
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer one buffers valid
  obtain ⟨after, z', result, actual, stateA, buffersA, accountA⟩ :=
    firstG ob oo pointer one buffers valid
  obtain ⟨globalsA, statusA⟩ := first_common_finish_one_world startG buffers pointer one valid globalsG
    actual stateA.good.live.hs
  have allocatorsA : DefAlloc z' := by
    rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
    exact ⟨keepAlloc.trans allocatorsG.1, keepFree.trans allocatorsG.2⟩
  refine ⟨after, z', result, actual, stateA, buffersA, accountA, ?_⟩
  intro input snapshot log
  apply stateA.completes globalsA allocatorsA buffersA snapshot ?_ log
  intro impossible
  rw [statusA] at impossible
  cases (by decide : BUSY_STATE ≠ FINISH_STATE) impossible

end Zlib.Deflate.Engine.Proofs
