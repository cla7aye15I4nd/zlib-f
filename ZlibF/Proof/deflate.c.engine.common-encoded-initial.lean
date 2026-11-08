import ZlibF.Proof.«deflate.c.engine.common-initial-observed»
import ZlibF.Proof.«deflate.c.engine.common-encoded-state»
import ZlibF.Proof.«deflate.c.engine.initial-encoding-checksum»

/-! # Real successful initialization establishes common-level observed encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real one-byte first call establishes the exact level-specific pending
header, empty accepted-input log and checksum on its actual returned heap.
The structural protocol comes from the separately proved actual call. -/
theorem common_split_header_encoding_of_run {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z z' : ZStream} {d result : DeflateState} {config : EngineConfig} {flush : Int32}
    (start : EngineStart h r ds z d)
    (boundary : BufferedBoundary h r ds z d (fun _ => 0) 0 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (one : z.avail_out = 1) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (low : 0 ≤ flush.toInt) (high : flush.toInt ≤ 5)
    (run : deflate (some r) flush h = .ok (Z_OK, after))
    (protocol : CommonSlowFinishBoundary after r ds z' result config) :
    CommonEncodingState after r ds z' result config [] [120] ∧
      Bytes after z.next_out 1 [120] := by
  obtain ⟨output, outGet, outRw, outBound, outside⟩ := caller_raw_output start.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := start.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans start.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lower := trees.base.lit_lo; omega
  have canonical := first_common_valid_one_source start trees.base.pbuf trees.base.bytes room trees.base.rw
    pointer outGet outRw separate outBound one valid flush low high
  have heapEq : after = levelHeaderOneHeap h r ds pb ob oo z d buf output :=
    (Prod.mk.inj (Except.ok.inj (run.symm.trans canonical))).2
  have stateEq : result = headerOneState d pb := by
    have get := protocol.good.live.hs
    rw [heapEq] at get
    simpa only [levelHeaderOneHeap, setD_dstates_same, Option.some.injEq] using get.symm
  obtain ⟨other, otherZ, otherD, finishRun, stateA, _buffersA, _accountA,
      _outA, _pendingA, statusA, _lastA⟩ :=
    first_common_finish_one_buffered start boundary buffers pointer one valid
  have actual := (first_common_valid_one_eq_finish start buffers pointer one valid flush low high).trans finishRun
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
  subst other
  have streams : otherZ = z' := Option.some.inj (stateA.good.live.hz.symm.trans protocol.good.live.hz)
  have states : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans protocol.good.live.hs)
  subst otherZ otherD
  have expectedGet : r.get (levelHeaderOneHeap h r ds pb ob oo z d buf output) =
      some (pendingStream z (.ref (.blk ob) (oo + 1)) 1) := by
    simp only [levelHeaderOneHeap, ZStreamRef.get_setD]
    apply ZStreamRef.get_put_same
    simpa only [levelHeaderOneBytes, stream_get_bytes] using start.good.live.hz
  have streamEq : z' = pendingStream z (.ref (.blk ob) (oo + 1)) 1 := by
    rw [← heapEq] at expectedGet
    exact Option.some.inj (protocol.good.live.hz.symm.trans expectedGet)
  have checksum : z'.adler = (ZlibF.Spec.adler32 []).toUInt64 := by
    rw [streamEq]
    change z.adler = (ZlibF.Spec.adler32 []).toUInt64
    rw [start.adler]
    rfl
  obtain ⟨written, encoding⟩ := common_header_one_output_encoding (pb := pb) start room pointer separate
    (by rw [one] at outBound; exact outBound)
  rw [← heapEq, ← stateEq] at encoding
  rw [← heapEq] at written
  have levelEq : d.level = config.level := congrArg EngineConfig.level boundary.configuration
  rw [levelEq] at encoding
  exact ⟨⟨protocol, checksum, Or.inl ⟨rfl, rfl, (fun _ => 0), stateA, statusA, encoding⟩⟩, written⟩

/-- Observed successful standard initialization at every normalized level
four through nine, followed by a legal caller replacement and any legal
one-byte first request, establishes the cumulative encoding invariant.
No allocation-success, representation-invariant or callee-contract premise
is required. First-call capacity one is the explicit scope of this result. -/
theorem common_observed_initialization_encoding {before initialized : Heap}
    {r : ZStreamRef} {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (domain : InitDomain before r version)
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (low : 4 ≤ p.level) (high : p.level ≤ 9)
    (actual : C.run (deflateInit_ (some r) level version 112) before = .ok (Z_OK, initialized)) :
    ∃ zf sf, EngineStart initialized r before.nextBlk zf sf ∧
      DeflateInitial before initialized r p ∧
      ∀ g, Rebuffer initialized g r → ∃ zg, r.get g = some zg ∧
        ∀ ob oo, zg.next_out = .ref (.blk ob) oo → zg.avail_out = 1 → StreamBuffers g r →
          (zg.avail_in ≠ 0 → zg.next_in ≠ .null) →
          ∀ flush : Int32, 0 ≤ flush.toInt → flush.toInt ≤ 5 →
            ∃ after z' result,
              deflate (some r) flush g = .ok (Z_OK, after) ∧
              CommonEncodingState after r before.nextBlk z' result (engineConfig sf) [] [120] ∧
              StreamBuffers after r ∧ StreamAccounting zg z' 0 1 ∧ Bytes after zg.next_out 1 [120] := by
  obtain ⟨zf, sf, start, initial, first⟩ := common_observed_initialization_protocol domain params low high actual
  obtain ⟨fresh, unique, globals, versionValue, z, getZ, allocators, _state⟩ := domain
  have allocation := common_init_success_allocations fresh unique globals getZ allocators versionValue params actual
  obtain ⟨computed, zi, si, run, startI, boundary, _frontier, _reachable, _raw, _checksum⟩ :=
    default_initialization_encoding_checksum fresh unique globals getZ allocators versionValue params allocation (fun _ => 0)
  have heaps : computed = initialized := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
  subst computed
  have streams : zi = zf := Option.some.inj (startI.good.live.hz.symm.trans start.good.live.hz)
  have states : si = sf := Option.some.inj (startI.good.live.hs.symm.trans start.good.live.hs)
  subst zi si
  have noHeader := initial_no_header start initial
  refine ⟨zf, sf, start, initial, ?_⟩
  intro g edit
  obtain ⟨zg, getG, firstG⟩ := first g edit
  obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit noHeader
  obtain ⟨zb, getB, boundaryG⟩ := rebuffer_buffered_boundary boundary edit noHeader
  have sameS : zs = zg := Option.some.inj (startG.good.live.hz.symm.trans getG)
  have sameB : zb = zg := Option.some.inj (getB.symm.trans getG)
  subst zs zb
  refine ⟨zg, getG, ?_⟩
  intro ob oo pointer one buffers valid flush flagLow flagHigh
  obtain ⟨after, z', result, actualFirst, protocolA, buffersA, accountA⟩ :=
    firstG ob oo pointer one buffers valid flush flagLow flagHigh
  obtain ⟨encodingA, writtenA⟩ := common_split_header_encoding_of_run startG boundaryG buffers pointer one valid
    flagLow flagHigh actualFirst protocolA
  exact ⟨after, z', result, actualFirst, encodingA, buffersA, accountA, writtenA⟩

end Zlib.Deflate.Engine.Proofs
