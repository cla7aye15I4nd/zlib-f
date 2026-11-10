import ZlibF.Proof.«inflate.c.whole-epoch-call-cut»
import ZlibF.Proof.«inflate.c.whole-epoch-dictionary-transition»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Two real observations of one stream resolve to the same private state. -/
theorem observed_state_unique {h : Heap} {r : ZStreamRef} {i j : Nat} {z v : ZStream} {s t : InflateState}
    (left : Good h r i z s) (right : Good h r j v t) : s = t := by
  have streams : z = v := Option.some.inj (left.live.hz.symm.trans right.live.hz)
  subst v
  have indices : i = j := by simpa using left.live.zst.symm.trans right.live.zst
  subst j
  exact Option.some.inj (left.live.hs.symm.trans right.live.hs)

/-- The reviewed source invariant with the additional actual default
wrapper scalars required by generic HEAD/DICTID consumers. -/
structure ScopedInvariant (h : Heap) (r : ZStreamRef) (log : DataLog) where
  core : Invariant h r log
  wrapperOrigins : WrapperOrigins core.source.point.state

theorem ScopedInvariant.init {before after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit before)
    (actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)) :
    Nonempty (ScopedInvariant after r {}) := by
  obtain ⟨core⟩ := Invariant.init domain platform actual
  obtain ⟨point, owner, _head, _bits, _hold⟩ := CausalInput.AtPublic.init domain platform actual
  have streamEq : core.source.point.z = point.z :=
    Option.some.inj (core.source.point.good.live.hz.symm.trans point.good.live.hz)
  have indexEq : core.source.point.zs = point.zs := by
    have other := point.good.live.zst
    rw [← streamEq] at other
    simpa using core.source.point.good.live.zst.symm.trans other
  have index : core.source.point.zs = before.nextBlk := indexEq.trans owner
  have allocation := ProtocolWindow.successful_init_allocation domain actual
  obtain ⟨fresh, _unique, _globals, validVersion, z, get, allocators, _tail⟩ := domain
  obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have expected : C.run (inflateInit2_ (some r) 15 version 112) before =
      .ok (Z_OK, initOkHeap before r z 5 15) := by
    exact inflateInit2_success get fresh allocation allocators.1 allocators.2 nonnull first
      (by decide +kernel)
  have heapEq : after = initOkHeap before r z 5 15 :=
    congrArg Prod.snd (Except.ok.inj (actual.symm.trans expected))
  have stateEq : core.source.point.state = resetKeepState before.nextBlk (resetPre (reset2Pre 5 15 (initState r))) := by
    apply Option.some.inj
    rw [← core.source.point.good.live.hs, index, heapEq]
    simp [initOkHeap]
  refine ⟨⟨core, ?_⟩⟩
  rw [stateEq]
  exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem ScopedInvariant.rebuffer {h after : Heap} {r : ZStreamRef} {log : DataLog}
    (before : ScopedInvariant h r log) (edit : Rebuffer h after r)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) : Nonempty (ScopedInvariant after r log) := by
  obtain ⟨core⟩ := before.core.rebuffer edit platform
  obtain ⟨_stream, _fields, kept⟩ := rebuffer_inflate_good before.core.source.point.good edit
  have same := observed_state_unique core.source.point.good kept
  exact ⟨core, same ▸ before.wrapperOrigins⟩

theorem ScopedInvariant.dictionary
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {source : BPtr} {len : UInt32} {bytes : List UInt8} {rc : Int32}
    (before : ScopedInvariant h r log)
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (range : CallerRange h r source len.toNat false) (input : Bytes h source len.toNat bytes)
    (actual : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after))
    (allowed : rc ≠ Z_OK ∨ pending = true) :
    Nonempty (ScopedInvariant after r {log with dictionary := if rc = Z_OK then bytes else log.dictionary}) := by
  obtain ⟨core⟩ := before.core.dictionary trace scope range input actual allowed
  obtain ⟨code, heap, state, run, current, outcomes⟩ :=
    inflateSetDictionary_source_frame before.core.origin before.core.allocator range input
  have pair := Except.ok.inj (run.symm.trans actual)
  cases pair
  have same := observed_state_unique core.source.point.good current.good
  have origins : WrapperOrigins state := by
    rcases outcomes with refused | failed | success
    · rw [refused.2.2]
      exact before.wrapperOrigins
    · rw [failed.2]
      refine ⟨before.wrapperOrigins.wrapped, ?_, ?_⟩
      · intro mode
        rcases mode with mode | mode <;> change MEM = _ at mode <;> contradiction
      · intro mode
        rcases mode with mode | mode | mode <;> change MEM = _ at mode <;> contradiction
    · obtain ⟨_ok, _nonnull, allowedMode, frame, _checksum⟩ := success
      have dict : before.core.source.point.state.mode = DICT :=
        allowedMode.resolve_left (by rw [before.wrapperOrigins.wrapped]; decide)
      rw [frame]
      refine ⟨before.wrapperOrigins.wrapped, ?_, ?_⟩
      · intro mode
        change before.core.source.point.state.mode = HEAD ∨ before.core.source.point.state.mode = DICTID at mode
        rw [dict] at mode
        rcases mode with mode | mode <;> contradiction
      · intro _mode
        exact before.wrapperOrigins.last (Or.inr (Or.inr dict))
  exact ⟨core, same ▸ origins⟩

theorem ScopedInvariant.refused_step
    {h after : Heap} {r : ZStreamRef} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (before : ScopedInvariant h r log)
    (observed : DataStep .inflate h after r flush rc input output used)
    (refused : (before.core.source.point.z.next_out == .null ||
      (before.core.source.point.z.next_in == .null && before.core.source.point.z.avail_in != 0)) = true) :
    rc = Z_STREAM_ERROR ∧ used = 0 ∧ output = [] ∧
      Nonempty (ScopedInvariant after r
        { log with
          input := log.input ++ input.take used
          output := log.output ++ output
          result := rc
          finished := log.finished || rc == Z_STREAM_END }) := by
  obtain ⟨code, zero, empty, ⟨core⟩⟩ := before.core.refused_step observed refused
  obtain ⟨expected, kept⟩ := entry_refused_origin before.core.origin flush refused
  obtain ⟨_beforeZ, _afterZ, _get0, _get1, _buffers, _header, _input, _count, _output, run⟩ := observed
  have pair := Except.ok.inj (run.symm.trans expected)
  cases pair
  have same := observed_state_unique core.source.point.good kept.good
  exact ⟨code, zero, empty, core, same ▸ before.wrapperOrigins⟩

#print axioms ScopedInvariant.init
#print axioms ScopedInvariant.rebuffer
#print axioms ScopedInvariant.dictionary
#print axioms ScopedInvariant.refused_step
end Zlib.Inflate.Proofs.WholeEpoch
