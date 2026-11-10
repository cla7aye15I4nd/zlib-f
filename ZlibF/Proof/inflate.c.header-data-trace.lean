import ZlibF.Proof.«inflate.c.origin-history-calls»
import ZlibF.Proof.«inflate.c.head-wait-history»
import ZlibF.Proof.«inflate.c.cumulative-table-boundary»
import ZlibF.Proof.«inflate.c.parser-refusal-stutter»
namespace Zlib.Inflate.Proofs.HeaderDataTrace
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Scope mentions only the real initial allocation and caller byte sizes.
It supplies no invariant or postcondition of an earlier library call. -/
inductive PlatformScope {r : ZStreamRef} : {h : Heap} → {log : DataLog} → InflateDataTrace 15 r h log → Prop where
  | init {before after : Heap} {version : BPtr} {domain : InitDomain before r version}
      {actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)} :
      ZlibF.PlatformMemory.ByteObjectsFit before → before.allocOk before.nalloc = true → PlatformScope (.init domain actual)
  | caller {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log} {edit : Rebuffer before after r} :
      PlatformScope prior → ZlibF.PlatformMemory.ByteObjectsFit after → PlatformScope (.caller prior edit)
  | step {before after : Heap} {log : DataLog} {flush rc : Int32} {input output : List UInt8} {used : Nat}
      {prior : InflateDataTrace 15 r before log} {actual : DataStep .inflate before after r flush rc input output used} :
      PlatformScope prior → PlatformScope (.step prior actual)
  | dictionary {before after : Heap} {log : DataLog} {source : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
      {prior : InflateDataTrace 15 r before log} {arguments : StreamArguments before r (.inflateSetDictionary (some r) source n)}
      {input : Bytes before source n.toNat bytes} {actual : C.run (inflateSetDictionary (some r) source n) before = .ok (rc, after)} :
      PlatformScope prior → PlatformScope (.dictionary prior arguments input actual)

/-- Actual wb15 initialization establishes Origin/J for the unchanged
original DataTrace, including every real data or dictionary call. -/
theorem origin_from_init {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : InflateDataTrace 15 r h log) (scope : PlatformScope history) :
    ∃ zs z s, DefaultOriginState h r zs z s ∧ DefAlloc z := by
  induction scope with
  | @init before after version domain actual platform allocation =>
    obtain ⟨computed, z, s, run, current, allocator, _reachable⟩ := inflate_default_origin_initial before r version domain platform allocation
    change C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, computed) at run
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨before.nextBlk, z, s, current, allocator⟩
  | @caller before after log prior edit earlier platform ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨stream0, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨other, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : other = stream0 := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst other
    refine ⟨zs, stream0, s, next, ?_⟩
    rw [fields]
    exact allocator
  | @step before after log flush rc input output used prior observed earlier ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨_z0, _z1, _get0, _get1, buffers, _header, _input, _used, _output, actual⟩ := observed
    obtain ⟨code, computed, stream0, state, _used0, _output0, run, next, nextAllocator, _rest⟩ :=
      inflate_default_origin_public_memory_contract current allocator buffers flush
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, stream0, state, next, nextAllocator⟩
  | @dictionary before after log source n bytes rc prior arguments _bytes actual earlier ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨code, computed, state, run, next, _codes⟩ := inflateSetDictionary_default_origin current allocator source n arguments
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, z, state, next, allocator⟩

#print axioms origin_from_init

/-- Source-only selection of the original DataTrace before HEAD completes.
All calls and caller edits are original constructors; no phase invariant
or target parser fact is recorded as an input. -/
inductive HeadEpoch (r : ZStreamRef) : (zs : Nat) → {h : Heap} → {log : DataLog} → InflateDataTrace 15 r h log → Prop where
  | init {before after : Heap} {version : BPtr} {domain : InitDomain before r version}
      {actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)} :
      ZlibF.PlatformMemory.ByteObjectsFit before → before.allocOk before.nalloc = true →
      HeadEpoch r before.nextBlk (.init domain actual)
  | caller {zs : Nat} {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {edit : Rebuffer before after r} : HeadEpoch r zs prior → ZlibF.PlatformMemory.ByteObjectsFit after → HeadEpoch r zs (.caller prior edit)
  | wait {zs : Nat} {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat}
      {actual : DataStep .inflate before after r flush rc input output used} {z : ZStream} {s : InflateState} :
      HeadEpoch r zs prior → r.get before = some z → before.istates zs = some s → s.mode = HEAD →
      s.bits.toNat + 8 * z.avail_in.toNat < 16 → HeadEpoch r zs (.step prior actual)
  | refused {zs : Nat} {before after : Heap} {log : DataLog} {prior : InflateDataTrace 15 r before log}
      {flush rc : Int32} {input output : List UInt8} {used : Nat} {z : ZStream}
      {actual : DataStep .inflate before after r flush rc input output used} :
      HeadEpoch r zs prior → r.get before = some z →
      (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true → HeadEpoch r zs (.step prior actual)

/-- The selected original trace starts with actual init, and its complete
HEAD phase retains the exact DataLog consumed bytes in the stored word.
The caller provides neither Origin/J nor an initialized parser invariant. -/
theorem HeadEpoch.sound {h : Heap} {r : ZStreamRef} {log : DataLog} {zs : Nat} {history : InflateDataTrace 15 r h log}
    (selected : HeadEpoch r zs history) :
    ∃ z s, DefaultOriginState h r zs z s ∧ DefAlloc z ∧ log.output = [] ∧
      s.mode = HEAD ∧ s.last = 0 ∧ s.wrap = 5 ∧ s.wsize = 0 ∧
      s.bits.toNat < 16 ∧ s.bits.toNat = 8 * log.input.length ∧
      natBits s.bits.toNat s.hold.toNat = bytesBits log.input ∧ log.input.length ≤ 1 := by
  induction selected with
  | @init before after version domain actual platform allocation =>
    obtain ⟨computed, z, s, run, current, allocator, _reachable⟩ := inflate_default_origin_initial before r version domain platform allocation
    have run0 := run
    change C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, computed) at run0
    have same := Except.ok.inj (run0.symm.trans actual)
    cases same
    obtain ⟨head, last, wrap, window, bits, held⟩ := EntryPath.HeadHistory.init_head_wait_fields domain allocation run current.good
    refine ⟨z, s, current, allocator, rfl, head, last, wrap, window, ?_, ?_, ?_, by simp⟩
    · rw [bits]; decide
    · rw [bits]; rfl
    · rw [bits, held]; rfl
  | @caller index before after log prior edit selected platform ih =>
    obtain ⟨z, s, current, allocator, empty, mode, last, wrap, window, below, count, word, bound⟩ := ih
    obtain ⟨stream0, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨other, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : other = stream0 := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst other
    refine ⟨stream0, s, next, ?_, empty, mode, last, wrap, window, below, count, word, bound⟩
    rw [fields]; exact allocator
  | @wait index before after log prior flush rc input output used actual observedZ observedS selected getZ getS head short ih =>
    obtain ⟨z, s, current, allocator, empty, mode, last, wrap, window, below, count, word, bound⟩ := ih
    have sameZ : observedZ = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
    have sameS : observedS = s := Option.some.inj (getS.symm.trans current.good.live.hs)
    subst observedZ observedS
    obtain ⟨nextZ, nextS, next, nextAllocator, usedBound, nextMode, nextLast, nextWrap, nextWindow, nextBelow, nextCount, nextWord, noOutput⟩ :=
      EntryPath.HeadHistory.head_wait_observed current allocator actual head (Or.inr wrap) window short
    have takeLength : (input.take used).length = used := by rw [List.length_take, Nat.min_eq_left usedBound]
    refine ⟨nextZ, nextS, next, nextAllocator, ?_, nextMode, nextLast.trans last, nextWrap.trans wrap, nextWindow, nextBelow, ?_, ?_, ?_⟩
    · change log.output ++ output = []; rw [empty, noOutput]; rfl
    · change nextS.bits.toNat = 8 * (log.input ++ input.take used).length
      rw [List.length_append, takeLength]; omega
    · change natBits nextS.bits.toNat nextS.hold.toNat = bytesBits (log.input ++ input.take used)
      rw [nextWord, word, bytesBits_append]
    · change (log.input ++ input.take used).length ≤ 1
      have total : nextS.bits.toNat = 8 * (log.input ++ input.take used).length := by rw [List.length_append, takeLength]; omega
      omega
  | @refused index before after log prior flush rc input output used observedZ actual selected getZ rejected ih =>
    obtain ⟨z, s, current, allocator, empty, mode, last, wrap, window, below, count, word, bound⟩ := ih
    have sameZ : observedZ = z := Option.some.inj (getZ.symm.trans current.good.live.hz)
    subst observedZ
    obtain ⟨_heap, _rc, next, zero, noOutput⟩ := ParserRefusal.dataStep_refused_stutter current actual rejected
    refine ⟨z, s, next, allocator, ?_, mode, last, wrap, window, below, ?_, ?_, ?_⟩
    · change log.output ++ output = []; rw [empty, noOutput]; rfl
    · simpa only [zero, List.take_zero, List.append_nil] using count
    · simpa only [zero, List.take_zero, List.append_nil] using word
    · simpa only [zero, List.take_zero, List.append_nil] using bound

#print axioms HeadEpoch.sound


/-- Observed records identify the relation established by actual init. -/
theorem origin_of_records {h : Heap} {r : ZStreamRef} {log : DataLog} {zs : Nat} {z : ZStream} {s : InflateState}
    (history : InflateDataTrace 15 r h log) (scope : PlatformScope history)
    (getZ : r.get h = some z) (pointer : z.state = some (.inflate zs)) (getS : h.istates zs = some s) :
    DefaultOriginState h r zs z s ∧ DefAlloc z := by
  obtain ⟨index, stream0, state, current, allocator⟩ := origin_from_init history scope
  have sameZ : stream0 = z := Option.some.inj (current.good.live.hz.symm.trans getZ)
  subst stream0
  have sameIndex : index = zs := by
    have statePointer := current.good.live.zst
    rw [pointer] at statePointer
    cases statePointer
    rfl
  subst index
  have sameState : state = s := Option.some.inj (current.good.live.hs.symm.trans getS)
  subst state
  exact ⟨current, allocator⟩

#print axioms origin_of_records


/-- The HEAD source selector supplies precisely the platform/init scope
needed by the generic original-DataTrace source observer. -/
theorem HeadEpoch.scope {h : Heap} {r : ZStreamRef} {log : DataLog} {zs : Nat} {history : InflateDataTrace 15 r h log}
    (selected : HeadEpoch r zs history) : PlatformScope history := by
  induction selected with
  | @init before after version domain actual platform allocation => exact .init (domain := domain) (actual := actual) platform allocation
  | @caller index before after log prior edit selected platform ih => exact .caller (edit := edit) ih platform
  | @wait index before after log prior flush rc input output used actual observedZ observedS selected getZ getS head short ih => exact .step (actual := actual) ih
  | @refused index before after log prior flush rc input output used observedZ actual selected getZ rejected ih => exact .step (actual := actual) ih

#print axioms HeadEpoch.scope

end Zlib.Inflate.Proofs.HeaderDataTrace
