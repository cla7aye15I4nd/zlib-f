import ZlibF.Proof.«inflate.c.call-safety»

/-!
# inflate.c: stream operations keep the object-size limit

The history relation assumes `ZlibF.PlatformMemory.ByteObjectsFit` on every
heap of a call history. These lemmas show the library itself never breaks
it, so a history that starts with it needs it again only where the caller
supplies new storage.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One stream operation keeps the object-size limit. -/
def PlatformPreserves (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h after : Heap) (i : Nat) (z : ZStream) (s : InflateState) (value : call.Result),
    InflateInv h r i z s → ZlibF.PlatformMemory.ByteObjectsFit h → StreamArguments h r call →
    call.execute default h = .ok ((value, default), after) →
    ZlibF.PlatformMemory.ByteObjectsFit after

theorem platform_resetHeap {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (s : InflateState) : ZlibF.PlatformMemory.ByteObjectsFit (resetHeap h s) := by
  unfold resetHeap
  split
  · exact platform_freeWin platform s.window
  · exact platform

/-- A record write: stream record and decoder state. -/
theorem platform_records {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (r : ZStreamRef) (stream : ZStream) (zs : Nat) (state : InflateState) :
    ZlibF.PlatformMemory.ByteObjectsFit (setI (r.put h stream) zs state) :=
  (platform.put_stream r stream).with_istates _

theorem inflateSyncPoint_platform (r : ZStreamRef) :
    PlatformPreserves r (.inflateSyncPoint (some r)) := by
  intro h after i z s value current platform _ actual
  have run := inflateSyncPoint_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact platform

theorem inflateMark_platform (r : ZStreamRef) : PlatformPreserves r (.inflateMark (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨mark, run, _⟩ := inflateMark_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact platform

theorem inflateCodesUsed_platform (r : ZStreamRef) :
    PlatformPreserves r (.inflateCodesUsed (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨offset, _, _, run⟩ := inflateCodesUsed_spec current.good
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact platform

theorem inflateUndermine_platform (r : ZStreamRef) (subvert : Int32) :
    PlatformPreserves r (.inflateUndermine (some r) subvert) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _⟩ := inflateUndermine_safe current.good subvert
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform.with_istates _

theorem inflateValidate_platform (r : ZStreamRef) (check : Int32) :
    PlatformPreserves r (.inflateValidate (some r) check) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _, _⟩ := inflateValidate_safe current.good check
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform.with_istates _

theorem inflatePrime_platform (r : ZStreamRef) (bits word : Int32) :
    PlatformPreserves r (.inflatePrime (some r) bits word) := by
  intro h after i z s value current platform _ actual
  change heapCall (inflatePrime (some r) bits word) default h = _ at actual
  have run := run_of_heapCall actual
  rcases inflatePrime_default_record_image current.good bits word run with same | ⟨state, heap, _⟩
  · rw [same]
    exact platform
  · rw [heap]
    exact platform.with_istates _

theorem inflateResetKeep_platform (r : ZStreamRef) :
    PlatformPreserves r (.inflateResetKeep (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _, _⟩ := inflateResetKeep_safe current.good
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform_records platform _ _ _ _

theorem inflateReset_platform (r : ZStreamRef) : PlatformPreserves r (.inflateReset (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _, _⟩ := inflateReset_safe current.good current.alloc.2
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform_records (platform_resetHeap platform s) _ _ _ _

theorem inflateReset2_platform (r : ZStreamRef) (wb : Int32) :
    PlatformPreserves r (.inflateReset2 (some r) wb) := by
  intro h after i z s value current platform _ actual
  obtain ⟨code, written, run, result⟩ := inflateReset2_safe current.good current.alloc.2 wb
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  cases params : reset2Params wb with
  | none =>
    rw [params] at result
    rw [result.2]
    exact platform
  | some selected =>
    obtain ⟨wrap, width⟩ := selected
    rw [params] at result
    rw [result.2.1]
    exact platform_records (platform_reset2Heap platform width s) _ _ _ _

theorem inflateGetHeader_platform (r : ZStreamRef) (head : GzHeaderPtr) :
    PlatformPreserves r (.inflateGetHeader (some r) head) := by
  intro h after i z s value current platform arguments actual
  change heapCall (inflateGetHeader (some r) head) default h = _ at actual
  have run := run_of_heapCall actual
  obtain ⟨memory, present⟩ := arguments
  by_cases nogzip : s.wrap &&& 2 = 0
  · have expected := inflateGetHeader_nogzip current.good.live head nogzip
    have same := Except.ok.inj (run.symm.trans expected)
    cases same
    exact platform
  rcases memory with none | ⟨b, gh, pointer, get, _⟩
  · exact absurd none present
  subst pointer
  obtain ⟨written, expected, heap, _, _, _⟩ :=
    inflateGetHeader_ok current.good (g := .tab b) get nogzip
  have same := Except.ok.inj (run.symm.trans expected)
  cases same
  rw [heap]
  apply platform.of_storage_eq
  all_goals simp only [GzHeaderRef.put, setI]
  all_goals split <;> rfl

#print axioms inflateReset2_platform
#print axioms inflateGetHeader_platform

end Zlib.Inflate.Proofs
