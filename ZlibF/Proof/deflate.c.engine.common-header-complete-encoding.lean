import ZlibF.Proof.«deflate.c.engine.common-header-caller»
import ZlibF.Proof.«deflate.c.engine.common-header-encoding»
import ZlibF.Proof.«deflate.c.engine.header-encoding»
import ZlibF.Proof.«deflate.c.engine.header-full-storage»
import ZlibF.Proof.«deflate.c.engine.public-output-interval-prefix»

/-! # Exact common-level completed header bytes, raw meaning and storage -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual completed-header heap contains both generated wrapper
bytes in the caller's output slice. Array suffix bytes are unconstrained. -/
theorem common_header_complete_prefix (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8)
    (pendingRoom : 2 ≤ buf.size) (outputRoom : oo + 2 ≤ output.size) :
    ∃ written, (levelHeaderCompleteHeap h r ds pb ob oo z d buf output).bytes ob = some written ∧
      written[oo]? = some ((levelHeaderWord d.level >>> 8).toUInt8) ∧
      written[oo + 1]? = some ((levelHeaderWord d.level &&& 0xff).toUInt8) := by
  let written := copyRange output (levelHeaderBytes d.level buf) oo 0 2
  have first : (levelHeaderBytes d.level buf)[0]! = (levelHeaderWord d.level >>> 8).toUInt8 := by
    simp [levelHeaderBytes, getElem!_def, Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds,
      show 0 < buf.size by omega]
  have second : (levelHeaderBytes d.level buf)[1]! = (levelHeaderWord d.level &&& 0xff).toUInt8 := by
    simp [levelHeaderBytes, getElem!_def, Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds,
      show 1 < buf.size by omega]
  refine ⟨written, by simp [levelHeaderCompleteHeap, levelHeaderCompleteBytes, written], ?_, ?_⟩
  · rw [getElem?_copyRange output (levelHeaderBytes d.level buf) oo 0 2 oo outputRoom]
    simp [first]
  · rw [getElem?_copyRange output (levelHeaderBytes d.level buf) oo 0 2 (oo + 1) outputRoom]
    simp [second]


theorem common_header_complete_raw_prefix {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {input : Nat → UInt8} {published : List UInt8}
    (initial : EngineStart h r ds z d) (boundary : ContentBoundary h r ds z d input origin base [])
    (pointer : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (outGet : h.bytes ob = some output) (outside : ¬ DeflateOwned ds d ob)
    (encoding : RawPrefix h d input base published) :
    RawPrefix (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) (headerCompleteState d) input base published := by
  have stateA := common_header_complete_content (oo := oo) boundary pointer get outGet outside
  exact encoding.empty_transport stateA.good
    (by rw [initial.pending]; rfl) (by rw [initial.bits]; rfl)
    (by change d.pending.toNat = 0; rw [initial.pending]; rfl)
    (by change d.bi_valid.toInt.toNat = 0; rw [initial.bits]; rfl)

/-- The exact caller slice of the real completed-header heap is the
independently specified default zlib header, with arbitrary array suffix. -/
theorem common_header_complete_output_bytes (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8)
    (pendingRoom : 2 ≤ buf.size) (outputRoom : oo + 2 ≤ output.size) :
    Bytes (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) (.ref (.blk ob) oo) 2 (levelHeaderPrefix d.level) := by
  obtain ⟨written, get, first, second⟩ := common_header_complete_prefix h r ds pb ob oo z d buf output pendingRoom outputRoom
  have size : written.size = output.size := by
    have actual : (levelHeaderCompleteHeap h r ds pb ob oo z d buf output).bytes ob =
        some (copyRange output (levelHeaderBytes d.level buf) oo 0 2) := by simp [levelHeaderCompleteHeap, levelHeaderCompleteBytes]
    have array := Option.some.inj (get.symm.trans actual)
    rw [array, size_copyRange]
  have slice : (written.toList.drop oo).take 2 = (levelHeaderPrefix d.level : List UInt8) := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, Array.length_toList, levelHeaderPrefix, List.length_cons, List.length_nil, size]
      omega
    · intro i hi hj
      have bound : i < 2 := by simpa only [levelHeaderPrefix, List.length_cons, List.length_nil] using hj
      have inside : oo + i < written.size := by omega
      have value : written[oo + i]? = some ((levelHeaderPrefix d.level : List UInt8)[i]) := by
        have casesI : i = 0 ∨ i = 1 := by omega
        rcases casesI with rfl | rfl
        · simpa only [Nat.add_zero, levelHeaderPrefix, List.getElem_cons_zero] using first
        · simpa only [List.getElem_cons_succ, levelHeaderPrefix, List.getElem_cons_zero] using second
      have equal : written[oo + i] = (levelHeaderPrefix d.level : List UInt8)[i] := by
        exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans value)
      simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList, levelHeaderPrefix] using equal
  exact Or.inr ⟨.blk ob, oo, written, rfl, get, by omega, slice.symm⟩


/-- The exact header preserves the full private/caller object frame. -/
theorem common_header_complete_full_storage {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes pb = some buf) (outGet : h.bytes ob = some output)
    (separate : ob ≠ pb) :
    OutputStorage h (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) r ds pb ob :=
  header_write_storage good get outGet separate _ _ _ _

/-- The complete actual header heap changes only its two-byte caller interval. -/
theorem common_header_complete_output_effect {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (get : h.bytes ob = some output) (bound : oo + 2 ≤ output.size) :
    RawOutputInterval h (levelHeaderCompleteHeap h r ds pb ob oo z d buf output) ob oo 2 := by
  intro before getBefore
  have same : before = output := Option.some.inj (getBefore.symm.trans get)
  subst before
  refine ⟨copyRange output (levelHeaderBytes d.level buf) oo 0 2, ?_, size_copyRange _ _ _ _ _, ?_⟩
  · simp only [levelHeaderCompleteHeap, setD_bytes, ZStreamRef.put_bytes, levelHeaderCompleteBytes, upd_same]
  · intro j _range outside
    rw [getElem?_copyRange output (levelHeaderBytes d.level buf) oo 0 2 j bound, ite_eq_right outside]


end Zlib.Deflate.Engine.Proofs
