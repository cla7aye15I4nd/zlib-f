import ZlibF.Proof.«deflate.c.engine.public-no-flush-ready-encoding»
import ZlibF.Proof.«deflate.c.engine.header-buffered»

/-! # Completed real wrapper headers retain the initial raw encoding phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Empty pending and held bits transport raw prefix meaning across a
proved state update, independently of unused pending-buffer contents. -/
theorem RawPrefix.empty_transport {h after : Heap} {r : ZStreamRef} {ds base : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8} {published : List UInt8}
    (encoding : RawPrefix h d input base published) (goodA : DGood after r ds z result)
    (pending : d.pending.toNat = 0) (bits : d.bi_valid.toInt.toNat = 0)
    (pendingA : result.pending.toNat = 0) (bitsA : result.bi_valid.toInt.toNat = 0) :
    RawPrefix after result input base published := by
  obtain ⟨before, encoded, held, wire, meaning⟩ := encoding
  have beforeEmpty := pending_bits_empty held pending bits
  obtain ⟨remaining, heldA⟩ := good_pending_bits goodA
  have afterEmpty := pending_bits_empty heldA pendingA bitsA
  rw [beforeEmpty] at wire
  rw [afterEmpty] at heldA
  exact ⟨[], encoded, heldA, wire, meaning⟩

/-- The complete actual header has no residual header bits in its pending
sequence. Its private content boundary and old raw history coexist. -/
theorem header_complete_raw_prefix {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {input : Nat → UInt8} {published : List UInt8}
    (initial : EngineStart h r ds z d) (boundary : ContentBoundary h r ds z d input origin base [])
    (pointer : d.pending_buf = .ref (.blk pb) 0) (get : h.bytes pb = some buf)
    (outGet : h.bytes ob = some output) (outside : ¬ DeflateOwned ds d ob)
    (encoding : RawPrefix h d input base published) :
    RawPrefix (headerCompleteHeap h r ds pb ob oo z d buf output) (headerCompleteState d) input base published := by
  have stateA := header_complete_content (oo := oo) boundary pointer get outGet outside
  exact encoding.empty_transport stateA.good
    (by rw [initial.pending]; rfl) (by rw [initial.bits]; rfl)
    (by change d.pending.toNat = 0; rw [initial.pending]; rfl)
    (by change d.bi_valid.toInt.toNat = 0; rw [initial.bits]; rfl)

/-- The exact caller slice of the real completed-header heap is the
independently specified default zlib header, with arbitrary array suffix. -/
theorem header_complete_output_bytes (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8)
    (pendingRoom : 2 ≤ buf.size) (outputRoom : oo + 2 ≤ output.size) :
    Bytes (headerCompleteHeap h r ds pb ob oo z d buf output) (.ref (.blk ob) oo) 2 [120, 156] := by
  obtain ⟨written, get, first, second⟩ := header_complete_prefix h r ds pb ob oo z d buf output pendingRoom outputRoom
  have size : written.size = output.size := by
    have actual : (headerCompleteHeap h r ds pb ob oo z d buf output).bytes ob =
        some (copyRange output (zlibHeaderBytes buf) oo 0 2) := by simp [headerCompleteHeap, headerCompleteBytes]
    have array := Option.some.inj (get.symm.trans actual)
    rw [array, size_copyRange]
  have slice : (written.toList.drop oo).take 2 = ([120, 156] : List UInt8) := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, Array.length_toList, List.length_cons, List.length_nil, size]
      omega
    · intro i hi hj
      have bound : i < 2 := by simpa only [List.length_cons, List.length_nil] using hj
      have inside : oo + i < written.size := by omega
      have value : written[oo + i]? = some (([120, 156] : List UInt8)[i]) := by
        have casesI : i = 0 ∨ i = 1 := by omega
        rcases casesI with rfl | rfl
        · simpa only [Nat.add_zero, List.getElem_cons_zero] using first
        · simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using second
      have equal : written[oo + i] = ([120, 156] : List UInt8)[i] := by
        exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans value)
      simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList] using equal
  exact Or.inr ⟨.blk ob, oo, written, rfl, get, by omega, slice.symm⟩

end Zlib.Deflate.Engine.Proofs
