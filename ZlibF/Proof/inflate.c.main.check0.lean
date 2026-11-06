import ZlibF.Proof.«inflate.c.main.simple»

/-!
# inflate.c: helpers for the table, check and leave modes

`badMode` (`strm->msg = "..."; state->mode = BAD`) as a heap function, and the evaluation rules of the mode
monad for the accesses to the stream and the state record that the modes of the dynamic tables and of the trailer use.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The heap after `badMode` with the literal number `i`: the stream's `msg` points to it and the mode is `BAD`. -/
def tcBadHeap (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (i : Nat) : Heap :=
  setI (r.put h { z with msg := .ref (.str i) 0 }) zs { s with mode := BAD }

theorem tcStrLit_run (h : Heap) (msg : String) (hm : msg ∈ strTable) :
    ∃ i, Zlib.Zutil.strLit msg h = .ok (.ref (.str i) 0, h) ∧ strTable[i]? = some msg :=
  Zlib.Zutil.Proofs.strLit_run h msg hm

/-- `badMode` writes the message pointer into the stream record and `BAD` into the state record. -/
theorem tcBadMode_run {h : Heap} {c : Ctx} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} (msg : String)
    (hm : msg ∈ strTable) (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) :
    ∃ i, strTable[i]? = some msg ∧ badMode c msg h = .ok ((), tcBadHeap h r zs z s i) := by
  obtain ⟨i, hi, hti⟩ := tcStrLit_run h msg hm
  refine ⟨i, hti, ?_⟩
  unfold badMode setMsg
  rw [hr, hc]
  simp [bind_app, hi, ldZ_eq, hz, stZ_eq, setMode, wrI_eq, ZStreamRef.put_istates, tcBadHeap, hs]

/-! ### The error messages of these modes are string literals of the sources -/

set_option maxRecDepth 100000 in
theorem lit_length_check : "incorrect length check" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_data_check : "incorrect data check" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_many_symbols : "too many length or distance symbols" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_code_lengths : "invalid code lengths set" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_bit_length_repeat : "invalid bit length repeat" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_missing_eob : "invalid code -- missing end-of-block" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_literal_lengths : "invalid literal/lengths set" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

set_option maxRecDepth 100000 in
theorem lit_distances : "invalid distances set" ∈ strTable := by
  rw [Array.mem_def]
  decide +kernel

end Zlib.Inflate.Proofs
