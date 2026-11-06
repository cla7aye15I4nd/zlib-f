import ZlibF.Proof.«trees.c.build.support»
import ZlibF.Proof.«trees.c.emit»
import ZlibF.Spec.Format.Bits

/-! # trees.c: transmitting the canonical values established by tree building -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- Stored reversed canonical words are sent in the format's most-significant
bit order. This statement concerns exact bit order; prefix freedom requires
the separate length/count consistency bridge. -/
theorem canonical_code_wire (tk : TK) (d : DeflateState) (v : Nat)
    (hc : (tk.arr d)[v]!.fc.toNat = Math.storedCode
      (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v) :
    Out.natBits (tk.arr d)[v]!.fc.toNat (tk.arr d)[v]!.dl.toNat =
      ZlibF.Spec.natToBitsMSB (tk.arr d)[v]!.dl.toNat
        (Math.canonicalCode (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v) := by
  rw [hc]
  unfold Out.natBits ZlibF.Spec.natToBitsMSB Math.storedCode
  exact Math.reverseLowBits_wire _ _

/-- The actual send_code reads the represented dynamic-tree entry and
emits its exact canonical bits. Length and code-value facts are the data
results of build_tree; its two reads are proved here. Output capacity and
the current live output invariant remain explicit caller obligations. -/
theorem send_canonical_code_emit {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : Out.TreesInvAt h id d b buf) (tk : TK) (v : Nat) (hv : v < (tk.arr d).size)
    (hl : (tk.arr d)[v]!.dl.toNat ≤ 15)
    (hc : (tk.arr d)[v]!.fc.toNat = Math.storedCode
      (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v)
    (hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + (tk.arr d)[v]!.dl.toNat ≤ 8 * buf.size) :
    Out.Emit id b (send_code (Sp id) (v : Int) (.ref (tk.ref id) 0)) h d buf
      (ZlibF.Spec.natToBitsMSB (tk.arr d)[v]!.dl.toNat
        (Math.canonicalCode (fun b => d.bl_count[b]!.toNat) (fun n => (tk.arr d)[n]!.dl.toNat) v)) 2 := by
  have hg := tk_get (h0 := h) (id := id) (d := d) tk
  rw [setD_self hI.base.dstate] at hg
  have hdl : getDl (.ref (tk.ref id) 0) (v : Int) h = .ok ((tk.arr d)[v]!.dl, h) := by
    simpa only [getElem!_pos, hv] using Out.getDl_gen hg hv
  have hfc : getFc (.ref (tk.ref id) 0) (v : Int) h = .ok ((tk.arr d)[v]!.fc, h) := by
    simpa only [getElem!_pos, hv] using Out.getFc_gen hg hv
  have hfit : (tk.arr d)[v]!.fc.toNat < 2 ^ (tk.arr d)[v]!.dl.toNat := by
    rw [hc]
    exact Math.storedCode_lt _ _ _
  have hemit := Out.send_code_emit hI (v : Int) (.ref (tk.ref id) 0) _ _ hdl hfc hl hfit hroom
  rw [canonical_code_wire tk d v hc] at hemit
  exact hemit

end Zlib.Trees.Proofs
