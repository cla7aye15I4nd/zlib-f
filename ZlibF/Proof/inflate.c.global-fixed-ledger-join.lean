import ZlibF.Proof.«inflate.c.generic-fixed-source-v1»
import ZlibF.Proof.«inflate.c.global-output-credit-transport»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
open Zlib.Inflate.Proofs.FunctionalTrailer Zlib.Inflate.Proofs.FixedBlockProducer
set_option autoImplicit false

/-- Strip the untouched caller buffer from a real DROPBITS source frame.
The resulting causal source cut fixes held bits only. -/
theorem held_drop_cut {before after : IL} {bs : List UInt8} {n : Nat}
    (fit : n ≤ before.bits.toNat)
    (source : stream after bs = (stream before bs).drop n) :
    natBits after.bits.toNat after.hold.toNat =
      (natBits before.bits.toNat before.hold.toNat).drop n := by
  apply (List.append_left_inj (bytesBits bs)).mp
  have bitFit : n ≤ (natBits before.bits.toNat before.hold.toNat).length := by
    rw [natBits_length]; exact fit
  simp only [stream] at source
  rw [List.drop_append_of_le_length bitFit] at source
  exact source

/-- Actual input refill credits only bytes pulled into the held word.
Unconsumed caller bytes are cancelled from the source equation. -/
theorem held_pull_cut {before after : IL} {bs : List UInt8} {used : Nat}
    (source : stream after (bs.drop used) = stream before bs) :
    natBits after.bits.toNat after.hold.toNat =
      natBits before.bits.toNat before.hold.toNat ++ bytesBits (bs.take used) := by
  apply (List.append_left_inj (bytesBits (bs.drop used))).mp
  have split : bytesBits bs = bytesBits (bs.take used) ++ bytesBits (bs.drop used) := by
    rw [← bytesBits_append, List.take_append_drop]
  simpa only [stream, split, List.append_assoc] using source

/-- The actual fixed selector installs the full common functional ledger.
The source-produced BFINAL and incoming causal Blocks cut identify the
same original block; no valid future or target output is assumed. -/
theorem fixed_selector_payload_ledger
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs dict prior emitted : List UInt8} {credited : Nat}
    {originalBits blockInput : List Bool} {last : Nat}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs)
    (modes : s.mode = TYPE ∨ s.mode = TYPEDO)
    (full : 2 ≤ l.bits.toNat) (incoming : l.bits.toNat ≤ 39)
    (kind : l.hold.toNat % 4 = 1)
    (dictionary : InflateDictionary h s ((dict ++ prior).drop ((dict ++ prior).length - 2 ^ s.wbits.toNat)))
    (output : OutputCredit h z s l prior emitted credited)
    (context : ZlibF.Math.InflateBlockContext.Context dict [] originalBits (prior ++ emitted) blockInput)
    (finalRead : readBits 1 blockInput = some (last, natBits l.bits.toNat l.hold.toNat)) :
    let regs := {l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2}
    let state := {fixedState s with mode := LEN_}
    runX (typedoTail c) l h =
      .ok ((if c.flush = Z_TREES then .error Ex.leave else .ok (), regs), setI h zs state) ∧
    Nonempty (PayloadLedger (setI h zs state) r zs z state regs bs dict prior emitted originalBits
      fixedLitLens fixedDistLens credited) := by
  dsimp only
  let regs := {l with hold := l.hold >>> (2 : UInt32).toUInt64, bits := l.bits - 2}
  let state := {fixedState s with mode := LEN_}
  obtain ⟨actual, representation, credit, fastL, fastD, next, put, haveEq, left, inEq, outEq, source⟩ :=
    fixed_selector_complete E origin buffers modes full incoming kind output.checksum dictionary
  have held := held_drop_cut full source
  have read := readBits_held_stream l [] 2 full
  have typeRead : readBits 2 (natBits l.bits.toNat l.hold.toNat) =
      some (1, natBits regs.bits.toNat regs.hold.toNat) := by
    rw [show natBits regs.bits.toNat regs.hold.toNat =
      (natBits l.bits.toNat l.hold.toNat).drop 2 from held]
    simpa only [stream, bytesBits_nil, List.append_nil, kind] using read
  have grammar : ZlibF.Math.InflateHuffmanBodyContext.ActiveBlock dict [] originalBits
      (prior ++ emitted) (natBits regs.bits.toNat regs.hold.toNat) fixedLitLens fixedDistLens :=
    ⟨prior ++ emitted, blockInput, natBits l.bits.toNat l.hold.toNat,
      natBits regs.bits.toNat regs.hold.toNat, natBits regs.bits.toNat regs.hold.toNat,
      1, last, context, finalRead, typeRead, .fixed _, .initial _ _ _ _ _⟩
  have queryFlags : InstalledQueryFlags (setI h zs state) state := by
    constructor
    · exact ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, rfl,
        by change some h.static.lenfix = some Zlib.InffixedH.lenfix; rw [origin.toDefaultStateJ.globals]; rfl, fastL⟩
    · exact ⟨.st_distfix, 0, Zlib.InffixedH.distfix, rfl,
        by change some h.static.distfix = some Zlib.InffixedH.distfix; rw [origin.toDefaultStateJ.globals]; rfl, fastD⟩
  have creditLedger : OutputCredit (setI h zs state) z state regs prior emitted credited := by
    obtain ⟨ref, off, array, pointer, get, start, finish, values⟩ := output.physical
    refine ⟨output.count, credit, ?_, ref, off, array, ?_, ?_, start, finish, values⟩
    · change (l.out_ - l.left).toNat = emitted.length - credited
      exact output.pending
    · exact pointer
    · rw [byte_view_get_setI]
      exact get
  exact ⟨actual, ⟨representation, allocator, queryFlags, grammar, creditLedger⟩⟩

end Zlib.Inflate.Proofs.FunctionalEpoch
