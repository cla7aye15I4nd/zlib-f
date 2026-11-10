import ZlibF.Proof.«inflate.c.fast-causal-committed-body»
import ZlibF.Proof.«inflate.c.fast-loop-source-origin-v1»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open ZlibF.Math.LZ77Copy ZlibF.Math.InflateCommittedTokens ZlibF.Math.InflateFastSource
set_option autoImplicit false

/-- Immutable source/table/history provenance for one actual fast loop.
No complete parser continuation or expected output is among these fields. -/
structure Parameters (ctx : FastLoopContext) where
  L : List Nat
  D : List Nat
  dict : List UInt8
  past : List UInt8
  start : List UInt8
  initialWords : List Bool
  entry : Zlib.Inffast.L
  input : List UInt8
  startOff : Nat
  saved : Array UInt8
  woff : Nat
  lmeaning : ∃ used, Inv LENS ctx.codes ctx.baseOff ctx.rootWidth used L
  lstable : StableQuery LENS ctx.codes ctx.baseOff ctx.rootWidth
  lflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS ctx.codes ctx.baseOff ctx.rootWidth
  dmeaning : ∃ used, Inv DISTS ctx.distCodes ctx.distOff ctx.distWidth used D
  dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS ctx.distCodes ctx.distOff ctx.distWidth
  dictionary : MatchHistory.saved saved ctx.c.wsize.toNat ctx.c.wnext.toNat ctx.c.whave.toNat woff =
    (dict ++ past).drop ((dict ++ past).length - 32768)
  dictCount : ((dict ++ past).drop ((dict ++ past).length - 32768)).length = ctx.c.whave.toNat
  rawMargin : 6 ≤ input.length
  initialLast : ctx.c.last = .ref ctx.inputRef (startOff + input.length - 5)

/-- Actual raw origin and the causal grammar are retained together.
Only accepted words enter the grammar; an actual BAD exit is separate. -/
structure Observation {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) where
  pulled : Nat
  word : List Bool
  history : List UInt8
  slow : IL
  packet : FastInputPacket h slow (p.input.drop pulled) q
  origin : Origin p.entry.hold.toNat p.entry.bits.toNat p.input q.hold.toNat q.bits.toNat pulled word.length
  physical : q.in_ = inputAdvance (.ref ctx.inputRef p.startOff) pulled
  historyView : ∀ j output, q.out = .ref ctx.dest j → Space.get h ctx.dest = some output →
    writtenBytes output j (j - ctx.bg) = history
  windowData : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
    Space.get h window = some p.saved ∧ p.woff + ctx.c.wsize.toNat ≤ p.saved.size

structure Tracked {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L)
    extends Observation p h q where
  committed : Committed p.L p.D p.dict p.start (p.initialWords ++ word) (p.past ++ history)

structure Ended {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L)
    extends Observation p h q where
  broke : q.broke = true
  state : DefaultStateJ h ctx.r ctx.zs ctx.z {ctx.s with mode := TYPE}
  symbols : Symbols p.L p.D p.dict p.start (p.initialWords ++ word) [] (p.past ++ history)

def Outcome {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  Nonempty (Tracked p h q) ∨ Nonempty (Ended p h q) ∨
    (q.broke = true ∧ ∃ i, DefaultStateJ h ctx.r ctx.zs
      {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD})

def Exit {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  FastLoopExit ctx h q ∧ Outcome p h q

structure Ready {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) where
  safety : FastLoopReady ctx h q
  tracked : Tracked p h q

/-- The initial tracked state is populated from the actual entry packet,
physical source pointer and pre-existing committed grammar projection. -/
theorem Ready.initial {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap}
    (safety : FastLoopReady ctx h p.entry) {slow : IL}
    (packet : FastInputPacket h slow p.input p.entry)
    (physical : p.entry.in_ = .ref ctx.inputRef p.startOff)
    (history : List UInt8)
    (observed : ∀ j output, p.entry.out = .ref ctx.dest j → Space.get h ctx.dest = some output →
      writtenBytes output j (j - ctx.bg) = history)
    (committed : Committed p.L p.D p.dict p.start p.initialWords (p.past ++ history))
    (windowData : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
      Space.get h window = some p.saved ∧ p.woff + ctx.c.wsize.toNat ≤ p.saved.size) :
    Nonempty (Ready p h p.entry) := by
  refine ⟨{
    safety := safety
    tracked := {
      pulled := 0
      word := []
      history := history
      slow := slow
      packet := ?_
      origin := Origin.initial _ _ _
      physical := ?_
      historyView := observed
      windowData := windowData
      committed := ?_ }}⟩
  · simpa only [List.drop_zero] using packet
  · simpa only [inputAdvance, Nat.add_zero] using physical
  · simpa only [List.append_nil] using committed

end Zlib.Inflate.Proofs.FastCommittedLoop
