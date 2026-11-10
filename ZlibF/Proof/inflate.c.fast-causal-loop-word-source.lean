import ZlibF.Proof.«inflate.c.fast-causal-loop-run»
namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- Exact content of the committed word, beyond Origin's length/drop
accounting. This is needed to identify the grammar with physical input. -/
def WordSource {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    (observation : Observation p h q) : Prop :=
  natBits p.entry.bits.toNat p.entry.hold.toNat ++ bytesBits p.input =
    observation.word ++ (natBits q.bits.toNat q.hold.toNat ++ bytesBits (p.input.drop observation.pulled))

structure WordReady {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) where
  state : Ready p h q
  source : WordSource state.tracked.toObservation

def WordOutcome {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  (∃ tracked : Tracked p h q, WordSource tracked.toObservation) ∨
  (∃ ended : Ended p h q, WordSource ended.toObservation) ∨
  (q.broke = true ∧ ∃ i, DefaultStateJ h ctx.r ctx.zs
    {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD})

def WordExit {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  FastLoopExit ctx h q ∧ WordOutcome p h q

theorem WordSource.advance
    {ctx : FastLoopContext} {p : Parameters ctx} {h after : Heap} {q result : Zlib.Inffast.L}
    {before : Observation p h q} {next : Observation p after result} {bs : List UInt8}
    {used : Nat} {consumed : List Bool}
    (source : WordSource before)
    (word : next.word = before.word ++ consumed)
    (pulled : next.pulled = before.pulled + used)
    (rawEq : bs = p.input.drop before.pulled)
    (step : natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used) =
      consumed ++ natBits result.bits.toNat result.hold.toNat) : WordSource next := by
  unfold WordSource at source ⊢
  calc
    _ = before.word ++ (natBits q.bits.toNat q.hold.toNat ++ bytesBits bs) := by
      simpa only [rawEq] using source
    _ = before.word ++ ((natBits q.bits.toNat q.hold.toNat ++ bytesBits (bs.take used)) ++
        bytesBits (bs.drop used)) := by
      rw [List.append_assoc, ← bytesBits_append, List.take_append_drop]
    _ = (before.word ++ consumed) ++
        (natBits result.bits.toNat result.hold.toNat ++ bytesBits (bs.drop used)) := by
      rw [step]
      simp only [List.append_assoc]
    _ = _ := by rw [word, pulled, rawEq, List.drop_drop]

/-- Entry constructs the empty committed word and its exact wire source.
No content-equality assumption is required of the caller. -/
theorem WordReady.initial {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap}
    (safety : FastLoopReady ctx h p.entry) {slow : IL}
    (packet : FastInputPacket h slow p.input p.entry)
    (physical : p.entry.in_ = .ref ctx.inputRef p.startOff)
    (history : List UInt8)
    (observed : ∀ j output, p.entry.out = .ref ctx.dest j → Space.get h ctx.dest = some output →
      ZlibF.Math.LZ77Copy.writtenBytes output j (j - ctx.bg) = history)
    (committed : ZlibF.Math.InflateCommittedTokens.Committed p.L p.D p.dict p.start p.initialWords (p.past ++ history))
    (windowData : ctx.c.whave ≠ 0 → ∃ window, window ≠ ctx.dest ∧ ctx.c.window = .ref window p.woff ∧
      Space.get h window = some p.saved ∧ p.woff + ctx.c.wsize.toNat ≤ p.saved.size) :
    Nonempty (WordReady p h p.entry) := by
  refine ⟨{
    state := {
      safety := safety
      tracked := {
        pulled := 0
        word := []
        history := history
        slow := slow
        packet := ?_
        origin := ZlibF.Math.InflateFastSource.Origin.initial _ _ _
        physical := ?_
        historyView := observed
        windowData := windowData
        committed := ?_ }}
    source := ?_ }⟩
  · simpa only [List.drop_zero] using packet
  · simpa only [inputAdvance, Nat.add_zero] using physical
  · simpa only [List.append_nil] using committed
  · simp only [WordSource, List.drop_zero, List.nil_append]

end Zlib.Inflate.Proofs.FastCommittedLoop
