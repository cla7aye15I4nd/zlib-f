import ZlibF.Math.InflateHuffmanBodyContext

namespace ZlibF.Math.InflateHuffmanBodyContext
open ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-- An accepted literal/match may finish reading its bits before writing
all bytes. The causal token context remains at the pre-token boundary;
actual output is only a prefix of the independently determined full effect. -/
structure PendingOutput (dict original : List UInt8) (originalInput : List Bool)
    (actualOutput : List UInt8) (unread : List Bool) (L D : List Nat) where
  before : List UInt8
  tokenInput : List Bool
  fullOutput : List UInt8
  block : ActiveBlock dict original originalInput before tokenInput L D
  accepted : Token.Step L D dict before tokenInput unread fullOutput false
  beforePrefix : before <+: actualOutput
  effectPrefix : actualOutput <+: fullOutput

/-- Output waits do not require a complete valid future. Extending input
preserves the accepted token and the not-yet-completed output effect. -/
def PendingOutput.extend {dict original actual : List UInt8}
    {originalInput unread : List Bool} {L D : List Nat}
    (pending : PendingOutput dict original originalInput actual unread L D) (bytes : List UInt8) :
    PendingOutput dict original (originalInput ++ bytesToBits bytes)
      actual (unread ++ bytesToBits bytes) L D :=
  ⟨pending.before, pending.tokenInput ++ bytesToBits bytes, pending.fullOutput,
    pending.block.extend bytes,
    InflateTokenContext.step_append pending.block.header.ext.1 pending.block.header.ext.2
      pending.accepted _, pending.beforePrefix, pending.effectPrefix⟩

/-- Only completion of the whole actual output effect advances the causal
token context. This prevents crediting a partially emitted MATCH as done. -/
def PendingOutput.complete {dict original actual : List UInt8}
    {originalInput unread : List Bool} {L D : List Nat}
    (pending : PendingOutput dict original originalInput actual unread L D)
    (complete : actual = pending.fullOutput) :
    ActiveBlock dict original originalInput actual unread L D := by
  rw [complete]
  exact pending.block.advance pending.accepted

/-- The valid-source output-prefix property holds during output waits too.
It follows from deterministic accepted reads and the actual emission prefix,
not from assuming a valid future as part of the pending-state invariant. -/
theorem PendingOutput.valid_source {dict original actual output : List UInt8}
    {originalInput unread rest : List Bool} {L D : List Nat} {future : List UInt8}
    (pending : PendingOutput dict original originalInput actual unread L D)
    (parsed : Blocks dict original (originalInput ++ bytesToBits future) rest output) :
    actual <+: output := by
  obtain ⟨bodyRest, bodyOutput, symbols, _beforePrefix, bodyPrefix⟩ :=
    pending.block.valid_source parsed
  have step := InflateTokenContext.step_append pending.block.header.ext.1
    pending.block.header.ext.2 pending.accepted (bytesToBits future)
  have tail := (InflateTokenContext.nonfinal_step_iff step).mp symbols
  exact pending.effectPrefix.trans ((InflateBlockContext.symbols_history_prefix tail).trans bodyPrefix)

end ZlibF.Math.InflateHuffmanBodyContext
