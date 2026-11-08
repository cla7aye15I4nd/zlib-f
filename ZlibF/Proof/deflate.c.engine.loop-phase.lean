import ZlibF.Proof.«deflate.c.engine.flush-frame»

/-! # Configuration and publication facts needed at each strategy iteration -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The fixed strategy configuration and private allocation keys. Variable
positions, matching work, trees and output counters are tracked separately. -/
structure EngineConfig where
  level : Int32
  strategy : Int32
  wrap : Int32
  windowBits : UInt32
  hashBits : UInt32
  memory : UInt32
  header : GzHeaderPtr
  window : BPtr
  prev : WPtr
  head : WPtr
  pending : BPtr
  stream : ZStreamPtr

def engineConfig (d : DeflateState) : EngineConfig :=
  ⟨d.level, d.strategy, d.wrap, d.w_bits, d.hash_bits, d.lit_bufsize,
    d.gzhead, d.window, d.prev, d.head, d.pending_buf, d.strm⟩

def ConfigFrame (before after : DeflateState) : Prop := engineConfig after = engineConfig before

/-- A continuing strategy iteration has no unpublished complete bytes,
a base pending cursor and fewer than eight buffered bits. -/
def PublishReady (d : DeflateState) : Prop :=
  d.pending = 0 ∧ d.pending_out = d.pending_buf ∧ d.bi_valid.toInt < 8

theorem ConfigFrame.refl (d : DeflateState) : ConfigFrame d d := rfl

theorem ConfigFrame.trans {a b c : DeflateState} (first : ConfigFrame a b) (second : ConfigFrame b c) :
    ConfigFrame a c := Eq.trans second first

theorem ConfigFrame.slow {a b : DeflateState} (frame : SlowRecordFrame a b) : ConfigFrame a b := by
  rw [frame]
  rfl

theorem ConfigFrame.fill {a b : DeflateState} (frame : FillRecordFrame a b) : ConfigFrame a b := by
  rw [frame]
  rfl

theorem ConfigFrame.flush {a b : DeflateState} {position : Int64}
    (frame : FlushWorkFrame { a with block_start := position } b) : ConfigFrame a b := by
  rw [frame]
  rfl

theorem ConfigFrame.bits {a b : DeflateState} (frame : Zlib.Trees.Proofs.Out.BitsDiff a b) :
    ConfigFrame a b := by
  obtain ⟨_, _, _, _, fields⟩ := frame
  rw [fields]
  rfl

theorem ConfigFrame.level {a b : DeflateState} (frame : ConfigFrame a b) : b.level = a.level :=
  congrArg EngineConfig.level frame

theorem ConfigFrame.memory {a b : DeflateState} (frame : ConfigFrame a b) : b.lit_bufsize = a.lit_bufsize :=
  congrArg EngineConfig.memory frame

theorem ConfigFrame.wrap {a b : DeflateState} (frame : ConfigFrame a b) : b.wrap = a.wrap :=
  congrArg EngineConfig.wrap frame

theorem ConfigFrame.header {a b : DeflateState} (frame : ConfigFrame a b) : b.gzhead = a.gzhead :=
  congrArg EngineConfig.header frame

theorem PublishReady.slow {a b : DeflateState} (ready : PublishReady a) (frame : SlowRecordFrame a b) :
    PublishReady b := by rw [frame]; exact ready

theorem PublishReady.fill {a b : DeflateState} (ready : PublishReady a) (frame : FillRecordFrame a b) :
    PublishReady b := by rw [frame]; exact ready

end Zlib.Deflate.Engine.Proofs
