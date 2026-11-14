import ZlibF.Proof.«deflate.c.engine.encoding-data-history»
import ZlibF.Proof.«deflate.c.engine.encoding-ordinary-history»
import ZlibF.Spec.Functional.Sequences
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual default data trace admits every signed flush and every caller output
reference allowed by DataStep. Its constructors record initialization, caller edits,
actual execution and byte observations, with no invariant or callee-contract field.
Existing raw/default trace declarations are preserved. -/
inductive GenericDefaultDataTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after) →
      GenericDefaultDataTrace r after {}
  | caller {h after log} : GenericDefaultDataTrace r h log → Rebuffer h after r →
      GenericDefaultDataTrace r after log
  | step {h after log z flush rc input output used} : GenericDefaultDataTrace r h log →
      r.get h = some z →
      DataStep .deflate h after r flush rc input output used →
      GenericDefaultDataTrace r after
        { log with
          input := log.input ++ input.take used, output := log.output ++ output
          result := rc, finished := log.finished || rc == Z_STREAM_END
          boundEligible := log.boundEligible && flush == Z_FINISH }

/-- The scoped history is an actual public data trace, with identical
accepted bytes, emitted bytes, return codes and completion/bound flags.
The default wrapper unfolds to fixed Init2 arguments; no universal Init2
correctness theorem is used. -/
theorem GenericDefaultDataTrace.public_trace {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) :
    DeflateDataTrace Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ _ actual ih => exact .step ih actual

/-- This default data epoch never records a dictionary. This is derived
from its actual constructors rather than supplied as an invariant. -/
theorem GenericDefaultDataTrace.dictionary_empty {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) : log.dictionary = [] ∧ log.singleDictionary = true := by
  induction history with
  | init => exact ⟨rfl, rfl⟩
  | caller _ _ ih => exact ih
  | step _ _ _ ih => exact ih

/-- Every old raw-output trace embeds with its exact unchanged observed log. -/
theorem GenericDefaultDataTrace.of_raw {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) : GenericDefaultDataTrace r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ getZ _raw observed ih => exact .step ih getZ observed

inductive GenericDefaultDataTrace.UsesFlush {r : ZStreamRef} (allowed : Int32 → Prop) :
    {h : Heap} → {log : DataLog} → GenericDefaultDataTrace r h log → Prop
  | init {h after version} {domain : InitDomain h r version}
      {actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after)} :
      UsesFlush allowed (.init domain actual)
  | caller {h after log} {history : GenericDefaultDataTrace r h log} {edit : Rebuffer h after r} :
      UsesFlush allowed history → UsesFlush allowed (.caller history edit)
  | step {h after log z flush rc input output used} {history : GenericDefaultDataTrace r h log}
      {getZ : r.get h = some z}
      {observed : DataStep .deflate h after r flush rc input output used} :
      UsesFlush allowed history → allowed flush → UsesFlush allowed (.step history getZ observed)


end Zlib.Deflate.Engine.Proofs
