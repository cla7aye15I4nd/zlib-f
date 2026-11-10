import ZlibF.Proof.«inflate.c.whole-epoch-entry-refusal-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Replace exactly the six fields written by public window/checksum bookkeeping. -/
def publicRefresh (s target : InflateState) : InflateState :=
  {s with window := target.window, wsize := target.wsize, whave := target.whave, wnext := target.wnext, total := target.total, check := target.check}

/-- An exact record frame, not a function-call contract. -/
def PublicRecordFrame (before after : InflateState) : Prop := after = publicRefresh before after

namespace PublicRecordTransport
variable {s target : InflateState} {log : DataLog} {wire : List Bool}

theorem readPrefix {L D : List Nat} {input rest : List Bool}
    (p : SlowReverseToken.ReadPrefix L D input s rest) :
    SlowReverseToken.ReadPrefix L D input (publicRefresh s target) rest := by
  cases p with
  | code a => exact .code a
  | literal a b c d e => exact .literal a b c d e
  | lenext a b c d e f g => exact .lenext a b c d e f g
  | dist a b c d e f g h => exact .dist a b c d e f g h
  | distext a b c d e f g h i j k l => exact .distext a b c d e f g h i j k l
  | matching p a b c d e => exact .matching p a b c d e

def reading (data : Reading log s wire) : Reading log (publicRefresh s target) wire :=
  {data with parsed := readPrefix data.parsed}

def matching (data : Matching log s wire) : Matching log (publicRefresh s target) wire :=
  {data with registers := data.registers}

def counts {received : List Bool} (data : ActualHeader.CountReadSource s received []) :
    ActualHeader.CountReadSource (publicRefresh s target) received [] :=
  {data with literalCount := data.literalCount}

def headerPrefix {alphabet : List Nat} (data : ActualHeader.HeaderSourcePrefix s (heldRegs s) [] alphabet) :
    ActualHeader.HeaderSourcePrefix (publicRefresh s target) (heldRegs (publicRefresh s target)) [] alphabet :=
  {data with literalCount := data.literalCount}

def alphabet (data : AlphabetHeader log s wire) : AlphabetHeader log (publicRefresh s target) wire :=
  {data with counts := counts data.counts}

def codes (data : CodeHeader log s wire) : CodeHeader log (publicRefresh s target) wire :=
  {data with headerPrefix := headerPrefix data.headerPrefix}

def emptyCodes (data : EmptyCodeHeader log s wire) : EmptyCodeHeader log (publicRefresh s target) wire :=
  {data with counts := counts data.counts}

def copying (data : StoredCopy log s wire) : StoredCopy log (publicRefresh s target) wire :=
  {data with debt := data.debt}

def unchecked (data : UncheckedMatching log s wire) : UncheckedMatching log (publicRefresh s target) wire :=
  {data with reading := reading data.reading}


noncomputable def legacy (phase : SourcePhase log s wire)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → target.check = s.check) :
    SourcePhase log (publicRefresh s target) wire := by
  induction phase with
  | head a b c d e => exact .head a b c d e
  | dictid cmf flg a b c d e f g => exact .dictid cmf flg a b c d e f g
  | dictionary w identifier mode flag anchor output bits check installed =>
    exact .dictionary w identifier mode flag anchor output bits
      ((keep (Or.inl mode)).trans check) installed
  | tag w word a b c d => exact .tag w word a b c d
  | table b a c d e f => exact .table b a c d e f
  | alphabet a data => exact .alphabet a (alphabet data)
  | codes a data => exact .codes a (codes data)
  | emptyCodes a data => exact .emptyCodes a (emptyCodes data)
  | stored b padding a c d e f g h => exact .stored b padding a c d e f g h
  | copying a data => exact .copying a (copying data)
  | ready boundary a b => exact .ready boundary a b
  | reading a data => exact .reading a (reading data)
  | matching a data => exact .matching a (matching data)
  | afterBlocks a b data => exact .afterBlocks a b data
  | trailer a b c data d e => exact .trailer a b c data d e
  | done a b data => exact .done a b data
  | rejected a data => exact .rejected a data
  | memory prior previous nonmem frame ih =>
    rw [frame] at keep ⊢
    have kept : target.check = prior.check := keep (Or.inr rfl)
    exact .memory (publicRefresh prior target) (ih (fun _ => kept)) nonmem rfl

theorem tableBinding {h after : Heap} {L D : List Nat}
    (tables : TableBinding h s L D)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) :
    TableBinding after (publicRefresh s target) L D := by
  exact TableBinding.of_views tables views

theorem legacy_materialized (phase : SourcePhase log s wire)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → target.check = s.check)
    {h after : Heap} (tables : phase.Materialized h) (inverse : phase.Reversible)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) :
    (legacy phase keep).Materialized after ∧ (legacy phase keep).Reversible := by
  cases phase
  case memory prior nonmem frame previous =>
    cases frame
    exact ⟨trivial, trivial⟩
  all_goals simp only [legacy, SourcePhase.Materialized, SourcePhase.Reversible] at tables inverse ⊢
  all_goals first | exact ⟨tableBinding tables views, trivial⟩ | exact ⟨tables, inverse⟩ | exact ⟨trivial, trivial⟩

noncomputable def revised (phase : SourcePhase4 log s wire)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → target.check = s.check) :
    SourcePhase4 log (publicRefresh s target) wire := by
  induction phase with
  | legacy previous => exact .legacy (legacy previous keep)
  | rawStored block a b c d e => exact .rawStored block a b c d e
  | uncheckedMatch mode data => exact .uncheckedMatch mode (unchecked data)
  | memory prior previous nonmem frame ih =>
    rw [frame] at keep ⊢
    have kept : target.check = prior.check := keep (Or.inr rfl)
    exact .memory (publicRefresh prior target) (ih (fun _ => kept)) nonmem rfl

theorem revised_materialized (phase : SourcePhase4 log s wire)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → target.check = s.check)
    {h after : Heap} (tables : phase.Materialized h)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) :
    (revised phase keep).Materialized after := by
  cases phase
  case memory prior nonmem frame previous =>
    cases frame
    exact trivial
  case legacy previous => exact legacy_materialized previous keep tables.1 tables.2 views
  case rawStored => exact trivial
  case uncheckedMatch mode data => exact tableBinding tables views

theorem revised_saved (phase : SourcePhase4 log s wire)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → target.check = s.check) :
    (revised phase keep).Saved ↔ phase.Saved := by
  cases phase
  case memory prior nonmem frame previous => cases frame; exact Iff.rfl
  all_goals exact Iff.rfl

end PublicRecordTransport

/-- Pure source and table transport across public bookkeeping. Code-view
preservation is an explicit heap frame. No public call, Adler credit,
window contents or successful callee execution is assumed or concluded. -/
theorem SourcePhase4.public_record_frame
    {s after : InflateState} {log : DataLog} {wire : List Bool} {h heap : Heap}
    (phase : SourcePhase4 log s wire) (tables : phase.Materialized h)
    (frame : PublicRecordFrame s after)
    (keep : (s.mode = DICT ∨ s.mode = MEM) → after.check = s.check)
    (views : ∀ ref : CodeRef, (Space.get heap ref : Option (Array Code)) = Space.get h ref) :
    ∃ next : SourcePhase4 log after wire, next.Materialized heap ∧ (next.Saved ↔ phase.Saved) := by
  have result : ∃ next : SourcePhase4 log (publicRefresh s after) wire,
      next.Materialized heap ∧ (next.Saved ↔ phase.Saved) :=
    ⟨PublicRecordTransport.revised phase keep,
      PublicRecordTransport.revised_materialized phase keep tables views,
      PublicRecordTransport.revised_saved phase keep⟩
  exact frame.symm ▸ result

#print axioms SourcePhase4.public_record_frame
#print axioms PublicRecordTransport.legacy_materialized
#print axioms PublicRecordTransport.revised_saved

end Zlib.Inflate.Proofs.WholeEpoch
