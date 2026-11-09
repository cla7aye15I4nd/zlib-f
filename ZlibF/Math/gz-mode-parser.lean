import ZlibF.Spec.Api.Gz
import Init.Data.SInt.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Complete byte classification for the gzip mode parser

The source signed-char decision tree and the unchanged public parser agree on
all byte values. Extra source flags are retained as actions, then projected out
only from the parser's semantic accumulator.
-/

namespace ZlibF.Math.GzModeParser
open ZlibF.Spec.Api

inductive Action where
  | level (value : Int32)
  | mode (value : GzMode)
  | bad | binary | cloexec | exclusive
  | strategy (value : Nat)
  | gzipOnly | nonblock | transparent | ignore
  deriving DecidableEq

inductive SemanticAction where
  | level (value : Int)
  | mode (value : GzMode)
  | bad
  | strategy (value : Nat)
  | direct (value : Int)
  | ignore
  deriving DecidableEq

/-- The exact complete source classification, including signed-char conversion. -/
def sourceAction (b : UInt8) : Action :=
  let c : Int32 := b.toInt8.toInt32
  if c ≥ 48 && c ≤ 57 then .level (c - 48)
  else if c == 114 then .mode .read
  else if c == 119 then .mode .write
  else if c == 97 then .mode .append
  else if c == 43 then .bad
  else if c == 98 then .binary
  else if c == 101 then .cloexec
  else if c == 120 then .exclusive
  else if c == 102 then .strategy 1
  else if c == 104 then .strategy 2
  else if c == 82 then .strategy 3
  else if c == 70 then .strategy 4
  else if c == 71 then .gzipOnly
  else if c == 78 then .nonblock
  else if c == 84 then .transparent
  else .ignore

/-- Only the extra OS/binary flags disappear from the API's semantic view. -/
def semanticAction : Action → SemanticAction
  | .level v => .level v.toInt
  | .mode m => .mode m
  | .bad => .bad
  | .strategy s => .strategy s
  | .gzipOnly => .direct (-1)
  | .transparent => .direct 1
  | _ => .ignore

/-- The unchanged public parser's character classification. -/
def charAction (c : Char) : SemanticAction :=
  if '0' ≤ c ∧ c ≤ '9' then .level (c.toNat - '0'.toNat : Nat)
  else if c = 'r' then .mode .read
  else if c = 'w' then .mode .write
  else if c = 'a' then .mode .append
  else if c = '+' then .bad
  else if c = 'f' then .strategy 1
  else if c = 'h' then .strategy 2
  else if c = 'R' then .strategy 3
  else if c = 'F' then .strategy 4
  else if c = 'G' then .direct (-1)
  else if c = 'T' then .direct 1
  else .ignore

/-- Exhaustive kernel evaluation over the complete eight-bit domain. In
particular, high-bit signed characters never match an ASCII source handler. -/
theorem sourceAction_semantic (b : UInt8) :
    semanticAction (sourceAction b) = charAction (Char.ofNat b.toNat) := by
  have complete : ∀ j : Fin 256,
      semanticAction (sourceAction (UInt8.ofNat j.val)) =
        charAction (Char.ofNat (UInt8.ofNat j.val).toNat) := by decide +kernel
  simpa using complete ⟨b.toNat, b.toNat_lt⟩

abbrev Acc := Option GzMode × Int × Nat × Int × Bool

def initial : Acc := (none, -1, 0, 0, false)

/-- The exact five public accumulator fields, with last assignment winning. -/
def semanticStep (acc : Acc) (action : SemanticAction) : Acc :=
  let (mo, lv, st, di, bad) := acc
  match action with
  | .level v => (mo, v, st, di, bad)
  | .mode m => (some m, lv, st, di, bad)
  | .bad => (mo, lv, st, di, true)
  | .strategy s => (mo, lv, s, di, bad)
  | .direct d => (mo, lv, st, d, bad)
  | .ignore => acc

/-- Exact named source cut of the public character step. -/
def charStep (acc : Acc) (c : Char) : Acc :=
  let (mo, lv, st, di, bad) := acc
  if '0' ≤ c ∧ c ≤ '9' then (mo, (c.toNat - '0'.toNat : Nat), st, di, bad)
  else if c = 'r' then (some .read, lv, st, di, bad)
  else if c = 'w' then (some .write, lv, st, di, bad)
  else if c = 'a' then (some .append, lv, st, di, bad)
  else if c = '+' then (mo, lv, st, di, true)
  else if c = 'f' then (mo, lv, 1, di, bad)
  else if c = 'h' then (mo, lv, 2, di, bad)
  else if c = 'R' then (mo, lv, 3, di, bad)
  else if c = 'F' then (mo, lv, 4, di, bad)
  else if c = 'G' then (mo, lv, st, -1, bad)
  else if c = 'T' then (mo, lv, st, 1, bad)
  else acc

/-- Exact final checks of the existing public parser. -/
def finish (acc : Acc) : Option (GzMode × Int × Nat × Int) :=
  match acc with
  | (some mo, lv, st, di, false) =>
    if mo = .read ∧ di = 1 then none
    else if mo ≠ .read ∧ di = -1 then none
    else some (mo, lv, st, di)
  | _ => none

/-- This is an equality to the existing public parser, not a replacement spec. -/
theorem gzMode_source_cut (cs : List Char) :
    gzMode? cs = finish (cs.foldl charStep initial) := by rfl

private theorem semanticStep_ite (acc : Acc) (p : Prop) [Decidable p]
    (a b : SemanticAction) :
    semanticStep acc (if p then a else b) = if p then semanticStep acc a else semanticStep acc b := by
  by_cases hp : p <;> simp [hp]

/-- Projection of the actual byte action is exactly the public character step. -/
theorem charStep_semantic (acc : Acc) (c : Char) :
    charStep acc c = semanticStep acc (charAction c) := by
  rcases acc with ⟨mo, lv, st, di, bad⟩
  simp only [charStep, charAction]
  simp only [semanticStep_ite]
  rfl

/-- The complete public parser is the semantic projection of source byte
classification over the entire input, in its original order. -/
theorem gzMode_byte_fold (bs : List UInt8) :
    gzMode? (bs.map (fun b => Char.ofNat b.toNat)) =
      finish (bs.foldl (fun acc b => semanticStep acc (semanticAction (sourceAction b))) initial) := by
  rw [gzMode_source_cut, List.foldl_map]
  have he : (fun acc b => charStep acc (Char.ofNat b.toNat)) =
      (fun acc b => semanticStep acc (semanticAction (sourceAction b))) := by
    funext acc b
    rw [charStep_semantic, sourceAction_semantic]
  rw [he]

/-- The freeing action is selected exactly by the '+' byte over the full domain. -/
theorem sourceAction_bad (b : UInt8) : sourceAction b = .bad ↔ b = 43 := by
  have complete : ∀ j : Fin 256, sourceAction (UInt8.ofNat j.val) = .bad ↔ UInt8.ofNat j.val = 43 := by
    decide +kernel
  simpa using complete ⟨b.toNat, b.toNat_lt⟩

def badFlag (acc : Acc) : Bool := acc.2.2.2.2

private theorem semantic_bad (acc : Acc) (action : SemanticAction) :
    badFlag (semanticStep acc action) = (badFlag acc || decide (action = .bad)) := by
  rcases acc with ⟨mo, lv, st, di, bad⟩
  cases action <;> simp [badFlag, semanticStep]

/-- A later valid-looking character never clears an earlier '+' error. -/
theorem semanticStep_bad (acc : Acc) (b : UInt8) :
    badFlag (semanticStep acc (semanticAction (sourceAction b))) =
      (badFlag acc || decide (b = 43)) := by
  rw [semantic_bad]
  have he : semanticAction (sourceAction b) = .bad ↔ sourceAction b = .bad := by
    cases sourceAction b <;> simp [semanticAction]
  simp only [he, sourceAction_bad]

/-- The public bad bit describes membership of '+' in the full mode list. -/
theorem badFlag_fold (bs : List UInt8) (acc : Acc) :
    badFlag (bs.foldl (fun acc b => semanticStep acc (semanticAction (sourceAction b))) acc) =
      (badFlag acc || decide ((43 : UInt8) ∈ bs)) := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, semanticStep_bad]
    simp [List.mem_cons, Bool.or_assoc, eq_comm]

/-- The original API parser rejects '+' anywhere, regardless of later flags. -/
theorem gzMode_plus (bs : List UInt8) (hb : (43 : UInt8) ∈ bs) :
    gzMode? (bs.map (fun b => Char.ofNat b.toNat)) = none := by
  rw [gzMode_byte_fold]
  have hbad : badFlag (bs.foldl (fun acc b => semanticStep acc (semanticAction (sourceAction b))) initial) = true := by
    rw [badFlag_fold]
    simp [hb]
  generalize he : bs.foldl (fun acc b => semanticStep acc (semanticAction (sourceAction b))) initial = acc at *
  rcases acc with ⟨mo, lv, st, di, bad⟩
  have hb' : bad = true := hbad
  subst bad
  cases mo <;> rfl

#print axioms sourceAction_bad
#print axioms badFlag_fold
#print axioms gzMode_plus
#print axioms sourceAction_semantic
#print axioms gzMode_source_cut
#print axioms charStep_semantic
#print axioms gzMode_byte_fold
end ZlibF.Math.GzModeParser
