import ZlibF.Proof.«deflate.c.quiet-silent»

/-!
# deflate.c: the potential of `DeflateQuiet`

`phiD d` encodes, lexicographically, five components of the deflate state:
1. `phase`: 2 before `FINISH_STATE`, 1 while the trailer is due (`wrap > 0`), 0 after;
2. `rank`: the header state still to write (INIT/GZIP 6, EXTRA 5, NAME 4, COMMENT 3, HCRC 2, else 0);
3. `gzrem`: 2^64 − 1 − `gzindex` (the position inside a header field);
4. `work`: 3·`lookahead` + 2·[`match_available` ≠ 0] + [`sym_next` ≠ 0], plus `strstart` − `block_start` at
   level 0 (the stored data not yet in a block);
5. `pending`.
Every component is bounded, so a lexicographic decrease is a decrease of `phiD` (`phiD_lt`).
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def phase (d : DeflateState) : Nat :=
  if d.status = FINISH_STATE then (if 0 < d.wrap.toInt then 1 else 0) else 2

def rank (d : DeflateState) : Nat :=
  if d.status = INIT_STATE ∨ d.status = GZIP_STATE then 6
  else if d.status = EXTRA_STATE then 5
  else if d.status = NAME_STATE then 4
  else if d.status = COMMENT_STATE then 3
  else if d.status = HCRC_STATE then 2
  else 0

def gzrem (d : DeflateState) : Nat := 2 ^ 64 - 1 - d.gzindex.toNat

def work (d : DeflateState) : Nat :=
  3 * d.lookahead.toNat + (if d.match_available = 0 then 0 else 2) + (if d.sym_next = 0 then 0 else 1) +
    (if d.level = 0 then d.strstart.toNat - d.block_start.toInt.toNat else 0)

/-- The potential of a deflate state. -/
def phiD (d : DeflateState) : Nat :=
  phase d * 2 ^ 166 + rank d * 2 ^ 163 + gzrem d * 2 ^ 99 + work d * 2 ^ 64 + d.pending.toNat

theorem phase_le (d : DeflateState) : phase d ≤ 2 := by
  unfold phase; split <;> (try split) <;> omega

theorem rank_le (d : DeflateState) : rank d ≤ 6 := by
  unfold rank; repeat (first | omega | split)

theorem gzrem_lt (d : DeflateState) : gzrem d < 2 ^ 64 := by
  unfold gzrem; omega

theorem work_lt (d : DeflateState) : work d < 2 ^ 35 := by
  unfold work
  have a := d.lookahead.toNat_lt
  have b := d.strstart.toNat_lt
  have : (if d.match_available = 0 then 0 else 2) ≤ 2 := by split <;> omega
  have : (if d.sym_next = 0 then 0 else 1) ≤ 1 := by split <;> omega
  have : (if d.level = 0 then d.strstart.toNat - d.block_start.toInt.toNat else 0) ≤ d.strstart.toNat := by
    split <;> omega
  omega

/-- A lexicographic decrease of the five components. -/
inductive LexLt (d' d : DeflateState) : Prop
  | phase : phase d' < phase d → LexLt d' d
  | rank : phase d' = phase d → rank d' < rank d → LexLt d' d
  | gzrem : phase d' = phase d → rank d' = rank d → gzrem d' < gzrem d → LexLt d' d
  | work : phase d' = phase d → rank d' = rank d → gzrem d' = gzrem d → work d' < work d → LexLt d' d
  | pending : phase d' = phase d → rank d' = rank d → gzrem d' = gzrem d → work d' = work d →
      d'.pending.toNat < d.pending.toNat → LexLt d' d

theorem phiD_lt {d d' : DeflateState} (lt : LexLt d' d) : phiD d' < phiD d := by
  have p1 := phase_le d; have p2 := phase_le d'
  have r1 := rank_le d; have r2 := rank_le d'
  have g1 := gzrem_lt d; have g2 := gzrem_lt d'
  have w1 := work_lt d; have w2 := work_lt d'
  have q1 := d.pending.toNat_lt; have q2 := d'.pending.toNat_lt
  unfold phiD
  cases lt with
  | phase a => omega
  | rank a b => omega
  | gzrem a b c => omega
  | work a b c e => omega
  | pending a b c e f => omega

/-- `Φ` of `DeflateQuiet`: the potential of the stream's deflate state. -/
def Phi (_flush : Int32) (h : Heap) (r : ZStreamRef) : Nat :=
  match stateOf h r with
  | some d => phiD d
  | none => 0

theorem Phi_eq {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} (flush : Int32)
    (inv : DInv h r ds z d) : Phi flush h r = phiD d := by
  unfold Phi; rw [stateOf_eq inv]

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.Quiet.phiD_lt
