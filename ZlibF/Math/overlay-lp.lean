import ZlibF.Math.HuffmanTree

/-!
# The memLevel 1–3 overlay LP of `lp2.py`, as data (step 6)

`docs/DEFLATE_OVERLAY.md` §8.2–8.4; `lean/scripts/overlay_search/lowmem/lp2.py`, class `LP`.
This file states that LP in Lean, column for column and row for row, in the same order, so that
a dual certificate written for `lp2.py` (`certs/*.json`, checked by `verify.py`) can be checked
against these rows (`OverlayLPDual.weak_duality`).

## Row format (the interface with the certificate check)

* Columns `Var`: `x ti f l` (number of codes of type `ti` used `f` times with length `l`), `hd`,
  `E`, `N t` (`t = 0..18`), `N16 v` (`v = 1..15`), `A k`, `B k` (`k ∈ {1, 2, 17, 18}`; zero chunks
  of 1, 2, 3–10, 11–138 entries in region A = literals, B = length codes and distance tree).
  `cols` lists them in the order of `lp2.LP.names`.
* A row is `Row Var`: an integer coefficient function and an integer right-hand side.
  `LPData.ineqs` are `≤` rows, `LPData.eqs` are `=` rows, each in the order of `lp2.LP.rows`
  resp. `lp2.LP.eq`, with the cut rows (one per cut code, in the certificate's `cuts` order)
  after the base inequalities.
* Only three rows are scaled to make the coefficients integers (multiply the dual entry of
  `lp2.py` by the inverse factor):
  - `kraftL`, `kraftD`: multiplied by `2^LMAX` (`lp2.py`: coefficients `1/2^l`, rhs 1);
  - each cut row: multiplied by `q`, where `covf = p/q` (`lp2.py`: coefficients
    `-(τ_t + extra_t + covf)`, rhs 71).
* Objective `hd + E`; bounds `0 ≤ x v ≤ ub v` on `cols`.

So a certificate `(yub, yeq)` of `lp2.py` becomes `yu_i = D·yub_i` (`D·yub_i/q` on a cut row),
`ye_k = D·yeq_k` (`D·yeq_k/2^LMAX` on a Kraft row), `D` a common denominator; `weak_duality`
then gives `D·(hd + E) ≤ dualBound` at every feasible point.
-/

namespace Zlib.Trees.OverlayLP
open Zlib.Trees.HuffmanAbstract

/-! ## Generic LP data -/

/-- One LP row: integer coefficients and right-hand side. -/
structure Row (α : Type) where
  coef : α → Int
  rhs : Int

/-- An LP: columns with upper bounds, rows `≤`, rows `=`, objective (maximised). -/
structure LPData (α : Type) where
  cols : List α
  ub : α → Int
  ineqs : List (Row α)
  eqs : List (Row α)
  obj : α → Int

/-- `g·x` over the columns. -/
def evalR {α : Type} (cols : List α) (g : α → Int) (x : α → Int) : Int := (cols.map fun v => g v * x v).sum

/-- A feasible point. -/
structure Feasible {α : Type} (P : LPData α) (x : α → Int) : Prop where
  box : ∀ v ∈ P.cols, 0 ≤ x v ∧ x v ≤ P.ub v
  ineq : ∀ r ∈ P.ineqs, evalR P.cols r.coef x ≤ r.rhs
  eq : ∀ r ∈ P.eqs, evalR P.cols r.coef x = r.rhs

/-- `Σ y_i a_i v` over dual/row pairs. -/
def comb {α : Type} (ps : List (Int × Row α)) (v : α) : Int := (ps.map fun p => p.1 * p.2.coef v).sum

/-- `Σ y_i b_i` over dual/row pairs. -/
def combRhs {α : Type} (ps : List (Int × Row α)) : Int := (ps.map fun p => p.1 * p.2.rhs).sum

/-- Reduced cost `D·c v − Σ y_i a_i v − Σ z_k e_k v`. -/
def redCost {α : Type} (P : LPData α) (D : Int) (yu ye : List Int) (v : α) : Int :=
  D * P.obj v - comb (yu.zip P.ineqs) v - comb (ye.zip P.eqs) v

/-- The dual bound `Σ y b + Σ z b + Σ_cols ub · max(0, red)`. -/
def dualBound {α : Type} (P : LPData α) (D : Int) (yu ye : List Int) : Int :=
  combRhs (yu.zip P.ineqs) + combRhs (ye.zip P.eqs) +
    (P.cols.map fun v => P.ub v * max 0 (redCost P D yu ye v)).sum

/-! ## Columns -/

/-- LP columns (`lp2.LP.names`). -/
inductive Var where
  | x (ti f l : Nat)
  | hd
  | E
  | N (t : Nat)
  | N16 (v : Nat)
  | A (k : Nat)
  | B (k : Nat)
  deriving DecidableEq, Repr

/-- The three cases by the distance tree: ≥ 2 distance codes used, exactly one, none. -/
inductive DCase where
  | M2
  | M1
  | M0
  deriving DecidableEq, Repr

/-- Kind of a code type. -/
inductive Kind where
  | lit
  | endb
  | lc
  | dc
  deriving DecidableEq, Repr

/-- A code type: kind, fixed-code cost of the code part (`fix`), extra bits, number of codes. -/
structure CType where
  kind : Kind
  fix : Nat
  xb : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- The 8 length-code types, `sorted(Counter((FIXL[k], XL[k])).items())`:
codes 0–7, 8–11, 12–15, 16–19, 20–22, 28, 23, 24–27. -/
def lcTypes : List CType :=
  [⟨.lc, 7, 0, 8⟩, ⟨.lc, 7, 1, 4⟩, ⟨.lc, 7, 2, 4⟩, ⟨.lc, 7, 3, 4⟩, ⟨.lc, 7, 4, 3⟩,
   ⟨.lc, 8, 0, 1⟩, ⟨.lc, 8, 4, 1⟩, ⟨.lc, 8, 5, 4⟩]

/-- The 14 distance-code types by extra bits `0..13` (4 codes with 0 extra bits, 2 otherwise). -/
def dcTypes : List CType := (List.range 14).map fun b => ⟨.dc, 5, b, if b = 0 then 4 else 2⟩

/-- The types (`lp2.LP.types`): literal (fixed cost relaxed to 9), END_BLOCK, and in M2/M1 the
length-code and distance-code types. -/
def types : DCase → List CType
  | .M0 => [⟨.lit, 9, 0, 256⟩, ⟨.endb, 0, 0, 1⟩]
  | _ => [⟨.lit, 9, 0, 256⟩, ⟨.endb, 0, 0, 1⟩] ++ lcTypes ++ dcTypes

/-- `lit_bufsize = 2^(memLevel + 6)`. -/
def LB (ml : Nat) : Nat := 2 ^ (ml + 6)

/-- At most `lit_bufsize − 1` symbols per block. -/
def NN (ml : Nat) : Nat := LB ml - 1

/-- `LMAX = max {l ∈ 1..15 : F(l+1) ≤ lit_bufsize}` (10, 12, 13 for memLevel 1, 2, 3). -/
def lmax (ml : Nat) : Nat := ((List.range' 1 15).filter fun l => fib (l + 1) ≤ LB ml).foldl max 0

/-- Lit/len types weigh at most `lit_bufsize` (symbols + END), distance types at most `N`. -/
def treeW (ml : Nat) (k : Kind) : Nat := if k = .dc then NN ml else LB ml

/-- The frequencies of a type's columns: `[1]` for END, `1..N` otherwise. -/
def fRange (ml : Nat) (k : Kind) : List Nat := if k = .endb then [1] else List.range' 1 (NN ml)

/-- Column `x ti f l` exists: `1 ≤ l ≤ LMAX`, `f·F(l+1) ≤ W` (property (F)), and in M1 the
distance code has length 1. -/
def xColOK (ml : Nat) (c : DCase) (k : Kind) (f l : Nat) : Bool :=
  !(c = .M1 && k = .dc && l != 1) && decide (f * fib (l + 1) ≤ treeW ml k)

/-- The `x` columns of type `ti`. -/
def xColsOf (ml : Nat) (c : DCase) (ti : Nat) (t : CType) : List Var :=
  (fRange ml t.kind).flatMap fun f =>
    ((List.range' 1 (lmax ml)).filter fun l => xColOK ml c t.kind f l).map fun l => Var.x ti f l

/-- Zero-chunk kinds `1, 2, 17, 18`. -/
def chunkKinds : List Nat := [1, 2, 17, 18]

/-- All columns, in the order of `lp2.LP.names`. -/
def cols (ml : Nat) (c : DCase) : List Var :=
  ((types c).zipIdx.flatMap fun p => xColsOf ml c p.2 p.1) ++ [Var.hd, Var.E] ++
    (List.range 19).map Var.N ++ (List.range' 1 15).map Var.N16 ++
    chunkKinds.map Var.A ++ chunkKinds.map Var.B

/-- Type of column index `ti` (a dummy literal type out of range). -/
def tyAt (c : DCase) (ti : Nat) : CType := (types c).getD ti ⟨.lit, 9, 0, 256⟩

/-- Upper bounds (`lp2.LP.ub`). -/
def ub (ml : Nat) (c : DCase) : Var → Int
  | .x ti f _ => if (tyAt c ti).kind = .endb then 1 else min ((tyAt c ti).size : Int) ((NN ml / f : Nat) : Int)
  | .hd => 100000
  | .E => 24 * (NN ml : Int)
  | _ => 400

/-! ## Rows -/

/-- Number of forced (phantom) distance codes of length 1: 0, 1, 2 in M2, M1, M0. -/
def ph : DCase → Nat
  | .M2 => 0
  | .M1 => 1
  | .M0 => 2

/-- A row given by its coefficient on `x ti f l` (through the type) and on the other columns. -/
def xrow (c : DCase) (gx : CType → Nat → Nat → Int) (g : Var → Int) (b : Int) : Row Var :=
  ⟨fun v => match v with
    | .x ti f l => gx (tyAt c ti) f l
    | v => g v, b⟩

/-- Lit/len tree types. -/
def isL (k : Kind) : Bool := k = .lit || k = .endb || k = .lc

/-- `kraftL` (scaled by `2^LMAX`): `Σ_L 2^(LMAX−l) x = 2^LMAX`. -/
def rowKraftL (ml : Nat) (c : DCase) : Row Var :=
  xrow c (fun t _ l => if isL t.kind then 2 ^ (lmax ml - l) else 0) (fun _ => 0) (2 ^ lmax ml)

/-- `kraftD` (M2, scaled by `2^LMAX`). -/
def rowKraftD (ml : Nat) (c : DCase) : Row Var :=
  xrow c (fun t _ l => if t.kind = .dc then 2 ^ (lmax ml - l) else 0) (fun _ => 0) (2 ^ lmax ml)

/-- Sum of the `x` columns of one kind. -/
def rowKind (c : DCase) (k : Kind) (b : Int) : Row Var :=
  xrow c (fun t _ _ => if t.kind = k then 1 else 0) (fun _ => 0) b

/-- `size ti`: at most `size` codes of type `ti`. -/
def rowSize (c : DCase) (ti : Nat) (t : CType) : Row Var :=
  ⟨fun v => match v with
    | .x ti' _ _ => if ti' = ti then 1 else 0
    | _ => 0, t.size⟩

/-- `nsym`: `Σ_{lit, lc} f x ≤ N`. -/
def rowNsym (ml : Nat) (c : DCase) : Row Var :=
  xrow c (fun t f _ => if t.kind = .lit ∨ t.kind = .lc then f else 0) (fun _ => 0) (NN ml)

/-- `m`: `Σ_lc f x = Σ_dc f x`. -/
def rowM (c : DCase) : Row Var :=
  xrow c (fun t f _ => if t.kind = .lc then f else if t.kind = .dc then -(f : Int) else 0) (fun _ => 0) 0

/-- `choice`: `hd + l_END − Σ f (fix − l) ≤ 6`. -/
def rowChoice (c : DCase) : Row Var :=
  xrow c (fun t f l => if t.kind = .endb then l else -((f : Int) * ((t.fix : Int) - l)))
    (fun v => if v = .hd then 1 else 0) 6

/-- `exc a`: `E ≤ Σ_lc f (l + xb − a)⁺ + Σ_dc f (l + xb − 24 + a)⁺`. -/
def rowExc (c : DCase) (a : Nat) : Row Var :=
  xrow c (fun t f l => if t.kind = .lc then -((f : Int) * max 0 ((l : Int) + t.xb - a))
      else if t.kind = .dc then -((f : Int) * max 0 ((l : Int) + t.xb - 24 + a)) else 0)
    (fun v => if v = .E then 1 else 0) 0

/-- `exc` in M0: `E ≤ 0`. -/
def rowExc0 (c : DCase) : Row Var := xrow c (fun _ _ _ => 0) (fun v => if v = .E then 1 else 0) 0

/-- A row on the zero-chunk columns of a region (`A` or `B`) plus `s` times the number of used
codes of the region's kinds. -/
def rowZ (c : DCase) (R : Nat → Var) (w : Nat → Int) (inR : Kind → Bool) (s : Int) (b : Int) : Row Var :=
  xrow c (fun t _ _ => if inR t.kind then s else 0)
    (fun v => if v = R 1 then w 1 else if v = R 2 then w 2 else if v = R 17 then w 17
      else if v = R 18 then w 18 else 0) b

/-- Region A kinds (literals). -/
def inA (k : Kind) : Bool := k = .lit
/-- Region B kinds (length and distance codes). -/
def inB (k : Kind) : Bool := k = .lc || k = .dc

/-- `zA<=`, `zA>=`, `runsA`, `zB<=`, `runsB`. -/
def rowZAle (c : DCase) : Row Var :=
  rowZ c Var.A (fun k => if k = 1 then 1 else if k = 2 then 2 else if k = 17 then 3 else 11) inA 1 256
def rowZAge (c : DCase) : Row Var :=
  rowZ c Var.A (fun k => if k = 1 then -1 else if k = 2 then -2 else if k = 17 then -10 else -138) inA (-1) (-256)
def rowRunsA (c : DCase) : Row Var := rowZ c Var.A (fun _ => 1) inA (-1) 2
def rowZBle (c : DCase) : Row Var :=
  rowZ c Var.B (fun k => if k = 1 then 1 else if k = 2 then 2 else if k = 17 then 3 else 11) inB 1
    (59 - ph c)
def rowRunsB (c : DCase) : Row Var := rowZ c Var.B (fun _ => 1) inB (-1) (ph c)

/-- `N0`, `N17`, `N18`, `N16` (equalities). -/
def rowN0 (c : DCase) : Row Var := xrow c (fun _ _ _ => 0)
  (fun v => if v = .N 0 then 1 else if v = .A 1 ∨ v = .B 1 then -1 else if v = .A 2 ∨ v = .B 2 then -2 else 0) 0
def rowN17 (c : DCase) : Row Var := xrow c (fun _ _ _ => 0)
  (fun v => if v = .N 17 then 1 else if v = .A 17 ∨ v = .B 17 then -1 else 0) 0
def rowN18 (c : DCase) : Row Var := xrow c (fun _ _ _ => 0)
  (fun v => if v = .N 18 then 1 else if v = .A 18 ∨ v = .B 18 then -1 else 0) 0
def rowN16 (c : DCase) : Row Var := xrow c (fun _ _ _ => 0)
  (fun v => match v with
    | .N t => if t = 16 then 1 else 0
    | .N16 u => if 1 ≤ u ∧ u ≤ 15 then -1 else 0
    | _ => 0) 0

/-- `cnt<=u`: `N_u + 3 N16_u − #{codes of length u} ≤ ph·[u = 1]`. -/
def rowCntLe (c : DCase) (u : Nat) : Row Var :=
  xrow c (fun _ _ l => if l = u then -1 else 0)
    (fun v => if v = .N u then 1 else if v = .N16 u then 3 else 0) (if u = 1 then ph c else 0)

/-- `cnt>=u`: `−N_u − 6 N16_u + #{codes of length u} ≤ −ph·[u = 1]`. -/
def rowCntGe (c : DCase) (u : Nat) : Row Var :=
  xrow c (fun _ _ l => if l = u then 1 else 0)
    (fun v => if v = .N u then -1 else if v = .N16 u then -6 else 0) (if u = 1 then -(ph c : Int) else 0)

/-- `extra_blbits` of bit-length symbol `t`. -/
def blExtra (t : Nat) : Nat := if t = 16 then 2 else if t = 17 then 3 else if t = 18 then 7 else 0

/-- Cut row for the code `τ` (scaled by `q`, `covf = p/q`):
`q·hd − Σ_t (q (τ_t + extra_t) + p) N_t ≤ 71 q`. -/
def rowCut (c : DCase) (p q : Nat) (tau : List Nat) : Row Var :=
  xrow c (fun _ _ _ => 0)
    (fun v => match v with
      | .hd => q
      | .N t => if t < 19 then -((q : Int) * (tau.getD t 0 + blExtra t) + p) else 0
      | _ => 0) (71 * q)

/-- Inequality rows (`lp2.LP.rows`), base part. -/
def ineqsBase (ml : Nat) (c : DCase) : List (Row Var) :=
  ((types c).zipIdx.map fun p => rowSize c p.2 p.1) ++ [rowNsym ml c, rowChoice c] ++
    (if c = .M0 then [rowExc0 c] else (List.range 25).map (rowExc c)) ++
    [rowZAle c, rowZAge c, rowRunsA c, rowZBle c, rowRunsB c] ++
    (List.range' 1 15).flatMap fun u => [rowCntLe c u, rowCntGe c u]

/-- Equality rows (`lp2.LP.eq`). -/
def eqRows (ml : Nat) (c : DCase) : List (Row Var) :=
  [rowKraftL ml c] ++ (if c = .M2 then [rowKraftD ml c] else []) ++
    (if c = .M1 then [rowKind c .dc 1] else []) ++ [rowKind c .endb 1] ++
    (if c = .M0 then [] else [rowM c]) ++ [rowN0 c, rowN17 c, rowN18 c, rowN16 c]

/-- The objective `hd + E`. -/
def objHE (v : Var) : Int := if v = .hd ∨ v = .E then 1 else 0

/-- **The LP of `lp2.py`** for memLevel `ml`, case `c`, overflow constant `covf = p/q` (0 for
`huff` and `crude`) and cut codes `cuts` (for `crude`, `cuts = [[7, …, 7]]`). -/
def theLP (ml : Nat) (c : DCase) (p q : Nat) (cuts : List (List Nat)) : LPData Var :=
  ⟨cols ml c, ub ml c, ineqsBase ml c ++ cuts.map (rowCut c p q), eqRows ml c, objHE⟩

end Zlib.Trees.OverlayLP
