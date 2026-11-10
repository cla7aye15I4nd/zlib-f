import ZlibF.Proof.«inflate.c.slow-fragment-parser»
import ZlibF.Proof.«inflate.c.pending-dispatch»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
set_option autoImplicit false

/-- A literal source equality changes only the parser entry expression. -/
theorem ParseResult.run_congr {L D : List Nat} {p : CopySyntax L D} {x next : X Unit} {c : Ctx}
    {h : Heap} {s : InflateState} {l : IL} {bs : List UInt8} {future : List Bool}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    (same : runX x l h = runX next l h)
    (parsed : ParseResult p next c h s l bs future r zs z) :
    ParseResult p x c h s l bs future r zs z := by
  rcases parsed with wait | matched
  · obtain ⟨after, state, regs, used, residual, point, actual, empty, mode⟩ := wait
    exact Or.inl ⟨after, state, regs, used, residual, point, same.trans actual, empty, mode⟩
  · obtain ⟨after, state, regs, used, point, mode, length, was, actual⟩ := matched
    exact Or.inr ⟨after, state, regs, used, point, mode, length, was, same.trans actual⟩

/-- On ordinary LEN, the LEN_ mode write is exactly a self write.
This uses the literal translation and the actual stored state. -/
theorem LEN_start_self {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LEN) :
    runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l h := by
  have same : {s with mode := LEN} = s := by rw [← mode]
  unfold inflate_LEN_
  rw [runX_bind, runX_setMode E, same, tcSetI_same E.hs]

/-- The real dispatch resumes every persistent slow input phase using
syntax retained by public leave and Rebuffer. Current input may end in
any code or extra-bit field. The internal slow guard selects the branch
owned by this proof; the fast branch has its separate semantic consumer. -/
theorem resume_slow_parse_result {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future residual : List Bool}
    {lref dref : CodeRef} {lo lextent doff dextent : Nat} {lca dca : Array Code}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (lpointer : s.lencode = .ref lref lo) (lget : Space.get h lref = some lca)
    (lmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS lca lo s.lenbits.toNat lextent L)
    (lstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS lca lo s.lenbits.toNat)
    (dpointer : s.distcode = .ref dref doff) (dget : Space.get h dref = some dca)
    (dmeaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS dca doff s.distbits.toNat dextent D)
    (dstable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS dca doff s.distbits.toNat)
    (B : BitInv h l bs) (phase : PendingSyntax p s residual) (source : FutureSource l bs future residual)
    (entry : ParserWaitingMode s ∨ s.mode = LEN_)
    (slow : s.mode = LEN ∨ s.mode = LEN_ → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ParseResult p (inflate_dispatch c) c h s l bs future r zs z := by
  have lengthWidth : L.getD p.symbol 0 ≤ 15 := by
    by_cases inside : p.symbol < L.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact lmeaning.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ p.symbol)]
  have distanceWidth : D.getD p.distanceSymbol 0 ≤ 15 := by
    by_cases inside : p.distanceSymbol < D.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      exact dmeaning.acceptable.1 _ (List.getElem_mem inside)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : D.length ≤ p.distanceSymbol)]
  cases phase with
  | len selected =>
    have parsed := LEN_parse_result E good tables lpointer lget lmeaning lstable dpointer dget dmeaning dstable
      B source (slow selected)
    rcases selected with mode | mode
    · exact ParseResult.run_congr ((inflate_dispatch_LEN E l mode).trans (LEN_start_self E l mode).symm) parsed
    · exact ParseResult.run_congr (inflate_dispatch_LEN_start E l mode) parsed
  | lenext mode base extra back =>
    exact ParseResult.run_congr (inflate_dispatch_LENEXT E l mode)
      (LENEXT_parse_result E good tables dpointer dget dmeaning dstable B mode (.lenext mode base extra back) lengthWidth source)
  | dist mode length was back =>
    exact ParseResult.run_congr (inflate_dispatch_DIST E l mode)
      (DIST_parse_result E good tables dpointer dget dmeaning dstable B mode (.dist mode length was back) lengthWidth source)
  | distext mode length was offset extra back =>
    exact ParseResult.run_congr (inflate_dispatch_DISTEXT E l mode)
      (DISTEXT_parse_result E good tables B mode (.distext mode length was offset extra back) lengthWidth distanceWidth source)
  | matching mode was remaining offset back =>
    rcases entry with selected | selected
    · rcases selected with selected | selected | selected | selected <;> rw [selected] at mode <;> contradiction
    · rw [selected] at mode
      contradiction

#print axioms ParseResult.run_congr
#print axioms LEN_start_self
#print axioms resume_slow_parse_result
end Zlib.Inflate.Proofs.SlowInputFragment
