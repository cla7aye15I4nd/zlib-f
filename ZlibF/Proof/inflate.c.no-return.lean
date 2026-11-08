import ZlibF.Proof.«inflate.c.main.table2»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- A do-while propagates only exceptions actually produced by its parts. -/
theorem noRet_xdoWhile {body : X Unit} {cond : X Bool} (hb : NoRet body) (hc : NoRet cond) :
    NoRet (xdoWhile body cond) := by
  unfold xdoWhile
  exact noRet_bind hb (fun _ => noRet_xwhile hc hb)

/-- A lookup loop does not invent a direct API return. -/
theorem noRet_xloopBrk {body : X Bool} (hb : NoRet body) : NoRet (xloopBrk body) :=
  noRet_xwhileBrk (noRet_pure true) hb

theorem noRet_BITS (n : UInt32) : NoRet (BITS n) := by
  unfold BITS
  exact noRet_bind noRet_get (fun _ => noRet_bind (noRet_lift _) (fun _ => noRet_pure _))

theorem noRet_DROPBITS (n : UInt32) : NoRet (DROPBITS n) := by
  unfold DROPBITS
  exact noRet_bind noRet_get (fun _ => noRet_bind (noRet_lift _) (fun _ => noRet_set _))

theorem noRet_LOAD (strm : ZStreamPtr) (st : InflateStatePtr) : NoRet (LOAD strm st) := by
  unfold LOAD
  exact noRet_bind (noRet_lift _) (fun _ => noRet_bind (noRet_lift _) (fun _ => noRet_modify _))

theorem noRet_RESTORE (strm : ZStreamPtr) (st : InflateStatePtr) : NoRet (RESTORE strm st) := by
  unfold RESTORE
  exact noRet_bind noRet_get (fun _ => noRet_bind (noRet_lift _) (fun _ => noRet_lift _))

theorem noRet_lookup1 (c : Ctx) (dist : Bool) : NoRet (lookup1 c dist) := by
  unfold lookup1
  apply noRet_xloopBrk
  repeat' first
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_lift _
    | with_reducible exact noRet_PULLBYTE
    | with_reducible exact noRet_BITS _
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))

theorem noRet_lookup2 (c : Ctx) (dist : Bool) : NoRet (lookup2 c dist) := by
  unfold lookup2
  apply noRet_xloopBrk
  repeat' first
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_lift _
    | with_reducible exact noRet_PULLBYTE
    | with_reducible exact noRet_BITS _
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))

/-- Actual LIT code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_LIT (c : Ctx) : NoRet (inflate_LIT c) := by
  unfold inflate_LIT
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual MATCH code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_MATCH (c : Ctx) : NoRet (inflate_MATCH c) := by
  unfold inflate_MATCH
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual DISTEXT code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_DISTEXT (c : Ctx) : NoRet (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual DIST code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_DIST (c : Ctx) : NoRet (inflate_DIST c) := by
  unfold inflate_DIST
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_inflate_DISTEXT _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual LENEXT code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_LENEXT (c : Ctx) : NoRet (inflate_LENEXT c) := by
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_inflate_DISTEXT _
    | with_reducible exact noRet_inflate_DIST _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual LEN code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_LEN (c : Ctx) : NoRet (inflate_LEN c) := by
  unfold inflate_LEN
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_inflate_DISTEXT _
    | with_reducible exact noRet_inflate_DIST _
    | with_reducible exact noRet_inflate_LENEXT _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual LEN_ code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_LEN_ (c : Ctx) : NoRet (inflate_LEN_ c) := by
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_inflate_DISTEXT _
    | with_reducible exact noRet_inflate_DIST _
    | with_reducible exact noRet_inflate_LENEXT _
    | with_reducible exact noRet_inflate_LEN _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual CODELENS code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_CODELENS (c : Ctx) : NoRet (inflate_CODELENS c) := by
  unfold inflate_CODELENS
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_inflate_DISTEXT _
    | with_reducible exact noRet_inflate_DIST _
    | with_reducible exact noRet_inflate_LENEXT _
    | with_reducible exact noRet_inflate_LEN _
    | with_reducible exact noRet_inflate_LEN_ _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual LENLENS code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_LENLENS (c : Ctx) : NoRet (inflate_LENLENS c) := by
  unfold inflate_LENLENS
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_inflate_DISTEXT _
    | with_reducible exact noRet_inflate_DIST _
    | with_reducible exact noRet_inflate_LENEXT _
    | with_reducible exact noRet_inflate_LEN _
    | with_reducible exact noRet_inflate_LEN_ _
    | with_reducible exact noRet_inflate_CODELENS _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _

/-- Actual TABLE code may leave the mode loop; it never returns an
arbitrary API code directly. Runtime faults are covered separately. -/
theorem noRet_inflate_TABLE (c : Ctx) : NoRet (inflate_TABLE c) := by
  unfold inflate_TABLE
  repeat' first
    | with_reducible exact noRet_NEEDBITS _
    | with_reducible exact noRet_BITS _
    | with_reducible exact noRet_DROPBITS _
    | with_reducible exact noRet_lookup1 _ _
    | with_reducible exact noRet_lookup2 _ _
    | with_reducible exact noRet_LOAD _ _
    | with_reducible exact noRet_RESTORE _ _
    | with_reducible exact noRet_inflate_LIT _
    | with_reducible exact noRet_inflate_MATCH _
    | with_reducible exact noRet_inflate_DISTEXT _
    | with_reducible exact noRet_inflate_DIST _
    | with_reducible exact noRet_inflate_LENEXT _
    | with_reducible exact noRet_inflate_LEN _
    | with_reducible exact noRet_inflate_LEN_ _
    | with_reducible exact noRet_inflate_CODELENS _
    | with_reducible exact noRet_inflate_LENLENS _
    | with_reducible exact noRet_pure _
    | with_reducible exact noRet_get
    | with_reducible exact noRet_modify _
    | with_reducible exact noRet_set _
    | with_reducible exact noRet_leave
    | with_reducible apply noRet_xdoWhile
    | with_reducible apply noRet_xwhile
    | with_reducible apply noRet_xwhileBrk
    | with_reducible apply noRet_ite
    | with_reducible (refine noRet_bind ?_ (fun _ => ?_))
    | with_reducible exact noRet_lift _


/-- A checked run of a mode without direct returns has exactly the two
control outcomes used by the main dispatch loop. -/
theorem NoRet.outcomes {program : X Unit} (noReturn : NoRet program)
    {l regs : IL} {h after : Heap} {outcome : Except Ex Unit}
    (run : runX program l h = .ok ((outcome, regs), after)) :
    outcome = .error Ex.leave ∨ outcome = .ok () := by
  cases outcome with
  | ok value => cases value; exact Or.inr rfl
  | error exit =>
    cases exit with
    | leave => exact Or.inl rfl
    | ret value => exact False.elim (noReturn l h _ regs after run value rfl)

end Zlib.Inflate.Proofs
