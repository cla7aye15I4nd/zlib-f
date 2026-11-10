import ZlibF.Proof.«inflate.c.fast-committed-entry-table-geometry»

namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inftrees.Proofs.QueryTakeSource
set_option autoImplicit false

theorem FastLoopReady.code_array_getters
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    Space.get h ctx.codeRef = some ctx.codes ∧
    Space.get h ctx.distRef = some ctx.distCodes := by
  rcases ready with ⟨_, _, _, _, _, _, _, _, codesGet, distGet, _⟩
  exact ⟨codesGet, distGet⟩

/-- Actual installed-table provenance supplies the fast loop's exact
consumed-prefix queries, after identifying the real prelude pointers and
mask widths. These are not public caller conditions. -/
theorem WordReady.installed_query_properties
    {ctx : FastLoopContext} {p : Parameters ctx}
    {h : Heap} {q : Zlib.Inffast.L} {L D : List Nat}
    (ready : WordReady p h q)
    (tables : FunctionalEpoch.InstalledTables h ctx.s L D)
    (take : FunctionalEpoch.InstalledQueryTake h ctx.s)
    (lenCode : ctx.c.lcode = ctx.s.lencode)
    (distCode : ctx.c.dcode = ctx.s.distcode)
    (lenWidth : ctx.rootWidth = ctx.s.lenbits.toNat)
    (distWidth : ctx.distWidth = ctx.s.distbits.toNat) :
    StableQuery DISTS ctx.distCodes ctx.distOff ctx.distWidth ∧
    QueryTake LENS ctx.codes ctx.baseOff ctx.rootWidth ∧
    QueryTake DISTS ctx.distCodes ctx.distOff ctx.distWidth := by
  obtain ⟨lenGet, distGet⟩ :=
    FastLoopReady.code_array_getters ready.state.safety
  have lenPtr : ctx.s.lencode = .ref ctx.codeRef ctx.baseOff :=
    lenCode.symm.trans ctx.lcodePtr
  have distPtr : ctx.s.distcode = .ref ctx.distRef ctx.distOff :=
    distCode.symm.trans ctx.dcodePtr
  obtain ⟨lr, lo, la, lptr, lget, ltake⟩ := take.1
  have lenEq : lr = ctx.codeRef ∧ lo = ctx.baseOff :=
    Ptr.ref.inj (lptr.symm.trans lenPtr)
  rcases lenEq with ⟨rfl, rfl⟩
  have lenArray : la = ctx.codes := Option.some.inj (lget.symm.trans lenGet)
  subst la
  obtain ⟨dr, doff, da, dptr, dget, dtake⟩ := take.2
  have distEq : dr = ctx.distRef ∧ doff = ctx.distOff :=
    Ptr.ref.inj (dptr.symm.trans distPtr)
  rcases distEq with ⟨rfl, rfl⟩
  have distArray : da = ctx.distCodes := Option.some.inj (dget.symm.trans distGet)
  subst da
  obtain ⟨sr, soff, sa, used, sptr, sget, _inv, stable⟩ := tables.2
  have stableEq : sr = ctx.distRef ∧ soff = ctx.distOff :=
    Ptr.ref.inj (sptr.symm.trans distPtr)
  rcases stableEq with ⟨rfl, rfl⟩
  have stableArray : sa = ctx.distCodes := Option.some.inj (sget.symm.trans distGet)
  subst sa
  exact ⟨by simpa only [distWidth] using stable,
    by simpa only [lenWidth] using ltake,
    by simpa only [distWidth] using dtake⟩

#print axioms WordReady.installed_query_properties
end Zlib.Inflate.Proofs.FastCommittedLoop
