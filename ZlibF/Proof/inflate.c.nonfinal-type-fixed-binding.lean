import ZlibF.Proof.«inflate.c.nonfinal-type-table-v1»
import ZlibF.Proof.«inffixed.h.fixed-length-query-take»
import ZlibF.Proof.«inftrees.c.fixed-distance-query-take-v1»
import ZlibF.Proof.«inftrees.c.global-pair-query-take»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inftrees.Proofs.QueryTakeSource
set_option autoImplicit false

/-- Actual static pointers and global arrays supply all three independent
fixed-table facts: canonical decode, fast flags, and consumed-prefix query. -/
theorem fixed_table_binding
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s mid : InflateState}
    (origin : DefaultOriginState h r zs z s) :
    TableBinding (setI h zs {fixedState mid with mode := LEN_})
      {fixedState mid with mode := LEN_} fixedLitLens fixedDistLens := by
  let state := {fixedState mid with mode := LEN_}
  have globals : LibraryGlobals h := origin.toDefaultStateJ.globals
  have lenGet : Space.get (setI h zs state) (CodeRef.st_lenfix) = some Zlib.InffixedH.lenfix := by
    change some h.static.lenfix = some Zlib.InffixedH.lenfix
    rw [globals]
    rfl
  have distGet : Space.get (setI h zs state) (CodeRef.st_distfix) = some Zlib.InffixedH.distfix := by
    change some h.static.distfix = some Zlib.InffixedH.distfix
    rw [globals]
    rfl
  have installed : InstalledTables (setI h zs state) state fixedLitLens fixedDistLens := by
    constructor
    · exact ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, 512, rfl, lenGet,
        Zlib.InffixedH.Proofs.lenfix_decode_invariant,
        Zlib.InffixedH.Proofs.lenfix_stable_query⟩
    · exact ⟨.st_distfix, 0, Zlib.InffixedH.distfix, 32, rfl, distGet,
        Zlib.InffixedH.Proofs.distfix_decode_invariant,
        Zlib.InffixedH.Proofs.distfix_stable_query⟩
  obtain ⟨fastLen, fastDist⟩ := Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags
  have flags : InstalledQueryFlags (setI h zs state) state := by
    constructor
    · exact ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, rfl, lenGet, fastLen⟩
    · exact ⟨.st_distfix, 0, Zlib.InffixedH.distfix, rfl, distGet, fastDist⟩
  have takes : InstalledQueryTake (setI h zs state) state := by
    constructor
    · exact ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, rfl, lenGet,
        Zlib.InffixedH.Proofs.lenfix_query_take⟩
    · exact ⟨.st_distfix, 0, Zlib.InffixedH.distfix, rfl, distGet,
        Zlib.Inftrees.Proofs.QueryTakeSource.fixed_distance_query_take⟩
  exact ⟨installed, flags, takes⟩

#print axioms fixed_table_binding
end Zlib.Inflate.Proofs.WholeEpoch
