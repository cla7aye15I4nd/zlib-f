import ZlibF.Spec.InflateCodeLengthInvariant
import ZlibF.Proof.«inflate.c.lenlens-table-safe»
import ZlibF.Proof.«inflate.c.default-entry»
import ZlibF.Proof.«inflate.c.table-rebuffer»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem codeLengthInvariant_head {state : Nat} {s : InflateState} (head : s.mode = HEAD) :
    CodeLengthInvariant state s := by
  intro mode
  rw [head] at mode
  cases mode

/-- The actual LENLENS result already retains the table predicate used
here. With the mode's count bounds, its installed state establishes every
CODELENS boundary clause; have is zero, so no unwritten lens cell is used. -/
theorem llOkSt_codeLengthInvariant (state : Nat) (s : InflateState) (used : Nat)
    (root : UInt32) (work : Array UInt16) (codes : Array Code)
    (table : Zlib.Inftrees.Spec.CodeLengthTableSafe codes 0 root.toNat)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30) :
    CodeLengthInvariant state (llOkSt state s used root work codes) := by
  intro _
  refine ⟨rfl, table, nlen, ndist, ?_, ?_⟩
  · change 0 ≤ _
    omega
  · intro k bound
    change k < 0 at bound
    omega

/-- Actual rebuffering preserves both current table clauses and the
private state record. Caller input and output contents need not be retained. -/
theorem rebuffer_table_clauses {before after : Heap} {r : ZStreamRef}
    {state : Nat} {z : ZStream} {s : InflateState}
    (good : Good before r state z s) (rebuffer : ZlibF.Spec.Public.Rebuffer before after r)
    (data : DataTableInvariant before s) (lengths : CodeLengthInvariant state s) :
    after.istates state = some s ∧ DataTableInvariant after s ∧ CodeLengthInvariant state s := by
  have preserved := rebuffer_dataTableInvariant good rebuffer data
  exact ⟨preserved.1, preserved.2, lengths⟩

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
Successful actual default initialization establishes both current guarded
table clauses. Caller byte storage must satisfy the explicit LP64 scope.
The complete persistent invariant and call-history induction remain separate. -/
theorem inflate_default_init_table_clauses
    (h : Heap) (r : ZStreamRef) (version : BPtr)
    (domain : ZlibF.Spec.Public.InitDomain h r version)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s,
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) ∧
      Good after r h.nextBlk z s ∧ DataTableInvariant after s ∧
      CodeLengthInvariant h.nextBlk s ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      ZlibF.Spec.Public.StreamReachable .inflate after r := by
  obtain ⟨after, z, s, run, _, good, head, _, _, _, tables, fit, reachable⟩ :=
    inflate_default_init_boundary h r version domain platform allocation
  exact ⟨after, z, s, run, good, tables, codeLengthInvariant_head head, fit, reachable⟩

end Zlib.Inflate.Proofs
