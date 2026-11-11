import ZlibF.Spec.InflateTableInvariant
import ZlibF.Proof.«inftrees.c.fixed»
import ZlibF.Proof.«inflate.c.platform»
import ZlibF.Proof.«inflate.c.main.type»

/-!
# inflate.c: producers of the guarded data-table invariant

The initial state and the actual fixed-table installation establish this
clause without assuming a decoder-table contract. Dynamic installation and
preservation through all stream operations are separate obligations.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
open Zlib.Inftrees.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- HEAD does not read a data table. Requiring a fully initialized data
table here would give the wrong invariant for successful initialization. -/
theorem dataTableInvariant_head {h : Heap} {s : InflateState} (head : s.mode = HEAD) :
    DataTableInvariant h s := by
  intro mode
  rw [head] at mode
  simp only [DataTableMode] at mode
  rcases mode with a | a | a | a | a | a | a <;> contradiction

set_option maxRecDepth 100000 in
/-- The fixed pointers resolve to the actual reviewed static arrays. -/
theorem fixedState_tables_safe {h : Heap} (s : InflateState) (globals : LibraryGlobals h) :
    DataTablesSafe h (fixedState s) := by
  constructor
  · refine ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, rfl, ?_, ?_⟩
    · change some h.static.lenfix = some Zlib.InffixedH.lenfix
      rw [globals]
      rfl
    · exact Zlib.Inffast.Proofs.lenfix_tableSafe
  · refine ⟨.st_distfix, 0, Zlib.InffixedH.distfix, rfl, ?_, ?_⟩
    · change some h.static.distfix = some Zlib.InffixedH.distfix
      rw [globals]
      rfl
    · exact Zlib.Inffast.Proofs.distfix_tableSafe
  · intro ref offset ca pointer get
    have fixed : Ptr.ref CodeRef.st_lenfix 0 = .ref ref offset := pointer
    cases fixed
    have known : Space.get h CodeRef.st_lenfix = some Zlib.InffixedH.lenfix := by
      change some h.static.lenfix = some Zlib.InffixedH.lenfix
      rw [globals]
      rfl
    rw [known] at get
    cases get
    exact Zlib.Inffast.Proofs.lenfix_leavesPositive

/-- `void inflate_fixed(struct inflate_state *state)`.
The actual installer returns pointers to the actual static arrays. Their
table safety comes from the proved static-table facts and the library's
explicit global-data representation, not a table premise from the caller. -/
theorem inflate_fixed_tables_safe {h : Heap} {zs : Nat} {s : InflateState}
    (state : h.istates zs = some s) (globals : LibraryGlobals h) :
    ∃ after,
      C.run (Zlib.Inftrees.inflate_fixed (some (.tab zs))) h = .ok ((), after) ∧
      after.istates zs = some (fixedState s) ∧
      DataTablesSafe after (fixedState s) := by
  exact ⟨setI h zs (fixedState s), inflate_fixed_ok state, by simp,
    fixedState_tables_safe s globals⟩

/-- `case TYPEDO:` with a fixed block and flush other than Z_TREES.
The actual branch enters LEN_ and establishes the now-active data-table
clause. This connects the installer to dispatch rather than only checking
the table arrays independently. -/
theorem typedoTail_fixed_tableInvariant {c : Ctx} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (env : Env c h r zs z s) (globals : LibraryGlobals h) (l : IL)
    (header : l.hold.toNat % 4 = 1) (flush : c.flush ≠ Z_TREES) :
    runX (typedoTail c) l h =
      .ok ((.ok (), { l with hold := l.hold >>> 2, bits := l.bits - 2 }),
        setI h zs { fixedState s with mode := LEN_ }) ∧
      DataTableInvariant (setI h zs { fixedState s with mode := LEN_ })
        { fixedState s with mode := LEN_ } := by
  refine ⟨typedoTail_fixed env l header flush, ?_⟩
  intro _
  have tables := fixedState_tables_safe
    (h := setI h zs { fixedState s with mode := LEN_ }) s globals
  exact ⟨tables.lengthTable, tables.distanceTable, tables.lengthLeaves⟩

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
For every accepted parameter, successful actual initialization establishes
the guarded data-table clause along with Good and the platform scope. No
table validity or callee correctness is assumed. This is one safety clause,
not a proof of the entire persistent invariant or public inflate call. -/
theorem inflate_init_dataTableInvariant
    (h : Heap) (r : ZStreamRef) (version : BPtr) (wb : Int32)
    (wrap : ZlibF.Spec.Api.Wrap) (bits : Nat)
    (domain : InitDomain h r version) (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (params : ZlibF.Spec.Api.inflWbits wb.toInt = some (wrap, bits))
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after z s,
      C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) ∧
      Good after r h.nextBlk z s ∧ s.mode = HEAD ∧
      DataTableInvariant after s ∧ ZlibF.PlatformMemory.ByteObjectsFit after ∧
      StreamReachable .inflate after r := by
  obtain ⟨after, run, initial, reachable, fit⟩ :=
    ZlibF.Spec.Public.Proofs.InflateInit.inflate_domain_general_platform
      h r version wb wrap bits domain platform params allocation
  obtain ⟨z, s, good, _, _, head, rest⟩ := initial
  exact ⟨after, z, s, run, good, head, dataTableInvariant_head head, fit, reachable⟩

end Zlib.Inflate.Proofs
