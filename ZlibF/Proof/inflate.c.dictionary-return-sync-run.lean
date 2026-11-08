import ZlibF.Proof.«inflate.c.dictionary-return-sync-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual complete mode switch retains actual public cursor
bindings on NEED_DICT, including non-default wrapper modes. -/
theorem needDictSyncX_inflate_dispatch (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_dispatch context) := by
  unfold inflate_dispatch
  have branch0 := needDictSyncX_inflate_DONE r context
  have branch1 := needDictSyncX_inflate_LENGTH r context
  have branch2 := needDictSyncX_inflate_CHECK r context
  have branch3 := needDictSyncX_inflate_LIT r context
  have branch4 := needDictSyncX_inflate_MATCH r context
  have branch5 := needDictSyncX_inflate_DISTEXT r context
  have branch6 := needDictSyncX_inflate_DIST r context
  have branch7 := needDictSyncX_inflate_LENEXT r context
  have branch8 := needDictSyncX_inflate_LEN r context
  have branch9 := needDictSyncX_inflate_LEN_ r context
  have branch10 := needDictSyncX_inflate_CODELENS r context
  have branch11 := needDictSyncX_inflate_LENLENS r context
  have branch12 := needDictSyncX_inflate_TABLE r context
  have branch13 := needDictSyncX_inflate_COPY r context
  have branch14 := needDictSyncX_inflate_COPY_ r context
  have branch15 := needDictSyncX_inflate_STORED r context
  have branch16 := needDictSyncX_inflate_TYPEDO r context
  have branch17 := needDictSyncX_inflate_TYPE r context
  have branch18 := needDictSyncX_inflate_DICT r context zs root state
  have branch19 := needDictSyncX_inflate_DICTID r context zs root state
  have branch20 := needDictSyncX_inflate_HCRC r context zs root state
  have branch21 := needDictSyncX_inflate_COMMENT r context zs root state
  have branch22 := needDictSyncX_inflate_NAME r context zs root state
  have branch23 := needDictSyncX_inflate_EXTRA r context zs root state
  have branch24 := needDictSyncX_inflate_EXLEN r context zs root state
  have branch25 := needDictSyncX_inflate_OS r context zs root state
  have branch26 := needDictSyncX_inflate_TIME r context zs root state
  have branch27 := needDictSyncX_inflate_FLAGS r context zs root state
  have branch28 := needDictSyncX_inflate_HEAD r context zs root state
  need_dict_sync_source r

/-- Entry normalization, LOAD and the entire actual mode loop retain the
public cursor/register agreement on every successful NEED_DICT return.
No input, representation, mode or callee safety contract is assumed. -/
theorem needDictSyncX_inflate_run (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_run context) := by
  unfold inflate_run
  have dispatch := needDictSyncX_inflate_dispatch r context zs root state
  need_dict_sync_source r

/-- The actual complete body exposes synchronized public bindings when
it directly requests a dictionary. No invariant or callee contract is
assumed by this successful-execution observer. -/
theorem inflate_run_need_dict_sync
    {context : Ctx} {r : ZStreamRef} {zs : Nat} {l regs : IL} {h after : Heap}
    (root : context.strm = some r) (state : context.st = some (.tab zs))
    (run : runX (inflate_run context) l h = .ok ((.error (.ret Z_NEED_DICT), regs), after)) :
    StreamRegsSync r regs after :=
  needDictSyncX_inflate_run r context zs root state l h _ regs after run (.ret Z_NEED_DICT) rfl rfl

#print axioms inflate_run_need_dict_sync
end Zlib.Inflate.Proofs
