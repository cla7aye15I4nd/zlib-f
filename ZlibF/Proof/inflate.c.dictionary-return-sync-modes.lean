import ZlibF.Proof.«inflate.c.dictionary-return-sync-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual DONE mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_DONE (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_DONE context) := by
  unfold inflate_DONE
  need_dict_sync_source r

/-- The actual LENGTH mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_LENGTH (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  have continuation0 := needDictSyncX_inflate_DONE r context
  need_dict_sync_source r

/-- The actual CHECK mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_CHECK (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_CHECK context) := by
  unfold inflate_CHECK
  have continuation0 := needDictSyncX_inflate_LENGTH r context
  need_dict_sync_source r

/-- The actual LIT mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_LIT (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_LIT context) := by
  unfold inflate_LIT
  need_dict_sync_source r

/-- The actual MATCH mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_MATCH (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_MATCH context) := by
  unfold inflate_MATCH
  need_dict_sync_source r

/-- The actual DISTEXT mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_DISTEXT (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  have continuation0 := needDictSyncX_inflate_MATCH r context
  need_dict_sync_source r

/-- The actual DIST mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_DIST (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_DIST context) := by
  unfold inflate_DIST
  have continuation0 := needDictSyncX_inflate_DISTEXT r context
  need_dict_sync_source r

/-- The actual LENEXT mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_LENEXT (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  have continuation0 := needDictSyncX_inflate_DIST r context
  need_dict_sync_source r

/-- The actual LEN mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_LEN (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_LEN context) := by
  unfold inflate_LEN
  have continuation0 := needDictSyncX_inflate_LENEXT r context
  need_dict_sync_source r

/-- The actual LEN_ mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_LEN_ (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_LEN_ context) := by
  unfold inflate_LEN_
  have continuation0 := needDictSyncX_inflate_LEN r context
  need_dict_sync_source r

/-- The actual CODELENS mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_CODELENS (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  have continuation0 := needDictSyncX_inflate_LEN_ r context
  need_dict_sync_source r

/-- The actual LENLENS mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_LENLENS (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  have continuation0 := needDictSyncX_inflate_CODELENS r context
  need_dict_sync_source r

/-- The actual TABLE mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_TABLE (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_TABLE context) := by
  unfold inflate_TABLE
  have continuation0 := needDictSyncX_inflate_LENLENS r context
  need_dict_sync_source r

/-- The actual COPY mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_COPY (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_COPY context) := by
  unfold inflate_COPY
  need_dict_sync_source r

/-- The actual COPY_ mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_COPY_ (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_COPY_ context) := by
  unfold inflate_COPY_
  have continuation0 := needDictSyncX_inflate_COPY r context
  need_dict_sync_source r

/-- The actual STORED mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_STORED (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_STORED context) := by
  unfold inflate_STORED
  have continuation0 := needDictSyncX_inflate_COPY_ r context
  need_dict_sync_source r

/-- The actual TYPEDO mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_TYPEDO (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  need_dict_sync_source r

/-- The actual TYPE mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_TYPE (r : ZStreamRef) (context : Ctx) :
    NeedDictSyncX r (inflate_TYPE context) := by
  unfold inflate_TYPE
  have continuation0 := needDictSyncX_inflate_TYPEDO r context
  need_dict_sync_source r

/-- The actual DICT mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_DICT (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_DICT context) := by
  unfold inflate_DICT
  have continuation0 := needDictSyncX_inflate_TYPE r context
  repeat' first
    | exact needDictSyncX_request r zs context root state
    | with_reducible exact needDictSyncX_RESTORE r _ _
    | with_reducible assumption
    | with_reducible exact exitPostX_pure _
    | with_reducible exact exitPostX_get
    | with_reducible exact exitPostX_set _
    | with_reducible exact exitPostX_modify _
    | with_reducible exact exitPostX_lift _
    | with_reducible apply exitPostX_ite
    | with_reducible refine exitPostX_bind ?_ (fun _ => ?_)
    | split

/-- The actual DICTID mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_DICTID (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_DICTID context) := by
  unfold inflate_DICTID
  have continuation0 := needDictSyncX_inflate_DICT r context zs root state
  need_dict_sync_source r

/-- The actual HCRC mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_HCRC (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (_root : context.strm = some r) (_state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_HCRC context) := by
  unfold inflate_HCRC
  need_dict_sync_source r

/-- The actual COMMENT mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_COMMENT (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  have continuation0 := needDictSyncX_inflate_HCRC r context zs root state
  need_dict_sync_source r

/-- The actual NAME mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_NAME (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_NAME context) := by
  unfold inflate_NAME
  have continuation0 := needDictSyncX_inflate_COMMENT r context zs root state
  need_dict_sync_source r

/-- The actual EXTRA mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_EXTRA (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  have continuation0 := needDictSyncX_inflate_NAME r context zs root state
  need_dict_sync_source r

/-- The actual EXLEN mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_EXLEN (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  have continuation0 := needDictSyncX_inflate_EXTRA r context zs root state
  need_dict_sync_source r

/-- The actual OS mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_OS (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_OS context) := by
  unfold inflate_OS
  have continuation0 := needDictSyncX_inflate_EXLEN r context zs root state
  need_dict_sync_source r

/-- The actual TIME mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_TIME (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_TIME context) := by
  unfold inflate_TIME
  have continuation0 := needDictSyncX_inflate_OS r context zs root state
  need_dict_sync_source r

/-- The actual FLAGS mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_FLAGS (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (root : context.strm = some r) (state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  have continuation0 := needDictSyncX_inflate_TIME r context zs root state
  need_dict_sync_source r

/-- The actual HEAD mode retains dictionary-return bindings on every successful
run, including its source fallthrough and explicit control exits. -/
theorem needDictSyncX_inflate_HEAD (r : ZStreamRef) (context : Ctx) (zs : Nat)
    (_root : context.strm = some r) (_state : context.st = some (.tab zs)) :
    NeedDictSyncX r (inflate_HEAD context) := by
  unfold inflate_HEAD
  need_dict_sync_source r

end Zlib.Inflate.Proofs
