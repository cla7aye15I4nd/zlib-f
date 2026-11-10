import ZlibF.Proof.«inflate.c.input-base-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual DONE mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_DONE (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_DONE context) := by
  unfold inflate_DONE
  input_base_source base

/-- The actual LENGTH mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_LENGTH (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  have continuation0 := inputBaseX_inflate_DONE base context
  input_base_source base

/-- The actual CHECK mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_CHECK (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_CHECK context) := by
  unfold inflate_CHECK
  have continuation0 := inputBaseX_inflate_LENGTH base context
  input_base_source base

/-- The actual LIT mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_LIT (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_LIT context) := by
  unfold inflate_LIT
  input_base_source base

/-- The actual MATCH mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_MATCH (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_MATCH context) := by
  unfold inflate_MATCH
  input_base_source base

/-- The actual DISTEXT mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_DISTEXT (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  have continuation0 := inputBaseX_inflate_MATCH base context
  input_base_source base

/-- The actual DIST mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_DIST (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_DIST context) := by
  unfold inflate_DIST
  have continuation0 := inputBaseX_inflate_DISTEXT base context
  input_base_source base

/-- The actual LENEXT mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_LENEXT (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  have continuation0 := inputBaseX_inflate_DIST base context
  input_base_source base

/-- The actual LEN mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_LEN (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_LEN context) := by
  unfold inflate_LEN
  have continuation0 := inputBaseX_inflate_LENEXT base context
  input_base_source base

/-- The actual LEN_ mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_LEN_ (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_LEN_ context) := by
  unfold inflate_LEN_
  have continuation0 := inputBaseX_inflate_LEN base context
  input_base_source base

/-- The actual CODELENS mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_CODELENS (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  have continuation0 := inputBaseX_inflate_LEN_ base context
  input_base_source base

/-- The actual LENLENS mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_LENLENS (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  have continuation0 := inputBaseX_inflate_CODELENS base context
  input_base_source base

/-- The actual TABLE mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_TABLE (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_TABLE context) := by
  unfold inflate_TABLE
  have continuation0 := inputBaseX_inflate_LENLENS base context
  input_base_source base

/-- The actual COPY mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_COPY (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_COPY context) := by
  unfold inflate_COPY
  input_base_source base

/-- The actual COPY_ mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_COPY_ (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_COPY_ context) := by
  unfold inflate_COPY_
  have continuation0 := inputBaseX_inflate_COPY base context
  input_base_source base

/-- The actual STORED mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_STORED (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_STORED context) := by
  unfold inflate_STORED
  have continuation0 := inputBaseX_inflate_COPY_ base context
  input_base_source base

/-- The actual TYPEDO mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_TYPEDO (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  input_base_source base

/-- The actual TYPE mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_TYPE (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_TYPE context) := by
  unfold inflate_TYPE
  have continuation0 := inputBaseX_inflate_TYPEDO base context
  input_base_source base

/-- The actual DICT mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_DICT (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_DICT context) := by
  unfold inflate_DICT
  have continuation0 := inputBaseX_inflate_TYPE base context
  input_base_source base

/-- The actual DICTID mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_DICTID (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_DICTID context) := by
  unfold inflate_DICTID
  have continuation0 := inputBaseX_inflate_DICT base context
  input_base_source base

/-- The actual HCRC mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_HCRC (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_HCRC context) := by
  unfold inflate_HCRC
  input_base_source base

/-- The actual COMMENT mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_COMMENT (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  have continuation0 := inputBaseX_inflate_HCRC base context
  input_base_source base

/-- The actual NAME mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_NAME (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_NAME context) := by
  unfold inflate_NAME
  have continuation0 := inputBaseX_inflate_COMMENT base context
  input_base_source base

/-- The actual EXTRA mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_EXTRA (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  have continuation0 := inputBaseX_inflate_NAME base context
  input_base_source base

/-- The actual EXLEN mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_EXLEN (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  have continuation0 := inputBaseX_inflate_EXTRA base context
  input_base_source base

/-- The actual OS mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_OS (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_OS context) := by
  unfold inflate_OS
  have continuation0 := inputBaseX_inflate_EXLEN base context
  input_base_source base

/-- The actual TIME mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_TIME (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_TIME context) := by
  unfold inflate_TIME
  have continuation0 := inputBaseX_inflate_OS base context
  input_base_source base

/-- The actual FLAGS mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_FLAGS (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  have continuation0 := inputBaseX_inflate_TIME base context
  input_base_source base

/-- The actual HEAD mode retains its input-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem inputBaseX_inflate_HEAD (base : UInt32) (context : Ctx) :
    InputBaseX base (inflate_HEAD context) := by
  unfold inflate_HEAD
  input_base_source base

end Zlib.Inflate.Proofs
