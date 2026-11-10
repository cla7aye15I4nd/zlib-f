import ZlibF.Proof.«inflate.c.output-base-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual DONE mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_DONE (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_DONE context) := by
  unfold inflate_DONE
  output_base_source base

/-- The actual LENGTH mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_LENGTH (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  have continuation0 := outputBaseX_inflate_DONE base context
  output_base_source base

/-- The actual LIT mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_LIT (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_LIT context) := by
  unfold inflate_LIT
  output_base_source base

/-- The actual MATCH mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_MATCH (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_MATCH context) := by
  unfold inflate_MATCH
  output_base_source base

/-- The actual DISTEXT mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_DISTEXT (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  have continuation0 := outputBaseX_inflate_MATCH base context
  output_base_source base

/-- The actual DIST mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_DIST (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_DIST context) := by
  unfold inflate_DIST
  have continuation0 := outputBaseX_inflate_DISTEXT base context
  output_base_source base

/-- The actual LENEXT mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_LENEXT (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  have continuation0 := outputBaseX_inflate_DIST base context
  output_base_source base

/-- The actual LEN mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_LEN (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_LEN context) := by
  unfold inflate_LEN
  have continuation0 := outputBaseX_inflate_LENEXT base context
  output_base_source base

/-- The actual LEN_ mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_LEN_ (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_LEN_ context) := by
  unfold inflate_LEN_
  have continuation0 := outputBaseX_inflate_LEN base context
  output_base_source base

/-- The actual CODELENS mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_CODELENS (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  have continuation0 := outputBaseX_inflate_LEN_ base context
  output_base_source base

/-- The actual LENLENS mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_LENLENS (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  have continuation0 := outputBaseX_inflate_CODELENS base context
  output_base_source base

/-- The actual TABLE mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_TABLE (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_TABLE context) := by
  unfold inflate_TABLE
  have continuation0 := outputBaseX_inflate_LENLENS base context
  output_base_source base

/-- The actual COPY mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_COPY (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_COPY context) := by
  unfold inflate_COPY
  output_base_source base

/-- The actual COPY_ mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_COPY_ (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_COPY_ context) := by
  unfold inflate_COPY_
  have continuation0 := outputBaseX_inflate_COPY base context
  output_base_source base

/-- The actual STORED mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_STORED (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_STORED context) := by
  unfold inflate_STORED
  have continuation0 := outputBaseX_inflate_COPY_ base context
  output_base_source base

/-- The actual TYPEDO mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_TYPEDO (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  output_base_source base

/-- The actual TYPE mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_TYPE (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_TYPE context) := by
  unfold inflate_TYPE
  have continuation0 := outputBaseX_inflate_TYPEDO base context
  output_base_source base

/-- The actual DICT mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_DICT (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_DICT context) := by
  unfold inflate_DICT
  have continuation0 := outputBaseX_inflate_TYPE base context
  output_base_source base

/-- The actual DICTID mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_DICTID (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_DICTID context) := by
  unfold inflate_DICTID
  have continuation0 := outputBaseX_inflate_DICT base context
  output_base_source base

/-- The actual HCRC mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_HCRC (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_HCRC context) := by
  unfold inflate_HCRC
  output_base_source base

/-- The actual COMMENT mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_COMMENT (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  have continuation0 := outputBaseX_inflate_HCRC base context
  output_base_source base

/-- The actual NAME mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_NAME (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_NAME context) := by
  unfold inflate_NAME
  have continuation0 := outputBaseX_inflate_COMMENT base context
  output_base_source base

/-- The actual EXTRA mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_EXTRA (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  have continuation0 := outputBaseX_inflate_NAME base context
  output_base_source base

/-- The actual EXLEN mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_EXLEN (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  have continuation0 := outputBaseX_inflate_EXTRA base context
  output_base_source base

/-- The actual OS mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_OS (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_OS context) := by
  unfold inflate_OS
  have continuation0 := outputBaseX_inflate_EXLEN base context
  output_base_source base

/-- The actual TIME mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_TIME (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_TIME context) := by
  unfold inflate_TIME
  have continuation0 := outputBaseX_inflate_OS base context
  output_base_source base

/-- The actual FLAGS mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_FLAGS (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  have continuation0 := outputBaseX_inflate_TIME base context
  output_base_source base

/-- The actual HEAD mode retains its output-count base on every successful
run, including its source fallthrough and explicit control exits. -/
theorem outputBaseX_inflate_HEAD (base : UInt32) (context : Ctx) :
    OutputBaseX base (inflate_HEAD context) := by
  unfold inflate_HEAD
  output_base_source base

end Zlib.Inflate.Proofs
