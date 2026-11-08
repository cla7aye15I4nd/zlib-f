import ZlibF.Proof.«inflate.c.exit-code-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual DONE mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_DONE (context : Ctx) :
    ExitCodesX (inflate_DONE context) := by
  unfold inflate_DONE
  exit_codes_source

/-- The actual LENGTH mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_LENGTH (context : Ctx) :
    ExitCodesX (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  have continuation0 := exitCodesX_inflate_DONE context
  exit_codes_source

/-- The actual CHECK mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_CHECK (context : Ctx) :
    ExitCodesX (inflate_CHECK context) := by
  unfold inflate_CHECK
  have continuation0 := exitCodesX_inflate_LENGTH context
  exit_codes_source

/-- The actual LIT mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_LIT (context : Ctx) :
    ExitCodesX (inflate_LIT context) := by
  unfold inflate_LIT
  exit_codes_source

/-- The actual MATCH mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_MATCH (context : Ctx) :
    ExitCodesX (inflate_MATCH context) := by
  unfold inflate_MATCH
  exit_codes_source

/-- The actual DISTEXT mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_DISTEXT (context : Ctx) :
    ExitCodesX (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  have continuation0 := exitCodesX_inflate_MATCH context
  exit_codes_source

/-- The actual DIST mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_DIST (context : Ctx) :
    ExitCodesX (inflate_DIST context) := by
  unfold inflate_DIST
  have continuation0 := exitCodesX_inflate_DISTEXT context
  exit_codes_source

/-- The actual LENEXT mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_LENEXT (context : Ctx) :
    ExitCodesX (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  have continuation0 := exitCodesX_inflate_DIST context
  exit_codes_source

/-- The actual LEN mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_LEN (context : Ctx) :
    ExitCodesX (inflate_LEN context) := by
  unfold inflate_LEN
  have continuation0 := exitCodesX_inflate_LENEXT context
  exit_codes_source

/-- The actual LEN_ mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_LEN_ (context : Ctx) :
    ExitCodesX (inflate_LEN_ context) := by
  unfold inflate_LEN_
  have continuation0 := exitCodesX_inflate_LEN context
  exit_codes_source

/-- The actual CODELENS mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_CODELENS (context : Ctx) :
    ExitCodesX (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  have continuation0 := exitCodesX_inflate_LEN_ context
  exit_codes_source

/-- The actual LENLENS mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_LENLENS (context : Ctx) :
    ExitCodesX (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  have continuation0 := exitCodesX_inflate_CODELENS context
  exit_codes_source

/-- The actual TABLE mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_TABLE (context : Ctx) :
    ExitCodesX (inflate_TABLE context) := by
  unfold inflate_TABLE
  have continuation0 := exitCodesX_inflate_LENLENS context
  exit_codes_source

/-- The actual COPY mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_COPY (context : Ctx) :
    ExitCodesX (inflate_COPY context) := by
  unfold inflate_COPY
  exit_codes_source

/-- The actual COPY_ mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_COPY_ (context : Ctx) :
    ExitCodesX (inflate_COPY_ context) := by
  unfold inflate_COPY_
  have continuation0 := exitCodesX_inflate_COPY context
  exit_codes_source

/-- The actual STORED mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_STORED (context : Ctx) :
    ExitCodesX (inflate_STORED context) := by
  unfold inflate_STORED
  have continuation0 := exitCodesX_inflate_COPY_ context
  exit_codes_source

/-- The actual TYPEDO mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_TYPEDO (context : Ctx) :
    ExitCodesX (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  exit_codes_source

/-- The actual TYPE mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_TYPE (context : Ctx) :
    ExitCodesX (inflate_TYPE context) := by
  unfold inflate_TYPE
  have continuation0 := exitCodesX_inflate_TYPEDO context
  exit_codes_source

/-- The actual DICT mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_DICT (context : Ctx) :
    ExitCodesX (inflate_DICT context) := by
  unfold inflate_DICT
  have continuation0 := exitCodesX_inflate_TYPE context
  exit_codes_source

/-- The actual DICTID mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_DICTID (context : Ctx) :
    ExitCodesX (inflate_DICTID context) := by
  unfold inflate_DICTID
  have continuation0 := exitCodesX_inflate_DICT context
  exit_codes_source

/-- The actual HCRC mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_HCRC (context : Ctx) :
    ExitCodesX (inflate_HCRC context) := by
  unfold inflate_HCRC
  exit_codes_source

/-- The actual COMMENT mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_COMMENT (context : Ctx) :
    ExitCodesX (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  have continuation0 := exitCodesX_inflate_HCRC context
  exit_codes_source

/-- The actual NAME mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_NAME (context : Ctx) :
    ExitCodesX (inflate_NAME context) := by
  unfold inflate_NAME
  have continuation0 := exitCodesX_inflate_COMMENT context
  exit_codes_source

/-- The actual EXTRA mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_EXTRA (context : Ctx) :
    ExitCodesX (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  have continuation0 := exitCodesX_inflate_NAME context
  exit_codes_source

/-- The actual EXLEN mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_EXLEN (context : Ctx) :
    ExitCodesX (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  have continuation0 := exitCodesX_inflate_EXTRA context
  exit_codes_source

/-- The actual OS mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_OS (context : Ctx) :
    ExitCodesX (inflate_OS context) := by
  unfold inflate_OS
  have continuation0 := exitCodesX_inflate_EXLEN context
  exit_codes_source

/-- The actual TIME mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_TIME (context : Ctx) :
    ExitCodesX (inflate_TIME context) := by
  unfold inflate_TIME
  have continuation0 := exitCodesX_inflate_OS context
  exit_codes_source

/-- The actual FLAGS mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_FLAGS (context : Ctx) :
    ExitCodesX (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  have continuation0 := exitCodesX_inflate_TIME context
  exit_codes_source

/-- The actual HEAD mode has classified direct-return exits on every successful
run, including its source fallthrough and explicit control exits. -/
theorem exitCodesX_inflate_HEAD (context : Ctx) :
    ExitCodesX (inflate_HEAD context) := by
  unfold inflate_HEAD
  exit_codes_source

end Zlib.Inflate.Proofs
