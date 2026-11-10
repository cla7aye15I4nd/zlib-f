import ZlibF.Proof.«inflate.c.no-direct-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual DONE mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_DONE (context : Ctx) :
    NoRet (inflate_DONE context) := by
  unfold inflate_DONE
  no_direct_source

/-- The actual LENGTH mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_LENGTH (context : Ctx) :
    NoRet (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  have continuation0 := noDirect_inflate_DONE context
  no_direct_source

/-- The actual CHECK mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_CHECK (context : Ctx) :
    NoRet (inflate_CHECK context) := by
  unfold inflate_CHECK
  have continuation0 := noDirect_inflate_LENGTH context
  no_direct_source

/-- The actual LIT mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_LIT (context : Ctx) :
    NoRet (inflate_LIT context) := by
  unfold inflate_LIT
  no_direct_source

/-- The actual MATCH mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_MATCH (context : Ctx) :
    NoRet (inflate_MATCH context) := by
  unfold inflate_MATCH
  no_direct_source

/-- The actual DISTEXT mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_DISTEXT (context : Ctx) :
    NoRet (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  have continuation0 := noDirect_inflate_MATCH context
  no_direct_source

/-- The actual DIST mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_DIST (context : Ctx) :
    NoRet (inflate_DIST context) := by
  unfold inflate_DIST
  have continuation0 := noDirect_inflate_DISTEXT context
  no_direct_source

/-- The actual LENEXT mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_LENEXT (context : Ctx) :
    NoRet (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  have continuation0 := noDirect_inflate_DIST context
  no_direct_source

/-- The actual LEN mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_LEN (context : Ctx) :
    NoRet (inflate_LEN context) := by
  unfold inflate_LEN
  have continuation0 := noDirect_inflate_LENEXT context
  no_direct_source

/-- The actual LEN_ mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_LEN_ (context : Ctx) :
    NoRet (inflate_LEN_ context) := by
  unfold inflate_LEN_
  have continuation0 := noDirect_inflate_LEN context
  no_direct_source

/-- The actual CODELENS mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_CODELENS (context : Ctx) :
    NoRet (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  have continuation0 := noDirect_inflate_LEN_ context
  no_direct_source

/-- The actual LENLENS mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_LENLENS (context : Ctx) :
    NoRet (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  have continuation0 := noDirect_inflate_CODELENS context
  no_direct_source

/-- The actual TABLE mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_TABLE (context : Ctx) :
    NoRet (inflate_TABLE context) := by
  unfold inflate_TABLE
  have continuation0 := noDirect_inflate_LENLENS context
  no_direct_source

/-- The actual COPY mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_COPY (context : Ctx) :
    NoRet (inflate_COPY context) := by
  unfold inflate_COPY
  no_direct_source

/-- The actual COPY_ mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_COPY_ (context : Ctx) :
    NoRet (inflate_COPY_ context) := by
  unfold inflate_COPY_
  have continuation0 := noDirect_inflate_COPY context
  no_direct_source

/-- The actual STORED mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_STORED (context : Ctx) :
    NoRet (inflate_STORED context) := by
  unfold inflate_STORED
  have continuation0 := noDirect_inflate_COPY_ context
  no_direct_source

/-- The actual TYPEDO mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_TYPEDO (context : Ctx) :
    NoRet (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  no_direct_source

/-- The actual TYPE mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_TYPE (context : Ctx) :
    NoRet (inflate_TYPE context) := by
  unfold inflate_TYPE
  have continuation0 := noDirect_inflate_TYPEDO context
  no_direct_source

/-- The actual HCRC mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_HCRC (context : Ctx) :
    NoRet (inflate_HCRC context) := by
  unfold inflate_HCRC
  no_direct_source

/-- The actual COMMENT mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_COMMENT (context : Ctx) :
    NoRet (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  have continuation0 := noDirect_inflate_HCRC context
  no_direct_source

/-- The actual NAME mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_NAME (context : Ctx) :
    NoRet (inflate_NAME context) := by
  unfold inflate_NAME
  have continuation0 := noDirect_inflate_COMMENT context
  no_direct_source

/-- The actual EXTRA mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_EXTRA (context : Ctx) :
    NoRet (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  have continuation0 := noDirect_inflate_NAME context
  no_direct_source

/-- The actual EXLEN mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_EXLEN (context : Ctx) :
    NoRet (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  have continuation0 := noDirect_inflate_EXTRA context
  no_direct_source

/-- The actual OS mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_OS (context : Ctx) :
    NoRet (inflate_OS context) := by
  unfold inflate_OS
  have continuation0 := noDirect_inflate_EXLEN context
  no_direct_source

/-- The actual TIME mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_TIME (context : Ctx) :
    NoRet (inflate_TIME context) := by
  unfold inflate_TIME
  have continuation0 := noDirect_inflate_OS context
  no_direct_source

/-- The actual FLAGS mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_FLAGS (context : Ctx) :
    NoRet (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  have continuation0 := noDirect_inflate_TIME context
  no_direct_source

/-- The actual HEAD mode has no direct API returns on every successful
run, including its source fallthrough and explicit control exits. -/
theorem noDirect_inflate_HEAD (context : Ctx) :
    NoRet (inflate_HEAD context) := by
  unfold inflate_HEAD
  no_direct_source

end Zlib.Inflate.Proofs
