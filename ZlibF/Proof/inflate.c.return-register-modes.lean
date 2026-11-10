import ZlibF.Proof.«inflate.c.return-register-macros»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The actual LIT mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_LIT (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_LIT context) := by
  unfold inflate_LIT
  return_register_source base

/-- The actual MATCH mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_MATCH (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_MATCH context) := by
  unfold inflate_MATCH
  return_register_source base

/-- The actual DISTEXT mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_DISTEXT (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  have continuation0 := returnRegisterX_inflate_MATCH base context
  return_register_source base

/-- The actual DIST mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_DIST (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_DIST context) := by
  unfold inflate_DIST
  have continuation0 := returnRegisterX_inflate_DISTEXT base context
  return_register_source base

/-- The actual LENEXT mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_LENEXT (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  have continuation0 := returnRegisterX_inflate_DIST base context
  return_register_source base

/-- The actual LEN mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_LEN (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_LEN context) := by
  unfold inflate_LEN
  have continuation0 := returnRegisterX_inflate_LENEXT base context
  return_register_source base

/-- The actual LEN_ mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_LEN_ (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_LEN_ context) := by
  unfold inflate_LEN_
  have continuation0 := returnRegisterX_inflate_LEN base context
  return_register_source base

/-- The actual COPY mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_COPY (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_COPY context) := by
  unfold inflate_COPY
  return_register_source base

/-- The actual COPY_ mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_COPY_ (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_COPY_ context) := by
  unfold inflate_COPY_
  have continuation0 := returnRegisterX_inflate_COPY base context
  return_register_source base

/-- The actual STORED mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_STORED (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_STORED context) := by
  unfold inflate_STORED
  have continuation0 := returnRegisterX_inflate_COPY_ base context
  return_register_source base

/-- The actual TYPEDO mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_TYPEDO (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  return_register_source base

/-- The actual TYPE mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_TYPE (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_TYPE context) := by
  unfold inflate_TYPE
  have continuation0 := returnRegisterX_inflate_TYPEDO base context
  return_register_source base

/-- The actual DICT mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_DICT (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_DICT context) := by
  unfold inflate_DICT
  have continuation0 := returnRegisterX_inflate_TYPE base context
  return_register_source base

/-- The actual DICTID mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_DICTID (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_DICTID context) := by
  unfold inflate_DICTID
  have continuation0 := returnRegisterX_inflate_DICT base context
  return_register_source base

/-- The actual HCRC mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_HCRC (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_HCRC context) := by
  unfold inflate_HCRC
  return_register_source base

/-- The actual COMMENT mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_COMMENT (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_COMMENT context) := by
  unfold inflate_COMMENT
  have continuation0 := returnRegisterX_inflate_HCRC base context
  return_register_source base

/-- The actual NAME mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_NAME (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_NAME context) := by
  unfold inflate_NAME
  have continuation0 := returnRegisterX_inflate_COMMENT base context
  return_register_source base

/-- The actual EXTRA mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_EXTRA (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_EXTRA context) := by
  unfold inflate_EXTRA
  have continuation0 := returnRegisterX_inflate_NAME base context
  return_register_source base

/-- The actual EXLEN mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_EXLEN (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_EXLEN context) := by
  unfold inflate_EXLEN
  have continuation0 := returnRegisterX_inflate_EXTRA base context
  return_register_source base

/-- The actual OS mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_OS (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_OS context) := by
  unfold inflate_OS
  have continuation0 := returnRegisterX_inflate_EXLEN base context
  return_register_source base

/-- The actual TIME mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_TIME (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_TIME context) := by
  unfold inflate_TIME
  have continuation0 := returnRegisterX_inflate_OS base context
  return_register_source base

/-- The actual FLAGS mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_FLAGS (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_FLAGS context) := by
  unfold inflate_FLAGS
  have continuation0 := returnRegisterX_inflate_TIME base context
  return_register_source base

/-- The actual HEAD mode retains its return register on every successful
run, including its source fallthrough and explicit control exits. -/
theorem returnRegisterX_inflate_HEAD (base : Int32) (context : Ctx) :
    ReturnRegisterX base (inflate_HEAD context) := by
  unfold inflate_HEAD
  return_register_source base

end Zlib.Inflate.Proofs
