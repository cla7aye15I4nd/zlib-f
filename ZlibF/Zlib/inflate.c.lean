import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«inftrees.c»
import ZlibF.Zlib.«zutil.c»
import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«inffast.c»

/-!
# inflate.c — faithful translation

Source: `inflate.c` of the verified source (`zlib/` plus `patches/*.patch`; there is no `ub.patch` yet), default x86_64
Linux build: `GUNZIP` defined, `Z_SOLO`, `PKZIP_BUG_WORKAROUND`, `INFLATE_STRICT`,
`INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`, `ZLIB_DEBUG` undefined (so `Tracev` is nothing and `dmax` is written but
never read). Types as in `docs/design/translation.md`. The notes are `docs/proof/inflate.md`.

## How the control flow is translated

* `inflate()` keeps its registers (`next put have left hold bits in out`) and its other locals (`copy from here last len
  ret`) in the record `IL`. A mode of the `switch` is one `def` (`inflate_HEAD`, ...) of the monad `X`, which is the
  state monad on `IL` over the runtime monad `M` with an exception: `X α = ExceptT Ex (StateT IL M) α`.
  * a mode that ends with `break` just returns;
  * `goto inf_leave` is `throw Ex.leave` (the registers at that moment are kept: the state is not rolled back);
  * `return v` is `throw (Ex.ret v)`;
  * a fall-through is a tail call of the next mode (`TYPE` calls `TYPEDO` without writing the mode field);
  * the macros are `def`s of `X` (`PULLBYTE`, `NEEDBITS`, `BITS`, ...), so a `goto` inside a macro is a `throw`.
* Loops are the runtime's `cwhile` (through `xwhileBrk`, which carries the registers and the exit reason in the loop
  state). `break` out of a `while` or `for (;;)` is the Boolean the body returns.
* The next mode is read from the heap field `state->mode` on every trip of `for (;;)`, as in C.

## Decisions (see the report with this file)

* A pointer to a scalar field (`&state->next`, `&state->lenbits`, `&state->have`, `uInt *dictLength`) is passed as the
  value in and returned as the value out.
* `unsigned char hbuf[4]` and `unsigned char buf[4]` are byte blocks made at the declaration (`allocLocalB`, which never
  fails; it uses the runtime's `allocBytes`) and freed before every return.
* The local variables of `inflate()` that the C leaves uninitialised (`copy len from here last`) start as `0`, `NULL`,
  `{0,0,0}`: an arbitrary value, as the guide allows; `from` starts null so that a use before assignment faults.
* Only the default allocator is modelled (`zcalloc`/`zcfree` stored in the stream); another `zalloc`/`zfree` that the
  code would call is `ub "custom allocator not modelled"`.
* The cast of `strm->state` to `struct inflate_state *` faults if the state is a `deflate_state` (the C reads through
  the wrong type, which is formally undefined).
* The upstream `inflateCopy` fix compares `state->lencode` with `state->codes` for equality before relocating
  pointers into the copied code array. A fixed-table pointer remains fixed and requires no cross-array ordering.
* Error messages are string literals: `strm->msg` points to a fresh read-only block (`Zlib.Zutil.strLit`).
-/

namespace Zlib.Inflate
open C
open Zlib.Crc32 (crc32)
open Zlib.Inffast (inflate_fast)
open Zlib.Inftrees (inflate_table inflate_fixed)
open Zlib.Adler32 (adler32)

/-! ## Arithmetic with the checks of the C -/

/-- `x << n` for `unsigned x`: faults if `n >= 32` (the count is out of range). -/
def shl32 (x n : UInt32) : M UInt32 := if n < 32 then pure (x <<< n) else ub "shift count out of range"
/-- `x >> n` for `unsigned x`. -/
def shr32 (x n : UInt32) : M UInt32 := if n < 32 then pure (x >>> n) else ub "shift count out of range"
/-- `x << n` for `unsigned long x`: faults if `n >= 64`. -/
def shl64 (x : UInt64) (n : UInt32) : M UInt64 := if n < 64 then pure (x <<< n.toUInt64) else ub "shift count out of range"
/-- `x >> n` for `unsigned long x`. -/
def shr64 (x : UInt64) (n : UInt32) : M UInt64 := if n < 64 then pure (x >>> n.toUInt64) else ub "shift count out of range"
/-- An `int` result: faults on signed overflow. -/
def chkI32 (v : Int) : M Int32 :=
  if -2147483648 ≤ v ∧ v < 2147483648 then pure (Int32.ofInt v) else ub "signed integer overflow"
/-- A `long` result: faults on signed overflow. -/
def chkI64 (v : Int) : M Int64 :=
  if -9223372036854775808 ≤ v ∧ v < 9223372036854775808 then pure (Int64.ofInt v) else ub "signed integer overflow"
/-- `(int)u` for `unsigned u` (modulo 2^32). -/
def u2i (x : UInt32) : Int32 := Int32.ofInt (x.toNat : Int)
/-- `(unsigned)i` for `int i`. -/
def i2u (x : Int32) : UInt32 := x.toUInt32
/-- `(unsigned long)i` for `int i` (sign extension, then modulo 2^64). -/
def i2ul (x : Int32) : UInt64 := x.toInt64.toUInt64

/-! ## The default allocator through the stream (`ZALLOC`, `ZFREE`) -/

/-- `ZALLOC(strm, items, size)` for a byte block: calls `strm->zalloc`. Only `zcalloc` is modelled. -/
def ZALLOCB (strm : ZStreamPtr) (items size : UInt32) : M BPtr := do
  let z ← ldZStream strm
  match z.zalloc with
  | .fn "zcalloc" => Zlib.Zutil.zcalloc z.«opaque» items size
  | _ => ub "custom allocator not modelled"

/-- `ZALLOC(strm, 1, sizeof(struct inflate_state))`: uninitialised record (arbitrary integers, null pointers). -/
def ZALLOCS (strm : ZStreamPtr) : M InflateStatePtr := do
  let z ← ldZStream strm
  match z.zalloc with
  | .fn "zcalloc" => allocInflateState
  | _ => ub "custom allocator not modelled"

/-- `ZFREE(strm, addr)` for a byte block. -/
def ZFREEB (strm : ZStreamPtr) (p : BPtr) : M Unit := do
  let z ← ldZStream strm
  match z.zfree with
  | .fn "zcfree" => Zlib.Zutil.zcfree z.«opaque» p
  | _ => ub "custom allocator not modelled"

/-- `ZFREE(strm, state)` for an inflate state. -/
def ZFREES (strm : ZStreamPtr) (st : InflateStatePtr) : M Unit := do
  let z ← ldZStream strm
  match z.zfree with
  | .fn "zcfree" => freeInflateState st
  | _ => ub "custom allocator not modelled"

/-- A local array (`unsigned char hbuf[4]`): a writable block made at the declaration, with arbitrary content. It takes
no allocation call of the failure oracle (a local cannot fail to exist); it uses the runtime's block allocator. -/
def allocLocalB (n : Nat) : M BPtr := fun h =>
  allocBytes (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val)) h

/-- `strm->msg = (z_const char *)"..."`. -/
def setMsg (strm : ZStreamPtr) (s : String) : M Unit := do
  let p ← Zlib.Zutil.strLit s
  let z ← ldZStream strm
  stZStream strm { z with msg := p }

/-! ## Access to the state and the stream -/

/-- Read a field of `*st`. -/
def rdS {α : Type} (st : InflateStatePtr) (f : InflateState → α) : M α := do return f (← ldInflateState st)
/-- Update fields of `*st`. -/
def wrS (st : InflateStatePtr) (f : InflateState → InflateState) : M Unit := do
  let s ← ldInflateState st
  stInflateState st (f s)
/-- Read a field of `*strm`. -/
def rdZ {α : Type} (strm : ZStreamPtr) (f : ZStream → α) : M α := do return f (← ldZStream strm)
/-- Update fields of `*strm`. -/
def wrZ (strm : ZStreamPtr) (f : ZStream → ZStream) : M Unit := do
  let z ← ldZStream strm
  stZStream strm (f z)

/-- `state->lens` (a pointer to element 0 of the array field). -/
def lensP (st : InflateStatePtr) : WPtr := match st with | some (.tab i) => .ref (.istate_lens i) 0 | none => .null
/-- `state->work`. -/
def workP (st : InflateStatePtr) : WPtr := match st with | some (.tab i) => .ref (.istate_work i) 0 | none => .null
/-- `state->codes`. -/
def codesP (st : InflateStatePtr) : CodePtr := match st with | some (.tab i) => .ref (.istate_codes i) 0 | none => .null

/-- `static const unsigned short order[19]` -/
def order : Array UInt16 := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
/-- `order[i]`: faults outside the array. -/
def orderAt (i : UInt32) : M UInt16 :=
  match order[i.toNat]? with
  | some v => pure v
  | none => ub "order index outside its array"

/-! ## `inflateStateCheck` .. `inflatePrime` -/

/-- `local int inflateStateCheck(z_streamp strm)` -/
def inflateStateCheck (strm : ZStreamPtr) : M Int32 := do
  -- if (strm == Z_NULL || strm->zalloc == (alloc_func)0 || strm->zfree == (free_func)0) return 1;
  if strm == none then return 1
  let z ← ldZStream strm
  if z.zalloc == .null || z.zfree == .null then return 1
  -- state = (struct inflate_state FAR *)strm->state;
  let state ← castInflateState z.state
  -- if (state == Z_NULL || state->strm != strm || state->mode < HEAD || state->mode > SYNC) return 1;
  if state == none then return 1
  let s ← ldInflateState state
  if s.strm != strm || s.mode < HEAD || s.mode > SYNC then return 1
  return 0

/-- `int ZEXPORT inflateResetKeep(z_streamp strm)` -/
def inflateResetKeep (strm : ZStreamPtr) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let state ← castInflateState z.state
  -- strm->total_in = strm->total_out = state->total = 0;
  wrS state fun s => { s with total := 0 }
  -- strm->msg = Z_NULL; strm->data_type = 0;
  wrZ strm fun z => { z with total_out := 0, total_in := 0, msg := .null, data_type := 0 }
  -- if (state->wrap) strm->adler = state->wrap & 1;
  let s ← ldInflateState state
  if s.wrap != 0 then wrZ strm fun z => { z with adler := i2ul (s.wrap &&& 1) }
  -- state->mode = HEAD; last = 0; havedict = 0; flags = -1; dmax = 32768U; head = Z_NULL; hold = 0; bits = 0;
  -- state->lencode = state->distcode = state->next = state->codes;
  -- state->sane = 1; state->back = -1;
  wrS state fun s => { s with
    mode := HEAD, last := 0, havedict := 0, flags := -1, dmax := 32768, head := none,
    hold := 0, bits := 0, next := codesP state, distcode := codesP state, lencode := codesP state, sane := 1, back := -1 }
  return Z_OK

/-- `int ZEXPORT inflateReset(z_streamp strm)` -/
def inflateReset (strm : ZStreamPtr) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let state ← castInflateState z.state
  let s ← ldInflateState state
  -- if (state->wbits != state->reqbits) { if (state->window != Z_NULL) { ZFREE; window = Z_NULL; } wbits = reqbits; }
  if s.wbits != s.reqbits then
    if s.window != .null then
      ZFREEB strm s.window
      wrS state fun s => { s with window := .null }
    wrS state fun s => { s with wbits := s.reqbits }
  -- state->wrap = state->reqwrap; wsize = 0; whave = 0; wnext = 0;
  wrS state fun s => { s with wrap := s.reqwrap, wsize := 0, whave := 0, wnext := 0 }
  return (← inflateResetKeep strm)

/-- `int ZEXPORT inflateReset2(z_streamp strm, int windowBits)` -/
def inflateReset2 (strm : ZStreamPtr) (windowBits : Int32) : M Int32 := do
  -- if (inflateStateCheck(strm)) return Z_STREAM_ERROR;
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let state ← castInflateState z.state
  let mut windowBits := windowBits
  let mut wrap : Int32 := 0
  -- if (windowBits < 0) { if (windowBits < -15) return Z_STREAM_ERROR; wrap = 0; windowBits = -windowBits; }
  if windowBits < 0 then
    if windowBits < -15 then return Z_STREAM_ERROR
    wrap := 0
    windowBits ← chkI32 (-(windowBits.toInt))
  else
    -- wrap = (windowBits >> 4) + 5;
    wrap ← chkI32 ((windowBits >>> 4).toInt + 5)
    -- if (windowBits < 48) windowBits &= 15;
    if windowBits < 48 then windowBits := windowBits &&& 15
  -- if (windowBits && (windowBits < 8 || windowBits > 15)) return Z_STREAM_ERROR;
  if windowBits != 0 && (windowBits < 8 || windowBits > 15) then return Z_STREAM_ERROR
  -- if (state->window != Z_NULL && state->wbits != (unsigned)windowBits) { ZFREE; window = Z_NULL; }
  let s ← ldInflateState state
  if s.window != .null && s.wbits != i2u windowBits then
    ZFREEB strm s.window
    wrS state fun s => { s with window := .null }
  -- state->reqwrap = state->wrap = wrap; state->reqbits = state->wbits = (unsigned)windowBits;
  wrS state fun s => { s with wrap := wrap, reqwrap := wrap, wbits := i2u windowBits, reqbits := i2u windowBits }
  return (← inflateReset strm)

/-- `int ZEXPORT inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`
(`version` is a pointer to a NUL-terminated string; `sizeof(z_stream)` is 112) -/
def inflateInit2_ (strm : ZStreamPtr) (windowBits : Int32) (version : BPtr) (stream_size : Int32) : M Int32 := do
  -- if (version == Z_NULL || version[0] != ZLIB_VERSION[0] || stream_size != (int)(sizeof(z_stream))) return Z_VERSION_ERROR;
  if version == .null then return Z_VERSION_ERROR
  if (← index8 version 0) != 49 then return Z_VERSION_ERROR
  if stream_size != 112 then return Z_VERSION_ERROR
  -- if (strm == Z_NULL) return Z_STREAM_ERROR;
  if strm == none then return Z_STREAM_ERROR
  -- strm->msg = Z_NULL;
  wrZ strm fun z => { z with msg := .null }
  -- if (strm->zalloc == (alloc_func)0) { strm->zalloc = zcalloc; strm->opaque = (voidpf)0; }
  if (← rdZ strm (·.zalloc)) == .null then
    wrZ strm fun z => { z with zalloc := .fn "zcalloc", «opaque» := .null }
  -- if (strm->zfree == (free_func)0) strm->zfree = zcfree;
  if (← rdZ strm (·.zfree)) == .null then
    wrZ strm fun z => { z with zfree := .fn "zcfree" }
  -- state = (struct inflate_state FAR *)ZALLOC(strm, 1, sizeof(struct inflate_state));
  let state ← ZALLOCS strm
  -- if (state == Z_NULL) return Z_MEM_ERROR;
  if state == none then return Z_MEM_ERROR
  -- zmemzero(state, sizeof(struct inflate_state));
  stInflateState state (InflateState.zeroed)
  -- strm->state = (struct internal_state FAR *)state;
  wrZ strm fun z => { z with state := StateRef.ofInflateState state }
  -- state->strm = strm; state->window = Z_NULL; state->mode = HEAD;
  wrS state fun s => { s with strm := strm, window := .null, mode := HEAD }
  -- ret = inflateReset2(strm, windowBits);
  let ret ← inflateReset2 strm windowBits
  -- if (ret != Z_OK) { ZFREE(strm, state); strm->state = Z_NULL; }
  if ret != Z_OK then
    ZFREES strm state
    wrZ strm fun z => { z with state := none }
  return ret

/-- `int ZEXPORT inflateInit_(z_streamp strm, const char *version, int stream_size)` -/
def inflateInit_ (strm : ZStreamPtr) (version : BPtr) (stream_size : Int32) : M Int32 :=
  inflateInit2_ strm DEF_WBITS version stream_size

/-- `int ZEXPORT inflatePrime(z_streamp strm, int bits, int value)` -/
def inflatePrime (strm : ZStreamPtr) (bits : Int32) (value : Int32) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  -- if (bits == 0) return Z_OK;
  if bits == 0 then return Z_OK
  let z ← ldZStream strm
  let state ← castInflateState z.state
  -- if (bits < 0) { state->hold = 0; state->bits = 0; return Z_OK; }
  if bits < 0 then
    wrS state fun s => { s with hold := 0, bits := 0 }
    return Z_OK
  -- if (bits > 16 || state->bits + (uInt)bits > 32) return Z_STREAM_ERROR;
  let s ← ldInflateState state
  if bits > 16 || s.bits + i2u bits > 32 then return Z_STREAM_ERROR
  -- value &= (1L << bits) - 1;   (`long` arithmetic; bits is in 1..16)
  let m : Int64 := ((1 : Int64) <<< bits.toInt64) - 1
  let value : Int32 := (value.toInt64 &&& m).toInt32
  -- state->hold += (unsigned long)value << state->bits;
  let sh ← shl64 (i2ul value) s.bits
  -- state->bits += (uInt)bits;
  wrS state fun s => { s with hold := s.hold + sh, bits := s.bits + i2u bits }
  return Z_OK

/-- `local int updatewindow(z_streamp strm, const Bytef *end, unsigned copy)` -/
def updatewindow (strm : ZStreamPtr) (end_ : BPtr) (copy : UInt32) : M Int32 := do
  let z ← ldZStream strm
  let state ← castInflateState z.state
  let s ← ldInflateState state
  -- if (state->window == Z_NULL) { state->window = ZALLOC(strm, 1U << state->wbits, sizeof(unsigned char)); if (...== Z_NULL) return 1; }
  if s.window == .null then
    let w ← ZALLOCB strm (← shl32 1 s.wbits) 1
    wrS state fun s => { s with window := w }
    if w == .null then return 1
  -- if (state->wsize == 0) { state->wsize = 1U << state->wbits; state->wnext = 0; state->whave = 0; }
  let s ← ldInflateState state
  if s.wsize == 0 then
    let ws ← shl32 1 s.wbits
    wrS state fun s => { s with wsize := ws, wnext := 0, whave := 0 }
  let s ← ldInflateState state
  if copy >= s.wsize then
    -- zmemcpy(state->window, end - state->wsize, state->wsize); wnext = 0; whave = wsize;
    memcpyB s.window (← end_.add (-(s.wsize.toNat : Int))) s.wsize.toNat
    wrS state fun s => { s with wnext := 0, whave := s.wsize }
  else
    -- dist = state->wsize - state->wnext; if (dist > copy) dist = copy;
    let mut dist := s.wsize - s.wnext
    if dist > copy then dist := copy
    -- zmemcpy(state->window + state->wnext, end - copy, dist);
    memcpyB (← s.window.add (s.wnext.toNat : Int)) (← end_.add (-(copy.toNat : Int))) dist.toNat
    -- copy -= dist;
    let copy := copy - dist
    if copy != 0 then
      -- zmemcpy(state->window, end - copy, copy); state->wnext = copy; state->whave = state->wsize;
      memcpyB s.window (← end_.add (-(copy.toNat : Int))) copy.toNat
      wrS state fun s => { s with wnext := copy, whave := s.wsize }
    else
      -- state->wnext += dist; if (state->wnext == state->wsize) state->wnext = 0; if (state->whave < state->wsize) state->whave += dist;
      let mut wnext := s.wnext + dist
      if wnext == s.wsize then wnext := 0
      let mut whave := s.whave
      if whave < s.wsize then whave := whave + dist
      wrS state fun s => { s with wnext := wnext, whave := whave }
  return 0

/-! ## The registers of `inflate()` and the monad of its modes -/

/-- How a mode leaves other than by `break`: `goto inf_leave`, or `return v`. -/
inductive Ex where
  | leave
  | ret (v : Int32)

/-- The locals of `inflate()` (and of `inflateBack()`): `next put have left hold bits in out copy from here last len
ret`. `have` and `in` are keywords, so `have_` and `in_`; `out` is `out_` for symmetry. -/
structure IL where
  next : BPtr
  put : BPtr
  have_ : UInt32
  left : UInt32
  hold : UInt64
  bits : UInt32
  in_ : UInt32
  out_ : UInt32
  copy : UInt32
  from_ : BPtr
  here : Code
  last : Code
  len : UInt32
  ret : Int32

/-- The registers before the first assignment (the C leaves these uninitialised; see the file comment). -/
def IL.init : IL where
  next := .null
  put := .null
  have_ := 0
  left := 0
  hold := 0
  bits := 0
  in_ := 0
  out_ := 0
  copy := 0
  from_ := .null
  here := default
  last := default
  len := 0
  ret := 0

/-- The monad of a mode: the registers, `goto inf_leave` / `return` as an exception, and the heap. -/
abbrev X := ExceptT Ex (StateT IL M)

/-- Why a loop of `X` ended. -/
inductive Stop where
  | go
  | brk
  | ex (e : Ex)

/-- `while (cond) body` where `body` returns `true` for `break`. Built on the runtime's `cwhile`; the registers and the
reason for stopping are the loop-carried state, so a `goto` or `return` inside leaves with the registers it had. -/
def xwhileBrk (cond : X Bool) (body : X Bool) : X Unit :=
  ExceptT.mk (fun l0 => do
    let r ← cwhile (σ := IL × Stop)
      (fun (l, s) => match s with
        | .go => do
          let (r, l') ← StateT.run (ExceptT.run cond) l
          pure (match r with
            | .ok b => (b, (l', Stop.go))
            | .error e => (false, (l', Stop.ex e)))
        | s => pure (false, (l, s)))
      (fun (l, _) => do
        let (r, l') ← StateT.run (ExceptT.run body) l
        pure (match r with
          | .ok b => (l', if b then Stop.brk else Stop.go)
          | .error e => (l', Stop.ex e)))
      (l0, Stop.go)
    let (l, s) := r
    pure (match s with
      | .ex e => (Except.error e, l)
      | _ => (Except.ok (), l)))

/-- `while (cond) body` -/
def xwhile (cond : X Bool) (body : X Unit) : X Unit := xwhileBrk cond (do body; pure false)

/-- `do body while (cond)` -/
def xdoWhile (body : X Unit) (cond : X Bool) : X Unit := do
  body
  xwhile cond body

/-- `for (;;) body` where `body` returns `true` for `break`. -/
def xloopBrk (body : X Bool) : X Unit := xwhileBrk (pure true) body

/-- The information `inflate()` and its macros share. -/
structure Ctx where
  strm : ZStreamPtr
  st : InflateStatePtr
  hbuf : BPtr
  flush : Int32

/-! ## The macros of `inflate.c`, each one a `def` -/

/-- `LOAD()` -/
def LOAD (strm : ZStreamPtr) (st : InflateStatePtr) : X Unit := do
  let z ← ldZStream strm
  let s ← ldInflateState st
  modify fun l => { l with
    put := z.next_out, left := z.avail_out, next := z.next_in, have_ := z.avail_in,
    hold := s.hold, bits := s.bits }

/-- `RESTORE()` -/
def RESTORE (strm : ZStreamPtr) (st : InflateStatePtr) : X Unit := do
  let l ← get
  wrZ strm fun z => { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }
  wrS st fun s => { s with hold := l.hold, bits := l.bits }

/-- `INITBITS()` -/
def INITBITS : X Unit := modify fun l => { l with hold := 0, bits := 0 }

/-- `PULLBYTE()`: `goto inf_leave` if there is no input. -/
def PULLBYTE : X Unit := do
  let l ← get
  if l.have_ == 0 then throw Ex.leave
  -- have--;
  set { l with have_ := l.have_ - 1 }
  -- hold += (unsigned long)(*next++) << bits; bits += 8;
  let b ← load8 l.next
  let nx ← l.next.add 1
  let sh ← shl64 b.toUInt64 l.bits
  set { l with have_ := l.have_ - 1, next := nx, hold := l.hold + sh, bits := l.bits + 8 }

/-- `NEEDBITS(n)`: `while (bits < (unsigned)(n)) PULLBYTE();` -/
def NEEDBITS (n : UInt32) : X Unit :=
  xwhile (do return (← get).bits < n) PULLBYTE

/-- `BITS(n)`: `((unsigned)hold & ((1U << (n)) - 1))` -/
def BITS (n : UInt32) : X UInt32 := do
  let l ← get
  let m ← shl32 1 n
  return l.hold.toUInt32 &&& (m - 1)

/-- `DROPBITS(n)`: `hold >>= (n); bits -= (unsigned)(n);` -/
def DROPBITS (n : UInt32) : X Unit := do
  let l ← get
  let h ← shr64 l.hold n
  set { l with hold := h, bits := l.bits - n }

/-- `BYTEBITS()`: `hold >>= bits & 7; bits -= bits & 7;` -/
def BYTEBITS : X Unit := do
  let l ← get
  let h ← shr64 l.hold (l.bits &&& 7)
  set { l with hold := h, bits := l.bits - (l.bits &&& 7) }

/-- `ZSWAP32(q)` -/
def ZSWAP32 (q : UInt64) : UInt64 :=
  ((q >>> 24) &&& (0xff : UInt64)) + ((q >>> 8) &&& (0xff00 : UInt64)) + ((q &&& (0xff00 : UInt64)) <<< 8) + ((q &&& (0xff : UInt64)) <<< 24)

/-- `UPDATE_CHECK(check, buf, len)`: `(state->flags ? crc32(check, buf, len) : adler32(check, buf, len))` -/
def UPDATE_CHECK (st : InflateStatePtr) (check : UInt64) (buf : BPtr) (len : UInt32) : M UInt64 := do
  if (← rdS st (·.flags)) != 0 then crc32 check buf len else adler32 check buf len

/-- `CRC2(state->check, hold)` -/
def CRC2 (c : Ctx) : X Unit := do
  let l ← get
  -- hbuf[0] = (unsigned char)(word); hbuf[1] = (unsigned char)((word) >> 8);
  store8 c.hbuf l.hold.toUInt8
  store8 (← c.hbuf.add 1) (l.hold >>> 8).toUInt8
  -- check = crc32(check, hbuf, 2);
  let ck ← rdS c.st (·.check)
  let v ← crc32 ck c.hbuf 2
  wrS c.st fun s => { s with check := v }

/-- `CRC4(state->check, hold)` -/
def CRC4 (c : Ctx) : X Unit := do
  let l ← get
  store8 c.hbuf l.hold.toUInt8
  store8 (← c.hbuf.add 1) (l.hold >>> 8).toUInt8
  store8 (← c.hbuf.add 2) (l.hold >>> 16).toUInt8
  store8 (← c.hbuf.add 3) (l.hold >>> 24).toUInt8
  let ck ← rdS c.st (·.check)
  let v ← crc32 ck c.hbuf 4
  wrS c.st fun s => { s with check := v }

/-- `(state->flags & 0x0200) && (state->wrap & 4)` -/
def hcrcOn (st : InflateStatePtr) : M Bool := do
  let s ← ldInflateState st
  return (s.flags &&& 0x0200) != 0 && (s.wrap &&& 4) != 0

/-- `state->mode = m;` -/
def setMode (st : InflateStatePtr) (m : UInt32) : M Unit := wrS st fun s => { s with mode := m }

/-- `strm->msg = "..."; state->mode = BAD;` -/
def badMode (c : Ctx) (msg : String) : M Unit := do
  setMsg c.strm msg
  setMode c.st BAD

/-! ## The modes of `inflate()`, from the last to the first (a fall-through is a tail call) -/

/-- `case DONE:` -/
def inflate_DONE (_c : Ctx) : X Unit := do
  -- ret = Z_STREAM_END; goto inf_leave;
  modify fun l => { l with ret := Z_STREAM_END }
  throw Ex.leave

/-- `case LENGTH:` -/
def inflate_LENGTH (c : Ctx) : X Unit := do
  -- if (state->wrap && state->flags) {
  let s ← ldInflateState c.st
  if s.wrap != 0 && s.flags != 0 then
    NEEDBITS 32
    -- if ((state->wrap & 4) && hold != (state->total & 0xffffffff)) { ...BAD; break; }
    let s ← ldInflateState c.st
    let l ← get
    if (s.wrap &&& 4) != 0 && l.hold != (s.total &&& 0xffffffff) then
      badMode c "incorrect length check"
      return
    INITBITS
  -- state->mode = DONE; /* fallthrough */
  setMode c.st DONE
  inflate_DONE c

/-- `case CHECK:` -/
def inflate_CHECK (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  -- if (state->wrap) {
  if s.wrap != 0 then
    NEEDBITS 32
    -- out -= left;
    modify fun l => { l with out_ := l.out_ - l.left }
    let l ← get
    -- strm->total_out += out; state->total += out;
    wrZ c.strm fun z => { z with total_out := z.total_out + l.out_.toUInt64 }
    wrS c.st fun s => { s with total := s.total + l.out_.toUInt64 }
    -- if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, put - out, out);
    let s ← ldInflateState c.st
    if (s.wrap &&& 4) != 0 && l.out_ != 0 then
      let p ← l.put.add (-(l.out_.toNat : Int))
      let v ← UPDATE_CHECK c.st s.check p l.out_
      wrS c.st fun s => { s with check := v }
      wrZ c.strm fun z => { z with adler := v }
    -- out = left;
    modify fun l => { l with out_ := l.left }
    -- if ((state->wrap & 4) && ((state->flags ? hold : ZSWAP32(hold)) != state->check)) { ...BAD; break; }
    let s ← ldInflateState c.st
    let l ← get
    if (s.wrap &&& 4) != 0 && (if s.flags != 0 then l.hold else ZSWAP32 l.hold) != s.check then
      badMode c "incorrect data check"
      return
    INITBITS
  -- state->mode = LENGTH; /* fallthrough */
  setMode c.st LENGTH
  inflate_LENGTH c

/-- `case LIT:` -/
def inflate_LIT (c : Ctx) : X Unit := do
  let l ← get
  -- if (left == 0) goto inf_leave;
  if l.left == 0 then throw Ex.leave
  -- *put++ = (unsigned char)(state->length);
  let s ← ldInflateState c.st
  store8 l.put s.length.toUInt8
  let p ← l.put.add 1
  -- left--; state->mode = LEN;
  set { l with put := p, left := l.left - 1 }
  setMode c.st LEN

/-- `case MATCH:` -/
def inflate_MATCH (c : Ctx) : X Unit := do
  let l ← get
  -- if (left == 0) goto inf_leave;
  if l.left == 0 then throw Ex.leave
  -- copy = out - left;
  let mut copy := l.out_ - l.left
  let mut from_ : BPtr := l.from_
  let s ← ldInflateState c.st
  -- if (state->offset > copy) { /* copy from window */
  if s.offset > copy then
    -- copy = state->offset - copy;
    copy := s.offset - copy
    -- if (copy > state->whave) { if (state->sane) { ...BAD; break; } }
    if copy > s.whave then
      if s.sane != 0 then
        badMode c "invalid distance too far back"
        return
    -- if (copy > state->wnext) { copy -= state->wnext; from = state->window + (state->wsize - copy); }
    if copy > s.wnext then
      copy := copy - s.wnext
      from_ ← s.window.add ((s.wsize - copy).toNat : Int)
    else
      -- else from = state->window + (state->wnext - copy);
      from_ ← s.window.add ((s.wnext - copy).toNat : Int)
    -- if (copy > state->length) copy = state->length;
    if copy > s.length then copy := s.length
  else
    -- from = put - state->offset; copy = state->length;
    from_ ← l.put.add (-(s.offset.toNat : Int))
    copy := s.length
  -- if (copy > left) copy = left;
  if copy > l.left then copy := l.left
  -- left -= copy; state->length -= copy;
  set { l with left := l.left - copy, copy := copy, from_ := from_ }
  wrS c.st fun s => { s with length := s.length - copy }
  -- do { *put++ = *from++; } while (--copy);
  xdoWhile
    (do
      let l ← get
      let b ← load8 l.from_
      store8 l.put b
      let p ← l.put.add 1
      let f ← l.from_.add 1
      set { l with put := p, from_ := f })
    (do
      let l ← get
      let n := l.copy - 1
      set { l with copy := n }
      return n != 0)
  -- if (state->length == 0) state->mode = LEN;
  if (← rdS c.st (·.length)) == 0 then setMode c.st LEN

/-- The bit-extraction part shared in spirit by `LENEXT` and `DISTEXT`: `if (state->extra) { NEEDBITS(state->extra); ...}`.
`case DISTEXT:` -/
def inflate_DISTEXT (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  -- if (state->extra) {
  if s.extra != 0 then
    NEEDBITS s.extra
    -- state->offset += BITS(state->extra);
    let b ← BITS s.extra
    wrS c.st fun s => { s with offset := s.offset + b }
    -- DROPBITS(state->extra);
    DROPBITS s.extra
    -- state->back += state->extra;   (`int += unsigned`: computed in unsigned, converted back)
    wrS c.st fun s => { s with back := u2i (i2u s.back + s.extra) }
  -- state->mode = MATCH; /* fallthrough */
  setMode c.st MATCH
  inflate_MATCH c

/-- The two-level table lookup `for (;;) { here = TABLE[BITS(bitsOfTable)]; if ((unsigned)(here.bits) <= bits) break; PULLBYTE(); }`.
`dist` selects `distcode`/`distbits`, else `lencode`/`lenbits`. -/
def lookup1 (c : Ctx) (dist : Bool) : X Unit :=
  xloopBrk (do
    let s ← ldInflateState c.st
    let tab := if dist then s.distcode else s.lencode
    let nb := if dist then s.distbits else s.lenbits
    let b ← BITS nb
    let here ← Ptr.index tab (b.toNat : Int)
    modify fun l => { l with here := here }
    if here.bits.toUInt32 <= (← get).bits then return true
    PULLBYTE
    return false)

/-- `for (;;) { here = TABLE[last.val + (BITS(last.bits + last.op) >> last.bits)]; if ((unsigned)(last.bits + here.bits) <= bits) break; PULLBYTE(); }` -/
def lookup2 (c : Ctx) (dist : Bool) : X Unit :=
  xloopBrk (do
    let s ← ldInflateState c.st
    let tab := if dist then s.distcode else s.lencode
    let last := (← get).last
    let b ← BITS (last.bits.toUInt32 + last.op.toUInt32)
    let sh ← shr32 b last.bits.toUInt32
    let here ← Ptr.index tab ((last.val.toUInt32 + sh).toNat : Int)
    modify fun l => { l with here := here }
    if (last.bits.toUInt32 + here.bits.toUInt32) <= (← get).bits then return true
    PULLBYTE
    return false)

/-- `case DIST:` -/
def inflate_DIST (c : Ctx) : X Unit := do
  lookup1 c true
  let here := (← get).here
  -- if ((here.op & 0xf0) == 0) {
  if (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c true
    let last := (← get).last
    DROPBITS last.bits.toUInt32
    let s ← ldInflateState c.st
    let bk ← chkI32 (s.back.toInt + last.bits.toNat)
    wrS c.st fun s => { s with back := bk }
  -- DROPBITS(here.bits); state->back += here.bits;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + here.bits.toNat)
  wrS c.st fun s => { s with back := bk }
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  -- state->offset = (unsigned)here.val; state->extra = (unsigned)(here.op) & 15; state->mode = DISTEXT;
  wrS c.st fun s => { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 }
  setMode c.st DISTEXT
  inflate_DISTEXT c

/-- `case LENEXT:` -/
def inflate_LENEXT (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  if s.extra != 0 then
    NEEDBITS s.extra
    -- state->length += BITS(state->extra);
    let b ← BITS s.extra
    wrS c.st fun s => { s with length := s.length + b }
    DROPBITS s.extra
    wrS c.st fun s => { s with back := u2i (i2u s.back + s.extra) }
  -- state->was = state->length; state->mode = DIST; /* fallthrough */
  wrS c.st fun s => { s with was := s.length, mode := DIST }
  inflate_DIST c

/-- `case LEN:` -/
def inflate_LEN (c : Ctx) : X Unit := do
  let l ← get
  -- if (have >= 6 && left >= 258 && bits < 8) { RESTORE(); inflate_fast(strm, out); LOAD(); ...; break; }
  if l.have_ >= 6 && l.left >= 258 && l.bits < 8 then
    RESTORE c.strm c.st
    inflate_fast c.strm l.out_
    LOAD c.strm c.st
    -- if (state->mode == TYPE) state->back = -1;
    if (← rdS c.st (·.mode)) == TYPE then wrS c.st fun s => { s with back := -1 }
    return
  -- state->back = 0;
  wrS c.st fun s => { s with back := 0 }
  lookup1 c false
  let here := (← get).here
  -- if (here.op && (here.op & 0xf0) == 0) {
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    let last := (← get).last
    DROPBITS last.bits.toUInt32
    let s ← ldInflateState c.st
    let bk ← chkI32 (s.back.toInt + last.bits.toNat)
    wrS c.st fun s => { s with back := bk }
  -- DROPBITS(here.bits); state->back += here.bits; state->length = (unsigned)here.val;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + here.bits.toNat)
  wrS c.st fun s => { s with back := bk, length := here.val.toUInt32 }
  -- if ((int)(here.op) == 0) { state->mode = LIT; break; }
  if here.op.toNat == 0 then
    setMode c.st LIT
    return
  -- if (here.op & 32) { state->back = -1; state->mode = TYPE; break; }
  if (here.op &&& 32) != 0 then
    wrS c.st fun s => { s with back := -1, mode := TYPE }
    return
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  -- state->extra = (unsigned)(here.op) & 15; state->mode = LENEXT; /* fallthrough */
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15, mode := LENEXT }
  inflate_LENEXT c

/-- `case LEN_:` -/
def inflate_LEN_ (c : Ctx) : X Unit := do
  setMode c.st LEN
  inflate_LEN c

/-- `case CODELENS:` -/
def inflate_CODELENS (c : Ctx) : X Unit := do
  -- while (state->have < state->nlen + state->ndist) {
  xwhileBrk
    (do let s ← ldInflateState c.st; return s.have < s.nlen + s.ndist)
    (do
      lookup1 c false
      let here := (← get).here
      -- if (here.val < 16) { DROPBITS(here.bits); state->lens[state->have++] = here.val; }
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let s ← ldInflateState c.st
        Ptr.store (← (lensP c.st).add (s.have.toNat : Int)) here.val
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        return false
      else
        if here.val == 16 then
          NEEDBITS (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          -- if (state->have == 0) { "invalid bit length repeat"; BAD; break; }
          let s ← ldInflateState c.st
          if s.«have» == 0 then
            badMode c "invalid bit length repeat"
            return true
          -- len = state->lens[state->have - 1]; copy = 3 + BITS(2); DROPBITS(2);
          let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
          let b ← BITS 2
          modify fun l => { l with len := v.toUInt32, copy := 3 + b }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          let b ← BITS 3
          modify fun l => { l with len := 0, copy := 3 + b }
          DROPBITS 3
        else
          NEEDBITS (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          let b ← BITS 7
          modify fun l => { l with len := 0, copy := 11 + b }
          DROPBITS 7
        -- if (state->have + copy > state->nlen + state->ndist) { "invalid bit length repeat"; BAD; break; }
        let s ← ldInflateState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          badMode c "invalid bit length repeat"
          return true
        -- while (copy--) state->lens[state->have++] = (unsigned short)len;
        xwhile
          (do
            let l ← get
            set { l with copy := l.copy - 1 }
            return l.copy != 0)
          (do
            let s ← ldInflateState c.st
            Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) (← get).len.toUInt16
            wrS c.st fun s => { s with «have» := s.«have» + 1 })
        return false)
  -- if (state->mode == BAD) break;
  if (← rdS c.st (·.mode)) == BAD then return
  -- if (state->lens[256] == 0) { "invalid code -- missing end-of-block"; BAD; break; }
  if (← Ptr.index (lensP c.st) 256) == (0 : UInt16) then
    badMode c "invalid code -- missing end-of-block"
    return
  -- state->next = state->codes; state->lencode = (const code FAR *)(state->next); state->lenbits = 9;
  wrS c.st fun s => { s with next := codesP c.st, lencode := codesP c.st, lenbits := 9 }
  -- ret = inflate_table(LENS, state->lens, state->nlen, &(state->next), &(state->lenbits), state->work);
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table LENS (lensP c.st) s.nlen s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  -- if (ret) { "invalid literal/lengths set"; BAD; break; }
  if r != 0 then
    badMode c "invalid literal/lengths set"
    return
  -- state->distcode = (const code FAR *)(state->next); state->distbits = 6;
  wrS c.st fun s => { s with distcode := s.next, distbits := 6 }
  -- ret = inflate_table(DISTS, state->lens + state->nlen, state->ndist, &(state->next), &(state->distbits), state->work);
  let s ← ldInflateState c.st
  let (r, nx, db) ← inflate_table DISTS (← (lensP c.st).add (s.nlen.toNat : Int)) s.ndist s.next s.distbits (workP c.st)
  wrS c.st fun s => { s with next := nx, distbits := db }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid distances set"
    return
  -- state->mode = LEN_; if (flush == Z_TREES) goto inf_leave; /* fallthrough */
  setMode c.st LEN_
  if c.flush == Z_TREES then throw Ex.leave
  inflate_LEN_ c

/-- `case LENLENS:` -/
def inflate_LENLENS (c : Ctx) : X Unit := do
  -- while (state->have < state->ncode) { NEEDBITS(3); state->lens[order[state->have++]] = (unsigned short)BITS(3); DROPBITS(3); }
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < s.ncode)
    (do
      NEEDBITS 3
      let s ← ldInflateState c.st
      wrS c.st fun s => { s with «have» := s.«have» + 1 }
      let o ← orderAt s.«have»
      let b ← BITS 3
      Ptr.store (← (lensP c.st).add (o.toNat : Int)) b.toUInt16
      DROPBITS 3)
  -- while (state->have < 19) state->lens[order[state->have++]] = 0;
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < 19)
    (do
      let s ← ldInflateState c.st
      wrS c.st fun s => { s with «have» := s.«have» + 1 }
      let o ← orderAt s.«have»
      Ptr.store (← (lensP c.st).add (o.toNat : Int)) (0 : UInt16))
  -- state->next = state->codes; state->lencode = state->distcode = (const code FAR *)(state->next); state->lenbits = 7;
  wrS c.st fun s => { s with next := codesP c.st, distcode := codesP c.st, lencode := codesP c.st, lenbits := 7 }
  -- ret = inflate_table(CODES, state->lens, 19, &(state->next), &(state->lenbits), state->work);
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table CODES (lensP c.st) 19 s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  -- if (ret) { "invalid code lengths set"; BAD; break; }
  if r != 0 then
    badMode c "invalid code lengths set"
    return
  -- state->have = 0; state->mode = CODELENS; /* fallthrough */
  wrS c.st fun s => { s with «have» := 0, mode := CODELENS }
  inflate_CODELENS c

/-- `case TABLE:` -/
def inflate_TABLE (c : Ctx) : X Unit := do
  NEEDBITS 14
  -- state->nlen = BITS(5) + 257; DROPBITS(5);
  let b ← BITS 5
  wrS c.st fun s => { s with nlen := b + 257 }
  DROPBITS 5
  -- state->ndist = BITS(5) + 1; DROPBITS(5);
  let b ← BITS 5
  wrS c.st fun s => { s with ndist := b + 1 }
  DROPBITS 5
  -- state->ncode = BITS(4) + 4; DROPBITS(4);
  let b ← BITS 4
  wrS c.st fun s => { s with ncode := b + 4 }
  DROPBITS 4
  -- if (state->nlen > 286 || state->ndist > 30) { "too many length or distance symbols"; BAD; break; }
  let s ← ldInflateState c.st
  if s.nlen > 286 || s.ndist > 30 then
    badMode c "too many length or distance symbols"
    return
  -- state->have = 0; state->mode = LENLENS; /* fallthrough */
  wrS c.st fun s => { s with «have» := 0, mode := LENLENS }
  inflate_LENLENS c

/-- `case COPY:` -/
def inflate_COPY (c : Ctx) : X Unit := do
  -- copy = state->length;
  let s ← ldInflateState c.st
  let mut copy := s.length
  -- if (copy) {
  if copy != 0 then
    let l ← get
    if copy > l.have_ then copy := l.have_
    if copy > l.left then copy := l.left
    -- if (copy == 0) goto inf_leave;
    if copy == 0 then
      set { l with copy := copy }
      throw Ex.leave
    -- zmemcpy(put, next, copy);
    memcpyB l.put l.next copy.toNat
    -- have -= copy; next += copy; left -= copy; put += copy; state->length -= copy;
    let nx ← l.next.add (copy.toNat : Int)
    let pt ← l.put.add (copy.toNat : Int)
    set { l with copy := copy, have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
    wrS c.st fun s => { s with length := s.length - copy }
    return
  modify fun l => { l with copy := copy }
  -- state->mode = TYPE; break;
  setMode c.st TYPE

/-- `case COPY_:` -/
def inflate_COPY_ (c : Ctx) : X Unit := do
  setMode c.st COPY
  inflate_COPY c

/-- `case STORED:` -/
def inflate_STORED (c : Ctx) : X Unit := do
  BYTEBITS
  NEEDBITS 32
  let l ← get
  -- if ((hold & 0xffff) != ((hold >> 16) ^ 0xffff)) { "invalid stored block lengths"; BAD; break; }
  if (l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64)) then
    badMode c "invalid stored block lengths"
    return
  -- state->length = (unsigned)hold & 0xffff;
  wrS c.st fun s => { s with length := l.hold.toUInt32 &&& 0xffff }
  INITBITS
  -- state->mode = COPY_; if (flush == Z_TREES) goto inf_leave; /* fallthrough */
  setMode c.st COPY_
  if c.flush == Z_TREES then throw Ex.leave
  inflate_COPY_ c

/-- `case TYPEDO:` -/
def inflate_TYPEDO (c : Ctx) : X Unit := do
  -- if (state->last) { BYTEBITS(); state->mode = CHECK; break; }
  if (← rdS c.st (·.last)) != 0 then
    BYTEBITS
    setMode c.st CHECK
    return
  NEEDBITS 3
  -- state->last = BITS(1); DROPBITS(1);
  let b ← BITS 1
  wrS c.st fun s => { s with last := u2i b }
  DROPBITS 1
  -- switch (BITS(2)) {
  match (← BITS 2) with
  | 0 => setMode c.st STORED
  | 1 =>
    inflate_fixed c.st
    setMode c.st LEN_
    -- if (flush == Z_TREES) { DROPBITS(2); goto inf_leave; }
    if c.flush == Z_TREES then
      DROPBITS 2
      throw Ex.leave
  | 2 => setMode c.st TABLE
  | _ => badMode c "invalid block type"
  -- DROPBITS(2); break;
  DROPBITS 2

/-- `case TYPE:` -/
def inflate_TYPE (c : Ctx) : X Unit := do
  -- if (flush == Z_BLOCK || flush == Z_TREES) goto inf_leave; /* fallthrough, the mode is not written */
  if c.flush == Z_BLOCK || c.flush == Z_TREES then throw Ex.leave
  inflate_TYPEDO c

/-- `case DICT:` -/
def inflate_DICT (c : Ctx) : X Unit := do
  -- if (state->havedict == 0) { RESTORE(); strm->total_in += in - strm->avail_in; return Z_NEED_DICT; }
  if (← rdS c.st (·.havedict)) == 0 then
    RESTORE c.strm c.st
    let l ← get
    wrZ c.strm fun z => { z with total_in := z.total_in + (l.in_ - z.avail_in).toUInt64 }
    throw (Ex.ret Z_NEED_DICT)
  -- strm->adler = state->check = adler32(0L, Z_NULL, 0);
  let v ← adler32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  -- state->mode = TYPE; /* fallthrough */
  setMode c.st TYPE
  inflate_TYPE c

/-- `case DICTID:` -/
def inflate_DICTID (c : Ctx) : X Unit := do
  NEEDBITS 32
  -- strm->adler = state->check = ZSWAP32(hold);
  let v := ZSWAP32 (← get).hold
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  INITBITS
  setMode c.st DICT
  inflate_DICT c

/-- `case HCRC:` -/
def inflate_HCRC (c : Ctx) : X Unit := do
  -- if (state->flags & 0x0200) {
  if ((← rdS c.st (·.flags)) &&& 0x0200) != 0 then
    NEEDBITS 16
    let s ← ldInflateState c.st
    -- if ((state->wrap & 4) && hold != (state->check & 0xffff)) { "header crc mismatch"; BAD; break; }
    if (s.wrap &&& 4) != 0 && (← get).hold != (s.check &&& 0xffff) then
      badMode c "header crc mismatch"
      return
    INITBITS
  -- if (state->head != Z_NULL) { state->head->hcrc = (int)((state->flags >> 9) & 1); state->head->done = 1; }
  let s ← ldInflateState c.st
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with hcrc := (s.flags >>> 9) &&& 1, done := 1 }
  -- strm->adler = state->check = crc32(0L, Z_NULL, 0);
  let v ← crc32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  -- state->mode = TYPE; break;
  setMode c.st TYPE

/-- `case COMMENT:` -/
def inflate_COMMENT (c : Ctx) : X Unit := do
  -- if (state->flags & 0x1000) {
  if ((← rdS c.st (·.flags)) &&& 0x1000) != 0 then
    -- if (have == 0) goto inf_leave; copy = 0;
    if (← get).have_ == 0 then throw Ex.leave
    modify fun l => { l with copy := 0 }
    -- do { len = (unsigned)(next[copy++]); if (head && head->comment && length < comm_max) head->comment[length++] = (Bytef)len; } while (len && copy < have);
    xdoWhile
      (do
        let l ← get
        let b ← index8 l.next l.copy.toNat
        set { l with len := b.toUInt32, copy := l.copy + 1 }
        let s ← ldInflateState c.st
        if s.head != none then
          let g ← ldGzHeader s.head
          if g.comment != .null && s.length < g.comm_max then
            store8 (← g.comment.add (s.length.toNat : Int)) b
            wrS c.st fun s => { s with length := s.length + 1 })
      (do let l ← get; return l.len != 0 && l.copy < l.have_)
    -- if ((state->flags & 0x0200) && (state->wrap & 4)) state->check = crc32(state->check, next, copy);
    if ← hcrcOn c.st then
      let l ← get
      let v ← crc32 (← rdS c.st (·.check)) l.next l.copy
      wrS c.st fun s => { s with check := v }
    -- have -= copy; next += copy; if (len) goto inf_leave;
    let l ← get
    let nx ← l.next.add (l.copy.toNat : Int)
    set { l with have_ := l.have_ - l.copy, next := nx }
    if l.len != 0 then throw Ex.leave
  else
    -- else if (state->head != Z_NULL) state->head->comment = Z_NULL;
    let s ← ldInflateState c.st
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with comment := .null }
  -- state->mode = HCRC; /* fallthrough */
  setMode c.st HCRC
  inflate_HCRC c

/-- `case NAME:` -/
def inflate_NAME (c : Ctx) : X Unit := do
  if ((← rdS c.st (·.flags)) &&& 0x0800) != 0 then
    if (← get).have_ == 0 then throw Ex.leave
    modify fun l => { l with copy := 0 }
    xdoWhile
      (do
        let l ← get
        let b ← index8 l.next l.copy.toNat
        set { l with len := b.toUInt32, copy := l.copy + 1 }
        let s ← ldInflateState c.st
        if s.head != none then
          let g ← ldGzHeader s.head
          if g.name != .null && s.length < g.name_max then
            store8 (← g.name.add (s.length.toNat : Int)) b
            wrS c.st fun s => { s with length := s.length + 1 })
      (do let l ← get; return l.len != 0 && l.copy < l.have_)
    if ← hcrcOn c.st then
      let l ← get
      let v ← crc32 (← rdS c.st (·.check)) l.next l.copy
      wrS c.st fun s => { s with check := v }
    let l ← get
    let nx ← l.next.add (l.copy.toNat : Int)
    set { l with have_ := l.have_ - l.copy, next := nx }
    if l.len != 0 then throw Ex.leave
  else
    -- else if (state->head != Z_NULL) state->head->name = Z_NULL;
    let s ← ldInflateState c.st
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with name := .null }
  -- state->length = 0; state->mode = COMMENT; /* fallthrough */
  wrS c.st fun s => { s with length := 0, mode := COMMENT }
  inflate_COMMENT c

/-- `case EXTRA:` -/
def inflate_EXTRA (c : Ctx) : X Unit := do
  -- if (state->flags & 0x0400) {
  if ((← rdS c.st (·.flags)) &&& 0x0400) != 0 then
    -- copy = state->length; if (copy > have) copy = have;
    let s ← ldInflateState c.st
    let l ← get
    let copy := if s.length > l.have_ then l.have_ else s.length
    set { l with copy := copy }
    -- if (copy) {
    if copy != 0 then
      -- if (state->head != Z_NULL && state->head->extra != Z_NULL && (len = state->head->extra_len - state->length) < state->head->extra_max) {
      if s.head != none then
        let g ← ldGzHeader s.head
        if g.extra != .null then
          let len := g.extra_len - s.length
          modify fun l => { l with len := len }
          if len < g.extra_max then
            -- zmemcpy(state->head->extra + len, next, len + copy > extra_max ? extra_max - len : copy);
            let n := if len + copy > g.extra_max then g.extra_max - len else copy
            memcpyB (← g.extra.add (len.toNat : Int)) (← get).next n.toNat
      -- if ((state->flags & 0x0200) && (state->wrap & 4)) state->check = crc32(state->check, next, copy);
      if ← hcrcOn c.st then
        let v ← crc32 (← rdS c.st (·.check)) (← get).next copy
        wrS c.st fun s => { s with check := v }
      -- have -= copy; next += copy; state->length -= copy;
      let l ← get
      let nx ← l.next.add (copy.toNat : Int)
      set { l with have_ := l.have_ - copy, next := nx }
      wrS c.st fun s => { s with length := s.length - copy }
    -- if (state->length) goto inf_leave;
    if (← rdS c.st (·.length)) != 0 then throw Ex.leave
  -- state->length = 0; state->mode = NAME; /* fallthrough */
  wrS c.st fun s => { s with length := 0, mode := NAME }
  inflate_NAME c

/-- `case EXLEN:` -/
def inflate_EXLEN (c : Ctx) : X Unit := do
  let s ← ldInflateState c.st
  -- if (state->flags & 0x0400) {
  if (s.flags &&& 0x0400) != 0 then
    NEEDBITS 16
    let l ← get
    -- state->length = (unsigned)(hold);
    wrS c.st fun s => { s with length := l.hold.toUInt32 }
    -- if (state->head != Z_NULL) state->head->extra_len = (unsigned)hold;
    let s ← ldInflateState c.st
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with extra_len := l.hold.toUInt32 }
    -- if ((state->flags & 0x0200) && (state->wrap & 4)) CRC2(state->check, hold);
    if ← hcrcOn c.st then CRC2 c
    INITBITS
  else
    -- else if (state->head != Z_NULL) state->head->extra = Z_NULL;
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with extra := .null }
  -- state->mode = EXTRA; /* fallthrough */
  setMode c.st EXTRA
  inflate_EXTRA c

/-- `case OS:` -/
def inflate_OS (c : Ctx) : X Unit := do
  NEEDBITS 16
  let l ← get
  let s ← ldInflateState c.st
  -- if (state->head != Z_NULL) { state->head->xflags = (int)(hold & 0xff); state->head->os = (int)(hold >> 8); }
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with xflags := (l.hold &&& 0xff).toUInt32.toInt32, os := (l.hold >>> 8).toUInt32.toInt32 }
  if ← hcrcOn c.st then CRC2 c
  INITBITS
  setMode c.st EXLEN
  inflate_EXLEN c

/-- `case TIME:` -/
def inflate_TIME (c : Ctx) : X Unit := do
  NEEDBITS 32
  let l ← get
  let s ← ldInflateState c.st
  -- if (state->head != Z_NULL) state->head->time = hold;
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with time := l.hold }
  -- if ((state->flags & 0x0200) && (state->wrap & 4)) CRC4(state->check, hold);
  if ← hcrcOn c.st then CRC4 c
  INITBITS
  setMode c.st OS
  inflate_OS c

/-- `case FLAGS:` -/
def inflate_FLAGS (c : Ctx) : X Unit := do
  NEEDBITS 16
  let l ← get
  -- state->flags = (int)(hold);   (implementation-defined conversion: modulo 2^32)
  wrS c.st fun s => { s with flags := l.hold.toUInt32.toInt32 }
  let s ← ldInflateState c.st
  -- if ((state->flags & 0xff) != Z_DEFLATED) { "unknown compression method"; BAD; break; }
  if (s.flags &&& 0xff) != Z_DEFLATED then
    badMode c "unknown compression method"
    return
  -- if (state->flags & 0xe000) { "unknown header flags set"; BAD; break; }
  if (s.flags &&& 0xe000) != 0 then
    badMode c "unknown header flags set"
    return
  -- if (state->head != Z_NULL) state->head->text = (int)((hold >> 8) & 1);
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with text := ((l.hold >>> 8) &&& 1).toUInt32.toInt32 }
  -- if ((state->flags & 0x0200) && (state->wrap & 4)) CRC2(state->check, hold);
  if ← hcrcOn c.st then CRC2 c
  INITBITS
  setMode c.st TIME
  inflate_TIME c

/-- `case HEAD:` -/
def inflate_HEAD (c : Ctx) : X Unit := do
  -- if (state->wrap == 0) { state->mode = TYPEDO; break; }
  if (← rdS c.st (·.wrap)) == 0 then
    setMode c.st TYPEDO
    return
  NEEDBITS 16
  let l ← get
  let s ← ldInflateState c.st
  -- if ((state->wrap & 2) && hold == 0x8b1f) {  /* gzip header */
  if (s.wrap &&& 2) != 0 && l.hold == 0x8b1f then
    -- if (state->wbits == 0) state->wbits = 15;
    if s.wbits == 0 then wrS c.st fun s => { s with wbits := 15 }
    -- state->check = crc32(0L, Z_NULL, 0); CRC2(state->check, hold); INITBITS(); state->mode = FLAGS; break;
    let v ← crc32 0 .null 0
    wrS c.st fun s => { s with check := v }
    CRC2 c
    INITBITS
    setMode c.st FLAGS
    return
  -- if (state->head != Z_NULL) state->head->done = -1;
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with done := -1 }
  -- if (!(state->wrap & 1) || ((BITS(8) << 8) + (hold >> 8)) % 31) { "incorrect header check"; BAD; break; }
  let b8 ← BITS 8
  if (s.wrap &&& 1) == 0 || ((b8 <<< 8).toUInt64 + (l.hold >>> 8)) % 31 != 0 then
    badMode c "incorrect header check"
    return
  -- if (BITS(4) != Z_DEFLATED) { "unknown compression method"; BAD; break; }
  if (← BITS 4) != i2u Z_DEFLATED then
    badMode c "unknown compression method"
    return
  DROPBITS 4
  -- len = BITS(4) + 8;
  let len := (← BITS 4) + 8
  modify fun l => { l with len := len }
  -- if (len > 15 || (state->wbits != 0 && len > state->wbits)) { "invalid window size"; BAD; break; }
  let s ← ldInflateState c.st
  if len > 15 || (s.wbits != 0 && len > s.wbits) then
    badMode c "invalid window size"
    return
  -- if (state->wbits == 0) state->wbits = len;
  if s.wbits == 0 then wrS c.st fun s => { s with wbits := len }
  -- state->dmax = 1U << len; state->flags = 0;
  let dm ← shl32 1 len
  wrS c.st fun s => { s with dmax := dm, flags := 0 }
  -- strm->adler = state->check = adler32(0L, Z_NULL, 0);
  let v ← adler32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  -- state->mode = hold & 0x200 ? DICTID : TYPE; INITBITS(); break;
  let l ← get
  setMode c.st (if (l.hold &&& 0x200) != 0 then DICTID else TYPE)
  INITBITS

/-- The `switch (state->mode)`: the mode is read from the heap on every trip. `MEM` returns `Z_MEM_ERROR`; `SYNC` and
every other value return `Z_STREAM_ERROR`. -/
def inflate_dispatch (c : Ctx) : X Unit := do
  let m ← rdS c.st (·.mode)
  if m == HEAD then inflate_HEAD c
  else if m == FLAGS then inflate_FLAGS c
  else if m == TIME then inflate_TIME c
  else if m == OS then inflate_OS c
  else if m == EXLEN then inflate_EXLEN c
  else if m == EXTRA then inflate_EXTRA c
  else if m == NAME then inflate_NAME c
  else if m == COMMENT then inflate_COMMENT c
  else if m == HCRC then inflate_HCRC c
  else if m == DICTID then inflate_DICTID c
  else if m == DICT then inflate_DICT c
  else if m == TYPE then inflate_TYPE c
  else if m == TYPEDO then inflate_TYPEDO c
  else if m == STORED then inflate_STORED c
  else if m == COPY_ then inflate_COPY_ c
  else if m == COPY then inflate_COPY c
  else if m == TABLE then inflate_TABLE c
  else if m == LENLENS then inflate_LENLENS c
  else if m == CODELENS then inflate_CODELENS c
  else if m == LEN_ then inflate_LEN_ c
  else if m == LEN then inflate_LEN c
  else if m == LENEXT then inflate_LENEXT c
  else if m == DIST then inflate_DIST c
  else if m == DISTEXT then inflate_DISTEXT c
  else if m == MATCH then inflate_MATCH c
  else if m == LIT then inflate_LIT c
  else if m == CHECK then inflate_CHECK c
  else if m == LENGTH then inflate_LENGTH c
  else if m == DONE then inflate_DONE c
  else if m == BAD then
    -- case BAD: ret = Z_DATA_ERROR; goto inf_leave;
    modify fun l => { l with ret := Z_DATA_ERROR }
    throw Ex.leave
  else if m == MEM then throw (Ex.ret Z_MEM_ERROR)
  else throw (Ex.ret Z_STREAM_ERROR)

/-- Everything of `inflate()` from `LOAD()` to the end of `for (;;) switch`. -/
def inflate_run (c : Ctx) : X Unit := do
  -- if (state->mode == TYPE) state->mode = TYPEDO;      /* skip check */
  if (← rdS c.st (·.mode)) == TYPE then setMode c.st TYPEDO
  LOAD c.strm c.st
  -- in = have; out = left; ret = Z_OK;
  modify fun l => { l with in_ := l.have_, out_ := l.left, ret := Z_OK }
  -- for (;;) switch (state->mode) { ... }
  xwhile (pure true) (inflate_dispatch c)

/-- `inf_leave:` and what follows it (`RESTORE()` .. `return ret`), with the registers `l` at the `goto`. -/
def inflate_leave (c : Ctx) (l : IL) : M Int32 := do
  -- RESTORE();
  wrZ c.strm fun z => { z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_ }
  wrS c.st fun s => { s with hold := l.hold, bits := l.bits }
  let z ← ldZStream c.strm
  let s ← ldInflateState c.st
  -- if (state->wsize || (out != strm->avail_out && state->mode < BAD && (state->mode < CHECK || flush != Z_FINISH)))
  --     if (updatewindow(strm, strm->next_out, out - strm->avail_out)) { state->mode = MEM; return Z_MEM_ERROR; }
  if s.wsize != 0 || (l.out_ != z.avail_out && s.mode < BAD && (s.mode < CHECK || c.flush != Z_FINISH)) then
    if (← updatewindow c.strm z.next_out (l.out_ - z.avail_out)) != 0 then
      setMode c.st MEM
      return Z_MEM_ERROR
  -- in -= strm->avail_in; out -= strm->avail_out;
  let in_ := l.in_ - z.avail_in
  let out_ := l.out_ - z.avail_out
  -- strm->total_in += in; strm->total_out += out; state->total += out;
  wrZ c.strm fun z => { z with total_in := z.total_in + in_.toUInt64, total_out := z.total_out + out_.toUInt64 }
  wrS c.st fun s => { s with total := s.total + out_.toUInt64 }
  -- if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, strm->next_out - out, out);
  let s ← ldInflateState c.st
  if (s.wrap &&& 4) != 0 && out_ != 0 then
    let p ← z.next_out.add (-(out_.toNat : Int))
    let v ← UPDATE_CHECK c.st s.check p out_
    wrS c.st fun s => { s with check := v }
    wrZ c.strm fun z => { z with adler := v }
  -- strm->data_type = (int)state->bits + (state->last ? 64 : 0) + (state->mode == TYPE ? 128 : 0) +
  --                   (state->mode == LEN_ || state->mode == COPY_ ? 256 : 0);
  let s ← ldInflateState c.st
  let dt ← chkI32 ((u2i s.bits).toInt + (if s.last != 0 then 64 else 0) + (if s.mode == TYPE then 128 else 0) +
    (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0))
  wrZ c.strm fun z => { z with data_type := dt }
  -- if (((in == 0 && out == 0) || flush == Z_FINISH) && ret == Z_OK) ret = Z_BUF_ERROR;
  let mut ret := l.ret
  if ((in_ == 0 && out_ == 0) || c.flush == Z_FINISH) && ret == Z_OK then ret := Z_BUF_ERROR
  return ret

/-- `int ZEXPORT inflate(z_streamp strm, int flush)` -/
def inflate (strm : ZStreamPtr) (flush : Int32) : M Int32 := do
  -- unsigned char hbuf[4];
  let hbuf ← allocLocalB 4
  let r ← (do
    -- if (inflateStateCheck(strm) || strm->next_out == Z_NULL || (strm->next_in == Z_NULL && strm->avail_in != 0)) return Z_STREAM_ERROR;
    if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
    let z ← ldZStream strm
    if z.next_out == .null || (z.next_in == .null && z.avail_in != 0) then return Z_STREAM_ERROR
    -- state = (struct inflate_state FAR *)strm->state;
    let st ← castInflateState z.state
    let c : Ctx := { strm, st, hbuf, flush }
    let (r, l) ← StateT.run (ExceptT.run (inflate_run c)) IL.init
    match r with
    | .error (.ret v) => return v
    | _ => inflate_leave c l)
  freeB hbuf
  return r

/-- `int ZEXPORT inflateEnd(z_streamp strm)` -/
def inflateEnd (strm : ZStreamPtr) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let st ← castInflateState z.state
  -- if (state->window != Z_NULL) ZFREE(strm, state->window);
  let s ← ldInflateState st
  if s.window != .null then ZFREEB strm s.window
  -- ZFREE(strm, strm->state); strm->state = Z_NULL;
  ZFREES strm st
  wrZ strm fun z => { z with state := none }
  return Z_OK

/-- `int ZEXPORT inflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`.
`dictLength` is the value of `*dictLength` (`none` for `NULL`); the second result is `*dictLength` afterwards. -/
def inflateGetDictionary (strm : ZStreamPtr) (dictionary : BPtr) (dictLength : Option UInt32) :
    M (Int32 × Option UInt32) := do
  if (← inflateStateCheck strm) != 0 then return (Z_STREAM_ERROR, dictLength)
  let z ← ldZStream strm
  let st ← castInflateState z.state
  let s ← ldInflateState st
  -- if (state->whave && dictionary != Z_NULL) {
  if s.whave != 0 && dictionary != .null then
    -- zmemcpy(dictionary, state->window + state->wnext, state->whave - state->wnext);
    memcpyB dictionary (← s.window.add (s.wnext.toNat : Int)) (s.whave - s.wnext).toNat
    -- zmemcpy(dictionary + state->whave - state->wnext, state->window, state->wnext);
    let d1 ← dictionary.add (s.whave.toNat : Int)
    let d2 ← d1.add (-(s.wnext.toNat : Int))
    memcpyB d2 s.window s.wnext.toNat
  -- if (dictLength != Z_NULL) *dictLength = state->whave;
  match dictLength with
  | some _ => return (Z_OK, some s.whave)
  | none => return (Z_OK, none)

/-- `int ZEXPORT inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)` -/
def inflateSetDictionary (strm : ZStreamPtr) (dictionary : BPtr) (dictLength : UInt32) : M Int32 := do
  -- if (inflateStateCheck(strm) || dictionary == Z_NULL) return Z_STREAM_ERROR;
  if (← inflateStateCheck strm) != 0 || dictionary == .null then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let st ← castInflateState z.state
  let s ← ldInflateState st
  -- if (state->wrap != 0 && state->mode != DICT) return Z_STREAM_ERROR;
  if s.wrap != 0 && s.mode != DICT then return Z_STREAM_ERROR
  -- if (state->mode == DICT) { dictid = adler32(0L, Z_NULL, 0); dictid = adler32(dictid, dictionary, dictLength); if (dictid != state->check) return Z_DATA_ERROR; }
  if s.mode == DICT then
    let dictid ← adler32 0 .null 0
    let dictid ← adler32 dictid dictionary dictLength
    if dictid != s.check then return Z_DATA_ERROR
  -- ret = updatewindow(strm, dictionary + dictLength, dictLength);
  let ret ← updatewindow strm (← dictionary.add (dictLength.toNat : Int)) dictLength
  -- if (ret) { state->mode = MEM; return Z_MEM_ERROR; }
  if ret != 0 then
    setMode st MEM
    return Z_MEM_ERROR
  -- state->havedict = 1;
  wrS st fun s => { s with havedict := 1 }
  return Z_OK

/-- `int ZEXPORT inflateGetHeader(z_streamp strm, gz_headerp head)` -/
def inflateGetHeader (strm : ZStreamPtr) (head : GzHeaderPtr) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let st ← castInflateState z.state
  -- if ((state->wrap & 2) == 0) return Z_STREAM_ERROR;
  if ((← rdS st (·.wrap)) &&& 2) == 0 then return Z_STREAM_ERROR
  -- state->head = head; head->done = 0;
  wrS st fun s => { s with head := head }
  let g ← ldGzHeader head
  stGzHeader head { g with done := 0 }
  return Z_OK

/-- `local unsigned syncsearch(unsigned FAR *have, const unsigned char FAR *buf, unsigned len)`.
`have` is the value of `*have`; the result is (return value, `*have` afterwards). -/
def syncsearch (have_ : UInt32) (buf : BPtr) (len : UInt32) : M (UInt32 × UInt32) := do
  -- got = *have; next = 0;
  let (next, got) ← cwhile (σ := UInt32 × UInt32)
    -- while (next < len && got < 4) {
    (fun (next, got) => pure (next < len && got < 4, (next, got)))
    (fun (next, got) => do
      let b ← index8 buf next.toNat
      -- if ((int)(buf[next]) == (got < 2 ? 0 : 0xff)) got++; else if (buf[next]) got = 0; else got = 4 - got;
      let got := if b.toNat == (if got < 2 then 0 else 0xff) then got + 1 else if b != 0 then 0 else 4 - got
      -- next++;
      pure (next + 1, got))
    (0, have_)
  -- *have = got; return next;
  return (next, got)

/-- `int ZEXPORT inflateSync(z_streamp strm)` -/
def inflateSync (strm : ZStreamPtr) : M Int32 := do
  -- unsigned char buf[4];
  let buf ← allocLocalB 4
  let r ← (do
    if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
    let z ← ldZStream strm
    let st ← castInflateState z.state
    let s ← ldInflateState st
    -- if (strm->avail_in == 0 && state->bits < 8) return Z_BUF_ERROR;
    if z.avail_in == 0 && s.bits < 8 then return Z_BUF_ERROR
    -- if (state->mode != SYNC) {
    if s.mode != SYNC then
      -- state->mode = SYNC; state->hold >>= state->bits & 7; state->bits -= state->bits & 7;
      let h ← shr64 s.hold (s.bits &&& 7)
      wrS st fun s => { s with mode := SYNC, hold := h, bits := s.bits - (s.bits &&& 7) }
      -- len = 0; while (state->bits >= 8) { buf[len++] = (unsigned char)(state->hold); state->hold >>= 8; state->bits -= 8; }
      let len ← cwhile (σ := UInt32)
        (fun len => do return ((← rdS st (·.bits)) >= 8, len))
        (fun len => do
          let s ← ldInflateState st
          store8 (← buf.add (len.toNat : Int)) s.hold.toUInt8
          wrS st fun s => { s with hold := s.hold >>> 8, bits := s.bits - 8 }
          pure (len + 1))
        0
      -- state->have = 0; syncsearch(&(state->have), buf, len);
      wrS st fun s => { s with «have» := 0 }
      let (_, hv) ← syncsearch 0 buf len
      wrS st fun s => { s with «have» := hv }
    -- len = syncsearch(&(state->have), strm->next_in, strm->avail_in);
    let z ← ldZStream strm
    let (len, hv) ← syncsearch (← rdS st (·.«have»)) z.next_in z.avail_in
    wrS st fun s => { s with «have» := hv }
    -- strm->avail_in -= len; strm->next_in += len; strm->total_in += len;
    let ni ← z.next_in.add (len.toNat : Int)
    wrZ strm fun z => { z with avail_in := z.avail_in - len, next_in := ni, total_in := z.total_in + len.toUInt64 }
    -- if (state->have != 4) return Z_DATA_ERROR;
    if (← rdS st (·.«have»)) != 4 then return Z_DATA_ERROR
    -- flags = state->flags; in = strm->total_in; out = strm->total_out;
    let flags ← rdS st (·.flags)
    let z ← ldZStream strm
    let in_ := z.total_in
    let out_ := z.total_out
    -- inflateReset(strm);
    let _ ← inflateReset strm
    -- strm->total_in = in; strm->total_out = out; state->flags = flags;
    wrZ strm fun z => { z with total_in := in_, total_out := out_ }
    wrS st fun s => { s with flags := flags }
    -- if (flags == -1) state->wrap = 0; else state->wrap &= ~4;
    if flags == -1 then wrS st fun s => { s with wrap := 0 }
    else wrS st fun s => { s with wrap := s.wrap &&& ~~~4 }
    -- if (state->wbits == 0) {
    let s ← ldInflateState st
    if s.wbits == 0 then
      if s.window != .null then
        ZFREEB strm s.window
        wrS st fun s => { s with window := .null }
      wrS st fun s => { s with wbits := 15 }
    -- state->mode = TYPE; return Z_OK;
    setMode st TYPE
    return Z_OK)
  freeB buf
  return r

/-- `int ZEXPORT inflateSyncPoint(z_streamp strm)` -/
def inflateSyncPoint (strm : ZStreamPtr) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let st ← castInflateState z.state
  let s ← ldInflateState st
  -- return state->mode == STORED && state->bits == 0;
  return if s.mode == STORED && s.bits == 0 then 1 else 0

/-- `int ZEXPORT inflateCopy(z_streamp dest, z_streamp source)` -/
def inflateCopy (dest source : ZStreamPtr) : M Int32 := do
  -- if (dest == Z_NULL) return Z_STREAM_ERROR;
  if dest == none then return Z_STREAM_ERROR
  -- if (inflateStateCheck(source)) { dest->state = Z_NULL; return Z_STREAM_ERROR; }
  if (← inflateStateCheck source) != 0 then
    wrZ dest fun z => { z with state := none }
    return Z_STREAM_ERROR
  let zs ← ldZStream source
  let state ← castInflateState zs.state
  -- copy = ZALLOC(source, 1, sizeof(struct inflate_state));
  let copy ← ZALLOCS source
  -- if (copy == Z_NULL) { dest->state = Z_NULL; return Z_MEM_ERROR; }
  if copy == none then
    wrZ dest fun z => { z with state := none }
    return Z_MEM_ERROR
  -- zmemzero(copy, sizeof(struct inflate_state));
  stInflateState copy (InflateState.zeroed)
  -- window = Z_NULL;
  let mut window : BPtr := .null
  let s ← ldInflateState state
  -- if (state->window != Z_NULL) {
  if s.window != .null then
    window ← ZALLOCB source (← shl32 1 s.wbits) 1
    -- if (window == Z_NULL) { ZFREE(source, copy); dest->state = Z_NULL; return Z_MEM_ERROR; }
    if window == .null then
      ZFREES source copy
      wrZ dest fun z => { z with state := none }
      return Z_MEM_ERROR
  -- zmemcpy(dest, source, sizeof(z_stream));   (a whole-struct copy; the same object is overlapping)
  copyZStream dest source
  -- zmemcpy(copy, state, sizeof(struct inflate_state));
  copyInflateState copy state
  -- copy->strm = dest;
  wrS copy fun s => { s with strm := dest }
  -- if (state->lencode == state->codes) {
  let s ← ldInflateState state
  if s.lencode == codesP state then
    -- copy->lencode = copy->codes;
    wrS copy fun s => { s with lencode := codesP copy }
    -- copy->distcode = copy->codes + (state->distcode - state->codes);
    let d2 ← Ptr.diff s.distcode (codesP state)
    let dc ← (codesP copy).add d2.toInt
    wrS copy fun s => { s with distcode := dc }
  -- copy->next = copy->codes + (state->next - state->codes);
  let d3 ← Ptr.diff s.next (codesP state)
  let nx ← (codesP copy).add d3.toInt
  wrS copy fun s => { s with next := nx }
  -- if (window != Z_NULL) zmemcpy(window, state->window, state->whave);
  if window != .null then memcpyB window s.window s.whave.toNat
  -- copy->window = window; dest->state = (struct internal_state FAR *)copy;
  wrS copy fun s => { s with window := window }
  wrZ dest fun z => { z with state := StateRef.ofInflateState copy }
  return Z_OK

/-- `int ZEXPORT inflateUndermine(z_streamp strm, int subvert)` (`INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR` undefined) -/
def inflateUndermine (strm : ZStreamPtr) (_subvert : Int32) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let st ← castInflateState z.state
  -- (void)subvert; state->sane = 1; return Z_DATA_ERROR;
  wrS st fun s => { s with sane := 1 }
  return Z_DATA_ERROR

/-- `int ZEXPORT inflateValidate(z_streamp strm, int check)` -/
def inflateValidate (strm : ZStreamPtr) (check : Int32) : M Int32 := do
  if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let z ← ldZStream strm
  let st ← castInflateState z.state
  let s ← ldInflateState st
  -- if (check && state->wrap) state->wrap |= 4; else state->wrap &= ~4;
  let wrap := if check != 0 && s.wrap != 0 then s.wrap ||| 4 else s.wrap &&& ~~~4
  -- if (check && state->reqwrap) state->reqwrap |= 4; else state->reqwrap &= ~4;
  let reqwrap := if check != 0 && s.reqwrap != 0 then s.reqwrap ||| 4 else s.reqwrap &&& ~~~4
  wrS st fun s => { s with wrap := wrap, reqwrap := reqwrap }
  return Z_OK

/-- `long ZEXPORT inflateMark(z_streamp strm)` -/
def inflateMark (strm : ZStreamPtr) : M Int64 := do
  -- if (inflateStateCheck(strm)) return -(1L << 16);
  if (← inflateStateCheck strm) != 0 then return -((1 : Int64) <<< 16)
  let z ← ldZStream strm
  let st ← castInflateState z.state
  let s ← ldInflateState st
  -- (long)(((unsigned long)((long)state->back)) << 16)
  let hi : Int64 := ((s.back.toInt64.toUInt64) <<< 16).toInt64
  -- state->mode == COPY ? state->length : (state->mode == MATCH ? state->was - state->length : 0)   (type unsigned)
  let lo : UInt32 := if s.mode == COPY then s.length else if s.mode == MATCH then s.was - s.length else 0
  chkI64 (hi.toInt + lo.toNat)

/-- `unsigned long ZEXPORT inflateCodesUsed(z_streamp strm)` -/
def inflateCodesUsed (strm : ZStreamPtr) : M UInt64 := do
  -- if (inflateStateCheck(strm)) return (unsigned long)-1;
  if (← inflateStateCheck strm) != 0 then return 0xffffffffffffffff
  let z ← ldZStream strm
  let st ← castInflateState z.state
  let s ← ldInflateState st
  -- return (unsigned long)(state->next - state->codes);
  let d ← Ptr.diff s.next (codesP st)
  return d.toUInt64

end Zlib.Inflate
