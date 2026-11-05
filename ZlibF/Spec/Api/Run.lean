import ZlibF.Spec.Api.Gz
import ZlibF.Spec.Api.Compress

/-!
# API model: operations and runs

One datatype of operations per stream family, with the model relation that dispatches to the
single-function relations, and the notion of a *run*: a sequence of calls in which the caller
re-presents the input that was not consumed (`A-stream-progress`). The goals quantify over runs,
so they hold for every chunking of the input and of the output room.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

/-! ## Inflate operations -/

/-- The operations on an initialised inflate stream. -/
inductive InflOp where
  | inflate (c : InflCall)
  | reset
  | reset2 (wb : Int)
  | prime (bits value : Int)
  | setDictionary (d : List UInt8)
  | getDictionary
  | sync (inp : List UInt8)
  | syncPoint
  | mark
  | getHeader (req : HdrReq)
  | undermine (subvert : Int)
  | validate (check : Int)

/-- What an inflate operation returns. `consumed` is for `inflate` and `sync`. -/
structure InflRes where
  rc : Int := 0
  out : InflOut := ⟨0, [], 0⟩
  buf : List UInt8 := []
  consumed : Nat := 0

/-- The model of an inflate operation: the operation, what it returned, the state after. -/
def InflModel (st : InflState) : InflOp → InflRes → InflState → Prop
  | .inflate c, r, st' => InflStep st c r.out st' ∧ r.rc = r.out.rc
  | .reset, r, st' => InflReset st r.rc st'
  | .reset2 wb, r, st' => InflReset2 st wb r.rc st'
  | .prime b v, r, st' => InflPrime st b v r.rc st'
  | .setDictionary d, r, st' => InflSetDict st d r.rc st'
  | .getDictionary, r, st' => InflGetDict st r.buf r.rc ∧ st' = st
  | .sync inp, r, st' => InflSync st inp r.consumed r.rc st'
  | .syncPoint, r, st' => InflSyncPoint st r.rc ∧ st' = st
  | .mark, r, st' => InflMark st r.rc ∧ st' = st
  | .getHeader req, r, st' => InflGetHeader st req r.rc st'
  | .undermine s, r, st' => InflUndermine st s r.rc st'
  | .validate c, r, st' => InflValidate st c r.rc st'

/-! ## Deflate operations -/

/-- The operations on an initialised deflate stream. `params` carries the input and the room the
stream has at the time of the call. -/
inductive DeflOp where
  | deflate (c : DeflCall)
  | params (level strategy : Int) (c : DeflCall)
  | reset
  | tune
  | setDictionary (d : List UInt8)
  | getDictionary
  | prime (bits value : Int)
  | pending
  | setHeader (h : GzHead)
  | bound (n : Nat)

/-- What a deflate operation returns. -/
structure DeflRes where
  rc : Int := 0
  out : DeflOut := ⟨0, [], 0⟩
  buf : List UInt8 := []
  pending : Nat := 0
  bits : Nat := 0
  bound : Nat := 0

/-- The model of a deflate operation. -/
def DeflModel (st : DeflState) : DeflOp → DeflRes → DeflState → Prop
  | .deflate c, r, st' => DeflStep st c r.out st' ∧ r.rc = r.out.rc
  | .params l s c, r, st' => DeflParamsFn st l s c r.out st' ∧ r.rc = r.out.rc
  | .reset, r, st' => DeflReset st r.rc st'
  | .tune, r, st' => DeflTune st r.rc st'
  | .setDictionary d, r, st' => DeflSetDict st d r.rc st'
  | .getDictionary, r, st' => DeflGetDict st r.buf r.rc ∧ st' = st
  | .prime b v, r, st' => DeflPrime st b v r.rc st'
  | .pending, r, st' => DeflPending st r.pending r.bits r.rc ∧ st' = st
  | .setHeader h, r, st' => DeflSetHeader st h r.rc st'
  | .bound n, r, st' => DeflBound st n r.bound ∧ st' = st

/-! ## Gz operations -/

/-- The operations on an open gz file (not open, not close). -/
inductive GzOp where
  | read (len : Nat) | fread (size nitems : Nat) | getc | ungetc (c : Int) | gets (len : Int)
  | eof | error | clearerr | rewind | seek (off whence : Int) | tell | offset | direct
  | buffer (size : Nat) | write (s : List UInt8) | fwrite (size : Nat) (s : List UInt8)
  | putc (c : Int) | puts (s : List UInt8) | printf (s : List UInt8)
  | setparams (level strategy : Int) | flush (flush : Int)

/-- What a gz operation returns: the integer result, the bytes read, the line of `gzgets`
(`none` is `NULL`), the number of items of `gzfread`/`gzfwrite`. -/
structure GzRes where
  ret : Int := 0
  bytes : List UInt8 := []
  line : Option (List UInt8) := none
  items : Nat := 0

/-- The model of a gz operation. -/
def GzModel (h : GzHandle) : GzOp → GzRes → GzHandle → Prop
  | .read n, r, h' => GzReadFn h n r.bytes r.ret h'
  | .fread s n, r, h' => GzFread h s n r.bytes r.items h'
  | .getc, r, h' => GzGetc h r.ret h'
  | .ungetc c, r, h' => GzUngetc h c r.ret h'
  | .gets n, r, h' => GzGets h n r.line h'
  | .eof, r, h' => GzEof h r.ret ∧ h' = h
  | .error, r, h' => GzError h r.ret ∧ h' = h
  | .clearerr, _, h' => GzClearerr h h'
  | .rewind, r, h' => GzRewind h r.ret h'
  | .seek o w, r, h' => GzSeek h o w r.ret h'
  | .tell, r, h' => GzTell h r.ret ∧ h' = h
  | .offset, r, h' => GzOffset h r.ret ∧ h' = h
  | .direct, r, h' => GzDirect h r.ret ∧ h' = h
  | .buffer n, r, h' => GzBuffer h n r.ret h'
  | .write s, r, h' => GzWrite h s r.ret h'
  | .fwrite n s, r, h' => GzFwrite h n s r.items h'
  | .putc c, r, h' => GzPutc h c r.ret h'
  | .puts s, r, h' => GzPuts h s r.ret h'
  | .printf s, r, h' => GzPrintf h s r.ret h'
  | .setparams l s, r, h' => GzSetParams h l s r.ret h'
  | .flush f, r, h' => GzFlush h f r.ret h'

/-! ## Traces -/

/-- A trace of inflate over the stream `Z`: `inflate` calls whose input is a prefix of the part of
`Z` that is not consumed yet (the caller re-presents unconsumed input, whatever its chunking,
whatever the room), and `setDictionary` calls with the dictionary `d0`. Each step is allowed by
the model. -/
inductive InflTrace (Z d0 : List UInt8) : InflState → InflState → Prop
  | nil {s : InflState} : InflTrace Z d0 s s
  | step {s s' s'' : InflState} {c : InflCall} {r : InflRes} :
      c.inp <+: Z.drop s.seen.length → InflModel s (.inflate c) r s' → InflTrace Z d0 s' s'' →
      InflTrace Z d0 s s''
  | dict {s s' s'' : InflState} {r : InflRes} :
      InflModel s (.setDictionary d0) r s' → InflTrace Z d0 s' s'' → InflTrace Z d0 s s''

/-- A trace of deflate over the input `X`: `deflate` calls whose input is a prefix of the part of `X`
not accepted yet, and `setDictionary`, `setHeader` calls (which `zlib.h` allows at the start). -/
inductive DeflTrace (X : List UInt8) : DeflState → DeflState → Prop
  | nil {s : DeflState} : DeflTrace X s s
  | step {s s' s'' : DeflState} {c : DeflCall} {r : DeflRes} :
      c.inp <+: X.drop s.input.length → DeflModel s (.deflate c) r s' → DeflTrace X s' s'' →
      DeflTrace X s s''
  | dict {s s' s'' : DeflState} {d : List UInt8} {r : DeflRes} :
      DeflModel s (.setDictionary d) r s' → DeflTrace X s' s'' → DeflTrace X s s''
  | header {s s' s'' : DeflState} {h : GzHead} {r : DeflRes} :
      DeflModel s (.setHeader h) r s' → DeflTrace X s' s'' → DeflTrace X s s''

end ZlibF.Spec.Api
