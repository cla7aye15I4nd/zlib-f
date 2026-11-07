import ZlibF.Runtime.Alloc

/-!
# gzfs: the external world of the gz* files (trusted base)

The runtime heap (`ZlibF/Runtime`) has no file system, no `errno` and no `printf`. The gz* functions call `open`,
`read`, `write`, `lseek`, `close`, `fcntl`, `strerror`, `snprintf`/`vsnprintf`. This file is the model of those
calls, written next to the translation; it is part of the trusted base (`docs/design/external-io.md`
lists every decision and narrowing).

The world is a record `Fs` that lives beside the heap: a gz computation is `G α = StateT Fs C.M α`, so a heap
computation (`C.M`) lifts into it and a fault is still `Fault.ub`.
-/

namespace Zlib.GzFs
open C

/-- An open file description (what a file descriptor refers to). -/
structure OFile where
  node : Nat
  pos : Nat
  rd : Bool
  wr : Bool
  append : Bool
  deriving Inhabited

/-- A file (its bytes) or a directory (no bytes; `open` for reading succeeds, `read` fails with `EISDIR`). -/
structure Node where
  data : Array UInt8
  isDir : Bool
  deriving Inhabited

/-- The file system, the descriptor table, `errno` and the file size limit (`RLIMIT_FSIZE`). Paths are flat
byte strings (no directory structure). -/
structure Fs where
  names : Array (Array UInt8 × Nat) := #[]
  nodes : Array Node := #[]
  fds : Array (Option OFile) := #[]
  errno : Int32 := 0
  fsizeLimit : Nat := 2 ^ 62
  deriving Inhabited

/-- A gz computation: the world in, the heap in, a value and both out, or a fault. -/
abbrev G (α : Type) : Type := StateT Fs M α

/-- Undefined behaviour inside `G`. -/
def gub {α : Type} (what : String) : G α := fun _ => C.ub what

/-- `ENOENT` etc. (Linux x86_64 values). -/
def ENOENT : Int32 := 2
def EBADF : Int32 := 9
def EEXIST : Int32 := 17
def EISDIR : Int32 := 21
def EINVAL : Int32 := 22
def EFBIG : Int32 := 27
def ENOSPC : Int32 := 28
def EOVERFLOW : Int32 := 75
def EAGAIN : Int32 := 11

/-- `errno` as read by the C. -/
def getErrno : G Int32 := do return (← get).errno
/-- `errno = e`. -/
def setErrno (e : Int32) : G Unit := modify fun w => { w with errno := e }

/-- `BLOCKED(e)`: `e == EAGAIN || e == EWOULDBLOCK` (both are 11). -/
def BLOCKED (e : Int32) : Bool := e == EAGAIN

/-- The text of `strerror(e)` (glibc), for the errno values the model can produce; others give glibc's
`Unknown error N`. -/
def strerrorText (e : Int32) : String :=
  if e == 0 then "Success"
  else if e == ENOENT then "No such file or directory"
  else if e == EBADF then "Bad file descriptor"
  else if e == EEXIST then "File exists"
  else if e == EISDIR then "Is a directory"
  else if e == EINVAL then "Invalid argument"
  else if e == EFBIG then "File too large"
  else if e == ENOSPC then "No space left on device"
  else if e == EOVERFLOW then "Value too large for defined data type"
  else s!"Unknown error {e.toInt}"

/-- A string literal of the C sources: the static read-only array of the runtime (`strLitRef`, the same pointer
every time). -/
def strLit (s : String) : M BPtr := strLitRef s

/-- The text returned by `strerror(e)`: a string of the C library, not of the sources, so it is not in `strTable`.
Modelled as a fresh read-only block (never freed). -/
def libcStr (s : String) : M BPtr := allocBytesRO (s.toUTF8.toList.toArray.push 0)

/-- `strerror(errno)`: a pointer to a string. -/
def zstrerror : G BPtr := do
  let e ← getErrno
  libcStr (strerrorText e)

/-- The bytes of the NUL-terminated string at `p` (without the NUL). Faults if `p` is null or has no NUL. -/
def cstring (p : BPtr) : M (Array UInt8) := do
  let n ← strlenB p
  let mut out : Array UInt8 := #[]
  for i in [0:n.toNat] do
    out := out.push (← index8 p i)
  return out

/-- Store `bs` at `p`, `p + 1`, ... as one block copy (what `read` and `vsnprintf` do to their buffer): faults if the
range is not inside the object or the object is read-only. (One copy instead of a store per byte: every store makes the
heap function one level deeper, which costs memory in the interpreter, not in the model.) -/
def storeBytes (p : BPtr) (bs : Array UInt8) : M Unit := do
  if bs.isEmpty then return
  let t ← allocBytes bs
  memcpyB p t bs.size
  freeB t

/-- Load `n` bytes from `p`. -/
def loadBytes (p : BPtr) (n : Nat) : M (Array UInt8) := do
  let mut out : Array UInt8 := #[]
  for i in [0:n] do
    out := out.push (← index8 p i)
  return out

/-! ## System calls -/

def O_WRONLY : Int32 := 1
def O_CREAT : Int32 := 64
def O_EXCL : Int32 := 128
def O_TRUNC : Int32 := 512
def O_APPEND : Int32 := 1024
def O_NONBLOCK : Int32 := 2048
def O_CLOEXEC : Int32 := 524288
def O_LARGEFILE : Int32 := 0
def SEEK_SET : Int32 := 0
def SEEK_CUR : Int32 := 1
def SEEK_END : Int32 := 2

private def findName (w : Fs) (p : Array UInt8) : Option Nat :=
  (w.names.find? (fun e => e.1 == p)).map (·.2)

private def lowestFd (w : Fs) : Nat :=
  let rec go (i : Nat) : Nat → Nat
    | 0 => i
    | k + 1 => if i < w.fds.size then (if (w.fds[i]!).isNone then i else go (i + 1) k) else i
  go 3 (w.fds.size + 3)

/-- `open(path, oflag, 0666)` for `path` given as its bytes. Returns the descriptor or -1 with `errno`. The
access mode is read-only or write-only; `O_CREAT`, `O_EXCL`, `O_TRUNC`, `O_APPEND` are honoured; `O_NONBLOCK`,
`O_CLOEXEC` and `O_LARGEFILE` do nothing (regular files only). Permissions are not modelled. -/
def fsOpen (path : Array UInt8) (oflag : Int32) : G Int32 := fun w =>
  let acc := oflag &&& 3
  let has (f : Int32) := (oflag &&& f) != 0
  let fail (e : Int32) : M (Int32 × Fs) := pure (-1, { w with errno := e })
  let openNode (n : Nat) (w : Fs) : M (Int32 × Fs) :=
    let node := w.nodes[n]!
    let wr := acc == 1
    if wr && node.isDir then pure (-1, { w with errno := EISDIR })
    else
      let w := if wr && has O_TRUNC then { w with nodes := w.nodes.set! n { node with data := #[] } } else w
      let fd := lowestFd w
      let fds := if fd < w.fds.size then w.fds else w.fds ++ Array.replicate (fd + 1 - w.fds.size) none
      let of : OFile := { node := n, pos := 0, rd := acc == 0, wr, append := has O_APPEND }
      pure (Int32.ofNat fd, { w with fds := fds.set! fd (some of) })
  if acc ≥ 2 then fail EINVAL
  else if path.isEmpty then fail ENOENT
  else match findName w path with
    | some n => if has O_CREAT && has O_EXCL then fail EEXIST else openNode n w
    | none =>
      if has O_CREAT then
        let n := w.nodes.size
        openNode n { w with names := w.names.push (path, n), nodes := w.nodes.push { data := #[], isDir := false } }
      else fail ENOENT

/-- `read(fd, buf, n)` as a pair: the result and the bytes that were read (to be stored at `buf` by the caller). -/
def fsRead (fd : Int32) (n : UInt64) : G (Int64 × Array UInt8) := fun w =>
  let fail (e : Int32) : M ((Int64 × Array UInt8) × Fs) := pure ((-1, #[]), { w with errno := e })
  if fd < 0 || fd.toInt ≥ w.fds.size then fail EBADF
  else match w.fds[fd.toInt.toNat]! with
    | none => fail EBADF
    | some of =>
      if !of.rd then fail EBADF
      else
        let node := w.nodes[of.node]!
        if node.isDir then fail EISDIR
        else
          let k := min n.toNat (node.data.size - of.pos)
          let bs := node.data.extract of.pos (of.pos + k)
          pure ((Int64.ofNat k, bs),
            { w with fds := w.fds.set! fd.toInt.toNat (some { of with pos := of.pos + k }) })

/-- `write(fd, buf, n)` for the bytes `bs` of the buffer. A write past the size limit is cut (a short write), and
a write with no room fails with `EFBIG`. -/
def fsWrite (fd : Int32) (bs : Array UInt8) : G Int64 := fun w =>
  let fail (e : Int32) : M (Int64 × Fs) := pure (-1, { w with errno := e })
  if fd < 0 || fd.toInt ≥ w.fds.size then fail EBADF
  else match w.fds[fd.toInt.toNat]! with
    | none => fail EBADF
    | some of =>
      if !of.wr then fail EBADF
      else if bs.isEmpty then pure (0, w)
      else
        let node := w.nodes[of.node]!
        let pos := if of.append then node.data.size else of.pos
        if pos ≥ w.fsizeLimit then fail EFBIG
        else
          let k := min bs.size (w.fsizeLimit - pos)
          let old := if pos > node.data.size then node.data ++ Array.replicate (pos - node.data.size) 0 else node.data
          let new := old.extract 0 pos ++ bs.extract 0 k ++ old.extract (pos + k) old.size
          pure (Int64.ofNat k,
            { w with nodes := w.nodes.set! of.node { node with data := new }
                     fds := w.fds.set! fd.toInt.toNat (some { of with pos := pos + k }) })

/-- `lseek(fd, off, whence)`. -/
def fsLseek (fd : Int32) (off : Int64) (whence : Int32) : G Int64 := fun w =>
  let fail (e : Int32) : M (Int64 × Fs) := pure (-1, { w with errno := e })
  if fd < 0 || fd.toInt ≥ w.fds.size then fail EBADF
  else match w.fds[fd.toInt.toNat]! with
    | none => fail EBADF
    | some of =>
      let base : Option Int :=
        if whence == SEEK_SET then some 0
        else if whence == SEEK_CUR then some of.pos
        else if whence == SEEK_END then some (w.nodes[of.node]!.data.size) else none
      match base with
      | none => fail EINVAL
      | some b =>
        let np := b + off.toInt
        if np < 0 then fail EINVAL
        else if np > 9223372036854775807 then fail EOVERFLOW
        else pure (Int64.ofInt np,
          { w with fds := w.fds.set! fd.toInt.toNat (some { of with pos := np.toNat }) })

/-- `close(fd)`. -/
def fsClose (fd : Int32) : G Int32 := fun w =>
  if fd < 0 || fd.toInt ≥ w.fds.size then pure (-1, { w with errno := EBADF })
  else match w.fds[fd.toInt.toNat]! with
    | none => pure (-1, { w with errno := EBADF })
    | some _ => pure (0, { w with fds := w.fds.set! fd.toInt.toNat none })

/-- `fcntl(fd, F_SETFL / F_SETFD, ...)` as used by `gz_open`: the result is ignored by the C and regular files
do not change behaviour, so it does nothing. -/
def fsFcntl (_fd : Int32) : G Unit := pure ()

/-! ## Harness access to the world (not C operations) -/

/-- Create or replace the file `name`. -/
def Fs.put (w : Fs) (name : Array UInt8) (data : Array UInt8) : Fs :=
  match findName w name with
  | some n => { w with nodes := w.nodes.set! n { data, isDir := false } }
  | none => { w with names := w.names.push (name, w.nodes.size), nodes := w.nodes.push { data, isDir := false } }

/-- Create a directory entry `name`. -/
def Fs.mkdir (w : Fs) (name : Array UInt8) : Fs :=
  { w with names := w.names.push (name, w.nodes.size), nodes := w.nodes.push { data := #[], isDir := true } }

/-- The bytes of the file `name`, if any. -/
def Fs.get? (w : Fs) (name : Array UInt8) : Option (Array UInt8) :=
  (findName w name).map fun n => w.nodes[n]!.data

/-- The position of the descriptor, if open. -/
def Fs.posOf? (w : Fs) (fd : Nat) : Option Nat :=
  if h : fd < w.fds.size then (w.fds[fd]).map (·.pos) else none

/-! ## Loops in `G` -/

def gwhile {σ : Type} (cond : σ → G (Bool × σ)) (body : σ → G σ) (s : σ) : G σ :=
  go C.fuel s
where
  go : Nat → σ → G σ
    | 0, _ => fun _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then go n (← body s) else pure s

def gdoWhile {σ : Type} (body : σ → G σ) (cond : σ → G (Bool × σ)) (s : σ) : G σ :=
  go C.fuel s
where
  go : Nat → σ → G σ
    | 0, _ => fun _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let s ← body s
      let (c, s) ← cond s
      if c then go n s else pure s

/-! ## printf -/

/-- One variadic argument. `int`/`uint` are 32-bit, `long`/`ulong` 64-bit, `str` is a `char *`. -/
inductive VaArg where
  | int (v : Int32)
  | uint (v : UInt32)
  | long (v : Int64)
  | ulong (v : UInt64)
  | str (p : BPtr)

structure Spec where
  minus : Bool := false
  zero : Bool := false
  plus : Bool := false
  space : Bool := false
  alt : Bool := false
  width : Nat := 0
  prec : Option Nat := none
  long : Bool := false
  conv : UInt8 := 0
  deriving DecidableEq

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- The decimal number that starts at `j` (at most `fuel` digits) added to `v`: its value and the position after it. -/
def readNumGo (f : Array UInt8) : Nat → Nat → Nat → Nat × Nat
  | 0, j, v => (v, j)
  | k + 1, j, v =>
    if j < f.size && isDigit f[j]! then readNumGo f k (j + 1) (v * 10 + (f[j]!.toNat - 48)) else (v, j)

/-- The decimal number that starts at `i` and the position after it. -/
def readNum (f : Array UInt8) (i : Nat) : Nat × Nat := readNumGo f f.size i 0

/-- The flags `-0+ #` that start at `j` (at most `fuel` of them), set in `sp`, and the position after them. -/
def parseFlags (f : Array UInt8) : Nat → Nat → Spec → Spec × Nat
  | 0, j, sp => (sp, j)
  | k + 1, j, sp =>
    if j < f.size then
      if f[j]! == 45 then parseFlags f k (j + 1) { sp with minus := true }
      else if f[j]! == 48 then parseFlags f k (j + 1) { sp with zero := true }
      else if f[j]! == 43 then parseFlags f k (j + 1) { sp with plus := true }
      else if f[j]! == 32 then parseFlags f k (j + 1) { sp with space := true }
      else if f[j]! == 35 then parseFlags f k (j + 1) { sp with alt := true }
      else (sp, j)
    else (sp, j)

/-- The conversion specification that starts at `i` (after the `%`): flags, width, precision, length modifier and
conversion character, and the position after it; `none` if the format ends first. -/
def parseSpec (f : Array UInt8) (i : Nat) : Option (Spec × Nat) :=
  let (sp, j) := parseFlags f f.size i {}
  let (w, j) := readNum f j
  let sp := { sp with width := w }
  let (sp, j) :=
    if j < f.size && f[j]! == 46 then
      let (p, j3) := readNum f (j + 1)
      ({ sp with prec := some p }, j3)
    else (sp, j)
  let (sp, j) :=
    if j < f.size && (f[j]! == 108 || f[j]! == 122 || f[j]! == 106 || f[j]! == 116) then
      ({ sp with long := true }, if j + 1 < f.size && f[j + 1]! == 108 then j + 2 else j + 1)
    else (sp, j)
  if j < f.size then some ({ sp with conv := f[j]! }, j + 1) else none

def natDigits (v : Nat) (base : Nat) (upper : Bool) : Array UInt8 :=
  (Nat.toDigits base v).toArray.map fun c =>
    let b := c.toNat.toUInt8
    if upper && b ≥ 97 then b - 32 else b

def pad (sp : Spec) (body : Array UInt8) (zeroOk : Bool) : Array UInt8 :=
  if body.size ≥ sp.width then body
  else
    let n := sp.width - body.size
    if sp.minus then body ++ Array.replicate n 32
    else if sp.zero && zeroOk then
      -- zeros go after the sign / prefix: callers pass sign/prefix separately, see fmtInt
      Array.replicate n 48 ++ body
    else Array.replicate n 32 ++ body

def fmtInt (sp : Spec) (neg : Bool) (mag : Nat) (base : Nat) (upper : Bool) (signed : Bool) :
    Array UInt8 :=
  let ds0 := natDigits mag base upper
  let ds1 := match sp.prec with
    | some 0 => if mag == 0 then #[] else ds0
    | some p => if ds0.size < p then Array.replicate (p - ds0.size) 48 ++ ds0 else ds0
    | none => ds0
  let prefixB : Array UInt8 :=
    if signed then (if neg then #[45] else if sp.plus then #[43] else if sp.space then #[32] else #[])
    else if sp.alt && mag != 0 && base == 16 then (if upper then #[48, 88] else #[48, 120])
    else #[]
  let ds1 := if sp.alt && base == 8 && (ds1.isEmpty || ds1[0]! != 48) then #[48] ++ ds1 else ds1
  let total := prefixB.size + ds1.size
  if total ≥ sp.width then prefixB ++ ds1
  else
    let n := sp.width - total
    if sp.minus then prefixB ++ ds1 ++ Array.replicate n 32
    else if sp.zero && sp.prec.isNone then prefixB ++ Array.replicate n 48 ++ ds1
    else Array.replicate n 32 ++ prefixB ++ ds1

/-- The text of a `%s` argument: `(null)` for a null pointer (as glibc), else what the heap resolver `res` gives. -/
def argStr (res : BPtr → Option (Array UInt8)) (p : BPtr) : Option (Array UInt8) :=
  if p == .null then some "(null)".toUTF8.toList.toArray else res p

/-- The output of `printf(f, args)` from position `i` on, as bytes, appended to `out`; `res p` is the string at `p` in
the heap (`none` if there is none). `fuel` is the number of steps left (`f.size + 1` suffices: each step consumes a
character). Supports `%%`, `%c`, `%s`, `%d`, `%i`, `%u`, `%x`, `%X`, `%o` with the flags `-0+ #`, a width, a
precision and the length modifiers `l`, `ll`, `z`, `j`, `t`. Anything else, an argument of the wrong kind, or too few
arguments is an error (undefined in C). -/
def formatGo (f : Array UInt8) (res : BPtr → Option (Array UInt8)) :
    Nat → Nat → List VaArg → Array UInt8 → Except String (Array UInt8)
  | 0, _, _, out => .ok out
  | fuel + 1, i, args, out =>
    if i < f.size then
      if f[i]! != 37 then formatGo f res fuel (i + 1) args (out.push f[i]!)
      else
        match parseSpec f (i + 1) with
        | none => .error "printf: incomplete conversion"
        | some (sp, j) =>
          let cv := sp.conv
          if cv == 37 then formatGo f res fuel j args (out.push 37)
          else if cv == 99 then
            match args with
            | .int v :: r => formatGo f res fuel j r (out ++ pad sp #[v.toUInt32.toUInt8] false)
            | _ => .error "printf: %c needs an int"
          else if cv == 115 then
            match args with
            | .str p :: r =>
              match argStr res p with
              | some s =>
                let s := match sp.prec with | some k => s.extract 0 k | none => s
                formatGo f res fuel j r (out ++ pad sp s false)
              | none => .error "printf: %s argument is not a NUL-terminated string"
            | _ => .error "printf: %s needs a pointer"
          else if cv == 100 || cv == 105 then
            match sp.long, args with
            | false, .int v :: r =>
              formatGo f res fuel j r (out ++ fmtInt sp (v.toInt < 0) v.toInt.natAbs 10 false true)
            | true, .long v :: r =>
              formatGo f res fuel j r (out ++ fmtInt sp (v.toInt < 0) v.toInt.natAbs 10 false true)
            | _, _ => .error "printf: %d argument of the wrong kind"
          else if cv == 117 || cv == 120 || cv == 88 || cv == 111 then
            let base := if cv == 117 then 10 else if cv == 111 then 8 else 16
            match sp.long, args with
            | false, .uint v :: r => formatGo f res fuel j r (out ++ fmtInt sp false v.toNat base (cv == 88) false)
            | false, .int v :: r =>
              formatGo f res fuel j r (out ++ fmtInt sp false v.toUInt32.toNat base (cv == 88) false)
            | true, .ulong v :: r => formatGo f res fuel j r (out ++ fmtInt sp false v.toNat base (cv == 88) false)
            | true, .long v :: r =>
              formatGo f res fuel j r (out ++ fmtInt sp false v.toUInt64.toNat base (cv == 88) false)
            | _, _ => .error "printf: unsigned conversion argument of the wrong kind"
          else .error "printf: conversion not modelled"
    else .ok out

/-- The string at `p` in the heap `h` (the bytes before the first NUL), if there is one. -/
def heapStr (h : Heap) (p : BPtr) : Option (Array UInt8) :=
  match cstring p h with | .ok (s, _) => some s | .error _ => none

/-- The full output of `printf(fmt, args)` as bytes (`formatGo`); the heap is read, not changed. -/
def formatBytes (f : Array UInt8) (args : List VaArg) : M (Array UInt8) := fun h =>
  match formatGo f (heapStr h) (f.size + 1) 0 args #[] with
  | .ok out => .ok (out, h)
  | .error m => .error (.ub m)

/-- `vsnprintf(dst, size, fmt, args)`: writes at most `size - 1` characters and a NUL (nothing if `size` is 0) and
returns the length the full output has. -/
def vsnprintf (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) : M Int32 := do
  let f ← cstring fmt
  let out ← formatBytes f args
  if out.size > 2147483647 then C.ub "vsnprintf: output longer than INT_MAX"
  if size != 0 then
    let k := min out.size (size.toNat - 1)
    storeBytes dst (out.extract 0 k)
    let q ← dst.add k
    store8 q 0
  return Int32.ofNat out.size

end Zlib.GzFs
