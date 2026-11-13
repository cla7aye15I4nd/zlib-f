import ZlibF.Zlib.«gzclose.c»
import ZlibF.Zlib.«uncompr.c»
import DiffTest.Common
import DiffTest.Heap

/-!
Lean side of the differential test for `gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c` and `uncompr.c`. It calls
the translations (the modules the proofs are about) and the file model `Zlib.GzFs`. The scenario language is the
one of `c/gz.c` and `gen/gz.py`; a fault stops the line and prints `FAULT ...` (the C side cannot fault).
-/

open DiffTest C Zlib.GzFs Zlib.Gzlib Zlib.Gzread Zlib.Gzwrite Zlib.Gzclose

/-- The heap of the tests: the static tables that the translations read are installed. -/
def startHeap : Heap := DiffTest.fullHeap

structure Env where
  fs : Fs
  h : Heap
  hs : Array GzFilePtr

def runG {α : Type} (e : Env) (x : G α) : Except Fault (α × Env) :=
  match (x.run e.fs) e.h with
  | .ok ((a, fs), h) => .ok (a, { e with fs, h })
  | .error f => .error f

def runM {α : Type} (e : Env) (x : M α) : Except Fault (α × Env) :=
  match x e.h with
  | .ok (a, h) => .ok (a, { e with h })
  | .error f => .error f

def toHex (bs : Array UInt8) : String := Id.run do
  let d := "0123456789abcdef".toList.toArray
  let mut s := ""
  for b in bs do
    s := s.push d[(b >>> 4).toNat]! |>.push d[(b &&& 15).toNat]!
  return s

def hexArg (s : String) : Except String (Array UInt8) :=
  if s == "-" then pure #[] else parseHex s

/-- The bytes of the block `p` points into (from its start). -/
def blockBytes (e : Env) (p : BPtr) : Array UInt8 :=
  match p with
  | .ref (.blk b) _ => (e.h.bytes b).getD #[]
  | _ => #[]

def cstr (s : String) : Array UInt8 := s.toUTF8.data.push 0

def fail {α : Type} (m : String) : Except Fault α := .error (.ub s!"BADINPUT {m}")

def pI32 (s : String) : Except String Int32 := do return Int32.ofInt (← parseI64 s).toInt

def printfFmt (k : Nat) : String :=
  match k with
  | 0 => "hello" | 1 => "%d" | 2 => "[%5d|%-5d|%05d]" | 3 => "%s=%s" | 4 => "%u %x %X %o"
  | 5 => "%ld %lu" | 6 => "%c%c" | 7 => "%.3s|%10s|%-10s|" | 8 => "%+d % d %%" | 9 => "%s"
  | 10 => "%#x %#o" | 11 => "%s" | 13 => "%d" | _ => "%.0d|%.5d"

def doOp (e : Env) (op : String) : Except Fault (String × Env) := do
  let f := op.splitOn ":"
  let c := f.headD ""
  let hIdx : Nat := match c with
    | "put" | "mkdir" | "dump" | "fsize" => 0
    | _ => ((f.getD 1 "0").toNat?).getD 0
  let g : GzFilePtr := e.hs.getD hIdx none
  let bad {α : Type} (m : String) : Except Fault α := fail m
  let pn (i : Nat) : Except Fault Nat :=
    match (f.getD i "").toNat? with | some n => pure n | none => bad s!"number {op}"
  let pi (i : Nat) : Except Fault Int :=
    match (f.getD i "").toInt? with | some n => pure n | none => bad s!"number {op}"
  let ph (i : Nat) : Except Fault (Array UInt8) :=
    match hexArg (f.getD i "") with | .ok b => pure b | .error m => bad m
  let setH (e : Env) (v : GzFilePtr) : Env := { e with hs := e.hs.set! hIdx v }
  let ro (e : Env) (s : String) : Except Fault (BPtr × Env) := runM e (allocBytesRO (cstr s))
  let nameB := (f.getD 1 "").toUTF8.data
  match c with
  | "put" => return ("p", { e with fs := e.fs.put nameB (← ph 2) })
  | "mkdir" => return ("d", { e with fs := e.fs.mkdir nameB })
  | "fsize" =>
    let v ← pn 1
    return ("z", { e with fs := { e.fs with fsizeLimit := if v == 0 then 2 ^ 62 else v } })
  | "dump" =>
    return (match e.fs.get? nameB with | none => "=-" | some d => "=" ++ toHex d, e)
  | "open" =>
    let (path, e) ← ro e (f.getD 2 "")
    let (mode, e) ← ro e (f.getD 3 "")
    let (r, e) ← runG e (gzopen path mode)
    return (s!"o{if r.isSome then 1 else 0}", setH e r)
  | "dopen" =>
    let (mode, e) ← ro e (f.getD 4 "")
    let k := f.getD 3 ""
    let (r, e) ← runG e (do
      let fd : Int32 ← if k == "bad" then pure (-1) else
        fsOpen (f.getD 2 "").toUTF8.data (if k == "r" then 0 else if k == "w" then 1 ||| 64 ||| 512
                       else if k == "a" then 1 ||| 64 ||| 1024 else 1 ||| 64)
      gzdopen fd mode)
    return (s!"D{if r.isSome then 1 else 0}", setH e r)
  | "buffer" =>
    let n ← pn 2
    let (r, e) ← runM e (gzbuffer g (UInt32.ofNat n))
    return (s!"b{r.toInt}", e)
  | "write" =>
    let d ← ph 2
    let (p, e) ← runM e (allocBytes d)
    let (r, e) ← runG e (gzwrite g p (UInt32.ofNat d.size))
    return (s!"w{r.toInt}", e)
  | "fwrite" =>
    let sz ← pn 2
    let d ← ph 3
    let (p, e) ← runM e (allocBytes d)
    let (r, e) ← runG e (gzfwrite p (UInt64.ofNat sz) (UInt64.ofNat (if sz == 0 then 0 else d.size / sz)) g)
    return (s!"W{r.toNat}", e)
  | "putc" =>
    let v ← pi 2
    let (r, e) ← runG e (gzputc g (Int32.ofInt v))
    return (s!"c{r.toInt}", e)
  | "puts" =>
    let d ← ph 2
    let (p, e) ← runM e (allocBytes (d.push 0))
    let (r, e) ← runG e (gzputs g p)
    return (s!"s{r.toInt}", e)
  | "printf" =>
    let k ← pn 2
    let mut env := e
    let mut args : List VaArg := []
    for a in (f.drop 3) do
      let t := (a.take 1).toString
      let rest := (a.drop 1).toString
      if t == "s" then
        let d ← match hexArg rest with | .ok b => pure b | .error m => bad m
        let (p, e') ← runM env (allocBytes (d.push 0))
        env := e'
        args := args ++ [VaArg.str p]
      else
        let v ← match rest.toInt? with | some n => pure n | none => bad s!"number {op}"
        args := args ++ [match t with
          | "i" => VaArg.int (Int32.ofInt v)
          | "u" => VaArg.uint (UInt32.ofNat v.toNat)
          | "l" => VaArg.long (Int64.ofInt v)
          | _ => VaArg.ulong (UInt64.ofNat v.toNat)]
    if k == 9 then
      let (p0, env') ← runM env (allocBytes #[0])
      env := env'
      args := [VaArg.str p0]
    let (fp, e) ← ro env (printfFmt k)
    -- format 13: the C side's "%3000000000d" fails in glibc; here "%d" with the vsnprintf oracle failing this call
    let e := if k == 13 then
      let n := e.fs.nprintf
      { e with fs := { e.fs with printfOk := fun m => m != n } } else e
    let (r, e) ← runG e (gzprintf g fp args)
    return (s!"f{r.toInt}", e)
  | "rfail" =>
    -- the next OS call is a read in every row that uses this op: its oracle entry fails with errno E
    let v ← pi 2
    let n := e.fs.nos
    let old := e.fs.readChoice
    return ("rf", { e with fs := { e.fs with readChoice := fun m => if m = n then .fail (Int32.ofInt v) else old m } })
  | "flush" =>
    let v ← pi 2
    let (r, e) ← runG e (gzflush g (Int32.ofInt v))
    return (s!"F{r.toInt}", e)
  | "setparams" =>
    let l ← pi 2
    let s ← pi 3
    let (r, e) ← runG e (gzsetparams g (Int32.ofInt l) (Int32.ofInt s))
    return (s!"P{r.toInt}", e)
  | "read" =>
    let n ← pn 2
    let (p, e) ← runM e (allocBytes (Array.replicate (max n 1) 0))
    let (r, e) ← runG e (gzread g p (UInt32.ofNat n))
    let out := if r.toInt > 0 then (blockBytes e p).extract 0 r.toInt.toNat else #[]
    -- free(b), as the C driver does: a later call must not depend on this buffer (R-4)
    let ((), e) ← runM e (freeB p)
    return (s!"r{r.toInt}:{toHex out}", e)
  | "fread" =>
    let sz ← pn 2
    let ni ← pn 3
    let (p, e) ← runM e (allocBytes (Array.replicate (max ((sz * ni) % 2 ^ 64) 1) 0))
    let (r, e) ← runG e (gzfread p (UInt64.ofNat sz) (UInt64.ofNat ni) g)
    let out := (blockBytes e p).extract 0 (r.toNat * sz)
    let ((), e) ← runM e (freeB p)
    return (s!"R{r.toNat}:{toHex out}", e)
  | "gets" =>
    let len ← pi 2
    let (p, e) ← runM e (allocBytes (Array.replicate (if len > 0 then len.toNat else 1) 0))
    let (r, e) ← runG e (gzgets g p (Int32.ofInt len))
    if r == .null then return ("gN", e)
    let b := blockBytes e p
    let n := (b.findIdx? (· == 0)).getD b.size
    return (s!"g{toHex (b.extract 0 n)}", e)
  | "getc" =>
    let (r, e) ← runG e (gzgetc g)
    return (s!"C{r.toInt}", e)
  | "ungetc" =>
    let v ← pi 2
    let (r, e) ← runG e (gzungetc (Int32.ofInt v) g)
    return (s!"u{r.toInt}", e)
  | "seek" =>
    let o ← pi 2
    let w ← pi 3
    let (r, e) ← runG e (gzseek g (Int64.ofInt o) (Int32.ofInt w))
    return (s!"S{r.toInt}", e)
  | "tell" =>
    let (r, e) ← runM e (gztell g)
    return (s!"T{r.toInt}", e)
  | "offset" =>
    let (r, e) ← runG e (gzoffset g)
    return (s!"O{r.toInt}", e)
  | "rewind" =>
    let (r, e) ← runG e (gzrewind g)
    return (s!"rw{r.toInt}", e)
  | "eof" =>
    let (r, e) ← runM e (gzeof g)
    return (s!"E{r.toInt}", e)
  | "direct" =>
    let (r, e) ← runG e (gzdirect g)
    return (s!"Di{r.toInt}", e)
  | "error" =>
    let (en, e) ← runM e (allocBytes (Array.replicate 4 0))
    let (m, e) ← runM e (gzerror g en)
    let num := (blockBytes e en)
    let ev : Int32 := (num[0]!.toUInt32 ||| (num[1]!.toUInt32 <<< 8) ||| (num[2]!.toUInt32 <<< 16) |||
      (num[3]!.toUInt32 <<< 24)).toInt32
    -- gzerror sets *errnum only for a valid file; the C driver pre-sets 12345
    if m == .null then
      return ("e12345:", e)
    let (s, e) ← runM e (cstring m)
    return (s!"e{ev.toInt}:{toHex s}", e)
  | "clearerr" =>
    let (_, e) ← runM e (gzclearerr g)
    return ("ce", e)
  | "close" =>
    let (r, e) ← runG e (gzclose g)
    return (s!"x{r.toInt}", setH e none)
  | "closer" =>
    let (r, e) ← runG e (gzclose_r g)
    return (s!"xr{r.toInt}", setH e none)
  | "closew" =>
    let (r, e) ← runG e (gzclose_w g)
    return (s!"xw{r.toInt}", setH e none)
  | _ => bad s!"unknown op {c}"

def doLine (ops : List String) : String := Id.run do
  let mut e : Env := { fs := {}, h := startHeap, hs := Array.replicate 4 none }
  let mut out : List String := []
  for o in ops do
    match doOp e o with
    | .ok (s, e') =>
      out := out ++ [s]
      e := e'
    | .error f => return String.intercalate "|" out ++ (if out.isEmpty then "" else "|") ++ showFault f
  return String.intercalate "|" out

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "gz", ops => .ok (doLine ops)
  | "unc", (hex :: dl :: rest) => do
    let src ← hexArg hex
    let dlen ← parseNat dl
    let slen ← match rest with | [s] => parseNat s | _ => pure src.size
    let r : Except Fault String := do
      let e : Env := { fs := {}, h := startHeap, hs := #[] }
      let (sp, e) ← runM e (allocBytes (if src.isEmpty then #[0] else src))
      let (dp, e) ← runM e (allocBytes (Array.replicate (max dlen 1) 0))
      let (dlp, e) ← runM e (allocBytes (Array.replicate 8 0))
      let (slp, e) ← runM e (allocBytes (Array.replicate 8 0))
      let (_, e) ← runM e (Zlib.Gzguts.store64 dlp (UInt64.ofNat dlen))
      let (_, e) ← runM e (Zlib.Gzguts.store64 slp (UInt64.ofNat slen))
      let (rc, e) ← runM e (Zlib.Uncompr.uncompress2 dp dlp sp slp)
      let (dl2, e) ← runM e (Zlib.Gzguts.load64 dlp)
      let (sl2, e) ← runM e (Zlib.Gzguts.load64 slp)
      let out := (blockBytes e dp).extract 0 dl2.toNat
      return s!"{rc.toInt}:{dl2.toNat}:{sl2.toNat}:{toHex out}"
    match r with
    | .ok s => .ok s
    | .error f => .ok (showFault f)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

/-- `DiffTest.mainLoop` with a flush after every line (a crash then loses nothing). -/
def mainFlush : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut bad : UInt32 := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    match line.splitOn " " with
    | [] => continue
    | fn :: args =>
      match handle fn args with
      | .ok r => stdout.putStrLn r
      | .error e =>
        IO.eprintln s!"bad input line: {e}"
        bad := 1
        stdout.putStrLn s!"BADINPUT {e}"
      stdout.flush
  return bad

def main : IO UInt32 := mainFlush
