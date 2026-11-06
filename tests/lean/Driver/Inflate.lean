import ZlibF.Zlib.«inflate.c»
import ZlibF.Zlib.«crc32.c»
import DiffTest.Common

/-!
Lean side of the differential test for `inflate.c`. It calls the translation in `ZlibF/Zlib/inflate.c.lean` (the module
the proofs are about) and does the same calls, in the same order, as `tests/c/inflate.c`; see that file for the format
of a case and of the output line. The driver builds the stream, the input chunks, the output buffers and the gzip header
buffers on the Lean heap, and prints what the C driver prints.

`flatten` is a driver-only step: the heap is a function updated by closures, so a long run would make every lookup walk a
long chain. Between two calls of `inflate` it rebuilds the tables as finite maps of the same content.
-/

open DiffTest C Zlib.Inflate

/-- The heap of the test: nothing allocated, the static tables of `crc32.c` and `inftrees.c` set. -/
def heap0 : Heap :=
  { Heap.empty with static := Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics default) }

/-- Same heap, tables rebuilt with exactly the block numbers below `nextBlk` (driver only). -/
def flatten : M Unit := fun h =>
  let n := h.nextBlk
  let bs := Array.ofFn (n := n) fun i => h.bytes i.val
  let ws := Array.ofFn (n := n) fun i => h.words i.val
  let ro := Array.ofFn (n := n) fun i => h.ro i.val
  let zs := Array.ofFn (n := n) fun i => h.streams i.val
  let gh := Array.ofFn (n := n) fun i => h.gzheaders i.val
  let ds := Array.ofFn (n := n) fun i => h.dstates i.val
  let is := Array.ofFn (n := n) fun i => h.istates i.val
  let gs := Array.ofFn (n := n) fun i => h.gzstates i.val
  .ok ((), { h with
    bytes := ⟨bs⟩
    words := ⟨ws⟩
    ro := ⟨ro⟩
    streams := ⟨zs⟩
    gzheaders := ⟨gh⟩
    dstates := ⟨ds⟩
    istates := ⟨is⟩
    gzstates := ⟨gs⟩ })

def hexDigit (n : UInt8) : String := String.singleton (Char.ofNat (if n < 10 then 48 + n.toNat else 87 + n.toNat))

def hexs (bs : Array UInt8) : String :=
  bs.foldl (fun (acc : String) (b : UInt8) => acc ++ hexDigit (b >>> 4) ++ hexDigit (b &&& 15)) ""

/-- `n` bytes from `p`. -/
def readBytes (p : BPtr) (n : Nat) : M (Array UInt8) := do
  let mut a : Array UInt8 := #[]
  for i in [0:n] do
    a := a.push (← index8 p i)
  return a

/-- The NUL-terminated string at `p` (at most `max` bytes) as hex; `-` for NULL, `~` for the empty string. -/
def cstrHex (p : BPtr) (max : Nat) : M String := do
  if p == .null then return "-"
  let mut a : Array UInt8 := #[]
  for i in [0:max] do
    let b ← index8 p i
    if b == 0 then break
    a := a.push b
  return if a.isEmpty then "~" else hexs a

structure Cfg where
  wb : Int32
  inch : Nat
  outch : Nat
  flush : Int32
  opts : Nat
  dict : Array UInt8
  input : Array UInt8
  z2 : ZStreamPtr

structure LS where
  zs : ZStreamPtr
  pos : Nat
  calls : Nat
  out : String
  tr : String
  final : Int32
  copied : Bool
  chunk : BPtr

def loop (c : Cfg) : Nat → LS → M LS
  | 0, s => pure s
  | fuel + 1, s => do
    flatten
    let mut s := s
    -- if (zs->avail_in == 0 && pos < ilen) { a fresh chunk }
    let z ← ldZStream s.zs
    if z.avail_in == 0 && s.pos < c.input.size then
      let n := min c.inch (c.input.size - s.pos)
      freeB s.chunk
      let p ← allocBytes (c.input.extract s.pos (s.pos + n))
      wrZ s.zs fun z => { z with next_in := p, avail_in := n.toUInt32 }
      s := { s with chunk := p, pos := s.pos + n }
    let ob ← allocBytes (Array.replicate c.outch 0)
    wrZ s.zs fun z => { z with next_out := ob, avail_out := c.outch.toUInt32 }
    let ret ← inflate s.zs c.flush
    let z ← ldZStream s.zs
    let produced := c.outch - z.avail_out.toNat
    let pb ← readBytes ob produced
    freeB ob
    s := { s with out := s.out ++ hexs pb, calls := s.calls + 1, final := ret }
    if s.calls <= 24 then
      s := { s with tr := s.tr ++ s!"{ret.toInt}:{z.avail_in.toNat}:{produced};" }
    if ret == Z_NEED_DICT then
      if c.dict.size != 0 then
        let dp ← allocBytes c.dict
        let r2 ← inflateSetDictionary s.zs dp c.dict.size.toUInt32
        if s.calls <= 24 then s := { s with tr := s.tr ++ s!"d{r2.toInt};" }
        if r2 != Z_OK then return s
        return (← loop c fuel s)
      return s
    if ret == Z_STREAM_END then return s
    if ret < 0 && ret != Z_BUF_ERROR then return s
    if ret == Z_BUF_ERROR && z.avail_in == 0 && s.pos ≥ c.input.size then return s
    if c.opts &&& 2 != 0 && s.calls == 2 && !s.copied then
      s := { s with copied := true }
      let rc ← inflateCopy c.z2 s.zs
      s := { s with tr := s.tr ++ s!"c{rc.toInt};" }
      let _ ← inflateEnd s.zs
      s := { s with zs := c.z2 }
    if s.calls ≥ 20000 then return s
    loop c fuel s

def zeroStream : M ZStreamPtr := do
  let p ← allocZStream
  stZStream p (ZStream.zeroed)
  return p

def runCase (c : Cfg) : M String := do
  let s1 ← zeroStream
  let c := { c with z2 := ← zeroStream }
  let ver ← allocBytesRO ("1.3.2.1-motley".toUTF8.data.push 0)
  let init ← inflateInit2_ s1 c.wb ver 112
  let mut line := s!"init={init.toInt}"
  if init != Z_OK then return line
  let extra ← allocBytes (Array.replicate 64 0)
  let name ← allocBytes (Array.replicate 64 0)
  let comm ← allocBytes (Array.replicate 64 0)
  let head ← allocGzHeader
  stGzHeader head { GzHeader.zeroed with
    extra := extra, extra_max := 64, name := name, name_max := 64, comment := comm, comm_max := 64 }
  let mut hd : Int32 := -99
  if c.opts &&& 32 != 0 then line := line ++ s!" val={(← inflateValidate s1 0).toInt}"
  if c.opts &&& 8 != 0 then line := line ++ s!" prime={(← inflatePrime s1 3 5).toInt}"
  if c.opts &&& 1 != 0 then hd ← inflateGetHeader s1 head
  if c.opts &&& 16 != 0 && c.dict.size != 0 then
    let dp ← allocBytes c.dict
    line := line ++ s!" sd0={(← inflateSetDictionary s1 dp c.dict.size.toUInt32).toInt}"
  let s ← loop c 20000 { zs := s1, pos := 0, calls := 0, out := "", tr := "", final := 0, copied := false, chunk := .null }
  let mut tr := s.tr
  let zs := s.zs
  if c.opts &&& 64 != 0 && s.final == Z_DATA_ERROR then
    let r3 ← inflateSync zs
    tr := tr ++ s!"sync{r3.toInt};"
    tr := tr ++ s!"sin{(← rdZ zs (·.avail_in)).toNat};"
    tr := tr ++ s!"mode{(← inflateSyncPoint zs).toInt};"
  let z ← ldZStream zs
  line := line ++ s!" rc={s.final.toInt} calls={s.calls} tin={z.total_in.toInt64.toInt} tout={z.total_out.toInt64.toInt}"
  line := line ++ s!" adler={z.adler.toInt64.toInt} dt={z.data_type.toInt}"
  line := line ++ s!" msg={← cstrHex z.msg 64}"
  line := line ++ s!" mark={(← inflateMark zs).toInt} sp={(← inflateSyncPoint zs).toInt}"
  line := line ++ s!" cu={(← inflateCodesUsed zs).toInt64.toInt}"
  if c.opts &&& 1 != 0 then
    let g ← ldGzHeader head
    line := line ++ s!" hd={hd.toInt} h={g.done.toInt},{g.text.toInt},{g.time.toInt64.toInt},{g.xflags.toInt},{g.os.toInt},{g.hcrc.toInt},{g.extra_len.toNat},"
    line := line ++ hexs (← readBytes extra (min g.extra_len.toNat 64))
    line := line ++ "," ++ (← cstrHex name 64) ++ "," ++ (← cstrHex comm 64)
    line := line ++ (if g.extra == .null then ",xn" else ",xp") ++ (if g.name == .null then "n" else "p") ++
      (if g.comment == .null then "n" else "p")
  if c.opts &&& 4 != 0 then
    let dbuf ← allocBytes (Array.replicate 32768 0)
    let (gd, dl) ← inflateGetDictionary zs dbuf (some 12345)
    let dl := dl.getD 0
    line := line ++ s!" gd={gd.toInt}:{dl.toNat}:" ++ hexs (← readBytes dbuf (if dl.toNat ≤ 32768 then dl.toNat else 0))
  line := line ++ s!" tr={tr} out={s.out}"
  let _ ← inflateEnd zs
  return line

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "inflate", [wb, inch, outch, flush, opts, dict, input] => do
    let wb ← parseI64 wb
    let inch ← parseNat inch
    let outch ← parseNat outch
    let flush ← parseI64 flush
    let opts ← parseNat opts
    let dict ← match ← parseBuf dict with
      | .bytes b => pure b
      | .null _ => throw "null dictionary"
    let input ← match ← parseBuf input with
      | .bytes b => pure b
      | .null _ => throw "null input"
    if outch == 0 then throw "outch must be positive"
    let inch := if inch == 0 then max input.size 1 else inch
    let cfg : Cfg := { wb := wb.toInt32, inch, outch, flush := flush.toInt32, opts, dict, input, z2 := none }
    return match C.run (runCase cfg) heap0 with
      | .ok (s, _) => s
      | .error f => showFault f
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
