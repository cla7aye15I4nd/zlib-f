import ZlibF.Runtime.Alloc

/-!
# Shared parts of the Lean differential-test drivers

Input format (one test case per line, fields separated by single spaces; blank lines are skipped):

* a function name, then its arguments;
* an unsigned integer is written in decimal, a signed one in decimal with an optional `-`;
* a buffer is `null:<len>` (a NULL pointer, with the length that is passed with it) or
  `hex:<hexdigits>` (a non-NULL pointer to that many bytes; the empty string is a valid pointer to
  zero bytes).

Output: one line per input line: the result in decimal, or `FAULT ...` if the Lean translation
raised a fault. The C side never faults, so a fault is always a difference.
-/

namespace DiffTest

/-- A buffer argument. -/
inductive Buf where
  | null (len : Nat)
  | bytes (b : Array UInt8)

def hexVal (c : UInt8) : Option UInt8 :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 97 + 10)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 65 + 10)
  else none

def parseHex (s : String) : Except String (Array UInt8) := do
  let cs := s.toUTF8
  if cs.size % 2 != 0 then throw "odd number of hex digits"
  let mut out : Array UInt8 := #[]
  for i in [0:cs.size / 2] do
    match hexVal cs[2 * i]!, hexVal cs[2 * i + 1]! with
    | some hi, some lo => out := out.push (hi * 16 + lo)
    | _, _ => throw "bad hex digit"
  return out

def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"bad unsigned number {s}"

def parseU64 (s : String) : Except String UInt64 := do
  let n ← parseNat s
  if n < 2 ^ 64 then pure (UInt64.ofNat n) else throw s!"out of range for uint64: {s}"

def parseI64 (s : String) : Except String Int64 :=
  match s.toInt? with
  | some n =>
    if -(2 ^ 63 : Int) ≤ n ∧ n < 2 ^ 63 then pure (Int64.ofInt n)
    else throw s!"out of range for int64: {s}"
  | none => throw s!"bad signed number {s}"

def parseBuf (s : String) : Except String Buf :=
  if s.startsWith "null:" then do
    return .null (← parseNat (s.drop 5).toString)
  else if s.startsWith "hex:" then do
    return .bytes (← parseHex (s.drop 4).toString)
  else throw s!"bad buffer {s}"

def showFault : C.Fault → String
  | .ub w => s!"FAULT ub {w}"
  | .outOfFuel => "FAULT outOfFuel"

/-- Run a translated function on a fresh heap and print its `UInt64` result. -/
def showResult (r : Except C.Fault (UInt64 × C.Heap)) : String :=
  match r with
  | .ok (v, _) => toString v.toNat
  | .error f => showFault f

/-- Allocate the buffer on a fresh heap and call `f ptr len`. -/
def withBuf (b : Buf) (f : C.BPtr → Nat → C.M UInt64) : String :=
  showResult <| C.run (h := C.Heap.empty) (do
    match b with
    | .null len => f .null len
    | .bytes bs => do
      let p ← C.allocBytes bs
      f p bs.size)

/-- Read stdin line by line, handle each non-blank line, print one result line each. -/
def mainLoop (handle : String → List String → Except String String) : IO UInt32 := do
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

end DiffTest
