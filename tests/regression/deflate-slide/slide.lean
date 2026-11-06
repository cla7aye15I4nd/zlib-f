import ZlibF.Zlib.«deflate_base.c»

/-! Internal-state boundary checks of the actual translated fill_window.
The overflowing state is artificial. API reachability is not asserted. -/

namespace SlideRegression
open C Zlib.Deflate

def state (start : Int64) : DeflateState :=
  { DeflateState.zeroed with
    strm := some (.tab 0), w_size := 512, w_mask := 511, window_size := 1024,
    hash_size := 256, strstart := 762, block_start := start,
    window := .ref (.blk 2) 0, head := .ref (.blk 3) 0, prev := .ref (.blk 4) 0 }

def heap (start : Int64) : Heap :=
  { Heap.empty with
    streams := upd Tbl.empty 0 (some ZStream.zeroed),
    dstates := upd Tbl.empty 1 (some (state start)),
    bytes := upd Tbl.empty 2 (some (Array.replicate 1024 0)),
    words := upd (upd Tbl.empty 3 (some (Array.replicate 256 0))) 4 (some (Array.replicate 512 0)),
    nextBlk := 5 }

def observe (start : Int64) : String :=
  match C.run (fill_window (some (.tab 1))) (heap start) with
  | .error (.ub message) => s!"UB: {message}"
  | .error .outOfFuel => "out of fuel"
  | .ok (_, h) => match h.dstates 1 with
    | none => "missing state"
    | some d => s!"block_start={d.block_start.toInt} strstart={d.strstart.toNat} high_water={d.high_water.toNat}"

end SlideRegression

def main : IO Unit := do
  for start in ([0, -9223372036854775296, 9223372036854775807, -9223372036854775808] : List Int64) do
    IO.println (SlideRegression.observe start)
