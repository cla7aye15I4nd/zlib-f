import ZlibF.Proof.«infback.c.safety-lookup2»

/-!
# infback.c: `case LEN` split at its lookups

`back_LEN` (`back_LEN_eq`, by `rfl`): the fast path; the literal/length lookup; `lenSym` (the
symbol: literal, end of block, invalid, or a length and its extra bits); `lenDist` (the distance
lookup); `distSym` (the distance, its extra bits); `lenCopy` (the distance check and the copy
through the window).
-/

namespace Zlib.Infback.Safety
open C Zlib.Inflate Zlib.Infback Zlib.Inftrees
open Zlib.Inffast (inflate_fast)
set_option autoImplicit false

/-- The distance check and the copy of the match through the window. -/
def lenCopy (c : BCtx) : X Unit := do
  let s ← ldInflateState c.st
  let l ← get
  if s.offset > s.wsize - (if s.whave < s.wsize then l.left else 0) then
    badMode c "invalid distance too far back"
    return
  -- do { ROOM(); copy = state->wsize - state->offset; ...; do { *put++ = *from++; } while (--copy); } while (state->length != 0);
  xdoWhile
    (do
      ROOM c
      let s ← ldInflateState c.st
      let l ← get
      -- copy = state->wsize - state->offset;
      let copy := s.wsize - s.offset
      -- if (copy < left) { from = put + copy; copy = left - copy; } else { from = put - state->offset; copy = left; }
      let (from_, copy) ← if copy < l.left then do
          pure (← l.put.add (copy.toNat : Int), l.left - copy)
        else do
          pure (← l.put.add (-(s.offset.toNat : Int)), l.left)
      -- if (copy > state->length) copy = state->length;
      let copy := if copy > s.length then s.length else copy
      -- state->length -= copy; left -= copy;
      wrS c.st fun s => { s with length := s.length - copy }
      set { l with copy := copy, from_ := from_, left := l.left - copy }
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
          return n != 0))
    (do return (← rdS c.st (·.length)) != 0)

/-- The distance symbol: `DROPBITS(here.bits)`, the invalid code, the distance and its extra bits. -/
def distSym (c : BCtx) : X Unit := do
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  -- if (here.op & 64) { "invalid distance code"; BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  -- state->offset = (unsigned)here.val; state->extra = (unsigned)(here.op) & 15;
  wrS c.st fun s => { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 }
  let ex := here.op.toUInt32 &&& 15
  if ex != 0 then
    NEEDBITS c ex
    let b ← BITS ex
    wrS c.st fun s => { s with offset := s.offset + b }
    DROPBITS ex
  lenCopy c

/-- The distance lookup. -/
def lenDist (c : BCtx) : X Unit := do
  lookup1 c true
  let here := (← get).here
  if (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c true
    DROPBITS (← get).last.bits.toUInt32
  distSym c

/-- The literal/length symbol after its lookup. -/
def lenSym (c : BCtx) : X Unit := do
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  wrS c.st fun s => { s with length := here.val.toUInt32 }
  -- if (here.op == 0) { ROOM(); *put++ = (unsigned char)(state->length); left--; state->mode = LEN; break; }
  if here.op == 0 then
    ROOM c
    let l ← get
    store8 l.put (← ldInflateState c.st).length.toUInt8
    let p ← l.put.add 1
    set { l with put := p, left := l.left - 1 }
    setMode c.st LEN
    return
  -- if (here.op & 32) { state->mode = TYPE; break; }
  if (here.op &&& 32) != 0 then
    setMode c.st TYPE
    return
  -- if (here.op & 64) { "invalid literal/length code"; BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  -- state->extra = (unsigned)(here.op) & 15; if (state->extra != 0) { NEEDBITS; length += BITS(extra); DROPBITS(extra); }
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15 }
  let ex := here.op.toUInt32 &&& 15
  if ex != 0 then
    NEEDBITS c ex
    let b ← BITS ex
    wrS c.st fun s => { s with length := s.length + b }
    DROPBITS ex
  lenDist c

theorem back_LEN_eq (c : BCtx) : back_LEN c = (do
  let l ← get
  -- if (have >= 6 && left >= 258) { RESTORE(); inflate_fast(strm, state->wsize); LOAD(); break; }
  if l.have_ >= 6 && l.left >= 258 then
    RESTORE c.strm c.st
    inflate_fast c.strm (← rdS c.st (·.wsize))
    LOAD c.strm c.st
    return
  lookup1 c false
  let here := (← get).here
  -- if (here.op && (here.op & 0xf0) == 0) {
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    DROPBITS (← get).last.bits.toUInt32
  -- DROPBITS(here.bits); state->length = (unsigned)here.val;
  lenSym c) := rfl

end Zlib.Infback.Safety
