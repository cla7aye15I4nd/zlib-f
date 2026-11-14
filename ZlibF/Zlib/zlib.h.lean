import ZlibF.Zlib.«gzread.c»

/-!
# zlib.h — the macros with a body

Default x86_64 Linux build: `Z_PREFIX_SET` is undefined, so the `gzgetc` macro is the one defined under
`#else` (`zlib.h`, "gzgetc() macro and its supporting function and exposed data structure").

Decisions:

* `struct gzFile_s` is the field `x` of `gz_state`, its first member. A `gzFile` is `GzFilePtr`
  (`some (.in_gzstate_x id)`); `(g)->f` is the field `x.f` of the record that `castState g` names, as in the
  translations of `gzread.c`. A NULL `g` is dereferenced by the macro: `ldS` raises `Fault.ub`.
* `(gzgetc)(g)`: the parentheses suppress the macro, so this is the function `gzgetc` of `gzread.c`
  (`Zlib.Gzread.gzgetc`).
* The operands of the comma operator are evaluated in order. `*((g)->next)++` loads the byte at the old `next`
  and stores `next + 1`; the result is the byte promoted to `int`.
-/

namespace Zlib.ZlibH
open C Zlib.GzFs Zlib.Gzguts

/-- `#define gzgetc(g) ((g)->have ? ((g)->have--, (g)->pos++, *((g)->next)++) : (gzgetc)(g))`

The macro, used as `gzgetc(g)` by an application that includes `zlib.h`. The inline branch changes `have`,
`pos` and `next` with no library call; unlike the function it never clears `err` or `msg`. -/
def gzgetc (g : GzFilePtr) : G Int32 := do
  let state := castState g
  -- (g)->have ?
  let s ← ldS state
  if s.x.«have» != 0 then
    -- (g)->have--,
    updX state fun x => { x with «have» := x.«have» - 1 }
    -- (g)->pos++,
    let np ← i64add s.x.pos 1
    updX state fun x => { x with pos := np }
    -- *((g)->next)++
    let s ← ldS state
    let b ← load8 s.x.next
    let nx ← s.x.next.add 1
    updX state fun x => { x with next := nx }
    return b.toUInt32.toInt32
  -- : (gzgetc)(g)
  Zlib.Gzread.gzgetc g

end Zlib.ZlibH
