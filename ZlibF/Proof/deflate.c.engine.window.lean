/-!
# deflate.c, engine: the window arithmetic of `fill_window` and `longest_match`

Statements about natural numbers. `ws` is `w_size` (512 to 32768, a power of two), the window has `2 * ws` bytes,
`ss` is `strstart`, `la` is `lookahead`, `MIN_LOOKAHEAD = 262`, `MAX_DIST = ws - 262`, `MAX_MATCH = 258`.

**D**, the window range: `ss + la <= 2 * ws`.

These are the numeric facts of `docs/proof/deflate.md` section 3: the slide test, the slide copy, the room left
after `fill_window`, the `high_water` clearing, and the margins that keep every read of `longest_match` inside the
window.
-/

namespace Zlib.Deflate.Engine.Proofs

/-! ## The slide of `fill_window` -/

/-- The amount `fill_window` slides by: `ws` when `strstart >= ws + MAX_DIST = 2 * ws - 262`, else `0`. -/
def fillD (ws ss : Nat) : Nat := if 2 * ws - 262 ≤ ss then ws else 0

/-- The number of bytes `fill_window` reads when `a` bytes of input are available: the first pass reads
`MIN(avail_in, more)` with `more = window_size - lookahead - strstart'`. (Later passes of the `do` loop read
further bytes only while `lookahead < MIN_LOOKAHEAD`; this is the first pass.) -/
def fillL (ws la ss a : Nat) : Nat := min a (2 * ws - la - (ss - fillD ws ss))

/-- `insert` after one pass of `fill_window`: the slide clamps it to `strstart' = ss - D`; if bytes were read and
`lookahead' + insert >= MIN_MATCH` the insertion loop runs until `insert = 0` or `lookahead' + insert < MIN_MATCH`,
leaving `MIN_MATCH - 1 - lookahead'` (truncated at 0). -/
def fillIns (ins ss D la L : Nat) : Nat :=
  if L = 0 ∨ la + L + min ins (ss - D) < 3 then min ins (ss - D) else 2 - (la + L)

/-- `high_water` after `fill_window` (`W = window_size`, `curr = strstart + lookahead` after the read): when
below `W` it is raised to at least `MIN(curr + WIN_INIT, W)`. -/
def fillHW (hw W curr : Nat) : Nat := if hw < W then max hw (min (curr + 258) W) else hw

theorem fillD_cases (ws ss : Nat) : (fillD ws ss = ws ∧ 2 * ws - 262 ≤ ss) ∨ (fillD ws ss = 0 ∧ ss < 2 * ws - 262) := by
  unfold fillD; split <;> omega

/-- **Lemma 1** (`I-fw-post-room`). Whenever `fill_window` returns, `strstart < window_size - MIN_LOOKAHEAD`. -/
theorem fill_post_room {ws ss la : Nat} (hws : 512 ≤ ws) (hD : ss + la ≤ 2 * ws) :
    ss - fillD ws ss < 2 * ws - 262 := by
  unfold fillD; split <;> omega

/-- The first read ends inside the window. -/
theorem fill_fit {ws ss la a : Nat} (hws : 512 ≤ ws) (hD : ss + la ≤ 2 * ws) :
    (ss - fillD ws ss) + la + fillL ws la ss a ≤ 2 * ws := by
  unfold fillL fillD; split <;> omega

/-- The slide: `more = window_size - lookahead - strstart` is at most `262` when the slide test holds, so
`wsize - more` is a proper count and the copy `[ws, 2 * ws - more) -> [0, ws - more)` is inside the window and
its two ranges do not overlap. Its length is `strstart + lookahead - ws`: the valid data moves down by `ws`. -/
theorem slide_copy {ws ss la : Nat} (hws : 512 ≤ ws) (hD : ss + la ≤ 2 * ws) (ht : 2 * ws - 262 ≤ ss) :
    let more := 2 * ws - la - ss
    more ≤ 262 ∧ more ≤ ws ∧ ws - more = ss + la - ws ∧ ws + (ws - more) ≤ 2 * ws ∧ ws - more ≤ ws ∧
      ws ≤ ss ∧ (ss - ws) + la ≤ ws := by
  intro more
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- After the slide `more + ws` is the room left: `window_size - lookahead - strstart'`. -/
theorem slide_more {ws ss la : Nat} (hws : 512 ≤ ws) (hD : ss + la ≤ 2 * ws) (ht : 2 * ws - 262 ≤ ss) :
    2 * ws - la - ss + ws = 2 * ws - la - (ss - ws) := by omega

/-- The slide test in `unsigned` arithmetic: no wrap in `wsize + (w_size - MIN_LOOKAHEAD)`. -/
theorem slide_test_nat {ws ss : Nat} (hws : 512 ≤ ws) (hle : ws ≤ 32768) :
    ws + (ws - 262) = 2 * ws - 262 ∧ ws + (ws - 262) < 2 ^ 32 := by
  constructor <;> omega

/-! ## The `high_water` clearing -/

/-- First branch (`high_water < curr`): `init = MIN(window_size - curr, WIN_INIT)`, the cleared range
`[curr, curr + init)` is inside the window, and the new `high_water = curr + init` is `fillHW`. -/
theorem hw_branch1 {hw W curr init : Nat} (hc : curr ≤ W) (h1 : hw < curr) (hi : init = min (W - curr) 258) :
    curr + init ≤ W ∧ curr + init = fillHW hw W curr := by
  unfold fillHW
  rw [if_pos (by omega)]
  constructor <;> omega

/-- Second branch (`curr <= high_water < curr + WIN_INIT`): `init` is the smaller of `curr + WIN_INIT - high_water`
and `window_size - high_water`; the cleared range `[high_water, high_water + init)` is inside the window and the
new `high_water` is `fillHW`. -/
theorem hw_branch2 {hw W curr init : Nat} (hc : curr ≤ W) (h1 : hw < W) (h2 : curr ≤ hw) (h3 : hw < curr + 258)
    (hi : init = min (curr + 258 - hw) (W - hw)) :
    hw + init ≤ W ∧ hw + init = fillHW hw W curr := by
  unfold fillHW
  rw [if_pos h1]
  constructor <;> omega

theorem fillHW_le {hw W curr : Nat} (hhw : hw ≤ W) : fillHW hw W curr ≤ W := by
  unfold fillHW; split <;> omega

theorem fillHW_ge (hw W curr : Nat) : hw ≤ fillHW hw W curr := by
  unfold fillHW; split <;> omega

/-! ## The margins of `longest_match` -/

/-- `longest_match` is called with `strstart <= window_size - MIN_LOOKAHEAD`. Then `scan + MAX_MATCH` (`strend`) and
the reads `scan[best_len]` (`best_len <= MAX_MATCH`) and `match[best_len]` stay inside the window, for every match
position `cur_match <= strstart`. -/
theorem lm_margin {ws ss c : Nat} (hss : ss ≤ 2 * ws - 262) (hc : c ≤ ss) (hws : 512 ≤ ws) :
    ss + 258 < 2 * ws ∧ c + 258 < 2 * ws ∧ ss + 259 ≤ 2 * ws := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The caller's facts give the margin: either `lookahead >= MIN_LOOKAHEAD` and (D) gives
`strstart <= window_size - MIN_LOOKAHEAD`, or `fill_window` has just run (`fill_post_room`). -/
theorem caller_margin {ws ss la : Nat} (hD : ss + la ≤ 2 * ws) (hla : 262 ≤ la) :
    ss ≤ 2 * ws - 262 := by omega

/-- `limit = strstart > MAX_DIST ? strstart - MAX_DIST : NIL`: every chain position above `limit` is within
`MAX_DIST` of `strstart`. -/
theorem limit_dist {ws ss p : Nat} (hlim : (if ss > ws - 262 then ss - (ws - 262) else 0) < p) (hp : p ≤ ss)
    (hws : 512 ≤ ws) : ss - p ≤ ws - 262 := by
  split at hlim <;> omega

end Zlib.Deflate.Engine.Proofs
