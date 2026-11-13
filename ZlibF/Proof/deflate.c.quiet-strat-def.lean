import ZlibF.Proof.«deflate.c.quiet-phi»
import ZlibF.Proof.«deflate.c.universal-call-dispatch»

/-!
# deflate.c: what a strategy run with no input does to the potential (`DeflateQuiet`)

`StratQuiet flush z d z1 d1 b` relates the state before a strategy run (`z`, `d`) with no input to the
state after it (`z1`, `d1`) and its result `b`:
1. the work term of the potential does not rise (`work d1 ≤ work d`);
2. if it stays equal, the run ended the stream's data (`finish_started`, `finish_done`) or it produced
   nothing (no output byte, nothing pending);
3. `need_more` with output room left leaves nothing pending, and the flush was not `Z_FINISH`;
4. `finish_started` leaves the output full;
5. `gzindex` is kept.
On the real C every strategy step lowers the work term (3·lookahead + 2·[match_available] +
[sym_next ≠ 0], plus `strstart − block_start` at level 0): a lookahead iteration costs 3 and adds at most
2, the last literal of a lazy match costs 2 and adds 1, a block flush clears `sym_next`.
-/

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

structure StratQuiet (flush : Int32) (z : ZStream) (d : DeflateState) (z1 : ZStream) (d1 : DeflateState)
    (b : block_state) : Prop where
  le : work d1 ≤ work d
  eq : work d1 = work d → b = finish_started ∨ b = finish_done ∨ (z1.avail_out = z.avail_out ∧ d1.pending = 0)
  more : b = need_more → z1.avail_out ≠ 0 → d1.pending = 0 ∧ flush ≠ Z_FINISH
  started : b = finish_started → z1.avail_out = 0
  gzindex : d1.gzindex = d.gzindex

end Zlib.Deflate.Universal.Quiet
