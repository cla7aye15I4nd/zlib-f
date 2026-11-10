import ZlibF.Proof.«inflate.c.input-base-run»
import ZlibF.Proof.«inflate.c.input-base-modes»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false



theorem inflate_loop_input_base {context : Ctx} {l regs : IL} {h after : Heap} {outcome : Except Ex Unit}
    (run : runX (xwhile (pure true) (inflate_dispatch context)) l h = .ok ((outcome, regs), after)) :
    regs.in_ = l.in_ := inputBaseX_inflate_loop l.in_ context l h outcome regs after rfl run

end Zlib.Inflate.Proofs
