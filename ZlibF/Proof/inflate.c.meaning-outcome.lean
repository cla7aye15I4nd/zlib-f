import ZlibF.Proof.«inflate.c.meaning-loop»
import ZlibF.Proof.«inflate.c.leave-cause-run»

/-!
# inflate.c: what one trip of the mode loop can end in

The loop assembly of `meaning_step` composes per-mode steps whose results are
`TripOutcome`s:

* the trip continues (`break` or fall-through) with `LoopMatches`, or with
  the decoder in `BAD` and the input read so far doomed (`LoopBad`);
* the trip leaves (`goto inf_leave`) with `LoopMatches` (input or output
  exhausted, `Z_BLOCK`), or from `DONE` with `Z_STREAM_END`, or from `BAD`
  with `Z_DATA_ERROR`.

`DICT` without a dictionary returns `Z_NEED_DICT` directly (no `inf_leave`)
and `MEM` returns `Z_MEM_ERROR`; both are handled by the call-level
assembly, not here.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The decoder is in `BAD` after this trip: the configuration and the input
cursor are those of the loop, and no valid full-window stream begins with
the input read so far. -/
def LoopBad (c : Ctx) (f : LoopFrame) (h : Heap) (l : IL) : Prop :=
  ∃ (zs : Nat) (s : InflateState), c.st = some (.tab zs) ∧ h.istates zs = some s ∧
    s.mode = BAD ∧ l.ret = Z_OK ∧ ConfigMatches (loopState s l) f.wrap f.configured ∧
    l.have_.toNat ≤ l.in_.toNat ∧ l.in_.toNat = f.inp.length ∧ LoopDoomed f l

/-- The possible ends of one trip of the mode loop (one `inflate_dispatch`). -/
def TripOutcome (c : Ctx) (f : LoopFrame) (result : Except Ex Unit) (h : Heap) (l : IL) : Prop :=
  (result = .ok () ∧ (LoopMatches c f h l ∨ LoopBad c f h l)) ∨
  (result = .error Ex.leave ∧
    (LoopMatches c f h l ∨
     (l.ret = Z_STREAM_END ∧ LoopMatches c f h { l with ret := Z_OK }) ∨
     (l.ret = Z_DATA_ERROR ∧ LoopBad c f h { l with ret := Z_OK })))

/-- `case BAD:` sets `Z_DATA_ERROR` and leaves. -/
theorem bad_trip {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (bad : LoopBad c f h l) (strm : c.strm = some r) (hz : r.get h = some z) :
    runX (inflate_dispatch c) l h = .ok ((.error .leave, { l with ret := Z_DATA_ERROR }), h) ∧
      TripOutcome c f (.error .leave) h { l with ret := Z_DATA_ERROR } := by
  obtain ⟨zs, s, st, hs, mode, retOk, rest⟩ := bad
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  refine ⟨inflate_dispatch_BAD_leave E l mode, Or.inr ⟨rfl, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩⟩
  have same : ({ { l with ret := Z_DATA_ERROR } with ret := Z_OK } : IL) = l := by
    cases l
    simp only at retOk ⊢
    rw [retOk]
  rw [same]
  exact ⟨zs, s, st, hs, mode, retOk, rest⟩

#print axioms bad_trip

end Zlib.Inflate.Proofs
