import ZlibF.Proof.«deflate.c.universal-call-keep-phases»

/-!
# deflate.c: what phases 2 to 4 of `deflate` return

Owner 2 of the deflate split (`deflate_call`). The header, strategy and trailer phases
(`deflate.c.universal-call-phases`) return `Z_OK` or `Z_STREAM_END` on every returning run: the
refusals (`Z_STREAM_ERROR`, `Z_BUF_ERROR`) are all in the entry phase.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal.Call
open Zlib.Trees.KeepProofs (Yields Yields.pure Yields.ub Yields.trivial Yields.bind Yields.ite)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The return codes of phases 2 to 4. -/
def RcOk (rc : Int32) : Prop := rc = Z_OK ∨ rc = Z_STREAM_END

theorem rcOk_ite (c : Prop) [Decidable c] : RcOk (if c then Z_OK else Z_STREAM_END) := by
  unfold RcOk; split <;> simp

macro "rc_step" : tactic => `(tactic|
  first
    | with_reducible exact Yields.ub _
    | (with_reducible apply Yields.bind (Yields.trivial _); intro _ _)
    | with_reducible apply Yields.ite
    | split
    | dsimp only
    | exact Yields.pure (Or.inl rfl)
    | exact Yields.pure (Or.inr rfl)
    | exact Yields.pure (rcOk_ite _))

theorem rc_trailerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) :
    Yields RcOk (trailerPhase strm s flush) := by
  unfold trailerPhase
  repeat' rc_step

theorem rc_strategyPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32)
    (hk : Yields RcOk k) : Yields RcOk (strategyPhase strm s flush k) := by
  unfold strategyPhase
  repeat' first
    | exact hk
    | rc_step

theorem rc_headerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32)
    (hk : Yields RcOk k) : Yields RcOk (headerPhase strm s flush k) := by
  unfold headerPhase
  repeat' first
    | exact hk
    | rc_step

/-- Phases 2 to 4 return `Z_OK` or `Z_STREAM_END`. -/
theorem rc_after_entry (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) :
    Yields RcOk (headerPhase strm s flush (strategyPhase strm s flush (trailerPhase strm s flush))) :=
  rc_headerPhase _ _ _ _ (rc_strategyPhase _ _ _ _ (rc_trailerPhase _ _ _))

end Zlib.Deflate.Universal.Keep
