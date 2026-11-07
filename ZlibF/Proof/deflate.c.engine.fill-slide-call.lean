import ZlibF.Proof.«deflate.c.engine.fill-slide-invariant»
import ZlibF.Proof.«deflate.c.engine.fill-caller»

/-! # Composing the sliding prefix with the rest of the real fill call -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- After equal first body evaluations, the rest of the actual do-while
is identical, including its condition, heap and remaining fuel. -/
theorem do_first_body_eq {α : Type} {body : α → M α} {cond : α → M (Bool × α)}
    {h g : Heap} {start : α} (same : body start h = body start g) :
    cdoWhile body cond start h = cdoWhile body cond start g := by
  unfold cdoWhile
  change cdoWhile.go body cond (18446744073709551615 + 1) start h =
    cdoWhile.go body cond (18446744073709551615 + 1) start g
  conv => lhs; rw [cdoWhile.go, bind_app]
  conv => rhs; rw [cdoWhile.go, bind_app]
  rw [same]

/-- The source's more += wsize is the real free room after moving data. -/
theorem slide_more_eq {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (sizeP : pa'.size = pa.size) (sizeH : qa'.size = qa.size)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    fillMore (slideState d) = fillMore d + d.w_size := by
  have counts := fill_slide_counts good env.win env.wbytes range taken
  have afterGood := slide_good good env sizeP sizeH
  have get : (slideHeap h ds w p q d wa pa' qa').bytes w = some (slideWindow d wa) := by simp [slideHeap]
  have afterRange : fillEnd (slideState d) ≤ (slideState d).window_size.toNat := by
    change fillEnd (slideState d) ≤ d.window_size.toNat
    have wsz := good.inv.wsz
    omega
  apply UInt32.toNat_inj.mp
  rw [fill_more_nat afterGood env.win get afterRange]
  exact counts.2.2.2.2.2.2.2.1.symm

/-- Executing the sliding prefix first leaves exactly the remainder of
the real fill_window call. This is equality of complete computations,
not an assumed successful return or a replacement loop model. -/
theorem fill_window_slide_transfer {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (good : DGood h r ds z d) (env : HashEnv h d w q p wa qa pa)
    (sizeP : pa'.size = pa.size) (sizeH : qa'.size = qa.size)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (prefixRun : fillSlide (some (.tab ds)) d d.w_size (fillMore d) h =
      .ok ((), slideHeap h ds w p q d wa pa' qa')) :
    fill_window (some (.tab ds)) h = fill_window (some (.tab ds)) (slideHeap h ds w p q d wa pa' qa') := by
  let hs := slideHeap h ds w p q d wa pa' qa'
  have afterGood : DGood hs r ds z (slideState d) := slide_good good env sizeP sizeH
  have counts := fill_slide_counts good env.win env.wbytes range taken
  have noSlide := counts.2.2.2.2.2.2.2.2
  have wsize : (slideState d).w_size = d.w_size := rfl
  have more := slide_more_eq good env sizeP sizeH range taken
  have first : fillBody (some (.tab ds)) d.w_size false h = fillBody (some (.tab ds)) d.w_size false hs := by
    simp only [fill_body_slide_source, bind_app, ldDeflateState_tab good.live.hs,
      ldDeflateState_tab afterGood.live.hs, wsize, taken, if_true, prefixRun, noSlide, if_false]
    rw [more]
  have loop := do_first_body_eq (cond := fillCond (some (.tab ds))) first
  have stateS : (slideHeap h ds w p q d wa pa' qa').dstates ds = some (slideState d) := by simp [slideHeap]
  simp only [fill_window_source, bind_app, rdD_eq, good.live.hs, stateS, wsize]
  rw [loop]

theorem slide_input_frame {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa' qa' : Array UInt16} {ref : BRef}
    (good : DGood h r ds z d) (separate : BRef.blk w ≠ ref) :
    Space.get (slideHeap h ds w p q d wa pa' qa') ref = (Space.get h ref : Option (Array UInt8)) := by
  cases ref with
  | blk b =>
    have different : b ≠ w := by intro same; subst b; exact separate rfl
    simp [slideHeap, Space.get, upd_ne _ _ _ _ different]
  | dstate_depth id =>
    by_cases same : id = ds
    · subst id
      simp [slideHeap, Space.get, good.live.hs, slideState, slideBeforeHash]
    · simp [slideHeap, Space.get, setD, upd_ne _ _ _ _ same]
  | str _ | st_dist_code | st_length_code => rfl

end Zlib.Deflate.Engine.Proofs
