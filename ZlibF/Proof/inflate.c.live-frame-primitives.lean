import ZlibF.Proof.«inflate.c.fast-memory-shape-source»
import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Zero-length memcpy writes back the same view, including read-only views. -/
theorem slow_byte_view_put_self {h : Heap} {ref : BRef} {old : Array UInt8}
    (get : Space.get h ref = some old) : Space.put h ref old = h := by
  cases ref with
  | blk id => simp only [Space.get] at get; simp [Space.put, upd_self _ _ _ get]
  | dstate_depth id =>
    cases state : h.dstates id with
    | none => simp [Space.get, state] at get
    | some s =>
      have same : s.depth = old := by simpa [Space.get, state] using get
      rw [← same]
      simp [Space.put, state, upd_self _ _ _ state]
  | str id => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

/-- Existing word views retain object presence on actual stores. -/
theorem slow_word_view_put_memory_meta (h : Heap) (ref : WRef) (old array : Array UInt16)
    (get : Space.get h ref = some old) :
    fastMemoryMeta (Space.put h ref array) = fastMemoryMeta h := by
  have shape : Shape h (Space.put h ref array) := by
    cases ref with
    | blk id =>
      intro b
      by_cases same : b = id
      · subst b; simp [Shape, Space.put, Space.get] at get ⊢; simp [get]
      · simp [Shape, Space.put, upd_ne _ _ _ _ same]
    | dstate_bl_count id =>
      cases state : h.dstates id with
      | none => simp [Space.get, state] at get
      | some s =>
        intro b
        by_cases same : b = id
        · subst b; simp [Shape, Space.put, state]
        · simp [Shape, Space.put, state, upd_ne _ _ _ _ same]
    | istate_lens id =>
      cases state : h.istates id with
      | none => simp [Space.get, state] at get
      | some s =>
        intro b
        by_cases same : b = id
        · subst b; simp [Shape, Space.put, state]
        · simp [Shape, Space.put, state, upd_ne _ _ _ _ same]
    | istate_work id =>
      cases state : h.istates id with
      | none => simp [Space.get, state] at get
      | some s =>
        intro b
        by_cases same : b = id
        · subst b; simp [Shape, Space.put, state]
        · simp [Shape, Space.put, state, upd_ne _ _ _ _ same]
  unfold fastMemoryMeta
  rw [fastMemoryMeta_live_eq_of_shape shape]
  cases ref <;> simp only [Space.put] <;> repeat' first | rfl | split

/-- Embedded code-table writes do not allocate or remove an object. -/
theorem slow_code_view_put_memory_meta (h : Heap) (ref : CodeRef) (_old array : Array Code) :
    fastMemoryMeta (Space.put h ref array) = fastMemoryMeta h := by
  have shape : Shape h (Space.put h ref array) := by
    cases ref with
    | istate_codes id =>
      cases state : h.istates id with
      | none => simpa only [Space.put, state] using Shape.refl h
      | some s =>
        intro b
        by_cases same : b = id
        · subst b; simp [Shape, Space.put, state]
        · simp [Shape, Space.put, state, upd_ne _ _ _ _ same]
    | st_lenfix => exact Shape.refl h
    | st_distfix => exact Shape.refl h
  unfold fastMemoryMeta
  rw [fastMemoryMeta_live_eq_of_shape shape]
  cases ref <;> simp only [Space.put] <;> repeat' first | rfl | split

theorem fastMemoryMetaFrameM_store16 (r : ZStreamRef) (p : WPtr) (value : UInt16) : FastMemoryMetaFrameM r (p.store value) :=
  fastMemoryMetaFrameM_ptr_store r p value (fun h ref old array get _ => slow_word_view_put_memory_meta h ref old array get)


theorem fastMemoryMetaFrameM_storeCode (r : ZStreamRef) (p : CodePtr) (value : Code) : FastMemoryMetaFrameM r (p.store value) :=
  fastMemoryMetaFrameM_ptr_store r p value (fun h ref old array _ _ => slow_code_view_put_memory_meta h ref old array)


theorem fastMemoryMetaFrameM_memcpyB (r : ZStreamRef) (destination source : BPtr) (count : Nat) :
    FastMemoryMetaFrameM r (memcpyB destination source count) := by
  intro h value after run
  cases destination with
  | null => cases run
  | ref dest off =>
    cases source with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first
        | cases run
        | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      by_cases zero : count = 0
      · subst count
        simp only [copyRange, List.range_zero, List.foldl_nil, slow_byte_view_put_self destGet] at run
        repeat' first | split at run | (cases run <;> rfl)
      · repeat' first
          | split at run
          | (cases run <;> exact fast_byte_view_put_memory_meta _ _ array _ destGet
              (by cases ro : Space.ro h dest <;> simp_all))

/-- Literal messages are a partial update of the same live stream. -/

theorem fastMemoryMetaFrameM_setMsg (r : ZStreamRef) (message : String) : FastMemoryMetaFrameM r (setMsg (some r) message) := by
  unfold setMsg
  refine fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_strLit r _) (fun pointer => ?_)
  change FastMemoryMetaFrameM r (wrZ (some r) (fun z => { z with msg := pointer }))
  exact fastMemoryMetaFrameM_wrZ r _ (fun _ => rfl)


theorem fastMemoryMetaFrameM_ldHeader (r : ZStreamRef) (pointer : GzHeaderPtr) : FastMemoryMetaFrameM r (ldGzHeader pointer) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run <;> rfl)


theorem fastMemoryMetaFrameM_stHeader (r : ZStreamRef) (pointer : GzHeaderPtr) (header : GzHeader) :
    FastMemoryMetaFrameM r (stGzHeader pointer header) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab id =>
      simp only [stGzHeader, GzHeaderRef.get, GzHeaderRef.isRo, Bool.false_eq_true, ↓reduceIte] at run
      cases get : h.gzheaders id with
      | none => rw [get] at run; cases run
      | some old =>
        rw [get] at run
        cases run
        have shape : Shape h (GzHeaderRef.put h (.tab id) header) := by
          intro b
          by_cases same : b = id
          · subst b; simp [Shape, GzHeaderRef.put, get]
          · simp [Shape, GzHeaderRef.put, get, upd_ne _ _ _ _ same]
        simp only [FastMemoryMetaFrame, fastMemoryMeta]
        rw [fastMemoryMeta_live_eq_of_shape shape]
        simp only [GzHeaderRef.put, get]


theorem fastMemoryMetaFrameM_shr32 (r : ZStreamRef) (value shift : UInt32) : FastMemoryMetaFrameM r (shr32 value shift) := by
  unfold shr32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)


theorem fastMemoryMetaFrameM_shl64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : FastMemoryMetaFrameM r (shl64 value shift) := by
  unfold shl64
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)


theorem fastMemoryMetaFrameM_shr64 (r : ZStreamRef) (value : UInt64) (shift : UInt32) : FastMemoryMetaFrameM r (shr64 value shift) := by
  unfold shr64
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)


theorem fastMemoryMetaFrameM_chkI32 (r : ZStreamRef) (value : Int) : FastMemoryMetaFrameM r (chkI32 value) := by
  unfold chkI32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)


theorem fastMemoryMetaFrameM_chkI64 (r : ZStreamRef) (value : Int) : FastMemoryMetaFrameM r (chkI64 value) := by
  unfold chkI64
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)


theorem fastMemoryMetaFrameM_hcrcOn (r : ZStreamRef) (pointer : InflateStatePtr) : FastMemoryMetaFrameM r (hcrcOn pointer) :=
  fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ldS r pointer) (fun _ => fastMemoryMetaFrameM_pure r _)


theorem fastMemoryMetaFrameM_badMode (r : ZStreamRef) (context : Ctx) (root : context.strm = some r) (message : String) :
    FastMemoryMetaFrameM r (badMode context message) := by
  unfold badMode
  rw [root]
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_setMsg r message) (fun _ => fastMemoryMetaFrameM_setMode r _ _)


theorem fastMemoryMetaFrameX_xdoWhile {r : ZStreamRef} {body : X Unit} {cond : X Bool}
    (hb : FastMemoryMetaFrameX r body) (hc : FastMemoryMetaFrameX r cond) : FastMemoryMetaFrameX r (xdoWhile body cond) :=
  fastMemoryMetaFrameX_bind hb (fun _ => fastMemoryMetaFrameX_xwhile hc hb)


theorem fastMemoryMetaFrameX_xloopBrk {r : ZStreamRef} {body : X Bool} (frame : FastMemoryMetaFrameX r body) :
    FastMemoryMetaFrameX r (xloopBrk body) := fastMemoryMetaFrameX_xwhileBrk (fastMemoryMetaFrameX_pure r true) frame


theorem fastMemoryMetaFrameM_orderAt (r : ZStreamRef) (index : UInt32) : FastMemoryMetaFrameM r (orderAt index) := by
  unfold orderAt
  split
  · exact fastMemoryMetaFrameM_pure r _
  · exact fastMemoryMetaFrameM_ub r _

end Zlib.Inflate.Proofs
