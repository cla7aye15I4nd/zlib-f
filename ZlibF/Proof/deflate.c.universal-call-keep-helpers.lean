import ZlibF.Proof.«deflate.c.universal-call-keep-steps»
import ZlibF.Proof.«trees.c.monad»

/-!
# deflate.c: `KeepRel` for the helpers of `deflate_base.c`

Port of `deflate.c.universal-params-helpers`: the macros and helpers of `deflate_base.c.lean` are
in `KeepM`.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

theorem keep_chk32 (v : Int) : KeepM (chk32 v) := by
  unfold chk32; exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)
theorem keep_chk64 (v : Int) : KeepM (chk64 v) := by
  unfold chk64; exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)
theorem keep_iadd (a b : Int32) : KeepM (iadd a b) := keep_chk32 _
theorem keep_isub (a b : Int32) : KeepM (isub a b) := keep_chk32 _
theorem keep_ineg (a : Int32) : KeepM (ineg a) := keep_chk32 _
theorem keep_ladd (a b : Int64) : KeepM (ladd a b) := keep_chk64 _
theorem keep_lsub (a b : Int64) : KeepM (lsub a b) := keep_chk64 _
theorem keep_ishl (a : Int32) (n : Int) : KeepM (ishl a n) := by
  unfold ishl; exact KeepM.ite _ (keep_chk32 _) (KeepM.ub _)
theorem keep_ushl (a n : UInt32) : KeepM (ushl a n) := by
  unfold ushl; exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)
theorem keep_config_at (level : Int32) : KeepM (config_at level) := by
  unfold config_at; exact KeepM.ite _ (KeepM.pure _) (KeepM.ub _)
theorem keep_padd {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : KeepM (padd p n) :=
  keep_ptr_add _ _
theorem keep_psub {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : KeepM (psub p n) :=
  keep_ptr_add _ _
theorem keep_rd {α : Type} (p : DeflateStatePtr) (f : DeflateState → α) : KeepM (rd p f) :=
  KeepM.bind (keep_ldDeflateState p) (fun _ => KeepM.pure _)
theorem keep_zrd {α : Type} (p : ZStreamPtr) (f : ZStream → α) : KeepM (zrd p f) :=
  KeepM.bind (keep_ldZStream p) (fun _ => KeepM.pure _)

/-- The helpers above as steps. -/
macro "k_leaf" : tactic => `(tactic|
  first
    | with_reducible exact keep_chk32 _
    | with_reducible exact keep_chk64 _
    | with_reducible exact keep_iadd _ _
    | with_reducible exact keep_isub _ _
    | with_reducible exact keep_ineg _
    | with_reducible exact keep_ladd _ _
    | with_reducible exact keep_lsub _ _
    | with_reducible exact keep_ishl _ _
    | with_reducible exact keep_ushl _ _
    | with_reducible exact keep_config_at _
    | with_reducible exact keep_padd _ _
    | with_reducible exact keep_psub _ _
    | with_reducible exact keep_rd _ _
    | with_reducible exact keep_zrd _ _
    | keep_leaf)

/-- One step: a helper, a primitive or a composition rule. -/
macro "k_step" : tactic => `(tactic|
  first
    | k_leaf
    | keep_step
    | split)

macro "k_steps" : tactic => `(tactic| repeat' k_step)

/-- A load, steps in `KeepM`, and a store of the record. -/
theorem keep_ld_st0 {β : Type} (p : DeflateStatePtr) (q : DeflateState → M β)
    (g : DeflateState → β → DeflateState) (hg : ∀ d x, (g d x).gzhead = d.gzhead) (hq : ∀ d, KeepM (q d)) :
    KeepM (do
      let d ← ldDeflateState p
      let x ← q d
      stDeflateState p (g d x)) := by
  have whole := keep_ld_st p q g (fun _ _ => (Pure.pure () : M Unit)) hg hq (fun _ _ => KeepM.pure _)
  have tail : ∀ (d : DeflateState) (x : β),
      (stDeflateState p (g d x) >>= fun _ => (Pure.pure () : M Unit)) = stDeflateState p (g d x) := by
    intro d x
    funext h
    simp only [bind_app, pure_app]
    cases stDeflateState p (g d x) h <;> rfl
  simpa only [tail] using whole

theorem keep_store_at (p : BPtr) (i : Nat) (v : UInt8) : KeepM (store_at p i v) := by
  unfold store_at; k_steps

theorem keep_put_byte (s : DeflateStatePtr) (c : UInt8) : KeepM (put_byte s c) := by
  unfold put_byte
  exact keep_ld_st0 s (fun d => store_at d.pending_buf d.pending.toNat c)
    (fun d _ => { d with pending := d.pending + 1 }) (fun _ _ => rfl) (fun _ => keep_store_at _ _ _)

theorem keep_putShortMSB (s : DeflateStatePtr) (b : UInt32) : KeepM (putShortMSB s b) := by
  unfold putShortMSB
  exact KeepM.bind (keep_put_byte _ _) (fun _ => keep_put_byte _ _)

theorem keep_UPDATE_HASH (s : DeflateStatePtr) (c : UInt8) : KeepM (UPDATE_HASH s c) := by
  unfold UPDATE_HASH
  exact keep_ld_st0 s (fun d => ushl d.ins_h d.hash_shift)
    (fun d sh => { d with ins_h := (sh ^^^ c.toUInt32) &&& d.hash_mask }) (fun _ _ => rfl) (fun _ => keep_ushl _ _)

theorem keep_INSERT_STRING (s : DeflateStatePtr) (str : UInt32) : KeepM (INSERT_STRING s str) := by
  unfold INSERT_STRING
  repeat' first | exact keep_UPDATE_HASH _ _ | k_step

theorem keep_CLEAR_HASH (s : DeflateStatePtr) : KeepM (CLEAR_HASH s) := by
  unfold CLEAR_HASH; k_steps

theorem keep_d_code (dist : UInt16) : KeepM (d_code dist) := by
  unfold d_code; k_steps

theorem keep_freq_inc (r : CtDataRef) (i : Nat) : KeepM (freq_inc r i) := by
  unfold freq_inc; k_steps

theorem keep_tally_lit (s : DeflateStatePtr) (c : UInt8) : KeepM (tally_lit s c) := by
  let rest : M Bool := match s with
    | none => ub "null deflate_state"
    | some (.tab id) => do
      freq_inc (.dstate_dyn_ltree id) c.toNat
      let d ← ldDeflateState s
      return d.sym_next == d.sym_end
  have grouped : tally_lit s c = (do
      let d ← ldDeflateState s
      let x ← (do
        store_at d.sym_buf d.sym_next.toNat 0
        store_at d.sym_buf (d.sym_next + 1).toNat 0
        store_at d.sym_buf (d.sym_next + 2).toNat c)
      stDeflateState s { d with sym_next := d.sym_next + 3 }
      rest) := by
    unfold tally_lit
    simp only [M_bind_assoc, rest]
    cases s with
    | none => rfl
    | some r => cases r; rfl
  rw [grouped]
  refine keep_ld_st s _ (fun d (_ : Unit) => { d with sym_next := d.sym_next + 3 }) (fun _ _ => rest)
    (fun _ _ => rfl) ?_ ?_
  · intro d
    exact KeepM.bind (keep_store_at _ _ _) (fun _ =>
      KeepM.bind (keep_store_at _ _ _) (fun _ => keep_store_at _ _ _))
  · intro d x
    cases s with
    | none => exact KeepM.ub _
    | some r =>
      cases r
      exact KeepM.bind (keep_freq_inc _ _) (fun _ =>
        KeepM.bind (keep_ldDeflateState _) (fun _ => KeepM.pure _))

theorem keep_slide_hash (s : DeflateStatePtr) : KeepM (slide_hash s) := by
  unfold slide_hash; k_steps

theorem keep_read_buf (p : ZStreamPtr) (buf : BPtr) (n : UInt32) : KeepM (read_buf p buf n) := by
  unfold read_buf; k_steps

theorem keep_fill_window (s : DeflateStatePtr) : KeepM (fill_window s) := by
  unfold fill_window
  repeat' first
    | with_reducible exact keep_slide_hash _
    | with_reducible exact keep_read_buf _ _ _
    | with_reducible exact keep_UPDATE_HASH _ _
    | k_step

end Zlib.Deflate.Universal.Keep
