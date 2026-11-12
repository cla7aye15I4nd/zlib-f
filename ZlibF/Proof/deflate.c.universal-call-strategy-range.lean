import ZlibF.Proof.«deflate.c.universal-call-strategy-pars»

/-!
# deflate.c: the block state a strategy returns

Batch C (owner 2's M16). `block_state` is a `UInt32` in the model, so that a strategy returns one
of the four enumerators is a fact about the code: every `return` in the five strategies, in
`FLUSH_BLOCK` and in `finish_tail` returns one of `need_more`, `block_done`, `finish_started`,
`finish_done`. `PostM P m` says that every returning run of `m` returns a value with `P`; it
composes like the parameter frame, and a bind needs nothing of its first part unless the value is
read later (`FLUSH_BLOCK`, the loop state).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- Every returning run of `m` returns a value with `P`. A structure, so that `intro` does not
unfold it inside the step tactics. -/
structure PostM {α : Type} (P : α → Prop) (m : M α) : Prop where
  run : ∀ h a h', m h = .ok (a, h') → P a

theorem PostM.pure {α : Type} {P : α → Prop} {a : α} (ha : P a) : PostM P (Pure.pure a : M α) :=
  ⟨fun h v h' run => by cases run; exact ha⟩

theorem PostM.ub {α : Type} {P : α → Prop} (what : String) : PostM P (C.ub what : M α) :=
  ⟨fun h v h' run => by cases run⟩

theorem PostM.bind {α β : Type} {P : β → Prop} {Q : α → Prop} {m : M α} {f : α → M β} (hm : PostM Q m)
    (hf : ∀ a, Q a → PostM P (f a)) : PostM P (m >>= f) := by
  refine ⟨fun h value after run => ?_⟩
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    exact (hf a (hm.run h a h1 e)).run h1 value after run

theorem PostM.bind_any {α β : Type} {P : β → Prop} {m : M α} {f : α → M β} (hf : ∀ a, PostM P (f a)) :
    PostM P (m >>= f) :=
  PostM.bind (Q := fun _ => True) ⟨fun _ _ _ _ => trivial⟩ (fun a _ => hf a)

theorem PostM.ite {α : Type} {P : α → Prop} (p : Prop) [Decidable p] {a b : M α} (ha : PostM P a)
    (hb : PostM P b) : PostM P (if p then a else b) := by
  split <;> assumption

theorem PostM.cwhile_go {σ : Type} {inv : σ → Prop} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, inv s → PostM (fun p => inv p.2) (cond s)) (hb : ∀ s, inv s → PostM inv (body s)) (n : Nat)
    (s : σ) (h0 : inv s) : PostM inv (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => exact ⟨fun h v after run => by cases run⟩
  | succ n ih =>
    rw [cwhile.go]
    refine PostM.bind (hc s h0) ?_
    rintro ⟨c, s'⟩ hs'
    exact PostM.ite _ (PostM.bind (hb s' hs') (fun t ht => ih t ht)) (PostM.pure hs')

theorem PostM.cwhile {σ : Type} {inv : σ → Prop} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, inv s → PostM (fun p => inv p.2) (cond s)) (hb : ∀ s, inv s → PostM inv (body s)) (s : σ)
    (h0 : inv s) : PostM inv (C.cwhile cond body s) := PostM.cwhile_go cond body hc hb fuel s h0

/-- The four enumerators of `block_state`. -/
def BlockRange (b : block_state) : Prop := b = need_more ∨ b = block_done ∨ b = finish_started ∨ b = finish_done

/-- The loop state of a strategy: a pending return is an enumerator. -/
def LoopRange (st : LoopS) : Prop := ∀ r, st.ret = some r → BlockRange r

/-- The steps of a result proof: binds that need nothing, branches, matches and the join points of
the translated `do` blocks. -/
macro "post_steps" : tactic => `(tactic|
  repeat' first
    | intro _
    | (apply PostM.pure; simp_all [BlockRange, LoopRange]; done)
    | (apply PostM.pure; split <;> simp [BlockRange])
    | with_reducible exact PostM.ub _
    | with_reducible apply PostM.ite
    | with_reducible apply PostM.bind_any
    | split
    | dsimp only)

theorem post_FLUSH_BLOCK (s : DeflateStatePtr) (last : Int32) :
    PostM (fun o => ∀ r, o = some r → BlockRange r) (FLUSH_BLOCK s last) := by
  unfold FLUSH_BLOCK
  post_steps

theorem post_finish_tail (s : DeflateStatePtr) (flush : Int32) : PostM BlockRange (finish_tail s flush) := by
  unfold finish_tail
  repeat' first
    | (refine PostM.bind (post_FLUSH_BLOCK _ _) ?_; intro o ho)
    | intro _
    | (apply PostM.pure; simp_all [BlockRange]; done)
    | with_reducible apply PostM.ite
    | with_reducible apply PostM.bind_any
    | split
    | dsimp only

/-- A loop body: the flushes inside return enumerators, every other value is kept. -/
macro "body_steps" : tactic => `(tactic|
  repeat' first
    | (refine PostM.bind (post_FLUSH_BLOCK _ _) ?_; intro _ _)
    | intro _
    | (apply PostM.pure; simp_all [BlockRange, LoopRange]; done)
    | with_reducible exact PostM.ub _
    | with_reducible apply PostM.ite
    | with_reducible apply PostM.bind_any
    | split
    | dsimp only)

theorem post_loop (body : LoopS → M LoopS) (hb : ∀ st, LoopRange st → PostM LoopRange (body st)) :
    PostM LoopRange (C.cwhile forever body {}) :=
  PostM.cwhile forever body (fun st hst => PostM.pure hst) hb {} (fun r e => by cases e)

/-- The end of the loop strategies: a pending return, or the tail. -/
theorem post_after_loop (body : LoopS → M LoopS) (hb : ∀ st, LoopRange st → PostM LoopRange (body st))
    (tail : M block_state) (ht : PostM BlockRange tail) :
    PostM BlockRange (do
      let st ← C.cwhile forever body {}
      if let some r := st.ret then return r
      tail) := by
  refine PostM.bind (post_loop body hb) ?_
  intro st hst
  split
  · rename_i r e
    exact PostM.pure (hst r e)
  · exact ht

theorem post_deflate_fast_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (hst : LoopRange st) :
    PostM LoopRange (deflate_fast_body s flush st) := by
  unfold deflate_fast_body
  body_steps

theorem post_deflate_slow_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (hst : LoopRange st) :
    PostM LoopRange (deflate_slow_body s flush st) := by
  unfold deflate_slow_body
  body_steps

theorem post_deflate_rle_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (hst : LoopRange st) :
    PostM LoopRange (deflate_rle_body s flush st) := by
  unfold deflate_rle_body
  body_steps

theorem post_deflate_huff_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (hst : LoopRange st) :
    PostM LoopRange (deflate_huff_body s flush st) := by
  unfold deflate_huff_body
  body_steps

theorem post_deflate_fast (s : DeflateStatePtr) (flush : Int32) : PostM BlockRange (deflate_fast s flush) := by
  unfold deflate_fast
  exact post_after_loop _ (post_deflate_fast_body s flush) _
    (PostM.bind_any (fun _ => post_finish_tail s flush))

theorem post_deflate_slow (s : DeflateStatePtr) (flush : Int32) : PostM BlockRange (deflate_slow s flush) := by
  unfold deflate_slow
  refine post_after_loop _ (post_deflate_slow_body s flush) _ ?_
  repeat' first
    | exact post_finish_tail s flush
    | intro _
    | with_reducible apply PostM.ite
    | with_reducible apply PostM.bind_any
    | split
    | dsimp only

theorem post_deflate_rle (s : DeflateStatePtr) (flush : Int32) : PostM BlockRange (deflate_rle s flush) := by
  unfold deflate_rle
  exact post_after_loop _ (post_deflate_rle_body s flush) _
    (PostM.bind_any (fun _ => post_finish_tail s flush))

theorem post_deflate_huff (s : DeflateStatePtr) (flush : Int32) : PostM BlockRange (deflate_huff s flush) := by
  unfold deflate_huff
  exact post_after_loop _ (post_deflate_huff_body s flush) _
    (PostM.bind_any (fun _ => post_finish_tail s flush))

theorem post_deflate_stored (s : DeflateStatePtr) (flush : Int32) : PostM BlockRange (deflate_stored s flush) := by
  unfold deflate_stored
  post_steps

theorem post_dispatch (s : DeflateStatePtr) (flush : Int32) (d : DeflateState) :
    PostM BlockRange (dispatch s flush d) := by
  unfold dispatch
  refine PostM.ite _ (post_deflate_stored _ _) (PostM.ite _ (post_deflate_huff _ _)
    (PostM.ite _ (post_deflate_rle _ _) (PostM.bind_any (fun c => ?_))))
  split
  · exact post_deflate_stored _ _
  · exact post_deflate_fast _ _
  · exact post_deflate_slow _ _

/-- **The dispatch returns one of the four enumerators** (M16). -/
theorem dispatch_range {h after : Heap} {ds : Nat} {d : DeflateState} {flush : Int32} {b : block_state}
    (run : dispatch (some (.tab ds)) flush d h = .ok (b, after)) :
    b = need_more ∨ b = block_done ∨ b = finish_started ∨ b = finish_done :=
  (post_dispatch _ _ _).run h b after run

end Zlib.Deflate.Universal.Call
