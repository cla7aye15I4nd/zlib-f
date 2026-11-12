import ZlibF.Proof.«deflate.c.universal-params-base»
import ZlibF.Zlib.«deflate.c»
import ZlibF.Spec.Public.Initialisation

/-!
# deflate.c: what every run of a `deflate` callee keeps

Owner 2 of the deflate split (`deflate_call`). Batch C's parameter frame (`universal-params-*`)
shows that a returning run keeps the parameters of every record. This module and its successors
show, in the same compositional way, three facts that `Goal.deflate` states for every call:

* no allocation and no release: `nalloc` is kept and every table keeps which entries exist, so
  `LiveChange h after ∅ ∅` and `after.nalloc = h.nalloc`;
* every stream record keeps `msg` (the error returns of `deflate` set it, and they are outside
  the callees covered here);
* every stream record changes `data_type` only from `Z_UNKNOWN` to `Z_BINARY` or `Z_TEXT`
  (`_tr_flush_block`).

`KeepRel h h'` is the relation between the heap before and after a run. One lemma per primitive
and per function; no callee contract is assumed.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- `data_type` is kept, or it goes from `Z_UNKNOWN` to a guess. -/
def DataStep (t t' : Int32) : Prop := t' = t ∨ (t = Z_UNKNOWN ∧ (t' = Z_BINARY ∨ t' = Z_TEXT))

theorem DataStep.refl (t : Int32) : DataStep t t := Or.inl rfl

theorem DataStep.trans {a b c : Int32} (first : DataStep a b) (second : DataStep b c) : DataStep a c := by
  rcases first with e | ⟨unknown, guess⟩
  · subst e; exact second
  · rcases second with e | ⟨again, _⟩
    · subst e; exact Or.inr ⟨unknown, guess⟩
    · subst again
      rcases guess with g | g <;> exact absurd g (by decide)

/-- Every heap change outside allocation keeps the stream fields of the relation. -/
def StreamKeep (h h' : Heap) : Prop :=
  ∀ (r : ZStreamRef) z, r.get h = some z →
    ∃ z', r.get h' = some z' ∧ z'.msg = z.msg ∧ DataStep z.data_type z'.data_type

/-- The relation between the heap before and after a run of a `deflate` callee. -/
structure KeepRel (h h' : Heap) : Prop where
  nalloc : h'.nalloc = h.nalloc
  used : ∀ b, h'.slotUsed b = h.slotUsed b
  stream : StreamKeep h h'

theorem KeepRel.refl (h : Heap) : KeepRel h h :=
  ⟨rfl, fun _ => rfl, fun _ z get => ⟨z, get, rfl, DataStep.refl _⟩⟩

theorem KeepRel.trans {a b c : Heap} (first : KeepRel a b) (second : KeepRel b c) : KeepRel a c := by
  refine ⟨second.nalloc.trans first.nalloc, fun x => (second.used x).trans (first.used x), fun r z get => ?_⟩
  obtain ⟨z1, get1, msg1, data1⟩ := first.stream r z get
  obtain ⟨z2, get2, msg2, data2⟩ := second.stream r z1 get1
  exact ⟨z2, get2, msg2.trans msg1, data1.trans data2⟩

/-- `slotUsed` and `live` say the same. -/
theorem live_iff_used (h : Heap) (b : Nat) : h.live b ↔ h.slotUsed b = true := by
  simp [Heap.live, Heap.slotUsed, Option.isSome_iff_ne_none, or_assoc]

/-- The allocation clauses of `Goal.deflate` from the relation. -/
theorem KeepRel.liveChange {h h' : Heap} (rel : KeepRel h h') :
    ZlibF.Spec.Public.LiveChange h h' (fun _ => False) (fun _ => False) := by
  intro b
  rw [live_iff_used, live_iff_used, rel.used b]
  simp

/-! ## Changes of single tables -/

/-- An entry changed in place keeps which entries exist. -/
theorem isSome_modify_map {β : Type} (t : Tbl (Option β)) (k : Nat) (g : β → β) (x : Nat) :
    ((t.modify k (Option.map g)) x).isSome = (t x).isSome := by
  rw [Zlib.Deflate.Universal.Params.Tbl.get_modify_map]
  split <;> simp

/-- An entry replaced by another one keeps which entries exist. -/
theorem isSome_upd_some {β : Type} (t : Tbl (Option β)) (k : Nat) (old v : β) (get : t k = some old) (x : Nat) :
    ((upd t k (some v)) x).isSome = (t x).isSome := by
  by_cases same : x = k
  · subst same; simp [get]
  · simp [upd_ne _ _ _ _ same]

/-- A change of the byte, word or record tables that keeps which entries exist, with the stream
and gzip-state tables untouched. -/
theorem KeepRel.quiet {h h' : Heap} (nalloc : h'.nalloc = h.nalloc)
    (bytes : ∀ x, (h'.bytes x).isSome = (h.bytes x).isSome)
    (words : ∀ x, (h'.words x).isSome = (h.words x).isSome)
    (gzheaders : ∀ x, (h'.gzheaders x).isSome = (h.gzheaders x).isSome)
    (dstates : ∀ x, (h'.dstates x).isSome = (h.dstates x).isSome)
    (istates : ∀ x, (h'.istates x).isSome = (h.istates x).isSome)
    (streams : h'.streams = h.streams) (gz : h'.gzstates = h.gzstates) : KeepRel h h' := by
  refine ⟨nalloc, fun x => ?_, fun r z get => ⟨z, ?_, rfl, DataStep.refl _⟩⟩
  · simp only [Heap.slotUsed, bytes, words, gzheaders, dstates, istates, streams, gz]
  · cases r with
    | tab i => simpa only [ZStreamRef.get, streams] using get
    | in_gzstate_strm i => simpa only [ZStreamRef.get, gz] using get

/-- A deflate state record changed in place. -/
theorem KeepRel.dstate_array {h : Heap} (id : Nat) (g : DeflateState → DeflateState) :
    KeepRel h { h with dstates := h.dstates.modify id (Option.map g) } :=
  KeepRel.quiet rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun x => isSome_modify_map _ _ _ x)
    (fun _ => rfl) rfl rfl

/-- An inflate state record changed in place. -/
theorem KeepRel.istate_array {h : Heap} (id : Nat) (g : InflateState → InflateState) :
    KeepRel h { h with istates := h.istates.modify id (Option.map g) } :=
  KeepRel.quiet rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun x => isSome_modify_map _ _ _ x) rfl rfl

/-- A deflate state record replaced by another one. -/
theorem KeepRel.upd_state {h : Heap} {i : Nat} {d : DeflateState} (get : h.dstates i = some d)
    (d' : DeflateState) : KeepRel h { h with dstates := upd h.dstates i (some d') } :=
  KeepRel.quiet rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun x => isSome_upd_some _ _ _ _ get x)
    (fun _ => rfl) rfl rfl

/-- The fields of a stream record that a callee's store keeps. The third field makes the three
fields close by `⟨rfl, rfl, rfl⟩`, as batch C's `ZSame` does. -/
structure ZKeep (z z' : ZStream) : Prop where
  msg : z'.msg = z.msg
  data_type : z'.data_type = z.data_type
  state : z'.state = z.state

/-- What writing a live stream record changes: that record only. -/
theorem put_stream_facts {h : Heap} {r : ZStreamRef} {z : ZStream} (get : r.get h = some z) (z' : ZStream) :
    (r.put h z').nalloc = h.nalloc ∧ (∀ b, (r.put h z').slotUsed b = h.slotUsed b) ∧
      r.get (r.put h z') = some z' ∧ ∀ q, q ≠ r → q.get (r.put h z') = q.get h := by
  refine ⟨?_, fun x => ?_, Zlib.Deflate.Proofs.ZStreamRef.get_put_same get z', fun q eq => ?_⟩
  · cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  · cases r with
    | tab i =>
      simp only [ZStreamRef.get] at get
      simp only [ZStreamRef.put, get, Heap.slotUsed]
      rw [isSome_upd_some _ _ _ _ get]
    | in_gzstate_strm i =>
      simp only [ZStreamRef.get] at get
      cases g : h.gzstates i with
      | none => simp [g] at get
      | some s =>
        simp only [ZStreamRef.put, g, Heap.slotUsed]
        rw [isSome_upd_some _ _ _ _ g]
  · cases r with
    | tab i =>
      cases q with
      | tab j =>
        have ne : j ≠ i := fun e => eq (by rw [e])
        simp only [ZStreamRef.put]
        split <;> simp_all [ZStreamRef.get, upd_ne _ _ _ _ ne]
      | in_gzstate_strm j =>
        simp only [ZStreamRef.put]
        split <;> rfl
    | in_gzstate_strm i =>
      cases q with
      | tab j =>
        simp only [ZStreamRef.put]
        split <;> rfl
      | in_gzstate_strm j =>
        have ne : j ≠ i := fun e => eq (by rw [e])
        simp only [ZStreamRef.put]
        split <;> simp_all [ZStreamRef.get, upd_ne _ _ _ _ ne]

/-- A heap in the relation, then a store into a stream record whose new `msg` and `data_type`
are a step of that record's values in the first heap. -/
theorem KeepRel.put_from {h h1 : Heap} {r : ZStreamRef} {z z1 : ZStream} (rel : KeepRel h h1)
    (get : r.get h = some z) (get1 : r.get h1 = some z1) (z' : ZStream)
    (msg : z'.msg = z.msg) (data : DataStep z.data_type z'.data_type) : KeepRel h (r.put h1 z') := by
  obtain ⟨nalloc, used, getr, others⟩ := put_stream_facts get1 z'
  refine ⟨nalloc.trans rel.nalloc, fun x => (used x).trans (rel.used x), fun q y got => ?_⟩
  by_cases eq : q = r
  · subst eq
    have yEq : y = z := Option.some.inj (got.symm.trans get)
    subst yEq
    exact ⟨z', getr, msg, data⟩
  · obtain ⟨y1, get1', msg1, data1⟩ := rel.stream q y got
    exact ⟨y1, (others q eq).trans get1', msg1, data1⟩

/-- Writing a stream record with a `msg` and a `data_type` step of the current record. -/
theorem keep_put_stream_step {h : Heap} {r : ZStreamRef} {z : ZStream} (get : r.get h = some z) (z' : ZStream)
    (msg : z'.msg = z.msg) (data : DataStep z.data_type z'.data_type) : KeepRel h (r.put h z') :=
  (KeepRel.refl h).put_from get get z' msg data

/-- Writing a stream record that keeps `msg` and `data_type`. -/
theorem keep_put_stream {h : Heap} {r : ZStreamRef} {z : ZStream} (get : r.get h = some z) (z' : ZStream)
    (same : ZKeep z z') : KeepRel h (r.put h z') :=
  keep_put_stream_step get z' same.msg (Or.inl same.data_type)

/-! ## Runs -/

/-- A returning run is in the relation. -/
def KeepM {α : Type} (m : M α) : Prop := ∀ h a h', m h = .ok (a, h') → KeepRel h h'

theorem KeepM.pure {α : Type} (a : α) : KeepM (Pure.pure a : M α) := by
  intro h v h' run; cases run; exact KeepRel.refl h

theorem KeepM.ub {α : Type} (what : String) : KeepM (C.ub what : M α) := by
  intro h v h' run; cases run

theorem KeepM.bind {α β : Type} {m : M α} {f : α → M β} (hm : KeepM m) (hf : ∀ a, KeepM (f a)) :
    KeepM (m >>= f) := by
  intro h value after run
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    exact (hm h a h1 e).trans (hf a h1 value after run)

theorem KeepM.ite {α : Type} (p : Prop) [Decidable p] {a b : M α} (ha : KeepM a) (hb : KeepM b) :
    KeepM (if p then a else b) := by
  split <;> assumption

theorem KeepM.cwhile_go {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, KeepM (cond s)) (hb : ∀ s, KeepM (body s)) (n : Nat) (s : σ) :
    KeepM (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => intro h v after run; cases run
  | succ n ih =>
    rw [cwhile.go]
    apply KeepM.bind (hc s)
    rintro ⟨c, s'⟩
    apply KeepM.ite
    · exact KeepM.bind (hb s') (fun t => ih t)
    · exact KeepM.pure _

theorem KeepM.cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, KeepM (cond s)) (hb : ∀ s, KeepM (body s)) (s : σ) :
    KeepM (C.cwhile cond body s) := KeepM.cwhile_go cond body hc hb fuel s

theorem KeepM.cdoWhile_go {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, KeepM (body s)) (hc : ∀ s, KeepM (cond s)) (n : Nat) (s : σ) :
    KeepM (cdoWhile.go body cond n s) := by
  induction n generalizing s with
  | zero => intro h v after run; cases run
  | succ n ih =>
    rw [cdoWhile.go]
    apply KeepM.bind (hb s)
    intro s'
    apply KeepM.bind (hc s')
    rintro ⟨c, t⟩
    exact KeepM.ite _ (ih t) (KeepM.pure _)

theorem KeepM.cdoWhile {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, KeepM (body s)) (hc : ∀ s, KeepM (cond s)) (s : σ) :
    KeepM (C.cdoWhile body cond s) := KeepM.cdoWhile_go body cond hb hc fuel s

/-! ## Array stores -/

theorem keep_modify_B (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) :
    KeepRel h (Space.modify h r f) := by
  cases r with
  | blk b =>
    change KeepRel h { h with bytes := h.bytes.modify b (Option.map f) }
    exact KeepRel.quiet rfl (fun x => isSome_modify_map _ _ _ x) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) rfl rfl
  | str i => exact KeepRel.refl h
  | dstate_depth id => exact KeepRel.dstate_array id _
  | st_dist_code => exact KeepRel.refl h
  | st_length_code => exact KeepRel.refl h

theorem keep_modify_W (h : Heap) (r : WRef) (f : Array UInt16 → Array UInt16) :
    KeepRel h (Space.modify h r f) := by
  cases r with
  | blk b =>
    change KeepRel h { h with words := h.words.modify b (Option.map f) }
    exact KeepRel.quiet rfl (fun _ => rfl) (fun x => isSome_modify_map _ _ _ x) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) rfl rfl
  | dstate_bl_count id => exact KeepRel.dstate_array id _
  | istate_lens id => exact KeepRel.istate_array id _
  | istate_work id => exact KeepRel.istate_array id _

theorem keep_modify_I (h : Heap) (r : IRef) (f : Array Int32 → Array Int32) :
    KeepRel h (Space.modify h r f) := by
  cases r with
  | dstate_heap id => exact KeepRel.dstate_array id _
  | _ => first | exact KeepRel.refl h | exact KeepRel.dstate_array _ _ | exact KeepRel.istate_array _ _

theorem keep_modify_Ct (h : Heap) (r : CtDataRef) (f : Array CtData → Array CtData) :
    KeepRel h (Space.modify h r f) := by
  cases r with
  | dstate_dyn_ltree id => exact KeepRel.dstate_array id _
  | dstate_dyn_dtree id => exact KeepRel.dstate_array id _
  | dstate_bl_tree id => exact KeepRel.dstate_array id _
  | _ => first | exact KeepRel.refl h | exact KeepRel.dstate_array _ _ | exact KeepRel.istate_array _ _

/-- A type of arrays whose in-place changes are in the relation. -/
class KeepSpace (R : Type) (T : Type) [Space Heap R T] : Prop where
  modify : ∀ (h : Heap) (r : R) (f : Array T → Array T), KeepRel h (Space.modify h r f)

instance : KeepSpace BRef UInt8 := ⟨keep_modify_B⟩
instance : KeepSpace WRef UInt16 := ⟨keep_modify_W⟩
instance : KeepSpace IRef Int32 := ⟨keep_modify_I⟩
instance : KeepSpace CtDataRef CtData := ⟨keep_modify_Ct⟩

theorem keep_ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : KeepM (p.add k) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : KeepM (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_ptr_index {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : KeepM (Ptr.index p k : M T) := by
  unfold Ptr.index
  exact KeepM.bind (keep_ptr_add _ _) (fun _ => keep_ptr_load _)

theorem keep_ptr_store {R T : Type} [Space Heap R T] [KeepSpace R T] (p : Ptr R) (v : T) :
    KeepM (Ptr.store p v) := by
  intro h value after run
  unfold Ptr.store at run
  repeat' first | split at run | (cases run; exact KeepSpace.modify h _ _) | contradiction

theorem keep_ptr_memcpy {R T : Type} [Space Heap R T] [KeepSpace R T] [DecidableEq R] [Inhabited T]
    (dst src : Ptr R) (n : Nat) : KeepM (Ptr.memcpy dst src n) := by
  intro h value after run
  unfold Ptr.memcpy at run
  repeat' first | split at run | (cases run; exact KeepSpace.modify h _ _) | contradiction

theorem keep_ptr_fill {R T : Type} [Space Heap R T] [KeepSpace R T] (dst : Ptr R) (v : T) (n : Nat) :
    KeepM (Ptr.fill dst v n) := by
  intro h value after run
  unfold Ptr.fill at run
  repeat' first | split at run | (cases run; exact KeepSpace.modify h _ _) | contradiction

theorem keep_ptr_diff {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    KeepM (Ptr.diff (T := T) p q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_ptr_lt {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    KeepM (Ptr.lt (T := T) p q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

/-! ## Records -/

theorem keep_ldDeflateState (p : DeflateStatePtr) : KeepM (ldDeflateState p) := by
  intro h value after run
  unfold ldDeflateState at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_ldZStream (p : ZStreamPtr) : KeepM (ldZStream p) := by
  intro h value after run
  unfold ldZStream at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_ldGzHeader (p : GzHeaderPtr) : KeepM (ldGzHeader p) := by
  intro h value after run
  unfold ldGzHeader at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_castDeflateState (p : Option StateRef) : KeepM (castDeflateState p) := by
  intro h value after run
  unfold castDeflateState at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

theorem keep_strLitRef (s : String) : KeepM (strLitRef s) := by
  intro h value after run
  unfold strLitRef at run
  repeat' first | split at run | (cases run; exact KeepRel.refl h) | contradiction

/-- `strm->f = ...`, when `f` keeps `msg` and `data_type`. -/
theorem keep_zwr (p : ZStreamPtr) (f : ZStream → ZStream) (hf : ∀ z, ZKeep z (f z)) : KeepM (zwr p f) := by
  intro h value after run
  unfold zwr at run
  rw [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases get : r.get h with
    | none => simp [ldZStream, get] at run
    | some z =>
      simp only [ldZStream, get, stZStream] at run
      split at run
      · cases run
      · cases run
        exact keep_put_stream get (f z) (hf z)

/-- `s->f = ...`: any change of a deflate state record. -/
theorem keep_wr (p : DeflateStatePtr) (f : DeflateState → DeflateState) : KeepM (wr p f) := by
  intro h value after run
  unfold wr at run
  rw [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases r with
    | tab i =>
      cases get : h.dstates i with
      | none => simp [ldDeflateState, DeflateStateRef.get, get] at run
      | some d =>
        simp only [ldDeflateState, DeflateStateRef.get, get, stDeflateState, DeflateStateRef.isRo] at run
        cases run
        rw [DeflateStateRef.put_tab get]
        exact KeepRel.upd_state get (f d)

/-- A store of a deflate state record built from an earlier load of the same record. -/
theorem keep_ld_st {β γ : Type} (p : DeflateStatePtr) (q : DeflateState → M β)
    (g : DeflateState → β → DeflateState) (k : DeflateState → β → M γ)
    (hq : ∀ d, KeepM (q d)) (hk : ∀ d x, KeepM (k d x)) :
    KeepM (do
      let d ← ldDeflateState p
      let x ← q d
      stDeflateState p (g d x)
      k d x) := by
  intro h value after run
  simp only [bind_app] at run
  cases p with
  | none => cases run
  | some r =>
    cases r with
    | tab i =>
      cases get : h.dstates i with
      | none => simp [ldDeflateState, DeflateStateRef.get, get] at run
      | some d =>
        simp only [ldDeflateState, DeflateStateRef.get, get] at run
        cases eq1 : q d h with
        | error _ => simp [eq1] at run
        | ok p1 =>
          rcases p1 with ⟨x, h1⟩
          simp only [eq1] at run
          have rel1 := hq d h x h1 eq1
          cases get1 : h1.dstates i with
          | none => simp [stDeflateState, DeflateStateRef.get, get1] at run
          | some d1 =>
            simp only [stDeflateState, DeflateStateRef.get, get1, DeflateStateRef.isRo] at run
            rw [DeflateStateRef.put_tab get1] at run
            exact rel1.trans ((KeepRel.upd_state get1 (g d x)).trans (hk d x _ value after run))

theorem keep_load8 (p : BPtr) : KeepM (load8 p) := keep_ptr_load p
theorem keep_index8 (p : BPtr) (i : Int) : KeepM (index8 p i) := keep_ptr_index p i
theorem keep_store8 (p : BPtr) (v : UInt8) : KeepM (store8 p v) := keep_ptr_store p v
theorem keep_memcpyB (dst src : BPtr) (n : Nat) : KeepM (memcpyB dst src n) := keep_ptr_memcpy dst src n
theorem keep_memsetB (dst : BPtr) (v : UInt8) (n : Nat) : KeepM (memsetB dst v n) := keep_ptr_fill dst v n

end Zlib.Deflate.Universal.Keep
