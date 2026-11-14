import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.LibcBorrowLoops

/-!
# deflate.c: the parameters of a deflate state are not changed by a deflate call

Batch C of the deflate skeleton (`bound_before_output`). `deflateBound` reads `level`, `w_bits`,
`hash_bits`, the size of the wrapper (`|wrap|`, `gzhead`) and checks the stream with
`deflateStateCheck` (`strm`, a valid `status`, the stream's `state`, `zalloc` and `zfree`). This
module and its successors prove that every returning run of `deflate` keeps these fields of every
deflate state record and of every stream record. The proof is compositional: one lemma per
primitive and per function, like the borrow-stable modules; no callee contract is assumed.

`ParRel keep h h'` is the relation between the heap before and after a run; `keep` says whether
`|wrap|` is kept (`deflateSetDictionary` sets `wrap` to 0 and restores it at the end).
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- The fields of a deflate state record that a deflate call keeps. -/
structure Same (keep : Bool) (d d' : DeflateState) : Prop where
  level : d'.level = d.level
  w_bits : d'.w_bits = d.w_bits
  hash_bits : d'.hash_bits = d.hash_bits
  gzhead : d'.gzhead = d.gzhead
  strm : d'.strm = d.strm
  wrap : keep = true → d'.wrap.toInt.natAbs = d.wrap.toInt.natAbs
  status : GoodStatus d.status → GoodStatus d'.status

theorem Same.refl (keep : Bool) (d : DeflateState) : Same keep d d :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, id⟩

theorem Same.trans {keep : Bool} {a b c : DeflateState} (first : Same keep a b) (second : Same keep b c) :
    Same keep a c :=
  ⟨second.level.trans first.level, second.w_bits.trans first.w_bits, second.hash_bits.trans first.hash_bits,
    second.gzhead.trans first.gzhead, second.strm.trans first.strm,
    fun k => (second.wrap k).trans (first.wrap k), fun g => second.status (first.status g)⟩

/-- The fields of a stream record that a deflate call keeps. -/
structure ZSame (z z' : ZStream) : Prop where
  state : z'.state = z.state
  zalloc : z'.zalloc = z.zalloc
  zfree : z'.zfree = z.zfree

theorem ZSame.refl (z : ZStream) : ZSame z z := ⟨rfl, rfl, rfl⟩

theorem ZSame.trans {a b c : ZStream} (first : ZSame a b) (second : ZSame b c) : ZSame a c :=
  ⟨second.state.trans first.state, second.zalloc.trans first.zalloc, second.zfree.trans first.zfree⟩

/-- Every gz record keeps every field but `strm`, the deflate or inflate stream embedded in it.
`gz_comp` (`gzwrite.c`) writes the gz record around its `deflate` calls; this relation says what a
deflate call on any stream, among them `ZStreamRef.in_gzstate_strm i`, leaves of the gz records. -/
def GzRecordsKept (h h' : Heap) : Prop :=
  ∀ i s, h.gzstates i = some s → ∃ s', h'.gzstates i = some s' ∧ s' = { s with strm := s'.strm }

theorem GzRecordsKept.refl (h : Heap) : GzRecordsKept h h :=
  fun _ s get => ⟨s, get, rfl⟩

theorem GzRecordsKept.of_eq {h h' : Heap} (gz : h'.gzstates = h.gzstates) : GzRecordsKept h h' :=
  fun _ s get => ⟨s, by rw [gz]; exact get, rfl⟩

theorem GzRecordsKept.trans {a b c : Heap} (first : GzRecordsKept a b) (second : GzRecordsKept b c) :
    GzRecordsKept a c := by
  intro i s get
  obtain ⟨s1, get1, e1⟩ := first i s get
  obtain ⟨s2, get2, e2⟩ := second i s1 get1
  refine ⟨s2, get2, ?_⟩
  calc s2 = { s1 with strm := s2.strm } := e2
    _ = { ({ s with strm := s1.strm } : GzState) with strm := s2.strm } :=
        congrArg (fun t : GzState => { t with strm := s2.strm }) e1
    _ = { s with strm := s2.strm } := rfl

/-- Writing a stream record, a table stream or the stream of a gz record, changes no gz record but
in its `strm` field. -/
theorem GzRecordsKept.put_stream (h : Heap) (r : ZStreamRef) (v : ZStream) :
    GzRecordsKept h (r.put h v) := by
  intro j s get
  cases r with
  | tab i =>
    refine ⟨s, ?_, rfl⟩
    simp only [ZStreamRef.put]
    split <;> exact get
  | in_gzstate_strm i =>
    simp only [ZStreamRef.put]
    split
    · next t ht =>
      by_cases same : j = i
      · subst same
        have eq : s = t := Option.some.inj (get.symm.trans ht)
        subst eq
        exact ⟨{ s with strm := v }, by simp, rfl⟩
      · exact ⟨s, by simpa [upd_ne _ _ _ _ same] using get, rfl⟩
    · exact ⟨s, get, rfl⟩

/-- Every deflate state record and every stream record keeps its parameters; every gz record keeps
everything but its stream. -/
def ParRel (keep : Bool) (h h' : Heap) : Prop :=
  (∀ ds d, h.dstates ds = some d → ∃ d', h'.dstates ds = some d' ∧ Same keep d d') ∧
  (∀ (r : ZStreamRef) z, r.get h = some z → ∃ z', r.get h' = some z' ∧ ZSame z z') ∧
  GzRecordsKept h h'

theorem ParRel.refl (keep : Bool) (h : Heap) : ParRel keep h h :=
  ⟨fun _ d get => ⟨d, get, Same.refl keep d⟩, fun _ z get => ⟨z, get, ZSame.refl z⟩, GzRecordsKept.refl h⟩

theorem ParRel.trans {keep : Bool} {a b c : Heap} (first : ParRel keep a b) (second : ParRel keep b c) :
    ParRel keep a c := by
  refine ⟨fun ds d get => ?_, fun r z get => ?_, first.2.2.trans second.2.2⟩
  · obtain ⟨d1, get1, same1⟩ := first.1 ds d get
    obtain ⟨d2, get2, same2⟩ := second.1 ds d1 get1
    exact ⟨d2, get2, same1.trans same2⟩
  · obtain ⟨z1, get1, same1⟩ := first.2.1 r z get
    obtain ⟨z2, get2, same2⟩ := second.2.1 r z1 get1
    exact ⟨z2, get2, same1.trans same2⟩

theorem ParRel.weaken {a b : Heap} (rel : ParRel true a b) : ParRel false a b :=
  ⟨fun ds d get => by
    obtain ⟨d', get', same⟩ := rel.1 ds d get
    exact ⟨d', get', ⟨same.level, same.w_bits, same.hash_bits, same.gzhead, same.strm,
      fun no => absurd no (by decide), same.status⟩⟩,
   rel.2⟩

/-- A heap change outside the state and stream tables. -/
theorem ParRel.quiet {keep : Bool} {h h' : Heap} (states : h'.dstates = h.dstates)
    (streams : h'.streams = h.streams) (gz : h'.gzstates = h.gzstates) : ParRel keep h h' := by
  refine ⟨fun ds d get => ⟨d, by rw [states]; exact get, Same.refl keep d⟩, fun r z get => ⟨z, ?_, ZSame.refl z⟩,
    GzRecordsKept.of_eq gz⟩
  cases r with
  | tab i => simpa only [ZStreamRef.get, streams] using get
  | in_gzstate_strm i => simpa only [ZStreamRef.get, gz] using get

/-- Changing an entry of a table of records in place. -/
theorem Tbl.get_modify_map {β : Type} (t : Tbl (Option β)) (k : Nat) (g : β → β) (x : Nat) :
    (t.modify k (Option.map g)) x = if x = k then (t x).map g else t x := by
  by_cases inside : k < t.arr.size
  · rw [Tbl.modify_eq t k _ inside]
    change (Tbl.get _ x) = _
    rw [Tbl.get_set]
    by_cases same : x = k
    · subst same; simp
    · simp [same]
  · have outside : t k = none := by
      change t.arr.getD k default = none
      simp [Array.getD, inside]
      rfl
    unfold Tbl.modify
    have unchanged : t.arr.modify k (Option.map g) = t.arr := by
      simp [Array.modify, Array.modifyM, inside]
    rw [unchanged]
    by_cases same : x = k
    · subst same; simp [outside]
    · simp [same]

/-- Changing one array field of a deflate state record in place keeps the parameters. -/
theorem ParRel.dstate_array {keep : Bool} {h : Heap} (id : Nat) (g : DeflateState → DeflateState)
    (same : ∀ d, Same keep d (g d)) :
    ParRel keep h { h with dstates := h.dstates.modify id (Option.map g) } := by
  refine ⟨fun ds d get => ?_, fun r z get => ⟨z, ?_, ZSame.refl z⟩, GzRecordsKept.of_eq rfl⟩
  · refine ⟨if ds = id then g d else d, ?_, ?_⟩
    · change (h.dstates.modify id (Option.map g)) ds = _
      rw [Tbl.get_modify_map]
      by_cases same : ds = id
      · subst same; simp [get]
      · simp [same, get]
    · by_cases same' : ds = id
      · simpa [same'] using same d
      · simpa [same'] using Same.refl keep d
  · cases r <;> simpa only [ZStreamRef.get] using get

end Zlib.Deflate.Universal.Params

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec

/-- The parameter fields of a record, exactly, with `last_flush` (only `deflate` itself, its gzip
string loop and the resets write it). -/
def Pars (d : DeflateState) : Int32 × UInt32 × UInt32 × GzHeaderPtr × ZStreamPtr × Int32 × Int32 × Int32 :=
  (d.level, d.w_bits, d.hash_bits, d.gzhead, d.strm, d.wrap, d.status, d.last_flush)

theorem Same.of_pars (keep : Bool) {d d' : DeflateState} (eq : Pars d' = Pars d) : Same keep d d' := by
  simp only [Pars, Prod.mk.injEq] at eq
  obtain ⟨l, w, hb, g, s, wr, st, _⟩ := eq
  exact ⟨l, w, hb, g, s, fun _ => by rw [wr], fun good => by rw [st]; exact good⟩

/-- Every record keeps its parameters exactly; every stream keeps `state` and the allocators; every
gz record keeps everything but its stream. -/
def ExactRel (h h' : Heap) : Prop :=
  (∀ ds d, h.dstates ds = some d → ∃ d', h'.dstates ds = some d' ∧ Pars d' = Pars d) ∧
  (∀ (r : ZStreamRef) z, r.get h = some z → ∃ z', r.get h' = some z' ∧ ZSame z z') ∧
  GzRecordsKept h h'

theorem ExactRel.refl (h : Heap) : ExactRel h h :=
  ⟨fun _ d get => ⟨d, get, rfl⟩, fun _ z get => ⟨z, get, ZSame.refl z⟩, GzRecordsKept.refl h⟩

theorem ExactRel.trans {a b c : Heap} (first : ExactRel a b) (second : ExactRel b c) : ExactRel a c := by
  refine ⟨fun ds d get => ?_, fun r z get => ?_, first.2.2.trans second.2.2⟩
  · obtain ⟨d1, get1, same1⟩ := first.1 ds d get
    obtain ⟨d2, get2, same2⟩ := second.1 ds d1 get1
    exact ⟨d2, get2, same2.trans same1⟩
  · obtain ⟨z1, get1, same1⟩ := first.2.1 r z get
    obtain ⟨z2, get2, same2⟩ := second.2.1 r z1 get1
    exact ⟨z2, get2, same1.trans same2⟩

theorem ExactRel.par {keep : Bool} {h h' : Heap} (rel : ExactRel h h') : ParRel keep h h' :=
  ⟨fun ds d get => by
    obtain ⟨d', get', eq⟩ := rel.1 ds d get
    exact ⟨d', get', Same.of_pars keep eq⟩, rel.2⟩

theorem ExactRel.quiet {h h' : Heap} (states : h'.dstates = h.dstates)
    (streams : h'.streams = h.streams) (gz : h'.gzstates = h.gzstates) : ExactRel h h' := by
  refine ⟨fun ds d get => ⟨d, by rw [states]; exact get, rfl⟩, fun r z get => ⟨z, ?_, ZSame.refl z⟩,
    GzRecordsKept.of_eq gz⟩
  cases r with
  | tab i => simpa only [ZStreamRef.get, streams] using get
  | in_gzstate_strm i => simpa only [ZStreamRef.get, gz] using get

theorem ExactRel.dstate_array {h : Heap} (id : Nat) (g : DeflateState → DeflateState)
    (same : ∀ d, Pars (g d) = Pars d) :
    ExactRel h { h with dstates := h.dstates.modify id (Option.map g) } := by
  refine ⟨fun ds d get => ?_, fun r z get => ⟨z, ?_, ZSame.refl z⟩, GzRecordsKept.of_eq rfl⟩
  · refine ⟨if ds = id then g d else d, ?_, ?_⟩
    · change (h.dstates.modify id (Option.map g)) ds = _
      rw [Tbl.get_modify_map]
      by_cases same : ds = id
      · subst same; simp [get]
      · simp [same, get]
    · by_cases same' : ds = id
      · simpa [same'] using same d
      · simp [same']
  · cases r <;> simpa only [ZStreamRef.get] using get

/-- A returning run keeps every parameter exactly. -/
def ExactM {α : Type} (m : M α) : Prop := ∀ h a h', m h = .ok (a, h') → ExactRel h h'

/-- A returning run keeps every parameter in the sense of `ParRel keep`. -/
def ParM {α : Type} (keep : Bool) (m : M α) : Prop := ∀ h a h', m h = .ok (a, h') → ParRel keep h h'

theorem ExactM.par {α : Type} {keep : Bool} {m : M α} (exact : ExactM m) : ParM keep m :=
  fun h a h' run => (exact h a h' run).par

theorem ExactM.pure {α : Type} (a : α) : ExactM (Pure.pure a : M α) := by
  intro h v h' run; cases run; exact ExactRel.refl h

theorem ExactM.ub {α : Type} (what : String) : ExactM (C.ub what : M α) := by
  intro h v h' run; cases run

theorem ExactM.bind {α β : Type} {m : M α} {f : α → M β} (hm : ExactM m) (hf : ∀ a, ExactM (f a)) :
    ExactM (m >>= f) := by
  intro h value after run
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    exact (hm h a h1 e).trans (hf a h1 value after run)

theorem ExactM.ite {α : Type} (p : Prop) [Decidable p] {a b : M α} (ha : ExactM a) (hb : ExactM b) :
    ExactM (if p then a else b) := by
  split <;> assumption

theorem ParM.pure {α : Type} (keep : Bool) (a : α) : ParM keep (Pure.pure a : M α) := (ExactM.pure a).par

theorem ParM.ub {α : Type} (keep : Bool) (what : String) : ParM keep (C.ub what : M α) := (ExactM.ub what).par

theorem ParM.bind {α β : Type} {keep : Bool} {m : M α} {f : α → M β} (hm : ParM keep m)
    (hf : ∀ a, ParM keep (f a)) : ParM keep (m >>= f) := by
  intro h value after run
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    exact (hm h a h1 e).trans (hf a h1 value after run)

theorem ParM.ite {α : Type} {keep : Bool} (p : Prop) [Decidable p] {a b : M α} (ha : ParM keep a)
    (hb : ParM keep b) : ParM keep (if p then a else b) := by
  split <;> assumption

theorem ExactM.cwhile_go {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, ExactM (cond s)) (hb : ∀ s, ExactM (body s)) (n : Nat) (s : σ) :
    ExactM (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => intro h v after run; cases run
  | succ n ih =>
    rw [cwhile.go]
    apply ExactM.bind (hc s)
    rintro ⟨c, s'⟩
    apply ExactM.ite
    · exact ExactM.bind (hb s') (fun t => ih t)
    · exact ExactM.pure _

theorem ExactM.cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, ExactM (cond s)) (hb : ∀ s, ExactM (body s)) (s : σ) :
    ExactM (C.cwhile cond body s) := ExactM.cwhile_go cond body hc hb fuel s

theorem ExactM.cdoWhile_go {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, ExactM (body s)) (hc : ∀ s, ExactM (cond s)) (n : Nat) (s : σ) :
    ExactM (cdoWhile.go body cond n s) := by
  induction n generalizing s with
  | zero => intro h v after run; cases run
  | succ n ih =>
    rw [cdoWhile.go]
    apply ExactM.bind (hb s)
    intro s'
    apply ExactM.bind (hc s')
    rintro ⟨c, t⟩
    exact ExactM.ite _ (ih t) (ExactM.pure _)

theorem ExactM.cdoWhile {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, ExactM (body s)) (hc : ∀ s, ExactM (cond s)) (s : σ) :
    ExactM (C.cdoWhile body cond s) := ExactM.cdoWhile_go body cond hb hc fuel s

theorem ParM.cwhile_go {σ : Type} {keep : Bool} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, ParM keep (cond s)) (hb : ∀ s, ParM keep (body s)) (n : Nat) (s : σ) :
    ParM keep (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => intro h v after run; cases run
  | succ n ih =>
    rw [cwhile.go]
    apply ParM.bind (hc s)
    rintro ⟨c, s'⟩
    apply ParM.ite
    · exact ParM.bind (hb s') (fun t => ih t)
    · exact ParM.pure _ _

theorem ParM.cwhile {σ : Type} {keep : Bool} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, ParM keep (cond s)) (hb : ∀ s, ParM keep (body s)) (s : σ) :
    ParM keep (C.cwhile cond body s) := ParM.cwhile_go cond body hc hb fuel s

theorem ParM.cdoWhile_go {σ : Type} {keep : Bool} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, ParM keep (body s)) (hc : ∀ s, ParM keep (cond s)) (n : Nat) (s : σ) :
    ParM keep (cdoWhile.go body cond n s) := by
  induction n generalizing s with
  | zero => intro h v after run; cases run
  | succ n ih =>
    rw [cdoWhile.go]
    apply ParM.bind (hb s)
    intro s'
    apply ParM.bind (hc s')
    rintro ⟨c, t⟩
    exact ParM.ite _ (ih t) (ParM.pure _ _)

theorem ParM.cdoWhile {σ : Type} {keep : Bool} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, ParM keep (body s)) (hc : ∀ s, ParM keep (cond s)) (s : σ) :
    ParM keep (C.cdoWhile body cond s) := ParM.cdoWhile_go body cond hb hc fuel s

end Zlib.Deflate.Universal.Params
