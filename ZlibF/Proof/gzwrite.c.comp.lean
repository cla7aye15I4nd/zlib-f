import ZlibF.Proof.«gzwrite.c.upto-input»
import ZlibF.Proof.«gz.read-store»
import ZlibF.Proof.«gz.record-free»
import ZlibF.Proof.«deflate.c.quiet-call»
import ZlibF.Proof.«deflate.c.quiet-in-stored»
import ZlibF.Proof.«deflate.c.universal-params-gz»
import ZlibF.Proof.«deflate.c.universal-ops-reset»
import ZlibF.Proof.«gzfs.borrowed-error»
import ZlibF.Proof.«libc-errno-cstring»

/-!
# gzwrite.c: safety of `gz_comp`

Part 1: the plumbing. A Hoare-style total run predicate over the gz world (`Ok`), the two loop forms of the
translation with a measure over the world, the contract of `write` (M2), and the source split of `gz_comp`
into its loops.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

/-! ## Running a computation of the gz world -/

theorem cbind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with
      | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases he : m fs h with
  | error e => rfl
  | ok result => obtain ⟨⟨a, fs1⟩, h1⟩ := result; rfl

theorem clift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with
      | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

theorem cpure_app {α : Type} (a : α) (fs : Fs) (h : Heap) :
    (pure a : G α) fs h = .ok ((a, fs), h) := rfl

/-- `m` returns from `(fs, h)` with a result satisfying `P`. -/
def Ok {α : Type} (m : G α) (fs : Fs) (h : Heap) (P : α → Fs → Heap → Prop) : Prop :=
  ∃ a fs' h', m fs h = .ok ((a, fs'), h') ∧ P a fs' h'

theorem Ok.mono {α : Type} {m : G α} {fs : Fs} {h : Heap} {P Q : α → Fs → Heap → Prop}
    (hm : Ok m fs h P) (hpq : ∀ a fs' h', P a fs' h' → Q a fs' h') : Ok m fs h Q := by
  obtain ⟨a, fs', h', run, p⟩ := hm
  exact ⟨a, fs', h', run, hpq a fs' h' p⟩

theorem Ok.bind {α β : Type} {m : G α} {f : α → G β} {fs : Fs} {h : Heap} {P : α → Fs → Heap → Prop}
    {Q : β → Fs → Heap → Prop} (hm : Ok m fs h P) (hf : ∀ a fs' h', P a fs' h' → Ok (f a) fs' h' Q) :
    Ok (m >>= f) fs h Q := by
  obtain ⟨a, fs1, h1, run, p⟩ := hm
  obtain ⟨b, fs2, h2, run2, q⟩ := hf a fs1 h1 p
  exact ⟨b, fs2, h2, by rw [cbind_app, run]; exact run2, q⟩

theorem Ok.pure {α : Type} {a : α} {fs : Fs} {h : Heap} {P : α → Fs → Heap → Prop} (p : P a fs h) :
    Ok (Pure.pure a : G α) fs h P := ⟨a, fs, h, rfl, p⟩

theorem Ok.lift {α : Type} {m : M α} {fs : Fs} {h h' : Heap} {a : α} {P : α → Fs → Heap → Prop}
    (run : m h = .ok (a, h')) (p : P a fs h') : Ok (StateT.lift m : G α) fs h P :=
  ⟨a, fs, h', by rw [clift_app, run], p⟩

/-- A computation that returns is safe in the sense of `RunSafe`. -/
theorem runSafe_of_ok {α : Type} {m : G α} {fs : Fs} {h : Heap} {P : α → Fs → Heap → Prop}
    (hm : Ok m fs h P) : RunSafe m fs h True P := by
  obtain ⟨a, fs', h', run, p⟩ := hm
  refine ⟨fun e he => ?_, fun _ => ⟨a, fs', h', run⟩, fun a' fs'' h'' he => ?_⟩
  · rw [run] at he; cases he
  · rw [run] at he
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    exact p

/-! ## Loops with a measure over the world -/

theorem gwhile_go_spec {σ : Type} (cond : σ → G (Bool × σ)) (body : σ → G σ)
    (J Post : σ → Fs → Heap → Prop) (μ : σ → Fs → Heap → Nat)
    (step : ∀ x fs h, J x fs h → ∃ c y fs1 h1, cond x fs h = .ok (((c, y), fs1), h1) ∧
      (c = false → Post y fs1 h1) ∧
      (c = true → ∃ z fs2 h2, body y fs1 h1 = .ok ((z, fs2), h2) ∧ J z fs2 h2 ∧ μ z fs2 h2 < μ x fs h)) :
    ∀ n x fs h, J x fs h → μ x fs h < n →
      ∃ z fs' h', Zlib.GzFs.gwhile.go cond body n x fs h = .ok ((z, fs'), h') ∧ Post z fs' h' := by
  intro n
  induction n with
  | zero => intro x fs h _ hm; omega
  | succ n ih =>
    intro x fs h hJ hm
    obtain ⟨c, y, fs1, h1, hc, hstop, hcont⟩ := step x fs h hJ
    rw [Zlib.GzFs.gwhile.go, cbind_app, hc]
    dsimp only
    cases c with
    | true =>
      obtain ⟨z, fs2, h2, hb, hJ', hlt⟩ := hcont rfl
      simp only [ite_true]
      rw [cbind_app, hb]
      exact ih z fs2 h2 hJ' (by omega)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨y, fs1, h1, rfl, hstop rfl⟩

theorem gdoWhile_go_spec' {σ : Type} (body : σ → G σ) (cond : σ → G (Bool × σ))
    (J Post : σ → Fs → Heap → Prop) (μ : σ → Fs → Heap → Nat)
    (step : ∀ x fs h, J x fs h → ∃ y fs1 h1, body x fs h = .ok ((y, fs1), h1) ∧
      ∃ c z fs2 h2, cond y fs1 h1 = .ok (((c, z), fs2), h2) ∧
        (c = true → J z fs2 h2 ∧ μ z fs2 h2 < μ x fs h) ∧ (c = false → Post z fs2 h2)) :
    ∀ n x fs h, J x fs h → μ x fs h < n →
      ∃ z fs' h', Zlib.GzFs.gdoWhile.go body cond n x fs h = .ok ((z, fs'), h') ∧ Post z fs' h' := by
  intro n
  induction n with
  | zero => intro x fs h _ hm; omega
  | succ n ih =>
    intro x fs h hJ hm
    obtain ⟨y, fs1, h1, hb, c, z, fs2, h2, hc, hcont, hstop⟩ := step x fs h hJ
    rw [Zlib.GzFs.gdoWhile.go, cbind_app, hb]
    dsimp only
    rw [cbind_app, hc]
    dsimp only
    cases c with
    | true =>
      obtain ⟨hJ', hlt⟩ := hcont rfl
      simp only [ite_true]
      exact ih z fs2 h2 hJ' (by omega)
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨z, fs2, h2, rfl, hstop rfl⟩

/-! ## The contract of `write` (M2) for every oracle value -/

theorem arr_set_get {α : Type} (a : Array α) (j i : Nat) (v : α) :
    (a.set! j v)[i]? = if j = i then (if j < a.size then some v else none) else a[i]? := by
  simp [Array.set!, Array.getElem?_setIfInBounds]

/-- **M2 for the regular-file write**: `-1`, or for a nonempty buffer a count `k` with `1 ≤ k ≤ bs.size`; the file
system stays well formed and no descriptor opens or closes. -/
theorem fsWriteReg_contract (fd : Int32) (bs : Array UInt8) (w : Fs) (hfs : FileSystem w) (hne : bs.size ≠ 0)
    (hsmall : bs.size < 2 ^ 63) :
    ∃ r w', fsWriteReg fd bs w = (Pure.pure (r, w') : M (Int64 × Fs)) ∧
      (r = -1 ∨ (1 ≤ r.toInt ∧ r.toInt ≤ bs.size)) ∧ FileSystem w' ∧ FdsKept w w' := by
  obtain ⟨hlim, hnames, hfds, hnodes⟩ := hfs
  have hemp : bs.isEmpty = false := by
    cases e : bs.isEmpty
    · rfl
    · exact absurd (Array.isEmpty_iff_size_eq_zero.mp e) hne
  unfold fsWriteReg
  dsimp only
  split
  · exact ⟨_, _, rfl, Or.inl rfl, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl⟩
  · rename_i hbad
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbad
    obtain ⟨hpos, hlt⟩ := hbad
    have hj : fd.toInt.toNat < w.fds.size := by
      have : ¬ fd.toInt < 0 := fun x => hpos (Int32.lt_iff_toInt_lt.mpr (by simpa using x))
      omega
    split
    · exact ⟨_, _, rfl, Or.inl rfl, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl⟩
    · rename_i of hof
      have hget : w.fds[fd.toInt.toNat]? = some (some of) := by
        rw [getElem!_pos w.fds _ hj] at hof
        rw [Array.getElem?_eq_getElem hj, hof]
      split
      · exact ⟨_, _, rfl, Or.inl rfl, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl⟩
      · rw [hemp]
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hnode, hopos, hwr⟩ := hfds _ _ hget
        have hnd : w.nodes[of.node]? = some w.nodes[of.node]! := by
          rw [getElem!_pos w.nodes _ hnode]; simp [hnode]
        have hsz := hnodes _ _ hnd
        generalize hp : (if of.append = true then (w.nodes[of.node]!).data.size else of.pos) = pos
        split
        · exact ⟨_, _, rfl, Or.inl rfl, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl⟩
        · rename_i hroom
          have hpl : pos < w.fsizeLimit := by simpa using hroom
          generalize hk : min bs.size (w.fsizeLimit - pos) = k
          have hk1 : 1 ≤ k := by omega
          have hkb : k ≤ bs.size := by omega
          refine ⟨_, _, rfl, Or.inr ⟨?_, ?_⟩, ⟨hlim, fun p n hm => by simpa using hnames p n hm, ?_, ?_⟩, ?_⟩
          · rw [Int64.toInt_ofNat', Zlib.Gzlib.Proofs.bmod64 _ (by omega) (by omega)]
            omega
          · rw [Int64.toInt_ofNat', Zlib.Gzlib.Proofs.bmod64 _ (by omega) (by omega)]
            omega
          · intro j file hi
            rw [arr_set_get] at hi
            by_cases e : fd.toInt.toNat = j
            · subst e
              rw [if_pos rfl, if_pos hj] at hi
              simp only [Option.some.injEq] at hi
              subst hi
              refine ⟨by simpa using hnode, ?_, fun node hn hd => ?_⟩
              · show pos + k ≤ 2 ^ 63 - 1
                omega
              · rw [arr_set_get, if_pos rfl, if_pos hnode] at hn
                simp only [Option.some.injEq] at hn
                subst hn
                exact hwr _ hnd hd
            · rw [if_neg e] at hi
              obtain ⟨n1, n2, n3⟩ := hfds j file hi
              refine ⟨by simpa using n1, n2, fun node hn hd => ?_⟩
              rw [arr_set_get] at hn
              by_cases e2 : of.node = file.node
              · rw [if_pos e2, if_pos hnode] at hn
                simp only [Option.some.injEq] at hn
                subst hn
                have hnd' : w.nodes[file.node]? = some w.nodes[of.node]! := e2 ▸ hnd
                exact n3 _ hnd' hd
              · rw [if_neg e2] at hn
                exact n3 node hn hd
          · intro j node hn
            rw [arr_set_get] at hn
            by_cases e : of.node = j
            · rw [if_pos e, if_pos hnode] at hn
              simp only [Option.some.injEq] at hn
              subst hn
              dsimp only
              by_cases hc : pos > (w.nodes[of.node]!).data.size
              · simp only [hc, ↓reduceIte, Array.size_append, Array.size_extract, Array.size_replicate]
                omega
              · simp only [hc, ↓reduceIte, Array.size_append, Array.size_extract]
                omega
            · rw [if_neg e] at hn
              exact hnodes j node hn
          · intro j
            unfold GzOracle.FdOpen
            rw [arr_set_get]
            by_cases e : fd.toInt.toNat = j
            · subst e
              rw [if_pos rfl, if_pos hj]
              exact ⟨fun _ => ⟨of, hget⟩, fun _ => ⟨_, rfl⟩⟩
            · rw [if_neg e]

/-- **M2, the contract of `write`, for every oracle value**: `-1`, or `k` with `1 ≤ k ≤ bs.size` for a nonempty
buffer. The heap is untouched, the file system stays well formed and no descriptor opens or closes. -/
theorem fsWrite_contract_m (fd : Int32) (bs : Array UInt8) (w : Fs) (hfs : FileSystem w)
    (hne : bs.size ≠ 0) (hsmall : bs.size < 2 ^ 63) :
    ∃ r w', fsWrite fd bs w = (Pure.pure (r, w') : M (Int64 × Fs)) ∧
      (r = -1 ∨ (1 ≤ r.toInt ∧ r.toInt ≤ bs.size)) ∧ FileSystem w' ∧ FdsKept w w' := by
  have hemp : bs.isEmpty = false := by
    cases e : bs.isEmpty
    · rfl
    · exact absurd (Array.isEmpty_iff_size_eq_zero.mp e) hne
  unfold fsWrite
  dsimp only
  split
  · obtain ⟨r, w1, e, hres, hfs1, hk1⟩ := fsWriteReg_contract fd bs (tickW w) hfs hne hsmall
    rw [e]
    by_cases hr : r = -1
    · refine ⟨r, _, rfl, hres, ?_, ?_⟩
      · simp only [hr, ite_true]; exact hfs1
      · intro j; simp only [hr, ite_true]; exact (hk1 j).trans Iff.rfl
    · obtain ⟨ho1, ho2⟩ := fs_okErr (w.okErrno w.nos) w1 hfs1
      refine ⟨r, _, rfl, hres, ?_, ?_⟩
      · simp only [hr, ite_false]; exact ho1
      · intro j; simp only [hr, ite_false]; exact (ho2 j).trans ((hk1 j).trans Iff.rfl)
  · exact ⟨-1, _, rfl, Or.inl rfl, hfs, fun _ => Iff.rfl⟩
  · rename_i k _
    obtain ⟨ho1, ho2⟩ := fs_okErr (w.okErrno w.nos) (tickW w) hfs
    refine ⟨_, _, rfl, Or.inr ?_, ho1, fun j => (ho2 j).trans Iff.rfl⟩
    rw [hemp]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hm : 1 ≤ max 1 (min k bs.size) ∧ max 1 (min k bs.size) ≤ bs.size := by omega
    rw [Int64.toInt_ofNat', Zlib.Gzlib.Proofs.bmod64 _ (by omega) (by omega)]
    omega

/-- **M2, the contract of `write`, for every oracle value**: `-1`, or `k` with `1 ≤ k ≤ bs.size` for a nonempty
buffer. The heap is untouched, the file system stays well formed and no descriptor opens or closes. -/
theorem fsWrite_contract (fd : Int32) (bs : Array UInt8) (w : Fs) (h : Heap) (hfs : FileSystem w)
    (hne : bs.size ≠ 0) (hsmall : bs.size < 2 ^ 63) :
    ∃ r w', fsWrite fd bs w h = .ok ((r, w'), h) ∧
      (r = -1 ∨ (1 ≤ r.toInt ∧ r.toInt ≤ bs.size)) ∧ FileSystem w' ∧ FdsKept w w' := by
  obtain ⟨r, w', e, p⟩ := fsWrite_contract_m fd bs w hfs hne hsmall
  exact ⟨r, w', by rw [e]; rfl, p⟩

/-! ## The source split of `gz_comp` -/

/-- The length of one transparent write. -/
def dirPut (max x : UInt32) : UInt32 := if x > max then max else x

/-- The length of one write of the output buffer. -/
def outPut (max : UInt32) (d : Int64) : UInt32 := if d > (Int64.ofNat max.toNat) then max else d.toUInt64.toUInt32

/-- The condition of the transparent write loop. -/
def directCond (i : Nat) (r : Option Int32) : G (Bool × Option Int32) := do
  if r.isSome then return (false, r)
  return ((← ldZ (strmOf (gzSt i))).avail_in != 0, r)

/-- The body of the transparent write loop. -/
def directBody (i : Nat) (_r : Option Int32) : G (Option Int32) := do
  let strm := strmOf (gzSt i)
  let state := gzSt i
  let max : UInt32 := (((0 : UInt32) - 1) >>> 2) + 1
  setErrno 0
  updS state fun s => { s with again := 0 }
  let z ← ldZ strm
  let s ← ldS state
  let put : UInt32 := dirPut max z.avail_in
  let bs ← loadBytes z.next_in put.toNat
  let writ := (← fsWrite s.fd bs).toInt32
  if writ < 0 then
    if BLOCKED (← getErrno) then updS state fun s => { s with again := 1 }
    Zlib.Gzlib.gz_error state Z_ERRNO (← zstrerror)
    return some (-1)
  let z ← ldZ strm
  let np ← z.next_in.add writ.toInt
  updZ strm fun z => { z with avail_in := z.avail_in - writ.toUInt32, next_in := np }
  return none

/-- The condition of the write-out loop. -/
def outCond (i : Nat) (r : Option Int32) : G (Bool × Option Int32) := do
  if r.isSome then return (false, r)
  let z ← ldZ (strmOf (gzSt i))
  let s ← ldS (gzSt i)
  return (← Ptr.lt s.x.next z.next_out, r)

/-- The body of the write-out loop. -/
def outBody (i : Nat) (_r : Option Int32) : G (Option Int32) := do
  let strm := strmOf (gzSt i)
  let state := gzSt i
  let max : UInt32 := (((0 : UInt32) - 1) >>> 2) + 1
  setErrno 0
  updS state fun s => { s with again := 0 }
  let z ← ldZ strm
  let s ← ldS state
  let d ← Ptr.diff z.next_out s.x.next
  let put : UInt32 := outPut max d
  let bs ← loadBytes s.x.next put.toNat
  let writ := (← fsWrite s.fd bs).toInt32
  if writ < 0 then
    if BLOCKED (← getErrno) then updS state fun s => { s with again := 1 }
    Zlib.Gzlib.gz_error state Z_ERRNO (← zstrerror)
    return some (-1)
  let s ← ldS state
  let nx ← s.x.next.add writ.toInt
  updX state fun x => { x with next := nx }
  return none

/-- The body of the deflate loop. -/
def compBody (i : Nat) (flush : Int32) (l : Zlib.Gzwrite.CompLoop) : G Zlib.Gzwrite.CompLoop := do
  let strm := strmOf (gzSt i)
  let state := gzSt i
  let z ← ldZ strm
  let mut l := l
  if z.avail_out == 0 || (flush != Z_NO_FLUSH && (flush != Z_FINISH || l.ret == Z_STREAM_END)) then
    let r ← gwhile (outCond i) (outBody i) none
    if r.isSome then return { l with res := r }
    if (← ldZ strm).avail_out == 0 then
      let s ← ldS state
      updZ strm fun z => { z with avail_out := s.size, next_out := s.out }
      updX state fun x => { x with next := s.out }
  let hv := (← ldZ strm).avail_out
  let ret ← Zlib.Deflate.deflate strm flush
  if ret == Z_STREAM_ERROR then
    Zlib.Gzlib.gz_error state Z_STREAM_ERROR (← Zlib.GzFs.strLit "internal error: deflate stream corrupt")
    return { l with ret, res := some (-1) }
  return { l with ret, «have» := hv - (← ldZ strm).avail_out }

/-- The condition of the deflate loop. -/
def compCond (l : Zlib.Gzwrite.CompLoop) : G (Bool × Zlib.Gzwrite.CompLoop) :=
  Pure.pure (l.res.isNone && l.«have» != 0, l)

theorem gz_comp_source (i : Nat) (flush : Int32) :
    Zlib.Gzwrite.gz_comp (gzSt i) flush = (do
      if (← ldS (gzSt i)).size == 0 then
        if (← Zlib.Gzwrite.gz_init (gzSt i)) == -1 then return -1
      if (← ldS (gzSt i)).direct != 0 then
        let r ← gwhile (directCond i) (directBody i) none
        return r.getD 0
      if (← ldS (gzSt i)).reset != 0 then
        let z ← ldZ (strmOf (gzSt i))
        if z.avail_in == 0 && flush == Z_NO_FLUSH then return 0
        let _ ← Zlib.Deflate.deflateReset (strmOf (gzSt i))
        updS (gzSt i) fun s => { s with reset := 0 }
      let l ← gdoWhile (compBody i flush) compCond { ret := Z_OK, «have» := 0, res := none }
      if let some r := l.res then return r
      if flush == Z_FINISH then updS (gzSt i) fun s => { s with reset := 1 }
      return 0) := rfl

/-! ## The writer invariant across a step of `gz_comp`

A step of `gz_comp` changes the record only in the stream, `x.next`, `again` and `reset`, may change the blocks of
the codec and the bytes of the data buffers, and keeps the live blocks. `inv_codec_step` re-establishes `GzInv`
of the record with no pending input; `upTo_step` lifts it to `GzInvUpToInput`. -/

open ZlibF.Spec.Public.GzRead (DataBuf)

/-- The fields of the record a step of `gz_comp` keeps. -/
def SameShape (t t' : GzState) : Prop :=
  t'.path = t.path ∧ t'.msg = t.msg ∧ t'.«in» = t.«in» ∧ t'.out = t.out ∧ t'.size = t.size ∧
    t'.mode = t.mode ∧ t'.direct = t.direct ∧ t'.want = t.want ∧ t'.err = t.err ∧ t'.skip = t.skip ∧
    t'.x.pos = t.x.pos ∧ t'.x.have = t.x.have ∧ t'.fd = t.fd

theorem SameShape.refl (t : GzState) : SameShape t t :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameShape.trans {a b c : GzState} (x : SameShape a b) (y : SameShape b c) : SameShape a c := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13⟩ := x
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13⟩ := y
  exact ⟨y1.trans x1, y2.trans x2, y3.trans x3, y4.trans x4, y5.trans x5, y6.trans x6, y7.trans x7,
    y8.trans x8, y9.trans x9, y10.trans x10, y11.trans x11, y12.trans x12, y13.trans x13⟩

/-- The input of the stream advanced by what was consumed: `next_in + avail_in` is kept. -/
def InTrack (t t' : GzState) : Prop :=
  ∃ used, t'.strm.next_in = advance t.strm.next_in used ∧ t'.strm.avail_in.toNat + used = t.strm.avail_in.toNat

theorem advance_zero (p : BPtr) : advance p 0 = p := by
  cases p <;> rfl

theorem advance_advance (p : BPtr) (a b : Nat) : advance (advance p a) b = advance p (a + b) := by
  cases p <;> simp [advance, Nat.add_assoc]

theorem InTrack.of_in {t t' : GzState} (hn : t'.strm.next_in = t.strm.next_in)
    (ha : t'.strm.avail_in = t.strm.avail_in) : InTrack t t' :=
  ⟨0, by rw [hn, advance_zero], by rw [ha]; rfl⟩

theorem InTrack.refl (t : GzState) : InTrack t t := InTrack.of_in rfl rfl

theorem InTrack.trans {a b c : GzState} (x : InTrack a b) (y : InTrack b c) : InTrack a c := by
  obtain ⟨u, hu, hu'⟩ := x
  obtain ⟨v, hv, hv'⟩ := y
  exact ⟨u + v, by rw [hv, hu, advance_advance], by omega⟩

theorem InTrack.le {t t' : GzState} (x : InTrack t t') : t'.strm.avail_in.toNat ≤ t.strm.avail_in.toNat := by
  obtain ⟨u, -, hu⟩ := x
  omega

/-- The output clause W5 of a record. -/
def OutW5 (t : GzState) : Prop :=
  ∃ b c, t.strm.next_out = padv t.out b ∧ t.strm.avail_out.toNat = t.size.toNat - b ∧
    t.x.next = padv t.out c ∧ c ≤ b ∧ b ≤ t.size.toNat

/-- The pending-input clause of `GzInvUpToInput`: `next_in` is NULL with no pending input, or inside the input
region. -/
def NextInOk (s : GzState) (src : Region) : Prop :=
  (s.strm.next_in = .null ∧ s.strm.avail_in = 0) ∨
    ∃ a, s.strm.next_in = padv src.pointer a ∧ a + s.strm.avail_in.toNat ≤ src.length

section step
variable {i : Nat}

theorem owned_of_shape {H H' : Heap} {t t' : GzState} (sh : SameShape t t')
    (hso : ∀ b, StreamOwned H' (gzStrm i) b ↔ StreamOwned H (gzStrm i) b) (b : Nat) :
    GzOwned H' i t' b ↔ GzOwned H i t b := by
  obtain ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, -⟩ := sh
  unfold GzOwned
  rw [hpath, hmsg, hsize, hin, hmode, hdirect, hout,
    show StreamOwned H' (.in_gzstate_strm i) b ↔ StreamOwned H (.in_gzstate_strm i) b from hso b]

/-- **`GzInv` of a compressing writer across a step that changes the stream, the codec's blocks and the bytes of
the data buffers.** -/
theorem inv_codec_step {H H' : Heap} {t t' : GzState}
    (inv : GzInv H i t) (hw : t.mode = GZ_WRITE) (hd : t.direct = 0) (hz : t.size ≠ 0)
    (rec' : H'.gzstates i = some t') (sh : SameShape t t')
    (fr : Frame H H' (fun b => b = i ∨ StreamOwned H (gzStrm i) b ∨ DataBuf t b))
    (hdata : ∀ b, DataBuf t b → (∃ a a', H.bytes b = some a ∧ H'.bytes b = some a' ∧ a'.size = a.size) ∧
      H'.ro b = H.ro b)
    (hso : ∀ b, StreamOwned H' (gzStrm i) b ↔ StreamOwned H (gzStrm i) b)
    (hlive : ∀ b, H'.live b ↔ H.live b)
    (fresh : Fresh H') (uniq : Zlib.Gzlib.Spec.Uniq H') (globals : LibraryGlobals H')
    (fit : ZlibF.PlatformMemory.ByteObjectsFit H')
    (codec : StreamReachable .deflate H' (gzStrm i) ∧ ∃ z k d, (gzStrm i).get H' = some z ∧
      z.state = some (.deflate k) ∧ H'.dstates k = some d ∧ d.gzhead = none)
    (reset' : t'.reset = 0 ∨ t'.reset = 1) (input' : t'.strm.next_in = .null ∧ t'.strm.avail_in = 0)
    (output' : OutW5 t') :
    GzInv H' i t' ∧ ∀ b, GzOwned H' i t' b ↔ GzOwned H i t b := by
  have c := inv.common
  have w := inv.writer hw
  have hown := owned_of_shape sh hso
  obtain ⟨hpath, hmsg, hin, hout, hsize, hmode, hdirect, hwant, herr, hskip, hpos, hhave, -⟩ := sh
  have kept : ∀ b, GzOwned H i t b → ¬ DataBuf t b → b ≠ i → ¬ StreamOwned H (gzStrm i) b →
      H'.bytes b = H.bytes b ∧ H'.words b = H.words b ∧ H'.streams b = H.streams b ∧
      H'.gzheaders b = H.gzheaders b ∧ H'.dstates b = H.dstates b ∧ H'.istates b = H.istates b ∧
      H'.gzstates b = H.gzstates b ∧ H'.ro b = H.ro b := by
    intro b ho hdb hbi hsb
    exact fr.2.2.2.2.2 b (c.live b ho) (by rintro (e | e | e) <;> contradiction)
  have hptrs : ownedPtrs t' = ownedPtrs t := by
    unfold ownedPtrs
    rw [hpath, hmsg, hsize, hin, hmode, hdirect, hout]
  have sep : ∀ p, p ∈ ownedPtrs t → ∀ b, blkOf p = some b → b ≠ i ∧ ¬ StreamOwned H (gzStrm i) b :=
    c.distinct.2
  have hexact : ∀ p n, (∀ b, p = .ref (.blk b) 0 → DataBuf t b) → ExactBuffer H p n → ExactBuffer H' p n := by
    intro p n own hx
    obtain ⟨b, a, hp, hb, hr, hsz⟩ := hx
    obtain ⟨⟨a0, a', h0, ha', hs'⟩, hro⟩ := hdata b (own b hp)
    rw [hb] at h0; cases h0
    exact ⟨b, a', hp, ha', by rw [hro]; exact hr, by rw [hs']; exact hsz⟩
  have hmallocK : ∀ p n b, p = .ref (.blk b) 0 → GzOwned H i t b → ¬ DataBuf t b → b ≠ i →
      ¬ StreamOwned H (gzStrm i) b → MallocBuffer H p n → MallocBuffer H' p n := by
    intro p n b hp ho hdb hbi hsb hx
    obtain ⟨b', a, hp', hb, hr, hsz⟩ := hx
    rw [hp] at hp'; cases hp'
    obtain ⟨e1, -, -, -, -, -, -, e8⟩ := kept b ho hdb hbi hsb
    exact ⟨b, a, hp, by rw [e1]; exact hb, by rw [e8]; exact hr, hsz⟩
  refine ⟨⟨?_, fun hr => absurd (hmode.trans hw) (by rw [hr]; decide), fun _ => ?_⟩, hown⟩
  · exact {
      record := rec'
      mode := hmode ▸ c.mode
      fresh := fresh
      uniq := uniq
      globals := globals
      fit := fit
      path := by
        obtain ⟨p, hc, hm⟩ := c.path
        obtain ⟨pb, a, hp, hb, hr, hn⟩ := hm
        have own : GzOwned H i t pb := Or.inr (Or.inl hp)
        have hmem : t.path ∈ ownedPtrs t := by simp [ownedPtrs]
        obtain ⟨hbi, hsb⟩ := sep _ hmem pb (by rw [hp]; rfl)
        have hdb : ¬ DataBuf t pb := fun x => (GzRead.GzInv.data_separate inv x).2.2.1 hp
        obtain ⟨e1, -⟩ := kept pb own hdb hbi hsb
        refine ⟨p, ?_, hmallocK _ _ pb (hpath.trans hp) own hdb hbi hsb ⟨pb, a, hpath.trans hp, hb, hr, hn⟩⟩
        rw [hpath, hp]
        rw [hp] at hc
        exact (cstring_blk_congr e1).2 hc
      msg := by
        rcases c.msg with hn | ⟨m, hc, hm⟩
        · exact Or.inl (hmsg ▸ hn)
        · obtain ⟨mb, a, hp, hb, hr, hn⟩ := hm
          have own : GzOwned H i t mb := Or.inr (Or.inr (Or.inl hp))
          have hmem : t.msg ∈ ownedPtrs t := by simp [ownedPtrs]
          obtain ⟨hbi, hsb⟩ := sep _ hmem mb (by rw [hp]; rfl)
          have hdb : ¬ DataBuf t mb := fun x => (GzRead.GzInv.data_separate inv x).2.2.2 hp
          obtain ⟨e1, -⟩ := kept mb own hdb hbi hsb
          refine Or.inr ⟨m, ?_, hmallocK _ _ mb (hmsg.trans hp) own hdb hbi hsb ⟨mb, a, hmsg.trans hp, hb, hr, hn⟩⟩
          rw [hmsg, hp]
          rw [hp] at hc
          exact (cstring_blk_congr e1).2 hc
      memerr := fun e => hmsg ▸ c.memerr (herr ▸ e)
      want := hwant ▸ c.want
      size := by rw [hsize, hwant]; exact c.size
      distinct := ⟨hptrs ▸ c.distinct.1, fun p hp b hb =>
        ⟨(c.distinct.2 p (hptrs ▸ hp) b hb).1, by rw [hso]; exact (c.distinct.2 p (hptrs ▸ hp) b hb).2⟩⟩
      live := fun b hb => (hlive b).2 (c.live b ((hown b).1 hb))
      pos := by rw [hskip, hpos, hhave]; exact c.pos
      next := fun _ => by
        obtain ⟨b, cc, -, -, hx, hcb, hbs⟩ := output'
        obtain ⟨ob, oa, hop, hob, -, hos⟩ := (w.bufs hz).2 hd
        have hdbo : DataBuf t ob := ⟨hz, Or.inr ⟨Or.inr hd, hop⟩⟩
        obtain ⟨⟨a0, a', h0, ha', hs'⟩, -⟩ := hdata ob hdbo
        rw [hob] at h0; cases h0
        refine ⟨ob, cc, a', by rw [hx, hout, hop]; simp [padv], ?_, ?_, ?_, ha', ?_⟩
        · exact (GzRead.GzInv.data_separate inv hdbo).1
        · exact (hown ob).2 hdbo.owned
        · rw [hmsg]
          intro e
          rcases c.msg with hn | ⟨m, _, mb, _, hp, _⟩
          · rw [hn] at e; cases e
          · rw [hp] at e
            simp only [blkOf, Option.some.injEq] at e
            subst e
            exact (GzRead.GzInv.data_separate inv hdbo).2.2.2 hp
        · rw [hhave, w.have0, hs', hos]
          rw [hsize] at hbs
          simp only [UInt32.toNat_zero, Nat.add_zero]
          omega
      nullHave := fun _ => by rw [hhave]; exact w.have0
      recordFree := fun hn => c.recordFree ((hso i).1 hn) }
  · exact {
      have0 := by rw [hhave]; exact w.have0
      direct := Or.inl (hdirect.trans hd)
      reset := reset'
      unalloc := fun e => absurd (hsize.symm.trans e) hz
      bufs := fun _ => by
        rw [hin, hout, hsize]
        refine ⟨hexact _ _ (fun b hp => ⟨hz, Or.inl hp⟩) (w.bufs hz).1, fun _ =>
          hexact _ _ (fun b hp => ⟨hz, Or.inr ⟨Or.inr hd, hp⟩⟩) ((w.bufs hz).2 hd)⟩
      input := Or.inl input'
      output := fun _ _ => output'
      codec := fun _ _ => codec
      transparent := fun e => absurd (hdirect.trans hd) e }

/-- The stream a record write leaves: only the four buffer fields may differ. -/
def BufOnly (z z' : ZStream) : Prop :=
  z' = { z with next_in := z'.next_in, avail_in := z'.avail_in, next_out := z'.next_out, avail_out := z'.avail_out }

theorem BufOnly.state {z z' : ZStream} (e : BufOnly z z') : z'.state = z.state := by
  rw [e]

theorem BufOnly.trans {a b c : ZStream} (x : BufOnly a b) (y : BufOnly b c) : BufOnly a c := by
  unfold BufOnly at *
  rw [y, x]

theorem BufOnly.clear (z : ZStream) : BufOnly z { z with avail_in := 0, next_in := .null } := rfl

theorem BufOnly.unclear (z : ZStream) : BufOnly { z with avail_in := 0, next_in := .null } z := by
  unfold BufOnly; cases z; rfl

/-- The record write that only rebuffers the stream is a rebuffer of the codec. -/
theorem rebuffer_put {h : Heap} {s v : GzState} (hs : h.gzstates i = some s)
    (hrec : ¬ StreamOwned h (gzStrm i) i) (fresh : Fresh h) (uniq : Zlib.Gzlib.Spec.Uniq h)
    (globals : LibraryGlobals h)
    (hz : BufOnly s.strm v.strm) :
    Rebuffer h (putGz h i v) (gzStrm i) := by
  refine ⟨putGz_fresh hs fresh, putGz_uniq hs uniq, globals, ?_, s.strm, v.strm, ?_, ?_, hz⟩
  · refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := by
      intro e
      subst e
      exact hb hrec
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hbi], rfl⟩
  · simp [ZStreamRef.get, gzStrm, hs]
  · simp [ZStreamRef.get, gzStrm, putGz]

/-- The facts of the actual heap a step of `gz_comp` reads, from `GzInvUpToInput` of a compressing writer. -/
structure Facts (h : Heap) (i : Nat) (s : GzState) : Prop where
  record : h.gzstates i = some s
  writer : s.mode = GZ_WRITE
  fresh : Fresh h
  uniq : Zlib.Gzlib.Spec.Uniq h
  globals : LibraryGlobals h
  fit : ZlibF.PlatformMemory.ByteObjectsFit h
  recFree : ¬ StreamOwned h (gzStrm i) i
  reach : StreamReachable .deflate h (gzStrm i)
  head : ∃ k d, s.strm.state = some (.deflate k) ∧ h.dstates k = some d ∧ d.gzhead = none
  inbuf : ExactBuffer h s.«in» (2 * s.size.toNat)
  outbuf : ExactBuffer h s.out s.size.toNat
  out : OutW5 s
  want : 8 ≤ s.size.toNat ∧ s.size.toNat < 2 ^ 31
  ownLive : ∀ b, GzOwned h i s b → h.live b
  streamOwned : ∀ b, StreamOwned h (gzStrm i) b → GzOwned h i s b
  have0 : s.x.have = 0
  reset : s.reset = 0 ∨ s.reset = 1

theorem facts_of {h : Heap} {s : GzState} {src : Region} (U : GzInvUpToInput h i s src) (hd : s.direct = 0)
    (hz : s.size ≠ 0) : Facts h i s := by
  obtain ⟨hs, invC, hmode, -, -⟩ := U
  have c := invC.common
  have w := invC.writer hmode
  have hsC : (putGz h i (clearIn s)).gzstates i = some (clearIn s) := by simp [putGz]
  have hso := streamOwned_clearIn hs
  have hrec : ¬ StreamOwned h (gzStrm i) i := fun x => c.recordFree ((hso i).2 x)
  have fresh : Fresh h := fun b hb hl => c.fresh b hb ((live_putGz hs _ b).2 hl)
  have uniq : Zlib.Gzlib.Spec.Uniq h := by
    intro b
    have hb := c.uniq b
    by_cases e : b = i
    · subst e
      simpa [putGz, hs] using hb
    · simpa [putGz, upd_ne _ _ _ _ e] using hb
  have fit : ZlibF.PlatformMemory.ByteObjectsFit h := by
    intro r a e
    exact c.fit r a (by rw [get_putGz]; exact e)
  obtain ⟨reachC, z, k, d, hzget, hzst, hk, hhead⟩ := w.codec hd hz
  have hzC : z = (clearIn s).strm := by
    simpa [ZStreamRef.get, gzStrm, putGz] using hzget.symm
  have reb : Rebuffer (putGz h i (clearIn s)) h (gzStrm i) := by
    have e := rebuffer_put (i := i) (h := putGz h i (clearIn s)) (s := clearIn s) (v := s) hsC
      (fun x => c.recordFree x) c.fresh c.uniq c.globals (BufOnly.unclear s.strm)
    rwa [putGz_putGz, putGz_self hs] at e
  refine {
    record := hs
    writer := hmode
    fresh := fresh
    uniq := uniq
    globals := c.globals
    fit := fit
    recFree := hrec
    reach := StreamReachable.rebuffer reachC reb (fun e => nomatch e)
    head := ⟨k, d, by rw [hzC] at hzst; exact hzst, by simpa [putGz] using hk, hhead⟩
    inbuf := by
      obtain ⟨b, a, hp, hb, hr, hsz⟩ := (w.bufs hz).1
      exact ⟨b, a, hp, hb, hr, hsz⟩
    outbuf := by
      obtain ⟨b, a, hp, hb, hr, hsz⟩ := (w.bufs hz).2 hd
      exact ⟨b, a, hp, hb, hr, hsz⟩
    out := w.output hd hz
    want := by
      rcases c.size with e | e
      · exact absurd e hz
      · change s.size = s.want at e
        rw [e]; exact c.want
    ownLive := fun b hb => (live_putGz hs _ b).1 (c.live b ((owned_clearIn hs b).2 hb))
    streamOwned := fun b hb => (owned_clearIn hs b).1 (invC.streamOwned_owned ((hso b).2 hb))
    have0 := w.have0
    reset := w.reset }

/-- **`GzInvUpToInput` across a step of `gz_comp`.** -/
theorem upTo_step {h h' : Heap} {s s' : GzState} {src : Region}
    (U : GzInvUpToInput h i s src) (hd : s.direct = 0) (hz : s.size ≠ 0)
    (rec' : h'.gzstates i = some s') (sh : SameShape s s')
    (fr : Frame h h' (fun b => b = i ∨ StreamOwned h (gzStrm i) b ∨ DataBuf s b))
    (hdata : ∀ b, DataBuf s b → (∃ a a', h.bytes b = some a ∧ h'.bytes b = some a' ∧ a'.size = a.size) ∧
      h'.ro b = h.ro b)
    (hso : ∀ b, StreamOwned h' (gzStrm i) b ↔ StreamOwned h (gzStrm i) b)
    (hlive : ∀ b, h'.live b ↔ h.live b)
    (fresh : Fresh h') (uniq : Zlib.Gzlib.Spec.Uniq h') (globals : LibraryGlobals h')
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h')
    (reach : StreamReachable .deflate h' (gzStrm i))
    (head : ∃ k d, s'.strm.state = some (.deflate k) ∧ h'.dstates k = some d ∧ d.gzhead = none)
    (reset' : s'.reset = 0 ∨ s'.reset = 1) (output' : OutW5 s')
    (input' : NextInOk s' src)
    (srcB : src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨ ∃ xs, Bytes h' src.pointer src.length xs) :
    GzInvUpToInput h' i s' src ∧ ∀ b, GzOwned h' i s' b ↔ GzOwned h i s b := by
  have U0 := U
  obtain ⟨hs, invC, hmode, -, hreg⟩ := U
  have F := facts_of U0 hd hz
  have hsC' : (putGz h' i (clearIn s')).gzstates i = some (clearIn s') := by simp [putGz]
  have hsoC := streamOwned_clearIn hs
  have hsoC' := streamOwned_clearIn rec'
  have hrec' : ¬ StreamOwned h' (gzStrm i) i := fun x => F.recFree ((hso i).1 x)
  have reb : Rebuffer h' (putGz h' i (clearIn s')) (gzStrm i) :=
    rebuffer_put (v := clearIn s') rec' hrec' fresh uniq globals (BufOnly.clear s'.strm)
  obtain ⟨k, d, hk, hdk, hhead⟩ := head
  have frC : Frame (putGz h i (clearIn s)) (putGz h' i (clearIn s'))
      (fun b => b = i ∨ StreamOwned (putGz h i (clearIn s)) (gzStrm i) b ∨ DataBuf (clearIn s) b) := by
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fr
    refine ⟨f1, f2, f3, f4, f5, fun b hl hn => ?_⟩
    have hbi : b ≠ i := fun e => hn (Or.inl e)
    have hl' : h.live b := (live_putGz hs _ b).1 hl
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      f6 b hl' (fun x => hn (x.imp id (Or.imp (fun y => (hsoC b).2 y) id)))
    refine ⟨g1, g2, g3, g4, g5, g6, ?_, g8⟩
    simp only [putGz, upd_ne _ _ _ _ hbi]
    exact g7
  obtain ⟨invC', hownC⟩ := inv_codec_step (i := i) invC hmode hd hz hsC'
    (by obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13⟩ := sh
        exact ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13⟩)
    frC (fun b hb => hdata b hb)
    (fun b => (hsoC' b).trans ((hso b).trans (hsoC b).symm))
    (fun b => (live_putGz rec' _ b).trans ((hlive b).trans (live_putGz hs _ b).symm))
    (putGz_fresh rec' fresh) (putGz_uniq rec' uniq) globals (putGz_fit fit)
    ⟨StreamReachable.rebuffer reach reb (fun e => nomatch e),
      { s'.strm with avail_in := 0, next_in := .null }, k, d, by simp [ZStreamRef.get, gzStrm, putGz, clearIn], hk,
      by simpa [putGz] using hdk, hhead⟩
    reset' ⟨rfl, rfl⟩ output'
  have hown : ∀ b, GzOwned h' i s' b ↔ GzOwned h i s b := fun b =>
    (owned_clearIn rec' b).symm.trans ((hownC b).trans (owned_clearIn hs b))
  refine ⟨⟨rec', invC', sh.2.2.2.2.2.1.trans hmode, input', ?_⟩, hown⟩
  have hin : s'.«in» = s.«in» := sh.2.2.1
  have hsz : s'.size = s.size := sh.2.2.2.2.1
  rcases hreg with ⟨hp, hl⟩ | ⟨-, no⟩
  · exact Or.inl ⟨hp.trans hin.symm, by rw [hsz]; exact hl⟩
  · rcases srcB with ⟨hp, hl⟩ | hb
    · exact Or.inl ⟨hp.trans hin.symm, by rw [hsz]; exact hl⟩
    · exact Or.inr ⟨hb, fun b hr ho => no b hr ((hown b).1 ho)⟩

end step

/-! ## Deflate quiescence with pending input: the premise of `gz_comp` -/

/-- **`DeflateQuietIn`**: the four clauses of `DeflateQuiet` (`gz.skeleton-write`), for the same potential `Φ` and
predicate `Quiet`, with four more clauses for the calls of `gz_comp` that have pending input.

* **(B)** For a reachable deflate stream with no gzip header record (`gzhead = NULL`, as gz never sets one),
  `Φ < 2^62`.
* **(1')** A call with input and at least 8 bytes of room that fills the output lowers `Φ + 2^30·avail_in`.
* **(2')** A call with input, before `FINISH_STATE`, that ends with room and does not return `Z_STREAM_ERROR` leaves
  `avail_in = 0` and `Quiet`.
* **(2f)** A call with input in `FINISH_STATE` that ends with room and does not return `Z_STREAM_ERROR` keeps
  `avail_in` and leaves `FINISH_STATE` with nothing pending. (In `FINISH_STATE` a call with input flushes the pending
  output, then is refused with `Z_BUF_ERROR`, `deflate.c`.)

Why (1') is weighted, not lexicographic in `(avail_in, Φ)`: `gz_comp`'s loops run on at most `2^64` iterations. A
lexicographic descent with `avail_in < 2^32` and `Φ < 2^62` can take about `2^94` steps; the weighted form bounds the
filling calls by `2^63`. It holds for a mixed-radix `Φ` whose part below the phase rises by less than `2^30` per byte
of input consumed (the work component `3·lookahead + …` rises by at most 4 per byte; `pending` is below `2^18`).

Why (2f): `FINISH_STATE` with pending input is reachable in `gz_comp`. A `gz_comp(Z_FINISH)` whose write fails returns
`-1` before it sets `reset`; after `gzclearerr`, `gzclose_w` calls `gz_comp(Z_FINISH)` again with input in `in`, and
`deflate` runs in `FINISH_STATE` with input. In that case (2') does not apply.

The witnesses of `deflate_quiet_holds` (`phiD`, mixed radix with the component `2^64 - 1 - gzindex`) do not satisfy
(B): `phiD ≥ 2^163`. A witness for this premise is a renormalised potential (batch 3). -/
def DeflateQuietIn : Prop :=
  ∃ (Φ : Int32 → Heap → ZStreamRef → Nat) (Quiet : Int32 → Heap → ZStreamRef → Prop),
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r < Φ flush h r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out ≠ 0 → Quiet flush after r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      Quiet flush h r → 0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = z.avail_out) ∧
    (∀ (flush : Int32) (h after : Heap) (r : ZStreamRef) (z z' : ZStream), StreamReachable .deflate h r →
      Rebuffer h after r → r.get h = some z →
      r.get after = some z' → z'.next_in = z.next_in → z'.avail_in = z.avail_in →
      Φ flush after r = Φ flush h r ∧ (Quiet flush h r → Quiet flush after r)) ∧
    -- (B)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState),
      0 ≤ flush.toInt → flush.toInt ≤ 5 → StreamReachable .deflate h r → r.get h = some z →
      z.state = some (.deflate k) → h.dstates k = some d → d.gzhead = none → Φ flush h r < 2 ^ 62) ∧
    -- (1')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in ≠ 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r + 2 ^ 30 * z'.avail_in.toNat < Φ flush h r + 2 ^ 30 * z.avail_in.toNat) ∧
    -- (2')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status ≠ FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 → z'.avail_in = 0 ∧ Quiet flush after r) ∧
    -- (2f)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status = FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 →
      z'.avail_in = z.avail_in ∧ ∃ d', after.dstates k = some d' ∧ d'.status = FINISH_STATE ∧ d'.pending = 0)

/-- The clauses of `DeflateQuietIn` for given witnesses (the same text). -/
def QuietClauses (Φ : Int32 → Heap → ZStreamRef → Nat) (Quiet : Int32 → Heap → ZStreamRef → Prop) : Prop :=
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r < Φ flush h r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out ≠ 0 → Quiet flush after r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      Quiet flush h r → 0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = z.avail_out) ∧
    (∀ (flush : Int32) (h after : Heap) (r : ZStreamRef) (z z' : ZStream), StreamReachable .deflate h r →
      Rebuffer h after r → r.get h = some z →
      r.get after = some z' → z'.next_in = z.next_in → z'.avail_in = z.avail_in →
      Φ flush after r = Φ flush h r ∧ (Quiet flush h r → Quiet flush after r)) ∧
    -- (B)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState),
      0 ≤ flush.toInt → flush.toInt ≤ 5 → StreamReachable .deflate h r → r.get h = some z →
      z.state = some (.deflate k) → h.dstates k = some d → d.gzhead = none → Φ flush h r < 2 ^ 62) ∧
    -- (1')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in ≠ 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r + 2 ^ 30 * z'.avail_in.toNat < Φ flush h r + 2 ^ 30 * z.avail_in.toNat) ∧
    -- (2')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status ≠ FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 → z'.avail_in = 0 ∧ Quiet flush after r) ∧
    -- (2f)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 5 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status = FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 →
      z'.avail_in = z.avail_in ∧ ∃ d', after.dstates k = some d' ∧ d'.status = FINISH_STATE ∧ d'.pending = 0)

theorem quiet_clauses (hq : DeflateQuietIn) : ∃ Φ Quiet, QuietClauses Φ Quiet := hq

/-- **`DeflateQuietIn` holds** (batch 3, `deflate_quiet_in_holds_block`, every flush up to `Z_BLOCK`). -/
theorem deflateQuietIn_holds : DeflateQuietIn := Zlib.Deflate.Universal.Quiet.deflate_quiet_in_holds_block

/-! ## The state of `gz_comp`'s deflate loop -/

/-- The state of a compressing writer inside `gz_comp`. -/
structure St (i : Nat) (src : Region) (h : Heap) (s : GzState) : Prop where
  up : GzInvUpToInput h i s src
  direct : s.direct = 0
  size : s.size ≠ 0

theorem padv_padv (p : BPtr) (a b : Nat) : padv (padv p a) b = padv p (a + b) := by
  cases p <;> simp [padv, Nat.add_assoc]

theorem advance_padv (p : BPtr) (a b : Nat) : advance (padv p a) b = padv p (a + b) := by
  cases p <;> simp [advance, padv, Nat.add_assoc]

theorem byteRoot_padv (p : BPtr) (a b : Nat) : ByteRoot (padv p a) b ↔ ByteRoot p b := by
  cases p with
  | null => exact Iff.rfl
  | ref r o => cases r <;> exact Iff.rfl

theorem bytes_sub {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} (hb : Bytes h p n xs) {a m : Nat}
    (hm : a + m ≤ n) : ∃ ys, Bytes h (padv p a) m ys := by
  rcases hb with ⟨rfl, rfl, rfl⟩ | ⟨r, o, arr, rfl, hg, hle, -⟩
  · exact ⟨[], Or.inl ⟨rfl, by omega, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨r, o + a, arr, rfl, hg, by omega, rfl⟩⟩

section codec
variable {i : Nat} {src : Region}

/-- The buffers the handle owns are outside the codec and distinct. -/
theorem ptr_free {h : Heap} {s : GzState} (U : GzInvUpToInput h i s src) (hz : s.size ≠ 0) (hd : s.direct = 0) :
    (∀ b, s.out = .ref (.blk b) 0 → b ≠ i ∧ ¬ StreamOwned h (gzStrm i) b) ∧
    (∀ b, s.«in» = .ref (.blk b) 0 → b ≠ i ∧ ¬ StreamOwned h (gzStrm i) b) ∧
    (∀ b, s.«in» = .ref (.blk b) 0 → s.out ≠ .ref (.blk b) 0) := by
  obtain ⟨hs, invC, -, -, -⟩ := U
  have c := invC.common
  have hso := streamOwned_clearIn hs
  have hmo : s.out ∈ ownedPtrs (clearIn s) := by simp [ownedPtrs, clearIn, hz, hd]
  have hmi : s.«in» ∈ ownedPtrs (clearIn s) := by simp [ownedPtrs, clearIn, hz]
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hi ho => ?_⟩
  · obtain ⟨h1, h2⟩ := c.distinct.2 _ hmo b (by rw [hb]; rfl)
    exact ⟨h1, fun x => h2 ((hso b).2 x)⟩
  · obtain ⟨h1, h2⟩ := c.distinct.2 _ hmi b (by rw [hb]; rfl)
    exact ⟨h1, fun x => h2 ((hso b).2 x)⟩
  · have nd := c.distinct.1
    have e : ownedPtrs (clearIn s) = [s.path, s.msg, s.«in», s.out] := by
      simp [ownedPtrs, clearIn, hz, hd]
    rw [e] at nd
    have := nd.sublist (List.Sublist.filterMap blkOf
      (List.Sublist.cons _ (List.Sublist.cons _ (List.Sublist.cons₂ _ (List.Sublist.cons₂ _
        (List.nil_sublist _))))))
    simp [hi, ho, blkOf] at this

/-- **The stream's buffers are caller ranges** (`StreamBuffers`), from the state of the loop. -/
theorem buffers_of {h : Heap} {s : GzState} (S : St i src h s) : StreamBuffers h (gzStrm i) := by
  have F := facts_of S.up S.direct S.size
  have P := ptr_free S.up S.size S.direct
  have hreg := S.up.2.2.2.2
  have hget : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, F.record]
  obtain ⟨ob, oa, hop, hob, hor, hos⟩ := F.outbuf
  obtain ⟨ib, ia, hip, hib, -, his⟩ := F.inbuf
  obtain ⟨bo, co, hnext, havail, -, -, hbs⟩ := F.out
  have hnext' : s.strm.next_out = .ref (.blk ob) bo := by rw [hnext, hop]; simp [padv]
  have obFree := P.1 ob hop
  have ibFree := P.2.1 ib hip
  have ibob : ib ≠ ob := fun e => P.2.2 ib hip (by rw [hop, e])
  have obOwn : GzOwned h i s ob := Or.inr (Or.inr (Or.inr ⟨S.size, Or.inr ⟨Or.inr S.direct, Or.inl hop⟩⟩))
  refine ⟨s.strm, hget, ?_, ?_, ?_⟩
  · rcases S.up.2.2.2.1 with ⟨hn, -⟩ | ⟨a, ha, hle⟩
    · exact Or.inl hn
    · right
      rcases hreg with ⟨hp, hl⟩ | ⟨⟨xs, hb⟩, no⟩
      · rw [hp, hip] at ha
        refine ⟨⟨_, Or.inr ⟨.blk ib, 0 + a, ia, by rw [ha]; rfl, hib, by omega, rfl⟩⟩, (fun e => nomatch e), ?_⟩
        intro b hr
        rw [ha] at hr
        change b = ib at hr
        subst hr
        exact ibFree.2
      · obtain ⟨ys, hys⟩ := bytes_sub hb hle
        refine ⟨⟨ys, by rw [ha]; exact hys⟩, (fun e => nomatch e), fun b hr hso => ?_⟩
        rw [ha, byteRoot_padv] at hr
        exact no b hr (F.streamOwned b hso)
  · right
    refine ⟨⟨_, Or.inr ⟨.blk ob, bo, oa, hnext', hob, by omega, rfl⟩⟩,
      fun _ => Or.inr ⟨.blk ob, bo, oa, hnext', hob, hor, by omega⟩, ?_⟩
    intro b hr
    rw [hnext'] at hr
    change b = ob at hr
    subst hr
    exact obFree.2
  · by_cases h0 : s.strm.avail_in = 0
    · exact Or.inl (by rw [h0]; rfl)
    rcases S.up.2.2.2.1 with ⟨hn, -⟩ | ⟨a, ha, hle⟩
    · right; right
      rw [hn, hnext']
      trivial
    · right; right
      rw [hnext']
      rcases hreg with ⟨hp, hl⟩ | ⟨-, no⟩
      · rw [ha, hp, hip]
        exact Or.inl (fun e => ibob (by cases e; rfl))
      · rw [ha]
        cases hsp : src.pointer with
        | null => trivial
        | ref r o =>
          simp only [padv]
          left
          intro e
          subst e
          exact no ob (by rw [hsp]; rfl) obOwn

/-- **No gzip header is read** (`ActiveHeader`): the deflate state of the handle has `gzhead = NULL`. -/
theorem active_of {h : Heap} {s : GzState} (S : St i src h s) : ActiveHeader h (gzStrm i) := by
  have F := facts_of S.up S.direct S.size
  have hget : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, F.record]
  obtain ⟨k, d, hk, hdk, hhead⟩ := F.head
  refine ⟨s.strm, hget, (fun k' st hst _ => by rw [hk] at hst; cases hst), fun k' d' hst hd' => ?_⟩
  rw [hk] at hst
  cases hst
  rw [hdk] at hd'
  cases hd'
  refine ⟨fun _ => Or.inl hhead, ?_, ?_⟩
  · intro j g hg; rw [hhead] at hg; cases hg
  · intro _ j g hg; rw [hhead] at hg; cases hg

/-- A buffer frame over one region of the output block: a frame with that block changed, which keeps its size and
its read-only flag. -/
theorem frame_of_out {h after : Heap} {C : Nat → Prop} {ob off n : Nat} {oa : Array UInt8}
    (bf : BufferFrame h after C [⟨.ref (.blk ob) off, n⟩]) (hob : h.bytes ob = some oa)
    (hl : h.live ob) (hc : ¬ C ob) :
    Frame h after (fun b => C b ∨ b = ob) ∧ (∃ a', after.bytes ob = some a' ∧ a'.size = oa.size) ∧
      after.ro ob = h.ro ob := by
  obtain ⟨⟨f1, f2, f3, f4, f5, f6⟩, inside⟩ := bf
  have hR : restoreRegions h after [⟨.ref (.blk ob) off, n⟩] =
      { after with bytes := upd after.bytes ob (some oa) } := by
    simp only [restoreRegions, List.foldl]
    rw [show Space.get h (BRef.blk ob) = some oa from hob]
    rfl
  rw [hR] at f1 f2 f3 f4 f5 f6
  refine ⟨⟨f1, f2, f3, f4, f5, fun b hb hn => ?_⟩, ?_, ?_⟩
  · have hbo : b ≠ ob := fun e => hn (Or.inr e)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := f6 b hb (fun x => hn (Or.inl x))
    refine ⟨?_, g2, g3, g4, g5, g6, g7, g8⟩
    simpa [upd_ne _ _ _ _ hbo] using g1
  · obtain ⟨a', g, sz, -⟩ := inside _ (List.mem_singleton.mpr rfl) (.blk ob) off oa rfl hob
    exact ⟨a', g, sz⟩
  · exact (f6 ob hl hc).2.2.2.2.2.2.2

theorem streamRoot_gz (b : Nat) : StreamRoot (gzStrm i) b ↔ b = i := Iff.rfl

theorem exec_deflate {r : ZStreamRef} {flush rc : Int32} {h after : Heap}
    (run : C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after)) :
    Call.execute (.deflate (some r) flush) default h = .ok ((rc, default), after) := by
  change heapCall (Zlib.Deflate.deflate (some r) flush) default h = _
  exact Zlib.Deflate.Universal.heapCall_run run

/-- **One `deflate` call of `gz_comp`** on the state of the loop: it returns, the state of the loop holds after it,
it changes only blocks the handle owns and keeps the live blocks and the owned blocks; with the facts the clauses
of `DeflateQuietIn` read. -/
theorem call_step {h : Heap} {s : GzState} (S : St i src h s) (flush : Int32) :
    ∃ rc after s' ds d, C.run (Zlib.Deflate.deflate (some (gzStrm i)) flush) h = .ok (rc, after) ∧
      after.gzstates i = some s' ∧ St i src after s' ∧ Frame h after (GzOwned h i s) ∧
      (∀ b, after.live b ↔ h.live b) ∧ (∀ b, GzOwned after i s' b ↔ GzOwned h i s b) ∧
      s' = { s with strm := s'.strm } ∧
      Call.execute (.deflate (some (gzStrm i)) flush) default h = .ok ((rc, default), after) ∧
      StreamReachable .deflate h (gzStrm i) ∧ StreamBuffers h (gzStrm i) ∧ ActiveHeader h (gzStrm i) ∧
      (gzStrm i).get h = some s.strm ∧ (gzStrm i).get after = some s'.strm ∧ s.strm.next_out ≠ .null ∧
      Zlib.Deflate.Universal.DInv h (gzStrm i) ds s.strm d ∧ s'.strm.state = s.strm.state ∧
      s'.strm.avail_out.toNat ≤ s.strm.avail_out.toNat ∧ InTrack s s' ∧
      (rc = Z_STREAM_ERROR ↔ DeflateRefuses s.strm d flush) := by
  have F := facts_of S.up S.direct S.size
  have P := ptr_free S.up S.size S.direct
  have buffers := buffers_of S
  have active := active_of S
  have hget : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, F.record]
  obtain ⟨ds, z0, d, inv, header, cf⟩ := Zlib.Deflate.Universal.reachable_inv_of
    (Zlib.Deflate.Universal.Call.sequence_facts_of Zlib.Deflate.Engine.Proofs.tinyOverlay) F.reach
  have e0 : z0 = s.strm := Option.some.inj (inv.good.live.hz.symm.trans hget)
  subst e0
  obtain ⟨rc, after, z', d', used, out, run, inv', -, -, cl, own, -, gzEq, -⟩ :=
    Zlib.Deflate.Universal.Call.deflate_call_full inv (Zlib.Deflate.Engine.Proofs.tinyOverlay.at _) header cf
      buffers active flush
  obtain ⟨acc, -, -, -, -, hse, -, -, -, -, -, -, -, -, -, -, bframe, lchange, -⟩ := cl
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6, hu7, -⟩ := acc
  obtain ⟨s', hs', es'⟩ := Zlib.Deflate.Universal.Params.deflate_keeps_gz_records _ _ _ _ _ run i s F.record
  have hz' : s'.strm = z' := by
    have g := inv'.good.live.hz
    simp only [ZStreamRef.get, gzStrm, hs', Option.map_some, Option.some.injEq] at g
    exact g
  have hget' : (gzStrm i).get after = some s'.strm := by simp [ZStreamRef.get, gzStrm, hs']
  obtain ⟨k, dk, hk, hdk, hhead⟩ := F.head
  have ek : k = ds := by
    have := inv.good.live.zst
    rw [hk] at this
    cases this
    rfl
  subst ek
  have ed : dk = d := Option.some.inj (hdk.symm.trans inv.good.live.hs)
  subst ed
  obtain ⟨ob, oa, hop, hob, hor, hos⟩ := F.outbuf
  obtain ⟨ib, ia, hip, hib, hir, his⟩ := F.inbuf
  obtain ⟨bo, co, hnext, havail, hx, hcb, hbs⟩ := F.out
  have hnext' : s.strm.next_out = .ref (.blk ob) bo := by rw [hnext, hop]; simp [padv]
  have obOwn : GzOwned h i s ob := Or.inr (Or.inr (Or.inr ⟨S.size, Or.inr ⟨Or.inr S.direct, Or.inl hop⟩⟩))
  have ibOwn : GzOwned h i s ib := Or.inr (Or.inr (Or.inr ⟨S.size, Or.inl hip⟩))
  have obLive := F.ownLive ob obOwn
  have soIff : ∀ b, StreamOwned h (gzStrm i) b ↔ DeflateOwned k dk b := inv.owned
  have obC : ¬ (StreamRoot (gzStrm i) ob ∨ DeflateOwned k dk ob) := by
    rintro (e | e)
    · exact (P.1 ob hop).1 e
    · exact (P.1 ob hop).2 ((soIff ob).2 e)
  rw [hnext'] at bframe
  obtain ⟨fr0, ⟨oa', hoa', hos'⟩, hro⟩ := frame_of_out bframe hob obLive obC
  have hlive : ∀ b, after.live b ↔ h.live b := fun b => by simpa using lchange b
  have hso : ∀ b, StreamOwned after (gzStrm i) b ↔ StreamOwned h (gzStrm i) b :=
    fun b => (inv'.owned b).trans ((own b).symm.trans (soIff b).symm)
  have frD : Frame h after (fun b => b = i ∨ StreamOwned h (gzStrm i) b ∨ DataBuf s b) :=
    Zlib.Gzwrite.SafeInit.frame_mono fr0 (fun b hb => by
      rcases hb with (e | e) | e
      · exact Or.inl e
      · exact Or.inr (Or.inl ((soIff b).2 e))
      · subst e
        exact Or.inr (Or.inr ⟨S.size, Or.inr ⟨Or.inr S.direct, hop⟩⟩))
  have frG : Frame h after (GzOwned h i s) :=
    Zlib.Gzwrite.SafeInit.frame_mono frD (fun b hb => by
      rcases hb with e | e | e
      · exact Or.inl e
      · exact F.streamOwned b e
      · exact e.owned)
  have hbor : after.libcErrorBorrow = h.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_deflate _ _ h rc after run
  have ibob : ib ≠ ob := fun e => P.2.2 ib hip (by rw [hop, e])
  have ibC : ¬ ((StreamRoot (gzStrm i) ib ∨ DeflateOwned k dk ib) ∨ ib = ob) := by
    rintro ((e | e) | e)
    · exact (P.2.1 ib hip).1 e
    · exact (P.2.1 ib hip).2 ((soIff ib).2 e)
    · exact ibob e
  have hdata : ∀ b, DataBuf s b → (∃ a a', h.bytes b = some a ∧ after.bytes b = some a' ∧ a'.size = a.size) ∧
      after.ro b = h.ro b := by
    rintro b ⟨-, hb | ⟨-, hb⟩⟩
    · rw [hip] at hb
      cases hb
      obtain ⟨e1, -, -, -, -, -, -, e8⟩ := fr0.2.2.2.2.2 ib (F.ownLive ib ibOwn) ibC
      exact ⟨⟨ia, ia, hib, by rw [e1]; exact hib, rfl⟩, e8⟩
    · rw [hop] at hb
      cases hb
      exact ⟨⟨oa, oa', hob, hoa', hos'⟩, hro⟩
  have uniq' : Zlib.Gzlib.Spec.Uniq after := (gz_uniq_iff_deflate after).2 inv'.good.uniq
  obtain ⟨w, p, q, bb, blocks⟩ := inv'.good.inv.blocks
  have I' := inv'.good.inv
  have wle : d'.w_size.toNat ≤ 2 ^ 15 := by
    rw [I'.wsize]; exact Nat.pow_le_pow_right (by decide) I'.wbits_hi
  have lle : d'.lit_bufsize.toNat ≤ 2 ^ 15 := by
    have e1 := I'.lit
    have e2 := I'.hsize
    have : 2 ^ d'.hash_bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) I'.hbits_hi
    omega
  have lim : (2 : Nat) ^ 18 < ZlibF.PlatformMemory.byteObjectLimit := by
    unfold ZlibF.PlatformMemory.byteObjectLimit; decide
  have changedOwned : ∀ x, DeflateOwned k dk x → x = k ∨ x = w ∨ x = p ∨ x = q ∨ x = bb := by
    intro x hx
    rcases (own x).1 hx with e | e | e | e | e
    · exact Or.inl e
    · rw [blocks.win] at e; cases e; exact Or.inr (Or.inl rfl)
    · rw [blocks.prev] at e; cases e; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [blocks.head] at e; cases e; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [blocks.pbuf] at e; cases e; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have fit : ZlibF.PlatformMemory.ByteObjectsFit after := by
    apply Zlib.Gzwrite.SafeInit.fit_of F.fit fr0.1.symm hbor
    · intro x arr e
      by_cases hxo : x = ob
      · subst hxo
        rw [hoa'] at e
        cases e
        right
        rw [hos']
        exact F.fit (.blk x) oa hob
      by_cases hl : h.live x
      · by_cases hc : StreamRoot (gzStrm i) x ∨ DeflateOwned k dk x
        · rcases hc with e1 | e1
          · exfalso
            change x = i at e1
            subst e1
            rw [(Zlib.Gzwrite.SafeInit.uniq_gz_only uniq' hs').1] at e
            cases e
          · rcases changedOwned x e1 with e2 | e2 | e2 | e2 | e2 <;> subst e2
            · exfalso
              rw [(Zlib.Gzwrite.SafeInit.uniq_dstates_only uniq' inv'.good.live.hs).1] at e; cases e
            · right
              obtain ⟨a, ga, gs⟩ := blocks.wa
              rw [ga] at e
              cases e
              rw [gs]
              exact Nat.lt_of_le_of_lt (by omega) lim
            · exfalso
              obtain ⟨a, ga, -⟩ := blocks.pa
              rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).1] at e; cases e
            · exfalso
              obtain ⟨a, ga, -⟩ := blocks.qa
              rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).1] at e; cases e
            · right
              obtain ⟨a, ga, gs⟩ := blocks.ba
              rw [ga] at e
              cases e
              rw [gs]
              exact Nat.lt_of_le_of_lt (by omega) lim
        · left
          rw [← (fr0.2.2.2.2.2 x hl (fun y => y.elim hc hxo)).1]
          exact e
      · exact absurd ((hlive x).1 (Or.inl (by rw [e]; simp))) hl
    · intro x d0 e
      by_cases hxk : x = k
      · subst hxk
        rw [inv'.good.live.hs] at e
        cases e
        right
        rw [I'.wf.2.2.2.2.2]
        exact Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt lim)
      have hl : h.live x := (hlive x).1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]; simp))))))
      by_cases hc : (StreamRoot (gzStrm i) x ∨ DeflateOwned k dk x) ∨ x = ob
      · exfalso
        rcases hc with (e1 | e1) | e1
        · change x = i at e1
          subst e1
          rw [(Zlib.Gzwrite.SafeInit.uniq_gz_only uniq' hs').2.2.2.2.1] at e; cases e
        · rcases changedOwned x e1 with e2 | e2 | e2 | e2 | e2 <;> subst e2
          · exact hxk rfl
          · obtain ⟨a, ga, -⟩ := blocks.wa
            rw [(Zlib.Gzwrite.SafeInit.uniq_bytes_only uniq' ga).1] at e; cases e
          · obtain ⟨a, ga, -⟩ := blocks.pa
            rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).2] at e; cases e
          · obtain ⟨a, ga, -⟩ := blocks.qa
            rw [(Zlib.Gzwrite.SafeInit.uniq_words_only uniq' ga).2] at e; cases e
          · obtain ⟨a, ga, -⟩ := blocks.ba
            rw [(Zlib.Gzwrite.SafeInit.uniq_bytes_only uniq' ga).1] at e; cases e
        · subst e1
          rw [(Zlib.Gzwrite.SafeInit.uniq_bytes_only uniq' hoa').1] at e; cases e
      · left
        exact ⟨d0, by rw [← (fr0.2.2.2.2.2 x hl hc).2.2.2.2.1]; exact e, rfl⟩
  have reach' : StreamReachable .deflate after (gzStrm i) :=
    StreamReachable.step (call := Call.deflate (some (gzStrm i)) flush) F.reach (fun e => nomatch e)
      ⟨rfl, rfl⟩ ⟨buffers, active⟩ (exec_deflate run)
  have hout' : s'.out = s.out := by rw [es']
  have hsz' : s'.size = s.size := by rw [es']
  have hx' : s'.x = s.x := by rw [es']
  have hdir' : s'.direct = s.direct := by rw [es']
  have sh : SameShape s s' := by rw [es']; exact SameShape.refl s
  have output' : OutW5 s' := by
    refine ⟨bo + out.length, co, ?_, ?_, by rw [hx', hout']; exact hx, by omega, by rw [hsz']; omega⟩
    · rw [hz', hu6, hnext, advance_padv, hout']
    · rw [hz', hsz']; omega
  have input' : NextInOk s' src := by
    rcases S.up.2.2.2.1 with ⟨hn, h0⟩ | ⟨a, ha, hle⟩
    · have hused : used = 0 := by rw [h0] at hu1; simpa using hu1
      subst hused
      left
      refine ⟨by rw [hz', hu5, hn]; rfl, ?_⟩
      apply UInt32.toNat_inj.mp
      rw [hz']
      rw [h0] at hu3
      simp only [UInt32.toNat_zero] at hu3 ⊢
      omega
    · exact Or.inr ⟨a + used, by rw [hz', hu5, ha, advance_padv], by rw [hz']; omega⟩
  have srcB : src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨ ∃ xs, Bytes after src.pointer src.length xs := by
    rcases S.up.2.2.2.2 with hin | ⟨⟨xs, hb⟩, no⟩
    · exact Or.inl hin
    · exact Or.inr ⟨xs, bytes_after hb no (fun r o hroot => get_of_frame frG hbor r o hroot)⟩
  obtain ⟨U', hown⟩ := upTo_step S.up S.direct S.size hs' sh frD hdata hso hlive inv'.good.fresh uniq'
    inv'.globals fit reach' ⟨k, d', by rw [hz', hu7]; exact hk, inv'.good.live.hs, by rw [gzEq]; exact hhead⟩
    (by rw [es']; exact F.reset) output' input' srcB
  refine ⟨rc, after, s', k, dk, run, hs', ⟨U', hdir'.trans S.direct, hsz'.symm ▸ S.size⟩, frG,
    hlive, hown, es', exec_deflate run, F.reach, buffers, active, hget, hget',
    by rw [hnext']; exact (fun e => nomatch e), inv, by rw [hz', hu7], by rw [hz']; omega, ⟨used, by rw [hz', hu5], by rw [hz']; omega⟩, hse⟩

theorem exec_reset {r : ZStreamRef} {rc : Int32} {h after : Heap}
    (run : C.run (Zlib.Deflate.deflateReset (some r)) h = .ok (rc, after)) :
    Call.execute (.deflateReset (some r)) default h = .ok ((rc, default), after) := by
  change heapCall (Zlib.Deflate.deflateReset (some r)) default h = _
  exact Zlib.Deflate.Universal.heapCall_run run

theorem owned_of_dlive {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (live : Zlib.Deflate.Spec.DLive h r ds z d) (b : Nat) : StreamOwned h r b ↔ DeflateOwned ds d b := by
  constructor
  · rintro ⟨z', get, (⟨k, st, state, _, _⟩ | ⟨k, st, state, dstate, owned⟩)⟩
    · have same : z' = z := Option.some.inj (get.symm.trans live.hz)
      subst same
      rw [live.zst] at state
      cases state
    · have same : z' = z := Option.some.inj (get.symm.trans live.hz)
      subst same
      rw [live.zst] at state
      cases state
      have sd : st = d := Option.some.inj (dstate.symm.trans live.hs)
      subst sd
      exact owned
  · intro owned
    exact ⟨z, live.hz, Or.inr ⟨ds, d, live.zst, live.hs, owned⟩⟩

/-- **`deflateReset` in `gz_comp`** on the state of the loop. -/
theorem reset_step {h : Heap} {s : GzState} (S : St i src h s) :
    ∃ after s', C.run (Zlib.Deflate.deflateReset (some (gzStrm i))) h = .ok (Z_OK, after) ∧
      after.gzstates i = some s' ∧ St i src after s' ∧ Frame h after (GzOwned h i s) ∧
      (∀ b, after.live b ↔ h.live b) ∧ (∀ b, GzOwned after i s' b ↔ GzOwned h i s b) ∧
      s' = { s with strm := s'.strm } ∧ s'.strm.avail_out = s.strm.avail_out ∧
        s'.strm.avail_in = s.strm.avail_in ∧ s'.strm.next_in = s.strm.next_in ∧
        after.libcErrorBorrow = h.libcErrorBorrow := by
  have F := facts_of S.up S.direct S.size
  have hget : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, F.record]
  obtain ⟨ds, z0, d, inv, -, -⟩ := Zlib.Deflate.Universal.reachable_inv_of
    (Zlib.Deflate.Universal.Call.sequence_facts_of Zlib.Deflate.Engine.Proofs.tinyOverlay) F.reach
  have e0 : z0 = s.strm := Option.some.inj (inv.good.live.hz.symm.trans hget)
  subst e0
  have good := inv.good
  obtain ⟨c1, c2, c3, h1, e1, rfl, -, -, -, good1, live1⟩ := Zlib.Deflate.Proofs.deflateResetKeep_safe good
  obtain ⟨q, qa, h2, e2, hq, hqa, he, good2, live2⟩ := Zlib.Deflate.Proofs.lm_init_safe good1
  have run : C.run (Zlib.Deflate.deflateReset (some (gzStrm i))) h = .ok (Z_OK, h2) := by
    have hz1 := good1.live
    unfold Zlib.Deflate.deflateReset
    rw [C.run] at e1 ⊢
    simp only [bind_app, e1, beq_self_eq_true, ↓reduceIte, Zlib.Deflate.Proofs.zrd_eq, hz1.hz, hz1.zst,
      Zlib.Deflate.Proofs.castD, pure_app]
    rw [C.run] at e2
    rw [e2]
  have hq0 : d.head = .ref (.blk q) 0 := by
    simpa [Zlib.Deflate.Spec.rkPost, Zlib.Deflate.Spec.rkPost3, Zlib.Deflate.Spec.rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec] using hq
  have frame : Frame h h2 (fun b => StreamRoot (gzStrm i) b ∨ DeflateOwned ds d b) := by
    rw [he]; exact Zlib.Deflate.Universal.reset_frame good.live.hz hq0
  have hlive : ∀ b, h2.live b ↔ h.live b := fun b => (live2 b).trans (live1 b)
  have own : ∀ b, DeflateOwned ds (Zlib.Deflate.Spec.lmD (Zlib.Deflate.Spec.rkPost ds
      (Zlib.Deflate.Spec.rkMid d) c1 c2 c3)) b ↔ DeflateOwned ds d b := fun b => by
    simp [DeflateOwned, Zlib.Deflate.Spec.lmD, Zlib.Deflate.Spec.rkPost, Zlib.Deflate.Spec.rkPost3,
      Zlib.Deflate.Spec.rkMid, Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]
  have hso : ∀ b, StreamOwned h2 (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := fun b =>
    (owned_of_dlive good2.live b).trans ((own b).trans (owned_of_dlive good.live b).symm)
  obtain ⟨s', hs', es'⟩ := Zlib.Deflate.Universal.Params.deflateReset_keeps_gz_records _ _ _ _ run i s F.record
  have hz' : s'.strm = Zlib.Deflate.Spec.rkZ s.strm d := by
    have g := good2.live.hz
    simp only [ZStreamRef.get, gzStrm, hs', Option.map_some, Option.some.injEq] at g
    exact g
  have hbytes : h2.bytes = h.bytes := by
    rw [he]; simp [Zlib.Deflate.Spec.setD, Zlib.Deflate.Proofs.setW, ZStreamRef.put, gzStrm, F.record]
  have hro : h2.ro = h.ro := by
    rw [he]; simp [Zlib.Deflate.Spec.setD, Zlib.Deflate.Proofs.setW, ZStreamRef.put, gzStrm, F.record]
  have hdst : ∀ x, x ≠ ds → h2.dstates x = h.dstates x := by
    intro x hx
    rw [he]; simp [Zlib.Deflate.Spec.setD, Zlib.Deflate.Proofs.setW, ZStreamRef.put, gzStrm, F.record, upd_ne _ _ _ _ hx]
  have hbor : h2.libcErrorBorrow = h.libcErrorBorrow :=
    Zlib.Deflate.BorrowProofs.stable_deflateReset _ h Z_OK h2 run
  have fit : ZlibF.PlatformMemory.ByteObjectsFit h2 := by
    apply Zlib.Gzwrite.SafeInit.fit_of F.fit frame.1.symm hbor
    · intro x arr e
      left; rw [← hbytes]; exact e
    · intro x d0 e
      by_cases hx : x = ds
      · subst hx
        rw [good2.live.hs] at e
        cases e
        right
        rw [good2.inv.wf.2.2.2.2.2]
        unfold ZlibF.PlatformMemory.byteObjectLimit
        decide
      · left
        exact ⟨d0, by rw [← hdst x hx]; exact e, rfl⟩
  have frD : Frame h h2 (fun b => b = i ∨ StreamOwned h (gzStrm i) b ∨ DataBuf s b) :=
    Zlib.Gzwrite.SafeInit.frame_mono frame (fun b hb => by
      rcases hb with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl ((owned_of_dlive good.live b).2 e)))
  have frG : Frame h h2 (GzOwned h i s) :=
    Zlib.Gzwrite.SafeInit.frame_mono frD (fun b hb => by
      rcases hb with e | e | e
      · exact Or.inl e
      · exact F.streamOwned b e
      · exact e.owned)
  have hdata : ∀ b, DataBuf s b → (∃ a a', h.bytes b = some a ∧ h2.bytes b = some a' ∧ a'.size = a.size) ∧
      h2.ro b = h.ro b := by
    rintro b ⟨-, hb | ⟨-, hb⟩⟩
    · obtain ⟨ib, ia, hip, hib, -, -⟩ := F.inbuf
      rw [hip] at hb
      cases hb
      exact ⟨⟨ia, ia, hib, by rw [hbytes]; exact hib, rfl⟩, by rw [hro]⟩
    · obtain ⟨ob, oa, hop, hob, -, -⟩ := F.outbuf
      rw [hop] at hb
      cases hb
      exact ⟨⟨oa, oa, hob, by rw [hbytes]; exact hob, rfl⟩, by rw [hro]⟩
  have reach' : StreamReachable .deflate h2 (gzStrm i) :=
    StreamReachable.step (call := Call.deflateReset (some (gzStrm i))) F.reach (fun e => nomatch e)
      ⟨rfl, rfl⟩ trivial (exec_reset run)
  have globals : LibraryGlobals h2 := by
    unfold LibraryGlobals; rw [← frame.1]; exact F.globals
  have srcB : src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨ ∃ xs, Bytes h2 src.pointer src.length xs := by
    rcases S.up.2.2.2.2 with hin | ⟨⟨xs, hb⟩, no⟩
    · exact Or.inl hin
    · exact Or.inr ⟨xs, bytes_after hb no (fun r o hroot => get_of_frame frG hbor r o hroot)⟩
  have sh : SameShape s s' := by rw [es']; exact SameShape.refl s
  obtain ⟨U', hown⟩ := upTo_step S.up S.direct S.size hs' sh frD hdata hso hlive good2.fresh
    ((gz_uniq_iff_deflate h2).2 good2.uniq) globals fit reach'
    ⟨ds, _, by rw [hz']; exact good.live.zst, good2.live.hs, by
      simp [Zlib.Deflate.Spec.lmD, Zlib.Deflate.Spec.rkPost, Zlib.Deflate.Spec.rkPost3,
        Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec]⟩
    (by rw [es']; exact F.reset) (by rw [es', hz']; exact F.out) (by rw [es', hz']; exact S.up.2.2.2.1) srcB
  have hdir' : s'.direct = s.direct := by rw [es']
  have hsz' : s'.size = s.size := by rw [es']
  exact ⟨h2, s', run, hs', ⟨U', hdir'.trans S.direct, hsz'.symm ▸ S.size⟩, frG, hlive, hown, es',
    by rw [hz']; rfl, by rw [hz']; rfl, by rw [hz']; rfl, hbor⟩

theorem streamOwned_put {h : Heap} {s v : GzState} (hs : h.gzstates i = some s)
    (hst : v.strm.state = s.strm.state) (b : Nat) :
    StreamOwned (putGz h i v) (gzStrm i) b ↔ StreamOwned h (gzStrm i) b := by
  unfold StreamOwned
  have g1 : (gzStrm i).get (putGz h i v) = some v.strm := by simp [ZStreamRef.get, gzStrm, putGz]
  have g2 : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, hs]
  rw [g1, g2]
  constructor
  · rintro ⟨z, hz, rest⟩
    cases hz
    refine ⟨s.strm, rfl, ?_⟩
    rw [← hst]
    exact rest
  · rintro ⟨z, hz, rest⟩
    cases hz
    refine ⟨v.strm, rfl, ?_⟩
    rw [hst]
    exact rest

theorem frame_put {h : Heap} (v : GzState) (C : Nat → Prop) (hi : C i) : Frame h (putGz h i v) C := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun b _ hn => ?_⟩
  have hb : b ≠ i := fun e => hn (e ▸ hi)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [putGz, upd_ne _ _ _ _ hb], rfl⟩

/-- **A record write of `gz_comp`** (`again`, `x.next`, the output buffer of the stream) on the state of the
loop. -/
theorem st_record {h : Heap} {s s' : GzState} (S : St i src h s) (sh : SameShape s s')
    (bo : BufOnly s.strm s'.strm) (hreset : s'.reset = 0 ∨ s'.reset = 1) (out' : OutW5 s')
    (inp : NextInOk s' src) :
    St i src (putGz h i s') s' ∧ Frame h (putGz h i s') (GzOwned h i s) ∧
      (∀ b, (putGz h i s').live b ↔ h.live b) ∧ (∀ b, GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b) := by
  have F := facts_of S.up S.direct S.size
  have hso : ∀ b, StreamOwned (putGz h i s') (gzStrm i) b ↔ StreamOwned h (gzStrm i) b :=
    streamOwned_put F.record bo.state
  have hdata : ∀ b, DataBuf s b → (∃ a a', h.bytes b = some a ∧ (putGz h i s').bytes b = some a' ∧
      a'.size = a.size) ∧ (putGz h i s').ro b = h.ro b := by
    rintro b ⟨-, hb | ⟨-, hb⟩⟩
    · obtain ⟨ib, ia, hip, hib, -, -⟩ := F.inbuf
      rw [hip] at hb
      cases hb
      exact ⟨⟨ia, ia, hib, hib, rfl⟩, rfl⟩
    · obtain ⟨ob, oa, hop, hob, -, -⟩ := F.outbuf
      rw [hop] at hb
      cases hb
      exact ⟨⟨oa, oa, hob, hob, rfl⟩, rfl⟩
  obtain ⟨k, d, hk, hdk, hhead⟩ := F.head
  have srcB : src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨
      ∃ xs, Bytes (putGz h i s') src.pointer src.length xs := by
    rcases S.up.2.2.2.2 with hin | ⟨⟨xs, hb⟩, -⟩
    · exact Or.inl hin
    · exact Or.inr ⟨xs, (bytes_putGz _ _ _ _ _ _).2 hb⟩
  have fr := frame_put (h := h) (i := i) s' (fun b => b = i ∨ StreamOwned h (gzStrm i) b ∨ DataBuf s b)
    (Or.inl rfl)
  obtain ⟨U', hown⟩ := upTo_step S.up S.direct S.size (by simp [putGz]) sh fr hdata hso
    (fun b => putGz_live F.record b) (putGz_fresh F.record F.fresh) (putGz_uniq F.record F.uniq) F.globals
    (putGz_fit F.fit)
    (StreamReachable.rebuffer F.reach (rebuffer_put F.record F.recFree F.fresh F.uniq F.globals bo)
      (fun e => nomatch e))
    ⟨k, d, by rw [bo.state]; exact hk, hdk, hhead⟩ hreset out' inp srcB
  refine ⟨⟨U', sh.2.2.2.2.2.2.1.trans S.direct, sh.2.2.2.2.1.symm ▸ S.size⟩,
    frame_put s' _ (Or.inl rfl), fun b => putGz_live F.record b, hown⟩

/-- `GzInv` of a transparent writer across a write of its record's stream input, `again` or `reset`. -/
theorem inv_direct_step {H : Heap} {t t' : GzState} (inv : GzInv H i t) (hw : t.mode = GZ_WRITE)
    (hd : t.direct ≠ 0) (hz : t.size ≠ 0) (sh : SameShape t t') (hx : t'.x = t.x)
    (hst : t'.strm.state = t.strm.state) (hin : t'.strm.next_in = .null ∧ t'.strm.avail_in = 0)
    (hreset : t'.reset = 0 ∨ t'.reset = 1) :
    GzInv (putGz H i t') i t' ∧ ∀ b, GzOwned (putGz H i t') i t' b ↔ GzOwned H i t b := by
  have c := inv.common
  have w := inv.writer hw
  have hs := c.record
  have nso : t.strm.state = none := w.transparent hd
  have hso : ∀ b, StreamOwned (putGz H i t') (gzStrm i) b ↔ StreamOwned H (gzStrm i) b :=
    streamOwned_put hs hst
  have hown := owned_of_shape sh hso
  obtain ⟨hpath, hmsg, hin', hout, hsize, hmode, hdirect, hwant, herr, hskip, hpos, hhave, -⟩ := sh
  have hptrs : ownedPtrs t' = ownedPtrs t := by
    unfold ownedPtrs
    rw [hpath, hmsg, hsize, hin', hmode, hdirect, hout]
  refine ⟨⟨?_, fun hr => absurd (hmode.trans hw) (by rw [hr]; decide), fun _ => ?_⟩, hown⟩
  · exact {
      record := by simp [putGz]
      mode := hmode ▸ c.mode
      fresh := putGz_fresh hs c.fresh
      uniq := putGz_uniq hs c.uniq
      globals := c.globals
      fit := putGz_fit c.fit
      path := by
        rw [hpath]
        obtain ⟨p, hc, hm⟩ := c.path
        exact ⟨p, (putGz_cstring _ _).2 hc, hm⟩
      msg := by
        rw [hmsg]
        rcases c.msg with hn | ⟨m, hc, hm⟩
        · exact Or.inl hn
        · exact Or.inr ⟨m, (putGz_cstring _ _).2 hc, hm⟩
      memerr := fun e => hmsg ▸ c.memerr (herr ▸ e)
      want := hwant ▸ c.want
      size := by rw [hsize, hwant]; exact c.size
      distinct := ⟨hptrs ▸ c.distinct.1, fun p hp b hb =>
        ⟨(c.distinct.2 p (hptrs ▸ hp) b hb).1, by rw [hso]; exact (c.distinct.2 p (hptrs ▸ hp) b hb).2⟩⟩
      live := fun b hb => (putGz_live hs b).2 (c.live b ((hown b).1 hb))
      pos := by rw [hskip, hpos, hhave]; exact c.pos
      next := fun hh => by
        rw [hx] at hh ⊢
        obtain ⟨b, off, a, hxn, hbi, ho, hmb, hb, hle⟩ := c.next hh
        exact ⟨b, off, a, hxn, hbi, (hown b).2 ho, by rw [hmsg]; exact hmb, hb, hle⟩
      nullHave := by rw [hx]; exact c.nullHave
      recordFree := fun x => c.recordFree ((hso i).1 x) }
  · exact {
      have0 := by rw [hx]; exact w.have0
      direct := hdirect ▸ w.direct
      reset := hreset
      unalloc := fun e => absurd (hsize.symm.trans e) hz
      bufs := by rw [hin', hout, hsize, hdirect]; exact w.bufs
      input := Or.inl hin
      output := fun e => absurd (hdirect.symm.trans e) hd
      codec := fun e => absurd (hdirect.symm.trans e) hd
      transparent := fun _ => hst.trans nso }

/-- **`GzInvUpToInput` of a transparent writer across a write of its record** (`again`, the input of the
stream). -/
theorem upTo_direct {h : Heap} {s s' : GzState} (U : GzInvUpToInput h i s src) (hd : s.direct ≠ 0)
    (hz : s.size ≠ 0) (sh : SameShape s s') (hx : s'.x = s.x) (bo : BufOnly s.strm s'.strm)
    (hreset : s'.reset = s.reset) (inp : NextInOk s' src) :
    GzInvUpToInput (putGz h i s') i s' src ∧ (∀ b, GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b) ∧
      Frame h (putGz h i s') (GzOwned h i s) ∧ (∀ b, (putGz h i s').live b ↔ h.live b) := by
  obtain ⟨hs, invC, hmode, -, hreg⟩ := U
  have w := invC.writer hmode
  obtain ⟨invC', hownC⟩ := inv_direct_step (t' := clearIn s') invC hmode hd hz
    (by obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13⟩ := sh
        exact ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13⟩)
    hx bo.state ⟨rfl, rfl⟩ (by show s'.reset = 0 ∨ s'.reset = 1; rw [hreset]; exact w.reset)
  have e1 : putGz (putGz h i (clearIn s)) i (clearIn s') = putGz (putGz h i s') i (clearIn s') := by
    rw [putGz_putGz, putGz_putGz]
  rw [e1] at invC' hownC
  have hs' : (putGz h i s').gzstates i = some s' := by simp [putGz]
  have hown : ∀ b, GzOwned (putGz h i s') i s' b ↔ GzOwned h i s b := fun b =>
    (owned_clearIn hs' b).symm.trans ((hownC b).trans (owned_clearIn hs b))
  refine ⟨⟨hs', invC', sh.2.2.2.2.2.1.trans hmode, inp, ?_⟩, hown, frame_put s' _ (Or.inl rfl),
    fun b => putGz_live hs b⟩
  have hin : s'.«in» = s.«in» := sh.2.2.1
  have hsz : s'.size = s.size := sh.2.2.2.2.1
  rcases hreg with ⟨hp, hl⟩ | ⟨⟨xs, hb⟩, no⟩
  · exact Or.inl ⟨hp.trans hin.symm, by rw [hsz]; exact hl⟩
  · exact Or.inr ⟨⟨xs, (bytes_putGz _ _ _ _ _ _).2 hb⟩, fun b hr ho => no b hr ((hown b).1 ho)⟩

/-! ## The bookkeeping of `GzPost` from the start of `gz_comp` -/

/-- From `(h0, s0)` to `(h, s)`: only owned blocks changed, the live and the owned blocks kept, the shape kept. -/
def Kept (i : Nat) (h0 : Heap) (s0 : GzState) (h : Heap) (s : GzState) : Prop :=
  Frame h0 h (GzOwned h0 i s0) ∧ (∀ b, h.live b ↔ h0.live b) ∧ (∀ b, GzOwned h i s b ↔ GzOwned h0 i s0 b) ∧
    SameShape s0 s ∧ InTrack s0 s ∧ h.libcErrorBorrow = h0.libcErrorBorrow

/-- `Kept` without the `strerror` borrow: what the report of a failed write keeps. -/
def KeptW (i : Nat) (h0 : Heap) (s0 : GzState) (h : Heap) (s : GzState) : Prop :=
  Frame h0 h (GzOwned h0 i s0) ∧ (∀ b, h.live b ↔ h0.live b) ∧ (∀ b, GzOwned h i s b ↔ GzOwned h0 i s0 b) ∧
    SameShape s0 s ∧ InTrack s0 s

theorem Kept.weak {h0 h : Heap} {s0 s : GzState} (K : Kept i h0 s0 h s) : KeptW i h0 s0 h s :=
  ⟨K.1, K.2.1, K.2.2.1, K.2.2.2.1, K.2.2.2.2.1⟩

theorem Kept.refl (h0 : Heap) (s0 : GzState) : Kept i h0 s0 h0 s0 :=
  ⟨Zlib.Gzwrite.SafeInit.frame_refl _ _, fun _ => Iff.rfl, fun _ => Iff.rfl, SameShape.refl _, InTrack.refl _, rfl⟩

theorem Kept.step {h0 h h' : Heap} {s0 s s' : GzState} (K : Kept i h0 s0 h s)
    (fr : Frame h h' (GzOwned h i s)) (hl : ∀ b, h'.live b ↔ h.live b)
    (ho : ∀ b, GzOwned h' i s' b ↔ GzOwned h i s b) (sh : SameShape s s')
    (hai : InTrack s s') (hbor : h'.libcErrorBorrow = h.libcErrorBorrow) :
    Kept i h0 s0 h' s' := by
  obtain ⟨fr0, hl0, ho0, sh0, ai0, b0⟩ := K
  refine ⟨⟨fr0.1.trans fr.1, fr0.2.1.trans fr.2.1, fr0.2.2.1.trans fr.2.2.1,
    Nat.le_trans fr0.2.2.2.1 fr.2.2.2.1, Nat.le_trans fr0.2.2.2.2.1 fr.2.2.2.2.1, fun b hb hn => ?_⟩,
    fun b => (hl b).trans (hl0 b), fun b => (ho b).trans (ho0 b), sh0.trans sh, ai0.trans hai, hbor.trans b0⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := fr0.2.2.2.2.2 b hb hn
  have hb1 : h.live b := (hl0 b).2 hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := fr.2.2.2.2.2 b hb1 (fun x => hn ((ho0 b).1 x))
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
    b8.trans a8⟩

/-- A world that differs only in the `strerror` borrow keeps everything `Kept` reads. -/
theorem Kept.borrow {h0 h : Heap} {s0 s : GzState} (K : Kept i h0 s0 h s) (x : Option (Nat × Int32)) :
    KeptW i h0 s0 { h with libcErrorBorrow := x } s := K.weak

theorem post_of_kept {h0 h : Heap} {s0 s : GzState} {fs : Fs} {P : Heap → Nat → GzState → Prop}
    (K : Kept i h0 s0 h s) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b) (hfs : FileSystem fs) (hp : P h i s) :
    GzPost h0 i s0 [] fs h P := by
  obtain ⟨fr, hl, ho, sh, -, -⟩ := K
  refine ⟨hfs, s, hp, sh.2.2.2.2.2.1, sh.2.2.2.2.2.2.2.2.2.2.2.2, ⟨fr, fun _ hm => by cases hm⟩, ?_,
    fun b hb => Or.inl ((ho b).1 hb)⟩
  intro b
  simp only
  rw [hl b, ho b]
  constructor
  · intro x
    exact Or.inl ⟨x, fun y => y.2 y.1⟩
  · rintro (⟨x, _⟩ | ⟨y, z⟩)
    · exact x
    · exact absurd (own0 b y) z

/-- The `GzPost` of a path that ends with `gz_error` after steps that kept the handle. -/
theorem post_of_error {h0 h1 h2 : Heap} {s0 s1 s2 : GzState} {fs : Fs} {P : Heap → Nat → GzState → Prop}
    (K : KeptW i h0 s0 h1 s1) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b)
    (rec1 : h1.gzstates i = some s1) (rec2 : h2.gzstates i = some s2)
    (e2 : s2 = { s1 with err := s2.err, msg := s2.msg })
    (fr : Frame h1 h2 (fun b => b = i ∨ blkOf s1.msg = some b))
    (lc : LiveChange h1 h2 (fun b => blkOf s2.msg = some b ∧ ¬ h1.live b) (fun b => blkOf s1.msg = some b))
    (own : ∀ b, GzOwned h2 i s2 b → h1.live b → GzOwned h1 i s1 b)
    (m1o : ∀ b, blkOf s1.msg = some b → GzOwned h1 i s1 b)
    (m2o : ∀ b, blkOf s2.msg = some b → GzOwned h2 i s2 b)
    (o2l : ∀ b, GzOwned h2 i s2 b → h2.live b)
    (hc : ∀ k, StreamOwned h1 (gzStrm i) k → ¬ (k = i ∨ blkOf s1.msg = some k))
    (hfs : FileSystem fs) (hp : P h2 i s2) : GzPost h0 i s0 [] fs h2 P := by
  obtain ⟨fr0, hl0, ho0, sh0, -⟩ := K
  have hpath : s2.path = s1.path := by rw [e2]
  have hin : s2.«in» = s1.«in» := by rw [e2]
  have hout : s2.out = s1.out := by rw [e2]
  have hsize : s2.size = s1.size := by rw [e2]
  have hmode : s2.mode = s1.mode := by rw [e2]
  have hdirect : s2.direct = s1.direct := by rw [e2]
  have hstrm : s2.strm = s1.strm := by rw [e2]
  have hfd : s2.fd = s1.fd := by rw [e2]
  have so : ∀ b, StreamOwned h1 (.in_gzstate_strm i) b → StreamOwned h2 (.in_gzstate_strm i) b := by
    rintro b ⟨z, hz1, ⟨k, st, hk, hst, ho⟩ | ⟨k, d, hk, hd, ho⟩⟩
    · have ownk : StreamOwned h1 (gzStrm i) k := ⟨z, hz1, Or.inl ⟨k, st, hk, hst, Or.inl rfl⟩⟩
      have live : h1.live k := by unfold Heap.live; simp [hst]
      have e := (fr.2.2.2.2.2 k live (hc k ownk)).2.2.2.2.2.1
      refine ⟨z, ?_, Or.inl ⟨k, st, hk, by rw [e]; exact hst, ho⟩⟩
      simp only [ZStreamRef.get, rec1, Option.map_some, Option.some.injEq] at hz1
      simp [ZStreamRef.get, rec2, hstrm, hz1]
    · have ownk : StreamOwned h1 (gzStrm i) k := ⟨z, hz1, Or.inr ⟨k, d, hk, hd, Or.inl rfl⟩⟩
      have live : h1.live k := by unfold Heap.live; simp [hd]
      have e := (fr.2.2.2.2.2 k live (hc k ownk)).2.2.2.2.1
      refine ⟨z, ?_, Or.inr ⟨k, d, hk, by rw [e]; exact hd, ho⟩⟩
      simp only [ZStreamRef.get, rec1, Option.map_some, Option.some.injEq] at hz1
      simp [ZStreamRef.get, rec2, hstrm, hz1]
  have keep : ∀ b, GzOwned h1 i s1 b → ¬ blkOf s1.msg = some b → GzOwned h2 i s2 b := by
    intro b hb hn
    rcases hb with e | e | e | ⟨hz, e | ⟨hmo, e | e⟩⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl (by rw [hpath]; exact e))
    · exact absurd (by rw [e]; rfl) hn
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [hsize]; exact hz, Or.inl (by rw [hin]; exact e)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [hsize]; exact hz, Or.inr ⟨by rw [hmode, hdirect]; exact hmo,
        Or.inl (by rw [hout]; exact e)⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by rw [hsize]; exact hz, Or.inr ⟨by rw [hmode, hdirect]; exact hmo,
        Or.inr (so b e)⟩⟩))
  refine ⟨hfs, s2, hp, hmode.trans sh0.2.2.2.2.2.1, hfd.trans sh0.2.2.2.2.2.2.2.2.2.2.2.2,
    ⟨⟨fr0.1.trans fr.1, fr0.2.1.trans fr.2.1, fr0.2.2.1.trans fr.2.2.1, Nat.le_trans fr0.2.2.2.1 fr.2.2.2.1,
      Nat.le_trans fr0.2.2.2.2.1 fr.2.2.2.2.1, fun b hb hn => ?_⟩, fun _ hm => by cases hm⟩, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := fr0.2.2.2.2.2 b hb hn
    have hb1 : h1.live b := (hl0 b).2 hb
    have hn1 : ¬ GzOwned h1 i s1 b := fun x => hn ((ho0 b).1 x)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ :=
      fr.2.2.2.2.2 b hb1 (fun c => c.elim (fun e => hn1 (Or.inl e)) (fun e => hn1 (m1o b e)))
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
      b8.trans a8⟩
  · intro b
    have L := lc b
    simp only at L ⊢
    rw [← hl0 b]
    constructor
    · intro hl2
      by_cases O2 : GzOwned h2 i s2 b
      · by_cases l1 : h1.live b
        · exact Or.inl ⟨l1, fun x => x.2 O2⟩
        · exact Or.inr ⟨O2, l1⟩
      · rcases L.1 hl2 with ⟨hl1, hn⟩ | ⟨x, _⟩
        · exact Or.inl ⟨hl1, fun y => O2 (keep b ((ho0 b).2 y.1) hn)⟩
        · exact absurd (m2o b x) O2
    · rintro (⟨hl1, hn⟩ | ⟨x, _⟩)
      · by_cases M1 : blkOf s1.msg = some b
        · exact o2l b (Classical.byContradiction fun y => hn ⟨(ho0 b).1 (m1o b M1), y⟩)
        · exact L.2 (Or.inl ⟨hl1, M1⟩)
      · exact o2l b x
  · intro b hb
    by_cases hl : h1.live b
    · exact Or.inl ((ho0 b).1 (own b hb hl))
    · exact Or.inr (fun x => hl ((hl0 b).2 x))

/-- After `strerror` the readability of the caller region may be lost: the weak invariant holds. -/
theorem weak_of_strerror {h : Heap} {s : GzState} (U : GzInvUpToInput h i s src) (x : Option (Nat × Int32)) :
    GzInvUpToInputWeak { h with libcErrorBorrow := x } i s src := by
  obtain ⟨hs, invC, hmode, hin, hreg⟩ := U
  refine ⟨hs, ?_, hmode, hin, hreg.imp id (fun y => y.2)⟩
  have c := invC.common
  have w := invC.writer hmode
  have e : putGz { h with libcErrorBorrow := x } i (clearIn s) =
      { putGz h i (clearIn s) with libcErrorBorrow := x } := rfl
  rw [e]
  refine (GzRead.GzInv.frame_data (after := { putGz h i (clearIn s) with libcErrorBorrow := x }) invC ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
    fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ ?_ c.fresh c.uniq c.globals
    (ZlibF.PlatformMemory.ByteObjectsFit.of_storage_eq c.fit rfl rfl rfl)).1
  rintro b ⟨hz, hb | ⟨hmo, hb⟩⟩
  · obtain ⟨b', a, hp, hb', -, -⟩ := (w.bufs hz).1
    rw [hp] at hb
    cases hb
    exact ⟨⟨a, a, hb', hb', rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hd : (clearIn s).direct = 0 := hmo.resolve_left (by rw [show (clearIn s).mode = s.mode from rfl, hmode]; decide)
    obtain ⟨b', a, hp, hb', -, -⟩ := (w.bufs hz).2 hd
    rw [hp] at hb
    cases hb
    exact ⟨⟨a, a, hb', hb', rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Running the primitives of `gz_comp` -/

theorem ldS_put (h : Heap) (v : GzState) : ldS (gzSt i) (putGz h i v) = .ok (v, putGz h i v) :=
  by rw [show gzSt i = some (.tab i) from rfl, Zlib.Gzlib.Proofs.ldS_eq]; simp [putGz]

theorem ldZ_put (h : Heap) (v : GzState) :
    ldZ (strmOf (gzSt i)) (putGz h i v) = .ok (v.strm, putGz h i v) :=
  by rw [show strmOf (gzSt i) = some (.in_gzstate_strm i) from rfl, Zlib.Gzlib.Proofs.ldZ_eq]; simp [putGz]

theorem updS_put (h : Heap) (v : GzState) (f : GzState → GzState) :
    updS (gzSt i) f (putGz h i v) = .ok ((), putGz h i (f v)) := by
  rw [show gzSt i = some (.tab i) from rfl, Zlib.Gzlib.Proofs.updS_eq]
  simp [putGz, Zlib.Gzlib.Spec.setS, upd_upd]

theorem updZ_put (h : Heap) (v : GzState) (f : ZStream → ZStream) :
    updZ (strmOf (gzSt i)) f (putGz h i v) = .ok ((), putGz h i { v with strm := f v.strm }) := by
  rw [show strmOf (gzSt i) = some (.in_gzstate_strm i) from rfl, Zlib.Gzlib.Proofs.updZ_eq]
  simp [putGz, Zlib.Gzlib.Spec.setS, upd_upd]

theorem updX_put (h : Heap) (v : GzState) (f : GzFile → GzFile) :
    updX (gzSt i) f (putGz h i v) = .ok ((), putGz h i { v with x := f v.x }) :=
  updS_put h v _

theorem getErrno_run (fs : Fs) (h : Heap) : getErrno fs h = .ok ((fs.errno, fs), h) := rfl

/-- The bytes `loadBytes` returns. -/
def loadSlice (a : Array UInt8) (o n : Nat) : Array UInt8 :=
  (List.range' 0 n).foldl (fun out j => out.push a[o + j]!) #[]

theorem foldl_push_size (f : Nat → UInt8) (xs : List Nat) (out : Array UInt8) :
    (xs.foldl (fun out j => out.push (f j)) out).size = out.size + xs.length := by
  induction xs generalizing out with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, Array.size_push, List.length_cons]; omega

theorem loadSlice_size (a : Array UInt8) (o n : Nat) : (loadSlice a o n).size = n := by
  unfold loadSlice
  rw [foldl_push_size (fun j => a[o + j]!)]
  simp

theorem loadBytes_eq {h : Heap} {r : BRef} {a : Array UInt8} {o n : Nat} (ha : Space.get h r = some a)
    (hn : o + n ≤ a.size) : loadBytes (.ref r o) n h = .ok (loadSlice a o n, h) := by
  have list : ∀ (xs : List Nat), (∀ j ∈ xs, o + j < a.size) → ∀ out : Array UInt8,
      (forIn' xs out (fun (j : Nat) _ (out : Array UInt8) => do
        let v ← index8 (.ref r o) (j : Int)
        pure (ForInStep.yield (out.push v)))) h =
        .ok (xs.foldl (fun out j => out.push a[o + j]!) out, h) := by
    intro xs
    induction xs with
    | nil => intro _ out; rfl
    | cons j xs ih =>
      intro hb out
      have hlt : o + j < a.size := hb j (by simp)
      have hi : index8 (.ref r o) j h = .ok (a[o + j]!, h) := by
        rw [getElem!_pos a (o + j) hlt]
        simpa [OkOn] using Ptr.index_ok (off := o) (i := j) ha hlt
      simp only [List.forIn'_cons, bind_app, hi, pure_app, List.foldl_cons]
      exact ih (fun k hk => hb k (by simp [hk])) _
  unfold loadBytes
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  have hr : ∀ j ∈ List.range' 0 n, o + j < a.size := by
    intro j hj
    simp only [List.mem_range'] at hj
    omega
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [bind_app, list _ hr]
  rfl

theorem max_eq : ((((0 : UInt32) - 1) >>> 2) + 1) = 1073741824 := by decide

theorem outPut_val (d : Int64) (k : Nat) (hd : d.toInt = k) (hk : k < 2 ^ 31) :
    (outPut ((((0 : UInt32) - 1) >>> 2) + 1) d).toNat = min k (2 ^ 30) := by
  rw [max_eq]
  unfold outPut
  have hm : (Int64.ofNat (1073741824 : UInt32).toNat).toInt = 1073741824 := by decide
  split
  · rename_i hgt
    simp only [gt_iff_lt, Int64.lt_iff_toInt_lt, hd, hm] at hgt
    simp only [UInt32.reduceToNat]
    omega
  · rename_i hle
    simp only [gt_iff_lt, Int64.lt_iff_toInt_lt, hd, hm] at hle
    have h0 : 0 ≤ d := by rw [Int64.le_iff_toInt_le, hd]; simp
    rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt, hd]
    simp only [Int.toNat_natCast]
    omega

theorem dirPut_val (x : UInt32) :
    (dirPut ((((0 : UInt32) - 1) >>> 2) + 1) x).toNat = min x.toNat (2 ^ 30) := by
  rw [max_eq]
  unfold dirPut
  split
  · rename_i hgt
    simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at hgt ⊢
    omega
  · rename_i hle
    simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at hle
    omega

/-! ## The `gz_error` report of a failed write -/

theorem weak_facts {h : Heap} {s : GzState} (W : GzInvUpToInputWeak h i s src) :
    (∀ b, blkOf s.msg = some b → GzOwned h i s b) ∧ (∀ b, GzOwned h i s b → h.live b) ∧
      (∀ k, StreamOwned h (gzStrm i) k → ¬ (k = i ∨ blkOf s.msg = some k)) := by
  obtain ⟨hs, invC, -, -, -⟩ := W
  refine ⟨msg_owned invC, fun b hb => (live_putGz hs _ b).1 (invC.common.live b ((owned_clearIn hs b).2 hb)), ?_⟩
  rintro k hk (e | e)
  · subst e
    exact invC.common.recordFree ((streamOwned_clearIn hs _).2 hk)
  · exact (GzInv.msg_separate invC e).2.2.1 ((streamOwned_clearIn hs k).2 hk)

/-- The record fields every run of `gz_comp` keeps, also when it fails (`gz_error` writes only `err` and `msg`). -/
abbrev CompShape (t t' : GzState) : Prop :=
  t'.path = t.path ∧ t'.«in» = t.«in» ∧ t'.out = t.out ∧ t'.size = t.size ∧ t'.mode = t.mode ∧
    t'.direct = t.direct ∧ t'.want = t.want ∧ t'.skip = t.skip ∧ t'.x.pos = t.x.pos ∧ t'.x.have = t.x.have ∧
    t'.fd = t.fd ∧ InTrack t t'

theorem CompShape.of_same {t t' : GzState} (sh : SameShape t t')
    (hai : InTrack t t') : CompShape t t' :=
  ⟨sh.1, sh.2.2.1, sh.2.2.2.1, sh.2.2.2.2.1, sh.2.2.2.2.2.1, sh.2.2.2.2.2.2.1, sh.2.2.2.2.2.2.2.1,
    sh.2.2.2.2.2.2.2.2.2.1, sh.2.2.2.2.2.2.2.2.2.2.1, sh.2.2.2.2.2.2.2.2.2.2.2.1, sh.2.2.2.2.2.2.2.2.2.2.2.2, hai⟩

/-- The shape after `gz_error` on a record of the same shape. -/
theorem CompShape.of_error {t s s2 : GzState} (sh : SameShape t s)
    (hai : InTrack t s) (e2 : s2 = { s with err := s2.err, msg := s2.msg }) :
    CompShape t s2 := by
  have c := CompShape.of_same sh hai
  rw [e2]; exact c

/-- The post of a failed `gz_comp`: the weak invariant, with the shape of the record at the start kept. -/
abbrev WeakS (src : Region) (s0 : GzState) : Heap → Nat → GzState → Prop :=
  fun h' i' s' => GzInvUpToInputWeak h' i' s' src ∧ CompShape s0 s'

/-- **The report of a failed write**: `gz_error(state, Z_ERRNO, zstrerror())` from the invariant up to the pending
input; the weak invariant and the `GzPost` from the start of `gz_comp` after it. -/
theorem err_tail (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 h : Heap} {s0 s : GzState}
    (K : Kept i h0 s0 h s) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b) (U : GzInvUpToInput h i s src)
    (fs : Fs) (hfs : FileSystem fs) :
    ∃ h2, Zlib.Gzlib.gz_error (gzSt i) Z_ERRNO
        (.ref (.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) fs.errno)) 0)
        { h with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno) } = .ok ((), h2) ∧
      GzPost h0 i s0 [] fs h2 (WeakS src s0) := by
  have W := weak_of_strerror U (some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno))
  have hmsg : (Ptr.ref (BRef.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) fs.errno)) 0 : BPtr) = .null ∨
      ∃ t, CString { h with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno) }
        (.ref (.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) fs.errno)) 0) t ∧
        ∀ b, ByteRoot (.ref (.str (libcErrnoIndex (Zlib.GzFs.Proofs.nextErrorEpoch h) fs.errno)) 0) b →
          ¬ GzOwned { h with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno) } i s b :=
    Or.inr ⟨_, Zlib.GzFs.Proofs.zstrerror_cstring (Zlib.GzFs.Proofs.zstrerror_run h fs),
      fun b hb => by simp [ByteRoot] at hb⟩
  have hlive : src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨
      ∀ b, ByteRoot src.pointer b →
        ({ h with libcErrorBorrow := some (Zlib.GzFs.Proofs.nextErrorEpoch h, fs.errno) } : Heap).live b := by
    rcases U.2.2.2.2 with hin | ⟨⟨xs, hb⟩, -⟩
    · exact Or.inl hin
    · exact Or.inr (fun b hr => root_live_of_bytes hb hr)
  obtain ⟨h2, s2, run, W2, e2, fr, lc, own⟩ := gz_error_upToInputWeak err errOwn W Z_ERRNO _ hmsg (by decide) hlive
  obtain ⟨m1o, -, hc⟩ := weak_facts W
  obtain ⟨m2o, o2l, -⟩ := weak_facts W2
  exact ⟨h2, run, post_of_error (K.borrow _) own0 U.1 W2.1 e2 fr lc own m1o m2o o2l hc hfs
    ⟨W2, CompShape.of_error K.2.2.2.1 K.2.2.2.2.1 e2⟩⟩

/-! ## The write-out loop -/

/-- The record during the write-out loop: `x.next` at offset `c` of the output block, and `again`. -/
def mkx (s : GzState) (ob c : Nat) (a : Int32) : GzState :=
  { s with x := { s.x with next := .ref (.blk ob) c }, again := a }

@[simp] theorem mkx_strm (s : GzState) (ob c : Nat) (a : Int32) : (mkx s ob c a).strm = s.strm := rfl
@[simp] theorem mkx_xnext (s : GzState) (ob c : Nat) (a : Int32) :
    (mkx s ob c a).x.next = Ptr.ref (BRef.blk ob) c := rfl
@[simp] theorem mkx_fd (s : GzState) (ob c : Nat) (a : Int32) : (mkx s ob c a).fd = s.fd := rfl
theorem updS_mkx_again (h : Heap) (s : GzState) (ob c : Nat) (a a' : Int32) :
    updS (gzSt i) (fun s => { s with again := a' }) (putGz h i (mkx s ob c a)) =
      .ok ((), putGz h i (mkx s ob c a')) := updS_put h _ _

theorem updX_mkx_next (h : Heap) (s : GzState) (ob c c' : Nat) (a : Int32) :
    updX (gzSt i) (fun x => { x with next := Ptr.ref (BRef.blk ob) c' }) (putGz h i (mkx s ob c a)) =
      .ok ((), putGz h i (mkx s ob c' a)) := updS_put h _ _

theorem mkx_self {s : GzState} {ob c : Nat} (hx : s.x.next = .ref (.blk ob) c) : mkx s ob c s.again = s := by
  unfold mkx
  rw [← hx]

/-- The state of the loop at an offset `c'` of `x.next`. -/
theorem out_state {h0 h1 : Heap} {s0 s1 : GzState} (S1 : St i src h1 s1) (K1 : Kept i h0 s0 h1 s1)
    {ob bo : Nat} (hop : s1.out = .ref (.blk ob) 0) (hno : s1.strm.next_out = .ref (.blk ob) bo)
    {c : Nat} (a : Int32) (hc : c ≤ bo) :
    St i src (putGz h1 i (mkx s1 ob c a)) (mkx s1 ob c a) ∧ Kept i h0 s0 (putGz h1 i (mkx s1 ob c a)) (mkx s1 ob c a) := by
  have F := facts_of S1.up S1.direct S1.size
  obtain ⟨b0, c0, hn0, ha0, -, -, hb0⟩ := F.out
  have e : bo = b0 := by
    rw [hno, hop] at hn0
    simp only [padv, Nat.zero_add, Ptr.ref.injEq, true_and] at hn0
    exact hn0
  subst e
  have sh : SameShape s1 (mkx s1 ob c a) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨St', fr, hl, ho⟩ := st_record S1 sh (by unfold BufOnly; rfl) F.reset
    ⟨bo, c, by show s1.strm.next_out = padv s1.out bo; rw [hno, hop]; simp [padv], ha0,
      by show (Ptr.ref (BRef.blk ob) c : BPtr) = padv s1.out c; rw [hop]; simp [padv], hc, hb0⟩ S1.up.2.2.2.1
  exact ⟨St', K1.step fr hl ho sh (InTrack.of_in rfl rfl) rfl⟩

theorem out_cond_none {h : Heap} {v : GzState} {ob c bo : Nat} {oa : Array UInt8} (hob : h.bytes ob = some oa)
    (hx : v.x.next = .ref (.blk ob) c) (hn : v.strm.next_out = .ref (.blk ob) bo) (hc : c ≤ oa.size)
    (hb : bo ≤ oa.size) (fs : Fs) :
    outCond i none fs (putGz h i v) = .ok (((decide (c < bo), none), fs), putGz h i v) := by
  have hlt := Ptr.lt_ok (h := putGz h i v) (r := BRef.blk ob) (a := oa) hob hc hb
  unfold outCond
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, liftM, monadLift, MonadLift.monadLift,
    MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, ldZ_put, ldS_put, hx, hn]
  rw [show Ptr.lt (Ptr.ref (BRef.blk ob) c) (Ptr.ref (BRef.blk ob) bo) (putGz h i v) =
    .ok (decide (c < bo), putGz h i v) from hlt]

theorem out_cond_some (v : Int32) (fs : Fs) (h : Heap) :
    outCond i (some v) fs h = .ok (((false, some v), fs), h) := by
  unfold outCond
  simp only [Option.isSome_some, ↓reduceIte, cpure_app]

/-- **One trip of the write-out loop**: it writes at least one byte of the output buffer, or fails with the
`gz_error` report. -/
theorem out_body (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 h1 : Heap} {s0 s1 : GzState} {fs0 fs : Fs}
    (S1 : St i src h1 s1) (K1 : Kept i h0 s0 h1 s1) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b)
    {ob bo c : Nat} {a : Int32} (hop : s1.out = .ref (.blk ob) 0) (hno : s1.strm.next_out = .ref (.blk ob) bo)
    (hcb : c < bo) (hfs : FileSystem fs) (hk : FdsKept fs0 fs) :
    ∃ z fs' h', outBody i none fs (putGz h1 i (mkx s1 ob c a)) = .ok ((z, fs'), h') ∧ FileSystem fs' ∧
      FdsKept fs0 fs' ∧
      ((z = none ∧ ∃ c', c < c' ∧ c' ≤ bo ∧ h' = putGz h1 i (mkx s1 ob c' 0)) ∨
        (z = some (-1) ∧ GzPost h0 i s0 [] fs' h' (WeakS src s0))) := by
  have F := facts_of S1.up S1.direct S1.size
  obtain ⟨ob', oa, hop', hob, -, hos⟩ := F.outbuf
  rw [hop] at hop'
  cases hop'
  obtain ⟨b0, c0, hn0, -, -, -, hb0⟩ := F.out
  have hbo : bo ≤ oa.size := by
    rw [hno, hop] at hn0
    simp only [padv, Nat.zero_add, Ptr.ref.injEq, true_and] at hn0
    omega
  have hsz := F.want
  have hdiff : ∀ v, Ptr.diff (Ptr.ref (BRef.blk ob) bo) (Ptr.ref (BRef.blk ob) c) (putGz h1 i v) =
      .ok (Int64.ofInt ((bo : Int) - (c : Int)), putGz h1 i v) :=
    fun v => Ptr.diff_ok (h := putGz h1 i v) (r := BRef.blk ob) (a := oa) hob hbo (by omega) (by omega)
  have hput : (outPut ((((0 : UInt32) - 1) >>> 2) + 1) (Int64.ofInt ((bo : Int) - (c : Int)))).toNat =
      min (bo - c) (2 ^ 30) := by
    apply outPut_val
    · rw [Int64.toInt_ofInt, Zlib.Gzlib.Proofs.bmod64 _ (by omega) (by omega)]
      omega
    · omega
  have hload : ∀ v, loadBytes (Ptr.ref (BRef.blk ob) c) (min (bo - c) (2 ^ 30)) (putGz h1 i v) =
      .ok (loadSlice oa c (min (bo - c) (2 ^ 30)), putGz h1 i v) :=
    fun v => loadBytes_eq (h := putGz h1 i v) (r := BRef.blk ob) hob (by omega)
  have hfs1 : FileSystem { fs with errno := 0 } := hfs
  obtain ⟨r, w', hw, hres, hfsw, hkw⟩ := fsWrite_contract_m s1.fd (loadSlice oa c (min (bo - c) (2 ^ 30)))
    { fs with errno := 0 } hfs1 (by rw [loadSlice_size]; omega) (by rw [loadSlice_size]; omega)
  have hk1 : FdsKept fs0 w' := fun j => (hkw j).trans (hk j)
  have hwH : ∀ H : Heap, fsWrite s1.fd (loadSlice oa c (min (bo - c) (2 ^ 30))) { fs with errno := 0 } H =
      .ok ((r, w'), H) := fun H => by rw [hw]; rfl
  have hst := fun a' => out_state S1 K1 hop hno a' (c := c) (Nat.le_of_lt hcb)
  unfold outBody
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
    Zlib.GzFs.Proofs.stable_setErrno, updS_mkx_again, ldZ_put, ldS_put, mkx_strm, mkx_xnext, mkx_fd,
    hno, hdiff, hput, hload, hwH, getErrno_run]
  rcases hres with rfl | ⟨hr1, hr2⟩
  · by_cases hb : BLOCKED w'.errno = true
    · obtain ⟨St', K'⟩ := hst 1
      obtain ⟨h2, hgz, hpost⟩ := err_tail err errOwn K' own0 St'.up w' hfsw
      simp only [GzRead.ret_fail.2, ↓reduceIte, cbind_app, clift_app, cpure_app, getErrno_run, hb,
        updS_mkx_again, Zlib.GzFs.Proofs.zstrerror_run, hgz]
      exact ⟨_, _, _, rfl, hfsw, hk1, Or.inr ⟨rfl, hpost⟩⟩
    · obtain ⟨St', K'⟩ := hst 0
      obtain ⟨h2, hgz, hpost⟩ := err_tail err errOwn K' own0 St'.up w' hfsw
      simp only [GzRead.ret_fail.2, ↓reduceIte, cbind_app, clift_app, cpure_app, getErrno_run, hb,
        Bool.false_eq_true, Zlib.GzFs.Proofs.zstrerror_run, hgz]
      exact ⟨_, _, _, rfl, hfsw, hk1, Or.inr ⟨rfl, hpost⟩⟩
  · rw [loadSlice_size] at hr2
    obtain ⟨k, hk⟩ : ∃ k : Nat, r.toInt = k := ⟨r.toInt.toNat, by omega⟩
    obtain ⟨hr3, -, -⟩ := GzRead.ret_count r k hk (by omega)
    have hneg : ¬ r.toInt32 < 0 := by
      rw [Int32.lt_iff_toInt_lt, hr3]; simp
    have hadd : ∀ v, Ptr.add (Ptr.ref (BRef.blk ob) c) (k : Int) (putGz h1 i v) =
        .ok (Ptr.ref (BRef.blk ob) (c + k), putGz h1 i v) :=
      fun v => Ptr.add_nat_ok (h := putGz h1 i v) (r := BRef.blk ob) (a := oa) hob (by omega)
    simp only [hneg, ↓reduceIte, cbind_app, clift_app, cpure_app, ldS_put, mkx_xnext, hr3, hadd,
      updX_mkx_next]
    exact ⟨_, _, _, rfl, hfsw, hk1, Or.inl ⟨rfl, c + k, by omega, by omega, rfl⟩⟩

/-- The offset of a pointer. -/
def poff : BPtr → Nat
  | .ref _ o => o
  | .null => 0

/-- **The write-out loop** `while (strm->next_out > state->x.next)`: it writes the output buffer up to `next_out`,
or fails with the `gz_error` report. The measure is the number of bytes still to write. -/
theorem out_loop (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 h1 : Heap} {s0 s1 : GzState} {fs0 fs : Fs}
    (S1 : St i src h1 s1) (K1 : Kept i h0 s0 h1 s1) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b)
    {ob bo c : Nat} (hop : s1.out = .ref (.blk ob) 0) (hno : s1.strm.next_out = .ref (.blk ob) bo)
    (hx : s1.x.next = .ref (.blk ob) c) (hc : c ≤ bo) (hfs : FileSystem fs) (hk : FdsKept fs0 fs) :
    ∃ z fs' h', gwhile (outCond i) (outBody i) none fs h1 = .ok ((z, fs'), h') ∧ FileSystem fs' ∧
      FdsKept fs0 fs' ∧
      ((z = none ∧ ∃ a, h' = putGz h1 i (mkx s1 ob bo a)) ∨
        (z = some (-1) ∧ GzPost h0 i s0 [] fs' h' (WeakS src s0))) := by
  have F := facts_of S1.up S1.direct S1.size
  obtain ⟨ob', oa, hop', hob, -, hos⟩ := F.outbuf
  rw [hop] at hop'
  cases hop'
  obtain ⟨b0, c0, hn0, -, -, -, hb0⟩ := F.out
  have hbo : bo ≤ oa.size := by
    rw [hno, hop] at hn0
    simp only [padv, Nat.zero_add, Ptr.ref.injEq, true_and] at hn0
    omega
  have hsz := F.want
  let J : Option Int32 → Fs → Heap → Prop := fun z fs h => FileSystem fs ∧ FdsKept fs0 fs ∧
    ((z = none ∧ ∃ c a, c ≤ bo ∧ h = putGz h1 i (mkx s1 ob c a)) ∨
      (z = some (-1) ∧ GzPost h0 i s0 [] fs h (WeakS src s0)))
  let P : Option Int32 → Fs → Heap → Prop := fun z fs h => FileSystem fs ∧ FdsKept fs0 fs ∧
    ((z = none ∧ ∃ a, h = putGz h1 i (mkx s1 ob bo a)) ∨
      (z = some (-1) ∧ GzPost h0 i s0 [] fs h (WeakS src s0)))
  let μ : Option Int32 → Fs → Heap → Nat := fun z _ h => match z with
    | some _ => 0
    | none => (match h.gzstates i with
      | some v => bo - poff v.x.next
      | none => 0) + 1
  have hμ : ∀ c a fs', μ none fs' (putGz h1 i (mkx s1 ob c a)) = bo - c + 1 := by
    intro c a fs'
    show (match (putGz h1 i (mkx s1 ob c a)).gzstates i with
      | some v => bo - poff v.x.next
      | none => 0) + 1 = bo - c + 1
    rw [show (putGz h1 i (mkx s1 ob c a)).gzstates i = some (mkx s1 ob c a) by simp [putGz]]
    rfl
  have step : ∀ x fs h, J x fs h → ∃ cc y fs1 h1', outCond i x fs h = .ok (((cc, y), fs1), h1') ∧
      (cc = false → P y fs1 h1') ∧
      (cc = true → ∃ z fs2 h2, outBody i y fs1 h1' = .ok ((z, fs2), h2) ∧ J z fs2 h2 ∧ μ z fs2 h2 < μ x fs h) := by
    rintro x fs h ⟨gfs, gk, ⟨rfl, c, a, hcb, rfl⟩ | ⟨rfl, gp⟩⟩
    · refine ⟨decide (c < bo), none, fs, _, out_cond_none hob rfl (by rw [mkx_strm]; exact hno) (by omega) hbo fs,
        fun e => ?_, fun e => ?_⟩
      · have : c = bo := by simp at e; omega
        subst this
        exact ⟨gfs, gk, Or.inl ⟨rfl, a, rfl⟩⟩
      · have hlt : c < bo := by simpa using e
        obtain ⟨z, fs2, h2, run, gfs2, gk2, res⟩ := out_body err errOwn S1 K1 own0 (a := a) hop hno hlt gfs gk
        refine ⟨z, fs2, h2, run, ⟨gfs2, gk2, ?_⟩, ?_⟩
        · rcases res with ⟨rfl, c', hcc, hcb', rfl⟩ | ⟨rfl, gp⟩
          · exact Or.inl ⟨rfl, c', 0, hcb', rfl⟩
          · exact Or.inr ⟨rfl, gp⟩
        · rcases res with ⟨rfl, c', hcc, hcb', rfl⟩ | ⟨rfl, gp⟩
          · rw [hμ c' 0 fs2, hμ c a fs]; omega
          · rw [hμ c a fs]; exact Nat.succ_pos _
    · exact ⟨false, some (-1), fs, h, out_cond_some (-1) fs h, fun _ => ⟨gfs, gk, Or.inr ⟨rfl, gp⟩⟩,
        fun e => by cases e⟩
  have init : J none fs h1 := ⟨hfs, hk, Or.inl ⟨rfl, c, s1.again, hc, by
    rw [mkx_self hx, putGz_self F.record]⟩⟩
  obtain ⟨z, fs', h', run, post⟩ := gwhile_go_spec (outCond i) (outBody i) J P μ step C.fuel none fs h1 init
    (by
      rw [show h1 = putGz h1 i (mkx s1 ob c s1.again) by rw [mkx_self hx, putGz_self F.record]]
      rw [hμ c s1.again fs]
      unfold C.fuel
      omega)
  exact ⟨z, fs', h', run, post.1, post.2.1, post.2.2⟩

/-! ## The transparent write loop -/

/-- The record with `again` set. -/
def mka (s : GzState) (a : Int32) : GzState := { s with again := a }

/-- The record after a transparent write of `w` bytes. -/
def mkn (s : GzState) (a : Int32) (w : UInt32) (np : BPtr) : GzState :=
  { mka s a with strm := { s.strm with avail_in := s.strm.avail_in - w, next_in := np } }

@[simp] theorem mka_strm (s : GzState) (a : Int32) : (mka s a).strm = s.strm := rfl
@[simp] theorem mka_fd (s : GzState) (a : Int32) : (mka s a).fd = s.fd := rfl

theorem updS_mka (h : Heap) (s : GzState) (a' : Int32) :
    updS (gzSt i) (fun s => { s with again := a' }) (putGz h i s) = .ok ((), putGz h i (mka s a')) :=
  updS_put h _ _

theorem updZ_mkn (h : Heap) (s : GzState) (a : Int32) (w : UInt32) (np : BPtr) :
    updZ (strmOf (gzSt i)) (fun z => { z with avail_in := z.avail_in - w, next_in := np }) (putGz h i (mka s a)) =
      .ok ((), putGz h i (mkn s a w np)) :=
  updZ_put h _ _

/-- A record write of a transparent writer, from the start of `gz_comp`. -/
theorem dstep {h0 h1 : Heap} {s0 s s' : GzState} (U : GzInvUpToInput (putGz h1 i s) i s src)
    (K : Kept i h0 s0 (putGz h1 i s) s) (hd : s.direct ≠ 0) (hz : s.size ≠ 0) (sh : SameShape s s')
    (hx : s'.x = s.x) (bo : BufOnly s.strm s'.strm) (hreset : s'.reset = s.reset) (inp : NextInOk s' src)
    (hai : InTrack s s') :
    GzInvUpToInput (putGz h1 i s') i s' src ∧ Kept i h0 s0 (putGz h1 i s') s' := by
  obtain ⟨U', ho, fr, hl⟩ := upTo_direct U hd hz sh hx bo hreset inp
  rw [putGz_putGz] at U' ho fr hl
  exact ⟨U', K.step fr hl ho sh hai rfl⟩

theorem direct_body (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 h1 : Heap} {s0 s : GzState} {fs0 fs : Fs}
    (U : GzInvUpToInput (putGz h1 i s) i s src) (K : Kept i h0 s0 (putGz h1 i s) s)
    (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b) (hd : s.direct ≠ 0) (hz : s.size ≠ 0)
    {r : BRef} {o : Nat} {arr : Array UInt8} (hsrc : src.pointer = .ref r o) (harr : Space.get h1 r = some arr)
    (hlen : o + src.length ≤ arr.size) (hav : s.strm.avail_in ≠ 0) (hfs : FileSystem fs) (hk : FdsKept fs0 fs) :
    ∃ z fs' h', directBody i none fs (putGz h1 i s) = .ok ((z, fs'), h') ∧ FileSystem fs' ∧ FdsKept fs0 fs' ∧
      ((z = none ∧ ∃ s', h' = putGz h1 i s' ∧ GzInvUpToInput h' i s' src ∧ Kept i h0 s0 h' s' ∧
          s'.direct ≠ 0 ∧ s'.size ≠ 0 ∧ s'.strm.avail_in.toNat < s.strm.avail_in.toNat) ∨
        (z = some (-1) ∧ GzPost h0 i s0 [] fs' h' (WeakS src s0))) := by
  obtain ⟨a0, hni, hle⟩ : ∃ a0, s.strm.next_in = padv src.pointer a0 ∧
      a0 + s.strm.avail_in.toNat ≤ src.length := by
    rcases U.2.2.2.1 with ⟨-, h0⟩ | e
    · exact absurd h0 hav
    · exact e
  have hni' : s.strm.next_in = Ptr.ref r (o + a0) := by rw [hni, hsrc]; rfl
  have hav' : 0 < s.strm.avail_in.toNat := by
    rcases Nat.eq_zero_or_pos s.strm.avail_in.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hav
    · exact e
  have hput : (dirPut ((((0 : UInt32) - 1) >>> 2) + 1) s.strm.avail_in).toNat =
      min s.strm.avail_in.toNat (2 ^ 30) := dirPut_val _
  have hload : ∀ v, loadBytes (Ptr.ref r (o + a0)) (min s.strm.avail_in.toNat (2 ^ 30)) (putGz h1 i v) =
      .ok (loadSlice arr (o + a0) (min s.strm.avail_in.toNat (2 ^ 30)), putGz h1 i v) :=
    fun v => loadBytes_eq (h := putGz h1 i v) (by rw [get_putGz]; exact harr) (by omega)
  have hfs1 : FileSystem { fs with errno := 0 } := hfs
  obtain ⟨w, w', hw, hres, hfsw, hkw⟩ := fsWrite_contract_m s.fd
    (loadSlice arr (o + a0) (min s.strm.avail_in.toNat (2 ^ 30))) { fs with errno := 0 } hfs1
    (by rw [loadSlice_size]; omega) (by rw [loadSlice_size]; omega)
  have hk1 : FdsKept fs0 w' := fun j => (hkw j).trans (hk j)
  have hwH : ∀ H : Heap, fsWrite s.fd (loadSlice arr (o + a0) (min s.strm.avail_in.toNat (2 ^ 30)))
      { fs with errno := 0 } H = .ok ((w, w'), H) := fun H => by rw [hw]; rfl
  have shA : ∀ a, SameShape s (mka s a) := fun a => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have stA : ∀ a, GzInvUpToInput (putGz h1 i (mka s a)) i (mka s a) src ∧
      Kept i h0 s0 (putGz h1 i (mka s a)) (mka s a) := fun a =>
    dstep U K hd hz (shA a) rfl (by unfold BufOnly; rfl) rfl U.2.2.2.1 (InTrack.of_in rfl rfl)
  unfold directBody
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
    Zlib.GzFs.Proofs.stable_setErrno, updS_mka, ldZ_put, ldS_put, mka_strm, mka_fd, hni', hput, hload, hwH,
    getErrno_run]
  rcases hres with rfl | ⟨hr1, hr2⟩
  · by_cases hb : BLOCKED w'.errno = true
    · have st1 := dstep (stA 0).1 (stA 0).2 hd hz
        (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : SameShape (mka s 0) (mka (mka s 0) 1))
        rfl (by unfold BufOnly; rfl) rfl U.2.2.2.1 (InTrack.of_in rfl rfl)
      obtain ⟨h2, hgz, hpost⟩ := err_tail err errOwn st1.2 own0 st1.1 w' hfsw
      simp only [GzRead.ret_fail.2, ↓reduceIte, cbind_app, clift_app, cpure_app, getErrno_run, hb,
        updS_mka, Zlib.GzFs.Proofs.zstrerror_run, hgz]
      exact ⟨_, _, _, rfl, hfsw, hk1, Or.inr ⟨rfl, hpost⟩⟩
    · obtain ⟨h2, hgz, hpost⟩ := err_tail err errOwn (stA 0).2 own0 (stA 0).1 w' hfsw
      simp only [GzRead.ret_fail.2, ↓reduceIte, cbind_app, clift_app, cpure_app, getErrno_run, hb,
        Bool.false_eq_true, Zlib.GzFs.Proofs.zstrerror_run, hgz]
      exact ⟨_, _, _, rfl, hfsw, hk1, Or.inr ⟨rfl, hpost⟩⟩
  · rw [loadSlice_size] at hr2
    obtain ⟨k, hk⟩ : ∃ k : Nat, w.toInt = k := ⟨w.toInt.toNat, by omega⟩
    obtain ⟨hr3, -, hr4⟩ := GzRead.ret_count w k hk (by omega)
    have hneg : ¬ w.toInt32 < 0 := by
      rw [Int32.lt_iff_toInt_lt, hr3]; simp
    have hadd : ∀ v, Ptr.add (Ptr.ref r (o + a0)) (k : Int) (putGz h1 i v) =
        .ok (Ptr.ref r (o + a0 + k), putGz h1 i v) :=
      fun v => Ptr.add_nat_ok (h := putGz h1 i v) (a := arr) (by rw [get_putGz]; exact harr) (by omega)
    simp only [hneg, ↓reduceIte, cbind_app, clift_app, cpure_app, ldZ_put, mka_strm, hni', hr3, hadd,
      updZ_mkn]
    have hsub : (s.strm.avail_in - w.toInt32.toUInt32).toNat = s.strm.avail_in.toNat - k := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hr4]; omega), hr4]
    have st := dstep (s' := mkn s 0 w.toInt32.toUInt32 (Ptr.ref r (o + a0 + k))) U K hd hz
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl (by unfold BufOnly; rfl) rfl
      (Or.inr ⟨a0 + k, by show Ptr.ref r (o + a0 + k) = padv src.pointer (a0 + k); rw [hsrc]; simp [padv]; omega,
        by show a0 + k + (s.strm.avail_in - w.toInt32.toUInt32).toNat ≤ src.length; rw [hsub]; omega⟩)
      ⟨k, by show Ptr.ref r (o + a0 + k) = advance s.strm.next_in k; rw [hni']; rfl,
        by show (s.strm.avail_in - w.toInt32.toUInt32).toNat + k = _; rw [hsub]; omega⟩
    exact ⟨_, _, _, rfl, hfsw, hk1, Or.inl ⟨rfl, _, rfl, st.1, st.2, hd, hz,
      by show (s.strm.avail_in - w.toInt32.toUInt32).toNat < _; rw [hsub]; omega⟩⟩

theorem direct_cond_none (h : Heap) (s : GzState) (fs : Fs) :
    directCond i none fs (putGz h i s) = .ok (((s.strm.avail_in != 0, none), fs), putGz h i s) := by
  unfold directCond
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, liftM, monadLift, MonadLift.monadLift,
    MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, ldZ_put]

theorem direct_cond_some (v : Int32) (fs : Fs) (h : Heap) :
    directCond i (some v) fs h = .ok (((false, some v), fs), h) := by
  unfold directCond
  simp only [Option.isSome_some, ↓reduceIte, cpure_app]

/-- **The transparent write loop** `while (strm->avail_in)`: it writes all the pending input, or fails with the
`gz_error` report. The measure is the pending input. -/
theorem direct_loop (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 h1 : Heap} {s0 s1 : GzState} {fs0 fs : Fs}
    (U : GzInvUpToInput h1 i s1 src) (K : Kept i h0 s0 h1 s1) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b)
    (hd : s1.direct ≠ 0) (hz : s1.size ≠ 0) (hfs : FileSystem fs) (hk : FdsKept fs0 fs) :
    ∃ z fs' h', gwhile (directCond i) (directBody i) none fs h1 = .ok ((z, fs'), h') ∧ FileSystem fs' ∧
      FdsKept fs0 fs' ∧
      ((z = none ∧ ∃ s', GzInvUpToInput h' i s' src ∧ Kept i h0 s0 h' s' ∧ s'.strm.avail_in = 0) ∨
        (z = some (-1) ∧ GzPost h0 i s0 [] fs' h' (WeakS src s0))) := by
  have hs1 := U.1
  have sh1 := K.2.2.2.1
  have hd0 : s0.direct ≠ 0 := fun e => hd (sh1.2.2.2.2.2.2.1.trans e)
  have hz0 : s0.size ≠ 0 := fun e => hz (sh1.2.2.2.2.1.trans e)
  have hview : ∀ s, GzInvUpToInput (putGz h1 i s) i s src → s.size ≠ 0 →
      s.strm.avail_in ≠ 0 → ∃ r o arr, src.pointer = .ref r o ∧ Space.get h1 r = some arr ∧
        o + src.length ≤ arr.size := by
    intro s Us hz' hav
    obtain ⟨a0, hni, hle⟩ : ∃ a0, s.strm.next_in = padv src.pointer a0 ∧
        a0 + s.strm.avail_in.toNat ≤ src.length := by
      rcases Us.2.2.2.1 with ⟨-, h0⟩ | e
      · exact absurd h0 hav
      · exact e
    have hav' : 0 < s.strm.avail_in.toNat := by
      rcases Nat.eq_zero_or_pos s.strm.avail_in.toNat with e | e
      · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hav
      · exact e
    rcases Us.2.2.2.2 with ⟨hp, hl⟩ | ⟨⟨xs, hb⟩, -⟩
    · obtain ⟨b, a, hp', hb, -, hsz'⟩ := ((Us.2.1.writer Us.2.2.1).bufs hz').1
      refine ⟨.blk b, 0, a, by rw [hp]; exact hp', hb, ?_⟩
      change a.size = 2 * s.size.toNat at hsz'
      omega
    · rcases hb with ⟨hn, hl0, -⟩ | ⟨r, o, arr, hp, hg, hl', -⟩
      · omega
      · exact ⟨r, o, arr, hp, by rw [get_putGz] at hg; exact hg, hl'⟩
  let J : Option Int32 → Fs → Heap → Prop := fun z fs h => FileSystem fs ∧ FdsKept fs0 fs ∧
    ((z = none ∧ ∃ s, h = putGz h1 i s ∧ GzInvUpToInput h i s src ∧ Kept i h0 s0 h s) ∨
      (z = some (-1) ∧ GzPost h0 i s0 [] fs h (WeakS src s0)))
  let P : Option Int32 → Fs → Heap → Prop := fun z fs h => FileSystem fs ∧ FdsKept fs0 fs ∧
    ((z = none ∧ ∃ s', GzInvUpToInput h i s' src ∧ Kept i h0 s0 h s' ∧ s'.strm.avail_in = 0) ∨
      (z = some (-1) ∧ GzPost h0 i s0 [] fs h (WeakS src s0)))
  let μ : Option Int32 → Fs → Heap → Nat := fun z _ h => match z with
    | some _ => 0
    | none => (match h.gzstates i with
      | some v => v.strm.avail_in.toNat
      | none => 0) + 1
  have hμ : ∀ s fs', μ none fs' (putGz h1 i s) = s.strm.avail_in.toNat + 1 := by
    intro s fs'
    show (match (putGz h1 i s).gzstates i with
      | some v => v.strm.avail_in.toNat
      | none => 0) + 1 = _
    rw [show (putGz h1 i s).gzstates i = some s by simp [putGz]]
  have step : ∀ x fs h, J x fs h → ∃ cc y fs1 h1', directCond i x fs h = .ok (((cc, y), fs1), h1') ∧
      (cc = false → P y fs1 h1') ∧
      (cc = true → ∃ z fs2 h2, directBody i y fs1 h1' = .ok ((z, fs2), h2) ∧ J z fs2 h2 ∧
        μ z fs2 h2 < μ x fs h) := by
    rintro x fs h ⟨gfs, gk, ⟨rfl, s, rfl, Us, Ks⟩ | ⟨rfl, gp⟩⟩
    · refine ⟨s.strm.avail_in != 0, none, fs, _, direct_cond_none h1 s fs,
        fun e => ⟨gfs, gk, Or.inl ⟨rfl, s, Us, Ks, by simpa using e⟩⟩,
        fun e => ?_⟩
      have hav : s.strm.avail_in ≠ 0 := by simpa using e
      have hds : s.direct ≠ 0 := fun x => hd0 (Ks.2.2.2.1.2.2.2.2.2.2.1.symm.trans x)
      have hzs : s.size ≠ 0 := fun x => hz0 (Ks.2.2.2.1.2.2.2.2.1.symm.trans x)
      obtain ⟨r, o, arr, hsrc, harr, hlen⟩ := hview s Us hzs hav
      obtain ⟨z, fs2, h2, run, gfs2, gk2, res⟩ :=
        direct_body err errOwn Us Ks own0 hds hzs hsrc harr hlen hav gfs gk
      refine ⟨z, fs2, h2, run, ⟨gfs2, gk2, ?_⟩, ?_⟩
      · rcases res with ⟨rfl, s', rfl, Us', Ks', -⟩ | ⟨rfl, gp⟩
        · exact Or.inl ⟨rfl, s', rfl, Us', Ks'⟩
        · exact Or.inr ⟨rfl, gp⟩
      · rcases res with ⟨rfl, s', rfl, -, -, -, -, hlt⟩ | ⟨rfl, -⟩
        · rw [hμ s' fs2, hμ s fs]; omega
        · rw [hμ s fs]; exact Nat.succ_pos _
    · exact ⟨false, some (-1), fs, h, direct_cond_some (-1) fs h, fun _ => ⟨gfs, gk, Or.inr ⟨rfl, gp⟩⟩,
        fun e => by cases e⟩
  have e1 : h1 = putGz h1 i s1 := (putGz_self hs1).symm
  have init : J none fs h1 := ⟨hfs, hk, Or.inl ⟨rfl, s1, e1, U, K⟩⟩
  obtain ⟨z, fs', h', run, post⟩ := gwhile_go_spec (directCond i) (directBody i) J P μ step C.fuel none fs h1 init
    (by
      rw [e1, hμ s1 fs]
      have := s1.strm.avail_in.toNat_lt
      unfold C.fuel
      omega)
  exact ⟨z, fs', h', run, post.1, post.2.1, post.2.2⟩

/-! ## One trip of the deflate loop -/

/-- The part of the body of the deflate loop from `have = strm->avail_out` on. -/
def compRest (i : Nat) (flush : Int32) (l : Zlib.Gzwrite.CompLoop) : G Zlib.Gzwrite.CompLoop := do
  let strm := strmOf (gzSt i)
  let state := gzSt i
  let hv := (← ldZ strm).avail_out
  let ret ← Zlib.Deflate.deflate strm flush
  if ret == Z_STREAM_ERROR then
    Zlib.Gzlib.gz_error state Z_STREAM_ERROR (← Zlib.GzFs.strLit "internal error: deflate stream corrupt")
    return { l with ret, res := some (-1) }
  return { l with ret, «have» := hv - (← ldZ strm).avail_out }

theorem compBody_eq (flush : Int32) (l : Zlib.Gzwrite.CompLoop) :
    compBody i flush l = (do
      let z ← ldZ (strmOf (gzSt i))
      if z.avail_out == 0 || (flush != Z_NO_FLUSH && (flush != Z_FINISH || l.ret == Z_STREAM_END)) then
        let r ← gwhile (outCond i) (outBody i) none
        if r.isSome then pure { l with res := r }
        else do
          if (← ldZ (strmOf (gzSt i))).avail_out == 0 then
            let s ← ldS (gzSt i)
            updZ (strmOf (gzSt i)) fun z => { z with avail_out := s.size, next_out := s.out }
            updX (gzSt i) fun x => { x with next := s.out }
          compRest i flush l
      else compRest i flush l) := rfl

set_option maxRecDepth 20000 in
theorem corrupt_cstring (H : Heap) {k : Nat} (hk : strIndex "internal error: deflate stream corrupt" = some k) :
    ∃ t, CString H (.ref (.str k) 0) t := by
  have hb : strBytes "internal error: deflate stream corrupt" =
      #[105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 100, 101, 102, 108, 97, 116,
        101, 32, 115, 116, 114, 101, 97, 109, 32, 99, 111, 114, 114, 117, 112, 116, 0] := by
    decide +kernel
  have hg : Space.get H (BRef.str k) =
      some #[105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 100, 101, 102, 108, 97, 116,
        101, 32, 115, 116, 114, 101, 97, 109, 32, 99, 111, 114, 114, 117, 112, 116, 0] := by
    have he := strLitRef_get (h := H) hk
    rw [hb] at he
    exact he
  exact ⟨[105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 100, 101, 102, 108, 97, 116,
      101, 32, 115, 116, 114, 101, 97, 109, 32, 99, 111, 114, 114, 117, 112, 116],
    Or.inr ⟨.str k, 0, _, rfl, hg, by decide, by decide⟩, by decide, by decide⟩

/-- **The deflate call and its report** (`compRest`), given the run of the call (`call_step`). -/
theorem comp_rest (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 H after : Heap} {s0 s s' : GzState}
    {fs0 fs : Fs} (S : St i src H s) (K : Kept i h0 s0 H s) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b)
    (flush rc : Int32) (l : Zlib.Gzwrite.CompLoop) (hfs : FileSystem fs) (hk : FdsKept fs0 fs)
    (run : C.run (Zlib.Deflate.deflate (some (gzStrm i)) flush) H = .ok (rc, after))
    (hs' : after.gzstates i = some s') (S' : St i src after s') (K' : Kept i h0 s0 after s') :
    ∃ l' h', compRest i flush l fs H = .ok ((l', fs), h') ∧
      ((rc = Z_STREAM_ERROR ∧ l'.res = some (-1) ∧
          GzPost h0 i s0 [] fs h' (WeakS src s0)) ∨
        (rc ≠ Z_STREAM_ERROR ∧ l' = { l with ret := rc, «have» := s.strm.avail_out - s'.strm.avail_out } ∧
          h' = after)) := by
  have hs := S.up.1
  have hz1 : ldZ (strmOf (gzSt i)) H = .ok (s.strm, H) := Zlib.Gzlib.Proofs.ldZ_run hs
  have hz2 : ldZ (strmOf (gzSt i)) after = .ok (s'.strm, after) := Zlib.Gzlib.Proofs.ldZ_run hs'
  have run' : Zlib.Deflate.deflate (strmOf (gzSt i)) flush H = .ok (rc, after) := by
    rw [show strmOf (gzSt i) = some (gzStrm i) from rfl]; exact run
  obtain ⟨k, hk'⟩ := strIndex_of_mem (s := "internal error: deflate stream corrupt") (by decide +kernel)
  unfold compRest
  simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
    hz1, run']
  by_cases he : rc = Z_STREAM_ERROR
  · subst he
    have W : GzInvUpToInput after i s' src := S'.up
    obtain ⟨t, ct⟩ := corrupt_cstring after hk'
    obtain ⟨h2, s2, run2, U2, e2, fr, lc, own⟩ := gz_error_upToInput err errOwn W Z_STREAM_ERROR
      (.ref (.str k) 0) (Or.inr ⟨t, ct, fun b hb => by simp [ByteRoot] at hb⟩) (by decide)
    have run2' : Zlib.Gzlib.gz_error (gzSt i) Z_STREAM_ERROR (.ref (.str k) 0) after = .ok ((), h2) := run2
    have weak : ∀ {h : Heap} {v : GzState}, GzInvUpToInput h i v src → GzInvUpToInputWeak h i v src :=
      fun U => ⟨U.1, U.2.1, U.2.2.1, U.2.2.2.1, U.2.2.2.2.imp id (fun y => y.2)⟩
    obtain ⟨m1o, -, hc⟩ := weak_facts (weak W)
    obtain ⟨m2o, o2l, -⟩ := weak_facts (weak U2)
    simp only [beq_self_eq_true, ↓reduceIte, cbind_app, clift_app, cpure_app, Zlib.GzFs.strLit,
      strLitRef_of_index hk', run2']
    exact ⟨_, _, rfl, Or.inl ⟨by simp, by simp,
      post_of_error K'.weak own0 hs' U2.1 e2 fr lc own m1o m2o o2l hc hfs
        ⟨weak U2, CompShape.of_error K'.2.2.2.1 K'.2.2.2.2.1 e2⟩⟩⟩
  · have hne : (rc == Z_STREAM_ERROR) = false := by simpa using he
    simp only [hne, Bool.false_eq_true, ↓reduceIte, cbind_app, clift_app, cpure_app, hz2]
    exact ⟨_, _, rfl, Or.inr ⟨he, rfl, rfl⟩⟩

/-- The record after the output buffer was written out and reset. -/
def mkr (s : GzState) (ob bo : Nat) (a : Int32) : GzState :=
  let v := mkx s ob bo a
  let v2 : GzState := { v with strm := { v.strm with avail_out := v.size, next_out := v.out } }
  { v2 with x := { v2.x with next := v.out } }

/-- **The prefix of the deflate loop's body**: the optional write-out and the reset of the output buffer. It
reaches the deflate call with room in the output buffer, or fails with the `gz_error` report. -/
theorem comp_prefix (err : GzErrorSpec) (errOwn : GzErrorOwn) {h0 h : Heap} {s0 s : GzState} {fs0 fs : Fs}
    (S : St i src h s) (K : Kept i h0 s0 h s) (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b)
    (flush : Int32) (l : Zlib.Gzwrite.CompLoop) (hfs : FileSystem fs) (hk : FdsKept fs0 fs) :
    (∃ s2 fs2, St i src (putGz h i s2) s2 ∧ Kept i h0 s0 (putGz h i s2) s2 ∧ BufOnly s.strm s2.strm ∧
      s2.strm.next_in = s.strm.next_in ∧ s2.strm.avail_in = s.strm.avail_in ∧ s2.strm.avail_out ≠ 0 ∧
      (s.strm.avail_out = 0 → s2.strm.avail_out = s.size) ∧
      (s.strm.avail_out ≠ 0 → s2.strm.avail_out = s.strm.avail_out) ∧
      FileSystem fs2 ∧ FdsKept fs0 fs2 ∧ compBody i flush l fs h = compRest i flush l fs2 (putGz h i s2)) ∨
    (∃ l' fs' h', compBody i flush l fs h = .ok ((l', fs'), h') ∧ l'.res = some (-1) ∧ FileSystem fs' ∧
      FdsKept fs0 fs' ∧ GzPost h0 i s0 [] fs' h' (WeakS src s0)) := by
  have F := facts_of S.up S.direct S.size
  obtain ⟨ob, oa, hop, hob, -, hos⟩ := F.outbuf
  obtain ⟨bo, c0, hn0, ha0, hx0, hcb, hb0⟩ := F.out
  have hno : s.strm.next_out = .ref (.blk ob) bo := by rw [hn0, hop]; simp [padv]
  have hx : s.x.next = .ref (.blk ob) c0 := by rw [hx0, hop]; simp [padv]
  have hz1 : ldZ (strmOf (gzSt i)) h = .ok (s.strm, h) := Zlib.Gzlib.Proofs.ldZ_run S.up.1
  have e : h = putGz h i s := (putGz_self S.up.1).symm
  have hsz : s.size.toNat ≠ 0 := by
    intro x; apply S.size; exact UInt32.toNat_inj.mp (by rw [x]; rfl)
  rw [compBody_eq]
  by_cases hA : (s.strm.avail_out == 0 || (flush != Z_NO_FLUSH && (flush != Z_FINISH || l.ret == Z_STREAM_END))) = true
  · obtain ⟨z, fs', h', run, gfs, gk, res⟩ := out_loop err errOwn S K own0 hop hno hx hcb hfs hk
    rcases res with ⟨rfl, a, rfl⟩ | ⟨rfl, gp⟩
    · obtain ⟨Sx, Kx⟩ := out_state S K hop hno a (Nat.le_refl bo)
      by_cases h0 : s.strm.avail_out = 0
      · have sh : SameShape (mkx s ob bo a) (mkr s ob bo a) :=
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨Sr, fr, hl, ho⟩ := st_record Sx sh (by unfold BufOnly; rfl) F.reset
          ⟨0, 0, by show s.out = padv s.out 0; rw [hop]; simp [padv],
            by show s.size.toNat = s.size.toNat - 0; omega,
            by show s.out = padv s.out 0; rw [hop]; simp [padv], Nat.le_refl 0, Nat.zero_le _⟩ S.up.2.2.2.1
        rw [putGz_putGz] at Sr fr hl ho
        refine Or.inl ⟨mkr s ob bo a, fs', Sr, Kx.step fr hl ho sh (InTrack.of_in rfl rfl) rfl, by unfold BufOnly; rfl, rfl, rfl, S.size,
          fun _ => rfl, fun e => absurd h0 e, gfs, gk, ?_⟩
        have hA0 : (s.strm.avail_out == 0) = true := by simp [h0]
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
          hz1, hA, ↓reduceIte, run, Option.isSome_none, Bool.false_eq_true]
        simp only [cbind_app, clift_app, cpure_app, ldZ_put, mkx_strm, hA0, ↓reduceIte, ldS_put,
          updZ_put, updX_put]
        rfl
      · refine Or.inl ⟨mkx s ob bo a, fs', Sx, Kx, by unfold BufOnly; rfl, rfl, rfl, h0, fun e => absurd e h0,
          fun _ => rfl, gfs, gk, ?_⟩
        have hA0 : (s.strm.avail_out == 0) = false := by simpa using h0
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
          hz1, hA, ↓reduceIte, run, Option.isSome_none, Bool.false_eq_true]
        simp only [cbind_app, clift_app, cpure_app, ldZ_put, mkx_strm, hA0, Bool.false_eq_true, ↓reduceIte]
    · refine Or.inr ⟨{ l with res := some (-1) }, fs', h', ?_, rfl, gfs, gk, gp⟩
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
        hz1, hA, ↓reduceIte, run, Option.isSome_some]
  · have hA' : (s.strm.avail_out == 0 || (flush != Z_NO_FLUSH && (flush != Z_FINISH || l.ret == Z_STREAM_END))) =
        false := by simpa using hA
    have h0 : s.strm.avail_out ≠ 0 := by
      intro x; simp [x] at hA
    refine Or.inl ⟨s, fs, by rw [← e]; exact S, by rw [← e]; exact K, by unfold BufOnly; rfl, rfl, rfl, h0,
      fun x => absurd x h0, fun _ => rfl, hfs, hk, ?_⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
      hz1, hA', Bool.false_eq_true, ↓reduceIte]
    rw [← e]


/-! ## The deflate loop: the measure -/

/-- The pending input of the record. -/
def recIn (h : Heap) (i : Nat) : Nat := match h.gzstates i with
  | some s => s.strm.avail_in.toNat
  | none => 0

/-- The room of the output buffer of the record. -/
def recOut (h : Heap) (i : Nat) : Nat := match h.gzstates i with
  | some s => s.strm.avail_out.toNat
  | none => 0

theorem recIn_of {h : Heap} {s : GzState} (hs : h.gzstates i = some s) : recIn h i = s.strm.avail_in.toNat := by
  simp [recIn, hs]

theorem recOut_of {h : Heap} {s : GzState} (hs : h.gzstates i = some s) : recOut h i = s.strm.avail_out.toNat := by
  simp [recOut, hs]

/-- The potential with the pending input. -/
def PsiP (Φ : Int32 → Heap → ZStreamRef → Nat) (flush : Int32) (i : Nat) (h : Heap) : Nat :=
  Φ flush h (gzStrm i) + 2 ^ 30 * recIn h i

/-- The next call produces nothing: quiet with no input, or finished with nothing pending and with input. -/
def SilentP (Quiet : Int32 → Heap → ZStreamRef → Prop) (flush : Int32) (i : Nat) (h : Heap) : Prop :=
  ∃ s, h.gzstates i = some s ∧ s.strm.avail_out ≠ 0 ∧
    ((s.strm.avail_in = 0 ∧ Quiet flush h (gzStrm i)) ∨
      (s.strm.avail_in ≠ 0 ∧ ∃ k d, s.strm.state = some (.deflate k) ∧ h.dstates k = some d ∧
        d.status = FINISH_STATE ∧ d.pending = 0))

open Classical in
/-- The measure of the deflate loop: 1 before a silent call, `2 + Ψ` before a call with a full output buffer
(reset to at least 8 bytes), `3 + 2^63` otherwise (the first trip only). -/
noncomputable def muP (Φ : Int32 → Heap → ZStreamRef → Nat) (Quiet : Int32 → Heap → ZStreamRef → Prop)
    (flush : Int32) (i : Nat) (h : Heap) : Nat :=
  if SilentP Quiet flush i h then 1 else if recOut h i = 0 then 2 + PsiP Φ flush i h else 3 + 2 ^ 63

theorem u32_ne_zero {x : UInt32} : x ≠ 0 ↔ x.toNat ≠ 0 := by
  constructor
  · intro hx e; exact hx (UInt32.toNat_inj.mp (by rw [e]; rfl))
  · intro hx e; exact hx (by rw [e]; rfl)

theorem psi_lt {Φ : Int32 → Heap → ZStreamRef → Nat} {Quiet : Int32 → Heap → ZStreamRef → Prop}
    (hc : QuietClauses Φ Quiet) {flush : Int32} (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5)
    {h : Heap} {s : GzState} (S : St i src h s) : PsiP Φ flush i h < 2 ^ 63 := by
  have F := facts_of S.up S.direct S.size
  obtain ⟨k, d, hk, hdk, hhead⟩ := F.head
  have hget : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, F.record]
  have hB := hc.2.2.2.2.1 flush h (gzStrm i) s.strm k d hf.1 hf.2 F.reach hget hk hdk hhead
  have := s.strm.avail_in.toNat_lt
  unfold PsiP
  rw [recIn_of F.record]
  omega

theorem muP_lt {Φ : Int32 → Heap → ZStreamRef → Nat} {Quiet : Int32 → Heap → ZStreamRef → Prop}
    (hc : QuietClauses Φ Quiet) {flush : Int32} (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5)
    {h : Heap} {s : GzState} (S : St i src h s) : muP Φ Quiet flush i h < C.fuel := by
  have := psi_lt hc hf S
  unfold muP C.fuel
  split
  · omega
  · split <;> omega

/-- **One trip of the deflate loop**, with the measure: when the loop continues, the measure falls. -/
theorem comp_trip (err : GzErrorSpec) (errOwn : GzErrorOwn) {Φ : Int32 → Heap → ZStreamRef → Nat}
    {Quiet : Int32 → Heap → ZStreamRef → Prop} (hc : QuietClauses Φ Quiet) {flush : Int32}
    (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) {h0 : Heap} {s0 : GzState} {fs0 : Fs}
    (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b) {l : Zlib.Gzwrite.CompLoop} {fs : Fs} {h : Heap} {s : GzState}
    (hl : l.res = none) (S : St i src h s) (K : Kept i h0 s0 h s) (hfs : FileSystem fs) (hk : FdsKept fs0 fs) :
    ∃ y fs1 h1, compBody i flush l fs h = .ok ((y, fs1), h1) ∧ FileSystem fs1 ∧ FdsKept fs0 fs1 ∧
      ((y.res = some (-1) ∧ GzPost h0 i s0 [] fs1 h1 (WeakS src s0)) ∨
        (y.res = none ∧ ∃ s1, St i src h1 s1 ∧ Kept i h0 s0 h1 s1 ∧
          (y.«have» = 0 → flush = Z_NO_FLUSH → s1.strm.avail_in = 0) ∧
          (y.«have» ≠ 0 → muP Φ Quiet flush i h1 < muP Φ Quiet flush i h))) := by
  classical
  obtain ⟨c1, c2, c3, c4, cB, c1', c2', c2f⟩ := hc
  have F := facts_of S.up S.direct S.size
  rcases comp_prefix err errOwn S K own0 flush l hfs hk with
    ⟨s2, fs2, S2, K2, bo2, hni2, hai2, hao2, hreset, hkeep, gfs2, gk2, heq⟩ |
    ⟨l', fs', h', run, hres, gfs, gk, gp⟩
  · obtain ⟨rc, after, s3, ds, d, run3, hs3, S3, frG, hlv, how, es3, exec, reach2, buf2, act2, get2, get3, nn2,
      inv2, st3, ao3, ai3, hse⟩ := call_step S2 flush
    have K3 : Kept i h0 s0 after s3 := K2.step frG hlv how (by rw [es3]; exact SameShape.refl _) ai3
      (Zlib.Deflate.BorrowProofs.stable_deflate _ _ _ _ _ run3)
    obtain ⟨l', h', run4, res⟩ := comp_rest err errOwn S2 K2 own0 flush rc l gfs2 gk2 run3 hs3 S3 K3
    refine ⟨l', fs2, h', by rw [heq]; exact run4, gfs2, gk2, ?_⟩
    rcases res with ⟨hrc, hres', gp⟩ | ⟨hrc, rfl, he⟩
    · exact Or.inl ⟨hres', gp⟩
    rw [he]
    refine Or.inr ⟨hl, s3, S3, K3, ?_, fun hhave => ?_⟩
    · -- a call that produced nothing with no flush consumed all the input
      intro h0 hnf
      have e3 : s3.strm.avail_out = s2.strm.avail_out := by
        have hsub : s2.strm.avail_out - s3.strm.avail_out = 0 := h0
        have hle : s3.strm.avail_out.toNat ≤ s2.strm.avail_out.toNat := ao3
        have hc := congrArg UInt32.toNat hsub
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)] at hc
        exact UInt32.toNat_inj.mp (by simp at hc; omega)
      by_cases hz : s2.strm.avail_in = 0
      · have h3 : s3.strm.avail_in.toNat ≤ s2.strm.avail_in.toNat := ai3.le
        rw [hz] at h3
        exact UInt32.toNat_inj.mp (by simpa using h3)
      · by_cases hfin : d.status = FINISH_STATE
        · exact absurd (hse.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨hfin, by rw [hnf]; decide⟩))))) hrc
        · exact (c2' flush (putGz h i s2) (gzStrm i) s2.strm ds d rc after s3.strm hf.1 hf.2 reach2 buf2 act2
            get2 inv2.good.live.zst inv2.good.live.hs hfin nn2 hz hao2 exec hrc get3 (by rw [e3]; exact hao2)).1
    have hne : s3.strm.avail_out ≠ s2.strm.avail_out := fun e => hhave (by
      show s2.strm.avail_out - s3.strm.avail_out = 0
      rw [e]; simp)
    -- the record write before the call is a rebuffer
    have hgetH : (gzStrm i).get h = some s.strm := by simp [ZStreamRef.get, gzStrm, F.record]
    have reb : Rebuffer h (putGz h i s2) (gzStrm i) := rebuffer_put F.record F.recFree F.fresh F.uniq F.globals bo2
    have keep4 := c4 flush h (putGz h i s2) (gzStrm i) s.strm s2.strm F.reach reb hgetH get2 hni2 hai2
    have zst := inv2.good.live.zst
    have hsd := inv2.good.live.hs
    have hsize8 := F.want
    have psi3 := psi_lt (src := src) ⟨c1, c2, c3, c4, cB, c1', c2', c2f⟩ hf S3
    have F3 := facts_of S3.up S3.direct S3.size
    -- the measure before and after
    have muH : muP Φ Quiet flush i h = if SilentP Quiet flush i h then 1 else
        if s.strm.avail_out.toNat = 0 then 2 + (Φ flush h (gzStrm i) + 2 ^ 30 * s.strm.avail_in.toNat)
        else 3 + 2 ^ 63 := by
      unfold muP PsiP; rw [recOut_of F.record, recIn_of F.record]
    have muA : ∀ (sil : SilentP Quiet flush i after → False), muP Φ Quiet flush i after =
        if s3.strm.avail_out.toNat = 0 then 2 + (Φ flush after (gzStrm i) + 2 ^ 30 * s3.strm.avail_in.toNat)
        else 3 + 2 ^ 63 := by
      intro sil
      unfold muP PsiP; rw [if_neg sil, recOut_of hs3, recIn_of hs3]
    have muS : SilentP Quiet flush i after → muP Φ Quiet flush i after = 1 := by
      intro sil; unfold muP; rw [if_pos sil]
    have ai3' : s3.strm.avail_in.toNat ≤ s2.strm.avail_in.toNat := ai3.le
    by_cases hsil : SilentP Quiet flush i h
    · exfalso
      obtain ⟨s', hs', hao, hcase⟩ := hsil
      rw [F.record] at hs'
      cases hs'
      have hao2' : s2.strm.avail_out = s.strm.avail_out := hkeep hao
      rcases hcase with ⟨hai, hq⟩ | ⟨hai, k, dk, hk, hdk, hfin, hpend⟩
      · have e := c3 flush (putGz h i s2) (gzStrm i) s2.strm rc after s3.strm (keep4.2 hq) hf.1 hf.2 reach2 buf2
          act2 get2 nn2 (hai2.trans hai) exec get3
        exact hne e
      · have ek : k = ds := by
          have := bo2.state
          rw [zst, hk] at this
          cases this
          rfl
        subst ek
        have ed : dk = d := by
          have : (putGz h i s2).dstates k = h.dstates k := rfl
          rw [this, hdk] at hsd
          cases hsd
          rfl
        subst ed
        by_cases hr : DeflateRefuses s2.strm dk flush
        · exact hrc (hse.2 hr)
        · obtain ⟨m, run5, -, -⟩ := Zlib.Deflate.Universal.Call.call_noprogress inv2 buf2 hpend hr hao2
            (Or.inr ⟨hfin, hai2 ▸ hai⟩)
          have e := run5.symm.trans run3
          simp only [Except.ok.injEq, Prod.mk.injEq] at e
          obtain ⟨-, e⟩ := e
          rw [← e] at get3
          have g : (gzStrm i).get (ZStreamRef.put (Zlib.Deflate.Spec.setD (putGz h i s2) k
              { dk with last_flush := flush }) (gzStrm i) { s2.strm with msg := m }) =
              some { s2.strm with msg := m } := by
            simp [ZStreamRef.get, ZStreamRef.put, gzStrm, Zlib.Deflate.Spec.setD, putGz]
          rw [g] at get3
          simp only [Option.some.injEq] at get3
          exact hne (by rw [← get3])
    · rw [muH, if_neg hsil]
      by_cases h3 : s3.strm.avail_out = 0
      · -- the call filled the output buffer
        have nsil : SilentP Quiet flush i after → False := by
          rintro ⟨s', hs', hao, -⟩
          rw [hs3] at hs'
          cases hs'
          exact hao h3
        rw [muA nsil]
        have h3' : s3.strm.avail_out.toNat = 0 := by rw [h3]; rfl
        rw [if_pos h3']
        by_cases h0 : s.strm.avail_out.toNat = 0
        · rw [if_pos h0]
          have hao2 : s2.strm.avail_out = s.size := hreset (UInt32.toNat_inj.mp (by rw [h0]; rfl))
          have room : 8 ≤ s2.strm.avail_out.toNat := by rw [hao2]; exact hsize8.1
          have hΦ := keep4.1
          by_cases hz : s2.strm.avail_in = 0
          · have lt := c1 flush (putGz h i s2) (gzStrm i) s2.strm rc after s3.strm hf.1 hf.2 reach2 buf2 act2
              get2 nn2 hz room exec get3 h3
            have hz' : s2.strm.avail_in.toNat = 0 := by rw [hz]; rfl
            have hs0 : s.strm.avail_in.toNat = 0 := by rw [← hai2]; exact hz'
            omega
          · have lt := c1' flush (putGz h i s2) (gzStrm i) s2.strm rc after s3.strm hf.1 hf.2 reach2 buf2 act2
              get2 nn2 hz room exec get3 h3
            rw [hai2] at lt
            omega
        · rw [if_neg h0]
          have := psi3
          unfold PsiP at this
          rw [recIn_of hs3] at this
          omega
      · -- the call ended with room: the next call is silent
        have sil : SilentP Quiet flush i after := by
          refine ⟨s3, hs3, h3, ?_⟩
          by_cases hz : s2.strm.avail_in = 0
          · have q := c2 flush (putGz h i s2) (gzStrm i) s2.strm rc after s3.strm hf.1 hf.2 reach2 buf2 act2 get2
              nn2 hz hao2 exec get3 h3
            have : s3.strm.avail_in.toNat = 0 := by rw [hz] at ai3'; simpa using ai3'
            exact Or.inl ⟨UInt32.toNat_inj.mp (by rw [this]; rfl), q⟩
          · by_cases hfin : d.status = FINISH_STATE
            · obtain ⟨e, d', hd', hfin', hpend⟩ := c2f flush (putGz h i s2) (gzStrm i) s2.strm ds d rc after
                s3.strm hf.1 hf.2 reach2 buf2 act2 get2 zst hsd hfin nn2 hz hao2 exec hrc get3 h3
              exact Or.inr ⟨by rw [e]; exact hz, ds, d', by rw [st3]; exact zst, hd', hfin', hpend⟩
            · obtain ⟨e, q⟩ := c2' flush (putGz h i s2) (gzStrm i) s2.strm ds d rc after s3.strm hf.1 hf.2
                reach2 buf2 act2 get2 zst hsd hfin nn2 hz hao2 exec hrc get3 h3
              exact Or.inl ⟨e, q⟩
        rw [muS sil]
        split <;> omega
  · exact ⟨l', fs', h', run, gfs, gk, Or.inl ⟨hres, gp⟩⟩

theorem compCond_run (l : Zlib.Gzwrite.CompLoop) (fs : Fs) (h : Heap) :
    compCond l fs h = .ok (((l.res.isNone && l.«have» != 0, l), fs), h) := rfl

/-- **The deflate loop** `do { ... } while (have)`: it returns, with the state of the loop or the `gz_error`
report. -/
theorem comp_loop (err : GzErrorSpec) (errOwn : GzErrorOwn) (hq : DeflateQuietIn) {flush : Int32}
    (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) {h0 h : Heap} {s0 s : GzState} {fs0 fs : Fs}
    (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b) (S : St i src h s) (K : Kept i h0 s0 h s)
    (hfs : FileSystem fs) (hk : FdsKept fs0 fs) (l0 : Zlib.Gzwrite.CompLoop) (hl0 : l0.res = none) :
    ∃ l fs' h', gdoWhile (compBody i flush) compCond l0 fs h = .ok ((l, fs'), h') ∧ FileSystem fs' ∧
      FdsKept fs0 fs' ∧
      ((l.res = none ∧ ∃ s', St i src h' s' ∧ Kept i h0 s0 h' s' ∧ (flush = Z_NO_FLUSH → s'.strm.avail_in = 0)) ∨
        (l.res = some (-1) ∧ GzPost h0 i s0 [] fs' h' (WeakS src s0))) := by
  obtain ⟨Φ, Quiet, hc⟩ := quiet_clauses hq
  let J : Zlib.Gzwrite.CompLoop → Fs → Heap → Prop := fun l fs h =>
    l.res = none ∧ FileSystem fs ∧ FdsKept fs0 fs ∧ ∃ s, St i src h s ∧ Kept i h0 s0 h s
  let P : Zlib.Gzwrite.CompLoop → Fs → Heap → Prop := fun l fs h => FileSystem fs ∧ FdsKept fs0 fs ∧
    ((l.res = none ∧ ∃ s', St i src h s' ∧ Kept i h0 s0 h s' ∧ (flush = Z_NO_FLUSH → s'.strm.avail_in = 0)) ∨
      (l.res = some (-1) ∧ GzPost h0 i s0 [] fs h (WeakS src s0)))
  let μ : Zlib.Gzwrite.CompLoop → Fs → Heap → Nat := fun _ _ h => muP Φ Quiet flush i h
  have step : ∀ x fs h, J x fs h → ∃ y fs1 h1, compBody i flush x fs h = .ok ((y, fs1), h1) ∧
      ∃ c z fs2 h2, compCond y fs1 h1 = .ok (((c, z), fs2), h2) ∧
        (c = true → J z fs2 h2 ∧ μ z fs2 h2 < μ x fs h) ∧ (c = false → P z fs2 h2) := by
    rintro x fs h ⟨hl, gfs, gk, s, Ss, Ks⟩
    obtain ⟨y, fs1, h1, run, gfs1, gk1, res⟩ := comp_trip err errOwn hc hf own0 hl Ss Ks gfs gk
    refine ⟨y, fs1, h1, run, _, y, fs1, h1, compCond_run y fs1 h1, fun e => ?_, fun e => ?_⟩
    · rcases res with ⟨hr, -⟩ | ⟨hr, s1, S1, K1, -, hlt⟩
      · rw [hr] at e; simp at e
      · have hy : y.«have» ≠ 0 := by
          rw [hr] at e; simpa using e
        exact ⟨⟨hr, gfs1, gk1, s1, S1, K1⟩, hlt hy⟩
    · rcases res with ⟨hr, gp⟩ | ⟨hr, s1, S1, K1, hin, -⟩
      · exact ⟨gfs1, gk1, Or.inr ⟨hr, gp⟩⟩
      · have hy : y.«have» = 0 := by
          rw [hr] at e; simpa using e
        exact ⟨gfs1, gk1, Or.inl ⟨hr, s1, S1, K1, hin hy⟩⟩
  obtain ⟨l, fs', h', run, post⟩ := gdoWhile_go_spec' (compBody i flush) compCond J P μ step C.fuel l0 fs h
    ⟨hl0, hfs, hk, s, S, K⟩ (muP_lt hc hf S)
  exact ⟨l, fs', h', run, post.1, post.2.1, post.2.2⟩


/-! ## `gz_comp` -/

/-- What `gz_comp` does after the reset: the deflate loop and its end. -/
def compTail (i : Nat) (flush : Int32) : G Int32 := do
  let l ← gdoWhile (compBody i flush) compCond { ret := Z_OK, «have» := 0, res := none }
  if let some r := l.res then return r
  if flush == Z_FINISH then updS (gzSt i) fun s => { s with reset := 1 }
  return 0

theorem gz_comp_source2 (flush : Int32) :
    Zlib.Gzwrite.gz_comp (gzSt i) flush = (do
      if (← ldS (gzSt i)).size == 0 then
        if (← Zlib.Gzwrite.gz_init (gzSt i)) == -1 then return -1
      if (← ldS (gzSt i)).direct != 0 then
        let r ← gwhile (directCond i) (directBody i) none
        return r.getD 0
      if (← ldS (gzSt i)).reset != 0 then
        let z ← ldZ (strmOf (gzSt i))
        if z.avail_in == 0 && flush == Z_NO_FLUSH then return 0
        let _ ← Zlib.Deflate.deflateReset (strmOf (gzSt i))
        updS (gzSt i) fun s => { s with reset := 0 }
      compTail i flush) := rfl

theorem GzPost.mono {h : Heap} {s : GzState} {fs : Fs} {after : Heap} {P Q : Heap → Nat → GzState → Prop}
    (p : GzPost h i s [] fs after P) (hpq : ∀ h' i' s', P h' i' s' → Q h' i' s') : GzPost h i s [] fs after Q := by
  obtain ⟨hfs, s', hp, rest⟩ := p
  exact ⟨hfs, s', hpq _ _ _ hp, rest⟩

/-- The result predicate of `gz_comp`. -/
def CompPost (i : Nat) (src : Region) (flush : Int32) (h : Heap) (s : GzState) (fs : Fs) (r : Int32) (fs' : Fs)
    (after : Heap) : Prop :=
  (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
    GzPost h i s [] fs' after (fun h' i' s' =>
      (if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) ∧ CompShape s s' ∧
        (r = 0 → flush = Z_NO_FLUSH → s'.strm.avail_in = 0) ∧ (r = 0 → h'.libcErrorBorrow = h.libcErrorBorrow))

theorem compPost_ok {h0 h : Heap} {s0 s : GzState} {fs0 fs : Fs} (K : Kept i h0 s0 h s)
    (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b) (hfs : FileSystem fs) (hk : FdsKept fs0 fs)
    (U : GzInvUpToInput h i s src) {flush : Int32} (hin : flush = Z_NO_FLUSH → s.strm.avail_in = 0) :
    CompPost i src flush h0 s0 fs0 0 fs h :=
  ⟨Or.inl rfl, hk, post_of_kept K own0 hfs ⟨by simp only [if_true]; exact U, CompShape.of_same K.2.2.2.1 K.2.2.2.2.1,
    fun _ => hin, fun _ => K.2.2.2.2.2⟩⟩

theorem compPost_err {h0 h : Heap} {s0 : GzState} {fs0 fs : Fs} (hk : FdsKept fs0 fs)
    (p : GzPost h0 i s0 [] fs h (WeakS src s0))
    {flush : Int32} : CompPost i src flush h0 s0 fs0 (-1) fs h :=
  ⟨Or.inr rfl, hk, GzPost.mono p fun h' i' s' w => by
    exact ⟨by rw [if_neg (by decide)]; exact w.1, w.2, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩⟩

theorem comp_tail (err : GzErrorSpec) (errOwn : GzErrorOwn) (hq : DeflateQuietIn) {flush : Int32}
    (hf : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) {h0 h : Heap} {s0 s : GzState} {fs0 fs : Fs}
    (own0 : ∀ b, GzOwned h0 i s0 b → h0.live b) (S : St i src h s) (K : Kept i h0 s0 h s)
    (hfs : FileSystem fs) (hk : FdsKept fs0 fs) :
    ∃ r fs' h', compTail i flush fs h = .ok ((r, fs'), h') ∧ CompPost i src flush h0 s0 fs0 r fs' h' := by
  obtain ⟨l, fs', h', run, gfs, gk, res⟩ := comp_loop err errOwn hq hf own0 S K hfs hk { ret := Z_OK, «have» := 0, res := none } rfl
  unfold compTail
  simp only [cbind_app, run]
  rcases res with ⟨hr, s', S', K', hin⟩ | ⟨hr, gp⟩
  · simp only [hr]
    by_cases hfin : flush = Z_FINISH
    · have hu : updS (gzSt i) (fun s => { s with reset := 1 }) h' = .ok ((), putGz h' i { s' with reset := 1 }) := by
        rw [← putGz_self S'.up.1]; rw [updS_put]; rw [putGz_putGz]
      have F' := facts_of S'.up S'.direct S'.size
      obtain ⟨S2, fr, hl, ho⟩ := st_record (s' := { s' with reset := 1 }) S'
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by unfold BufOnly; rfl) (Or.inr rfl)
        F'.out S'.up.2.2.2.1
      simp only [hfin, beq_self_eq_true, ↓reduceIte, cbind_app, clift_app, cpure_app, liftM, monadLift,
        MonadLift.monadLift, MonadLiftT.monadLift, hu]
      exact ⟨_, _, _, rfl, compPost_ok (K'.step fr hl ho ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl⟩ (InTrack.of_in rfl rfl) rfl) own0 gfs gk S2.up (fun e => absurd e (by decide))⟩
    · have hfin' : (flush == Z_FINISH) = false := by simpa using hfin
      simp only [hfin', Bool.false_eq_true, ↓reduceIte, cbind_app, cpure_app]
      exact ⟨_, _, _, rfl, compPost_ok K' own0 gfs gk S'.up hin⟩
  · simp only [hr]
    exact ⟨_, _, _, rfl, compPost_err gk gp⟩

/-- **`gz_comp` is safe, and keeps the shape of the record**, given the facts of `gz_error` and `DeflateQuietIn`: the
statement of `gz_comp_safe` of `gz.skeleton-write`, strengthened by `CompShape` (the buffers, sizes, mode,
position, skip and descriptor are kept, also on failure, and the input only advances by what was consumed: `InTrack`), and by the consumption of the input: a run with
`Z_NO_FLUSH` that returns 0 leaves no pending input (clause (2') of `DeflateQuietIn`; a finished stream refuses
`Z_NO_FLUSH` with `Z_STREAM_ERROR`). `gz_zero` and `gz_write` need the shape to re-establish W4 after a failed
`gz_comp`, and the consumption for the termination of their loops. A run that returns 0 keeps the `strerror`
borrow, so a caller region that is a borrowed view stays readable (the small path of `gz_write`). -/
theorem gz_comp_safe_shape (err : GzErrorSpec) (errOwn : GzErrorOwn) (hq : DeflateQuietIn)
    (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        (if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) ∧ CompShape s s' ∧
          (r = 0 → flush = Z_NO_FLUSH → s'.strm.avail_in = 0) ∧ (r = 0 → h'.libcErrorBorrow = h.libcErrorBorrow)) := by
  apply runSafe_of_ok (P := CompPost i src flush h s fs)
  unfold Ok
  have hs := inv.1
  have own0 : ∀ b, GzOwned h i s b → h.live b := fun b hb =>
    (live_putGz hs _ b).1 (inv.2.1.common.live b ((owned_clearIn hs b).2 hb))
  have K0 : Kept i h s h s := Kept.refl h s
  have hk0 : FdsKept fs fs := fun _ => Iff.rfl
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run hs
  have hz0 : (s.size == 0) = false := by simpa using hsz
  rw [gz_comp_source2]
  by_cases hd : s.direct = 0
  · have S : St i src h s := ⟨inv, hd, hsz⟩
    have hd' : (s.direct != 0) = false := by simp [hd]
    by_cases hr : s.reset = 0
    · have hr' : (s.reset != 0) = false := by simp [hr]
      obtain ⟨r, fs', h', run, post⟩ := comp_tail err errOwn hq hflush own0 S K0 hfs hk0
      simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
        hS, hz0, hd', hr', Bool.false_eq_true, ↓reduceIte, run]
      exact ⟨_, _, _, rfl, post⟩
    · have hr' : (s.reset != 0) = true := by simpa using hr
      have hZ : ldZ (strmOf (gzSt i)) h = .ok (s.strm, h) := Zlib.Gzlib.Proofs.ldZ_run hs
      by_cases hq0 : (s.strm.avail_in == 0 && flush == Z_NO_FLUSH) = true
      · simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
          hS, hz0, hd', hr', Bool.false_eq_true, ↓reduceIte, hZ, hq0]
        exact ⟨_, _, _, rfl, compPost_ok K0 own0 hfs hk0 inv (fun _ => by
          simp only [Bool.and_eq_true, beq_iff_eq] at hq0; exact hq0.1)⟩
      · have hq0' : (s.strm.avail_in == 0 && flush == Z_NO_FLUSH) = false := by simpa using hq0
        obtain ⟨after, s', run, hs', S', frG, hlv, how, es', -, hai', hni', hbor'⟩ := reset_step S
        have run' : Zlib.Deflate.deflateReset (strmOf (gzSt i)) h = .ok (Z_OK, after) := by
          rw [show strmOf (gzSt i) = some (gzStrm i) from rfl]; exact run
        have K' : Kept i h s after s' := K0.step frG hlv how (by rw [es']; exact SameShape.refl _)
          (InTrack.of_in hni' hai') hbor'
        have hu : updS (gzSt i) (fun s => { s with reset := 0 }) after =
            .ok ((), putGz after i { s' with reset := 0 }) := by
          rw [← putGz_self hs']; rw [updS_put]; rw [putGz_putGz]
        have F' := facts_of S'.up S'.direct S'.size
        obtain ⟨S2, fr, hl, ho⟩ := st_record (s' := { s' with reset := 0 }) S'
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by unfold BufOnly; rfl) (Or.inl rfl)
          F'.out S'.up.2.2.2.1
        have K2 := K'.step fr hl ho ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (InTrack.of_in rfl rfl) rfl
        obtain ⟨r, fs', h', run2, post⟩ := comp_tail err errOwn hq hflush own0 S2 K2 hfs hk0
        simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
          hS, hz0, hd', hr', Bool.false_eq_true, ↓reduceIte, hZ, hq0', run', hu, run2]
        exact ⟨_, _, _, rfl, post⟩
  · have hd' : (s.direct != 0) = true := by simpa using hd
    obtain ⟨z, fs', h', run, gfs, gk, res⟩ := direct_loop err errOwn inv K0 own0 hd hsz hfs hk0
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app,
      hS, hz0, hd', Bool.false_eq_true, ↓reduceIte, run]
    rcases res with ⟨rfl, s', U', K', hin⟩ | ⟨rfl, gp⟩
    · exact ⟨_, _, _, rfl, compPost_ok K' own0 gfs gk U' (fun _ => hin)⟩
    · exact ⟨_, _, _, rfl, compPost_err gk gp⟩

/-- **`gz_comp` is safe**, given the facts of `gz_error` and `DeflateQuietIn`: the statement of `gz_comp_safe` of
`gz.skeleton-write`. -/
theorem gz_comp_safe_of (err : GzErrorSpec) (errOwn : GzErrorOwn) (hq : DeflateQuietIn)
    (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) := by
  obtain ⟨h1, h2, h3⟩ := gz_comp_safe_shape err errOwn hq i flush src h fs s inv hfs hsz hflush
  exact ⟨h1, h2, fun r fs' after hr => let ⟨a, b, c⟩ := h3 r fs' after hr; ⟨a, b, GzPost.mono c fun _ _ _ x => x.1⟩⟩

/-- **`gz_comp` is safe and keeps the shape of the record, given the facts of `gz_error`**: `DeflateQuietIn` is
proved (`deflateQuietIn_holds`). -/
theorem gz_comp_safe_shape_of' (err : GzErrorSpec) (errOwn : GzErrorOwn)
    (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        (if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) ∧ CompShape s s' ∧
          (r = 0 → flush = Z_NO_FLUSH → s'.strm.avail_in = 0) ∧ (r = 0 → h'.libcErrorBorrow = h.libcErrorBorrow)) :=
  gz_comp_safe_shape err errOwn deflateQuietIn_holds i flush src h fs s inv hfs hsz hflush

/-- **`gz_comp` is safe, given the facts of `gz_error`**: `DeflateQuietIn` is proved (`deflateQuietIn_holds`). -/
theorem gz_comp_safe_of' (err : GzErrorSpec) (errOwn : GzErrorOwn)
    (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) :=
  gz_comp_safe_of err errOwn deflateQuietIn_holds i flush src h fs s inv hfs hsz hflush

end codec

end ZlibF.Spec.Public.GzSkeleton
