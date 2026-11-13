import ZlibF.Proof.«public-uncompress-heap»
import ZlibF.Proof.«public-uncompress-format»
import ZlibF.Proof.«public-uncompress-loop-rule»
import ZlibF.Proof.«public-uncompress-ranges»
import ZlibF.Proof.«inflate.c.reachable»

/-!
# uncompr.c: one iteration of the decompression loop

The loop body of `uncompress2_z` refills an empty output and an empty input
from the remaining lengths, then calls `inflate`. `BodyOK` says what a body does:
each refill is the remaining length capped at `2^32 - 1` (`refill`, stated as a
minimum, not as the code's expression), then one `inflate` call. `CondOK` says
the loop continues exactly while `err == Z_OK`. The proofs of the translation's
own body and condition are `body_ok` and `cond_ok`: the program is never restated.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Uncompr
open Zlib.Inflate (inflate)
set_option autoImplicit false

/-- A refill: the remaining length capped at `2^32 - 1`. -/
def refill (x : UInt64) : UInt32 := (min x.toNat 4294967295).toUInt32

theorem refill_toNat (x : UInt64) : (refill x).toNat = min x.toNat 4294967295 := by
  unfold refill
  simp
  omega

/-- The code's refill `left > (z_size_t)max ? max : (uInt)left` is the capped length. -/
theorem refill_code (x : UInt64) :
    (if x > (0xFFFFFFFF : UInt32).toUInt64 then (0xFFFFFFFF : UInt32) else x.toUInt32) = refill x := by
  apply UInt32.toNat_inj.mp
  rw [refill_toNat]
  by_cases big : x > (0xFFFFFFFF : UInt32).toUInt64
  · rw [if_pos big]
    have : (4294967295 : Nat) < x.toNat := by simpa [UInt64.lt_iff_toNat_lt] using big
    simp; omega
  · rw [if_neg big]
    have : x.toNat ≤ 4294967295 := by simp [UInt64.lt_iff_toNat_lt] at big; omega
    simp; omega

/-- The stream after the refills of one iteration. -/
def refilled (z : ZStream) (l : UncLoop) : ZStream :=
  { z with
    avail_out := if z.avail_out = 0 then refill l.left else z.avail_out
    avail_in := if z.avail_in = 0 then refill l.len else z.avail_in }

/-- The remaining lengths after the refills of one iteration. -/
def refilledLoop (z : ZStream) (l : UncLoop) : UncLoop :=
  { l with
    left := if z.avail_out = 0 then l.left - (refill l.left).toUInt64 else l.left
    len := if z.avail_in = 0 then l.len - (refill l.len).toUInt64 else l.len }

/-- The refill in the form `simp` leaves it. -/
theorem refill_code' (x : UInt64) :
    (if (4294967295 : UInt64) < x then (4294967295 : UInt32) else x.toUInt32) = refill x :=
  refill_code x

/-- What one iteration of the loop does on the stream `r`: the refills, then one
`inflate` call whose result is the new `err`. -/
def BodyOK (r : ZStreamRef) (body : UncLoop → M UncLoop) : Prop :=
  ∀ l H z, r.get H = some z →
    body l H = (do let e ← inflate (some r) Z_NO_FLUSH; pure { refilledLoop z l with err := e } : M UncLoop)
      (r.put H (refilled z l))

/-- The loop continues exactly while `err == Z_OK`. -/
def CondOK (cond : UncLoop → M (Bool × UncLoop)) : Prop :=
  ∀ l H, cond l H = .ok ((l.err == Z_OK, l), H)

theorem put_self_tab {H : Heap} {k : Nat} {z : ZStream} (hz : (ZStreamRef.tab k).get H = some z) :
    (ZStreamRef.tab k).put H z = H := by
  simp only [ZStreamRef.get] at hz; simp [ZStreamRef.put, hz, upd_self _ _ _ hz]

/-- Proves `BodyOK (.tab k) body` for the loop body of the translation of
`uncompress2_z`, by running it. -/
macro "body_ok" : tactic => `(tactic| (
  intro l H z hz
  have self := put_self_tab hz
  by_cases ho : z.avail_out = 0 <;> by_cases hi : z.avail_in = 0 <;>
    simp [ldZ, updZ, ldZStream, stZStream, hz, ZStreamRef.isRo, ho, hi, ZStreamRef.get_put_same hz,
      ZStreamRef.put_put, refilled, refilledLoop, refill_code, refill_code', self] <;>
    rfl))

/-- Fixed data of one run of `uncompress2_z`: the caller heap, the source pointer,
the output pointer after the null substitution, the source bytes and both lengths. -/
structure Env where
  h₀ : Heap
  source : BPtr
  out0 : BPtr
  src : List UInt8
  n : Nat
  cap : Nat

namespace Env
/-- The block of the automatic `z_stream`. -/
def k (e : Env) : Nat := e.h₀.nextBlk
/-- The automatic `z_stream`. -/
def r (e : Env) : ZStreamRef := .tab e.h₀.nextBlk
end Env

/-- What the accepted caller arguments give for the whole run. -/
structure EnvOK (e : Env) : Prop where
  fresh : Fresh e.h₀
  srcBytes : Bytes e.h₀ e.source e.n e.src
  srcLen : e.src.length = e.n
  outW : (e.out0 = .ref (.blk (e.k + 1)) 0 ∧ e.cap = 0) ∨ Writable e.h₀ e.out0 e.cap
  outNotNull : e.out0 ≠ .null
  sep : Separate e.source e.n e.out0 e.cap
  nBound : e.n < 2 ^ 63
  capBound : e.cap < 2 ^ 63

/-- The safety state of the run before an iteration (or after a continuing one):
everything but the format fact `noOver`. -/
structure SafeState (e : Env) (l : UncLoop) (H : Heap) (log : DataLog) (i : Nat) (z : ZStream)
    (s : InflateState) : Prop where
  trace : InflateProtocolTrace 15 e.r H log false
  single : log.singleDictionary = true
  dict : log.dictionary = []
  reach : StreamReachable .inflate H e.r
  fit : ZlibF.PlatformMemory.ByteObjectsFit H
  good : Zlib.Inflate.Spec.Good H e.r i z s
  alloc : Zlib.Inflate.Spec.DefAlloc z
  noSync : s.mode ≠ SYNC
  noMem : s.mode ≠ MEM
  head : s.head = none
  globals : LibraryGlobals H
  inTake : log.input = e.src.take log.input.length
  inCount : log.input.length + z.avail_in.toNat + l.len.toNat = e.n
  nextIn : z.next_in = advance e.source log.input.length
  outCount : log.output.length + z.avail_out.toNat + l.left.toNat = e.cap
  nextOut : z.next_out = advance e.out0 log.output.length
  agree : Agree e.h₀.live (writeOut e.h₀ e.out0 log.output) H
  notOwned : ∀ b, e.h₀.live b ∨ b = e.k ∨ b = e.k + 1 → ¬ InflateOwned i s b
  liveOnly : ∀ b, H.live b → e.h₀.live b ∨ b = e.k ∨ b = e.k + 1 ∨ InflateOwned i s b
  reservedBytes : H.bytes (e.k + 1) = some (reservedBytes e.h₀)
  reservedRo : H.ro (e.k + 1) = false
  nalloc : e.h₀.nalloc ≤ H.nalloc

/-- No complete stream at the start of the source has been read to its end. A
format fact: only the functional proof carries it. -/
def NoOver (e : Env) (log : DataLog) : Prop :=
  ∀ m o, m ≤ e.src.length → Zlib.Decodes [] (e.src.take m) o →
    log.input <+: e.src.take m ∧ log.input ≠ e.src.take m

/-- The state of the run with the format fact of the functional proof. -/
structure State (e : Env) (l : UncLoop) (H : Heap) (log : DataLog) (i : Nat) (z : ZStream)
    (s : InflateState) : Prop extends SafeState e l H log i z s where
  noOver : NoOver e log

/-- Every reachable inflate stream has a decoder with the default allocators
(`reachable_invariant_kind`, no premise). -/
theorem reach_invariant {H : Heap} {r : ZStreamRef} (reach : StreamReachable .inflate H r) :
    ∃ i z s, Zlib.Inflate.Spec.Good H r i z s ∧ Zlib.Inflate.Spec.DefAlloc z := by
  obtain ⟨i, z, s, inv, -⟩ := reachable_invariant_kind reach rfl
  exact ⟨i, z, s, inv.good, inv.alloc⟩

/-- The remaining work: unread source and unfilled room. -/
def measure (e : Env) (l : UncLoop) (H : Heap) : Nat :=
  match e.r.get H with
  | some z => z.avail_in.toNat + l.len.toNat + z.avail_out.toNat + l.left.toNat
  | none => 0

theorem refill_le (x : UInt64) : (refill x).toUInt64.toNat ≤ x.toNat ∧ ((refill x) = 0 ↔ x = 0) := by
  rw [← refill_code]
  by_cases big : x > (0xFFFFFFFF : UInt32).toUInt64
  · simp only [big, ite_true]
    have : (4294967295 : Nat) < x.toNat := by
      simpa [UInt64.lt_iff_toNat_lt] using big
    refine ⟨by simp; omega, ?_⟩
    constructor
    · intro e; cases e
    · intro e; rw [e] at this; simp at this
  · simp only [big, ite_false]
    have small : x.toNat ≤ 4294967295 := by
      simp [UInt64.lt_iff_toNat_lt] at big; omega
    have rt : x.toUInt32.toUInt64.toNat = x.toNat := by
      simp [UInt64.toNat_toUInt32]; omega
    refine ⟨by rw [rt]; exact Nat.le_refl _, ?_⟩
    constructor
    · intro e
      apply UInt64.toNat_inj.mp
      have := congrArg (fun y : UInt32 => y.toUInt64.toNat) e
      simp only [rt] at this
      simpa using this
    · intro e; subst e; rfl

/-- The heap determines the decoder. -/
theorem good_unique {H : Heap} {r : ZStreamRef} {i i' : Nat} {z z' : ZStream} {s s' : InflateState}
    (g : Zlib.Inflate.Spec.Good H r i z s) (g' : Zlib.Inflate.Spec.Good H r i' z' s') :
    i = i' ∧ z = z' ∧ s = s' := by
  have ez : z = z' := Option.some.inj (g.live.hz.symm.trans g'.live.hz)
  subst ez
  have ei : i = i' := by
    have both := g.live.zst.symm.trans g'.live.zst
    cases both
    rfl
  subst ei
  exact ⟨rfl, rfl, Option.some.inj (g.live.hs.symm.trans g'.live.hs)⟩

/-- A stream record write at a live table entry. -/
theorem put_tab_eq {H : Heap} {k : Nat} {z v : ZStream} (hz : H.streams k = some z) :
    (ZStreamRef.tab k).put H v = { H with streams := upd H.streams k (some v) } := by
  simp [ZStreamRef.put, hz]

theorem put_tab_same {H : Heap} {k : Nat} {z : ZStream} (hz : H.streams k = some z) (v : ZStream) (b : Nat) :
    SameAt H { H with streams := upd H.streams k (some v) } b ∨ b = k := by
  by_cases e : b = k
  · exact Or.inr e
  · left; exact ⟨rfl, rfl, by simp [upd_ne _ _ _ _ e], rfl, rfl, rfl, rfl, rfl⟩

theorem put_tab_live {H : Heap} {k : Nat} {z : ZStream} (hz : H.streams k = some z) (v : ZStream) (b : Nat) :
    ({ H with streams := upd H.streams k (some v) } : Heap).live b ↔ H.live b := by
  simp only [Heap.live, upd_apply]
  by_cases e : b = k
  · subst e; simp [hz]
  · simp [e]

theorem put_tab_get {H : Heap} {k : Nat} (v : ZStream) (rr : BRef) :
    Space.get ({ H with streams := upd H.streams k (some v) } : Heap) rr = Space.get H rr ∧
      Space.ro ({ H with streams := upd H.streams k (some v) } : Heap) rr = Space.ro H rr := by
  cases rr <;> simp [Space.get, Space.ro, staticStringBytes]

theorem fit_put_tab {H : Heap} {k : Nat} (v : ZStream) (fit : ZlibF.PlatformMemory.ByteObjectsFit H) :
    ZlibF.PlatformMemory.ByteObjectsFit { H with streams := upd H.streams k (some v) } := by
  intro rr a g
  rw [(put_tab_get v rr).1] at g
  exact fit rr a g

theorem uniq_put_tab {H : Heap} {k : Nat} {z : ZStream} (hz : H.streams k = some z) (v : ZStream)
    (u : Zlib.Inflate.Spec.Uniq H) : Zlib.Inflate.Spec.Uniq { H with streams := upd H.streams k (some v) } := by
  intro b
  have ub := u b
  simp only [upd_apply]
  by_cases e : b = k
  · subst e; simpa [hz] using ub
  · simpa [e] using ub

theorem fresh_put_tab {H : Heap} {k : Nat} {z : ZStream} (hz : H.streams k = some z) (v : ZStream)
    (f : Fresh H) : Fresh { H with streams := upd H.streams k (some v) } := by
  intro b hb
  rw [put_tab_live hz]
  exact f b hb

/-- A rebuffer of the automatic stream: only its buffer fields change. -/
theorem rebuffer_put {e : Env} {H : Heap} {i : Nat} {z z₁ : ZStream} {s : InflateState}
    (good : Zlib.Inflate.Spec.Good H e.r i z s) (globals : LibraryGlobals H)
    (notOwned : ¬ InflateOwned i s e.k)
    (form : z₁ = { z with next_in := z₁.next_in, avail_in := z₁.avail_in, next_out := z₁.next_out, avail_out := z₁.avail_out }) :
    Rebuffer H (e.r.put H z₁) e.r := by
  simp only [Env.r, Env.k] at *
  have hz : H.streams e.h₀.nextBlk = some z := good.live.hz
  rw [put_tab_eq hz]
  refine ⟨fresh_put_tab hz z₁ good.fresh, uniq_put_tab hz z₁ good.uniq, globals, ?_, z,
    z₁, good.live.hz, by simp [ZStreamRef.get], form⟩
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b live changed
  rcases put_tab_same hz z₁ b with same | rfl
  · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := same
    exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
  · exfalso
    apply changed
    rintro ⟨z', hz', hown⟩
    rcases hown with ⟨i', s', hst, his, own⟩ | ⟨i', s', hst, -, -⟩
    · have ez : z' = z := Option.some.inj (hz'.symm.trans good.live.hz)
      subst ez
      rw [good.live.zst] at hst
      cases hst
      rw [good.live.hs] at his
      cases his
      exact notOwned own
    · have ez : z' = z := Option.some.inj (hz'.symm.trans good.live.hz)
      subst ez
      rw [good.live.zst] at hst
      cases hst

theorem refill_sum (a : UInt32) (x : UInt64) :
    (if a = 0 then refill x else a).toNat + (if a = 0 then x - (refill x).toUInt64 else x).toNat =
      a.toNat + x.toNat := by
  by_cases h : a = 0
  · subst h
    simp only [ite_true, UInt32.toNat_zero, Nat.zero_add]
    have le := (refill_le x).1
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact le)]
    have : (refill x).toUInt64.toNat = (refill x).toNat := by simp
    omega
  · simp [h]

theorem refilled_avail_in (z : ZStream) (l : UncLoop) :
    (refilled z l).avail_in.toNat + (refilledLoop z l).len.toNat = z.avail_in.toNat + l.len.toNat :=
  refill_sum z.avail_in l.len

theorem refilled_avail_out (z : ZStream) (l : UncLoop) :
    (refilled z l).avail_out.toNat + (refilledLoop z l).left.toNat = z.avail_out.toNat + l.left.toNat :=
  refill_sum z.avail_out l.left

/-- The refills move room and source from the remaining lengths to the stream. -/
theorem SafeState.refill {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat}
    {z : ZStream} {s : InflateState} (ok : EnvOK e) (st : SafeState e l H log i z s) :
    SafeState e (refilledLoop z l) (e.r.put H (refilled z l)) log i (refilled z l) s := by
  have hz : H.streams e.k = some z := st.good.live.hz
  have H1eq : e.r.put H (refilled z l) = { H with streams := upd H.streams e.k (some (refilled z l)) } :=
    put_tab_eq (v := refilled z l) hz
  have rebuf := rebuffer_put st.good st.globals (st.notOwned e.k (Or.inr (Or.inl rfl)))
    (z₁ := refilled z l) (by simp [refilled])
  have fit1 : ZlibF.PlatformMemory.ByteObjectsFit (e.r.put H (refilled z l)) := by
    rw [H1eq]; exact fit_put_tab _ st.fit
  have reach1 := StreamReachable.rebuffer st.reach rebuf (fun _ => fit1)
  obtain ⟨i', z', s', g', d'⟩ := reach_invariant reach1
  have hz1 : e.r.get (e.r.put H (refilled z l)) = some (refilled z l) :=
    ZStreamRef.get_put_same st.good.live.hz _
  have ez : z' = refilled z l := Option.some.inj (g'.live.hz.symm.trans hz1)
  subst ez
  have ei : i' = i := by
    have := g'.live.zst
    simp only [refilled] at this
    rw [st.good.live.zst] at this
    cases this; rfl
  subst ei
  have es : s' = s := by
    have := g'.live.hs
    rw [H1eq] at this
    exact Option.some.inj (this.symm.trans st.good.live.hs)
  subst es
  have k0 : ¬ e.h₀.live e.k := ok.fresh e.k (Nat.le_refl _)
  have sameOut : ∀ b, b ≠ e.k → SameAt H (e.r.put H (refilled z l)) b := by
    intro b ne
    rw [H1eq]
    rcases put_tab_same hz (refilled z l) b with x | x
    · exact x
    · exact absurd x ne
  refine
    { trace := InflateProtocolTrace.caller st.trace rebuf fit1
      single := st.single
      dict := st.dict
      reach := reach1
      fit := fit1
      good := g'
      alloc := by simpa [refilled, Zlib.Inflate.Spec.DefAlloc] using st.alloc
      noSync := st.noSync
      noMem := st.noMem
      head := st.head
      globals := by rw [H1eq]; exact st.globals
      inTake := st.inTake
      inCount := by have := refilled_avail_in z l; have := st.inCount; omega
      nextIn := by simpa [refilled] using st.nextIn
      outCount := by have := refilled_avail_out z l; have := st.outCount; omega
      nextOut := by simpa [refilled] using st.nextOut
      agree := ?_
      notOwned := st.notOwned
      liveOnly := ?_
      reservedBytes := by
        rw [H1eq]; simp only [Env.k] at *
        exact st.reservedBytes
      reservedRo := by rw [H1eq]; exact st.reservedRo
      nalloc := by rw [H1eq]; exact st.nalloc }
  · refine ⟨fun b live => (st.agree.blocks b live).trans (sameOut b (fun e' => k0 (e' ▸ live))), ?_, ?_, ?_, ?_⟩
    · rw [H1eq]; exact st.agree.static
    · rw [H1eq]; exact st.agree.allocOk
    · rw [H1eq]; exact st.agree.garbage
    · rw [H1eq]; exact st.agree.borrow
  · intro b live
    rw [H1eq, put_tab_live hz] at live
    exact st.liveOnly b live

/-- The refills keep the state with the format fact. -/
theorem State.refill {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat}
    {z : ZStream} {s : InflateState} (ok : EnvOK e) (st : State e l H log i z s) :
    State e (refilledLoop z l) (e.r.put H (refilled z l)) log i (refilled z l) s :=
  { toSafeState := st.toSafeState.refill ok, noOver := st.noOver }

end ZlibF.Spec.Public.Proofs.Uncompress
