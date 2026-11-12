import ZlibF.Proof.«public-compress-safe-init»
import ZlibF.Proof.«deflate.c.universal-history»

/-!
# compress.c: safety, the loop

The loop of `compress2_z` refills an empty output and an empty input from the remaining
lengths (each capped at `2^32 - 1`, `refill`), then calls `deflate` with `Z_NO_FLUSH` while
source remains and `Z_FINISH` after. `CState` is the state between iterations. One iteration
keeps it (`step`). The measure, the unread source plus the unfilled room, falls at every
`Z_OK` call: by `DeflateLoopFacts` for `Z_NO_FLUSH` (the call has input) and by the
`Z_FINISH` progress clause of `Goal.deflate` otherwise.
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Compress Zlib.Deflate
open ZlibF.Spec.Public.Proofs.Uncompress hiding measure
open Zlib.Deflate.Spec (DGood)
set_option autoImplicit false

/-- Fixed data of one accepted run of `compress2_z`. -/
structure CEnv where
  h₀ : Heap
  dest : BPtr
  source : BPtr
  src : List UInt8
  n : Nat
  cap : Nat

namespace CEnv
/-- The block of the automatic `z_stream`. -/
def k (e : CEnv) : Nat := e.h₀.nextBlk
/-- The automatic `z_stream`. -/
def r (e : CEnv) : ZStreamRef := .tab e.h₀.nextBlk
end CEnv

/-- What the accepted caller arguments give for the whole run. -/
structure COK (e : CEnv) : Prop where
  fresh : Fresh e.h₀
  globals : LibraryGlobals e.h₀
  srcBytes : Bytes e.h₀ e.source e.n e.src
  destW : Writable e.h₀ e.dest e.cap
  sep : Separate e.source e.n e.dest e.cap
  nBound : e.n < 2 ^ 63
  capBound : e.cap < 2 ^ 63

/-- The loop state of the translation: the last result, the remaining room and the
remaining source. -/
abbrev Loop := Int32 × UInt64 × UInt64

/-- The state of the run between iterations. -/
structure CState (e : CEnv) (st : Loop) (H : Heap) (out : List UInt8) (used : Nat) (z : ZStream)
    (s : DeflateState) : Prop where
  reach : StreamReachable .deflate H e.r
  good : DGood H e.r (e.k + 1) z s
  zfree : z.zfree = .fn "zcfree"
  gzhead : s.gzhead = none
  owned : ∀ b, DeflateOwned (e.k + 1) s b ↔ e.k + 1 ≤ b ∧ b < e.k + 6
  inCount : used + z.avail_in.toNat + st.2.2.toNat = e.n
  nextIn : z.next_in = advance e.source used
  outCount : out.length + z.avail_out.toNat + st.2.1.toNat = e.cap
  nextOut : z.next_out = advance e.dest out.length
  agree : Agree e.h₀.live (writeOut e.h₀ e.dest out) H
  liveOnly : ∀ b, H.live b → e.h₀.live b ∨ b = e.k ∨ (e.k + 1 ≤ b ∧ b < e.k + 6)
  nalloc : e.h₀.nalloc ≤ H.nalloc

/-- The remaining work: unread source and unfilled room. -/
def cmeasure (e : CEnv) (st : Loop) (H : Heap) : Nat :=
  match e.r.get H with
  | some z => z.avail_in.toNat + st.2.2.toNat + z.avail_out.toNat + st.2.1.toNat
  | none => 0

/-- The stream after the refills of one iteration. -/
def crefilled (z : ZStream) (st : Loop) : ZStream :=
  { z with
    avail_out := if z.avail_out = 0 then refill st.2.1 else z.avail_out
    avail_in := if z.avail_in = 0 then refill st.2.2 else z.avail_in }

/-- The remaining room and source after the refills of one iteration. -/
def crest (z : ZStream) (st : Loop) : UInt64 × UInt64 :=
  (if z.avail_out = 0 then st.2.1 - (refill st.2.1).toUInt64 else st.2.1,
   if z.avail_in = 0 then st.2.2 - (refill st.2.2).toUInt64 else st.2.2)

/-- `sourceLen ? Z_NO_FLUSH : Z_FINISH` after the refills. -/
def cflush (z : ZStream) (st : Loop) : Int32 :=
  if (crest z st).2 = 0 then Z_FINISH else Z_NO_FLUSH

/-- What one iteration of the loop does on the stream `r`: the refills, then one `deflate`
call whose result is the new first component. -/
def CBodyOK (r : ZStreamRef) (body : Loop → M Loop) : Prop :=
  ∀ st H z, r.get H = some z →
    body st H = (do let e ← deflate (some r) (cflush z st); pure (e, crest z st) : M Loop)
      (r.put H (crefilled z st))

/-- The loop continues exactly while the last result is `Z_OK`. -/
def CCondOK (cond : Loop → M (Bool × Loop)) : Prop :=
  ∀ st H, cond st H = .ok ((st.1 == Z_OK, st), H)

/-- Proves `CBodyOK (.tab k) body` for the loop body of the translation of `compress2_z`. -/
macro "cbody_ok" : tactic => `(tactic| (
  intro st H z hz
  have self := put_self_tab hz
  obtain ⟨e0, l0, s0⟩ := st
  by_cases ho : z.avail_out = 0 <;> by_cases hi : z.avail_in = 0 <;>
    simp [zrd, zwr, ldZStream, stZStream, hz, ZStreamRef.isRo, ho, hi, Zlib.Deflate.Proofs.ZStreamRef.get_put_same hz,
      Zlib.Deflate.Proofs.ZStreamRef.put_put, crefilled, crest, cflush, refill_code, refill_code', self] <;>
    rfl))

theorem crest_in (z : ZStream) (st : Loop) :
    (crefilled z st).avail_in.toNat + (crest z st).2.toNat = z.avail_in.toNat + st.2.2.toNat :=
  ZlibF.Spec.Public.Proofs.Uncompress.refill_sum z.avail_in st.2.2

theorem crest_out (z : ZStream) (st : Loop) :
    (crefilled z st).avail_out.toNat + (crest z st).1.toNat = z.avail_out.toNat + st.2.1.toNat :=
  ZlibF.Spec.Public.Proofs.Uncompress.refill_sum z.avail_out st.2.1

/-- A `Z_NO_FLUSH` call has input: source remains after the refill, so the input buffer is
not empty. -/
theorem noflush_input {z : ZStream} {st : Loop} (h : cflush z st = Z_NO_FLUSH) :
    (crefilled z st).avail_in ≠ 0 := by
  unfold cflush at h
  by_cases r0 : (crest z st).2 = 0
  · rw [if_pos r0] at h; exact absurd h (by decide)
  · simp only [crefilled]
    by_cases zi : z.avail_in = 0
    · rw [if_pos zi]
      intro e
      have x0 := (refill_le st.2.2).2.1 e
      apply r0
      simp only [crest, zi, if_true, x0]
      rfl
    · rw [if_neg zi]; exact zi

/-- The owned blocks of a decoder with `DGood`. -/
theorem good_owned {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (b : Nat) : StreamOwned h r b ↔ DeflateOwned ds d b := by
  have live := good.live
  constructor
  · rintro ⟨z', get, (⟨i, s, state, _, _⟩ | ⟨i, s, state, dstate, owned⟩)⟩
    · have same : z' = z := Option.some.inj (get.symm.trans live.hz)
      subst same
      rw [live.zst] at state
      cases state
    · have same : z' = z := Option.some.inj (get.symm.trans live.hz)
      subst same
      rw [live.zst] at state
      cases state
      have sd : s = d := Option.some.inj (dstate.symm.trans live.hs)
      subst sd
      exact owned
  · intro owned
    exact ⟨z, live.hz, Or.inr ⟨ds, d, live.zst, live.hs, owned⟩⟩

/-- A block of a caller view is a block of the caller heap. -/
theorem caller_view_blocks {h : Heap} {p : BPtr} {n : Nat} (w : (∃ xs, Bytes h p n xs) ∨ Writable h p n) :
    ∀ r j, p = .ref r j → ∀ c, BRef.block r = some c → h.live c := by
  intro r j hp c hc
  rcases w with ⟨xs, ⟨h0, -, -⟩ | ⟨r', j', a, hq, g, -, -⟩⟩ | ⟨h0, -⟩ | ⟨r', j', a, hq, g, -, -⟩
  · rw [hp] at h0; cases h0
  · rw [hp] at hq; cases hq; exact view_block_live g c hc
  · rw [hp] at h0; cases h0
  · rw [hp] at hq; cases hq; exact view_block_live g c hc

theorem advance_blocks {h : Heap} {p : BPtr} (m : Nat)
    (blocks : ∀ r j, p = .ref r j → ∀ c, BRef.block r = some c → h.live c) :
    ∀ r j, advance p m = .ref r j → ∀ c, BRef.block r = some c → h.live c := by
  intro r j hp c hc
  cases p with
  | null => cases hp
  | ref r' j' =>
    simp only [advance, Ptr.ref.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    exact blocks r' j' rfl c hc

/-- One iteration: the refills, then one `deflate` call. The state is kept, the measure falls
on `Z_OK`, and the result is one of the four codes of `deflate`. -/
theorem step (call : Goal.deflate) (facts : DeflateLoopFacts) {e : CEnv} (ok : COK e) {st : Loop}
    {H : Heap} {out : List UInt8} {used : Nat} {z : ZStream} {s : DeflateState}
    (cs : CState e st H out used z s) :
    ∃ rc H', (do let x ← deflate (some e.r) (cflush z st); pure (x, crest z st) : M Loop)
        (e.r.put H (crefilled z st)) = .ok ((rc, crest z st), H') ∧
      (∃ out' used' z' s', CState e (rc, crest z st) H' out' used' z' s') ∧
      (rc = Z_OK → cmeasure e (rc, crest z st) H' < cmeasure e st H) ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  let z1 := crefilled z st
  let H1 := e.r.put H z1
  have hz : H.streams e.k = some z := cs.good.live.hz
  have H1eq : H1 = { H with streams := upd H.streams e.k (some z1) } := put_tab_eq hz
  have k0 : ¬ e.h₀.live e.k := ok.fresh e.k (Nat.le_refl _)
  have hzH : e.r.get H = some z := cs.good.live.hz
  have hz1 : e.r.get H1 = some z1 := Zlib.Deflate.Proofs.ZStreamRef.get_put_same hzH _
  have sameOut : ∀ b, b ≠ e.k → SameAt H H1 b := by
    intro b ne
    rw [H1eq]
    rcases put_tab_same hz z1 b with x | x
    · exact x
    · exact absurd x ne
  have liveH1 : ∀ b, H1.live b ↔ H.live b := by intro b; rw [H1eq]; exact put_tab_live hz z1 b
  have hglob : LibraryGlobals H := by
    have g := ok.globals
    simp only [LibraryGlobals] at g ⊢
    rw [cs.agree.static, (put_globals_writeOut _ _ _).1]; exact g
  -- the refills are a rebuffer
  have rb : Rebuffer H H1 e.r := by
    refine ⟨by rw [H1eq]; exact fresh_put_tab hz z1 cs.good.fresh,
      by rw [H1eq]; exact uniq_put_tab hz z1 (by exact cs.good.uniq), by rw [H1eq]; exact hglob, ?_,
      z, z1, hzH, hz1, by simp [z1, crefilled]⟩
    refine ⟨by rw [H1eq], by rw [H1eq], by rw [H1eq], by rw [H1eq]; exact Nat.le_refl _,
      by rw [H1eq]; exact Nat.le_refl _, ?_⟩
    intro b live notChanged
    by_cases bk : b = e.k
    · exfalso
      apply notChanged
      intro own
      have o := (good_owned cs.good b).1 own
      rw [cs.owned b] at o
      omega
    · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := sameOut b bk
      exact ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩
  have reach1 : StreamReachable .deflate H1 e.r := .rebuffer cs.reach rb (fun e => by cases e)
  obtain ⟨z1', hz1', -, good1⟩ := Zlib.Deflate.Universal.rebuffer_good cs.good rb
  have ez : z1' = z1 := Option.some.inj (hz1'.symm.trans hz1)
  subst ez
  -- the caller heap agrees with the refilled heap
  have agree1 : Agree e.h₀.live (writeOut e.h₀ e.dest out) H1 := by
    refine ⟨fun b live => (cs.agree.blocks b live).trans (sameOut b (fun x => k0 (x ▸ live))), ?_, ?_, ?_, ?_⟩
    · rw [H1eq]; exact cs.agree.static
    · rw [H1eq]; exact cs.agree.allocOk
    · rw [H1eq]; exact cs.agree.garbage
    · rw [H1eq]; exact cs.agree.borrow
  have inC := cs.inCount
  have outC := cs.outCount
  have cin : z1.avail_in.toNat + (crest z st).2.toNat = z.avail_in.toNat + st.2.2.toNat := crest_in z st
  have cout : z1.avail_out.toNat + (crest z st).1.toNat = z.avail_out.toNat + st.2.1.toNat := crest_out z st
  have notOwned : ∀ (q : BPtr), (∀ r j, q = .ref r j → ∀ c, BRef.block r = some c → e.h₀.live c) →
      ∀ b, ByteRoot q b → ¬ StreamOwned H1 e.r b := by
    intro q blocks b root own
    have o := (good_owned good1 b).1 own
    rw [cs.owned b] at o
    cases q with
    | null => cases root
    | ref r j =>
      have lb := blocks r j rfl b (byteRoot_block root)
      have := ok.fresh.lt lb
      simp only [CEnv.k] at o
      omega
  have srcBlocks := caller_view_blocks (Or.inl ⟨_, ok.srcBytes⟩)
  have destBlocks := caller_view_blocks (Or.inr ok.destW)
  -- the input range
  have inBytes : Bytes e.h₀ (advance e.source used) z1.avail_in.toNat
      ((e.src.drop used).take z1.avail_in.toNat) := bytes_sub ok.srcBytes (by omega)
  have sepIn : Separate (advance e.source used) z1.avail_in.toNat e.dest e.cap := by
    have := separate_sub (c := used) (d := 0) (n' := z1.avail_in.toNat) (m' := e.cap) ok.sep (by omega) (by omega)
    rwa [advance_zero] at this
  have inE := bytes_writeOut_sep (xs := out) inBytes sepIn (by omega) ok.destW
  have nextIn1 : z1.next_in = advance e.source used := cs.nextIn
  have nextOut1 : z1.next_out = advance e.dest out.length := cs.nextOut
  have inH1 := agree1.bytes inE (advance_blocks used srcBlocks)
  -- the output range
  have outW : Writable e.h₀ (advance e.dest out.length) z1.avail_out.toNat := writable_sub ok.destW (by omega)
  have outE := writable_writeOut (xs := out) outW (by omega) ok.destW
  have outH1 := agree1.writable outE (advance_blocks out.length destBlocks)
  have buffers : StreamBuffers H1 e.r := by
    refine ⟨z1, hz1, ?_, ?_, ?_⟩
    · rw [nextIn1]
      by_cases sn : advance e.source used = .null
      · exact Or.inl sn
      · exact Or.inr ⟨⟨_, inH1⟩, fun h => absurd h (by decide),
          notOwned _ (advance_blocks used srcBlocks)⟩
    · rw [nextOut1]
      rcases outH1 with ⟨h0, -⟩ | ⟨r, j, a, hq, g, ro, fit⟩
      · exact Or.inl h0
      · exact Or.inr ⟨⟨_, Or.inr ⟨r, j, a, hq, g, fit, rfl⟩⟩, fun _ => Or.inr ⟨r, j, a, hq, g, ro, fit⟩,
          notOwned _ (advance_blocks out.length destBlocks)⟩
    · rw [nextIn1, nextOut1]
      exact separate_sub ok.sep (by omega) (by omega)
  have active : ActiveHeader H1 e.r := by
    refine ⟨z1, hz1, ?_, ?_⟩
    · intro i' s' hst
      rw [good1.live.zst] at hst
      cases hst
    · intro i' s' hst hs
      rw [good1.live.zst] at hst
      cases hst
      have es : s' = s := Option.some.inj (hs.symm.trans good1.live.hs)
      subst es
      refine ⟨fun _ => Or.inl cs.gzhead, ?_, ?_⟩
      · intro i g hg; rw [cs.gzhead] at hg; cases hg
      · intro _ i g hg; rw [cs.gzhead] at hg; cases hg
  -- the call
  obtain ⟨rc, after, z', s', u, o, run, good', acc, written, -, -, codes, refuseIff, -, -, -, noRoom, -,
      finProg, -, -, -, -, frame, live, nallocEq⟩ :=
    call H1 e.r (e.k + 1) z1 s (cflush z st) reach1 good1 buffers active
  obtain ⟨aU, aO, aIn, aOut, aNextIn, aNextOut, aState, -, aZfree, -, -⟩ := acc
  have F := facts H1 e.r (e.k + 1) z1 s (cflush z st) rc after reach1 good1 buffers active run
  have exec : Call.execute (.deflate (some e.r) (cflush z st)) default H1 = .ok ((rc, default), after) := by
    simp [Call.execute, heapCall, C.run] at run ⊢
    rw [run]
  have reach' : StreamReachable .deflate after e.r :=
    .step (call := .deflate (some e.r) (cflush z st)) reach1 (fun e => by cases e) ⟨rfl, rfl⟩ ⟨buffers, active⟩ exec
  have run' : deflate (some e.r) (cflush z st) H1 = .ok (rc, after) := run
  refine ⟨rc, after, ?_, ?_, ?_, codes⟩
  · show (deflate (some e.r) (cflush z st) >>= fun x => pure (x, crest z st)) H1 = _
    simp only [bind_app, run', pure_app]
  · -- the state after the call
    have borrow : after.libcErrorBorrow = H1.libcErrorBorrow :=
      Zlib.Deflate.BorrowProofs.stable_deflate (some e.r) (cflush z st) H1 rc after run'
    have outside : ∀ b, e.h₀.live b → ¬ (StreamRoot e.r b ∨ DeflateOwned (e.k + 1) s b) := by
      intro b lb ch
      have lt : b < e.k := ok.fresh.lt lb
      rcases ch with ch | ch
      · simp only [StreamRoot, CEnv.r] at ch; exact absurd ch (by simp only [CEnv.k] at lt; omega)
      · rw [cs.owned b] at ch; omega
    have outLe : o.length ≤ z1.avail_out.toNat := by omega
    have wOutE : o ≠ [] → Writable (writeOut e.h₀ e.dest out) z1.next_out o.length := by
      intro _
      rw [nextOut1]
      exact writable_writeOut (writable_sub ok.destW (by omega)) (by omega) ok.destW
    have agreeE := agree_after_call agree1 (fun b l => (writeOut_live b).2 l) (fun b l => (writeOut_live b).1 l)
      outside (by simpa using frame) written wOutE borrow
    have agree' : Agree e.h₀.live (writeOut e.h₀ e.dest (out ++ o)) after := by
      by_cases ne : o = []
      · subst ne; simpa [writeOut_nil] using agreeE
      · have W2 : Writable e.h₀ e.dest (out.length + o.length) := by
          have := writable_sub (c := 0) (m := out.length + o.length) ok.destW (by omega)
          rwa [advance_zero] at this
        rw [← writeOut_append W2, ← nextOut1]
        exact agreeE
    obtain ⟨gz', own'⟩ := F.2.2 z' s' good'
    refine ⟨out ++ o, used + u, z', s', ?_⟩
    exact
      { reach := reach'
        good := good'
        zfree := by rw [aZfree]; exact cs.zfree
        gzhead := gz'.trans cs.gzhead
        owned := fun b => (own' b).trans (cs.owned b)
        inCount := by simp only []; omega
        nextIn := by rw [aNextIn, nextIn1, advance_add]
        outCount := by simp only [List.length_append]; omega
        nextOut := by rw [aNextOut, nextOut1, advance_add, List.length_append]
        agree := agree'
        liveOnly := by
          intro b lb
          have l1 : H1.live b := by
            have := (live b).1 lb
            simpa using this
          exact cs.liveOnly b ((liveH1 b).1 l1)
        nalloc := by
          rw [nallocEq, H1eq]
          exact cs.nalloc }
  · -- the measure falls
    intro rcOk
    have notRef : ¬ DeflateRefuses z1 s (cflush z st) := by
      intro ref
      have := refuseIff.2 ref
      rw [rcOk] at this
      exact absurd this (by decide)
    have room : z1.avail_out ≠ 0 := by
      intro r0
      have := noRoom notRef r0
      rw [rcOk] at this
      exact absurd this (by decide)
    have prog : u ≠ 0 ∨ o ≠ [] := by
      by_cases fl : cflush z st = Z_FINISH
      · by_cases fs : s.status = FINISH_STATE ∧ z1.avail_in ≠ 0
        · have := F.2.1 notRef fs.1 fs.2
          rw [rcOk] at this
          exact absurd this (by decide)
        · rcases finProg fl notRef room fs with x | x
          · rw [rcOk] at x; exact absurd x (by decide)
          · exact x
      · have nf : cflush z st = Z_NO_FLUSH := by
          unfold cflush at fl ⊢
          split
          · rename_i h0; rw [if_pos h0] at fl; exact absurd rfl fl
          · rfl
        have ch := F.1 notRef nf (noflush_input nf) room rcOk z' good'.live.hz
        rcases ch with x | x
        · left; intro u0; apply x
          apply UInt32.toNat_inj.mp; omega
        · right; intro o0; apply x
          subst o0
          apply UInt32.toNat_inj.mp; simp at aOut; omega
    simp only [cmeasure]
    rw [good'.live.hz, hzH]
    simp only []
    rcases prog with p | p
    · omega
    · have : o.length ≠ 0 := fun h => p (List.eq_nil_of_length_eq_zero h)
      omega

/-- The codes of `deflate`. -/
def DCode (rc : Int32) : Prop := rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR

theorem cmeasure_bound {e : CEnv} (ok : COK e) {st : Loop} {H : Heap} {out : List UInt8} {used : Nat}
    {z : ZStream} {s : DeflateState} (cs : CState e st H out used z s) : cmeasure e st H < fuel := by
  have hz : e.r.get H = some z := cs.good.live.hz
  simp only [cmeasure, hz]
  have := cs.inCount
  have := cs.outCount
  have := ok.nBound
  have := ok.capBound
  simp only [fuel]
  omega

/-- The loop returns with the state kept and a code of `deflate`. -/
theorem loop_run (call : Goal.deflate) (facts : DeflateLoopFacts) {e : CEnv} (ok : COK e)
    {body : Loop → M Loop} {cond : Loop → M (Bool × Loop)} (hB : CBodyOK e.r body) (hC : CCondOK cond)
    {st : Loop} {H : Heap} {out : List UInt8} {used : Nat} {z : ZStream} {s : DeflateState}
    (cs : CState e st H out used z s) (code : DCode st.1) :
    ∃ st' H', cdoWhile body cond st H = .ok (st', H') ∧ DCode st'.1 ∧
      ∃ out' used' z' s', CState e st' H' out' used' z' s' := by
  let P : Loop → Heap → Prop := fun st H => DCode st.1 ∧ ∃ out used z s, CState e st H out used z s
  have start : P st H := ⟨code, out, used, z, s, cs⟩
  refine cdoWhile_decreasing P P (cmeasure e) ?_ start (cmeasure_bound ok cs)
  rintro st H ⟨-, out, used, z, s, cs⟩
  have hz : e.r.get H = some z := cs.good.live.hz
  obtain ⟨rc, H', run, kept, lt, codes⟩ := step call facts ok cs
  have bodyEq : body st H = .ok ((rc, crest z st), H') := by rw [hB st H z hz]; exact run
  refine ⟨_, H', rc == Z_OK, (rc, crest z st), H', bodyEq, hC _ _, ?_, ?_⟩
  · intro c
    have rcOk : rc = Z_OK := by simpa using c
    exact ⟨⟨codes, kept⟩, lt rcOk⟩
  · intro _
    exact ⟨codes, kept⟩

/-- The loop of the translation, found in a goal by `generalize`, returns with the state kept. -/
theorem loop_result (call : Goal.deflate) (facts : DeflateLoopFacts) {e : CEnv} (ok : COK e)
    {body : Loop → M Loop} {cond : Loop → M (Bool × Loop)}
    {st : Loop} {H : Heap} {out : List UInt8} {used : Nat} {z : ZStream} {s : DeflateState}
    (cs : CState e st H out used z s) (code : DCode st.1) {res : Except Fault (Loop × Heap)}
    (hres : cdoWhile body cond st H = res) {k : Nat} (hk : e.r = .tab k) (hB : CBodyOK (.tab k) body)
    (hC : CCondOK cond) :
    ∃ st' H', res = .ok (st', H') ∧ DCode st'.1 ∧ ∃ out' used' z' s', CState e st' H' out' used' z' s' := by
  obtain ⟨st', H', run, done⟩ := loop_run call facts ok (hk ▸ hB) hC cs code
  exact ⟨st', H', hres.symm.trans run, done⟩

end ZlibF.Spec.Public.Proofs.Compress
