import ZlibF.Proof.«inflate.c.reachable»
import ZlibF.Proof.«inflate.c.default-view-finish-code»
import ZlibF.Proof.«inflate.c.default-view-return-trace»
import ZlibF.Proof.«inflate.c.dictionary-return-sync-run»
import ZlibF.Proof.«inflate.c.main.table2»
import ZlibF.Proof.«inflate.c.block-type»
import ZlibF.Proof.«inflate.c.header-default»

/-!
# inflate.c: a call from `HEAD` uses input

An `inflate(strm, Z_NO_FLUSH)` call on a reachable stream in mode `HEAD`, with no held bits, `last = 0` and
pending input, either refuses the stream (`Z_STREAM_ERROR`) or returns with less input than it started with.

* The first trip of the loop pulls a byte: `HEAD` with `wrap ≠ 0` runs `NEEDBITS(16)`; `HEAD` with `wrap = 0` moves to
  `TYPEDO` with the registers unchanged, and `TYPEDO` with `last = 0` runs `NEEDBITS(3)`. The rest of those two
  modes does not raise `have` (`HaveLeX`, a register observer).
* No later trip raises `have`: every default dispatch step accounts `regs.have + used = l.have`
  (`inflate_dispatch_default_view_state_rank`, which covers `inflate_fast` with its proved bit budget).
* `inf_leave` writes `strm->avail_in = have`; the direct `Z_NEED_DICT` return restores the registers first
  (`inflate_run_need_dict_sync`); `Z_MEM_ERROR` from the switch needs mode `MEM`, which a call from `HEAD` never
  reaches (`inflate_dispatch_normal_low`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## A register observer: `have` does not rise above a bound -/

/-- Every successful execution keeps `have` at most `base` when it starts at most `base`. It assumes neither safety
nor termination. -/
def HaveLeX {α : Type} (base : Nat) (program : X α) : Prop :=
  ∀ l h result regs after, l.have_.toNat ≤ base →
    runX program l h = .ok ((result, regs), after) → regs.have_.toNat ≤ base

theorem haveLeX_pure {α : Type} (base : Nat) (value : α) : HaveLeX base (pure value) := by
  intro l h result regs after current run
  cases run
  exact current

theorem haveLeX_get (base : Nat) : HaveLeX base (get : X IL) := by
  intro l h result regs after current run
  cases run
  exact current

theorem haveLeX_set (base : Nat) (l : IL) (current : l.have_.toNat ≤ base) :
    HaveLeX base (set l : X Unit) := by
  intro before h result regs after _ run
  cases run
  exact current

theorem haveLeX_modify (base : Nat) (update : IL → IL)
    (fixed : ∀ l, l.have_.toNat ≤ base → (update l).have_.toNat ≤ base) :
    HaveLeX base (modify update : X Unit) := by
  intro l h result regs after current run
  cases run
  exact fixed l current

theorem haveLeX_lift {α : Type} (base : Nat) (program : M α) :
    HaveLeX base (monadLift program : X α) := by
  intro l h result regs after current run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact current

theorem haveLeX_throw {α : Type} (base : Nat) (exit : Ex) :
    HaveLeX base (throw exit : X α) := by
  intro l h result regs after current run
  cases run
  exact current

theorem haveLeX_bind {α β : Type} {base : Nat} {first : X α} {next : α → X β}
    (hf : HaveLeX base first) (hn : ∀ value, HaveLeX base (next value)) :
    HaveLeX base (first >>= next) := by
  intro l h result regs after current run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    have middle := hf _ _ _ _ _ current firstRun
    cases decision with
    | error exit => cases run; exact middle
    | ok value => exact hn value _ _ _ _ _ middle run

theorem haveLeX_get_bind {α : Type} {base : Nat} {next : IL → X α}
    (body : ∀ l, l.have_.toNat ≤ base → HaveLeX base (next l)) :
    HaveLeX base (get >>= next) := by
  intro l h result regs after current run
  rw [runX_bind, runX_get] at run
  exact body l current _ _ _ _ _ current run

theorem haveLeX_ite {α : Type} {base : Nat} {test : Prop} [Decidable test] {yes no : X α}
    (hy : HaveLeX base yes) (hn : HaveLeX base no) : HaveLeX base (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

macro "have_le_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact haveLeX_pure _ _
    | with_reducible exact haveLeX_get _
    | with_reducible exact haveLeX_lift _ _
    | with_reducible exact haveLeX_throw _ _
    | with_reducible refine haveLeX_set _ _ ?_
    | with_reducible refine haveLeX_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine haveLeX_get_bind (fun _ fixed => ?_)
    | with_reducible apply haveLeX_ite
    | with_reducible refine haveLeX_bind ?_ (fun _ => ?_)
    | assumption
    | split)

theorem haveLeX_BITS (base : Nat) (n : UInt32) : HaveLeX base (BITS n) := by
  unfold BITS
  have_le_source

theorem haveLeX_DROPBITS (base : Nat) (n : UInt32) : HaveLeX base (DROPBITS n) := by
  unfold DROPBITS
  have_le_source

theorem haveLeX_INITBITS (base : Nat) : HaveLeX base INITBITS := by
  unfold INITBITS
  have_le_source

theorem haveLeX_CRC2 (base : Nat) (c : Ctx) : HaveLeX base (CRC2 c) := by
  unfold CRC2
  have_le_source

macro "have_le_mode" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact haveLeX_BITS _ _
    | with_reducible exact haveLeX_DROPBITS _ _
    | with_reducible exact haveLeX_INITBITS _
    | with_reducible exact haveLeX_CRC2 _ _
    | with_reducible assumption
    | with_reducible exact haveLeX_pure _ _
    | with_reducible exact haveLeX_get _
    | with_reducible exact haveLeX_lift _ _
    | with_reducible exact haveLeX_throw _ _
    | with_reducible refine haveLeX_set _ _ ?_
    | with_reducible refine haveLeX_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine haveLeX_get_bind (fun _ fixed => ?_)
    | with_reducible apply haveLeX_ite
    | with_reducible refine haveLeX_bind ?_ (fun _ => ?_)
    | assumption
    | split)

/-! ## The first trip pulls a byte -/

/-- `NEEDBITS(n)` with fewer than `n` bits held and pending input pulls at least one byte, and never returns. -/
theorem headUses_needbits_strict {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) (n : UInt32)
    (hn : n.toNat ≤ 49) (short : l.bits.toNat < n.toNat) (pending : l.have_ ≠ 0) :
    ∃ r1 l1, runX (NEEDBITS n) l h = .ok ((r1, l1), h) ∧ l1.have_.toNat < l.have_.toNat ∧
      ∀ v, r1 ≠ .error (Ex.ret v) := by
  obtain ⟨r1, l1, j, run, hj, B1, _, bits1, _, _, _, okBits, leaveFacts⟩ := NEEDBITS_run B n hn
  have noRet := noRet_NEEDBITS n _ _ _ _ _ run
  refine ⟨r1, l1, run, ?_, noRet⟩
  have e1 := B1.have_eq
  have e0 := B.have_eq
  rw [List.length_drop] at e1
  have positive : l.have_.toNat ≠ 0 := fun zero => pending (UInt32.toNat_inj.mp (by simp [zero]))
  have one : 1 ≤ j := by
    rcases r1 with e | u
    · cases e with
      | leave =>
        obtain ⟨all, _, _⟩ := leaveFacts rfl
        omega
      | ret v => exact absurd rfl (noRet v)
    · cases u
      have := okBits rfl
      omega
  omega

/-- From `HEAD` with `wrap ≠ 0`, or from `TYPEDO` with `last = 0`, with no held bits and pending input, one trip of
the switch ends with less input. -/
theorem headUses_dispatch_pulls {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} (E : Env c h r zs z s) (B : BitInv h l bs) (b0 : l.bits = 0)
    (pending : l.have_ ≠ 0) (mode : (s.mode = HEAD ∧ s.wrap ≠ 0) ∨ (s.mode = TYPEDO ∧ s.last = 0))
    {o : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (inflate_dispatch c) l h = .ok ((o, regs), after)) :
    regs.have_.toNat < l.have_.toNat := by
  have short : ∀ n : UInt32, 0 < n.toNat → l.bits.toNat < n.toNat := by
    intro n p
    rw [b0]
    exact p
  rcases mode with ⟨head, wrap⟩ | ⟨typedo, last⟩
  · rw [inflate_dispatch_HEAD E l head] at run
    have nowrap : (s.wrap == 0) = false := by simp [wrap]
    unfold inflate_HEAD at run
    rw [runX_bind, runX_rdS E] at run
    simp only [nowrap, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨r1, l1, nb, lt1, _⟩ := headUses_needbits_strict B 16 (by decide) (short 16 (by decide)) pending
    rw [runX_bind, nb] at run
    rcases r1 with e | u
    · simp only [] at run
      cases run
      exact lt1
    · cases u
      simp only [] at run
      have key : ∀ {p : X Unit}, HaveLeX l1.have_.toNat p → runX p l1 h = .ok ((o, regs), after) →
          regs.have_.toNat ≤ l1.have_.toNat := fun hp hr => hp _ _ _ _ _ (Nat.le_refl _) hr
      refine Nat.lt_of_le_of_lt (key ?_ run) lt1
      have_le_mode
  · rw [inflate_dispatch_block_type E l (Or.inr typedo)] at run
    rw [if_neg (by rw [typedo]; decide)] at run
    unfold inflate_TYPEDO at run
    rw [runX_bind, runX_rdS E] at run
    simp only [last, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨r1, l1, nb, lt1, _⟩ := headUses_needbits_strict B 3 (by decide) (short 3 (by decide)) pending
    rw [runX_bind, nb] at run
    rcases r1 with e | u
    · simp only [] at run
      cases run
      exact lt1
    · cases u
      simp only [] at run
      have key : ∀ {p : X Unit}, HaveLeX l1.have_.toNat p → runX p l1 h = .ok ((o, regs), after) →
          regs.have_.toNat ≤ l1.have_.toNat := fun hp hr => hp _ _ _ _ _ (Nat.le_refl _) hr
      refine Nat.lt_of_le_of_lt (key ?_ run) lt1
      have_le_mode

/-! ## The loop -/

/-- Either input was used, or the loop is still at its start: all `A` input bytes pending, no held bits, `last = 0`,
and mode `HEAD` or `TYPEDO`. -/
def HeadFresh (A : Nat) (l : IL) (s : InflateState) : Prop :=
  l.have_.toNat < A ∨ (l.have_.toNat = A ∧ A ≠ 0 ∧ l.bits = 0 ∧ s.last = 0 ∧ (s.mode = HEAD ∨ s.mode = TYPEDO))

/-- The loop invariant: the default dispatch invariant of `NoSyncLoopInv`, the decoder not in `MEM`, and `HeadFresh`. -/
def HeadLoopInv (c : Ctx) (r : ZStreamRef) (zs : Nat) (A : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ HeaderLocal c h r s l ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39 ∧
    s.mode ≠ SYNC ∧ s.mode ≠ MEM ∧ HeadFresh A l s

/-- What the loop leaves with: less input than `A`, and not the direct `Z_MEM_ERROR` return. -/
def HeadLoopPost (A : Nat) (exit : Ex) (regs : IL) (_after : Heap) : Prop :=
  regs.have_.toNat < A ∧ exit ≠ .ret Z_MEM_ERROR

theorem headUses_step {c : Ctx} {r : ZStreamRef} {zs : Nat} {A : Nat}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (l : IL) (h : Heap) (outcome : Except Ex Unit) (regs : IL) (after : Heap)
    (current : HeadLoopInv c r zs A l h)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    match outcome with
    | .ok () => HeadLoopInv c r zs A regs after
    | .error exit => HeadLoopPost A exit regs after := by
  obtain ⟨zz, ss, bs, J, local_, buffers, bits39, nsync, nmem, fresh⟩ := current
  have env : Env c h r zs zz ss := ⟨root, state, J.good.live.hz, J.good.live.hs⟩
  obtain ⟨o2, regs2, after2, nextZ, nextS, used, made, _, source, final, ⟨rest, _, packet⟩, _, _, count, _, _,
    bits, finalLocal, _⟩ := inflate_dispatch_default_view_state_rank env J buffers local_ bits39
  have same := Except.ok.inj (source.symm.trans run)
  simp only [Prod.mk.injEq] at same
  obtain ⟨⟨e1, e2⟩, e3⟩ := same
  subst o2
  subst regs2
  subst after2
  have progress : regs.have_.toNat < A ∨
      (outcome = .ok () ∧ regs.have_.toNat = A ∧ A ≠ 0 ∧ regs.bits = 0 ∧ nextS.last = 0 ∧ nextS.mode = TYPEDO) := by
    rcases fresh with lt | ⟨eqA, Apos, b0, last0, modes⟩
    · left
      omega
    · have pending : l.have_ ≠ 0 := fun zero => Apos (by rw [← eqA, zero]; rfl)
      have pull : (ss.mode = HEAD ∧ ss.wrap ≠ 0) ∨ (ss.mode = TYPEDO ∧ ss.last = 0) → regs.have_.toNat < A := by
        intro md
        rw [← eqA]
        exact headUses_dispatch_pulls env buffers.bits b0 pending md run
      rcases modes with head | typedo
      · by_cases w : ss.wrap = 0
        · right
          have isZero : (ss.wrap == 0) = true := by simp [w]
          have hrun : runX (inflate_dispatch c) l h =
              .ok ((.ok (), l), setI h zs { ss with mode := TYPEDO }) := by
            rw [inflate_dispatch_HEAD env l head]
            unfold inflate_HEAD
            rw [runX_bind, runX_rdS env]
            simp only [isZero, ↓reduceIte]
            rw [runX_bind, runX_setMode env]
            rfl
          have e := Except.ok.inj (hrun.symm.trans run)
          simp only [Prod.mk.injEq] at e
          obtain ⟨⟨f1, f2⟩, f3⟩ := e
          have hs := final.good.live.hs
          rw [← f3, setI_istates_same] at hs
          cases hs
          rw [← f2]
          exact ⟨f1.symm, eqA, Apos, b0, last0, rfl⟩
        · left
          exact pull (Or.inl ⟨head, w⟩)
      · left
        exact pull (Or.inr ⟨typedo, last0⟩)
  cases outcome with
  | ok u =>
    cases u
    show HeadLoopInv c r zs A regs after
    have low := inflate_dispatch_normal_low env J buffers local_ bits39 run final.good.live.hs
    refine ⟨nextZ, nextS, rest, final, finalLocal, packet, bits, ?_, ?_, ?_⟩
    · intro sync
      rw [sync] at low
      exact (by decide : ¬ SYNC < MEM) low
    · intro memory
      rw [memory] at low
      exact (by decide : ¬ MEM < MEM) low
    · rcases progress with lt | ⟨_, eqA, Apos, b0, last0, typedo⟩
      · exact Or.inl lt
      · exact Or.inr ⟨eqA, Apos, b0, last0, Or.inr typedo⟩
  | error exit =>
    show HeadLoopPost A exit regs after
    have lt : regs.have_.toNat < A := by
      rcases progress with lt | ⟨impossible, _⟩
      · exact lt
      · cases impossible
    refine ⟨lt, ?_⟩
    intro memory
    subst memory
    obtain ⟨modes, _, _⟩ := inflate_dispatch_direct_terminal env J buffers local_ bits39 run (Or.inl rfl)
    rcases modes with ⟨m, _⟩ | ⟨m, _⟩
    · exact nmem m
    · exact nsync m

theorem headUses_loop {c : Ctx} {r : ZStreamRef} {zs : Nat} {A : Nat} {l regs : IL} {h after : Heap} {exit : Ex}
    (root : c.strm = some r) (state : c.st = some (.tab zs))
    (initial : HeadLoopInv c r zs A l h)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after)) :
    HeadLoopPost A exit regs after :=
  xwhile_success_control_post (HeadLoopInv c r zs A) (HeadLoopPost A)
    (fun l h outcome regs after current run => by
      have step := headUses_step root state l h outcome regs after current run
      rcases outcome with e | ⟨⟩ <;> exact step)
    initial run

/-- The body of a call from `HEAD` (no held bits, `last = 0`, pending input) leaves the loop with less input and not
by the direct `Z_MEM_ERROR` return. -/
theorem headUses_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (mode : s.mode = HEAD) (b0 : s.bits = 0) (last0 : s.last = 0) (pending : z.avail_in ≠ 0)
    {exit : Ex} {regs : IL} {after : Heap}
    (run : runX (inflate_run c) IL.init h = .ok ((.error exit, regs), after)) :
    HeadLoopPost z.avail_in.toNat exit regs after := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, entrySizes, entryFrame, entryHeapEq,
    stateEq⟩ := inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have entryLocal := inflate_run_entry_local invariant current entrySizes entryFrame entryHeapEq stateEq local_
  have notType : ¬ s.mode = TYPE := by rw [mode]; decide
  rw [if_neg notType] at stateEq
  subst entryState
  rw [cut] at run
  have positive : z.avail_in.toNat ≠ 0 := fun zero => pending (UInt32.toNat_inj.mp (by simp [zero]))
  exact headUses_loop E.strm E.st
    ⟨z, s, bs, current, entryLocal, packet, bits, by rw [mode]; decide, by rw [mode]; decide,
      Or.inr ⟨rfl, positive, b0, last0, Or.inl mode⟩⟩ run

end Zlib.Inflate.Proofs

namespace ZlibF.Spec.Public.GzRead
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- **The HEAD fact on reachable streams.** An `inflate` call from mode `HEAD` with no held bits, `last = 0` and
pending input takes input or refuses the stream. The premises are those of `Goal.inflate` (`inflate_public`).

`Good` alone (the premise of `InflateHeadUsesInput`) is not enough for a proof from the existing facts: the input
that `inflate_fast` gives back (`len = bits >> 3; in -= len`) is bounded by the bytes it pulled only while its decode
tables are valid. With arbitrary table entries, `bits -= op` can wrap, and `avail_in` can grow in the model. From
`HEAD` the tables used in the call are built in the same call (`TYPEDO`, `CODELENS`), but carrying that through a
whole run under `Good` alone needs a new invariant; the history invariant of reachable streams (`InflateInv`) and
the call premises already give it (`DefaultStateJ`, `DispatchBuffers`). -/
def InflateHeadUsesInputR : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {k : Nat} {z : ZStream} {st : InflateState},
    StreamReachable .inflate h r → Zlib.Inflate.Spec.Good h r k z st →
    ZlibF.PlatformMemory.ByteObjectsFit h → Zlib.Inflate.Spec.DefAlloc z → StreamBuffers h r →
    ActiveHeader h r →
    st.mode = HEAD → st.bits = 0 → st.last = 0 → z.avail_in ≠ 0 →
    ∀ {rc : Int32} {after : Heap} {z' : ZStream},
      C.run (Zlib.Inflate.inflate (some r) Z_NO_FLUSH) h = .ok (rc, after) → r.get after = some z' →
      z'.avail_in.toNat < z.avail_in.toNat ∨ rc = Z_STREAM_ERROR

theorem inflateHeadUsesInputR_holds : InflateHeadUsesInputR := by
  intro h r k z st reach good platform allocator buffers header mode b0 last0 pending rc after z' run get
  obtain ⟨current, _⟩ := inflate_reachable_invariant reach good
  have invariant : DefaultStateJ h r k z st := (current.to_origin platform).toDefaultStateJ
  have entry := ActiveHeader.entry header current.good.live
  let c : Ctx := ⟨some r, some (.tab k), syncBuf h, Z_NO_FLUSH⟩
  have allocated := default_state_syncAlloc invariant
  have local_ : HeaderLocal c (syncAlloc h) r st (dispatchRegs z st) :=
    entry_header_local invariant.good.fresh entry Z_NO_FLUSH
  have env : Env c (syncAlloc h) r k z st :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · right
    have refused : C.run (inflate (some r) Z_NO_FLUSH) h =
        .ok (Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h)) := by
      unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    have e := Except.ok.inj (refused.symm.trans run)
    exact (congrArg Prod.fst e).symm
  · have accepted : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by
      intro null
      apply rejected
      simp [null]
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have callBuffers := streamBuffers_syncAlloc invariant.good.fresh buffers
    obtain ⟨rc2, heap1, stream, state, bytes, exit, regs, loopHeap, loopZ, loopS, used, made, bodyRun, final, _,
      localGet, localSize, localRo, loopRun, loopJ, _, _, _, _, _, trace⟩ :=
      inflate_default_view_local_return_trace env allocated allocator callBuffers nonnull inputValid local_
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have publicRun : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (rc2, freeWin heap1 (syncBuf h)) := by
      unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
      rw [bind_app] at bodyRun
      unfold runX at bodyRun
      dsimp only [c] at bodyRun
      erw [bodyRun]
      simp only []
      change (do freeB (syncBuf h); pure rc2) heap1 = .ok (rc2, freeWin heap1 (syncBuf h))
      rw [bind_app]
      dsimp only [syncBuf]
      rw [freeBuf_run localGet localRo]
      rfl
    have e := Except.ok.inj (publicRun.symm.trans run)
    simp only [Prod.mk.injEq] at e
    obtain ⟨rcEq, afterEq⟩ := e
    have freed := final.free_local localGet localSize
    have streamGet : r.get after = some stream := by
      rw [← afterEq]
      exact freed.good.live.hz
    have zEq : z' = stream := Option.some.inj (get.symm.trans streamGet)
    subst zEq
    have post := headUses_run env allocated callBuffers nonnull inputValid local_ mode b0 last0 pending loopRun
    cases exit with
    | leave =>
      obtain ⟨_, availIn, _⟩ := trace
      left
      rw [availIn]
      exact post.1
    | ret value =>
      obtain ⟨sameRc, _, streamEq, _, direct⟩ := trace
      rcases direct with needDict | memory | streamError
      · subst needDict
        obtain ⟨zz, g, _, avail, _⟩ := inflate_run_need_dict_sync (context := c) rfl rfl loopRun
        have same : zz = loopZ := Option.some.inj (g.symm.trans loopJ.good.live.hz)
        left
        rw [streamEq, ← same, avail]
        exact post.1
      · subst memory
        exact absurd rfl post.2
      · right
        rw [← rcEq, sameRc, streamError]

#print axioms Zlib.Inflate.Proofs.headUses_dispatch_pulls
#print axioms Zlib.Inflate.Proofs.headUses_run
#print axioms inflateHeadUsesInputR_holds

end ZlibF.Spec.Public.GzRead
