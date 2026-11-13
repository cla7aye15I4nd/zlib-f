import ZlibF.Proof.«infback.c.safety-valid»
import ZlibF.Spec.Public.Sequences
import ZlibF.Proof.«infback.c.pull»
import ZlibF.Proof.«infback.c.wf»
import ZlibF.Proof.«inffast.c.tableok»
import ZlibF.Proof.«inftrees.c.decode.prefix-query»
import ZlibF.Proof.«inftrees.c.decode.invariant»
import ZlibF.Proof.«inftrees.c.decode.invariant-prefix»

/-!
# infback.c: the invariant of the dispatch loop over the caller protocol, and `PULL()`

`PInv` is what holds whenever `for (;;) switch (state->mode)` of `inflateBack()` is about to
read the mode. It is stated over the caller protocol of `Goal.inflate_back_sequence_safety`,
with the protocol's observation log as ghost state: the state is valid over the caller's window,
`put`/`left` describe the unwritten tail of the window, the input registers describe the rest of
the chunk `in` returned last (all of which stays readable, outside the window, the stream record
and the state record), the protocol's invariant holds of the log, and the heap differs from the
heap at the call by a `CallbackFrame` and no change of liveness outside the call-backs' blocks.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
set_option autoImplicit false

/-- The protocol of the call-backs of a context. -/
abbrev Proto (c : BCtx) (r : ZStreamRef) (i : Nat) (window : BPtr) (n : Nat) :=
  CallbackProtocol r i window n c.inCb c.inDesc c.outCb c.outDesc

/-- The chunk `held` at `active` is readable, outside the window, the stream record and the state. -/
def ChunkOk (h : Heap) (r : ZStreamRef) (i : Nat) (window : BPtr) (n : Nat) (active : BPtr)
    (held : List UInt8) : Prop :=
  held ≠ [] → Bytes h active held.length held ∧ Separate active held.length window n ∧
    ∀ b, ByteRoot active b → b ≠ i ∧ ¬ StreamRoot r b

/-- The decoding tables of the current block: each is either the state's own `codes` array
with the shape `inflate_fast` needs, every literal/length leaf reading at least one bit, and the
query stability of a prefix code (a byte is pulled only while the held bits are short), or the
static fixed table. -/
def TablesOk (i : Nat) (s : InflateState) : Prop :=
  ((∃ ol, s.lencode = .ref (.istate_codes i) ol ∧ Zlib.Inffast.Spec.LenTableSafe s.codes ol s.lenbits.toNat ∧
      Zlib.Inffast.Spec.LenLeavesPositive s.codes ol s.lenbits.toNat ∧
      Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS s.codes ol s.lenbits.toNat ∧
      Zlib.Inftrees.Proofs.PrefixQuery LENS s.codes ol s.lenbits.toNat ∧
      ∃ used lens, Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS s.codes ol s.lenbits.toNat used lens) ∨
    (s.lencode = .ref .st_lenfix 0 ∧ s.lenbits = 9)) ∧
  ((∃ od, s.distcode = .ref (.istate_codes i) od ∧ Zlib.Inffast.Spec.DistTableSafe s.codes od s.distbits.toNat ∧
      Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS s.codes od s.distbits.toNat ∧
      Zlib.Inftrees.Proofs.PrefixQuery DISTS s.codes od s.distbits.toNat ∧
      ∃ used lens, Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS s.codes od s.distbits.toNat used lens) ∨
    (s.distcode = .ref .st_distfix 0 ∧ s.distbits = 5))

/-- The modes the dispatch loop of `inflateBack()` can be in, with the tables in `LEN`. -/
def ModeOk (i : Nat) (s : InflateState) : Prop :=
  (s.mode = TYPE ∨ s.mode = STORED ∨ s.mode = TABLE ∨ s.mode = LEN ∨ s.mode = DONE ∨ s.mode = BAD) ∧
    (s.mode = LEN → TablesOk i s)

/-- The state fields `inflate_fast` relies on and `inflateBack()` never breaks: `sane` stays
nonzero, `wnext` stays 0, and `whave` is at most `wsize`. -/
def StOk (s : InflateState) : Prop := s.sane ≠ 0 ∧ s.wnext = 0 ∧ s.whave.toNat ≤ s.wsize.toNat

/-- A state write that keeps `sane` and `wnext`, and sets `whave` to itself or to `wsize`. -/
def StKeep (s s' : InflateState) : Prop :=
  s'.sane = s.sane ∧ s'.wnext = s.wnext ∧ (s'.whave = s.whave ∨ s'.whave = s'.wsize)

/-- **The invariant of the dispatch loop**, relative to the heap `h0` at the call. -/
structure PInv (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 h : Heap) (l : IL) (log : BackLog) : Prop where
  cstrm : c.strm = some r
  cst : c.st = some (.tab i)
  valid : ∃ z s, BackValid h r i z s ∧ s.window = window ∧ s.wsize.toNat = n
  winRoot : ∀ b, ByteRoot window b → b ≠ i ∧ ¬ StreamRoot r b
  put : l.put = advance window (n - l.left.toNat) ∧ l.left.toNat ≤ n
  chunk : l.have_.toNat ≤ log.held.length ∧
    (l.have_ ≠ 0 → l.next = advance log.active (log.held.length - l.have_.toNat))
  held : ChunkOk h r i window n log.active log.held
  bits : l.bits.toNat ≤ 39 ∧ l.hold.toNat < 2 ^ l.bits.toNat
  proto : pr.invariant h log
  frame : CallbackFrame pr.own h0 h r i window n
  live : ∀ b, ¬ pr.own b → (h.live b ↔ h0.live b)
  mode : ∀ s, h.istates i = some s → ModeOk i s
  /-- The platform side of the protocol (`BackPlatform`). -/
  platform : BackPlatform pr
  /-- Every byte object has fewer than `2^63` bytes. -/
  fit : ZlibF.PlatformMemory.ByteObjectsFit h
  /-- The chunk in use lies in a heap byte block. -/
  chunkBlk : log.held ≠ [] → ∃ b off, log.active = .ref (.blk b) off
  /-- The state fields of `StOk`. -/
  stOk : ∀ s, h.istates i = some s → StOk s

/-- The rank of a mode in the measure: the modes that leave at once rank lowest. -/
def modeRank (m : UInt32) : Nat := if m == DONE || m == BAD then 0 else if m == TYPE then 1 else 2

/-- The measure of the dispatch loop: four times the input bits still readable (held, in the
chunk, and what `in` may still deliver within `inputBound`), plus the rank of the mode. -/
def backMeasure {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h : Heap) (l : IL) (log : BackLog) : Nat :=
  4 * (l.bits.toNat + 8 * l.have_.toNat + 8 * (pr.inputBound - log.supplied.length)) +
    ((h.istates i).map (fun s => modeRank s.mode)).getD 0

theorem advance_zero (p : BPtr) : advance p 0 = p := by
  cases p <;> rfl

/-- The window's views name only writable byte views of blocks outside the changed set. -/
theorem window_views {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {own : Nat → Prop}
    (writable : Writable h window n) (root : ∀ b, ByteRoot window b → b ≠ i ∧ ¬ StreamRoot r b)
    (disjoint : ∀ x, ByteRoot window x → ¬ own x) :
    RegionViews (fun x => StreamRoot r x ∨ x = i ∨ own x) [⟨window, n⟩] := by
  intro ref rootR
  obtain ⟨region, member, off, pointer⟩ := rootR
  simp only [List.mem_singleton] at member
  subst member
  change window = .ref ref off at pointer
  have outside : ∀ b, ByteRoot window b → ¬ (StreamRoot r b ∨ b = i ∨ own b) := by
    intro b rb inside
    obtain ⟨ne, nroot⟩ := root b rb
    rcases inside with x | x | x
    · exact nroot x
    · exact ne x
    · exact disjoint b rb x
  cases ref with
  | blk b => exact Or.inl ⟨b, rfl, outside b (by rw [pointer]; rfl)⟩
  | dstate_depth b => exact Or.inr ⟨b, rfl, outside b (by rw [pointer]; rfl)⟩
  | _ =>
    exfalso
    rcases writable with ⟨null, -⟩ | ⟨ref0, off0, a0, ptr0, -, ro0, -⟩
    · rw [null] at pointer; cases pointer
    · rw [ptr0] at pointer
      injection pointer with e _
      subst e
      cases ro0

/-- The liveness ledger of a call-back step. -/
theorem live_callback {h h' : Heap} {own : Nat → Prop} (frame : ExternalFrame own h h') (b : Nat)
    (notOwn : ¬ own b) : h'.live b ↔ h.live b := by
  constructor
  · intro live'
    exact Classical.byContradiction fun dead => notOwn (frame.2.2.2.1 b dead live')
  · intro live
    exact Frame.live_kept frame.1 live notOwn

/-- The mode rank of the measure reads the state record, which a call-back keeps. -/
theorem rank_frame {h h' : Heap} {own : Nat → Prop} (frame : ExternalFrame own h h') {i : Nat}
    {s : InflateState} (get : h.istates i = some s) (outside : ¬ own i) :
    (h'.istates i).map (fun s => modeRank s.mode) = (h.istates i).map (fun s => modeRank s.mode) := by
  rw [istates_frame frame.1 get outside, get]

/-- **`PULL()` on the invariant.** With input left nothing happens. With the chunk used up, `in`
is called once (the protocol's `inStep`): a non-empty chunk becomes the chunk in use, recorded in
the log; an empty one ends the call with `Z_BUF_ERROR` and `next = NULL`. The measure does not
grow: the bytes `in` hands out were counted as still deliverable. -/
theorem PULL_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog}
    (I : PInv c pr h0 h l log) :
    ∃ res l' h' log', runX (PULL c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → l'.have_ ≠ 0 ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧ l'.put = l.put ∧ l'.left = l.left ∧
        (l'.next = l.next ∨ l.have_ = 0) ∧ l'.last = l.last) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧ l'.copy = l.copy ∧
      h'.istates i = h.istates i ∧
      backMeasure pr h' l' log' ≤ backMeasure pr h l log := by
  by_cases hz : l.have_ = 0
  · obtain ⟨k, pointer, after, bytes, run, len, ext, window', fresh, inv'⟩ := pr.inStep h log l.next I.proto
    obtain ⟨fit', blk'⟩ := I.platform.1 h log l.next k pointer after I.proto I.fit run
    obtain ⟨z, s, valid, win, size⟩ := I.valid
    have stateOut := pr.disjoint.1
    have rootOut := pr.disjoint.2
    have valid' : BackValid after r i z s :=
      backValid_callback valid ext stateOut rootOut (by rw [win, size]; exact window')
    have writable : Writable h window n := by
      have w := valid.2.2.2.2.2.2.2.2.2.2.1
      rw [win, size] at w; exact w
    have frame' : CallbackFrame pr.own h0 after r i window n :=
      CallbackFrame.trans I.frame (callbackFrame_of_external ext writable)
        (fun disjoint => window_views (valid.2.2.2.2.2.2.2.2.2.2.1 |> fun w => by rw [win, size] at w; exact w)
          I.winRoot disjoint)
    have live' : ∀ b, ¬ pr.own b → (after.live b ↔ h0.live b) :=
      fun b notOwn => (live_callback ext b notOwn).trans (I.live b notOwn)
    have bound := pr.bounded after _ inv'
    simp only [List.length_append] at bound
    have rank := rank_frame ext valid.2.1 stateOut
    by_cases hk : k = 0
    · subst hk
      have bytes0 : bytes = [] := List.eq_nil_of_length_eq_zero (by rw [len]; rfl)
      subst bytes0
      refine ⟨.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }, after, _,
        PULL_noinput hz run,
        { cstrm := I.cstrm, cst := I.cst, valid := ⟨z, s, valid', win, size⟩, winRoot := I.winRoot,
          put := I.put, chunk := ⟨by simp, fun e => absurd rfl e⟩, held := fun e => absurd rfl e,
          bits := I.bits, proto := inv', frame := frame', live := live',
          mode := fun s1 g => by
            rw [istates_frame ext.1 valid.2.1 stateOut] at g; injection g with e; subst e; exact I.mode s valid.2.1,
          platform := I.platform, fit := fit', chunkBlk := fun e => absurd rfl e,
          stOk := fun s1 g => by
            rw [istates_frame ext.1 valid.2.1 stateOut] at g; injection g with e; subst e; exact I.stOk s valid.2.1 },
        fun e => (nomatch e), fun e he => by injection he with he; subst he; exact ⟨rfl, rfl⟩, rfl,
        by rw [istates_frame ext.1 valid.2.1 stateOut, valid.2.1], ?_⟩
      unfold backMeasure
      rw [rank, hz]
      simp only [List.length_append, List.length_nil, Nat.add_zero, UInt32.toNat_zero]
      omega
    · obtain ⟨bytesB, sep, roots⟩ := fresh hk
      have kpos : k.toNat ≠ 0 := fun e => hk (UInt32.toNat_inj.mp (by rw [e]; rfl))
      refine ⟨.ok (), { l with have_ := k, next := pointer }, after, _, PULL_chunk hz hk run,
        { cstrm := I.cstrm, cst := I.cst, valid := ⟨z, s, valid', win, size⟩, winRoot := I.winRoot,
          put := I.put, chunk := ⟨by show k.toNat ≤ bytes.length; rw [len]; exact Nat.le_refl _,
            fun _ => by simp [len, advance_zero]⟩,
          held := fun _ => ⟨by rw [len]; exact bytesB, by rw [len]; exact sep, roots⟩,
          bits := I.bits, proto := inv', frame := frame', live := live',
          mode := fun s1 g => by
            rw [istates_frame ext.1 valid.2.1 stateOut] at g; injection g with e; subst e; exact I.mode s valid.2.1,
          platform := I.platform, fit := fit', chunkBlk := fun _ => blk' hk,
          stOk := fun s1 g => by
            rw [istates_frame ext.1 valid.2.1 stateOut] at g; injection g with e; subst e; exact I.stOk s valid.2.1 },
        fun _ => ⟨hk, rfl, rfl, rfl, rfl, Or.inr hz, rfl⟩, fun e he => (nomatch he), rfl,
        by rw [istates_frame ext.1 valid.2.1 stateOut, valid.2.1], ?_⟩
      unfold backMeasure
      rw [rank, hz]
      simp only [UInt32.toNat_zero, List.length_append, len]
      rw [len] at bound
      omega
  · refine ⟨.ok (), l, h, log, PULL_have hz, I, fun _ => ⟨hz, rfl, rfl, rfl, rfl, Or.inl rfl, rfl⟩,
      fun e he => (nomatch he), rfl, rfl, Nat.le_refl _⟩

/-- The registers of `PInv` satisfy the bit invariant of `inflate()` for the rest of the chunk. -/
theorem bitInv_of {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) :
    Zlib.Inflate.Proofs.BitInv h l (log.held.drop (log.held.length - l.have_.toNat)) := by
  obtain ⟨le, next⟩ := I.chunk
  refine ⟨by simp; omega, ?_, I.bits.2⟩
  by_cases empty : log.held.drop (log.held.length - l.have_.toNat) = []
  · exact Or.inl empty
  · right
    have heldNe : log.held ≠ [] := fun e => empty (by rw [e]; simp)
    have haveNe : l.have_ ≠ 0 := by
      intro e; apply empty; rw [e]; simp
    obtain ⟨bytes, -, -⟩ := I.held heldNe
    rcases bytes with ⟨_, len0, held0⟩ | ⟨ref, off, a, ptr, get, room, held⟩
    · exact absurd held0 heldNe
    · have nx := next haveNe
      generalize hk : log.held.length = k at le nx room held
      generalize hv : l.have_.toNat = v at le nx
      refine ⟨ref, a, off + (k - v), ?_, get, ?_, ?_⟩
      · rw [nx, ptr]; rfl
      · rw [held, List.length_drop, List.length_take, List.length_drop, Array.length_toList]; omega
      · rw [held, List.drop_take, List.drop_drop]
        congr 1
        rw [List.length_take, List.length_drop, Array.length_toList]
        omega

/-- `PULLBYTE()` keeps the bits held below the new byte. -/
theorem pulled_hold_mod (l : IL) (b : UInt8) (nx : BPtr) (hb : l.bits.toNat ≤ 31)
    (hl : l.hold.toNat < 2 ^ l.bits.toNat) :
    (Zlib.Inflate.Proofs.pulled l b nx).hold.toNat % 2 ^ l.bits.toNat = l.hold.toNat := by
  have p31 : 2 ^ l.bits.toNat ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hb
  have b256 : b.toNat < 256 := b.toNat_lt
  have prod : b.toNat * 2 ^ l.bits.toNat ≤ 255 * 2 ^ 31 := Nat.mul_le_mul (by omega) p31
  have hb64 : l.bits.toNat % 64 = l.bits.toNat := Nat.mod_eq_of_lt (by omega)
  have shl : (b.toUInt64 <<< l.bits.toUInt64).toNat = b.toNat * 2 ^ l.bits.toNat := by
    rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, hb64, UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  show (l.hold + (b.toUInt64 <<< l.bits.toUInt64)).toNat % 2 ^ l.bits.toNat = l.hold.toNat
  rw [UInt64.toNat_add, shl,
    Nat.mod_eq_of_lt (show l.hold.toNat + b.toNat * 2 ^ l.bits.toNat < 2 ^ 64 by omega),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

/-- **`PULLBYTE()` on the invariant**, with room for eight more bits. -/
theorem PULLBYTE_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog}
    (I : PInv c pr h0 h l log) (room : l.bits.toNat ≤ 31) :
    ∃ res l' h' log', runX (Zlib.Infback.PULLBYTE c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → l'.bits.toNat = l.bits.toNat + 8 ∧ l'.put = l.put ∧ l'.left = l.left ∧
        l'.hold.toNat % 2 ^ l.bits.toNat = l.hold.toNat ∧ l'.last = l.last) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧ h'.istates i = h.istates i ∧
      backMeasure pr h' l' log' ≤ backMeasure pr h l log := by
  obtain ⟨res1, l1, h1, log1, run1, I1, okc, errc, -, ist1, meas1⟩ := PULL_p c pr I
  cases res1 with
  | error e =>
    obtain ⟨rfl, ret⟩ := errc e rfl
    refine ⟨.error Ex.leave, l1, h1, log1, ?_, I1, fun e => (nomatch e), fun e he => ?_, ist1, meas1⟩
    · unfold Zlib.Infback.PULLBYTE
      rw [runX_bind, run1]
    · injection he with he; subst he; exact ⟨rfl, ret⟩
  | ok u =>
    obtain ⟨hne, bitsEq, holdEq, putEq, leftEq, -, lastEq⟩ := okc rfl
    have same : runX (Zlib.Infback.PULLBYTE c) l h = runX (Zlib.Infback.PULLBYTE c) l1 h1 := by
      unfold Zlib.Infback.PULLBYTE
      rw [runX_bind, runX_bind, run1, PULL_have hne]
    rw [same, PULLBYTE_c_eq c hne]
    have B := bitInv_of I1
    have room1 : l1.bits.toNat ≤ 31 := by rw [bitsEq]; exact room
    obtain ⟨le, next⟩ := I1.chunk
    have haveNat : l1.have_.toNat ≠ 0 := fun e => hne (UInt32.toNat_inj.mp (by rw [e]; rfl))
    cases hbs : log1.held.drop (log1.held.length - l1.have_.toNat) with
    | nil =>
      exfalso
      have := congrArg List.length hbs
      simp at this
      omega
    | cons b rest =>
      rw [hbs] at B
      obtain ⟨nx, run2, B2, -, bits2⟩ := Zlib.Inflate.Proofs.PULLBYTE_succ B (by omega)
      obtain ⟨ref, a, off0, ptr0, get0, size0, bytes0⟩ := B.next.resolve_left (by simp)
      have hsz : off0 + rest.length + 1 ≤ a.size := by simp at size0; omega
      have head : a[off0]'(by omega) = b := by
        have := Zlib.Inflate.Proofs.take_succ_drop a off0 rest.length hsz
        simp only [List.length_cons] at bytes0
        rw [this] at bytes0
        injection bytes0 with e _
        exact e.symm
      have run3 := Zlib.Infback.Proofs.PULLBYTE_nx (b := b) hne ptr0 get0 (by omega) head (by omega)
      rw [run2] at run3
      have nxEq : nx = .ref ref (off0 + 1) := by
        have := congrArg (fun x => match x with | .ok ((_, l), _) => l.next | .error _ => .null) run3
        simpa [Zlib.Inflate.Proofs.pulled] using this
      subst nxEq
      refine ⟨.ok (), Zlib.Inflate.Proofs.pulled l1 b (.ref ref (off0 + 1)), h1, log1, run2,
        { I1 with put := ?_, chunk := ⟨?_, ?_⟩, bits := ⟨?_, B2.hold_lt⟩ },
        fun _ => ⟨by rw [bits2, bitsEq], putEq, leftEq, by
          rw [← bitsEq, ← holdEq]; exact pulled_hold_mod l1 b _ room1 I1.bits.2, lastEq⟩,
        fun e he => (nomatch he), ist1, ?_⟩
      · exact I1.put
      · show (l1.have_ - 1).toNat ≤ log1.held.length
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
        simp; omega
      · intro _
        show Ptr.ref ref (off0 + 1) = advance log1.active (log1.held.length - (l1.have_ - 1).toNat)
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
        have nx1 := next hne
        rw [ptr0] at nx1
        cases act : log1.active with
        | null => rw [act] at nx1; cases nx1
        | ref ref' o =>
          rw [act] at nx1
          injection nx1 with e1 e2
          subst e1
          simp only [advance, UInt32.toNat_one]
          congr 1
          omega
      · rw [bits2]; omega
      · unfold backMeasure
        unfold backMeasure at meas1
        simp only [Zlib.Inflate.Proofs.pulled]
        rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
        have bits8 : (l1.bits + 8).toNat = l1.bits.toNat + 8 := by
          rw [UInt32.toNat_add]; simp; omega
        rw [bits8]
        simp only [UInt32.toNat_one]
        omega

/-- **`NEEDBITS(k)` on the invariant**, for `k ≤ 32`: at least `k` bits held, or the call leaves
with `Z_BUF_ERROR`. -/
theorem NEEDBITS_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (k : UInt32) (hk : k.toNat ≤ 32)
    (I : PInv c pr h0 h l log) :
    ∃ res l' h' log', runX (Zlib.Infback.NEEDBITS c k) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → k.toNat ≤ l'.bits.toNat ∧ l'.put = l.put ∧ l'.left = l.left ∧
        l'.bits.toNat ≤ max l.bits.toNat (k.toNat + 7)) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧ h'.istates i = h.istates i ∧
      backMeasure pr h' l' log' ≤ backMeasure pr h l log := by
  let start := backMeasure pr h l log
  let Inv : IL → Heap → Prop := fun l' h' => ∃ log', PInv c pr h0 h' l' log' ∧ l'.put = l.put ∧
    l'.left = l.left ∧ h'.istates i = h.istates i ∧ backMeasure pr h' l' log' ≤ start ∧
    l'.bits.toNat ≤ max l.bits.toNat (k.toNat + 7)
  let Q : Except Ex Unit → IL → Heap → Prop := fun res l' h' => ∃ log', PInv c pr h0 h' l' log' ∧
    (res = .ok () → k.toNat ≤ l'.bits.toNat ∧ l'.put = l.put ∧ l'.left = l.left ∧
      l'.bits.toNat ≤ max l.bits.toNat (k.toNat + 7)) ∧
    (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧ h'.istates i = h.istates i ∧
    backMeasure pr h' l' log' ≤ start
  have loop := Zlib.Infback.Proofs.xwhileBrk_wf (cond := do return (← get).bits < k)
    (body := do Zlib.Infback.PULLBYTE c; pure false) Inv Q (fun l' _ => k.toNat - l'.bits.toNat)
    (by
      intro l1 h1 ⟨log1, I1, put1, left1, ist1, meas1, mx1⟩
      refine ⟨l1, h1, decide (l1.bits < k), by simp [runX_bind, runX_get, runX_pure], ?_, ?_⟩
      · intro lt
        have lt' : l1.bits.toNat < k.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true lt)
        obtain ⟨res2, l2, h2, log2, run2, I2, okc, errc, ist2, meas2⟩ := PULLBYTE_p c pr I1 (by omega)
        cases res2 with
        | error e =>
          refine ⟨.error e, l2, h2, by rw [runX_bind, run2], ⟨log2, I2, fun x => (nomatch x), errc, ist2.trans ist1, by omega⟩⟩
        | ok u =>
          obtain ⟨bits2, put2, left2, -, -⟩ := okc rfl
          refine ⟨.ok false, l2, h2, by rw [runX_bind, run2]; rfl, ⟨⟨log2, I2, put2.trans put1, left2.trans left1,
            ist2.trans ist1, by omega, by omega⟩, by omega⟩⟩
      · intro ge
        have ge' : k.toNat ≤ l1.bits.toNat := by
          have : ¬ l1.bits < k := fun x => by simp [x] at ge
          exact Nat.le_of_not_lt (fun x => this (UInt32.lt_iff_toNat_lt.mpr x))
        exact ⟨log1, I1, fun _ => ⟨ge', put1, left1, mx1⟩, fun e x => (nomatch x), ist1, meas1⟩)
    ⟨log, I, rfl, rfl, rfl, Nat.le_refl _, by omega⟩ (by unfold fuel; omega)
  obtain ⟨res, l', h', run, log', I', okc, errc, ist, meas⟩ := loop
  exact ⟨res, l', h', log', run, I', okc, errc, ist, meas⟩

end Zlib.Infback.Safety
