import ZlibF.Proof.«inflate.c.call-default»
import ZlibF.Proof.«inflate.c.sync-invariant»
import ZlibF.Proof.«inflate.c.stored-call»
import ZlibF.Proof.«inflate.c.fast-writeback-frame»
import ZlibF.Proof.«inflate.c.output-frame-local-cleanup»
import ZlibF.Proof.«inflate.c.live-frame-leave»
import ZlibF.Proof.«inflate.c.sync-default-public»

/-!
# inflate.c: the refused call

A null output pointer, null input with input pending, or a decoder in `SYNC`
makes `inflate` return `Z_STREAM_ERROR`. The first two are refused by the
entry check; `SYNC` reaches the mode switch, whose default case returns
`Z_STREAM_ERROR` before any state write. In every case the only heap change is
the local `hbuf` array, which is created and freed again. The stream and the
decoder are unchanged, and the call satisfies every clause of `Goal.inflate`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `SYNC` falls to the default case of the mode switch. -/
theorem inflate_dispatch_SYNC {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = SYNC) :
    runX (inflate_dispatch c) l h = .ok ((.error (.ret Z_STREAM_ERROR), l), h) := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
    LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC]
  all_goals rfl

/-- The loop of a call that starts in `SYNC` returns `Z_STREAM_ERROR` and
writes nothing. -/
theorem inflate_run_SYNC {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (mode : s.mode = SYNC) :
    ∃ regs, runX (inflate_run c) IL.init h = .ok ((.error (.ret Z_STREAM_ERROR), regs), h) := by
  unfold inflate_run
  rw [runX_bind, runX_rdS E]
  simp only [mode]
  change ∃ regs, runX (do
    LOAD c.strm c.st
    modify fun l => { l with in_ := l.have_, out_ := l.left, ret := Z_OK }
    xwhile (pure true) (inflate_dispatch c)) IL.init h = _
  rw [runX_bind, LOAD_run E]
  simp only []
  rw [runX_bind, runX_modify]
  simp only []
  refine ⟨_, xwhile_run_chain (inflate_dispatch c) (fun _ => _) (fun _ => h) 0 (by decide)
    (.ret Z_STREAM_ERROR) _ h (fun j small => absurd small (Nat.not_lt_zero j))
    (inflate_dispatch_SYNC E _ mode)⟩

/-- The local array is the only change, and it is gone again. -/
theorem byte_view_tmpFreed {h : Heap} (fresh : Fresh h) (ref : BRef) :
    Space.get (tmpFreed h) ref = Space.get h ref := by
  cases ref with
  | blk b =>
    by_cases same : b = h.nextBlk
    · subst b
      have absent := (fresh_dead fresh (Nat.le_refl h.nextBlk)).1
      simp only [Space.get, tmpFreed, freeWin, syncBuf, upd_same, absent]
    · simp only [Space.get, tmpFreed, freeWin, syncBuf, syncAlloc, upd_ne _ _ _ _ same]
  | dstate_depth i => simp only [Space.get, tmpFreed, freeWin, syncBuf, syncAlloc]
  | str _ | st_dist_code | st_length_code => rfl

/-- The refused call runs to `Z_STREAM_ERROR` on the heap with the local
array made and freed. -/
theorem inflate_refused_run {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) (flush : Int32)
    (refused : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC) :
    C.run (inflate (some r) flush) h = .ok (Z_STREAM_ERROR, tmpFreed h) := by
  have allocated := current.sync_alloc
  unfold C.run inflate
  rw [bind_app, allocLocalB_run h current.good.fresh]
  simp only []
  rw [bind_app]
  by_cases entry : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
  · simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, entry, ite_true, pure_app]
    dsimp only [syncBuf]
    rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    rfl
  · have sync : s.mode = SYNC := by
      rcases refused with output | ⟨input, pending⟩ | sync
      · exact absurd (by simp [output]) entry
      · exact absurd (by simp [input, pending]) entry
      · exact sync
    have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      simpa using entry
    let c : Ctx := ⟨some r, some (.tab i), syncBuf h, flush⟩
    have env : Env c (syncAlloc h) r i z s :=
      ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
    obtain ⟨regs, loop⟩ := inflate_run_SYNC env sync
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
    unfold runX at loop
    dsimp only [c] at loop
    erw [loop]
    simp only []
    change (do freeB (syncBuf h); pure Z_STREAM_ERROR) (syncAlloc h) = .ok (Z_STREAM_ERROR, tmpFreed h)
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    rfl

/-- Entry refusal: a NULL output pointer, NULL input with pending input,
or a decoder in `SYNC` returns `Z_STREAM_ERROR`; the stream and decoder are
unchanged and only the local array was made and freed. -/
theorem inflate_call_refused {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) (caller : CallPremises h r) (flush : Int32)
    (refused : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC) :
    InflateCall h r i z s flush := by
  have fresh := current.good.fresh
  have views := byte_view_tmpFreed fresh
  have next : InflateInv (tmpFreed h) r i z s :=
    current.sync_alloc.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
  have shape := sync_tmp_freed_shape fresh
  have accounting : StreamAccounting z z 0 ([] : List UInt8).length := by
    refine ⟨Nat.zero_le _, Nat.zero_le _, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · cases z.next_in <;> rfl
    · cases z.next_out <;> rfl
  have observed : Bytes (tmpFreed h) z.next_out ([] : List UInt8).length [] := by
    cases pointer : z.next_out with
    | null => exact Or.inl ⟨rfl, rfl, rfl⟩
    | ref ref off =>
      obtain ⟨stream, get, _, output, _⟩ := caller.buffers
      have same : stream = z := Option.some.inj (get.symm.trans current.good.live.hz)
      subst stream
      rcases output with nullOut | ⟨_, writable, _⟩
      · rw [pointer] at nullOut
        cases nullOut
      · rcases writable rfl with nullOut | ⟨ref', off', array, same, arrayGet, _, room⟩
        · rw [pointer] at nullOut
          cases nullOut.1
        · rw [pointer] at same
          cases same
          exact Or.inr ⟨ref, off, array, rfl, (views ref).trans arrayGet, by simp only [List.length_nil]; omega,
            by simp⟩
  have frame : Frame h (tmpFreed h)
      (fun b => StreamRoot r b ∨ InflateOwned i s b ∨ s.head = some (.tab b)) := by
    have base : Frame (syncAlloc h) (syncAlloc h)
        (fun b => StreamRoot r b ∨ InflateOwned i s b ∨ s.head = some (.tab b)) := by
      refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro b _ _
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact frame_cancel_local fresh base
  refine ⟨Z_STREAM_ERROR, tmpFreed h, z, s, 0, [], inflate_refused_run current flush refused,
    next, accounting, observed, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
    fun e => absurd e (by decide), ⟨fun _ => refused, fun _ => rfl⟩,
    fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun e => absurd e (by decide),
    fun _ _ _ _ e => absurd e (by decide), fun e => absurd e (by decide),
    fun e => absurd e (by decide), fun e => absurd e (by decide), fun e => absurd e (by decide),
    fun e => by rcases e with e | e | e | e <;> exact absurd e (by decide), ⟨?_, ?_⟩, ?_⟩
  · rw [restoreRegions_unchanged views]
    exact frame
  · intro region _ ref off array _ get
    exact ⟨array, (views ref).trans get, rfl, fun _ _ _ => rfl⟩
  · intro b
    rw [shape.live b]
    constructor
    · intro live
      exact Or.inl ⟨live, id⟩
    · rintro (⟨live, _⟩ | ⟨owned, _⟩)
      · exact live
      · exact good_inflate_owned_live current.good owned

#print axioms inflate_call_refused
end Zlib.Inflate.Proofs
