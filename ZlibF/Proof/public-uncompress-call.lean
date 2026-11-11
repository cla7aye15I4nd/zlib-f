import ZlibF.Proof.«public-uncompress-step»
import ZlibF.Proof.«inflate.c.borrow-stable-run»

/-!
# uncompr.c: the `inflate` call of one iteration

After the refills the loop calls `inflate(&stream, Z_NO_FLUSH)`. From the decoder
facts, the call either continues the run (`Z_OK`, with the loop state kept and less
work left) or ends it with the data the cleanup and the data relation need.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Uncompr
open Zlib.Inflate (inflate)
set_option autoImplicit false

/-- The end of the run: the last call and the state after it. -/
structure Final (e : Env) (l : UncLoop) (rc : Int32) (Hp H : Heap) (logp : DataLog)
    (input output : List UInt8) (u i : Nat) (zp z : ZStream) (sp s : InflateState) : Prop where
  pre : State e l Hp logp i zp sp
  step : DataStep .inflate Hp H e.r Z_NO_FLUSH rc input output u
  input_eq : input = (e.src.drop logp.input.length).take zp.avail_in.toNat
  used_le : u ≤ zp.avail_in.toNat
  reach : StreamReachable .inflate H e.r
  fit : ZlibF.PlatformMemory.ByteObjectsFit H
  good : Zlib.Inflate.Spec.Good H e.r i z s
  alloc : Zlib.Inflate.Spec.DefAlloc z
  inCount : logp.input.length + u + z.avail_in.toNat + l.len.toNat = e.n
  outCount : (logp.output ++ output).length + z.avail_out.toNat + l.left.toNat = e.cap
  agree : Agree e.h₀.live (writeOut e.h₀ e.out0 (logp.output ++ output)) H
  notOwned : ∀ b, e.h₀.live b ∨ b = e.k ∨ b = e.k + 1 → ¬ InflateOwned i s b
  liveOnly : ∀ b, H.live b → e.h₀.live b ∨ b = e.k ∨ b = e.k + 1 ∨ InflateOwned i s b
  reservedBytes : H.bytes (e.k + 1) = some (reservedBytes e.h₀)
  reservedRo : H.ro (e.k + 1) = false
  globals : LibraryGlobals H
  nalloc : e.h₀.nalloc ≤ H.nalloc
  codes : rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨ rc = Z_BUF_ERROR
  buf : rc = Z_BUF_ERROR → z.avail_in.toNat + l.len.toNat = 0 ∨
    ((logp.output ++ output).length = e.cap ∧ z.avail_in ≠ 0)
  mem : rc = Z_MEM_ERROR → AllocationFailed e.h₀ H

theorem not_streamOwned {H : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState} {b : Nat}
    (g : Zlib.Inflate.Spec.Good H r i z s) (n : ¬ InflateOwned i s b) : ¬ StreamOwned H r b := by
  rintro ⟨z', hz', own⟩
  have ez : z' = z := Option.some.inj (hz'.symm.trans g.live.hz)
  subst ez
  rcases own with ⟨i', s', hst, his, o⟩ | ⟨i', s', hst, -, -⟩
  · rw [g.live.zst] at hst
    cases hst
    rw [g.live.hs] at his
    cases his
    exact n o
  · rw [g.live.zst] at hst
    cases hst

theorem streamOwned_of {H : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState} {b : Nat}
    (g : Zlib.Inflate.Spec.Good H r i z s) (o : StreamOwned H r b) : InflateOwned i s b := by
  obtain ⟨z', hz', own⟩ := o
  have ez : z' = z := Option.some.inj (hz'.symm.trans g.live.hz)
  subst ez
  rcases own with ⟨i', s', hst, his, o⟩ | ⟨i', s', hst, -, -⟩
  · rw [g.live.zst] at hst
    cases hst
    rw [g.live.hs] at his
    cases his
    exact o
  · rw [g.live.zst] at hst
    cases hst

/-- The blocks a pointer reads through are its view's blocks. -/
theorem byteRoot_block {r : BRef} {i b : Nat} (h : ByteRoot (.ref r i) b) : BRef.block r = some b := by
  cases r <;> simp_all [ByteRoot, BRef.block]

/-- The error field does not enter the loop state. -/
theorem State.setErr {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat} {z : ZStream}
    {s : InflateState} (st : State e l H log i z s) (x : Int32) :
    State e { l with err := x } H log i z s :=
  { trace := st.trace, single := st.single, dict := st.dict, reach := st.reach, fit := st.fit,
    good := st.good, alloc := st.alloc, noSync := st.noSync, noMem := st.noMem, head := st.head,
    globals := st.globals, inTake := st.inTake, inCount := st.inCount, nextIn := st.nextIn,
    outCount := st.outCount, nextOut := st.nextOut, agree := st.agree, notOwned := st.notOwned,
    liveOnly := st.liveOnly, reservedBytes := st.reservedBytes, reservedRo := st.reservedRo,
    noOver := st.noOver, nalloc := st.nalloc }

/-- A caller block is live in a heap that agrees with the written caller heap. -/
theorem State.callerLive {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat} {z : ZStream}
    {s : InflateState} (st : State e l H log i z s) {b : Nat} (live : e.h₀.live b) : H.live b := by
  have el : (writeOut e.h₀ e.out0 log.output).live b := (writeOut_live b).2 live
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := st.agree.blocks b live
  simp only [Heap.live] at el ⊢
  rw [s1, s2, s3, s4, s5, s6, s7]; exact el

theorem advance_ne_null {p : BPtr} (n : Nat) (h : p ≠ .null) : advance p n ≠ .null := by
  cases p with
  | null => exact absurd rfl h
  | ref r i => simp [advance]

theorem advance_null_iff {p : BPtr} (n : Nat) : advance p n = .null ↔ p = .null := by
  cases p <;> simp [advance]

theorem put_globals_writeOut (h : Heap) (p : BPtr) (xs : List UInt8) :
    (writeOut h p xs).static = h.static ∧ (writeOut h p xs).allocOk = h.allocOk := by
  unfold writeOut
  split
  · split
    · split
      · exact ⟨rfl, rfl⟩
      · exact ⟨(put_globals _ _ _).1, (put_globals _ _ _).2.1⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem put_nalloc (X : Heap) (r : BRef) (a : Array UInt8) : (Space.put X r a).nalloc = X.nalloc := by
  cases r with
  | dstate_depth b => simp only [Space.put]; split <;> rfl
  | _ => rfl

theorem restore_nalloc (H H' : Heap) (p : BPtr) (n : Nat) :
    (restoreRegions H H' [⟨p, n⟩]).nalloc = H'.nalloc := by
  rw [restore_one]
  cases p with
  | null => rfl
  | ref r i =>
    simp only []
    split
    · rfl
    · exact put_nalloc _ _ _

/-- A call frame keeps a live unchanged block that it does not write. -/
theorem frame_keeps_block {H H' : Heap} {changed : Nat → Prop} {p : BPtr} {out : List UInt8} {b : Nat}
    (frame : BufferFrame H H' changed [⟨p, out.length⟩]) (live : H.live b) (unchanged : ¬ changed b)
    (notWritten : ∀ r i, p = .ref r i → BRef.block r = some b → out = []) : SameAt H H' b := by
  obtain ⟨⟨-, -, -, -, -, fb⟩, part⟩ := frame
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := fb b live unchanged
  have restored : SameAt H (restoreRegions H H' [⟨p, out.length⟩]) b := ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩
  rw [restore_one] at restored
  cases p with
  | null => exact restored
  | ref rr off =>
    simp only [] at restored
    cases g : Space.get H rr with
    | none => rw [g] at restored; exact restored
    | some aH =>
      rw [g] at restored
      simp only [] at restored
      obtain ⟨a', g', size, same⟩ := part ⟨Ptr.ref rr off, out.length⟩ (List.mem_singleton_self _) rr off aH rfl g
      have H'eq : Space.put (Space.put H' rr aH) rr a' = H' := by rw [put_put_any, put_self_any g']
      by_cases blockB : BRef.block rr = some b
      · have e := notWritten rr off rfl blockB
        subst e
        have arr : a' = aH := by
          apply Array.ext size
          intro j h1 h2
          have := same j h2 (by
            rintro ⟨reg, mem, ⟨o, -, lo, hi⟩⟩
            simp only [List.mem_singleton] at mem
            subst mem
            simp only [List.length_nil] at hi
            omega)
          rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at this
          exact Option.some.inj this
        rw [arr] at H'eq
        rw [← H'eq, put_put_any]
        exact restored
      · have t := SameAt.put_other (Space.put H' rr aH) a' blockB
        rw [H'eq] at t
        exact restored.trans t

/-- The caller ranges of one call: the source piece and the room. -/
theorem call_ranges {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat}
    {z : ZStream} {s : InflateState} (ok : EnvOK e) (st : State e l H log i z s) :
    Bytes H z.next_in z.avail_in.toNat ((e.src.drop log.input.length).take z.avail_in.toNat) ∧
    (∀ r j, z.next_in = .ref r j → ∀ c, BRef.block r = some c → e.h₀.live c) ∧
    Writable H z.next_out z.avail_out.toNat ∧
    (∀ r j, z.next_out = .ref r j → ∀ c, BRef.block r = some c → e.h₀.live c ∨ c = e.k + 1) ∧
    Separate z.next_in z.avail_in.toNat z.next_out z.avail_out.toNat ∧
    (log.output ≠ [] ∨ z.avail_out ≠ 0 → Writable e.h₀ e.out0 e.cap) := by
  have inC := st.inCount
  have outC := st.outCount
  have srcPart : Bytes e.h₀ (advance e.source log.input.length) z.avail_in.toNat
      ((e.src.drop log.input.length).take z.avail_in.toNat) :=
    bytes_sub ok.srcBytes (by omega)
  have srcBlocks : ∀ r j, advance e.source log.input.length = .ref r j →
      ∀ c, BRef.block r = some c → e.h₀.live c := by
    intro r j hp c hc
    rcases ok.srcBytes with ⟨hs, -, -⟩ | ⟨r', i', a, hs, g, -, -⟩
    · rw [hs] at hp; cases hp
    · rw [hs] at hp
      simp only [advance] at hp
      cases hp
      exact view_block_live g c hc
  rw [st.nextIn, st.nextOut]
  rcases ok.outW with ⟨res, cap0⟩ | W
  · have p0 : log.output = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ao0 : z.avail_out.toNat = 0 := by omega
    have agree := st.agree
    rw [p0, writeOut_nil] at agree
    refine ⟨agree.bytes srcPart srcBlocks, srcBlocks, ?_, ?_, Or.inr (Or.inl ao0), ?_⟩
    · rw [ao0, p0, res]
      exact Or.inr ⟨.blk (e.k + 1), 0, reservedBytes e.h₀, by simp [advance], st.reservedBytes,
        st.reservedRo, by simp [reservedBytes]⟩
    · intro r j hp c hc
      rw [p0, res] at hp
      simp only [List.length_nil, advance, Nat.add_zero, Ptr.ref.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      simp only [BRef.block, Option.some.injEq] at hc
      exact Or.inr hc.symm
    · intro h
      rcases h with h | h
      · exact absurd p0 h
      · exact absurd (UInt32.toNat_inj.mp (by simpa using ao0)) h
  · have sepIn : Separate (advance e.source log.input.length) z.avail_in.toNat e.out0 e.cap := by
      have := separate_sub (c := log.input.length) (d := 0) (n' := z.avail_in.toNat) (m' := e.cap)
        ok.sep (by omega) (by omega)
      rwa [advance_zero] at this
    have srcE := bytes_writeOut_sep (xs := log.output) srcPart sepIn (by omega) W
    have outBlocks : ∀ r j, e.out0 = .ref r j → ∀ c, BRef.block r = some c → e.h₀.live c := by
      intro r j hp c hc
      rcases W with ⟨h0, -⟩ | ⟨r', j', a, hq, g, -, -⟩
      · exact absurd h0 ok.outNotNull
      · rw [hq] at hp; cases hp; exact view_block_live g c hc
    have advBlocks : ∀ r j, advance e.out0 log.output.length = .ref r j → ∀ c, BRef.block r = some c →
        e.h₀.live c := by
      intro r j hp c hc
      cases h0 : e.out0 with
      | null => exact absurd h0 ok.outNotNull
      | ref r' j' =>
        rw [h0] at hp
        simp only [advance, Ptr.ref.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        exact outBlocks r' j' h0 c hc
    have wOut : Writable e.h₀ (advance e.out0 log.output.length) z.avail_out.toNat :=
      writable_sub W (by omega)
    have wE := writable_writeOut (xs := log.output) wOut (by omega) W
    refine ⟨st.agree.bytes srcE srcBlocks, srcBlocks, st.agree.writable wE advBlocks,
      fun r j hp c hc => Or.inl (advBlocks r j hp c hc), separate_sub ok.sep (by omega) (by omega),
      fun _ => W⟩

/-- One call after the refills. -/
theorem call_phase (facts : DecoderFacts) {e : Env} {l : UncLoop} {H : Heap} {log : DataLog} {i : Nat}
    {z : ZStream} {s : InflateState} (ok : EnvOK e) (st : State e l H log i z s)
    (fullIn : z.avail_in = 0 → l.len = 0) (fullOut : z.avail_out = 0 → l.left = 0) :
    ∃ rc H', C.run (inflate (some e.r) Z_NO_FLUSH) H = .ok (rc, H') ∧
      (rc = Z_OK → ∃ log' z' s', State e { l with err := rc } H' log' i z' s' ∧
        measure e { l with err := rc } H' < measure e l H) ∧
      (rc ≠ Z_OK → ∃ input output u z' s', Final e { l with err := rc } rc H H' log input output u i z z' s s') := by
  obtain ⟨srcH, srcBlocks, outW, outBlocks, sepIO, outW0⟩ := call_ranges ok st
  have k0 : ¬ e.h₀.live e.k := ok.fresh e.k (Nat.le_refl _)
  have k1 : ¬ e.h₀.live (e.k + 1) := ok.fresh (e.k + 1) (Nat.le_succ _)
  -- the arguments of the call
  have notOwnedRoot : ∀ (q : BPtr), (∀ r j, q = .ref r j → ∀ c, BRef.block r = some c →
      e.h₀.live c ∨ c = e.k + 1) → ∀ b, ByteRoot q b → ¬ StreamOwned H e.r b := by
    intro q blocks b root
    apply not_streamOwned st.good
    apply st.notOwned
    cases q with
    | null => cases root
    | ref r j =>
      rcases blocks r j rfl b (byteRoot_block root) with x | x
      · exact Or.inl x
      · exact Or.inr (Or.inr x)
  have buffers : StreamBuffers H e.r := by
    refine ⟨z, st.good.live.hz, ?_, ?_, sepIO⟩
    · exact Or.inr ⟨⟨_, srcH⟩, (fun h => absurd h (by decide)),
        notOwnedRoot z.next_in (fun r j hp c hc => Or.inl (srcBlocks r j hp c hc))⟩
    · rcases outW with ⟨h0, -⟩ | ⟨r, j, a, hq, g, ro, fit⟩
      · exact Or.inl h0
      · refine Or.inr ⟨⟨_, Or.inr ⟨r, j, a, hq, g, fit, rfl⟩⟩, fun _ => Or.inr ⟨r, j, a, hq, g, ro, fit⟩,
          notOwnedRoot z.next_out outBlocks⟩
  have active : ActiveHeader H e.r := by
    refine ⟨z, st.good.live.hz, ?_, ?_⟩
    · intro i' s' hst his
      left
      rw [st.good.live.zst] at hst
      cases hst
      rw [st.good.live.hs] at his
      cases his
      exact st.head
    · intro i' s' hst
      rw [st.good.live.zst] at hst
      cases hst
  obtain ⟨rc, H', z', s', u, out, run, good', acc, written, codes, progress, sErr, sErrEq, bufCl, progCl,
      endMode, dictMode, dataMode, memCl, totals, frame, live⟩ :=
    facts.call H e.r i z s Z_NO_FLUSH st.reach st.good st.fit st.alloc buffers active
  obtain ⟨aU, aO, aIn, aOut, aNextIn, aNextOut, aState, aZalloc, aZfree, aOpaque, aRes⟩ := acc
  simp only [st.head, HeaderRegions] at frame
  have hz' : e.r.get H' = some z' := good'.live.hz
  -- the observed call
  have dstep : DataStep .inflate H H' e.r Z_NO_FLUSH rc ((e.src.drop log.input.length).take z.avail_in.toNat)
      out u := ⟨z, z', st.good.live.hz, hz', buffers, active, srcH, by omega,
        by rw [show z.avail_out.toNat - z'.avail_out.toNat = out.length by omega]; exact written, run⟩
  have exec : Call.execute (.inflate (some e.r) Z_NO_FLUSH) default H = .ok ((rc, default), H') := by
    simp [Call.execute, heapCall, C.run] at run ⊢
    rw [run]
  have reach' : StreamReachable .inflate H' e.r :=
    StreamReachable.step (call := .inflate (some e.r) Z_NO_FLUSH) st.reach (fun _ => st.fit) ⟨rfl, rfl⟩
      ⟨buffers, active⟩ exec
  obtain ⟨noSync', memRc, head', keepOwn, newOwn⟩ :=
    facts.control H e.r i z s Z_NO_FLUSH rc H' z' s' st.reach st.good run good'
  have borrow : H'.libcErrorBorrow = H.libcErrorBorrow :=
    Zlib.Inflate.BorrowProofs.stable_inflate (some e.r) Z_NO_FLUSH H rc H' run
  have inC := st.inCount
  have outC := st.outCount
  -- the caller heap after the call
  have outside : ∀ b, e.h₀.live b → ¬ (StreamRoot e.r b ∨ InflateOwned i s b) := by
    intro b live ch
    rcases ch with ch | ch
    · simp only [StreamRoot, Env.r] at ch
      exact k0 (by rw [Env.k, ← ch]; exact live)
    · exact st.notOwned b (Or.inl live) ch
  have frame1 : BufferFrame H H' (fun b => StreamRoot e.r b ∨ InflateOwned i s b)
      [⟨z.next_out, out.length⟩] := by simpa using frame
  have outLe : out.length ≤ z.avail_out.toNat := by omega
  have wOutE : out ≠ [] → Writable (writeOut e.h₀ e.out0 log.output) z.next_out out.length := by
    intro ne
    have W := outW0 (Or.inr (by
      intro h0; rw [h0] at outLe; exact ne (List.eq_nil_of_length_eq_zero (by simpa using outLe))))
    rw [st.nextOut]
    exact writable_writeOut (writable_sub W (by omega)) (by omega) W
  have agreeE := agree_after_call st.agree (fun b live => (writeOut_live b).2 live)
    (fun b live => (writeOut_live b).1 live) outside frame1 written wOutE borrow
  have agree' : Agree e.h₀.live (writeOut e.h₀ e.out0 (log.output ++ out)) H' := by
    by_cases ne : out = []
    · subst ne; simpa [writeOut_nil] using agreeE
    · have W := outW0 (Or.inr (by
        intro h0; rw [h0] at outLe; exact ne (List.eq_nil_of_length_eq_zero (by simpa using outLe))))
      have W2 : Writable e.h₀ e.out0 (log.output.length + out.length) := by
        have := writable_sub (c := 0) (m := log.output.length + out.length) W (by omega)
        rwa [advance_zero] at this
      rw [← writeOut_append W2, ← st.nextOut]
      exact agreeE
  -- the reserved block is not written
  have resLive : H.live (e.k + 1) := Or.inl (by rw [st.reservedBytes]; simp)
  have resKeep : SameAt H H' (e.k + 1) := by
    refine frame_keeps_block frame1 resLive ?_ ?_
    · rintro (ch | ch)
      · simp only [StreamRoot, Env.r] at ch; simp [Env.k] at ch
      · exact st.notOwned (e.k + 1) (Or.inr (Or.inr rfl)) ch
    · intro r j hp hb
      rcases ok.outW with ⟨res, cap0⟩ | W
      · have : z.avail_out.toNat = 0 := by omega
        exact List.eq_nil_of_length_eq_zero (by omega)
      · exfalso
        rcases W with ⟨h0, -⟩ | ⟨r', j', a, hq, g, -, -⟩
        · exact ok.outNotNull h0
        · rw [st.nextOut, hq] at hp
          simp only [advance, Ptr.ref.injEq] at hp
          obtain ⟨rfl, -⟩ := hp
          exact k1 (view_block_live g _ hb)
  -- ownership and liveness
  have ownLive : ∀ b, e.h₀.live b ∨ b = e.k ∨ b = e.k + 1 → H.live b := by
    intro b h
    rcases h with h | h | h
    · exact st.callerLive h
    · subst h
      have hz : H.streams e.k = some z := st.good.live.hz
      exact Or.inr (Or.inr (Or.inl (by rw [hz]; simp)))
    · subst h; exact resLive
  have notOwned' : ∀ b, e.h₀.live b ∨ b = e.k ∨ b = e.k + 1 → ¬ InflateOwned i s' b := by
    intro b h own
    rcases newOwn b own with o | o
    · exact st.notOwned b h o
    · exact o (ownLive b h)
  have liveOnly' : ∀ b, H'.live b → e.h₀.live b ∨ b = e.k ∨ b = e.k + 1 ∨ InflateOwned i s' b := by
    intro b lb
    rcases (live b).1 lb with ⟨lh, -⟩ | ⟨o, -⟩
    · rcases st.liveOnly b lh with x | x | x | x
      · exact Or.inl x
      · exact Or.inr (Or.inl x)
      · exact Or.inr (Or.inr (Or.inl x))
      · exact Or.inr (Or.inr (Or.inr (keepOwn b x)))
    · exact Or.inr (Or.inr (Or.inr o))
  have globals' : LibraryGlobals H' := by
    have a1 := agree'.static
    have a2 := st.agree.static
    have g0 := st.globals
    simp only [LibraryGlobals] at g0 ⊢
    rw [a1, (put_globals_writeOut _ _ _).1]
    rw [a2, (put_globals_writeOut _ _ _).1] at g0
    exact g0
  have nalloc' : e.h₀.nalloc ≤ H'.nalloc := by
    have := frame1.1.2.2.2.2.1
    rw [restore_nalloc] at this
    exact Nat.le_trans st.nalloc this
  -- consumption
  have srcLen := ok.srcLen
  have inTake' : log.input ++ ((e.src.drop log.input.length).take z.avail_in.toNat).take u =
      e.src.take (log.input.length + u) := by
    rw [List.take_take, Nat.min_eq_left aU, List.take_add, ← st.inTake]
  have given : log.input ++ (e.src.drop log.input.length).take z.avail_in.toNat <+: e.src := by
    have e1 : log.input ++ (e.src.drop log.input.length).take z.avail_in.toNat =
        e.src.take (log.input.length + z.avail_in.toNat) := by
      conv => lhs; arg 1; rw [st.inTake]
      rw [← List.take_add]
    rw [e1]
    exact List.take_prefix _ _
  have within : ∀ m o, m ≤ e.src.length → Zlib.Decodes [] (e.src.take m) o →
      e.src.take (log.input.length + u) <+: e.src.take m ∧
      (e.src.take (log.input.length + u) = e.src.take m → rc = Z_STREAM_END ∨ rc = Z_MEM_ERROR) := by
    intro m o hm d
    have w := facts.within 15 .zlib 15 e.r H H' log false Z_NO_FLUSH rc _ out u (e.src.take m) o
      inflWbits_15 st.trace st.single (by rw [st.dict]; exact zlib_layer d) zlib_full (st.noOver m o hm d).1
      (List.prefix_or_prefix_of_prefix given (List.take_prefix m e.src)) dstep
    rw [inTake'] at w
    exact w
  have lenTake : (e.src.take (log.input.length + u)).length = log.input.length + u := by
    rw [List.length_take]; omega
  have trace' := InflateProtocolTrace.step st.trace st.fit dstep
  have alloc' : Zlib.Inflate.Spec.DefAlloc z' := by
    obtain ⟨h1, h2⟩ := st.alloc
    exact ⟨aZalloc ▸ h1, aZfree ▸ h2⟩
  have nextIn' : z'.next_in = advance e.source (e.src.take (log.input.length + u)).length := by
    rw [lenTake, aNextIn, st.nextIn, advance_add]
  have nextOut' : z'.next_out = advance e.out0 (log.output ++ out).length := by
    rw [aNextOut, st.nextOut, advance_add, List.length_append]
  refine ⟨rc, H', run, ?_, ?_⟩
  · -- the run continues
    intro rcOk
    subst rcOk
    have notDict : (Z_OK == Z_NEED_DICT) = false := by decide
    rw [notDict] at trace'
    refine ⟨{ log with
      input := log.input ++ ((e.src.drop log.input.length).take z.avail_in.toNat).take u
      output := log.output ++ out, result := Z_OK
      finished := log.finished || Z_OK == Z_STREAM_END }, z', s', ?_, ?_⟩
    · exact
        { trace := trace'
          single := st.single
          dict := st.dict
          reach := reach'
          fit := facts.size H e.r i z s Z_NO_FLUSH Z_OK H' st.reach st.good st.fit buffers active run
          good := good'
          alloc := alloc'
          noSync := noSync' st.noSync
          noMem := fun m => by
            rcases memRc m with x | x
            · exact absurd x (by decide)
            · exact st.noMem x
          head := head'.trans st.head
          globals := globals'
          inTake := by simp only []; rw [inTake', lenTake]
          inCount := by simp only []; rw [inTake', lenTake]; omega
          nextIn := by simp only []; rw [inTake']; exact nextIn'
          outCount := by simp only [List.length_append]; omega
          nextOut := nextOut'
          agree := agree'
          notOwned := notOwned'
          liveOnly := liveOnly'
          reservedBytes := by rw [resKeep.1]; exact st.reservedBytes
          reservedRo := by rw [resKeep.2.2.2.2.2.2.2]; exact st.reservedRo
          noOver := by
            intro m o hm d
            simp only []
            rw [inTake']
            obtain ⟨pre, eq⟩ := within m o hm d
            refine ⟨pre, fun h => ?_⟩
            rcases eq h with x | x <;> exact absurd x (by decide)
          nalloc := nalloc' }
    · have prog := (progress rfl).1
      simp only [measure, Env.r] at hz' ⊢
      have hz0 : (ZStreamRef.tab e.h₀.nextBlk).get H = some z := st.good.live.hz
      rw [hz', hz0]
      simp only []
      rcases prog with p | p
      · omega
      · have : out.length ≠ 0 := fun h => p (List.eq_nil_of_length_eq_zero h)
        omega
  · -- the run ends
    intro rcNe
    have notStreamError : rc ≠ Z_STREAM_ERROR := by
      intro he
      rcases sErr.1 he with h | ⟨h, ai⟩ | h
      · rw [st.nextOut] at h
        exact advance_ne_null _ ok.outNotNull h
      · rw [st.nextIn, advance_null_iff] at h
        have n0 : e.n = 0 := by
          rcases ok.srcBytes with ⟨-, n0, -⟩ | ⟨r, j, a, hs, -, -, -⟩
          · exact n0
          · rw [h] at hs; cases hs
        exact ai (UInt32.toNat_inj.mp (by simp; omega))
      · exact st.noSync h
    have codes' : rc = Z_STREAM_END ∨ rc = Z_NEED_DICT ∨ rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR ∨
        rc = Z_BUF_ERROR := by
      rcases codes with h | h | h | h | h | h | h
      · exact absurd h rcNe
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd h notStreamError
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    refine ⟨(e.src.drop log.input.length).take z.avail_in.toNat, out, u, z', s', ?_⟩
    exact
      { pre := st.setErr rc
        step := dstep
        input_eq := rfl
        used_le := aU
        reach := reach'
        fit := facts.size H e.r i z s Z_NO_FLUSH rc H' st.reach st.good st.fit buffers active run
        good := good'
        alloc := alloc'
        inCount := by simp only []; omega
        outCount := by simp only [List.length_append]; omega
        agree := agree'
        notOwned := notOwned'
        liveOnly := liveOnly'
        reservedBytes := by rw [resKeep.1]; exact st.reservedBytes
        reservedRo := by rw [resKeep.2.2.2.2.2.2.2]; exact st.reservedRo
        globals := globals'
        nalloc := nalloc'
        codes := codes'
        buf := by
          intro hb
          have none : u = 0 ∧ out = [] := by
            rcases bufCl hb with h | h
            · exact h
            · exact absurd h (by decide)
          obtain ⟨u0, o0⟩ := none
          subst o0
          by_cases zin : z.avail_in = 0
          · left
            have l0 : l.len.toNat = 0 := by rw [fullIn zin]; rfl
            have : z.avail_in.toNat = 0 := by rw [zin]; rfl
            simp only []
            omega
          · by_cases zout : z.avail_out = 0
            · right
              have := fullOut zout
              have l0 : l.left.toNat = 0 := by rw [this]; rfl
              have o0 : z.avail_out.toNat = 0 := by rw [zout]; rfl
              refine ⟨by simp only [List.append_nil]; omega, ?_⟩
              intro z0
              apply zin
              apply UInt32.toNat_inj.mp
              have : z'.avail_in.toNat = 0 := by rw [z0]; rfl
              simp only [UInt32.toNat_zero]
              omega
            · exfalso
              rcases progCl zin zout (by decide) (by decide) hb with h | h
              · exact h u0
              · exact h rfl
        mem := by
          intro hm
          obtain ⟨j, lo, hi, bad⟩ :=
            facts.mem H e.r i z s Z_NO_FLUSH H' st.reach st.good st.noMem (by rw [← hm]; exact run)
          refine ⟨j, Nat.le_trans st.nalloc lo, hi, ?_⟩
          rw [st.agree.allocOk, (put_globals_writeOut _ _ _).2] at bad
          exact bad }

end ZlibF.Spec.Public.Proofs.Uncompress
