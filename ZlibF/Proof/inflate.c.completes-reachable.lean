import ZlibF.Proof.«public-uncompress2-z»

/-!
# inflate.c: completion on a reachable heap within the object-size limit

`InflateCompletes` with two more premises on the heap of the call: an actual
stream history reaches it (`StreamReachable`), and every object fits the LP64
limit (`ByteObjectsFit`). `Goal.inflate` needs both. A protocol history does not
yet carry them; once it does, this theorem gives `InflateCompletes`. The decoder
facts (`DecoderFacts`) are explicit hypotheses.
-/

namespace Zlib.Inflate.Proofs
open C ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Public.Proofs.Uncompress
set_option autoImplicit false

/-- `InflateCompletes` on a reachable heap within the object-size limit. -/
def InflateCompletesReachable : Prop :=
  ∀ (wb : Int32) wrap bits r h log source decoded z i s (flush : Int32),
    Api.inflWbits wb.toInt = some (wrap, bits) → AllowedInflateProtocol wb r h log →
    StreamReachable .inflate h r → ZlibF.PlatformMemory.ByteObjectsFit h →
    log.singleDictionary = true → log.finished = false →
    Api.Layer.Decodes wrap bits log.dictionary source decoded → Api.FullWindow wrap bits source →
    log.input <+: source → Zlib.Inflate.Spec.Good h r i z s →
    s.mode ≠ BAD → s.mode ≠ MEM → s.mode ≠ SYNC → (s.mode = DICT → s.havedict ≠ 0) →
    StreamBuffers h r → ActiveHeader h r → NoAllocationFailure h →
    Bytes h z.next_in z.avail_in.toNat (source.drop log.input.length) →
    decoded.length ≤ log.output.length + z.avail_out.toNat →
    (flush = Z_NO_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FINISH) →
    ∃ rc after, C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) ∧
      ((rc = Z_STREAM_END ∧
        Bytes after z.next_out (decoded.length - log.output.length) (decoded.drop log.output.length)) ∨
       (rc = Z_NEED_DICT ∧ s.havedict = 0 ∧
        (wrap = .zlib ∨ wrap = .auto) ∧
        (∃ cmf flg tail, source = cmf :: flg :: tail ∧ Zlib.HeaderOK cmf flg ∧
          flg.toNat / 32 % 2 = 1) ∧
        ∃ z' i' s', Zlib.Inflate.Spec.Good after r i' z' s' ∧
          s'.mode = DICT ∧ s'.havedict = 0 ∧ z'.avail_out = z.avail_out) ∨
       (rc = Z_STREAM_ERROR ∧
        (z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0)) ∧
        Zlib.Inflate.Spec.Good after r i z s))

theorem inflate_completes_reachable (facts : DecoderFacts) : InflateCompletesReachable := by
  intro wb wrap bits r h log source decoded z i s flush params ⟨pending, trace⟩ reach fit single unfinished
    valid full started good notBad notMem notSync dictOk buffers active noFail input room flushes
  -- the decoder's allocator
  obtain ⟨i0, z0, s0, g0, alloc0⟩ := facts.safety.1 h r reach
  have alloc : Zlib.Inflate.Spec.DefAlloc z := (good_unique g0 good).2.1 ▸ alloc0
  obtain ⟨rc, after, z', s', u, out, run, good', acc, written, codes, okProg, sErr, sErrEq, bufCl, progCl,
    endMode, dictMode, dataMode, memCl, totals, frame, live⟩ :=
    facts.call h r i z s flush reach good fit alloc buffers active
  obtain ⟨aU, aO, aIn, aOut, -, -, -, -, -, -, -⟩ := acc
  have hz' : r.get after = some z' := good'.live.hz
  obtain ⟨rest, hrest⟩ := started
  have dropEq : source.drop log.input.length = rest := by rw [← hrest]; simp
  have given : log.input ++ source.drop log.input.length = source := by rw [dropEq, hrest]
  have dstep : DataStep .inflate h after r flush rc (source.drop log.input.length) out u :=
    ⟨z, z', good.live.hz, hz', buffers, active, input, by omega,
      by rw [show z.avail_out.toNat - z'.avail_out.toNat = out.length by omega]; exact written, run⟩
  have trace' := InflateProtocolTrace.step trace dstep
  have comparable : log.input ++ source.drop log.input.length <+: source ∨
      source <+: log.input ++ source.drop log.input.length := Or.inl (by rw [given]; exact List.prefix_refl _)
  have pre : log.input <+: source := ⟨rest, hrest⟩
  obtain ⟨within, atEnd⟩ := facts.within wb wrap bits r h after log pending flush rc _ out u source decoded params
    trace single valid full pre comparable dstep
  have fmt := (facts.format wb wrap bits r after _ params ⟨_, trace'⟩).2 source decoded valid single full within
  simp only [] at fmt
  obtain ⟨outPre, notData, endEq⟩ := fmt
  have takeLen : (log.input ++ (source.drop log.input.length).take u).length = log.input.length + u := by
    have bl := bytes_length input
    simp only [List.length_append, List.length_take]
    omega
  refine ⟨rc, after, run, ?_⟩
  rcases codes with h0 | h0 | h0 | h0 | h0 | h0 | h0
  · -- Z_OK
    exfalso
    subst h0
    by_cases ain : z'.avail_in = 0
    · have all : log.input ++ (source.drop log.input.length).take u = source := by
        have : u = (source.drop log.input.length).length := by
          have bl := bytes_length input
          have : z'.avail_in.toNat = 0 := by rw [ain]; rfl
          omega
        rw [this, List.take_length, given]
      rcases atEnd all with x | x <;> exact absurd x (by decide)
    · obtain ⟨o0, lt⟩ := facts.stops wb wrap bits r h after log pending flush Z_OK _ out u source decoded z' params
        trace single valid full pre comparable dstep flushes (Or.inl rfl) hz' ain
      have : z'.avail_out.toNat = 0 := by rw [o0]; rfl
      omega
  · -- Z_STREAM_END
    subst h0
    obtain ⟨-, outEq⟩ := endEq rfl
    left
    refine ⟨rfl, ?_⟩
    have dropOut : out = decoded.drop log.output.length := by rw [← outEq]; simp
    rw [← dropOut, show decoded.length - log.output.length = out.length by rw [← outEq]; simp]
    exact written
  · -- Z_NEED_DICT
    subst h0
    obtain ⟨hd, o0, wr, ⟨cmf, flg, tail, eq, hdr, fd, -⟩, z'', s'', g'', md, hd''⟩ :=
      facts.needDict wb wrap bits r h after log pending flush Z_NEED_DICT _ out u i z s params trace good dstep rfl
    obtain ⟨-, ez', es'⟩ := good_unique g'' good'
    subst ez' es'
    right; left
    obtain ⟨t, ht⟩ := within
    rw [eq] at ht
    refine ⟨rfl, hd, wr, ⟨cmf, flg, tail ++ t, by rw [← ht]; rfl, hdr, fd⟩, z'', i, s'', g'', md, hd'', ?_⟩
    subst o0
    apply UInt32.toNat_inj.mp
    simp only [List.length_nil] at aOut
    omega
  · -- Z_STREAM_ERROR
    subst h0
    obtain ⟨ez, es, -, -⟩ := sErrEq rfl
    subst ez es
    rcases sErr.1 rfl with x | x | x
    · exact Or.inr (Or.inr ⟨rfl, Or.inl x, good'⟩)
    · exact Or.inr (Or.inr ⟨rfl, Or.inr x, good'⟩)
    · exact absurd x notSync
  · exact absurd h0 notData
  · -- Z_MEM_ERROR
    subst h0
    obtain ⟨j, lo, -, bad⟩ := facts.mem h r i z s flush after reach good notMem run
    rw [noFail j] at bad
    cases bad
  · -- Z_BUF_ERROR
    exfalso
    subst h0
    by_cases ain : z'.avail_in = 0
    · have all : log.input ++ (source.drop log.input.length).take u = source := by
        have : u = (source.drop log.input.length).length := by
          have bl := bytes_length input
          have : z'.avail_in.toNat = 0 := by rw [ain]; rfl
          omega
        rw [this, List.take_length, given]
      rcases atEnd all with x | x <;> exact absurd x (by decide)
    · obtain ⟨o0, lt⟩ := facts.stops wb wrap bits r h after log pending flush Z_BUF_ERROR _ out u source decoded z'
        params trace single valid full pre comparable dstep flushes (Or.inr rfl) hz' ain
      have : z'.avail_out.toNat = 0 := by rw [o0]; rfl
      omega

end Zlib.Inflate.Proofs
