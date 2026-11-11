import ZlibF.Proof.«inflate.c.completes-needdict»
import ZlibF.Proof.«inflate.c.completes-evidence»
import ZlibF.Proof.«inflate.c.completes-stops»
import ZlibF.Spec.Api.Examples

/-!
# uncompr.c: the data relation from the last decoder call

After the call loop of `uncompress2_z`, the actual history of its local stream
is a protocol history with window bits 15 and no dictionary. From the decoder
facts and the last call, the returned code, the output and the consumed source
satisfy `Api.Uncompress2`.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The return code of `uncompress2_z` from the last `inflate` result and the
unused source length (`len` after the loop). -/
def finalCode (err : Int32) (rest : UInt64) : Int32 :=
  if err == Z_STREAM_END then Z_OK
  else if err == Z_NEED_DICT then Z_DATA_ERROR
  else if err == Z_BUF_ERROR && rest == 0 then Z_DATA_ERROR
  else err

theorem inflWbits_15 : Api.inflWbits (15 : Int32).toInt = some (.zlib, 15) := by decide

theorem zlib_fits_15 {s o : List UInt8} (d : Zlib.Decodes [] s o) : Api.ZlibFits 15 s := by
  obtain ⟨cmf, flg, pre, rest, rfl, ⟨-, cinfo, -⟩, -, -⟩ := d
  exact Or.inr ⟨cmf, rfl, by omega⟩

theorem zlib_layer {s o : List UInt8} (d : Zlib.Decodes [] s o) : Api.Layer.Decodes .zlib 15 [] s o :=
  ⟨d, zlib_fits_15 d⟩

theorem zlib_full {s : List UInt8} : Api.FullWindow .zlib 15 s := Or.inl rfl

theorem zlib_decodes_long {d s o : List UInt8} (h : Zlib.Decodes d s o) : 2 ≤ s.length := by
  obtain ⟨cmf, flg, pre, rest, rfl, -⟩ := h
  simp

theorem accepted_zlib {s o : List UInt8} (h : Api.Layer.InflateAccepted .zlib 15 [] s o) :
    Zlib.Decodes [] s o := by
  obtain ⟨⟨cmf, flg, pre, rest, e, hdr, h0, h1⟩, -⟩ := h
  exact ⟨cmf, flg, pre, rest, e, hdr, h0, fun f => by simpa using h1 f⟩

/-- The log after one observed call, as in `InflateProtocolTrace.step`. -/
def stepLog (log : DataLog) (rc : Int32) (input output : List UInt8) (used : Nat) : DataLog :=
  { log with
    input := log.input ++ input.take used, output := log.output ++ output
    result := rc, finished := log.finished || rc == Z_STREAM_END }

/-- The data relation of `uncompress2_z` from its last decoder call. `noOver` says
that no complete stream at the start of the source has been read to its end
before the last call; the loop keeps it, since reading such an end returns
`Z_STREAM_END` or `Z_MEM_ERROR` and stops the loop. -/
theorem uncompressed_final (facts : DecoderFacts) {r : ZStreamRef} {Hp H : Heap} {logp : DataLog}
    {e : Int32} {input output : List UInt8} {usedc used cap : Nat} {src : List UInt8} {R : UInt64}
    (tracep : InflateProtocolTrace 15 r Hp logp false) (fitp : ZlibF.PlatformMemory.ByteObjectsFit Hp)
    (single : logp.singleDictionary = true) (dict : logp.dictionary = [])
    (good : ∃ i z s, Zlib.Inflate.Spec.Good Hp r i z s)
    (step : DataStep .inflate Hp H r Z_NO_FLUSH e input output usedc)
    (hin : logp.input ++ input.take usedc = src.take used) (hused : used ≤ src.length)
    (hgiven : logp.input ++ input <+: src)
    (hout : (logp.output ++ output).length ≤ cap)
    (noOver : ∀ m o, m ≤ src.length → Zlib.Decodes [] (src.take m) o →
      logp.input <+: src.take m ∧ logp.input ≠ src.take m)
    (codes : e = Z_STREAM_END ∨ e = Z_NEED_DICT ∨ e = Z_DATA_ERROR ∨ e = Z_MEM_ERROR ∨
      e = Z_BUF_ERROR)
    (buf : e = Z_BUF_ERROR → R = 0 ∨
      ((logp.output ++ output).length = cap ∧ ∃ z', r.get H = some z' ∧ z'.avail_in ≠ 0))
    (hR : R.toNat = src.length - used) :
    Uncompressed src cap (finalCode e R) (logp.output ++ output) used := by
  have trace := InflateProtocolTrace.step tracep fitp step
  have allowed : AllowedInflateProtocol 15 r H (stepLog logp e input output usedc) := ⟨_, trace⟩
  have single' : (stepLog logp e input output usedc).singleDictionary = true := single
  have dict' : (stepLog logp e input output usedc).dictionary = [] := dict
  have fmt := sequence_format facts.step 15 .zlib 15 r H _ inflWbits_15 allowed
  have ev := trace_evidence facts.step facts.stepEvidence 15 .zlib 15 r H _ _ inflWbits_15 trace single' (Or.inl dict')
  simp only [stepLog] at fmt
  simp only [dict, hin] at fmt ev
  -- the call never reads past a complete stream at the start of the source
  have within : ∀ m o, m ≤ src.length → Zlib.Decodes [] (src.take m) o →
      src.take used <+: src.take m ∧ (src.take used = src.take m → e = Z_STREAM_END ∨ e = Z_MEM_ERROR) := by
    intro m o hm d
    have pre := (noOver m o hm d).1
    have comparable : logp.input ++ input <+: src.take m ∨ src.take m <+: logp.input ++ input := by
      exact List.prefix_or_prefix_of_prefix hgiven (List.take_prefix m src)
    have w := facts.within 15 .zlib 15 r Hp H logp false Z_NO_FLUSH e input output usedc
      (src.take m) o inflWbits_15 tracep single fitp (by rw [dict]; exact zlib_layer d) zlib_full pre
      comparable step
    rw [hin] at w
    exact ⟨w.1, fun eq => w.2 eq (Or.inl (by decide))⟩
  -- facts for every complete stream at the start of the source
  have pre : ∀ m o, m ≤ src.length → Zlib.Decodes [] (src.take m) o →
      logp.output ++ output <+: o ∧ e ≠ Z_DATA_ERROR ∧
      (e = Z_STREAM_END → src.take used = src.take m ∧ logp.output ++ output = o) := by
    intro m o hm d
    exact fmt.2 (src.take m) o (zlib_layer d) single zlib_full (within m o hm d).1
  have dictCase : e = Z_NEED_DICT → ∀ m o, m ≤ src.length → Zlib.Decodes [] (src.take m) o →
      Api.HdrNeedsDict .zlib 15 (src.take m) := by
    intro he m o hm d
    obtain ⟨i, z, st, g⟩ := good
    obtain ⟨-, -, -, ⟨cmf, flg, tail, eq, hdr, fd, -⟩, -⟩ :=
      need_dictionary_call facts.call facts.step 15 .zlib 15 r Hp H logp false Z_NO_FLUSH e input output usedc i z st
        inflWbits_15 tracep single fitp g step he
    rw [hin] at eq
    obtain ⟨rest, hrest⟩ := (within m o hm d).1
    refine ⟨Or.inl rfl, cmf, flg, tail ++ rest, ?_, hdr, fd, zlib_fits_15 d⟩
    rw [← hrest, eq]
    rfl
  have stopCase : e = Z_BUF_ERROR → (logp.output ++ output).length = cap →
      (∃ z', r.get H = some z' ∧ z'.avail_in ≠ 0) →
      ∀ m o, m ≤ src.length → Zlib.Decodes [] (src.take m) o → cap < o.length := by
    intro he full ⟨z', hz', avail⟩ m o hm d
    have comparable : logp.input ++ input <+: src.take m ∨ src.take m <+: logp.input ++ input :=
      List.prefix_or_prefix_of_prefix hgiven (List.take_prefix m src)
    have st := stops_when_blocked facts.step facts.within facts.blocked 15 .zlib 15 r Hp H logp false Z_NO_FLUSH e input output usedc
      (src.take m) o z' inflWbits_15 tracep single fitp (by rw [dict]; exact zlib_layer d) zlib_full
      (noOver m o hm d).1 comparable step (Or.inl rfl) (Or.inr he) hz' avail
    rw [List.length_append] at full
    omega
  unfold Uncompressed Api.Uncompress2
  rw [if_neg (by decide)]
  refine ⟨hused, hout, ?_⟩
  rcases codes with rfl | rfl | rfl | rfl | rfl
  · -- Z_STREAM_END: Z_OK
    have code : finalCode Z_STREAM_END R = Z_OK := by unfold finalCode; rfl
    rw [code]
    refine ⟨Or.inl (by decide), fun _ => accepted_zlib (fmt.1 single rfl), fun h => absurd h (by decide),
      ev.2, ev.1, fun m o hm d => ⟨(pre m o hm d).1, fun _ => ⟨fun _ => Or.inl (by decide), fun big => ?_⟩⟩⟩
    have same := ((pre m o hm d).2.2 rfl).2
    rw [← same] at big
    omega
  · -- Z_NEED_DICT: Z_DATA_ERROR
    have code : finalCode Z_NEED_DICT R = Z_DATA_ERROR := by unfold finalCode; rfl
    rw [code]
    refine ⟨Or.inr (Or.inr (Or.inl (by decide))), fun h => absurd h (by decide),
      fun h => absurd h (by decide), ev.2, ev.1,
      fun m o hm d => ⟨(pre m o hm d).1, fun nd => absurd (dictCase rfl m o hm d) nd⟩⟩
  · -- Z_DATA_ERROR
    have code : finalCode Z_DATA_ERROR R = Z_DATA_ERROR := by unfold finalCode; rfl
    rw [code]
    refine ⟨Or.inr (Or.inr (Or.inl (by decide))), fun h => absurd h (by decide),
      fun h => absurd h (by decide), ev.2, ev.1,
      fun m o hm d => ⟨(pre m o hm d).1, fun _ => absurd rfl (pre m o hm d).2.1⟩⟩
  · -- Z_MEM_ERROR
    have code : finalCode Z_MEM_ERROR R = Z_MEM_ERROR := by unfold finalCode; rfl
    rw [code]
    refine ⟨Or.inr (Or.inr (Or.inr (by decide))), fun h => absurd h (by decide),
      fun h => absurd h (by decide), ev.2, ev.1,
      fun m o hm d => ⟨(pre m o hm d).1, fun _ => ⟨fun _ => Or.inr (by decide),
        fun _ => Or.inr (by decide)⟩⟩⟩
  · -- Z_BUF_ERROR
    by_cases r0 : R = 0
    · have code : finalCode Z_BUF_ERROR R = Z_DATA_ERROR := by subst r0; decide
      rw [code]
      have all : used = src.length := by
        have := congrArg UInt64.toNat r0
        simp only [UInt64.toNat_zero] at this
        omega
      refine ⟨Or.inr (Or.inr (Or.inl (by decide))), fun h => absurd h (by decide),
        fun h => absurd h (by decide), ev.2, ev.1,
        fun m o hm d => ⟨(pre m o hm d).1, fun _ => ?_⟩⟩
      exfalso
      obtain ⟨p, q⟩ := within m o hm d
      have eqm : src.take used = src.take m := by
        rw [all, List.take_length] at p ⊢
        have len : (src.take m).length ≤ src.length := List.length_take_le' m src
        exact p.eq_of_length (by have := p.length_le; omega)
      rcases q eqm with h | h <;> exact absurd h (by decide)
    · have code : finalCode Z_BUF_ERROR R = Z_BUF_ERROR := by
        simp only [finalCode, show (R == 0) = false from beq_false_of_ne r0, Bool.and_false,
          Bool.false_eq_true, ite_false]
        rfl
      rw [code]
      have full := (buf rfl).resolve_left r0
      have more : used < src.length := by
        have : R.toNat ≠ 0 := fun h => r0 (UInt64.toNat_inj.mp (by simpa using h))
        omega
      refine ⟨Or.inr (Or.inl (by decide)), fun h => absurd h (by decide), fun _ => ⟨full.1, more⟩,
        ev.2, ev.1, fun m o hm d => ⟨(pre m o hm d).1, fun _ => ⟨fun small => ?_, fun _ => Or.inl rfl⟩⟩⟩
      have := stopCase rfl full.1 full.2 m o hm d
      omega

/-- The empty output with nothing consumed: initialization failed. -/
theorem uncompressed_mem_init (src : List UInt8) (cap : Nat) : Uncompressed src cap Z_MEM_ERROR [] 0 := by
  unfold Uncompressed Api.Uncompress2
  rw [if_neg (by decide)]
  refine ⟨Nat.zero_le _, Nat.zero_le _, Or.inr (Or.inr (Or.inr (by decide))), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun _ _ _ _ => List.nil_prefix, ?_, ?_⟩
  · refine ⟨[], List.nil_prefix, ⟨[], Api.zA, [0x61], rfl, Or.inl List.nil_prefix, Api.zA_layer⟩, ?_⟩
    intro _ _ _ _ _ _
    exact List.nil_prefix
  · intro m o _ _
    exact ⟨List.nil_prefix, fun _ => ⟨fun _ => Or.inr (by decide), fun _ => Or.inr (by decide)⟩⟩

end ZlibF.Spec.Public.Proofs.Uncompress
