import ZlibF.Proof.«inflate.c.completes-meaning»

/-!
# inflate.c: where `Z_NEED_DICT` comes from

`NeedDictionaryCall` from `Goal.inflate` (a `Z_NEED_DICT` return leaves `DICT`)
and the format meaning after the call (`MeaningStep`, open): with the request
token set, the stage is `needDict header`, so the consumed input is a zlib
header with `FDICT` and its dictionary identifier, no output was delivered and
no dictionary is installed. The call keeps `havedict` (`call_keeps_havedict`),
so none was installed before it either.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem need_dictionary_call (call : Goal.inflate) (step : MeaningStep) : NeedDictionaryCall := by
  intro wb wrap bits r h after log pending flush rc input output used i z s params trace single fit
    good dstep need
  subst need
  have before := meaning_of_protocol step trace
  have saved := before
  obtain ⟨_, _, i0, z0, s0, _, inv0, _⟩ := saved
  obtain ⟨-, ez0, -⟩ := good_same inv0.good good
  have alloc : Zlib.Inflate.Spec.DefAlloc z := ez0 ▸ inv0.alloc
  have observed := dstep
  obtain ⟨_, _, _, _, buffers, active, _, _, _, run⟩ := observed
  obtain ⟨rc', after', z', s', _, _, run', good', -, -, -, -, -, -, -, -, -, dictMode, -⟩ :=
    call h r i z s flush (InflateProtocolTrace.reachable trace) good fit alloc buffers active
  have same : (Z_NEED_DICT, after) = (rc', after') := Except.ok.inj (run.symm.trans run')
  cases same
  have mode : s'.mode = DICT := dictMode rfl
  have kept : s'.havedict = s.havedict := call_keeps_havedict good run good'
  obtain ⟨wrap', configured, i1, z1, s1, params', inv, _, _, _, _, _, stageClause⟩ :=
    step wb r h after log pending flush Z_NEED_DICT input output used before fit dstep
  rw [params] at params'
  obtain ⟨rfl, rfl⟩ : wrap = wrap' ∧ bits = configured := by
    cases params'
    exact ⟨rfl, rfl⟩
  obtain ⟨-, -, es⟩ := good_same inv.good good'
  have es' := es.symm
  subst es'
  obtain ⟨consumed, held, stage, inputBits, _, parsed, _, _, outputEq, request⟩ :=
    stageClause single (by rw [mode]; decide) (by rw [mode]; decide) (by rw [mode]; decide)
  obtain ⟨header, rfl, missing⟩ := request.mp (by decide)
  obtain ⟨consumedEq, wrapper, cmf, flg, dictid, headerEq, _, ok, fits, fdict⟩ := parsed
  subst consumedEq headerEq
  have outputNil : output = [] := by
    have e : log.output ++ output = [] := outputEq
    exact (List.append_eq_nil_iff.mp e).2
  have pre : [cmf, flg] <+: log.input ++ input.take used := by
    apply bytesToBits_prefix_iff.mp
    rw [inputBits]
    exact ⟨bytesToBits dictid ++ held, by rw [bytesToBits_append', List.append_assoc]⟩
  obtain ⟨tail, tailEq⟩ := pre
  refine ⟨kept ▸ missing, outputNil, wrapper, ⟨cmf, flg, tail, tailEq.symm, ok, fdict, ?_⟩,
    z', s', good', mode, missing⟩
  rw [← tailEq]
  exact fits

#print axioms need_dictionary_call
end Zlib.Inflate.Proofs
