import ZlibF.Proof.«inflate.c.meaning-dictid»
import ZlibF.Proof.«inflate.c.meaning-block»
import ZlibF.Proof.«inflate.c.meaning-frame»
import ZlibF.Proof.«inflate.c.head-default-state»

/-!
# inflate.c: `HEAD` keeps the format meaning in the loop

Batch 2, `head_step`. Raw data (`wrap = 0`): `case HEAD` enters `TYPEDO`
without reading, and the parse stands at the first block boundary with
nothing held.
-/

namespace Zlib.Inflate.Proofs.MeaningHead
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningBits Zlib.Inflate.Proofs.MeaningDictid
set_option autoImplicit false

/-- `case HEAD` for raw data in the loop: it enters `TYPEDO` at the first
block boundary. `width` is the configured raw width (8 to 15), which the call
assembly takes from `inflWbits`. -/
theorem head_raw_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (head : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = HEAD)
    (raw : f.wrap = .raw) (width : 8 ≤ f.configured ∧ f.configured ≤ 15) :
    ∃ result l' h', runX (inflate_HEAD c) l h = .ok ((result, l'), h') ∧
      TripOutcome c f result h' l' := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe, pend,
    putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM, wrapM,
    outputEq⟩ := loop
  have mode : s.mode = HEAD := head zs s st hs
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have wrap0 : s.wrap = 0 := by
    have code : s.wrap = wrapCode f.wrap := config.1
    rw [code, raw]
    rfl
  obtain ⟨bytes, rfl⟩ := stage_of_header stageM (by show s.mode ≤ DICTID; rw [mode]; decide)
  obtain ⟨⟨_, headC, _, _, _, _, last0, total0, rawBits⟩, windowM, _⟩ := wrapM
  obtain ⟨bytesNil, _, _⟩ := headC mode
  subst bytesNil
  have bits0 : l.bits.toNat = 0 := by
    have := rawBits raw
    simp only [loopState] at this
    rw [this]
    rfl
  obtain ⟨consumedEq, more, bodyDict, wh, _⟩ := parsed
  have consumedNil : consumed = [] := by simpa [bytesToBits] using consumedEq
  subst consumedNil
  have heldNil : held = [] := by
    have := heldBits.1
    simp only [loopState] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst heldNil
  have outNil : f.logOut ++ callOut = [] := outputEq.symm
  have logNil : f.logOut = [] := (List.append_eq_nil_iff.mp outNil).1
  have callNil : callOut = [] := (List.append_eq_nil_iff.mp outNil).2
  have pend0 : loopPending l = callOut.length := by
    have := pend.1
    rw [callNil] at this ⊢
    simpa using this
  rw [raw] at wh
  have moreNil : more = [] := by simpa using wh.1
  subst moreNil
  have wbitsEq : (loopState s l).wbits.toNat = f.configured := config.2.2.2.2.1 (by omega)
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
  refine ⟨_, _, _, inflate_HEAD_raw_run E l wrap0, Or.inl ⟨rfl, Or.inl ?_⟩⟩
  refine MeaningBlock.loop_move (s' := { s with mode := TYPEDO }) (j := 0) (header := [])
    (bitsP := []) (pos := ⟨[], false, .boundary⟩) (bodyDict := bodyDict) (consumed := []) (held := [])
    st retOk ⟨c1, c2, c3, c4, c5, show TYPEDO ≠ SYNC by decide⟩ haveLe inLen leftLe pend0 putEq outBytes
    writable sepIn sepWin sepOutIn ⟨rfl, rfl, rfl, rfl, rfl⟩ (by omega) (inputAdvance_zero l.next).symm
    binv bitsEq heldBits (by rw [raw]; exact ⟨rfl, wh.2⟩) (by simp [bytesToBits]) .start
    ⟨Or.inr rfl, rfl, last0, by show l.bits.toNat < 8; omega⟩ ?_ ?_ ⟨by simp [FlagsMatch, raw], ?_,
      Or.inr (Or.inl raw)⟩ (by rw [logNil, callNil]; rfl)
  · rw [logNil]
    exact WindowMeaning.frame (fun _ _ _ => byte_view_get_setI h zs _ _) windowM
  · refine ⟨?_, fun four => absurd (by show s.wrap &&& 4 = 0; rw [wrap0]; rfl) four⟩
    rw [logNil, callNil]
    simp only [List.append_nil, List.take_nil, List.length_nil]
    exact total0
  · refine ⟨?_, ?_, fun zero => by omega⟩
    · show 8 ≤ (loopState s l).wbits.toNat
      rw [wbitsEq]
      exact width.1
    · show (loopState s l).wbits.toNat ≤ 15
      rw [wbitsEq]
      exact width.2
#print axioms head_raw_step

end Zlib.Inflate.Proofs.MeaningHead
