import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Format.Examples
import ZlibF.Proof.Format.Api
import ZlibF.Proof.Api.InflateCausality

/-!
# API model: examples and non-vacuity

Computable definitions are checked by `decide`/`rfl` on small cases. Then a tiny deflate-then-inflate
is run through the model itself: the specification of `deflate` and of `inflate` is satisfied by
a concrete run (so neither is contradictory), and the output of the first is accepted by the
second. The example stream is the zlib stream of "a" of `Format/Examples.lean`.
-/

namespace ZlibF.Spec.Api

open ZlibF.Spec

set_option maxRecDepth 100000

local macro "dk" : term => `(by decide +kernel)

/-! ## Parameters (computable) -/

example : inflWbits 15 = some (.zlib, 15) := by decide
example : inflWbits 0 = some (.zlib, 0) := by decide
example : inflWbits 31 = some (.gzip, 15) := by decide
example : inflWbits 16 = some (.gzip, 0) := by decide
example : inflWbits 47 = some (.auto, 15) := by decide
example : inflWbits (-15) = some (.raw, 15) := by decide
example : inflWbits (-8) = some (.raw, 8) := by decide
example : inflWbits 7 = none := by decide
example : inflWbits 48 = none := by decide
example : inflWbits (-7) = none := by decide
example : inflWbits (-16) = none := by decide
example : inflWbits 16 ≠ inflWbits 0 := by decide

example : deflInit? (-1) 8 15 8 0 = some ⟨6, .zlib, 15, 8, 0⟩ := by decide
example : deflInit? 9 8 31 9 4 = some ⟨9, .gzip, 15, 9, 4⟩ := by decide
example : deflInit? 6 8 (-15) 8 0 = some ⟨6, .raw, 15, 8, 0⟩ := by decide
example : deflInit? 6 8 8 8 0 = some ⟨6, .zlib, 9, 8, 0⟩ := by decide
example : deflInit? 6 8 (-8) 8 0 = none := by decide     -- raw with 8 bits is refused
example : deflInit? 6 8 24 8 0 = none := by decide        -- gzip with 8 bits is refused
example : deflInit? 10 8 15 8 0 = none := by decide
example : deflInit? 6 8 15 0 0 = none := by decide
example : deflInit? 6 8 15 8 5 = none := by decide
example : deflInit? 6 9 15 8 0 = none := by decide
example : deflInit? 6 8 0 8 0 = none := by decide

example : compressBound 0 = 13 := by decide
example : compressBound 4096 = 4096 + 1 + 0 + 0 + 13 := by decide
example : compressBound (2 ^ 64 - 1) = 2 ^ 64 - 1 := by decide

/-- With the parameters of `compress2` the bound of `deflateBound` is the bound of `compressBound`
(`compress.c`: "if the default memLevel or windowBits for deflateInit() is changed, then this
function needs to be updated"). -/
theorem bound_default (n : Nat) (h : n < 2 ^ 60) :
    (DeflState.fresh ⟨6, .zlib, 15, 8, 0⟩).bound n = compressBound n := by
  unfold DeflState.bound compressBound DeflState.fresh DeflState.dictEff
  simp only [Option.getD_none]
  have : ¬ (n + n / 2 ^ 12 + n / 2 ^ 14 + n / 2 ^ 25 + 13 ≥ 2 ^ 64) := by omega
  simp [this]

example : (DeflState.fresh ⟨6, .gzip, 15, 8, 0⟩).bound 0 = 13 + 12 := by decide
example : (DeflState.fresh ⟨6, .raw, 15, 8, 0⟩).bound 0 = 7 := by decide
example : (DeflState.fresh ⟨6, .zlib, 9, 8, 0⟩).bound 0 = 4 + 6 := by decide
example : (DeflState.fresh ⟨6, .zlib, 15, 1, 0⟩).bound 100 = 100 + 3 + 0 + 0 + 7 + 6 := by decide

example : syncSearch 0 [1, 0, 0, 255, 255, 7] = (4, 5) := by decide
example : syncSearch 0 [0, 0, 255] = (3, 3) := by decide
example : syncSearch 3 [255, 9] = (4, 1) := by decide
example : syncSearch 0 [0, 0, 0, 255, 255] = (4, 5) := by decide
example : (syncSearch 0 [1, 2, 3]).1 = 0 := by decide

example : gzMode? "rb".toList = some (.read, -1, 0, 1) → False := by decide
example : gzMode? "rb".toList = some (.read, -1, 0, 0) := by decide
example : gzMode? "wb9".toList = some (.write, 9, 0, 0) := by decide
example : gzMode? "ab6h".toList = some (.append, 6, 2, 0) := by decide
example : gzMode? "wT".toList = some (.write, -1, 0, 1) := by decide
example : gzMode? "rb+".toList = none := by decide
example : gzMode? "b".toList = none := by decide
example : gzMode? "rT".toList = none := by decide
example : gzMode? "wG".toList = none := by decide

example : syncStep 0 0 = 1 ∧ syncStep 2 255 = 3 ∧ syncStep 2 7 = 0 ∧ syncStep 3 0 = 1 := by decide

/-! ## The example stream and a model run of inflate -/

/-- zlib's stream for "a" (`Format/Examples.lean`). -/
def zA : List UInt8 := [0x78, 0x9C, 0x4b, 0x04, 0x00, 0x00, 0x62, 0x00, 0x62]

theorem zA_decodes : Zlib.Decodes [] zA [0x61] :=
  ⟨0x78, 0x9C, [], _, rfl, dk, fun _ => ⟨rfl, _, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩,
    fun h => absurd h dk⟩

theorem zA_layer : Layer.Decodes .zlib 15 [] zA [0x61] :=
  ⟨zA_decodes, Or.inr ⟨0x78, rfl, by decide⟩⟩

theorem zA_not_needDict : ¬ HdrNeedsDict .zlib 15 zA := by
  rintro ⟨_, cmf, flg, r, h, _, hb, _⟩
  have h2 : flg = 0x9C := by simp [zA] at h; exact h.2.1.symm
  subst h2
  exact absurd hb dk

theorem zA_not_detectable : ¬ Layer.Detectable .zlib 15 [] zA := by
  rintro ⟨m, hm, hv⟩
  have h1 : m ≤ 1 := by simp [detectLag, zA] at hm; omega
  exact hv (Or.inl (by simp [hdrLag, List.length_take]; omega))

/-- Everything inflate does with the whole stream in one call: one `Z_FINISH` call with room 10. -/
def stDoneA : InflState :=
  { (InflState.fresh .zlib 15) with
    phase := .done, seen := zA, out := [0x61], totalIn := 9, totalOut := 1, adler := adler32 [0x61] }

theorem infl_one_call :
    InflStep (InflState.fresh .zlib 15) ⟨zA, 10, .finish, false⟩ ⟨9, [0x61], Z.streamEnd⟩ stDoneA := by
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  show InflRun _ _ _ _
  left
  unfold InflRunOk
  and_intros
  all_goals first
    | rfl
    | decide
    | (intro h; exact absurd h (by decide))
    | (intro _ h; exact absurd h (by decide))
    | (intro _ _; exact zA_layer)
    | (intro _ _ _ _ _; rfl)
    | (intro _ _ _ hD _; exact absurd hD (by simpa [InflState.dictEff, InflState.fresh] using zA_not_detectable))
    | (intro _ _ _ hN; exact absurd hN (by simpa [InflState.fresh] using zA_not_needDict))
    | (intro _ _ _; rfl)
    | (intro req h; simp [InflState.fresh] at h)

theorem not_zlib_short (d x o : List UInt8) (h : x.length < 2) : ¬ Zlib.Decodes d x o := by
  rintro ⟨cmf, flg, pre, s, hs, _⟩
  simp [hs] at h
  omega

theorem not_decodes_short (d x o : List UInt8) (b : Nat) (h : x.length < 2) :
    ¬ Layer.Decodes .zlib b d x o := by
  rintro ⟨⟨cmf, flg, pre, s, hs, _⟩, _⟩
  simp [hs] at h
  omega

/-- Closes the side conditions of `InflRun` for the concrete steps below. -/
local macro "close_infl" : tactic =>
  `(tactic| (and_intros; all_goals first
      | rfl
      | decide
      | (intro h; exact absurd h (by decide))
      | (intro _ h; exact absurd h (by decide))
      | (intro _ _; exact zA_layer)
      | (intro _ _ _ _ _; rfl)
      | (intro _ _ _ hD _; exact absurd hD zA_not_detectable)
      | (intro _ _ _ hN; exact absurd hN zA_not_needDict)
      | (intro _ _ h; exact absurd h (by decide))
      | (intro _ _ _; rfl)
      | (intro req h; cases h <;> fail)
      | (intro _; exact ⟨Or.inl (by decide), by decide, rfl⟩)
      | (intro _ _; exact Proofs.output_evidence_nil (Or.inl (by decide)) zA_layer _)
      | (intro _ _ _ _ _ _ _ _; exact List.nil_prefix)
      | (intro _ _ _ _ ⟨n, o', h1, h2, h3, _⟩; exact absurd h3 (not_decodes_short _ _ _ _ (Nat.lt_of_le_of_lt (List.length_take_le' _ _) (by simp [InflState.fresh]))))
      | (intro _ _ _ ⟨m, hm, _⟩ _; exact absurd hm (by simp [detectLag, InflState.fresh] <;> omega))
      | (intro _ _ h; rcases h with h | h; exact absurd rfl h; exact absurd h (by decide))))

/-- Two calls with the same stream cut after the first byte: the first call only reads the byte of
the header that it gets, with `Z_OK`. -/
def stHalfA : InflState :=
  { (InflState.fresh .zlib 15) with seen := [0x78], totalIn := 1 }

theorem infl_step1 :
    InflStep (InflState.fresh .zlib 15) ⟨[0x78], 10, .noFlush, false⟩ ⟨1, [], Z.ok⟩ stHalfA := by
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  show InflRun _ _ _ _
  left
  unfold InflRunOk
  close_infl

theorem infl_step2 :
    InflStep stHalfA ⟨zA.drop 1, 10, .finish, false⟩ ⟨8, [0x61], Z.streamEnd⟩ stDoneA := by
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  show InflRun _ _ _ _
  left
  unfold InflRunOk
  close_infl

/-- A run of `inflate` over `zA` cut in two calls reaches the end of the stream with the
decoded data. -/
theorem infl_trace : InflTrace zA [] (InflStart .zlib 15 []) stDoneA :=
  .step (c := ⟨[0x78], 10, .noFlush, false⟩) (r := { rc := Z.ok, out := ⟨1, [], Z.ok⟩ })
    (by decide) ⟨infl_step1, rfl⟩
    (.step (c := ⟨zA.drop 1, 10, .finish, false⟩) (r := { rc := Z.streamEnd, out := ⟨8, [0x61], Z.streamEnd⟩ })
      (by decide) ⟨infl_step2, rfl⟩ .nil)

/-! ## A model run of deflate -/

/-- The parameters of `compress2` at level 6. -/
def dP : DeflParams := ⟨6, .zlib, 15, 8, 0⟩

theorem zA_valid : (DeflState.fresh dP).Valid zA [0x61] :=
  ⟨zA_decodes, by decide, 0x78, 0x9C, _, rfl, by decide⟩

/-- The state after one `Z_FINISH` call with the byte "a" and room 20 that delivers `zA`. -/
def dDoneA : DeflState :=
  { (DeflState.fresh dP) with
    input := [0x61], produced := zA, totalIn := 1, totalOut := 9, adler := adler32 [0x61],
    last := 4, finishing := true, done := true, started := true }

theorem defl_one_call :
    DeflStep (DeflState.fresh dP) ⟨[0x61], 20, .finish, false⟩ ⟨1, zA, Z.streamEnd⟩ dDoneA := by
  refine ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide),
    fun _ _ _ h => absurd h (by decide), fun _ _ _ _ => ?_⟩
  unfold DeflRun DeflFrame
  and_intros
  all_goals first
    | rfl
    | decide
    | (intro h; exact absurd h (by decide))
    | (intro h; exact absurd h.2.1 (by decide))
    | (intro _; refine ⟨rfl, fun v h => ?_⟩; exact (Option.some.inj h).symm)
    | (intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => zA_valid, fun _ h => absurd h (by decide), fun _ => by decide⟩)
    | (intro _ _ _ _ _ _; rfl)
    | (intro _ _ h; exact absurd h (by decide))
    | (intro _ _; exact absurd ‹_› (by decide))
    | (intro _ _ _; exact absurd ‹_› (by decide))

/-- Deflate then inflate, through the model: the data of the example goes through both. -/
theorem roundtrip_example :
    DeflTrace [0x61] (DeflState.fresh dP) dDoneA ∧ InflTrace zA [] (InflStart .zlib 15 []) stDoneA ∧
    dDoneA.produced = zA ∧ stDoneA.out = [0x61] :=
  ⟨.step (c := ⟨[0x61], 20, .finish, false⟩) (r := { rc := Z.streamEnd, out := ⟨1, zA, Z.streamEnd⟩ })
      (by decide) ⟨defl_one_call, rfl⟩ .nil,
    infl_trace, rfl, rfl⟩

/-- Non-vacuity of `Goal.roundtrip`'s hypotheses: this deflate trace is one the goal talks
about, and the inflate trace is one of its runs. -/
example : DeflCfg dP ∧ Compatible dP .zlib 15 ∧ dDoneA.done = true ∧ dDoneA.precise = true ∧
    dDoneA.input = [0x61] ∧ dDoneA.dictEff = [] :=
  ⟨⟨6, 8, 15, 8, 0, by decide⟩, ⟨⟨15, by decide⟩, rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩, rfl, rfl, rfl, rfl⟩

/-- The hypotheses of `Goal.inflate_decodes` and `Goal.inflate_completes` are satisfiable. -/
example : InflCfg .zlib 15 ∧ Layer.Decodes .zlib 15 [] zA [0x61] ∧ FullWindow .zlib 15 zA ∧
    ¬ HdrNeedsDict .zlib 15 zA ∧ InflTrace zA [] (InflStart .zlib 15 []) stHalfA :=
  ⟨⟨15, by decide⟩, zA_layer, Or.inl rfl, zA_not_needDict,
    .step (c := ⟨[0x78], 10, .noFlush, false⟩) (r := { rc := Z.ok, out := ⟨1, [], Z.ok⟩ })
      (by decide) ⟨infl_step1, rfl⟩ .nil⟩

/-- Two states of the `Goal.inflate_completes` shape: from `stHalfA` the call with the rest ends the
stream (this is `infl_step2`, seen as the conclusion of the goal). -/
example : (⟨zA.drop 1, 10, .finish, false⟩ : InflCall).inp = zA.drop stHalfA.seen.length ∧
    zA_layer = zA_layer ∧ [0x61].length ≤ stHalfA.out.length + 10 := ⟨rfl, rfl, by decide⟩

/-! ## `compress2` and `uncompress2` -/

example : compressParams 6 = some dP := by decide
example : compressParams (-1) = some dP := by decide
example : compressParams 10 = none := by decide

theorem compress2_example : Compress2 true 6 [0x61] 100 Z.ok zA :=
  Or.inr (Or.inl ⟨rfl, zA_valid, by decide, by decide⟩)

/-- A level outside -1 to 9: nothing is written. -/
example : Compress2 true 10 [0x61] 100 Z.streamError [] := ⟨rfl, rfl⟩
/-- A null argument. -/
example : Compress2 false 6 [0x61] 100 Z.streamError [] := ⟨rfl, rfl⟩
/-- A destination of `compressBound` bytes is enough: the same call with the room at the bound
still succeeds. -/
example : Compress2 true 6 [0x61] (compressBound 1) Z.ok zA :=
  Or.inr (Or.inl ⟨rfl, zA_valid, by decide, by decide⟩)

/-- The room is one byte: only the first byte of a stream fits. -/
example : Compress2 true 6 [0x61] 1 Z.bufError [0x78] :=
  Or.inr (Or.inr ⟨rfl, rfl, by decide, zA, zA_valid, by decide⟩)

/-- `uncompress2` on an empty source: `Z_DATA_ERROR` and nothing is written. -/
example : Uncompress2 true [] 10 Z.dataError [] 0 := by
  refine ⟨by decide, by decide, Or.inr (Or.inr (Or.inl rfl)),
    fun h => absurd h (by decide), fun h => absurd h (by decide), ?_, ?_, ?_⟩
  · intro stream decoded _ _
    exact List.nil_prefix
  · exact Proofs.output_evidence_nil (allowed := fun dictionary => dictionary = []) rfl zA_layer []
  · intro n o _ h
    exact absurd h (not_zlib_short _ _ _ (by simp))

/-- Null arguments to `uncompress2`. -/
example : Uncompress2 false zA 10 Z.streamError [] 0 := ⟨rfl, rfl, rfl⟩

/-! ## gz files -/

/-- A file of two bytes is read as it is. -/
theorem gz_direct_file : GzDecoded false [0x61, 0x62] [0x61, 0x62] Z.ok :=
  Or.inl ⟨rfl, fun h => absurd h.1 (by decide), rfl, rfl⟩

/-- Opening it for reading. -/
def gzR : GzHandle :=
  { mode := .read, level := -1, strategy := 0, direct := 0, raw := [0x61, 0x62], dec := [0x61, 0x62],
    dstat := Z.ok, rpos := 0, pushed := [], past := false, err := Z.ok, written := [], out := [],
    base := [], want := gzBufDefault, sized := false, failed := false }

example : GzOpen "r".toList (some [0x61, 0x62]) (some gzR) :=
  Or.inr ⟨[0x61, 0x62], [0x61, 0x62], Z.ok, fun _ => ⟨rfl, gz_direct_file⟩, rfl⟩

example : GzOpen "r".toList none none := Or.inl rfl
example : GzOpen "q".toList (some []) none := rfl
example : GzOpen "r+".toList (some []) none := rfl

/-- Reading one byte, then asking for more than is left: the second read comes up short and sets
the end indicator. -/
example : GzReadFn gzR 1 [0x61] 1 { gzR with rpos := 1, sized := true } := by
  unfold GzReadFn GzHandle.avail
  refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
  decide
example : GzReadFn { gzR with rpos := 1 } 5 [0x62] 1 { gzR with rpos := 2, sized := true, past := true } := by
  unfold GzReadFn GzHandle.avail
  refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
  decide
example : GzReadFn { gzR with rpos := 2 } 5 [] 0 { gzR with rpos := 2, sized := true, past := true } := by
  unfold GzReadFn GzHandle.avail
  refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
  decide

example : GzEof { gzR with past := true } 1 := by unfold GzEof; decide
example : GzEof gzR 0 := by unfold GzEof; decide
example : GzTell { gzR with rpos := 1 } 1 := by unfold GzTell GzHandle.tell; decide
example : GzDirect gzR 1 { gzR with sized := true } :=
  ⟨Or.inl ⟨rfl, rfl, fun h => absurd h.1 (by decide), by decide⟩, rfl⟩

/-- zlib's gzip member for "a" (`Format/Examples.lean`). -/
def gzA : List UInt8 := [31, 139, 8, 0, 0, 0, 0, 0, 2, 19, 75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0]

theorem gzA_decodes : Gzip.Decodes gzA [0x61] :=
  ⟨0, [0, 0, 0, 0], 2, 19, [], [], [], [75, 4, 0, 67, 190, 183, 232, 1, 0, 0, 0], dk, dk, dk, dk, dk, dk,
    _, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩

theorem gzip_empty (o : List UInt8) : ¬ Gzip.Decodes [] o := by
  rintro ⟨flg, mtime, xfl, os, extra, name, comment, s, _, _, _, _, _, hm, _⟩
  simp [Gzip.header] at hm

/-- The file that a writer produces for "a" reads back as "a" (`C7`): the member is the whole
file, there is nothing after it. -/
theorem gzA_file : GzDecoded false gzA [0x61] Z.ok :=
  Or.inr (Or.inr ⟨Or.inl ⟨by decide, by decide, by decide, by decide, by decide⟩,
    [(gzA, [0x61])], [], by simpa using gzA_decodes, rfl,
    fun ⟨m, o, t, h, hd⟩ => by
      have hm : m = [] := (List.append_eq_nil_iff.mp h.symm).1
      subst hm
      exact gzip_empty _ hd,
    Or.inl ⟨rfl, by simp, rfl, rfl⟩⟩)

/-- A writer that wrote "a" and closes: the file is the member. -/
def gzW : GzHandle :=
  { gzR with mode := .write, raw := [], dec := [], written := [0x61], out := gzA }

example : GzClose gzW Z.ok gzA := by
  refine ⟨Or.inl rfl, fun h => absurd h (by decide), fun _ _ => Or.inr rfl, fun _ _ _ => ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
  exact ⟨gzA, by simp [gzW, gzR], List.prefix_refl _, gzA_decodes⟩

/-! ## Witnesses for the repaired parts of the specification

A `Z_FINISH` call that returns `Z_BUF_ERROR` (nothing is consumed, nothing is finished, `done` stays
false), a completed `Z_FULL_FLUSH` (it sets `fullAt`), and an `inflate` call that returns
`Z_MEM_ERROR` after reading input and writing output (the totals stay). The lemmas say that the
clauses of the model are the ones that exclude the earlier errors. -/

theorem defl_done_iff {st : DeflState} {c : DeflCall} {o : DeflOut} {st' : DeflState}
    (h : DeflRun st c o st') : st'.done = true ↔ (st.done = true ∨ o.rc = Z.streamEnd) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hd, -⟩ := h
  exact hd

/-- `done` is not set by a `Z_BUF_ERROR` (the first error of the review). -/
theorem defl_no_done_on_buf_error {st : DeflState} {c : DeflCall} {o : DeflOut} {st' : DeflState}
    (h : DeflRun st c o st') (hr : o.rc = Z.bufError) (hd : st.done = false) : st'.done = false := by
  have := (defl_done_iff h).1
  cases hd' : st'.done
  · rfl
  · rcases this hd' with h1 | h1
    · simp [hd] at h1
    · rw [hr] at h1; exact absurd h1 (by decide)

/-- `fullAt` is kept by every call that does not complete a full flush. -/
theorem defl_fullAt_kept {st : DeflState} {c : DeflCall} {o : DeflOut} {st' : DeflState}
    (h : DeflRun st c o st')
    (hn : ¬ (o.rc = Z.ok ∧ o.produced.length < c.availOut ∧ c.flush = .fullFlush)) :
    st'.fullAt = st.fullAt := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hk, -⟩ := h
  exact hk hn

/-- A stream whose `Z_FINISH` was accepted but not finished: the output bytes `78` are out, three are pending. -/
def dBusy : DeflState :=
  { (DeflState.fresh dP) with
    input := [0x61], produced := [0x78], totalIn := 1, totalOut := 1, adler := adler32 [0x61],
    pend := 3, last := 4, finishing := true, started := true }

/-- More input after `Z_FINISH`: `Z_BUF_ERROR`, nothing consumed, the stream is not finished. -/
theorem defl_finish_buf_error :
    DeflStep dBusy ⟨[0x62], 5, .finish, false⟩ ⟨0, [], Z.bufError⟩ dBusy := by
  refine ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide),
    fun _ _ _ h => absurd h (by decide), fun _ _ _ _ => ?_⟩
  unfold DeflRun DeflFrame
  and_intros
  all_goals first
    | rfl
    | decide
    | (intro h; exact absurd h (by decide))
    | (intro h; exact absurd h.1 (by decide))
    | (intro _ h; exact absurd h (by decide))
    | (intro _ _; exact Or.inl rfl)
    | (intro _ _; exact ⟨rfl, Or.inl rfl⟩)
    | (intro _ _; exact absurd ‹_› (by decide))
    | (intro _ _ h; exact absurd h (by decide))
    | (intro _ _ _; exact absurd ‹_› (by decide))
    | (intro h _; exact absurd h (by decide))
    | (intro _ _ _ _ _ h; exact absurd h (by decide))

/-- The stream state of that witness is not finished, and the `done` flag stays false, whatever
the call: the repaired clause. -/
example : dBusy.done = false := rfl

/-- Raw deflate of "a" with a completed full flush: `4a 04 00` then the empty stored block `00 00 ff ff`
(what zlib writes). Followed by `03 00` it is a valid stream of "a". -/
def fullA : List UInt8 := [0x4a, 0x04, 0x00, 0x00, 0x00, 0xff, 0xff]

theorem fullA_flushed : Deflate.Decodes [] (fullA ++ [3, 0]) [0x61] :=
  ⟨_, .more rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl)))
    (.more rfl rfl (.stored rfl rfl rfl rfl) (.last rfl rfl (.fixed (.eob rfl)))), dk⟩

def dPraw : DeflParams := ⟨6, .raw, 15, 8, 0⟩

def dFullA : DeflState :=
  { (DeflState.fresh dPraw) with
    input := [0x61], produced := fullA, totalIn := 1, totalOut := 7, last := 3, started := true,
    clean := false, fullAt := some (7, 1) }

/-- A completed full flush with `fullAt = none` before: the call has an allowed outcome and sets `fullAt`. -/
theorem defl_full_flush :
    DeflStep (DeflState.fresh dPraw) ⟨[0x61], 20, .fullFlush, false⟩ ⟨1, fullA, Z.ok⟩ dFullA := by
  refine ⟨fun h => absurd h (by decide), fun _ h => absurd h (by decide),
    fun _ _ _ h => absurd h (by decide), fun _ _ _ _ => ?_⟩
  unfold DeflRun DeflFrame
  and_intros
  all_goals first
    | rfl
    | decide
    | (intro h; exact absurd h (by decide))
    | (intro h; exact absurd h.1 (by decide))
    | (intro _ h; exact absurd h (by decide))
    | (intro _; exact ⟨rfl, fun v h => by cases h⟩)
    | (intro _ _ _; exact ⟨by decide, by decide, rfl⟩)
    | (intro _ _ _; exact ⟨rfl, rfl⟩)
    | (intro _ _ _; refine ⟨rfl, fun _ => ?_⟩; exact fullA_flushed)
    | (intro _ _ _; rfl)
    | (intro _ _ _ _ _ _; exact absurd ‹_› (by decide))
    | (intro _ h; exact absurd h (by decide))
    | (intro h; exact absurd ⟨rfl, by decide, rfl⟩ h)

/-- The completed flush is not the old, contradictory outcome (`fullAt` kept `none`). -/
example : dFullA.fullAt ≠ (DeflState.fresh dPraw).fullAt := by decide

/-- An inflate call that reads the whole raw stream of "a" and writes the byte, then fails to allocate the
window: `Z_MEM_ERROR`, consumed 3, produced 1, `total_in` and `total_out` still 0, state `mem`. -/
def rawA : List UInt8 := [0x4b, 0x04, 0x00]

def stMemA : InflState :=
  { (InflState.fresh .raw 15) with phase := .mem, seen := rawA, out := [0x61] }

theorem rawA_decodes : Layer.Decodes .raw 15 [] rawA [0x61] :=
  ⟨_, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩

theorem infl_mem_error :
    InflStep (InflState.fresh .raw 15) ⟨rawA, 10, .noFlush, false⟩ ⟨3, [0x61], Z.memError⟩ stMemA := by
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  show InflRun _ _ _ _
  right
  unfold InflRunMem
  and_intros
  all_goals first
    | rfl
    | decide
    | (intro _; exact Proofs.output_evidence_of_decodes (Or.inr rfl)
        (fun d hd => by simpa [InflState.PermitsDictionary, InflState.fresh] using hd) rawA_decodes)
    | (intro _ dictionary _
       change Layer.Determined .raw 15 dictionary rawA [0x61]
       have ha : Layer.Decodes .raw 15 dictionary rawA [0x61] :=
         ⟨_, .last rfl rfl (.fixed (.lit (s := 97) rfl dk (.eob rfl))), dk⟩
       intro stream decoded comparable hd
       rcases comparable with ⟨tail, heq⟩ | ⟨tail, heq⟩
       · have hx := Proofs.Layer.ext ha (by simpa only [← heq] using hd)
         simpa only [← hx.2] using (List.prefix_refl [0x61])
       · have hx := Proofs.Layer.ext hd (by simpa only [← heq] using ha)
         simpa only [hx.2] using (List.prefix_refl [0x61]))
    | (intro req h; cases h)

example : stMemA.totalIn = 0 ∧ stMemA.totalOut = 0 ∧ (3 : Nat) > 0 ∧ stMemA.out = [0x61] := ⟨rfl, rfl, by decide, rfl⟩

/-- In the `mem` state every call returns `Z_MEM_ERROR` and changes nothing. -/
example : InflStep stMemA ⟨[0], 10, .noFlush, false⟩ ⟨0, [], Z.memError⟩ stMemA :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## `gzseek` after the end of the data -/

/-- A gzip file of "a", read to its end (`past`). -/
def gzP : GzHandle :=
  { gzR with raw := gzA, dec := [0x61], rpos := 1, past := true, sized := true }

theorem gzA_looks : GzLooksGzip gzA := by unfold GzLooksGzip gzA; decide

/-- `gzseek(f, 5, SEEK_CUR)` returns 6 but `gztell` stays 1 and `gzeof` stays 1: what the real library
does (a quirk). The model allows exactly this. -/
theorem gz_seek_quirk :
    GzSeek gzP 5 1 6 { gzP with rpos := 6 } ∧ ({ gzP with rpos := 6 } : GzHandle).tell = 1 ∧
      GzEof { gzP with rpos := 6 } 1 := by
  refine ⟨?_, by unfold GzHandle.tell; decide, by unfold GzEof; decide⟩
  unfold GzSeek
  refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by decide, rfl, fun h => absurd h (by decide), ?_⟩⟩
  intro _
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h
    rcases h with hc | hc
    · exact absurd gzA_looks hc.2.2.1
    · exact absurd hc (by decide)
  · intro _ _
    exact ⟨rfl, rfl, by decide, by decide⟩

/-- In a transparent file the same seek clears `past`, and `gztell` is the position. -/
def gzC : GzHandle :=
  { gzR with rpos := 2, past := true, sized := true }

theorem gz_seek_copy :
    GzSeek gzC 5 1 7 { gzC with rpos := 7, past := false } ∧
      ({ gzC with rpos := 7, past := false } : GzHandle).tell = 7 := by
  refine ⟨?_, by unfold GzHandle.tell; decide⟩
  unfold GzSeek
  have hc : gzC.CopyMode := ⟨rfl, by decide, fun h => absurd h.1 (by decide), by decide⟩
  refine ⟨fun h => absurd h (by decide), fun _ => Or.inr ⟨by decide, rfl, fun h => absurd h (by decide), ?_⟩⟩
  intro _
  refine ⟨rfl, rfl, fun _ => ⟨by decide, rfl, rfl, by decide⟩, fun h => absurd hc h⟩

end ZlibF.Spec.Api
