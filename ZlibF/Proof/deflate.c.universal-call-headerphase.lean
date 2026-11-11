import ZlibF.Proof.«deflate.c.universal-call-markers»

/-!
# deflate.c: the header phase of one `deflate` call

Batch C (`deflate_header_trailer`). `headerPhase` is the chain of the header stages
(`header_stages`); a stage whose status test fails passes the heap on unchanged.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

section skip
variable {h : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} (state : h.dstates ds = some d) (k : M Int32)
include state

theorem wrap_stage_skip (no : ¬ (d.status = INIT_STATE ∧ d.wrap = 0)) :
    wrapStage (some r) (some (.tab ds)) k h = k h := by
  unfold wrapStage
  by_cases st : d.status = INIT_STATE
  · have w : d.wrap ≠ 0 := fun e => no ⟨st, e⟩
    simp [bind_app, rdD_eq, state, st, w]
  · simp [bind_app, rdD_eq, state, st]

theorem wrap_stage_busy (st : d.status = INIT_STATE) (w : d.wrap = 0) :
    wrapStage (some r) (some (.tab ds)) k h = k (setD h ds { d with status := BUSY_STATE }) := by
  unfold wrapStage
  simp [bind_app, rdD_eq, state, st, w, wrD_eq]

theorem init_stage_skip (no : d.status ≠ INIT_STATE) : initStage (some r) (some (.tab ds)) k h = k h := by
  unfold initStage; simp [bind_app, rdD_eq, state, no]

theorem gzip_stage_skip (no : d.status ≠ GZIP_STATE) : gzipStage (some r) (some (.tab ds)) k h = k h := by
  unfold gzipStage; simp [bind_app, rdD_eq, state, no]

theorem extra_stage_skip (no : d.status ≠ EXTRA_STATE) : extraStage (some r) (some (.tab ds)) k h = k h := by
  unfold extraStage; simp [bind_app, rdD_eq, state, no]

theorem name_stage_skip (no : d.status ≠ NAME_STATE) : nameStage (some r) (some (.tab ds)) k h = k h := by
  unfold nameStage; simp [bind_app, rdD_eq, state, no]

theorem comment_stage_skip (no : d.status ≠ COMMENT_STATE) : commentStage (some r) (some (.tab ds)) k h = k h := by
  unfold commentStage; simp [bind_app, rdD_eq, state, no]

theorem hcrc_stage_skip (no : d.status ≠ HCRC_STATE) : hcrcStage (some r) (some (.tab ds)) k h = k h := by
  unfold hcrcStage; simp [bind_app, rdD_eq, state, no]

end skip

end Zlib.Deflate.Universal.Call
