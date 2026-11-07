import ZlibF.Proof.«deflate.c.engine.block-reset»
import ZlibF.Proof.«trees.c.header-decode»

/-! # Actual tree constructors retain the compressor's complete heap representation -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (TK BTBuildFrame)
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Tree construction changes the embedded depth bytes, but keeps their
extent. Caller byte ranges therefore retain their admitted capacities. -/
theorem tree_record_sizes {h : Heap} {ds : Nat} {d result : DeflateState}
    (state : h.dstates ds = some d) (depth : result.depth.size = d.depth.size) :
    ByteSizes h (setD h ds result) := by
  refine ⟨?_, fun ref => by cases ref <;> rfl⟩
  intro ref a get
  cases ref with
  | dstate_depth i =>
    by_cases same : i = ds
    · subst i
      have equal : d.depth = a := by simpa only [Space.get, state, Option.map_some, Option.some.injEq] using get
      exact ⟨result.depth, by simp [Space.get], depth.trans (congrArg Array.size equal)⟩
    · exact ⟨a, by simpa [Space.get, setD, upd_ne _ _ _ _ same] using get, rfl⟩
  | blk _ | str _ | st_dist_code | st_length_code => exact ⟨a, get, rfl⟩

/-- The actual complete construction footprint retains DGood. No
constructor or tree invariant is a caller assumption: its checked frame
supplies the changed array sizes, and treesInvAt derives its representation. -/
theorem tree_build_frame_good {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d result : DeflateState} {buf : Array UInt8} {tk : TK}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (frame : BTBuildFrame tk tk d result) :
    DGood (setD h ds result) r ds z result := by
  have treesA := frame.treesInvAt trees
  have inv : DStInv h ds result := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [fields] at treesA ⊢
    cases tk <;>
      exact { good.inv with wf := treesA.base.wf
                            blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have shape := shape_setD good.live.hs result
  refine ⟨?_, DStInv.congr (h := h) (h' := setD h ds result) rfl rfl rfl rfl inv,
    shape.uniq good.uniq, shape.fresh rfl good.fresh, ⟨result, pb, buf, treesA⟩⟩
  have back : result.strm = d.strm := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [fields]
    cases tk <;> rfl
  have status : result.status = d.status := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [fields]
    cases tk <;> rfl
  exact ⟨by simpa only [ZStreamRef.get_setD] using good.live.hz, by simp, good.live.zst,
    back.trans good.live.back, status ▸ good.live.status, good.live.zalloc, good.live.zfree⟩

/-- `local void build_tree(deflate_state *s, tree_desc *desc)`.
Each installed alphabet's actual construction executes on the compressor
heap. The complete caller representation, buffers and allocation ledger
survive its real work-array and descriptor updates. Output bits are
unchanged. The record frame exposes every changed field for stronger
engine invariants. The cost/overlay bound is a separate obligation. -/
theorem build_tree_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (tk : TK) :
    ∃ result,
      Zlib.Trees.build_tree (some (.tab ds)) (some (tk.descRef ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ BTBuildFrame tk tk d result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨value, result, run, frame⟩ := Zlib.Trees.Proofs.ws_build_tree_frame_initialized
    (h0 := h) tk trees.base.wf trees.base.static trees.run.to0
  have unit : value = () := Subsingleton.elim _ _
  subst value
  rw [Zlib.Trees.Proofs.setD_self trees.base.dstate] at run
  have goodA := tree_build_frame_good good trees frame
  have depth : result.depth.size = d.depth.size := by
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _t, _h, depth, _b⟩ := frame
    rw [fields]
    cases tk <;> exact depth
  have sizes := tree_record_sizes good.live.hs depth
  have owned : ∀ b, StreamOwned (setD h ds result) r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA, stream_owned_deflate good]
    obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [fields]
    cases tk <;> rfl
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := buf)
    good.live.hs trees.base.bytes
  rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes] at storage
  exact ⟨result, run, goodA, frame.treesInvAt trees,
    stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z),
    sizes, storage, frame, frame.outBits buf⟩

/-- The adjacent actual literal and distance constructors establish BLInput
on the same returned compressor heap. Complete engine ownership and caller
ranges survive both calls; their source-tree frames stay available. -/
theorem source_trees_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    ∃ literal result,
      Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ Zlib.Trees.Proofs.BLInput result ∧
      BTBuildFrame .lit .lit d literal ∧ BTBuildFrame .dist .dist literal result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨literal, runL, goodL, treesL, buffersL, sizesL, storageL, frameL, bitsL⟩ :=
    build_tree_engine (ob := ob) good trees buffers .lit
  obtain ⟨result, runD, goodD, treesD, buffersD, sizesD, storageD, frameD, bitsD⟩ :=
    build_tree_engine (ob := ob) goodL treesL buffersL .dist
  have prepare : Zlib.Trees.Proofs.blPrepare (some (.tab ds)) h = .ok ((), setD h ds result) := by
    have ptrL : Zlib.Trees.pLdesc (some (.tab ds)) h = .ok (some (.in_dstate_l_desc ds), h) := by
      simp only [Zlib.Trees.pLdesc, bind_app, Zlib.Trees.Proofs.Out.sid_run good.live.hs]
      rfl
    have ptrD : Zlib.Trees.pDdesc (some (.tab ds)) (setD h ds literal) =
        .ok (some (.in_dstate_d_desc ds), setD h ds literal) := by
      simp only [Zlib.Trees.pDdesc, bind_app, Zlib.Trees.Proofs.Out.sid_run goodL.live.hs]
      rfl
    unfold Zlib.Trees.Proofs.blPrepare
    simp only [bind_app, ptrL, ptrD, TK.descRef] at runL runD ⊢
    rw [runL]
    simp only [bind_app, ptrD]
    simpa only [setD_setD] using runD
  obtain ⟨other, prepared, input, _trees, _bl, _bits⟩ := Zlib.Trees.Proofs.bl_prepare trees
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs prepare prepared
  have sizes := sizesL.trans sizesD
  have storage := storageL.trans storageD
  simp only [setD_setD] at goodD treesD buffersD sizes storage
  exact ⟨literal, result, prepare, goodD, treesD, buffersD, sizes, storage,
    same ▸ input, frameL, frameD, bitsD.trans bitsL⟩

end Zlib.Deflate.Engine.Proofs
