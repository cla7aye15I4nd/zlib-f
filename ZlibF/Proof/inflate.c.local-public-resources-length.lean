import ZlibF.Proof.«inflate.c.local-public-resources-fast-length»
import ZlibF.Proof.«inflate.c.local-public-resources-slow-length»
import ZlibF.Proof.«inflate.c.length-mode-output-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Both actual LEN implementations write exactly their produced prefix.
The real fast guard selects the full fast execution; all other callers use
the proved slow length/distance/MATCH chain. -/
theorem inflate_LEN_exact_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN) :
    ∃ outcome regs after stream state made,
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  have active : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · obtain ⟨regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_LEN_fast_exact_frame E invariant buffers active fast
    exact ⟨.ok (), regs, after, stream, state, made, run, current.good, count, put, frame⟩
  · exact inflate_LEN_slow_exact_frame E invariant.good (invariant.tables active) buffers
      (by rw [invariant.pending.sane]; decide) fast

/-- LEN_ establishes the same initialized relation at LEN before entering
its real slow or fast continuation. No caller-domain restriction is added. -/
theorem inflate_LEN_start_exact_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_) :
    ∃ outcome regs after stream state made,
      runX (inflate_LEN_ c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  let current := { s with mode := LEN }
  let heap := setI h zs current
  have stateFrame : DecodeStateFrame s current := rfl
  have good := invariant.good.decode_update stateFrame
    (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have oldMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  have tables := (invariant.tables oldMode).decode_update invariant.good.live.hs stateFrame
  have pending : DataPendingInvariant current := by
    apply dataPendingInvariant_idle (s := current) invariant.pending.sane
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have decoded := invariant.toLocalDecodeJ.decode_update good (fun _ => tables)
    pending stateFrame
    (by change DataExitMode LEN; exact Or.inl (by unfold DataTableMode; decide))
    (byte_view_sizes_setI h zs current) rfl
  have currentJ : LocalStateJ heap cutoff r zs z current :=
    ⟨decoded, invariant.requestedBits, invariant.requestedWrap,
      Or.inr (Or.inr (Or.inr (Or.inr (invariant.data_format oldMode)))),
      ⟨invariant.roots.stream, invariant.roots.state, invariant.roots.window⟩⟩
  have packet : DispatchBuffers heap r l bs :=
    dispatch_byte_views_local buffers invariant.good good rfl
      (byte_view_get_setI h zs current) (byte_view_ro_setI h zs current)
  have env1 : Env c heap r zs z current := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
  obtain ⟨outcome, regs, after, stream, state, made, run, final, count, put, frame⟩ :=
    inflate_LEN_exact_frame env1 currentJ packet rfl
  have source : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := by
    unfold inflate_LEN_
    rw [runX_bind, runX_setMode E]
  have actual := source.trans run
  obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
    callerRange_slow_output invariant.good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  have metadata := fastMemoryMetaFrameX_inflate_LEN_ r c E.strm l h outcome regs after actual
  have ro : after.ro = h.ro := congrArg Prod.fst metadata
  have writable : Space.ro after dest = false := by
    cases dest <;> simp only [Space.ro] at write ⊢
    all_goals first | exact write | (rw [ro]; exact write) | rfl
  refine ⟨outcome, regs, after, stream, state, made, actual, final, count, put, ?_⟩
  rw [pointer] at frame ⊢
  have frame' : BufferFrame (setI (r.put h z) zs current) after
      (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
    simpa only [ZStreamRef.put_self E.hz] using frame
  exact metadata_then_output_buffer_frame E.hz E.hs get write frame' writable

#print axioms inflate_LEN_exact_frame
#print axioms inflate_LEN_start_exact_frame
end Zlib.Inflate.Local
