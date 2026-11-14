import ZlibF.Proof.«public-compress-safe-call»
import ZlibF.Proof.«deflate.c.universal-init-lit»
import ZlibF.Spec.Safety.Utilities

/-!
# compress.c: the four `compress*` safety goals with no hypothesis

`compress2_z` initialises its stream with `memLevel` 8 (`deflateInit_`), so its symbol buffer has
16384 entries and the overlay room needs no hypothesis (`overlayAt_mid`). The `compress*` proof is
generic in the reachability of the stream it drives (`CompressReach`): here it runs over
`DeflateReachMid`, the histories that start with `deflateInit2_` at `memLevel ≥ 3` and then only
rebuffer the stream and call `deflate`. Along them `lit_bufsize ≥ 512` (`init2_lit`, and every
`deflate` call keeps `lit_bufsize`: `deflate_call_full`), so `Goal.deflate` and the loop facts hold
there with no hypothesis (`goalDeflate_mid`, `loopFacts_mid`).
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal
set_option autoImplicit false

/-- The histories of a deflate stream whose `deflateInit2_` used `memLevel ≥ 3` and which since
then was only rebuffered and passed to `deflate`. Every such history is reachable
(`DeflateReachMid.reach`). -/
inductive DeflateReachMid : Heap → ZStreamRef → Prop
  | init {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr} {level method wb mem strategy : Int32} :
      Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h → r.get h = some z →
      DefaultOrNull z → VersionValue h version (some 49) → 3 ≤ mem.toInt →
      C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h = .ok (Z_OK, after) →
      DeflateReachMid after r
  | rebuffer {h after : Heap} {r : ZStreamRef} : DeflateReachMid h r → Rebuffer h after r → DeflateReachMid after r
  | step {h after : Heap} {r : ZStreamRef} {flush value : Int32} : DeflateReachMid h r →
      StreamArguments h r (.deflate (some r) flush) →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → DeflateReachMid after r

theorem DeflateReachMid.reach {h : Heap} {r : ZStreamRef} (mid : DeflateReachMid h r) :
    StreamReachable .deflate h r := by
  induction mid with
  | init fresh uniq globals get dflt ver _ run => exact .deflateInit fresh uniq globals get dflt ver run
  | rebuffer _ rb ih => exact .rebuffer ih rb (fun e => by cases e)
  | step _ args exec ih => exact .step (call := .deflate (some _) _) ih (fun e => by cases e) ⟨rfl, rfl⟩ args exec

/-- **The invariant along these histories**, with a symbol buffer of at least 512 entries. -/
theorem mid_inv {h : Heap} {r : ZStreamRef} (mid : DeflateReachMid h r) :
    ∃ ds z d, DInv h r ds z d ∧ HeaderInv d ∧ CallFacts d ∧ 512 ≤ d.lit_bufsize.toNat := by
  induction mid with
  | init fresh uniq globals get dflt ver mem3 run =>
    obtain ⟨ds, z, d, inv, lit⟩ := init2_lit fresh uniq globals get dflt ver run
    obtain ⟨ds1, z1, d1, inv1, calls⟩ := init2_inv fresh uniq globals get dflt ver run
    obtain ⟨ds2, z2, d2, inv2, header⟩ := init2_header fresh uniq globals get dflt ver run
    obtain ⟨-, -, e1⟩ := inv.unique inv1.good
    obtain ⟨-, -, e2⟩ := inv.unique inv2.good
    exact ⟨ds, z, d, inv, e2 ▸ header, e1 ▸ calls, lit mem3⟩
  | rebuffer _ rb ih =>
    obtain ⟨ds, z, d, inv, header, calls, lit⟩ := ih
    obtain ⟨z', _, inv'⟩ := inv.rebuffer rb
    exact ⟨ds, z', d, inv', header, calls, lit⟩
  | @step h after r flush value _ args exec ih =>
    obtain ⟨ds, z, d, inv, header, calls, lit⟩ := ih
    obtain ⟨buffers, active⟩ := args
    obtain ⟨rc, after', z', d', _, _, run, inv', header', calls', _, _, _, _, litEq⟩ :=
      Call.deflate_call_full inv (Block.overlayAt_mid lit) header calls buffers active flush
    have exec' : Call.execute (.deflate (some r) flush) default h = .ok ((rc, default), after') := by
      simp [Call.execute, heapCall, C.run] at run ⊢
      rw [run]
    have same := exec.symm.trans exec'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    exact ⟨ds, z', d', inv', header', calls', by rw [litEq]; exact lit⟩

/-- **`Goal.deflate` along these histories**, with no hypothesis. -/
theorem goalDeflate_mid : GoalDeflateFor DeflateReachMid := by
  intro h r i z s flush mid good buffers active
  obtain ⟨ds, z₀, d, inv, header, calls, lit⟩ := mid_inv mid
  obtain ⟨rfl, rfl, rfl⟩ := inv.unique good
  obtain ⟨rc, after, z', d', used, out, run, invAfter, -, -, clauses, -, -, -, -⟩ :=
    Call.deflate_call_full inv (Block.overlayAt_mid lit) header calls buffers active flush
  exact ⟨rc, after, z', d', used, out, run, invAfter.dgood, clauses⟩

/-- **The loop facts of `compress*` along these histories**, with no hypothesis. -/
theorem loopFacts_mid : DeflateLoopFactsFor DeflateReachMid := by
  intro h r i z s flush rc after mid good buffers active run
  obtain ⟨ds, z0, d0, inv, header, calls, lit⟩ := mid_inv mid
  obtain ⟨e1, e2, e3⟩ := dgood_unique inv.good good
  subst e1 e2 e3
  obtain ⟨rc', after', z', d', used, out, run', inv', -, -, -, owned, prog, gz, -⟩ :=
    Call.deflate_call_full inv (Block.overlayAt_mid lit) header calls buffers active flush
  have same := Except.ok.inj (run'.symm.trans run)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  refine ⟨?_, ?_, ?_⟩
  · intro notRef nf ain aout _ z'' get
    have status : d0.status ≠ FINISH_STATE := by
      intro fs
      apply notRef
      right; right; right; right
      refine ⟨fs, ?_⟩
      rw [nf]; decide
    have e : z'' = z' := Option.some.inj (get.symm.trans inv'.good.live.hz)
    subst e
    exact prog notRef aout ain status
  · intro notRef fs ain
    exact finished_new_input inv buffers active run notRef fs ain
  · intro z'' s'' good''
    obtain ⟨-, -, es⟩ := dgood_unique good'' inv'.good
    subst es
    exact ⟨gz, fun b => (owned b).symm⟩

/-- `compress2_z`'s `deflateInit_` (memLevel 8), its rebuffers and its `deflate` calls stay in
`DeflateReachMid`. -/
theorem compressReach_mid : CompressReach DeflateReachMid where
  init fresh uniq globals get dflt ver run := .init fresh uniq globals get dflt ver (by decide) run
  rebuffer mid rb := .rebuffer mid rb
  step mid args exec := .step mid args exec

/-- **`Goal.compress2_z_safety`**, with no hypothesis. -/
theorem compress2_z_safety : Goal.compress2_z_safety :=
  compress2_z_safety_gen compressReach_mid goalDeflate_mid loopFacts_mid

/-- **`Goal.compress_z_safety`**, with no hypothesis. -/
theorem compress_z_safety : Goal.compress_z_safety :=
  compress_z_safety_gen compressReach_mid goalDeflate_mid loopFacts_mid

/-- **`Goal.compress2_safety`**, with no hypothesis. -/
theorem compress2_safety : Goal.compress2_safety :=
  compress2_safety_gen compressReach_mid goalDeflate_mid loopFacts_mid

/-- **`Goal.compress_safety`**, with no hypothesis. -/
theorem compress_safety : Goal.compress_safety :=
  compress_safety_gen compressReach_mid goalDeflate_mid loopFacts_mid

end ZlibF.Spec.Public.Proofs.Compress
