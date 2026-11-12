import ZlibF.Proof.«public-compress-safe-init»
import ZlibF.Proof.«deflate.c.universal-call-clauses»

/-!
# compress.c: `DeflateLoopFacts` from the deflate skeleton

`DeflateLoopFacts`, the hypothesis of the `compress*` safety proofs beside `Goal.deflate`, follows
from the statements of three skeleton lemmas of the deflate owner (`reachable_inv`,
`deflate_call` with `CallClauses`, `call_frame`) and one fact that `CallClauses` does not state
yet, `FinishedNewInput`. Each is an explicit hypothesis of exactly the skeleton's type, so the
derivation closes when they are proved.

* progress without `Z_FINISH`: the progress clause of `CallClauses` (a `Z_NO_FLUSH` call on a
  finished stream is refused);
* the owned blocks: the ownership clause of `CallClauses`, for every call;
* the gzip header pointer: `call_frame`;
* new input after the first `Z_FINISH`: `FinishedNewInput`.
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal
set_option autoImplicit false

/-- The statement of the skeleton lemma `reachable_inv`. -/
def ReachableInv : Prop :=
  ∀ {h : Heap} {r : ZStreamRef}, StreamReachable .deflate h r → ∃ ds z d, DInv h r ds z d ∧ HeaderInv d

/-- The statement of the skeleton lemma `deflate_call`. -/
def DeflateCall : Prop :=
  ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → StreamBuffers h r → ActiveHeader h r → ∀ flush : Int32,
    ∃ rc after z' d' used out,
      C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
      DInv after r ds z' d' ∧ CallClauses h r ds z d flush rc after z' d' used out

/-- The statement of the skeleton lemma `call_frame`. -/
def CallFrameFacts : Prop :=
  ∀ {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush rc : Int32},
    DInv h r ds z d → StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    ∃ z' d', r.get after = some z' ∧ after.dstates ds = some d' ∧
      d'.level = d.level ∧ d'.w_bits = d.w_bits ∧ d'.hash_bits = d.hash_bits ∧ d'.gzhead = d.gzhead ∧
      (z'.avail_out = z.avail_out → d'.wrap = d.wrap) ∧
      (0 < d.wrap.toInt → (d.status = INIT_STATE ∨ d.status = GZIP_STATE) →
        ¬ DeflateRefuses z d flush → z.avail_out ≠ 0 → z'.avail_out.toNat < z.avail_out.toNat)

/-- New input after the first `Z_FINISH`: a call that is not refused either returns
`Z_BUF_ERROR` or writes a byte (pending output is flushed before `deflate.c` checks
`s->status == FINISH_STATE && strm->avail_in != 0`). Not in `CallClauses` yet. -/
def FinishedNewInput : Prop :=
  ∀ {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush rc : Int32},
    DInv h r ds z d → StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    ¬ DeflateRefuses z d flush → d.status = FINISH_STATE → z.avail_in ≠ 0 →
    rc = Z_BUF_ERROR ∨ ∀ z', r.get after = some z' → z'.avail_out ≠ z.avail_out

/-- `DGood` determines the state index, the record and the state. -/
theorem dgood_unique {h : Heap} {r : ZStreamRef} {i i' : Nat} {z z' : ZStream} {s s' : DeflateState}
    (g : DGood h r i z s) (g' : DGood h r i' z' s') : i = i' ∧ z = z' ∧ s = s' := by
  have ez : z = z' := Option.some.inj (g.live.hz.symm.trans g'.live.hz)
  subst ez
  have ei : i = i' := by
    have both := g.live.zst.symm.trans g'.live.zst
    cases both
    rfl
  subst ei
  exact ⟨rfl, rfl, Option.some.inj (g.live.hs.symm.trans g'.live.hs)⟩

/-- `DeflateLoopFacts` from the deflate skeleton. -/
theorem deflate_loop_facts_of (reach : ReachableInv) (call : DeflateCall) (frame : CallFrameFacts)
    (finished : FinishedNewInput) : DeflateLoopFacts := by
  intro h r i z s flush rc after reachable good buffers active run
  obtain ⟨ds, z0, d0, inv, -⟩ := reach reachable
  obtain ⟨e1, e2, e3⟩ := dgood_unique inv.good good
  subst e1 e2 e3
  obtain ⟨rc', after', z', d', used, out, run', inv', ⟨goal, owned, prog⟩⟩ := call inv buffers active flush
  have same := Except.ok.inj (run'.symm.trans run)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨acc, -⟩ := goal
  obtain ⟨-, -, aIn, aOut, -⟩ := acc
  have hz' : r.get after' = some z' := inv'.good.live.hz
  refine ⟨?_, ?_, ?_⟩
  · intro notRef nf ain aout rcOk z'' hz''
    have ez : z'' = z' := Option.some.inj (hz''.symm.trans hz')
    subst ez
    have status : d0.status ≠ FINISH_STATE := by
      intro fs
      apply notRef
      right; right; right; right
      refine ⟨fs, ?_⟩
      rw [nf]; decide
    rcases prog notRef aout ain status rcOk with u | o
    · left; intro e; apply u
      have := congrArg UInt32.toNat e
      omega
    · right; intro e; apply o
      have := congrArg UInt32.toNat e
      exact List.eq_nil_of_length_eq_zero (by omega)
  · intro notRef fs ain
    exact finished inv buffers active run notRef fs ain
  · intro z'' s'' good''
    obtain ⟨-, -, es⟩ := dgood_unique good'' inv'.good
    subst es
    obtain ⟨zf, df, hzf, hdf, -, -, -, gz, -⟩ := frame inv buffers active run
    have edf : df = s'' := Option.some.inj (hdf.symm.trans good''.live.hs)
    subst edf
    exact ⟨gz, fun b => (owned b).symm⟩

#print axioms deflate_loop_facts_of

end ZlibF.Spec.Public.Proofs.Compress
