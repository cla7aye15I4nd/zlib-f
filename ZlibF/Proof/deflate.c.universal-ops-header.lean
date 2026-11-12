import ZlibF.Proof.«deflate.c.universal-ops-dispatch»
import ZlibF.Proof.«deflate.c.universal-header-inv»

/-!
# deflate.c: the header facts after one stream operation (`operation_header`)

`HeaderInv` (beside `DInv`) after each operation of `StreamOperation .deflate`, case by case. The
operations that do not write the stream record keep its state pointer, so the state after the
call sits at the same block; batch C's lemmas (`deflate.c.universal-header-inv`) then give the
header facts of that state. The operations whose header lemma is not yet a theorem are hypotheses
of `operation_header_of`: `deflate` (its header phase), `deflateParams` and `deflateSetDictionary`.
A direct `deflateResetKeep` is not a stream operation (`StreamOperation`).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

theorem heapCall_ok {α : Type} {p : M α} {h H : Heap} {v : α} {fs : Zlib.GzFs.Fs}
    (e : heapCall p default h = .ok ((v, fs), H)) : p h = .ok (v, H) := by
  unfold heapCall at e
  cases hp : p h with
  | error err => rw [hp] at e; cases e
  | ok q =>
    obtain ⟨a, h1⟩ := q
    rw [hp] at e
    cases e
    rfl

/-- After a call that keeps the state pointer of the stream record, the invariant of the result
names the state at the same block. -/
theorem state_after {after : Heap} {r : ZStreamRef} {ds ds' : Nat} {zA z' : ZStream} {d' : DeflateState}
    (getA : r.get after = some zA) (stA : zA.state = some (.deflate ds))
    (invAfter : DInv after r ds' z' d') : after.dstates ds = some d' := by
  have e : zA = z' := Option.some.inj (getA.symm.trans invAfter.good.live.hz)
  subst e
  rw [invAfter.good.live.zst] at stA
  cases stA
  exact invAfter.good.live.hs

/-- A call that leaves the heap unchanged keeps the header facts. -/
theorem header_unchanged {h : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream} {d d' : DeflateState}
    (inv : DInv h r ds z d) (header : HeaderInv d) (invAfter : DInv h r ds' z' d') : HeaderInv d' := by
  obtain ⟨-, -, e⟩ := inv.unique invAfter.good
  rw [e]
  exact header

/-- **`operation_header` from the open header lemmas.** Hypotheses (not yet theorems):
`deflateHeader` (the header phase of `deflate`), `paramsHeader` and `setDictionaryHeader`.
Premise: the between-calls facts `calls` (which `params_header` reads). -/
theorem operation_header_of
    (deflateHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
      {d d' : DeflateState} {flush rc : Int32}, DInv h r ds z d → HeaderInv d → StreamBuffers h r →
      ActiveHeader h r → C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
      DInv after r ds' z' d' → HeaderInv d')
    (paramsHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
      {d d' : DeflateState} {level strategy rc : Int32}, DInv h r ds z d → CallFacts d → HeaderInv d →
      StreamBuffers h r →
      ActiveHeader h r → C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after) →
      DInv after r ds' z' d' → HeaderInv d')
    (setDictionaryHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
      {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}, DInv h r ds z d →
      HeaderInv d → CallFacts d → CallerRange h r dictionary dictLength.toNat false →
      C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after) →
      DInv after r ds' z' d' → HeaderInv d')
    {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {call : Call} {value : call.Result}
    (inv : DInv h r ds z d) (header : HeaderInv d) (calls : CallFacts d)
    (operation : StreamOperation .deflate r call)
    (args : StreamArguments h r call) (run : call.execute default h = .ok ((value, default), after))
    (invAfter : DInv after r ds' z' d') : HeaderInv d' := by
  have good := inv.good
  have hL := good.live
  cases call
  all_goals first
    | (exfalso; simp [StreamOperation] at operation; done)
    | skip
  case deflate p flush =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨buffers, act⟩ := args
    exact deflateHeader inv header buffers act (heapCall_ok run) invAfter
  case deflateReset p =>
    simp [StreamOperation] at operation
    subst operation
    have r' := heapCall_ok run
    obtain ⟨a1, a2, a3, q, qa, h', run', -, -, -, -, -, he, -, -⟩ := deflateReset_safe good
    have same := r'.symm.trans run'
    cases same
    have getA : r.get after = some (rkZ z d) := by
      rw [he]; simp [ZStreamRef.get_put_same hL.hz]
    exact reset_header good r' (state_after getA (by simpa [rkZ] using hL.zst) invAfter)
  case deflateParams p level strategy =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨buffers, act⟩ := args
    exact paramsHeader inv calls header buffers act (heapCall_ok run) invAfter
  case deflatePrime p bits value' =>
    simp [StreamOperation] at operation
    subst operation
    have r' := heapCall_ok run
    have same := prime_stream inv r'
    exact prime_header inv header r' (state_after (same.trans hL.hz) hL.zst invAfter)
  case deflateGetDictionary p dictionary hasDictLength =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨z1, i, s, get, zst, hs, range⟩ := args
    have zz : z1 = z := Option.some.inj (get.symm.trans hL.hz)
    subst zz
    rw [hL.zst] at zst
    cases zst
    have ss : s = d := Option.some.inj (hs.symm.trans hL.hs)
    subst ss
    obtain ⟨h', run', -, str', dst, -⟩ :=
      getDictionary_view inv dictionary hasDictLength range (fun _ => False)
    have same := (heapCall_ok run).symm.trans run'
    cases same
    have getA : r.get after = some z1 := by rw [str']; exact hL.hz
    have state := state_after getA hL.zst invAfter
    rw [dst, hL.hs] at state
    cases state
    exact header
  case deflateSetDictionary p dictionary dictLength =>
    simp [StreamOperation] at operation
    subst operation
    exact setDictionaryHeader inv header calls args (heapCall_ok run) invAfter
  case deflateSetHeader p head =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, z1, i, s, get, zst, hs, started⟩ := args
    have zz : z1 = z := Option.some.inj (get.symm.trans hL.hz)
    subst zz
    rw [hL.zst] at zst
    cases zst
    have ss : s = d := Option.some.inj (hs.symm.trans hL.hs)
    subst ss
    have r' := heapCall_ok run
    have getA : r.get after = some z1 := by
      by_cases wrap : s.wrap = 2
      · obtain ⟨h', run', rfl, -, -⟩ := deflateSetHeader_safe good wrap head (gzOk_any h head)
        have same := r'.symm.trans run'
        cases same
        simpa using hL.hz
      · have same := r'.symm.trans (deflateSetHeader_run_other hL wrap head)
        cases same
        exact hL.hz
    exact setHeader_header good header started r' (state_after getA hL.zst invAfter)
  case deflateTune p g m n c =>
    simp [StreamOperation] at operation
    subst operation
    have r' := heapCall_ok run
    obtain ⟨h', run', rfl, -, -⟩ := deflateTune_safe good g m n c
    have same := r'.symm.trans run'
    cases same
    exact tune_header good header r' (state_after (by simpa using hL.hz) hL.zst invAfter)
  case deflatePending p hasPending hasBits =>
    simp [StreamOperation] at operation
    subst operation
    have same := (heapCall_ok run).symm.trans (deflatePending_run hL hasPending hasBits)
    cases same
    exact header_unchanged inv header invAfter
  case deflateUsed p hasBits =>
    simp [StreamOperation] at operation
    subst operation
    have same := (heapCall_ok run).symm.trans (deflateUsed_run hL hasBits)
    cases same
    exact header_unchanged inv header invAfter
  case deflateBound p n =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, live⟩ := args
    obtain ⟨wl, -, run'⟩ := deflateBound_safe good (hdrStrOk_of_live inv live) n
    have same := (heapCall_ok run).symm.trans run'
    cases same
    exact header_unchanged inv header invAfter
  case deflateBound_z p n =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, live⟩ := args
    obtain ⟨wl, -, run'⟩ := deflateBound_z_safe good (hdrStrOk_of_live inv live) n
    have same := (heapCall_ok run).symm.trans run'
    cases same
    exact header_unchanged inv header invAfter

end Zlib.Deflate.Universal
