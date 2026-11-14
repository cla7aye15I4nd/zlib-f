import ZlibF.Spec.Public.StreamQueries
import ZlibF.Proof.«deflate.c.base»
import ZlibF.Spec.Functional.StreamQueries

namespace ZlibF.Spec.Public.DeflateQueryProof
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs

theorem refused_deflate_dom {h : Heap} {p : ZStreamPtr} (hr : RefusedDeflate h p) : StreamDom h p := by
  rcases hr with hnull | ⟨r,z,rfl,hz,hbad⟩
  · exact Or.inl hnull
  · refine Or.inr ⟨r,z,rfl,hz,?_⟩
    rcases hbad with hza | hzf | hs | ⟨i,s,hstate,hsi,_⟩
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzf)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr ⟨i,s,hstate,hsi⟩))

theorem refused_deflate_not_init {h : Heap} {p : ZStreamPtr} (hr : RefusedDeflate h p) : ¬ DInitialised h p := by
  intro ⟨r',i',z',s',hp,hL⟩
  rcases hr with hn | ⟨r,z,hp',hz,hbad⟩
  · rw [hn] at hp; cases hp
  · rw [hp'] at hp
    cases hp
    have heq : z = z' := Option.some.inj (hz.symm.trans hL.hz)
    subst z'
    rcases hbad with ha | hf | hstate | ⟨i,s,hi,hs,hfail⟩
    · exact hL.zalloc ha
    · exact hL.zfree hf
    · have hh := hL.zst
      rw [hstate] at hh; cases hh
    · have hieq : i = i' := by
        have hh := hL.zst
        rw [hi] at hh
        cases hh
        rfl
      subst i'
      have hseq : s = s' := Option.some.inj (hs.symm.trans hL.hs)
      subst s'
      rcases hfail with hback | hstatus
      · exact hback hL.back
      · exact hstatus hL.status

theorem view_dlive {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : DeflateState}
    (hv : DeflateView h r i z s) : DLive h r i z s := by
  rcases hv with ⟨hz,hstate,hi,hback,ha,hf,hstatus⟩
  exact ⟨hz,hi,hstate,hback,hstatus,ha,hf⟩

/-- `int deflateUsed(z_streamp strm, int *bits)` reads the optional bit count. -/
theorem used_public : Goal.deflateUsed := by
  intro bits
  constructor
  · intro h p hr
    unfold deflateUsed
    exact check_refuse (refused_deflate_dom hr) (refused_deflate_not_init hr) _ _
  · intro h r i z s hv
    have hl := view_dlive hv
    show deflateUsed (some r) bits h = _
    unfold deflateUsed
    dsimp' [stateCheck_live hl, hl.zst, hl.hz, hl.hs]

/-- `int deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain)` updates four tuning fields. -/
theorem tune_public : Goal.deflateTune := by
  intro good lazy nice chain
  constructor
  · intro h p hr
    unfold deflateTune
    exact check_refuse (refused_deflate_dom hr) (refused_deflate_not_init hr) _ _
  · intro h r i z s hv
    have hl := view_dlive hv
    show deflateTune (some r) good lazy nice chain h = _
    unfold deflateTune
    dsimp' [stateCheck_live hl, hl.zst, hl.hz, hl.hs, putDeflate, setD]

/-- `int deflateSetHeader(z_streamp strm, gz_headerp head)` stores the header only for gzip streams. -/
theorem header_public : Goal.deflateSetHeader := by
  intro head
  constructor
  · intro h p hr
    unfold deflateSetHeader
    exact check_refuse (refused_deflate_dom hr) (refused_deflate_not_init hr) _ _
  · intro h r i z s hv
    have hl := view_dlive hv
    show deflateSetHeader (some r) head h = _
    unfold deflateSetHeader
    by_cases hw : s.wrap = 2
    · dsimp' [stateCheck_live hl, hl.zst, hl.hz, hl.hs, putDeflate, setD, hw]
    · dsimp' [stateCheck_live hl, hl.zst, hl.hz, hl.hs, hw]

def pendingResult (d : DeflateState) (hasPending hasBits : Bool) : Int32 × Option UInt32 × Option Int32 :=
  let bits := if hasBits then some d.bi_valid else none
  if hasPending then
    if d.pending.toUInt32.toUInt64 != d.pending then (Z_BUF_ERROR, some 0xffffffff, bits)
    else (Z_OK, some d.pending.toUInt32, bits)
  else (Z_OK, none, bits)

theorem deflatePending_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hasPending hasBits : Bool) :
    deflatePending (some r) hasPending hasBits h = .ok (pendingResult d hasPending hasBits, h) := by
  unfold deflatePending
  cases hasPending <;> cases hasBits <;> dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, pendingResult] <;>
    split <;> simp_all


theorem pending_cast_iff (x : UInt64) :
    x.toUInt32.toUInt64 = x ↔ x.toNat < 2 ^ 32 := by
  constructor
  · intro he
    have hn := congrArg UInt64.toNat he
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32] at hn
    have hm := Nat.mod_lt x.toNat (by decide : 0 < 2 ^ 32)
    rw [hn] at hm
    exact hm
  · intro hn
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hn]

/-- `int deflatePending(z_streamp strm, unsigned *pending, int *bits)` returns
the exact public result for an accepted state, including oversized pending
counts and both optional outputs. It does not modify the heap. -/
theorem deflatePending_public {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : DeflateState}
    (hl : DLive h r i z s) (pending bits : Bool) :
    C.run (deflatePending (some r) pending bits) h =
      .ok (((if pending ∧ 2 ^ 32 ≤ s.pending.toNat then Z_BUF_ERROR else Z_OK),
        if pending then some (if 2 ^ 32 ≤ s.pending.toNat then 0xffffffff else s.pending.toUInt32) else none,
        if bits then some s.bi_valid else none), h) := by
  have hr := deflatePending_run hl pending bits
  have hc := pending_cast_iff s.pending
  by_cases hp : pending = true
  · subst pending
    by_cases ho : 2 ^ 32 ≤ s.pending.toNat
    · have hne : s.pending.toUInt32.toUInt64 ≠ s.pending := fun he => by have := hc.mp he; omega
      have hr' := hr
      simp only [pendingResult, ite_true, bne_iff_ne] at hr'
      split at hr'
      · simpa [C.run, ho] using hr'
      · rename_i hc2
        exact (hc2 hne).elim
    · have he : s.pending.toUInt32.toUInt64 = s.pending := hc.mpr (by omega)
      simpa [C.run, pendingResult, he, ho] using hr
  · have hp' : pending = false := by cases pending <;> simp_all
    subst pending
    simpa [C.run, pendingResult] using hr


/-- `int deflatePending(z_streamp strm, unsigned *pending, int *bits)` returns both optional values and detects a 32-bit overflow. -/
theorem pending_public : Goal.deflatePending := by
  intro pending bits
  constructor
  · intro h p hr
    unfold deflatePending
    exact check_refuse (refused_deflate_dom hr) (refused_deflate_not_init hr) _ _
  · intro h r i z state hv
    exact deflatePending_public (view_dlive hv) pending bits

#print axioms pending_public
#print axioms used_public
#print axioms tune_public
#print axioms header_public
end ZlibF.Spec.Public.DeflateQueryProof
