import ZlibF.Spec.Public.StreamQueries
import ZlibF.Proof.«inflate.c.base»

namespace ZlibF.Spec.Public.InflateQueryProof
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

theorem refused_dom {h : Heap} {p : ZStreamPtr} (hr : RefusedInflate h p) : StreamDom h p := by
  rcases hr with hnull | ⟨r,z,rfl,hz,hbad⟩
  · exact Or.inl hnull
  · refine Or.inr ⟨r,z,rfl,hz,?_⟩
    rcases hbad with hza | hzf | hs | ⟨i,s,hstate,hsi,_⟩
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzf)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr ⟨i,s,hstate,hsi⟩))

theorem refused_not_initialised {h : Heap} {p : ZStreamPtr} (hr : RefusedInflate h p) : ¬ Initialised h p := by
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
      rcases hfail with hback | hlo | hhi
      · exact hback hL.back
      · exact (UInt32.not_lt.mpr hL.mode.1) hlo
      · exact (UInt32.not_lt.mpr hL.mode.2) hhi

/-- `int inflateSyncPoint(z_streamp strm)` tests the stored-block boundary. -/
theorem syncpoint_public : Goal.inflateSyncPoint := by
  constructor
  · intro h p hr
    show inflateSyncPoint p h = _
    unfold inflateSyncPoint
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app, Z_STREAM_ERROR]
  · intro h r i z s hv
    rcases hv with ⟨hz, hstate, hi, hb, ha, hf, hlo, hhi⟩
    have hl : Live h r i z s := ⟨hz, hi, hstate, hb, ⟨hlo, hhi⟩, ha, hf⟩
    show inflateSyncPoint (some r) h = _
    unfold inflateSyncPoint
    by_cases hc : s.mode = STORED ∧ s.bits = 0
    · isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, hc.1, hc.2]
    · isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, hc]

/-- `int inflateUndermine(z_streamp strm, int subvert)` keeps strict distance checks. -/
theorem undermine_public : Goal.inflateUndermine := by
  intro subvert
  constructor
  · intro h p hr
    show inflateUndermine p subvert h = _
    unfold inflateUndermine
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app, Z_STREAM_ERROR]
  · intro h r i z s hv
    rcases hv with ⟨hz, hstate, hi, hb, ha, hf, hlo, hhi⟩
    have hl : Live h r i z s := ⟨hz, hi, hstate, hb, ⟨hlo, hhi⟩, ha, hf⟩
    show inflateUndermine (some r) subvert h = _
    unfold inflateUndermine
    isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, putInflate, setI]

/-- `int inflateValidate(z_streamp strm, int check)` changes both validation flags. -/
theorem validate_public : Goal.inflateValidate := by
  intro check
  constructor
  · intro h p hr
    show inflateValidate p check h = _
    unfold inflateValidate
    simp [bind_app, notInit_check (refused_dom hr) (refused_not_initialised hr), pure_app, Z_STREAM_ERROR]
  · intro h r i z s hv
    rcases hv with ⟨hz, hstate, hi, hb, ha, hf, hlo, hhi⟩
    have hl : Live h r i z s := ⟨hz, hi, hstate, hb, ⟨hlo, hhi⟩, ha, hf⟩
    show inflateValidate (some r) check h = _
    unfold inflateValidate
    isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, putInflate, setI]

#print axioms syncpoint_public
#print axioms undermine_public
#print axioms validate_public
end ZlibF.Spec.Public.InflateQueryProof
