import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«inflate.c.base»

namespace ZlibF.Spec.Public.InflateHeaderProof
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

theorem inflateGetHeader_nogzip {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (head : GzHeaderPtr) (hw : st.wrap &&& 2 = 0) :
    C.run (inflateGetHeader (some r) head) h = .ok (Z_STREAM_ERROR, h) := by
  show inflateGetHeader (some r) head h = _
  unfold inflateGetHeader
  isimp [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw]

/-- The state record after a successful `inflateGetHeader`: only `head` changes. -/
def getHeaderState (head : GzHeaderPtr) (st : InflateState) : InflateState := { st with head := head }


theorem inflateGetHeader_record {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hl : Live h r zs z st) {g : GzHeaderRef} {gh : GzHeader}
    (hg : g.get h = some gh) (hw : st.wrap &&& 2 ≠ 0) :
    C.run (inflateGetHeader (some r) (some g)) h =
      .ok (Z_OK, g.put (setI h zs (getHeaderState (some g) st)) { gh with done := 0 }) := by
  have hg1 : g.get (setI h zs (getHeaderState (some g) st)) = some gh := by
    cases g with | tab i => simp [GzHeaderRef.get, setI] at hg ⊢; exact hg
  show inflateGetHeader (some r) (some g) h = _
  unfold inflateGetHeader
  have hro : g.isRo = false := by cases g; rfl
  have hg' : GzHeaderRef.get (setI h zs { st with head := some g }) g = some gh := hg1
  isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, hw, getHeaderState, ldGzHeader_ok hg', stGzHeader_ok hg' hro]


theorem getheader_public : Goal.inflateGetHeader := by
  intro h r i z s head hv hheader
  rcases hv with ⟨hz,hstate,hi,hback,ha,hf,hlo,hhi⟩
  have hl : Live h r i z s := ⟨hz,hi,hstate,hback,⟨hlo,hhi⟩,ha,hf⟩
  by_cases hw : s.wrap &&& 2 = 0
  · exact ⟨Z_STREAM_ERROR, h, inflateGetHeader_nogzip hl head hw, by simp [hw]⟩
  · obtain ⟨g, gh, hptr, hgh⟩ := hheader hw
    subst head
    refine ⟨Z_OK, (GzHeaderRef.tab g).put (setI h i (getHeaderState (some (.tab g)) s)) { gh with done := 0 }, ?_, ?_⟩
    · simpa [GzHeaderRef.get, GzHeaderRef.put, getHeaderState, setI, putInflate] using
        inflateGetHeader_record hl (g := .tab g) (gh := gh) hgh hw
    · simp [hw, hgh, GzHeaderRef.put, getHeaderState, setI, putInflate]


#print axioms getheader_public
end ZlibF.Spec.Public.InflateHeaderProof
