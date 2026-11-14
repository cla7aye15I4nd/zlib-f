import ZlibF.Proof.«public-inflate-init2»
import ZlibF.Proof.«public-deflate-init2»
import ZlibF.Spec.Safety.Initialisation

/-!
# Safety of the inflate and deflate init functions

Each goal of `ZlibF/Spec/Safety/Initialisation.lean` follows from the full contract of the same
function (`Goal.inflateInit2_`, `Goal.deflateInit2_`), restricted to `InitDomain`. The failure
branches of the contracts give `SameObjects` (or `SameObjectsUpToTableShape`) with the heap whose
stream record was rewritten; `frame_of_same` turns that into the frame of the record and an
unchanged set of live blocks. `inflateInit_` and `deflateInit_` are `inflateInit2_` and
`deflateInit2_` with fixed arguments in the translation.
-/

namespace ZlibF.Spec.Public.InitSafetyProof
open C ZlibF.Spec ZlibF.Spec.Public

theorem upToShape_of_same {e a : Heap} (s : SameObjects e a) : SameObjectsUpToTableShape e a := by
  obtain ⟨hb, hw, hro, hs, hg, hd, hi, hgz, hst, hal, hga, hn, hna⟩ := s
  exact ⟨fun b => by rw [hb], fun b => by rw [hw], hro, fun b => by rw [hs], fun b => by rw [hg],
    fun b => by rw [hd], fun b => by rw [hi], fun b => by rw [hgz], hst, hal, hga, hn, hna⟩

/-- Rewriting a live stream record changes nothing but that record, and keeps every block live. -/
theorem frame_of_same {h after : Heap} {r : ZStreamRef} {z v : ZStream} (hz : r.get h = some z)
    (s : SameObjectsUpToTableShape (r.put h v) after) :
    Frame h after (StreamRoot r) ∧ LiveChange h after (fun _ => False) (fun _ => False) := by
  obtain ⟨hb, hw, hro, hs, hg, hd, hi, hgz, hst, hal, hga, hn, hna⟩ := s
  cases r with
  | tab i =>
    have hzi : h.streams i = some z := hz
    have hput : ZStreamRef.put h (.tab i) v = { h with streams := upd h.streams i (some v) } := by
      simp [ZStreamRef.put, hzi]
    rw [hput] at hb hw hro hs hg hd hi hgz hst hal hga hn hna
    have hlive : ∀ b, after.live b ↔ h.live b := by
      intro b
      by_cases hbi : b = i
      · subst hbi
        simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_same, hzi]
        simp
      · simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_ne _ _ _ _ hbi]
    refine ⟨⟨hst.symm, hal.symm, hga.symm, hn, hna, ?_⟩, fun b => by simp [hlive b]⟩
    intro b hl hnot
    have hbi : b ≠ i := hnot
    refine ⟨hb b, hw b, ?_, hg b, hd b, hi b, hgz b, ?_⟩
    · rw [hs b]; exact upd_ne _ _ _ _ hbi
    · exact hro b (by simpa [Heap.live, upd_ne _ _ _ _ hbi] using hl)
  | in_gzstate_strm i =>
    obtain ⟨g, hgi, -⟩ : ∃ g, h.gzstates i = some g ∧ g.strm = z := by
      simp only [ZStreamRef.get, Option.map_eq_some_iff] at hz; exact hz
    have hput : ZStreamRef.put h (.in_gzstate_strm i) v =
        { h with gzstates := upd h.gzstates i (some { g with strm := v }) } := by
      simp [ZStreamRef.put, hgi]
    rw [hput] at hb hw hro hs hg hd hi hgz hst hal hga hn hna
    have hlive : ∀ b, after.live b ↔ h.live b := by
      intro b
      by_cases hbi : b = i
      · subst hbi
        simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_same, hgi]
        simp
      · simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_ne _ _ _ _ hbi]
    refine ⟨⟨hst.symm, hal.symm, hga.symm, hn, hna, ?_⟩, fun b => by simp [hlive b]⟩
    intro b hl hnot
    have hbi : b ≠ i := hnot
    refine ⟨hb b, hw b, hs b, hg b, hd b, hi b, ?_, ?_⟩
    · rw [hgz b]; exact upd_ne _ _ _ _ hbi
    · exact hro b (by simpa [Heap.live, upd_ne _ _ _ _ hbi] using hl)

theorem inflateInit2__safety : Goal.inflateInit2__safety := by
  intro h r version wb ⟨hf, hu, hg, hv, z, hz, hd, _⟩
  obtain ⟨rc, after, hrun, -, hbr⟩ :=
    (ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public wb).2.2 h r z version hf hu hg hz hd hv
  refine ⟨rc, after, hrun, ?_⟩
  by_cases ha : h.allocOk h.nalloc = false
  · rw [if_pos ha] at hbr
    obtain ⟨hrc, hsame⟩ := hbr
    obtain ⟨hfr, hl⟩ := frame_of_same hz (upToShape_of_same hsame)
    exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
  · rw [if_neg ha] at hbr
    cases hw : Api.inflWbits wb.toInt with
    | none =>
      rw [hw] at hbr
      obtain ⟨hrc, hsame⟩ := hbr
      obtain ⟨hfr, hl⟩ := frame_of_same hz hsame
      exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
    | some p =>
      obtain ⟨wrap, bits⟩ := p
      rw [hw] at hbr
      obtain ⟨hrc, z', s', hgood, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr, hl⟩ := hbr
      subst hrc
      refine ⟨hfr, Or.inl ⟨rfl, StreamReachable.inflateInit hf hu hg hz hd hv hrun,
        fun b => b = h.nextBlk, ?_, hl⟩⟩
      intro b hb
      subst hb
      exact ⟨z', hgood.live.hz, Or.inl ⟨h.nextBlk, s', hgood.live.zst, hgood.live.hs, Or.inl rfl⟩⟩

theorem inflateInit__safety : Goal.inflateInit__safety :=
  fun h r version d => inflateInit2__safety h r version DEF_WBITS d

theorem deflateInit2__safety : Goal.deflateInit2__safety := by
  intro h r version level method wb mem strategy ⟨hf, hu, hg, hv, z, hz, hd, _⟩
  obtain ⟨rc, after, hrun, hbr⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof level method wb mem strategy).2.2
      h r z version hf hu hg hz hd hv
  refine ⟨rc, after, hrun, ?_⟩
  cases hp : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
  | none =>
    rw [hp] at hbr
    obtain ⟨hrc, hsame, -⟩ := hbr
    obtain ⟨hfr, hl⟩ := frame_of_same hz (upToShape_of_same hsame)
    exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
  | some p =>
    rw [hp] at hbr
    dsimp only at hbr
    by_cases ha : h.allocOk h.nalloc = false
    · rw [if_pos ha] at hbr
      obtain ⟨hrc, -, hsame⟩ := hbr
      obtain ⟨hfr, hl⟩ := frame_of_same hz (upToShape_of_same hsame)
      exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
    · rw [if_neg ha] at hbr
      obtain ⟨-, hbr⟩ := hbr
      by_cases hall : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
      · rw [if_pos hall] at hbr
        obtain ⟨hrc, z', s', hgood, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr, hl, -⟩ := hbr
        subst hrc
        refine ⟨hfr, Or.inl ⟨rfl, StreamReachable.deflateInit hf hu hg hz hd hv hrun,
          DeflateOwned h.nextBlk s', ?_, hl⟩⟩
        intro b hb
        exact ⟨z', hgood.live.hz, Or.inr ⟨h.nextBlk, s', hgood.live.zst, hgood.live.hs, hb⟩⟩
      · rw [if_neg hall] at hbr
        obtain ⟨hrc, -, hl, hfr⟩ := hbr
        exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩

theorem deflateInit__safety : Goal.deflateInit__safety :=
  fun h r version level d =>
    deflateInit2__safety h r version level Z_DEFLATED MAX_WBITS
      DEF_MEM_LEVEL Z_DEFAULT_STRATEGY d

end ZlibF.Spec.Public.InitSafetyProof
