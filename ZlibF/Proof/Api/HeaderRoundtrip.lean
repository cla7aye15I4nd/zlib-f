import ZlibF.Proof.Api.GzipRoundtrip

namespace ZlibF.Spec.Api.Proofs
open ZlibF.Spec ZlibF.Spec.Proofs

/-- Two legal parses of the same gzip header agree on every field the API exposes. -/
theorem header_fill_unique {flag : UInt8} {mt mt' : List UInt8} {xf xf' os os' : UInt8}
    {ex ex' nm nm' cm cm' : List UInt8} (req : HdrReq)
    (hm : mt.length = 4) (hm' : mt'.length = 4)
    (he : ex.length < 2 ^ 16) (he' : ex'.length < 2 ^ 16)
    (hn : (0 : UInt8) ∉ nm) (hn' : (0 : UInt8) ∉ nm')
    (_hc : (0 : UInt8) ∉ cm) (_hc' : (0 : UInt8) ∉ cm')
    (hh : Gzip.header flag mt xf os ex nm cm = Gzip.header flag mt' xf' os' ex' nm' cm') :
    fillHeader req flag.toNat (mt.foldr (fun b a => a * 256 + b.toNat) 0) xf.toNat os.toNat ex nm cm =
    fillHeader req flag.toNat (mt'.foldr (fun b a => a * 256 + b.toNat) 0) xf'.toNat os'.toNat ex' nm' cm' := by
  rw [header_eq, header_eq] at hh
  simp only [List.cons.injEq, true_and] at hh
  simp only [List.append_assoc] at hh
  have hmt := List.append_inj_left hh (by omega : mt.length = mt'.length)
  subst mt'
  have htail := List.append_cancel_left hh
  simp only [List.cons_append, List.cons.injEq] at htail
  obtain ⟨rfl, rfl, hbody⟩ := htail
  have hextra : flag.toNat / 4 % 2 = 1 → ex = ex' := by
    intro hbit
    simp only [hbit, ↓reduceIte] at hbody
    have hpart := PU_extra (le16 ex.length ++ ex) (le16 ex'.length ++ ex') _ _
      ⟨ex, he, rfl⟩ ⟨ex', he', rfl⟩ (by simpa [List.append_assoc] using hbody)
    have htail := congrArg (List.drop 2) hpart
    simpa [le16] using htail
  have hname : flag.toNat / 8 % 2 = 1 → nm = nm' := by
    intro hbit
    by_cases hbitex : flag.toNat / 4 % 2 = 1
    · have ee := hextra hbitex
      subst ex'
      simp only [hbitex, ↓reduceIte, List.append_assoc, List.append_right_inj] at hbody
      simp only [hbit, ↓reduceIte] at hbody
      have hpart := PU_term (nm ++ [0]) (nm' ++ [0]) _ _ ⟨nm, hn, rfl⟩ ⟨nm', hn', rfl⟩
        (by simpa [List.append_assoc] using hbody)
      exact List.append_cancel_right hpart
    · simp only [hbitex, ↓reduceIte, List.nil_append, hbit] at hbody
      have hpart := PU_term (nm ++ [0]) (nm' ++ [0]) _ _ ⟨nm, hn, rfl⟩ ⟨nm', hn', rfl⟩
        (by simpa [List.append_assoc] using hbody)
      exact List.append_cancel_right hpart
  have hcomment : flag.toNat / 16 % 2 = 1 → cm = cm' := by
    intro hbit
    by_cases hbex : flag.toNat / 4 % 2 = 1
    · have ee := hextra hbex
      subst ex'
      simp only [hbex, ↓reduceIte, List.append_assoc, List.append_right_inj] at hbody
      by_cases hbnm : flag.toNat / 8 % 2 = 1
      · have en := hname hbnm
        subst nm'
        simp only [hbnm, ↓reduceIte, List.append_assoc, List.append_right_inj, hbit] at hbody
        exact List.append_cancel_right hbody
      · simp only [hbnm, ↓reduceIte, List.nil_append, hbit] at hbody
        exact List.append_cancel_right hbody
    · simp only [hbex, ↓reduceIte, List.nil_append] at hbody
      by_cases hbnm : flag.toNat / 8 % 2 = 1
      · have en := hname hbnm
        subst nm'
        simp only [hbnm, ↓reduceIte, List.append_assoc, List.append_right_inj, hbit] at hbody
        exact List.append_cancel_right hbody
      · simp only [hbnm, ↓reduceIte, List.nil_append, hbit] at hbody
        exact List.append_cancel_right hbody
  unfold fillHeader
  by_cases hbex : flag.toNat / 4 % 2 = 1 <;>
    by_cases hbnm : flag.toNat / 8 % 2 = 1 <;>
    by_cases hbcm : flag.toNat / 16 % 2 = 1 <;>
    simp_all

private theorem flag_values (h : GzHead) : h.flg.toUInt8.toNat = h.flg ∧
    (h.flg.toUInt8.toNat / 2 % 2 = 1 ↔ h.hcrc = true) := by
  cases h with
  | mk text time os extra name comment hcrc =>
    cases text <;> cases hcrc <;> cases extra <;> cases name <;> cases comment <;> simp [GzHead.flg]

private theorem mtime_value (t : Nat) :
    (le32 t).foldr (fun b a => a * 256 + b.toNat) 0 = t % 2 ^ 32 := by
  simp [le32, Nat.toUInt8, UInt8.toNat_ofNat']
  omega

private theorem xfl_value (p : DeflParams) : (xflOf p).toUInt8.toNat = xflOf p := by
  unfold xflOf
  split <;> (try rfl)
  split <;> rfl

/-- The model header reader recovers the fields of the valid header written by deflate. -/
theorem header_roundtrip : Goal.header_roundtrip := by
  intro p h x sd req g hc hw hvalid ht hd hp hhead hread
  have hparam : sd.params = p := by simpa [DeflState.fresh] using deflate_trace_params ht
  have hheader : sd.header = h := by simp [DeflState.header, hhead]
  have hv := deflate_valid p x sd hc ht hd hp
  have hwritten : Gzip.DecodesWith (h.bytes p) sd.produced sd.input := by
    simpa [DeflState.Valid, hparam, hw, hheader] using hv
  have hformat := gzip_decode_with_header hvalid hwritten
  obtain ⟨tail, hstream, _⟩ := hwritten
  rcases hread with hread | hread
  · obtain ⟨flag, mt, xf, os, ex, nm, cm, rest, hflag, hmt, hex, hnm, hcm, hparse, rfl⟩ := hread
    have hcore : sd.produced = Gzip.header h.flg.toUInt8 (le32 h.time) (xflOf p).toUInt8 h.os.toUInt8
          (h.extra.getD []) (h.name.getD []) (h.comment.getD []) ++
        (if h.hcrc then le16 ((crc32 (h.core p)).toNat % 2 ^ 16) else []) ++ tail := by
      simpa [GzHead.bytes, GzHead.core] using hstream
    have he : h.flg.toUInt8 = flag := by
      rw [hcore, header_eq, header_eq] at hparse
      simp only [List.cons_append, List.cons.injEq] at hparse
      exact hparse.2.2.2.1
    subst flag
    have hvalidextra : (h.extra.getD []).length < 2 ^ 16 := by
      cases he : h.extra with
      | none => simp
      | some e => simpa [he] using hvalid.1 e he
    have hvalidname : (0 : UInt8) ∉ h.name.getD [] := by
      cases hn : h.name with
      | none => simp
      | some name => simpa [hn] using hvalid.2.1 name hn
    have hvalidcomment : (0 : UInt8) ∉ h.comment.getD [] := by
      cases hc : h.comment with
      | none => simp
      | some comment => simpa [hc] using hvalid.2.2 comment hc
    have hmem1 := header_mem h.flg.toUInt8 (le32 h.time) (xflOf p).toUInt8 h.os.toUInt8
      (h.extra.getD []) (h.name.getD []) (h.comment.getD []) (le32_length _) hvalidextra hvalidname hvalidcomment
    have hmem2 := header_mem h.flg.toUInt8 mt xf os ex nm cm hmt hex hnm hcm
    have heq := hcore.symm.trans hparse
    have hheaders := PU_HdrSet h.flg.toUInt8 _ _ _ _ hmem1 hmem2 (by simpa [List.append_assoc] using heq)
    have hfill := header_fill_unique req (le32_length _) hmt hvalidextra hex hvalidname hnm
      hvalidcomment hcm hheaders
    have hvalues := flag_values h
    have hx : xflOf p % 256 = xflOf p := by
      simpa [Nat.toUInt8, UInt8.toNat_ofNat'] using xfl_value p
    simpa [expectedHdr, hvalues.1, mtime_value, Nat.toUInt8, UInt8.toNat_ofNat', hx] using hfill.symm
  · obtain ⟨cmf, flag, r, hs, hh, _⟩ := hread
    obtain ⟨rest, hprefix⟩ := ZlibF.Spec.gzip_head hformat
    rw [hs] at hprefix
    simp only [List.cons.injEq] at hprefix
    have he : cmf = 31 := hprefix.1
    rw [he] at hh
    exact False.elim ((by decide : ¬ ((31 : UInt8).toNat % 16 = 8)) hh.1)

#print axioms header_roundtrip
#print axioms header_fill_unique
end ZlibF.Spec.Api.Proofs
