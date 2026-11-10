import ZlibF.Proof.«inflate.c.header-default»
namespace Zlib.Inflate.Proofs.HeaderSource
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Exhaustive arithmetic classification of RFC1950 valid headers without
FDICT. Every input byte pair remains covered; this is not a chosen witness. -/
theorem header_words {cmf flg : UInt8} (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0) :
    cmf.toNat + 256 * flg.toNat ∈ [7432, 23304, 39176, 55048, 6424, 22296, 38168, 54040, 5416, 21288, 37160, 53032, 4408, 20280, 36152, 52024, 3400, 19272, 35144, 51016, 2392, 18264, 34136, 50008, 1384, 17256, 33128, 56936, 376, 24184, 40056, 55928] := by
  obtain ⟨method, window, checksum⟩ := valid
  have cmfBound := cmf.toNat_lt
  have flgBound := flg.toNat_lt
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have cases : cmf.toNat = 8 ∨ cmf.toNat = 24 ∨ cmf.toNat = 40 ∨ cmf.toNat = 56 ∨ cmf.toNat = 72 ∨ cmf.toNat = 88 ∨ cmf.toNat = 104 ∨ cmf.toNat = 120 := by omega
  have flgBlock : flg.toNat / 32 = 0 ∨ flg.toNat / 32 = 2 ∨ flg.toNat / 32 = 4 ∨ flg.toNat / 32 = 6 := by omega
  rcases cases with c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7
  · rw [c0] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega
  · rw [c1] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega
  · rw [c2] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega
  · rw [c3] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega
  · rw [c4] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega
  · rw [c5] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega
  · rw [c6] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega
  · rw [c7] at checksum ⊢
    rcases flgBlock with f0 | f2 | f4 | f6 <;> omega


/-- The actual HEAD tests accept every valid no-dictionary header word
under the initialized zlib wrapper; window and TYPE selection are derived. -/
theorem valid_plain_guards {cmf flg : UInt8} {s : InflateState} {l : IL}
    (valid : Zlib.HeaderOK cmf flg) (plain : flg.toNat / 32 % 2 = 0)
    (wrap : s.wrap = 5) (word : l.hold.toNat = cmf.toNat + 256 * flg.toNat) :
    headHeaderRejected s l = false ∧ headMethodRejected l = false ∧
    (headWindowRegs l).len.toNat ≤ 15 ∧ headDefaultMode l = TYPE := by
  have choices := header_words valid plain
  simp only [List.mem_cons, List.not_mem_nil, or_false] at choices
  rw [← word] at choices
  rcases choices with case0 | case1 | case2 | case3 | case4 | case5 | case6 | case7 | case8 | case9 | case10 | case11 | case12 | case13 | case14 | case15 | case16 | case17 | case18 | case19 | case20 | case21 | case22 | case23 | case24 | case25 | case26 | case27 | case28 | case29 | case30 | case31
  · have held : l.hold = (7432 : UInt64) := UInt64.toNat_inj.mp case0
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (23304 : UInt64) := UInt64.toNat_inj.mp case1
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (39176 : UInt64) := UInt64.toNat_inj.mp case2
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (55048 : UInt64) := UInt64.toNat_inj.mp case3
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (6424 : UInt64) := UInt64.toNat_inj.mp case4
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (22296 : UInt64) := UInt64.toNat_inj.mp case5
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (38168 : UInt64) := UInt64.toNat_inj.mp case6
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (54040 : UInt64) := UInt64.toNat_inj.mp case7
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (5416 : UInt64) := UInt64.toNat_inj.mp case8
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (21288 : UInt64) := UInt64.toNat_inj.mp case9
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (37160 : UInt64) := UInt64.toNat_inj.mp case10
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (53032 : UInt64) := UInt64.toNat_inj.mp case11
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (4408 : UInt64) := UInt64.toNat_inj.mp case12
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (20280 : UInt64) := UInt64.toNat_inj.mp case13
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (36152 : UInt64) := UInt64.toNat_inj.mp case14
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (52024 : UInt64) := UInt64.toNat_inj.mp case15
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (3400 : UInt64) := UInt64.toNat_inj.mp case16
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (19272 : UInt64) := UInt64.toNat_inj.mp case17
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (35144 : UInt64) := UInt64.toNat_inj.mp case18
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (51016 : UInt64) := UInt64.toNat_inj.mp case19
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (2392 : UInt64) := UInt64.toNat_inj.mp case20
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (18264 : UInt64) := UInt64.toNat_inj.mp case21
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (34136 : UInt64) := UInt64.toNat_inj.mp case22
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (50008 : UInt64) := UInt64.toNat_inj.mp case23
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (1384 : UInt64) := UInt64.toNat_inj.mp case24
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (17256 : UInt64) := UInt64.toNat_inj.mp case25
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (33128 : UInt64) := UInt64.toNat_inj.mp case26
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (56936 : UInt64) := UInt64.toNat_inj.mp case27
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (376 : UInt64) := UInt64.toNat_inj.mp case28
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (24184 : UInt64) := UInt64.toNat_inj.mp case29
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (40056 : UInt64) := UInt64.toNat_inj.mp case30
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide
  · have held : l.hold = (55928 : UInt64) := UInt64.toNat_inj.mp case31
    simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
    decide

#print axioms header_words
#print axioms valid_plain_guards
end Zlib.Inflate.Proofs.HeaderSource
