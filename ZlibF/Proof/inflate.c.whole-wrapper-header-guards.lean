import ZlibF.Proof.«inflate.c.whole-wrapper-byte-source»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- All RFC1950 header bytes, including FDICT, drive the actual HEAD guards. -/
theorem valid_header_guards {cmf flg : UInt8} {s : InflateState} {l : IL}
    (valid : Zlib.HeaderOK cmf flg) (wrap : s.wrap = 5)
    (word : l.hold.toNat = cmf.toNat + 256 * flg.toNat) :
    headHeaderRejected s l = false ∧ headMethodRejected l = false ∧
      (headWindowRegs l).len.toNat ≤ 15 ∧
      headDefaultMode l = (if flg.toNat / 32 % 2 = 1 then DICTID else TYPE) := by
  obtain ⟨method, window, checksum⟩ := valid
  have cmfBound := cmf.toNat_lt
  have flgBound := flg.toNat_lt
  have cmfCases : cmf.toNat = 8 ∨ cmf.toNat = 24 ∨ cmf.toNat = 40 ∨ cmf.toNat = 56 ∨ cmf.toNat = 72 ∨ cmf.toNat = 88 ∨ cmf.toNat = 104 ∨ cmf.toNat = 120 := by omega
  rcases cmfCases with c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7
  · have flgCases : flg.toNat = 29 ∨ flg.toNat = 60 ∨ flg.toNat = 91 ∨ flg.toNat = 122 ∨ flg.toNat = 153 ∨ flg.toNat = 184 ∨ flg.toNat = 215 ∨ flg.toNat = 246 := by
      rw [c0] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7
    · have held : l.hold = (7432 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 7432; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (15368 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 15368; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (23304 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 23304; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (31240 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 31240; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (39176 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 39176; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (47112 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 47112; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (55048 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 55048; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (62984 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 62984; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
  · have flgCases : flg.toNat = 25 ∨ flg.toNat = 56 ∨ flg.toNat = 87 ∨ flg.toNat = 118 ∨ flg.toNat = 149 ∨ flg.toNat = 180 ∨ flg.toNat = 211 ∨ flg.toNat = 242 := by
      rw [c1] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7
    · have held : l.hold = (6424 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 6424; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (14360 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 14360; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (22296 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 22296; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (30232 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 30232; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (38168 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 38168; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (46104 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 46104; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (54040 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 54040; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (61976 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 61976; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
  · have flgCases : flg.toNat = 21 ∨ flg.toNat = 52 ∨ flg.toNat = 83 ∨ flg.toNat = 114 ∨ flg.toNat = 145 ∨ flg.toNat = 176 ∨ flg.toNat = 207 ∨ flg.toNat = 238 := by
      rw [c2] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7
    · have held : l.hold = (5416 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 5416; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (13352 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 13352; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (21288 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 21288; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (29224 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 29224; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (37160 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 37160; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (45096 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 45096; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (53032 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 53032; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (60968 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 60968; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
  · have flgCases : flg.toNat = 17 ∨ flg.toNat = 48 ∨ flg.toNat = 79 ∨ flg.toNat = 110 ∨ flg.toNat = 141 ∨ flg.toNat = 172 ∨ flg.toNat = 203 ∨ flg.toNat = 234 := by
      rw [c3] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7
    · have held : l.hold = (4408 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 4408; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (12344 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 12344; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (20280 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 20280; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (28216 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 28216; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (36152 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 36152; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (44088 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 44088; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (52024 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 52024; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (59960 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 59960; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
  · have flgCases : flg.toNat = 13 ∨ flg.toNat = 44 ∨ flg.toNat = 75 ∨ flg.toNat = 106 ∨ flg.toNat = 137 ∨ flg.toNat = 168 ∨ flg.toNat = 199 ∨ flg.toNat = 230 := by
      rw [c4] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7
    · have held : l.hold = (3400 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 3400; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (11336 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 11336; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (19272 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 19272; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (27208 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 27208; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (35144 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 35144; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (43080 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 43080; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (51016 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 51016; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (58952 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 58952; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
  · have flgCases : flg.toNat = 9 ∨ flg.toNat = 40 ∨ flg.toNat = 71 ∨ flg.toNat = 102 ∨ flg.toNat = 133 ∨ flg.toNat = 164 ∨ flg.toNat = 195 ∨ flg.toNat = 226 := by
      rw [c5] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7
    · have held : l.hold = (2392 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 2392; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (10328 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 10328; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (18264 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 18264; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (26200 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 26200; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (34136 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 34136; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (42072 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 42072; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (50008 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 50008; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (57944 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 57944; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
  · have flgCases : flg.toNat = 5 ∨ flg.toNat = 36 ∨ flg.toNat = 67 ∨ flg.toNat = 98 ∨ flg.toNat = 129 ∨ flg.toNat = 160 ∨ flg.toNat = 191 ∨ flg.toNat = 222 ∨ flg.toNat = 253 := by
      rw [c6] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8
    · have held : l.hold = (1384 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 1384; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (9320 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 9320; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (17256 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 17256; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (25192 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 25192; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (33128 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 33128; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (41064 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 41064; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (49000 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 49000; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (56936 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 56936; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (64872 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 64872; omega)
      rw [f8]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
  · have flgCases : flg.toNat = 1 ∨ flg.toNat = 32 ∨ flg.toNat = 63 ∨ flg.toNat = 94 ∨ flg.toNat = 125 ∨ flg.toNat = 156 ∨ flg.toNat = 187 ∨ flg.toNat = 218 ∨ flg.toNat = 249 := by
      rw [c7] at checksum
      omega
    rcases flgCases with f0 | f1 | f2 | f3 | f4 | f5 | f6 | f7 | f8
    · have held : l.hold = (376 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 376; omega)
      rw [f0]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (8312 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 8312; omega)
      rw [f1]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (16248 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 16248; omega)
      rw [f2]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (24184 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 24184; omega)
      rw [f3]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (32120 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 32120; omega)
      rw [f4]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (40056 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 40056; omega)
      rw [f5]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (47992 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 47992; omega)
      rw [f6]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (55928 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 55928; omega)
      rw [f7]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide
    · have held : l.hold = (63864 : UInt64) := UInt64.toNat_inj.mp (by change l.hold.toNat = 63864; omega)
      rw [f8]
      simp only [headHeaderRejected, wrap, headMethodRejected, headWindowRegs, headDefaultMode, held]
      decide

#print axioms valid_header_guards
end Zlib.Inflate.Proofs.WholeWrapper
