import ZlibF.Proof.«gzlib.c.base»

/-!
# gzfs: the OS-call oracle never touches the heap, and its regular instance

Each of `fsRead`, `fsWrite`, `fsLseek`, `fsClose`, `fsOpen` is `pure` of a result that depends on the world only,
for every oracle value: it never faults and never changes the heap. When the oracle entry of the call is
`regular` (and, for `close`/`open`, no failure or move is chosen, and no errno is chosen after success), the call
is its regular-file version on the world with the counter advanced.
-/

namespace Zlib.GzFs.Proofs
open C Zlib.GzFs

/-! ## The regular-file versions are pure -/

theorem fsReadReg_pure (fd : Int32) (n : UInt64) (w : Fs) :
    ∃ x, fsReadReg fd n w = (pure x : M ((Int64 × Array UInt8) × Fs)) := by
  unfold fsReadReg
  repeat' first
    | exact ⟨_, rfl⟩
    | split
    | dsimp only

theorem fsWriteReg_pure (fd : Int32) (bs : Array UInt8) (w : Fs) :
    ∃ x, fsWriteReg fd bs w = (pure x : M (Int64 × Fs)) := by
  unfold fsWriteReg
  repeat' first
    | exact ⟨_, rfl⟩
    | split
    | dsimp only

theorem fsLseekReg_pure (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ∃ x, fsLseekReg fd off wh w = (pure x : M (Int64 × Fs)) ∧ (x.1 = -1 ∨ 0 ≤ x.1.toInt) := by
  unfold fsLseekReg
  repeat' first
    | exact ⟨_, rfl, Or.inl rfl⟩
    | (refine ⟨_, rfl, Or.inr ?_⟩
       simp only []
       rw [Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)]
       omega)
    | split
    | dsimp only

theorem fsCloseReg_pure (fd : Int32) (w : Fs) :
    ∃ x, fsCloseReg fd w = (pure x : M (Int32 × Fs)) := by
  unfold fsCloseReg
  repeat' first
    | exact ⟨_, rfl⟩
    | split
    | dsimp only

theorem fsOpenReg_pure (path : Array UInt8) (flags : Int32) (w : Fs) :
    ∃ x, fsOpenReg path flags w = (pure x : M (Int32 × Fs)) := by
  unfold fsOpenReg
  repeat' first
    | exact ⟨_, rfl⟩
    | split
    | dsimp only

/-! ## The oracle versions are pure, for every oracle value -/

theorem fsRead_pure (fd : Int32) (n : UInt64) (w : Fs) :
    ∃ x, fsRead fd n w = (pure x : M ((Int64 × Array UInt8) × Fs)) := by
  unfold fsRead
  dsimp only
  split
  · obtain ⟨⟨⟨r, bs⟩, w'⟩, hy⟩ := fsReadReg_pure fd (UInt64.ofNat (readCap fd n w)) (tickW w)
    rw [hy]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem fsWrite_pure (fd : Int32) (bs : Array UInt8) (w : Fs) :
    ∃ x, fsWrite fd bs w = (pure x : M (Int64 × Fs)) := by
  unfold fsWrite
  dsimp only
  split
  · obtain ⟨⟨r, w'⟩, hy⟩ := fsWriteReg_pure fd bs (tickW w)
    rw [hy]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem fsLseek_pure (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ∃ x, fsLseek fd off wh w = (pure x : M (Int64 × Fs)) ∧ (x.1 = -1 ∨ 0 ≤ x.1.toInt) := by
  unfold fsLseek
  dsimp only
  split
  · obtain ⟨⟨r, w'⟩, hy, hp⟩ := fsLseekReg_pure fd off wh (tickW w)
    rw [hy]
    exact ⟨_, rfl, hp⟩
  · exact ⟨_, rfl, Or.inl rfl⟩
  · refine ⟨_, rfl, Or.inr ?_⟩
    simp only []
    rw [Zlib.Gzlib.Proofs.i64_toInt_ofInt (by omega) (by omega)]
    omega

theorem fsClose_pure (fd : Int32) (w : Fs) :
    ∃ x, fsClose fd w = (pure x : M (Int32 × Fs)) := by
  unfold fsClose
  dsimp only
  obtain ⟨⟨r, w'⟩, hy⟩ := fsCloseReg_pure fd (tickW w)
  rw [hy]
  exact ⟨_, rfl⟩

theorem fsOpen_pure (path : Array UInt8) (flags : Int32) (w : Fs) :
    ∃ x, fsOpen path flags w = (pure x : M (Int32 × Fs)) := by
  unfold fsOpen
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨⟨r, w'⟩, hy⟩ := fsOpenReg_pure path flags (tickW w)
    rw [hy]
    exact ⟨_, rfl⟩

/-! ## The regular instance -/

/-- With a regular oracle entry and no budget, `read` is the regular-file read on the advanced world (a success
may still be followed by an oracle errno, which `okErrW` applies). -/
theorem fsRead_regular (fd : Int32) (n : UInt64) (w : Fs) (hc : w.readChoice w.nos = .regular)
    (hb : readCap fd n w = n.toNat) :
    fsRead fd n w = (do
      let ((r, bs), w') ← fsReadReg fd n (tickW w)
      pure ((r, bs), if r = -1 then w' else okErrW (w.okErrno w.nos) (debitW fd bs.size w'))) := by
  unfold fsRead
  dsimp only
  rw [hc, hb, UInt64.ofNat_toNat]

/-- With a regular oracle entry, `write` is the regular-file write on the advanced world. -/
theorem fsWrite_regular (fd : Int32) (bs : Array UInt8) (w : Fs) (hc : w.writeChoice w.nos = .regular) :
    fsWrite fd bs w = (do
      let (r, w') ← fsWriteReg fd bs (tickW w)
      pure (r, if r = -1 then w' else okErrW (w.okErrno w.nos) w')) := by
  unfold fsWrite
  dsimp only
  rw [hc]

/-- With a regular oracle entry, `lseek` is the regular-file `lseek` on the advanced world. -/
theorem fsLseek_regular (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) (hc : w.lseekChoice w.nos = .regular) :
    fsLseek fd off wh w = (do
      let (r, w') ← fsLseekReg fd off wh (tickW w)
      pure (r, if r = -1 then w' else okErrW (w.okErrno w.nos) w')) := by
  unfold fsLseek
  dsimp only
  rw [hc]

/-- With no oracle failure, `close` is the regular-file `close` on the advanced world. -/
theorem fsClose_regular (fd : Int32) (w : Fs) (hc : w.closeFail w.nos = none) :
    fsClose fd w = (do
      let (r, w') ← fsCloseReg fd (tickW w)
      pure (r, if r = -1 then w' else okErrW (w.okErrno w.nos) w')) := by
  unfold fsClose
  dsimp only
  rw [hc]

/-- With no oracle failure and no move, `open` is the regular-file `open` on the advanced world. -/
theorem fsOpen_regular (path : Array UInt8) (flags : Int32) (w : Fs) (hc : w.openFail w.nos = none)
    (hm : w.openFd w.nos = none) :
    fsOpen path flags w = (do
      let (r, w') ← fsOpenReg path flags (tickW w)
      pure (if r = -1 then (r, w') else (r, okErrW (w.okErrno w.nos) w'))) := by
  unfold fsOpen
  dsimp only
  rw [hc, hm]

end Zlib.GzFs.Proofs
