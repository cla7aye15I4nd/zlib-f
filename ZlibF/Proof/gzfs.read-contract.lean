import ZlibF.Proof.«gzfs.oracle»
import ZlibF.Proof.«gz.inv-model»

/-!
# gzfs: the contract of `read` (M1) for every oracle value

`fsRead fd n` returns `-1` with no bytes, or `k ≤ n` bytes with result `k`. It changes no heap, keeps the
well-formedness of the file system (`FileSystem`) and opens or closes no descriptor (`FdsKept`). This holds for
every entry of the read oracle (`regular`, `fail`, `bytes`) and every budget.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs
set_option autoImplicit false

theorem fds_set_get (a : Array (Option OFile)) (j i : Nat) (v : Option OFile) :
    (a.set! j v)[i]? = if j = i then (if j < a.size then some v else none) else a[i]? := by
  simp [Array.set!, Array.getElem?_setIfInBounds]

/-- A world that differs only in `errno` keeps `FileSystem` and the open descriptors. -/
theorem errno_world (w : Fs) (e : Int32) (hfs : FileSystem w) :
    FileSystem { w with errno := e } ∧ FdsKept w { w with errno := e } :=
  ⟨hfs, fun _ => Iff.rfl⟩

/-- **M1 for the regular-file read**: `-1` and no bytes, or `k ≤ m` bytes with result `k`; only the descriptor's
position and `errno` change, the file system stays well formed and no descriptor opens or closes. -/
theorem fsReadReg_contract (fd : Int32) (m : UInt64) (w : Fs) (hfs : FileSystem w) (hm : m.toNat < 2 ^ 63) :
    ∃ r bs w', fsReadReg fd m w = (pure ((r, bs), w') : M ((Int64 × Array UInt8) × Fs)) ∧
      ((r = -1 ∧ bs.size = 0) ∨ (r.toInt = bs.size ∧ bs.size ≤ m.toNat)) ∧ FileSystem w' ∧ FdsKept w w' ∧
      w'.nos = w.nos ∧ w'.readBudget = w.readBudget ∧ w'.okErrno = w.okErrno := by
  obtain ⟨hlim, hnames, hfds, hnodes⟩ := hfs
  unfold fsReadReg
  dsimp only
  split
  · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl⟩, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl, rfl, rfl, rfl⟩
  · rename_i hbad
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbad
    obtain ⟨hpos, hlt⟩ := hbad
    have hj : fd.toInt.toNat < w.fds.size := by
      have : ¬ fd.toInt < 0 := fun x => hpos (Int32.lt_iff_toInt_lt.mpr (by simpa using x))
      omega
    split
    · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl⟩, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl, rfl, rfl, rfl⟩
    · rename_i of hof
      have hget : w.fds[fd.toInt.toNat]? = some (some of) := by
        rw [getElem!_pos w.fds _ hj] at hof
        rw [Array.getElem?_eq_getElem hj, hof]
      split
      · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl⟩, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl, rfl, rfl, rfl⟩
      · try dsimp only
        split
        · exact ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl⟩, ⟨hlim, hnames, hfds, hnodes⟩, fun _ => Iff.rfl, rfl, rfl, rfl⟩
        · rename_i hdir
          obtain ⟨hnode, hopos, hwr⟩ := hfds _ _ hget
          have hnd : w.nodes[of.node]? = some w.nodes[of.node]! := by
            rw [getElem!_pos w.nodes _ hnode]; simp [hnode]
          have hsz := hnodes _ _ hnd
          generalize hk : min m.toNat ((w.nodes[of.node]!).data.size - of.pos) = k
          have hkm : k ≤ m.toNat := by omega
          have hkn : k + of.pos ≤ (w.nodes[of.node]!).data.size ∨ k = 0 := by omega
          have hext : ((w.nodes[of.node]!).data.extract of.pos (of.pos + k)).size = k := by
            simp only [Array.size_extract]; omega
          refine ⟨_, _, _, rfl, Or.inr ⟨?_, ?_⟩, ⟨hlim, hnames, ?_, hnodes⟩, ?_, rfl, rfl, rfl⟩
          · rw [hext, Int64.toInt_ofNat', Zlib.Gzlib.Proofs.bmod64 _ (by omega) (by omega)]
          · rw [hext]; exact hkm
          · intro i file hi
            rw [fds_set_get] at hi
            split at hi
            · rename_i e
              subst e
              simp only [hj, ite_true, Option.some.injEq] at hi
              subst hi
              refine ⟨hnode, ?_, fun node hn hd => hwr node hn hd⟩
              show of.pos + k ≤ 2 ^ 63 - 1
              omega
            · exact hfds i file hi
          · intro i
            unfold GzOracle.FdOpen
            rw [fds_set_get]
            split
            · rename_i e
              subst e
              exact ⟨fun _ => ⟨of, hget⟩, fun _ => ⟨_, rfl⟩⟩
            · exact Iff.rfl

theorem readCap_le (fd : Int32) (n : UInt64) (w : Fs) : readCap fd n w ≤ n.toNat := by
  unfold readCap
  split
  · exact Nat.le_refl _
  · split <;> omega

theorem fs_debit (fd : Int32) (k : Nat) (w : Fs) (hfs : FileSystem w) :
    FileSystem (debitW fd k w) ∧ FdsKept w (debitW fd k w) := by
  unfold debitW
  split
  · exact ⟨hfs, fun _ => Iff.rfl⟩
  · exact ⟨hfs, fun _ => Iff.rfl⟩

theorem fs_okErr (o : Option Int32) (w : Fs) (hfs : FileSystem w) :
    FileSystem (okErrW o w) ∧ FdsKept w (okErrW o w) := by
  unfold okErrW
  split
  · exact ⟨hfs, fun _ => Iff.rfl⟩
  · exact ⟨hfs, fun _ => Iff.rfl⟩

/-- **M1, the contract of `read`, for every oracle value**: `-1` and no bytes, or `k ≤ n` bytes with result `k`.
The heap is untouched (`pure`), the file system stays well formed and no descriptor opens or closes. -/
theorem fsRead_contract (fd : Int32) (n : UInt64) (w : Fs) (hfs : FileSystem w) (hn : n.toNat < 2 ^ 63) :
    ∃ r bs w', fsRead fd n w = (pure ((r, bs), w') : M ((Int64 × Array UInt8) × Fs)) ∧
      ((r = -1 ∧ bs.size = 0) ∨ (r.toInt = bs.size ∧ bs.size ≤ n.toNat)) ∧ FileSystem w' ∧ FdsKept w w' := by
  have hcap := readCap_le fd n w
  unfold fsRead
  dsimp only
  split
  · have hm : (UInt64.ofNat (readCap fd n w)).toNat = readCap fd n w := by
      have := n.toNat_lt
      simp only [UInt64.toNat_ofNat']
      omega
    obtain ⟨r, bs, w1, e, hres, hfs1, hk1, -, -, -⟩ :=
      fsReadReg_contract fd (UInt64.ofNat (readCap fd n w)) (tickW w) hfs (by rw [hm]; omega)
    rw [e]
    by_cases hr : r = -1
    · refine ⟨r, bs, _, rfl, ?_, ?_, ?_⟩
      · rcases hres with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, by rw [hm] at h2; omega⟩
      · simp only [hr, ite_true]; exact hfs1
      · intro j; simp only [hr, ite_true]; exact (hk1 j).trans Iff.rfl
    · obtain ⟨hd1, hd2⟩ := fs_debit fd bs.size w1 hfs1
      obtain ⟨ho1, ho2⟩ := fs_okErr (w.okErrno w.nos) (debitW fd bs.size w1) hd1
      refine ⟨r, bs, _, rfl, ?_, ?_, ?_⟩
      · rcases hres with h1 | ⟨h1, h2⟩
        · exact absurd h1.1 hr
        · exact Or.inr ⟨h1, by rw [hm] at h2; omega⟩
      · simp only [hr, ite_false]; exact ho1
      · intro j; simp only [hr, ite_false]; exact (ho2 j).trans ((hd2 j).trans (hk1 j))
  · exact ⟨-1, #[], _, rfl, Or.inl ⟨rfl, rfl⟩, hfs, fun _ => Iff.rfl⟩
  · rename_i bs0 _
    have hsz : (bs0.extract 0 (readCap fd n w)).size ≤ readCap fd n w := by
      simp only [Array.size_extract]; omega
    obtain ⟨hd1, hd2⟩ := fs_debit fd (bs0.extract 0 (readCap fd n w)).size (tickW w) hfs
    obtain ⟨ho1, ho2⟩ := fs_okErr (w.okErrno w.nos) _ hd1
    refine ⟨_, _, _, rfl, Or.inr ⟨?_, by omega⟩, ho1, fun j => (ho2 j).trans ((hd2 j).trans Iff.rfl)⟩
    rw [Int64.toInt_ofNat', Zlib.Gzlib.Proofs.bmod64 _ (by omega) (by omega)]

end ZlibF.Spec.Public
