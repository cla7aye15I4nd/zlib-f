import ZlibF.Proof.«gz.inv-open-path»

/-!
# gzlib.c: the descriptor table after `open`, for every world

`open` (`fsOpen`) on every OS-call oracle and every flag value keeps a well-formed world. When it returns -1 no
descriptor is opened or closed. Otherwise it returns a non-negative descriptor that was not open, and no other
descriptor changes: the regular-file `open` takes the lowest free slot, which is below `2^31` (it fails with `EMFILE`
otherwise), and the oracle may move it to another free slot below `2^31` (`relocateW`).
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof
open ZlibF.Spec.Public (FileSystem FdsKept)
open ZlibF.Spec.Public.GzOracle (FdOpen)
set_option autoImplicit false

/-- The lowest-slot search ends on a slot that is not open. -/
theorem lowestFd_go_free (w : Fs) : ∀ k i, w.fds.size ≤ i + k → ¬ FdOpen w (lowestFd.go w i k) := by
  intro k
  induction k with
  | zero =>
    rintro i hi ⟨f, hf⟩
    change w.fds[i]? = some (some f) at hf
    rw [Array.getElem?_eq_none (by omega)] at hf
    cases hf
  | succ k ih =>
    rintro i hi ⟨f, hf⟩
    have e : lowestFd.go w i (k + 1) =
        if i < w.fds.size then (if (w.fds[i]!).isNone then i else lowestFd.go w (i + 1) k) else i := rfl
    rw [e] at hf
    by_cases h1 : i < w.fds.size
    · by_cases h2 : (w.fds[i]!).isNone = true
      · rw [if_pos h1, if_pos h2] at hf
        rw [getElem!_pos w.fds i h1] at h2
        rw [Array.getElem?_eq_getElem h1] at hf
        simp only [Option.some.injEq] at hf
        rw [hf] at h2
        simp at h2
      · rw [if_pos h1, if_neg h2] at hf
        exact ih (i + 1) (by omega) ⟨f, hf⟩
    · rw [if_neg h1] at hf
      rw [Array.getElem?_eq_none (by omega)] at hf
      cases hf

theorem lowestFd_free (w : Fs) : ¬ FdOpen w (lowestFd w) :=
  lowestFd_go_free w (w.fds.size + 3) 3 (by omega)

/-- An existing descriptor other than the new slot stays open after the table update. -/
theorem openFdTable_keep (fds : Array (Option OFile)) (slot j : Nat) (file old : OFile)
    (hj : j ≠ slot) (hold : fds[j]? = some (some old)) :
    (openFdTable fds slot file)[j]? = some (some old) := by
  have hjs : j < fds.size := (Array.getElem?_eq_some_iff.mp hold).1
  by_cases hs : slot < fds.size
  · simpa [openFdTable, hs, Array.getElem?_setIfInBounds, Ne.symm hj] using hold
  · simpa [openFdTable, hs, Array.getElem?_setIfInBounds, Ne.symm hj, Array.getElem?_append, hjs] using hold

theorem openFdTable_iff (fds : Array (Option OFile)) (slot j : Nat) (file : OFile) (hj : j ≠ slot) :
    (∃ f, (openFdTable fds slot file)[j]? = some (some f)) ↔ ∃ f, fds[j]? = some (some f) :=
  ⟨fun ⟨f, hf⟩ => ⟨f, openFdTable_old fds slot j file f hj hf⟩,
   fun ⟨f, hf⟩ => ⟨f, openFdTable_keep fds slot j file f hj hf⟩⟩

theorem ofNat_ne_neg_one (slot : Nat) (hslot : slot < 2 ^ 31) : Int32.ofNat slot ≠ -1 := by
  intro he
  have h := (openSlot_cast slot hslot).2.2
  rw [he] at h
  exact absurd h (by decide)

/-- The node step of the regular-file `open`: an `EISDIR` refusal changes no descriptor; otherwise the chosen
slot is opened and nothing else changes in the table. -/
theorem openSourceNode_fds (slot n : Nat) (w : Fs) (acc : Int32) (has : Int32 → Bool)
    (hfs : FileSystem w) (hn : n < w.nodes.size) (r : Int32 × Fs)
    (hrun : openSourceNode slot n w acc has Heap.empty = .ok (r, Heap.empty)) :
    FileSystem r.2 ∧ ((r.1 = -1 ∧ r.2.fds = w.fds) ∨
      (r.1 = Int32.ofNat slot ∧ FdOpen r.2 slot ∧ ∀ j, j ≠ slot → (FdOpen r.2 j ↔ FdOpen w j))) := by
  unfold openSourceNode at hrun
  dsimp only at hrun
  split at hrun
  · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, -⟩ := hrun
    exact ⟨hfs, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i hnd
    simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, -⟩ := hrun
    have hget : w.nodes[n]? = some w.nodes[n]! := Array.getElem?_eq_some_getElem! _ _ hn
    split
    · rename_i ht
      refine ⟨?_, Or.inr ⟨rfl, ⟨_, (openFdTable_at _ _ _).2⟩, fun j hj => openFdTable_iff _ _ _ _ hj⟩⟩
      apply openFs_fd_valid _ slot _ (openFs_truncate_valid w n hfs hn)
      · simpa using hn
      · simp
      · intro node hg hd
        try dsimp only at hg
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_pos rfl, if_pos hn] at hg
        simp only [Option.some.injEq] at hg
        subst hg
        try dsimp only at hd
        simp only [hd, Bool.and_true] at hnd
        simpa using hnd
    · refine ⟨?_, Or.inr ⟨rfl, ⟨_, (openFdTable_at _ _ _).2⟩, fun j hj => openFdTable_iff _ _ _ _ hj⟩⟩
      apply openFs_fd_valid _ slot _ hfs hn (by simp)
      intro node hg hd
      try dsimp only at hg
      rw [hget] at hg
      simp only [Option.some.injEq] at hg
      subst hg
      simp only [hd, Bool.and_true] at hnd
      simpa using hnd

/-- The regular-file `open`, for every flag value: a refusal changes no descriptor; a success opens the lowest
free slot, which is below `2^31`, and nothing else in the table. -/
theorem openFsResultReg_fds (name : Array UInt8) (flags : Int32) (w : Fs) (hfs : FileSystem w) :
    FileSystem (openFsResultReg name flags w).2 ∧
    ((openFsResultReg name flags w).1 = -1 → FdsKept w (openFsResultReg name flags w).2) ∧
    ((openFsResultReg name flags w).1 ≠ -1 →
      (openFsResultReg name flags w).1 = Int32.ofNat (lowestFd w) ∧ lowestFd w < 2 ^ 31 ∧
      FdOpen (openFsResultReg name flags w).2 (lowestFd w) ∧
      ∀ j, j ≠ lowestFd w → (FdOpen (openFsResultReg name flags w).2 j ↔ FdOpen w j)) := by
  generalize he : openFsResultReg name flags w = result
  have hactual := openFsReg_eq name flags w Heap.empty
  rw [he] at hactual
  change openSource lowestFd name flags w Heap.empty = .ok (result, Heap.empty) at hactual
  unfold openSource at hactual
  dsimp only at hactual
  have fail : ∀ e : Int32, result = (-1, { w with errno := e }) →
      FileSystem result.2 ∧ (result.1 = -1 → FdsKept w result.2) ∧
      (result.1 ≠ -1 → result.1 = Int32.ofNat (lowestFd w) ∧ lowestFd w < 2 ^ 31 ∧
        FdOpen result.2 (lowestFd w) ∧ ∀ j, j ≠ lowestFd w → (FdOpen result.2 j ↔ FdOpen w j)) := by
    intro e hr
    subst hr
    exact ⟨hfs, fun _ _ => Iff.rfl, fun h => absurd rfl h⟩
  have node : ∀ (w' : Fs) (n : Nat) (acc : Int32) (has : Int32 → Bool), FileSystem w' → n < w'.nodes.size →
      w'.fds = w.fds → lowestFd w < 2 ^ 31 →
      openSourceNode (lowestFd w) n w' acc has Heap.empty = .ok (result, Heap.empty) →
      FileSystem result.2 ∧ (result.1 = -1 → FdsKept w result.2) ∧
      (result.1 ≠ -1 → result.1 = Int32.ofNat (lowestFd w) ∧ lowestFd w < 2 ^ 31 ∧
        FdOpen result.2 (lowestFd w) ∧ ∀ j, j ≠ lowestFd w → (FdOpen result.2 j ↔ FdOpen w j)) := by
    intro w' n acc has hw hn hfds hlt hrun
    obtain ⟨hF, hres⟩ := openSourceNode_fds (lowestFd w) n w' acc has hw hn result hrun
    rcases hres with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨hF, fun _ j => ?_, fun h => absurd h1 h⟩
      unfold FdOpen
      rw [h2, hfds]
    · refine ⟨hF, fun h => absurd h (by rw [h1]; exact ofNat_ne_neg_one _ hlt), fun _ => ⟨h1, hlt, h2, ?_⟩⟩
      intro j hj
      rw [h3 j hj]
      unfold FdOpen
      rw [hfds]
  split at hactual
  · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
    exact fail _ hactual.1.symm
  · split at hactual
    · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
      exact fail _ hactual.1.symm
    · split at hactual
      · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
        exact fail _ hactual.1.symm
      · rename_i hge
        have hlt : lowestFd w < 2 ^ 31 := by omega
        generalize hfind : (w.names.find? (fun e => e.1 == name)).map (·.2) = found at hactual
        cases found with
        | some n =>
          dsimp only at hactual
          split at hactual
          · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
            exact fail _ hactual.1.symm
          · exact node w n _ _ hfs (openFs_lookup_valid w name n hfs hfind) rfl hlt hactual
        | none =>
          dsimp only at hactual
          split at hactual
          · exact node _ w.nodes.size _ _ (openFs_create_valid w name hfs) (by simp) rfl hlt hactual
          · simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
            exact fail _ hactual.1.symm

theorem okErrW_fds (o : Option Int32) (w : Fs) : (okErrW o w).fds = w.fds := by
  cases o <;> rfl

theorem okErrW_fs (o : Option Int32) {w : Fs} (hw : FileSystem w) : FileSystem (okErrW o w) := by
  cases o
  · exact hw
  · exact hw

theorem set2_get_other (G : Array (Option OFile)) (k s j : Nat) (e : Option OFile) (hj : j ≠ s) (hjk : j ≠ k) :
    ((G.set! k e).set! s none)[j]? = G[j]? := by
  simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Ne.symm hj, Ne.symm hjk]

theorem set2_get_k (G : Array (Option OFile)) (k s : Nat) (e : Option OFile) (f : OFile) (hks : k ≠ s)
    (h : ((G.set! k e).set! s none)[k]? = some (some f)) : e = some f := by
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
  repeat' split at h
  all_goals simp_all

theorem set2_get_s (G : Array (Option OFile)) (k s : Nat) (e : Option OFile) (f : OFile) :
    ((G.set! k e).set! s none)[s]? ≠ some (some f) := by
  intro h
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
  repeat' split at h
  all_goals simp_all

theorem grow_get (fds : Array (Option OFile)) (k j : Nat) (f : OFile) :
    (if k < fds.size then fds else fds ++ Array.replicate (k + 1 - fds.size) none)[j]? = some (some f) ↔
      fds[j]? = some (some f) := by
  by_cases hk : k < fds.size
  · rw [if_pos hk]
  · rw [if_neg hk]
    by_cases hjs : j < fds.size
    · simp [Array.getElem?_append, hjs]
    · rw [Array.getElem?_eq_none (show fds.size ≤ j by omega)]
      simp [Array.getElem?_append, hjs, Array.getElem?_replicate]

/-- The table after the oracle's move of descriptor `slot` to the free slot `k`. -/
theorem relocate_get (fds : Array (Option OFile)) (slot k j : Nat) (e : Option OFile) (f : OFile)
    (hj : j ≠ slot) (hjk : j ≠ k) :
    ((((if k < fds.size then fds else fds ++ Array.replicate (k + 1 - fds.size) none).set! k e).set! slot none)[j]? =
      some (some f)) ↔ fds[j]? = some (some f) := by
  rw [set2_get_other _ k slot j e hj hjk]
  exact grow_get fds k j f

/-- What `open` guarantees of its result `x` on the world `fs` (the statement of `openFsResult_fds`). -/
def OpenPost (fs : Fs) (x : Int32 × Fs) : Prop :=
  FileSystem x.2 ∧ (x.1 = -1 → FdsKept fs x.2) ∧
    (x.1 ≠ -1 → 0 ≤ x.1.toInt ∧ ¬ FdOpen fs x.1.toInt.toNat ∧
      ∀ j, j ≠ x.1.toInt.toNat → (FdOpen x.2 j ↔ FdOpen fs j))

/-- **`open`, for every world and every flag value.** It keeps a well-formed world. When it returns -1 no
descriptor changes; otherwise its result is a non-negative descriptor that was not open, and no other descriptor
changes. -/
theorem openFsResult_fds (name : Array UInt8) (flags : Int32) (fs : Fs) (hfs : FileSystem fs) :
    FileSystem (openFsResult name flags fs).2 ∧
    ((openFsResult name flags fs).1 = -1 → FdsKept fs (openFsResult name flags fs).2) ∧
    ((openFsResult name flags fs).1 ≠ -1 →
      0 ≤ (openFsResult name flags fs).1.toInt ∧
      ¬ FdOpen fs (openFsResult name flags fs).1.toInt.toNat ∧
      ∀ j, j ≠ (openFsResult name flags fs).1.toInt.toNat →
        (FdOpen (openFsResult name flags fs).2 j ↔ FdOpen fs j)) := by
  generalize he : openFsResult name flags fs = result
  have hactual := openFs_eq name flags fs Heap.empty
  rw [he] at hactual
  unfold fsOpen at hactual
  dsimp only at hactual
  cases hof : fs.openFail fs.nos with
  | some e =>
    simp only [hof, pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
    obtain ⟨rfl, -⟩ := hactual
    exact ⟨hfs, fun _ _ => Iff.rfl, fun h => absurd rfl h⟩
  | none =>
    simp only [hof] at hactual
    obtain ⟨⟨r, w'⟩, hy⟩ := Zlib.GzFs.Proofs.fsOpenReg_pure name flags (tickW fs)
    have hreg : openFsResultReg name flags (tickW fs) = (r, w') := by
      unfold openFsResultReg
      rw [hy]
      rfl
    rw [hy] at hactual
    simp only [bind_app, pure_app, Except.ok.injEq, Prod.mk.injEq] at hactual
    obtain ⟨rfl, -⟩ := hactual
    have hR := openFsResultReg_fds name flags (tickW fs) hfs
    rw [hreg] at hR
    obtain ⟨hF, hK, hS⟩ := hR
    by_cases hr : r = -1
    · rw [if_pos hr]
      exact ⟨hF, fun _ => hK hr, fun h => absurd hr h⟩
    · rw [if_neg hr]
      obtain ⟨hcast, hlt, hopen, hothers⟩ := hS hr
      obtain ⟨hti, htn, htpos⟩ := openSlot_cast (lowestFd (tickW fs)) hlt
      have hfree : ¬ FdOpen fs (lowestFd (tickW fs)) := lowestFd_free (tickW fs)
      have hcast' : r = Int32.ofNat (lowestFd (tickW fs)) := hcast
      have hrn : r.toInt.toNat = lowestFd (tickW fs) := by rw [hcast']; exact htn
      have hrpos : 0 ≤ r.toInt := by rw [hcast']; exact htpos
      generalize hW : okErrW (fs.okErrno fs.nos) w' = W
      have hWfds : W.fds = w'.fds := by rw [← hW]; exact okErrW_fds _ _
      have hWfs : FileSystem W := by rw [← hW]; exact okErrW_fs _ hF
      have hWopen : ∀ j, FdOpen W j ↔ FdOpen w' j := by
        intro j
        unfold FdOpen
        rw [hWfds]
      have plain : OpenPost fs (r, W) := by
        unfold OpenPost
        refine ⟨hWfs, fun h => absurd h hr, fun _ => ⟨hrpos, ?_, ?_⟩⟩
        · show ¬ FdOpen fs r.toInt.toNat
          rw [hrn]
          exact hfree
        · intro j hj
          show FdOpen W j ↔ FdOpen fs j
          rw [hWopen j]
          exact hothers j (by rw [← hrn]; exact hj)
      have moved : ∀ k : Nat, ¬ FdOpen W k → k < 2 ^ 31 →
          OpenPost fs (Int32.ofNat k, { W with fds :=
            ((if k < W.fds.size then W.fds else W.fds ++ Array.replicate (k + 1 - W.fds.size) none).set! k
              ((W.fds[r.toInt.toNat]?).getD none)).set! r.toInt.toNat none }) := by
        intro k hkW hk31
        have hks : k ≠ lowestFd (tickW fs) := by
          intro hks
          subst hks
          exact hkW ((hWopen _).2 hopen)
        have hkfs : ¬ FdOpen fs k := by
          intro hko
          exact hkW ((hWopen k).2 ((hothers k hks).2 hko))
        obtain ⟨hki, hkn, hkpos⟩ := openSlot_cast k hk31
        obtain ⟨hl, hp, hfd, hd⟩ := hWfs
        unfold OpenPost
        refine ⟨⟨hl, hp, ?_, hd⟩, fun h => absurd h (ofNat_ne_neg_one k hk31), fun _ => ⟨hkpos, ?_, ?_⟩⟩
        · intro i file hget
          change (((if k < W.fds.size then W.fds else W.fds ++ Array.replicate (k + 1 - W.fds.size) none).set! k
              ((W.fds[r.toInt.toNat]?).getD none)).set! r.toInt.toNat none)[i]? = some (some file) at hget
          rw [hrn] at hget
          by_cases his : i = lowestFd (tickW fs)
          · subst his
            exact absurd hget (set2_get_s _ _ _ _ _)
          · by_cases hik : i = k
            · subst hik
              have he := set2_get_k _ i _ _ file (fun h => his h) hget
              apply hfd (lowestFd (tickW fs)) file
              cases hx : W.fds[lowestFd (tickW fs)]? with
              | none => rw [hx] at he; cases he
              | some x => rw [hx] at he; simp only [Option.getD_some] at he; rw [he]
            · exact hfd i file ((relocate_get W.fds _ k i _ file his hik).1 hget)
        · show ¬ FdOpen fs (Int32.ofNat k).toInt.toNat
          rw [hkn]
          exact hkfs
        · intro j hj
          change j ≠ (Int32.ofNat k).toInt.toNat at hj
          rw [hkn] at hj
          show (∃ f, (((if k < W.fds.size then W.fds else W.fds ++ Array.replicate (k + 1 - W.fds.size) none).set! k
              ((W.fds[r.toInt.toNat]?).getD none)).set! r.toInt.toNat none)[j]? = some (some f)) ↔ FdOpen fs j
          rw [hrn]
          by_cases hjs : j = lowestFd (tickW fs)
          · subst hjs
            constructor
            · rintro ⟨f, hf⟩
              exact absurd hf (set2_get_s _ _ _ _ _)
            · intro hj'
              exact absurd hj' hfree
          · have e2 : FdOpen fs j ↔ FdOpen W j := ((hWopen j).trans (hothers j hjs)).symm
            rw [e2]
            exact ⟨fun ⟨f, hf⟩ => ⟨f, (relocate_get W.fds _ k j _ f hjs hj).1 hf⟩,
              fun ⟨f, hf⟩ => ⟨f, (relocate_get W.fds _ k j _ f hjs hj).2 hf⟩⟩
      split
      · rename_i k hk
        show OpenPost fs (relocateW r k W)
        unfold relocateW
        cases hx : W.fds[k]? with
        | none =>
          dsimp only
          split
          · rename_i hc
            exact moved k (fun ⟨f, hf⟩ => by rw [hx] at hf; cases hf) hc.2.1
          · exact plain
        | some o =>
          cases o with
          | none =>
            dsimp only
            split
            · rename_i hc
              exact moved k (fun ⟨f, hf⟩ => by rw [hx] at hf; cases hf) hc.2.1
            · exact plain
          | some f =>
            dsimp only
            split
            · rename_i hc
              exact absurd hc.2.2 (by decide)
            · exact plain
      · exact plain

#print axioms lowestFd_free
#print axioms openFsResultReg_fds
#print axioms openFsResult_fds

end Zlib.Gzlib.Proofs
