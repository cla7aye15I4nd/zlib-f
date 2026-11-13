import ZlibF.Proof.«public-gz-rewind»
import ZlibF.Proof.«gzlib.c.dopen-joint-witness»

/-!
# Offset and rewind values need the regular-file instance

Commit `caad9db4` made `read`, `write`, `lseek`, `close` and `open` calls of an OS-call oracle. An oracle `lseek`
may return a value in `[0, 2^63 - 1]` without moving the descriptor (M3; Linux devices such as `/dev/zero` return
0 without moving). `Goal.gzoffset64`, `Goal.gzoffset` and `Goal.gzrewind` state the descriptor position after
`lseek`, so they became false. They now assume `RegularOs fs`, and the offset contract lets the call counter
`nos` change with `errno`.

The world below is admitted by `FileSystem`: descriptor 3 reads the file `p`, at position 0, and every `lseek`
returns 77 without moving. `gzdopen(3, "r")` records the start 77 (the `gzdopen` goal, proved for every world,
gives the state). Then:

- `gzoffset64` and `gzoffset` return 77, but the old contracts claim the descriptor position, 0. The corrected
  contract without `RegularOs` is false too, so the premise is needed, not only the relaxed counter.
- `gzrewind` returns 0, but the descriptor stays at 0, not at the start 77, which the old goal claims.

The old statements are copied here verbatim. These regressions fail if the premise is dropped again.
-/

namespace ZlibF.Spec.Public.GzOffsetRegularWorld
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public.OffsetProof

/-! ## The statements before `caad9db4` -/

/-- `OffsetContract` before `caad9db4`: no `RegularOs` premise, and only `errno` may change in the world. -/
def OldOffsetContract (program : GzFilePtr → G Int64) : Prop :=
  (∀ h fs, program none fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s → FileSystem fs →
    ∃ value fs', program (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), h) ∧
      { fs' with errno := fs.errno } = fs ∧
      (if s.fd.toInt < 0 then value = -1 else match fs.fds[s.fd.toInt.toNat]? with
       | some (some file) => value.toInt = (file.pos : Int) -
           (if s.mode = GZ_READ then s.strm.avail_in.toNat else 0)
       | _ => value = -1))

/-- `Goal.gzrewind` before `caad9db4`: the present goal without `RegularOs fs`. -/
def OldGzrewind : Prop :=
  (∀ h fs, Zlib.Gzlib.gzrewind none fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s →
    ∃ rc fs' after, Zlib.Gzlib.gzrewind (some (.in_gzstate_x i)) fs h = .ok ((rc, fs'), after) ∧
      ((rc = -1 ∧ after = h) ∨
       (rc = 0 ∧ after = putGz (dropWindow h s.msg) i (rewoundState s) ∧
        ∃ file, fs'.fds[s.fd.toInt.toNat]? = some (some file) ∧ file.pos = s.start.toInt.toNat)) ∧
      (s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR) → rc = -1 ∧ fs' = fs))

/-- The present `OffsetContract` without its `RegularOs fs` premise. -/
def OffsetContractEveryWorld (program : GzFilePtr → G Int64) : Prop :=
  (∀ h fs, program none fs h = .ok ((-1, fs), h)) ∧
  (∀ h fs i s, GzReachable h fs i → GzValid h i s → FileSystem fs →
    ∃ value fs', program (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), h) ∧
      { fs' with errno := fs.errno, nos := fs.nos } = fs ∧
      (if s.fd.toInt < 0 then value = -1 else match fs.fds[s.fd.toInt.toNat]? with
       | some (some file) => value.toInt = (file.pos : Int) -
           (if s.mode = GZ_READ then s.strm.avail_in.toNat else 0)
       | _ => value = -1))

/-- The old contract implies the corrected one without `RegularOs`. -/
theorem old_offset_every_world {program : GzFilePtr → G Int64} (hc : OldOffsetContract program) :
    OffsetContractEveryWorld program := by
  refine ⟨hc.1, fun h fs i s hr hv hfs => ?_⟩
  obtain ⟨value, fs', e, hf, hval⟩ := hc.2 h fs i s hr hv hfs
  have hn : fs'.nos = fs.nos := by
    have e := congrArg Fs.nos hf
    exact e
  refine ⟨value, fs', e, ?_, hval⟩
  rw [← hn]
  exact hf

/-- `gzoffset` is `gzoffset64`, so the wrapper's contract gives the other. -/
theorem every_world_wrapper (hc : OffsetContractEveryWorld Zlib.Gzlib.gzoffset) :
    OffsetContractEveryWorld Zlib.Gzlib.gzoffset64 := by
  refine ⟨fun h fs => ?_, fun h fs i s hr hv hfs => ?_⟩
  · rw [← gzoffset_eq]
    exact hc.1 h fs
  · obtain ⟨value, fs', e, hf, hval⟩ := hc.2 h fs i s hr hv hfs
    exact ⟨value, fs', by rw [← gzoffset_eq]; exact e, hf, hval⟩

/-! ## A world whose `lseek` does not move -/

/-- The descriptor's file entry: file `p`, read-only, at position 0. -/
def file0 : OFile := { node := 0, pos := 0, rd := true, wr := false, append := false }

/-- File `p` holds `"hi"`; descriptor 3 reads it; every `lseek` returns 77 and does not move (M3). -/
def readerWorld : Fs :=
  { names := #[(#[112], 0)]
    nodes := #[{ data := #[104, 105], isDir := false }]
    fds := #[none, none, none, some file0]
    lseekChoice := fun _ => .value 77 }

/-- What the oracle `lseek` returns. -/
def V : Int64 := Int64.ofInt (min ((77 : Nat) : Int) (2 ^ 63 - 1))

/-- The world is not the regular-file instance. -/
theorem readerWorld_not_regular : ¬ RegularOs readerWorld := by
  intro h
  have hc := (h.1 0 (Nat.zero_le _)).2.2.1
  cases hc

/-- The caller heap: the mode string `"r"` in block 0, and the build's constant tables. -/
def readerHeap : Heap :=
  { Heap.empty with bytes := ⟨#[some #[114, 0]]⟩
                    nextBlk := 1, static := Zlib.Gzlib.Proofs.descriptorJointStatics }

theorem reader_fresh : Fresh readerHeap := by
  intro b hb hl
  have hb1 : 1 ≤ b := hb
  have hn : [some #[(114 : UInt8), 0]][b]? = none :=
    List.getElem?_eq_none (by change 1 ≤ b; omega)
  simp [Heap.live, readerHeap, Heap.empty, Tbl.get, Tbl.empty, Array.getD_eq_getD_getElem?, default, hn] at hl

theorem reader_uniq : Zlib.Gzlib.Spec.Uniq readerHeap := by
  intro b
  have hc : b = 0 ∨ 1 ≤ b := by omega
  rcases hc with rfl | hb
  all_goals simp (disch := omega) [readerHeap, Heap.empty, Tbl.get, Tbl.empty,
    Zlib.Gzlib.Spec.cnt, Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
  all_goals first | decide | split <;> omega

theorem reader_globals : LibraryGlobals readerHeap := rfl

theorem reader_mode : CString readerHeap (.ref (.blk 0) 0) [114] :=
  ⟨Or.inr ⟨.blk 0, 0, #[114, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩

theorem reader_filesystem : FileSystem readerWorld := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro path node hm
    simp [readerWorld] at hm
    rcases hm with ⟨rfl, rfl⟩
    decide
  · intro i file hi
    have hr : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i := by omega
    rcases hr with rfl | rfl | rfl | rfl | hb
    · simp [readerWorld] at hi
    · simp [readerWorld] at hi
    · simp [readerWorld] at hi
    · simp [readerWorld] at hi
      subst file
      refine ⟨by decide, by decide, ?_⟩
      intro node hn
      simp [readerWorld, file0] at hn
      subst node
      simp [file0]
    · have hn : readerWorld.fds[i]? = none := Array.getElem?_eq_none (by change 4 ≤ i; exact hb)
      rw [hn] at hi
      contradiction
  · intro i node hi
    by_cases he : i = 0
    · subst i
      simp [readerWorld] at hi
      subst node
      decide
    · have hb : 1 ≤ i := by omega
      have hn : readerWorld.nodes[i]? = none := Array.getElem?_eq_none (by change 1 ≤ i; exact hb)
      rw [hn] at hi
      contradiction

/-- `gzdopen(3, "r")` in this world opens a reader whose start is the value `lseek` returned, 77, while the
descriptor stays at 0. Everything comes from the `gzdopen` goal, proved for every world. -/
theorem reader_opened : ∃ fs' after i s,
    GzReachable after fs' i ∧ GzValid after i s ∧ FileSystem fs' ∧ fs' = tickW readerWorld ∧
    s.fd = 3 ∧ s.mode = GZ_READ ∧ s.err = Z_OK ∧ s.msg = .null ∧ s.strm.avail_in = 0 ∧ s.start = V := by
  have hm : ((.ref (.blk 0) 0 : BPtr) ≠ .null → CString readerHeap (.ref (.blk 0) 0) [114]) :=
    fun _ => reader_mode
  have hp0 : parsedMode [114] = some (.read, -1, 0, 0) := by decide
  obtain ⟨result, fs', after, hrun, -, hpost⟩ := Zlib.Gzlib.Proofs.gzdopen_complete.2 readerHeap readerWorld 3
    (.ref (.blk 0) 0) [114] reader_fresh reader_uniq reader_globals reader_filesystem (by decide) hm
  cases result with
  | none =>
    obtain ⟨-, -, hwhy⟩ := hpost
    rcases hwhy with hn | hn | ⟨k, -, -, hk⟩
    · cases hn
    · rw [hp0] at hn
      cases hn
    · have ht : readerHeap.allocOk k = true := rfl
      rw [ht] at hk
      cases hk
  | some p =>
    rcases p with ⟨i⟩
    obtain ⟨s, mode, level, strategy, direct, hp, hst, hw, -⟩ := hpost
    rw [hp0] at hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -, -, -⟩ := hp
    obtain ⟨hv, hmode, hfd, -, -, -, -, -, -, herr, hmsg, -, -, -, -, -, havail, -⟩ := hst
    obtain ⟨opened, ⟨-, rfl⟩, hw2⟩ := hw
    rw [if_neg (show ¬ ((3 : Int32) = -1) by decide),
      if_neg (show ¬ (ZlibF.Spec.Api.GzMode.read = .append) by decide), if_pos rfl] at hw2
    obtain ⟨position, hl, hstart⟩ := hw2
    rw [fsLseek_eq] at hl
    have hv77 : lseekRes 3 0 SEEK_CUR readerWorld = (V, tickW readerWorld) := rfl
    rw [hv77] at hl
    cases hl
    rw [if_neg (show ¬ (V = -1) by decide)] at hstart
    exact ⟨tickW readerWorld, after, i, s,
      GzReachable.dopen reader_fresh reader_uniq reader_globals reader_filesystem reader_mode hrun,
      hv, reader_filesystem, rfl, hfd, hmode.trans (if_pos rfl), herr, hmsg, havail, hstart⟩

/-! ## The old statements are false -/

/-- **The corrected offset contract needs `RegularOs`**: without it, `gzoffset64` on the reader returns 77 while
the descriptor is at 0. -/
theorem gzoffset64_every_world_false : ¬ OffsetContractEveryWorld Zlib.Gzlib.gzoffset64 := by
  intro hc
  obtain ⟨fs', after, i, s, hr, hv, hfs, rfl, hfd, hmode, -, -, havail, -⟩ := reader_opened
  obtain ⟨value, fs'', hrun, -, hval⟩ := hc.2 after (tickW readerWorld) i s hr hv hfs
  have hrec := gzoffset64_record hv.1 (Or.inl hmode) (tickW readerWorld)
  rw [hfd] at hrec
  have hl1 : (lseekRes 3 0 SEEK_CUR (tickW readerWorld)).1 = V := rfl
  have hl2 : (lseekRes 3 0 SEEK_CUR (tickW readerWorld)).2 = tickW (tickW readerWorld) := rfl
  rw [hl1, hl2, if_neg (show ¬ (V = -1) by decide), if_pos hmode, havail] at hrec
  have hrec' : Zlib.Gzlib.gzoffset64 (some (.in_gzstate_x i)) (tickW readerWorld) after = _ := hrec
  rw [hrec'] at hrun
  cases hrun
  have hf : (tickW readerWorld).fds[s.fd.toInt.toNat]? = some (some file0) := by rw [hfd]; rfl
  rw [if_neg (show ¬ (s.fd.toInt < 0) by rw [hfd]; decide), hf] at hval
  have hv2 : (Int64.ofInt (V.toInt - ((0 : UInt32).toNat : Int))).toInt =
      (file0.pos : Int) - (if s.mode = GZ_READ then s.strm.avail_in.toNat else 0) := hval
  rw [if_pos hmode, havail] at hv2
  exact absurd hv2 (by decide)

/-- **`Goal.gzoffset64` before `caad9db4` is false.** -/
theorem old_gzoffset64_false : ¬ OldOffsetContract Zlib.Gzlib.gzoffset64 :=
  fun hc => gzoffset64_every_world_false (old_offset_every_world hc)

/-- The corrected `gzoffset` contract needs `RegularOs` too. -/
theorem gzoffset_every_world_false : ¬ OffsetContractEveryWorld Zlib.Gzlib.gzoffset :=
  fun hc => gzoffset64_every_world_false (every_world_wrapper hc)

/-- **`Goal.gzoffset` before `caad9db4` is false.** -/
theorem old_gzoffset_false : ¬ OldOffsetContract Zlib.Gzlib.gzoffset :=
  fun hc => gzoffset_every_world_false (old_offset_every_world hc)

/-- **`Goal.gzrewind` before `caad9db4` is false**: `gzrewind` on the reader returns 0, but the descriptor stays
at 0, not at the start 77. -/
theorem old_gzrewind_false : ¬ OldGzrewind := by
  intro hc
  obtain ⟨fs', after, i, s, hr, hv, -, rfl, hfd, hmode, herr, hmsg, -, hstart⟩ := reader_opened
  obtain ⟨rc, fs'', after', hrun, hcase, -⟩ := hc.2 after (tickW readerWorld) i s hr hv
  have hrec := GzRewindProof.gzrewind_record hv.1 (Or.inl hmsg) (fun _ => hmsg) (tickW readerWorld)
  have hcond : ¬ (s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)) := by
    rw [hmode, herr]
    decide
  rw [if_neg hcond, hfd, hstart] at hrec
  have hl1 : (lseekRes 3 V SEEK_SET (tickW readerWorld)).1 = V := rfl
  have hl2 : (lseekRes 3 V SEEK_SET (tickW readerWorld)).2 = tickW (tickW readerWorld) := rfl
  rw [hl1, hl2, if_neg (show ¬ (V = -1) by decide)] at hrec
  have hrec' : Zlib.Gzlib.gzrewind (some (.in_gzstate_x i)) (tickW readerWorld) after = _ := hrec
  rw [hrec'] at hrun
  cases hrun
  rcases hcase with ⟨h0, -⟩ | ⟨-, -, file, hf, hpos⟩
  · exact absurd h0 (by decide)
  · rw [hfd] at hf
    have hf0 : (tickW (tickW readerWorld)).fds[(3 : Int32).toInt.toNat]? = some (some file0) := rfl
    rw [hf0] at hf
    cases hf
    rw [hstart] at hpos
    exact absurd hpos (by decide)

#print axioms readerWorld_not_regular
#print axioms reader_opened
#print axioms gzoffset64_every_world_false
#print axioms old_gzoffset64_false
#print axioms gzoffset_every_world_false
#print axioms old_gzoffset_false
#print axioms old_gzrewind_false
end ZlibF.Spec.Public.GzOffsetRegularWorld
