import ZlibF.Proof.«gzlib.c.open»

/-!
# gzlib.c: successful state allocation and mode rejection

These are executions of the real `gz_open`, including its allocation, field
writes, mode loop, and cleanup. The mode pointer here is into a heap byte block.
The rejection branches do not read the path. A complete successful execution
and its public state invariant have a concrete witness. The universal open
contract remains open.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Exact heap after allocating and releasing the fresh handle. The allocation
metadata advances, and every pre-existing object is retained. -/
def openReleased (h : Heap) : Heap :=
  { h with
    gzstates := upd h.gzstates h.nextBlk none
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1 }

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` rejects an empty
mode after allocating, initializing, and freeing its handle. This internal lemma
uses a mode byte block, with a readable NUL at the given offset. -/
theorem gz_open_empty_mode (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (b off : Nat) (a : Array UInt8) (hp : path ≠ .null)
    (ha : h.bytes b = some a) (hb : off < a.size) (hz : a[off] = 0)
    (hok : h.allocOk h.nalloc = true) (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open path fd (.ref (.blk b) off) fs h = .ok ((none, fs), openReleased h) := by
  unfold gz_open
  offsetsimp [hp, allocGzState, hok, hfresh, setS, upd_upd]
  unfold gwhile
  rw [show fuel = 18446744073709551615 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, ha, hb, hz, setS, upd_upd, GZ_NONE, freeGzState, openReleased]

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` rejects `+`
immediately and frees its handle. It neither scans subsequent mode bytes nor
reads the path. The mode pointer is into a heap byte block. -/
theorem gz_open_plus_mode (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32)
    (b off : Nat) (a : Array UInt8) (hp : path ≠ .null)
    (ha : h.bytes b = some a) (hb : off < a.size) (hz : a[off] = 43)
    (hok : h.allocOk h.nalloc = true) (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open path fd (.ref (.blk b) off) fs h = .ok ((none, fs), openReleased h) := by
  unfold gz_open
  offsetsimp [hp, allocGzState, hok, hfresh, setS, upd_upd]
  unfold gwhile
  rw [show fuel = 18446744073709551615 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, ha, hb, hz, setS, upd_upd, GZ_NONE, freeGzState, openReleased]
  rw [show 18446744073709551615 = 18446744073709551614 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, ha, hb, hz, setS, upd_upd, freeGzState, openReleased]

/-- Rejection after a successful handle allocation preserves every existing
object, with no outstanding allocation. -/
theorem openReleased_frame (h : Heap) (hfresh : h.slotUsed h.nextBlk = false) :
    ZlibF.Spec.Public.Frame h (openReleased h) (fun _ => False) ∧
    ZlibF.Spec.Public.LiveChange h (openReleased h) (fun _ => False) (fun _ => False) := by
  have hn := Heap.slotUsed_eq_false.mp hfresh
  have hg : h.gzstates h.nextBlk = none := (Heap.not_live.mp hn).2.2.2.2.2.2
  have hsame (b : Nat) : (upd h.gzstates h.nextBlk none) b = h.gzstates b := by
    by_cases he : b = h.nextBlk
    · subst b; simp [hg]
    · simp [he]
  constructor
  · refine ⟨rfl, rfl, rfl, by simp [openReleased], by simp [openReleased], ?_⟩
    intro b _ _
    simp [openReleased, hsame]
  · intro b
    simp [Heap.live, openReleased, hsame]

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` with the exact
mode `w` frees its allocated handle if the following path allocation fails.
The path may have any length and both pointers may be offsets in byte blocks.
The real mode loop and `strlen` are evaluated; no file call is reached. -/
theorem gz_open_write_path_alloc_failure (h : Heap) (fs : Fs) (fd : Int32)
    (mb mo pb po last : Nat) (ma pa : Array UInt8)
    (hm : h.bytes mb = some ma) (hmend : mo + 1 < ma.size)
    (hmw : ma[mo] = 119) (hmz : ma[mo + 1] = 0)
    (hp : h.bytes pb = some pa) (hplast : po ≤ last)
    (hpz : pa[last]? = some 0)
    (hpn : ∀ j, po ≤ j → j < last → pa[j]? ≠ some 0)
    (hok : h.allocOk h.nalloc = true) (hfail : h.allocOk (h.nalloc + 1) = false)
    (hfresh : h.slotUsed h.nextBlk = false) :
    gz_open (.ref (.blk pb) po) fd (.ref (.blk mb) mo) fs h =
      .ok ((none, fs), { openReleased h with nalloc := h.nalloc + 2 }) := by
  have hmo : mo < ma.size := by omega
  have hadd : 0 ≤ (mo : Int) + 1 ∧ (mo : Int) + 1 ≤ (ma.size : Int) := by omega
  have hs : strlenFrom pa po = some last :=
    strlenFrom_eq pa last hpz (last - po) po (by omega) hpn
  unfold gz_open
  offsetsimp [allocGzState, hok, hfresh, setS, upd_upd]
  unfold gwhile
  rw [show fuel = 18446744073709551615 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, hm, hmo, hmw, setS, upd_upd, Ptr.add, hmend, hadd]
  rw [show 18446744073709551615 = 18446744073709551614 + 1 by rfl, gwhile.go]
  offsetsimp [load8, Ptr.load, hm, hmend, hmz, setS, upd_upd,
    GZ_NONE, GZ_WRITE, GZ_READ, strlenB, hp, hs, allocB, hfail,
    freeGzState, openReleased]

/-- A concrete caller heap with the path `p` and the mode `w`. Its two byte
blocks are live, and all allocator calls succeed. -/
def openWriteWitnessHeap (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[112, 0], some #[119, 0]]⟩
    nextBlk := 2
    static := statics }

/-- Handle returned by the concrete write-mode open. Integer fields not written
by initialization retain the chosen zero garbage; this does not claim that C
initializes pointer fields which it never writes. -/
def openWriteWitnessState : GzState :=
  { GzState.zeroed with
    mode := GZ_WRITE
    fd := 3
    path := .ref (.blk 3) 0
    want := 8192
    level := Z_DEFAULT_COMPRESSION }

/-- Exact world after creating the witness file. -/
def openWriteWitnessFs : Fs :=
  { names := #[(#[112], 0)]
    nodes := #[{ data := #[], isDir := false }]
    fds := #[none, none, none, some { node := 0, pos := 0, rd := false, wr := true, append := false }]
    nos := 1 }

/-- Exact result heap, including the freed formatting temporary. -/
def openWriteWitnessAfter (statics : Statics) : Heap :=
  { Heap.empty with
    bytes := ⟨#[some #[112, 0], some #[119, 0], none, some #[112, 0], none]⟩
    ro := ⟨#[false, false, false, false, false]⟩
    gzstates := ⟨#[none, none, some openWriteWitnessState]⟩
    nextBlk := 5
    nalloc := 2
    static := statics }

set_option maxRecDepth 20000 in
/-- Kernel reduction of the complete real successful open, including path copy,
`fsOpen`, and `gz_reset`. -/
theorem gzopen_write_witness_run (statics : Statics) :
    gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) ({} : Fs)
      (openWriteWitnessHeap statics) =
      .ok ((some (.in_gzstate_x 2), openWriteWitnessFs), openWriteWitnessAfter statics) := by
  conv => lhs; cbv
  rfl

/-- `gzFile gzopen(const char *path, const char *mode)` has a real successful
execution from caller-owned path and mode bytes. The result records the handle,
its copied path, and exact allocation metadata from that same execution.
This is a concrete witness, not the universal open contract. -/
theorem gzopen_write_success_witness (statics : Statics) :
    ∃ fs after s,
      gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) ({} : Fs) (openWriteWitnessHeap statics) =
        .ok ((some (.in_gzstate_x 2), fs), after) ∧
      after.gzstates 2 = some s ∧
      s.mode = GZ_WRITE ∧ s.fd = 3 ∧ s.path = .ref (.blk 3) 0 ∧
      s.size = 0 ∧ s.want = 8192 ∧ s.err = Z_OK ∧ s.msg = .null ∧
      s.x.have = 0 ∧ s.x.pos = 0 ∧ s.past = 0 ∧ s.again = 0 ∧
      s.skip = 0 ∧ s.strm.avail_in = 0 ∧
      after.bytes 3 = some #[112, 0] ∧ after.nalloc = 2 ∧ after.nextBlk = 5 := by
  refine ⟨openWriteWitnessFs, openWriteWitnessAfter statics, openWriteWitnessState, ?_, ?_⟩
  · exact gzopen_write_witness_run statics
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The successful result has no live object at or beyond its next block. -/
theorem openWriteWitnessAfter_fresh (statics : Statics) :
    Fresh (openWriteWitnessAfter statics) := by
  intro b hb hl
  have hb5 : 5 ≤ b := hb
  have hb3 : 3 ≤ b := by omega
  simp (disch := omega) [Heap.live, openWriteWitnessAfter, Heap.empty, Tbl.get,
    Tbl.empty, Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default] at hl

/-- The handle and copied path occupy different block identities. -/
theorem openWriteWitnessAfter_uniq (statics : Statics) :
    Uniq (openWriteWitnessAfter statics) := by
  intro b
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ 5 ≤ b := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | hb
  all_goals simp (disch := omega) [openWriteWitnessAfter, Heap.empty, Tbl.get,
    Tbl.empty, cnt, Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
  all_goals first | decide | split <;> omega

/-- The successful real execution establishes the public open-state invariant
when the caller heap carries the specified library globals. This witnesses the
write-mode invariant; it does not prove the universal `OpenContract`. -/
theorem gzopen_write_success_OpenState (statics : Statics)
    (hg : ZlibF.Spec.Public.LibraryGlobals (openWriteWitnessHeap statics)) :
    ZlibF.Spec.Public.OpenState (openWriteWitnessAfter statics) 2 openWriteWitnessState
      .write (-1) 0 0 3 [112] := by
  have hglobals : ZlibF.Spec.Public.LibraryGlobals (openWriteWitnessAfter statics) := hg
  have hstr : ZlibF.Spec.Public.CString (openWriteWitnessAfter statics)
      (.ref (.blk 3) 0) [112] := by
    refine ⟨Or.inr ⟨.blk 3, 0, #[112, 0], rfl, rfl, by decide, rfl⟩,
      by decide, by decide⟩
  have hbuf : ZlibF.Spec.Public.MallocBuffer (openWriteWitnessAfter statics)
      (.ref (.blk 3) 0) 2 := ⟨3, #[112, 0], rfl, rfl, rfl, by decide⟩
  have hv : ZlibF.Spec.Public.GzValid (openWriteWitnessAfter statics) 2
      openWriteWitnessState := by
    refine ⟨rfl, Or.inr rfl, openWriteWitnessAfter_fresh statics,
      openWriteWitnessAfter_uniq statics, hglobals, ⟨[112], hstr, hbuf⟩,
      Or.inl rfl, ?_, by decide, by decide, ?_, ?_⟩
    · intro _; rfl
    · intro hn; exact (hn rfl).elim
    · intro hn; exact (hn rfl).elim
  exact ⟨hv, rfl, rfl, hstr, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- The initialized public state and the real successful run are about the same
explicit heap. A library-global table satisfying the entry condition exists. -/
theorem gzopen_write_initialization_witness :
    ∃ statics, ZlibF.Spec.Public.LibraryGlobals (openWriteWitnessHeap statics) ∧
      gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) ({} : Fs)
        (openWriteWitnessHeap statics) =
        .ok ((some (.in_gzstate_x 2), openWriteWitnessFs), openWriteWitnessAfter statics) ∧
      ZlibF.Spec.Public.OpenState (openWriteWitnessAfter statics) 2 openWriteWitnessState
        .write (-1) 0 0 3 [112] := by
  let statics := Zlib.Crc32.initStatics
    (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static))
  have hg : ZlibF.Spec.Public.LibraryGlobals (openWriteWitnessHeap statics) := rfl
  exact ⟨statics, hg, gzopen_write_witness_run statics,
    gzopen_write_success_OpenState statics hg⟩

#print axioms gz_open_empty_mode
#print axioms gz_open_plus_mode
#print axioms openReleased_frame
#print axioms gz_open_write_path_alloc_failure
#print axioms gzopen_write_success_witness
#print axioms gzopen_write_success_OpenState
#print axioms gzopen_write_initialization_witness
end Zlib.Gzlib.Proofs
