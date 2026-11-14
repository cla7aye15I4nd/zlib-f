import ZlibF.Proof.«infback.c.safety-call»
import ZlibF.Proof.«public-infback-init»
import ZlibF.Proof.«public-infback-end»

/-!
# infback.c: the histories of the callback decoder

The steps of a `BackSafeReachable` history: `reach_init` (initialisation) and `reach_caller` (a
caller's edit) keep a valid state over the caller's window, and `back_reach_window` shows that the
window is a slice of a heap byte block. `back_null` is clause 1 of
`Goal.inflate_back_sequence_safety`. The goal is composed in `infback.c.safety-fast`.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
set_option autoImplicit false

/-- The window of every history is a slice of a heap byte block. -/
theorem back_reach_window {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (reach : BackSafeReachable h r i window n) : ∃ w off, window = .ref (.blk w) off := by
  induction reach with
  | init _ _ _ _ _ blk _ => exact blk
  | caller _ _ _ _ ih => exact ih
  | step _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- `inflateBackInit_` leaves a valid state over the window. -/
theorem reach_init {h after : Heap} {r : ZStreamRef} {version : BPtr} {wb : Int32} {window : BPtr}
    (hd : InitDomain h r version) (lo : 8 ≤ wb.toInt) (hi : wb.toInt ≤ 15)
    (wr : Writable h window (2 ^ wb.toInt.toNat)) (nn : window ≠ .null)
    (run : C.run (Zlib.Infback.inflateBackInit_ (some r) wb window version 112) h = .ok (Z_OK, after)) :
    ∃ z s, BackValid after r h.nextBlk z s ∧ s.window = window ∧ s.wsize.toNat = 2 ^ wb.toInt.toNat ∧
      (s.sane ≠ 0 ∧ s.wnext = 0) := by
  obtain ⟨hf, hu, hg, hv, z, hz, hdz, -⟩ := hd
  obtain ⟨rc, after', hrun, -, hs⟩ :=
    ZlibF.Spec.Public.InflateBackInitProof.back_init_public.2.2 h r z wb window version hf hu hg hz hdz hv lo hi nn wr
  rw [run] at hrun
  simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  split at hs
  · exact absurd hs.1 (by decide)
  · obtain ⟨-, valid, -, -⟩ := hs
    refine ⟨_, _, valid, rfl, ?_, ⟨by simp [backInitialState], rfl⟩⟩
    show ((1 : UInt32) <<< wb.toUInt32).toNat = 2 ^ wb.toInt.toNat
    have hwb : wb.toUInt32.toNat = wb.toInt.toNat := by
      rw [Int32.toNat_toUInt32_of_le]
      · rfl
      · rw [Int32.le_iff_toInt_le]
        simp only [Int32.toInt_zero]
        omega
    rw [Zlib.Infback.Proofs.shl32_one (by rw [hwb]; omega), hwb]

/-- A caller's edit between calls keeps a valid state over the window. -/
theorem reach_caller {h after : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {z : ZStream}
    {s : InflateState} (valid : BackValid h r i z s) (win : s.window = window) (size : s.wsize.toNat = n)
    (rebuf : Rebuffer h after r) (same : SameBytePrefix h after window window n)
    (ro : ∀ b, h.live b → after.live b → after.ro b = h.ro b) :
    ∃ z' , BackValid after r i z' s := by
  obtain ⟨fresh', uniq', glob', frame, z0, z', hz0, hz', eq⟩ := rebuf
  obtain ⟨hz, hs, zst, za, zf, wf, lo, hi, ws, nn, wr, -, -, -⟩ := valid
  have e : z0 = z := Option.some.inj (hz0.symm.trans hz)
  subst e
  have owned : StreamOwned h r i := ⟨z0, hz0, Or.inl ⟨i, s, zst, hs, Or.inl rfl⟩⟩
  have hs' : after.istates i = some s := istates_frame frame hs (fun x => x owned)
  have st' : z'.state = z0.state := by rw [eq]
  have za' : z'.zalloc = z0.zalloc := by rw [eq]
  have zf' : z'.zfree = z0.zfree := by rw [eq]
  refine ⟨z', hz', hs', by rw [st']; exact zst, by rw [za']; exact za, by rw [zf']; exact zf, wf, lo, hi, ws, nn,
    ?_, fresh', uniq', glob'⟩
  rw [win, size]
  rw [win, size] at wr
  obtain ⟨xs, -, bytesA⟩ := same
  rcases bytesA with ⟨null, -, -⟩ | ⟨ref, off, a, ptr, get, room, -⟩
  · rw [win] at nn; exact absurd null nn
  · rcases wr with ⟨null, -⟩ | ⟨ref0, off0, a0, ptr0, get0, ro0, -⟩
    · rw [win] at nn; exact absurd null nn
    · rw [ptr] at ptr0
      injection ptr0 with e1 e2
      subst e1 e2
      refine Or.inr ⟨ref, off, a, ptr, get, ?_, room⟩
      cases ref with
      | blk b =>
        change after.ro b = false
        change h.ro b = false at ro0
        have liveB : h.live b := Or.inl (by change h.bytes b = some a0 at get0; rw [get0]; simp)
        have liveB' : after.live b := Or.inl (by change after.bytes b = some a at get; rw [get]; simp)
        rw [ro b liveB liveB']
        exact ro0
      | _ => exact ro0

/-- A null stream is refused. -/
theorem back_null : ∀ h input inDesc output outDesc,
    C.run (Zlib.Infback.inflateBack none input inDesc output outDesc) h = .ok (Z_STREAM_ERROR, h) :=
  fun h input inDesc output outDesc => inflateBack_nullstream input inDesc output outDesc h

end Zlib.Infback.Safety
