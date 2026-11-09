import ZlibF.Proof.«inflate.c.local-default-state»
import ZlibF.Proof.«public-inflate-end»

/-! Actual end under local allocation uniqueness. Old caller typed collisions
are permitted. The ages of private roots are explicit representation facts. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

private theorem cnt_zero {α : Type} {o : Option α} (zero : cnt o = 0) : o = none := by
  cases o <;> simp_all

theorem UniqueFrom.bytes_only {h : Heap} {first b : Nat} (unique : UniqueFrom h first)
    (lower : first ≤ b) {a : Array UInt8} (get : h.bytes b = some a) :
    h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧
    h.dstates b = none ∧ h.istates b = none ∧ h.gzstates b = none := by
  have bound := unique b lower
  simp only [get, cnt_some] at bound
  exact ⟨cnt_zero (by omega), cnt_zero (by omega), cnt_zero (by omega),
    cnt_zero (by omega), cnt_zero (by omega), cnt_zero (by omega)⟩

theorem UniqueFrom.istates_only {h : Heap} {first b : Nat} (unique : UniqueFrom h first)
    (lower : first ≤ b) {s : InflateState} (get : h.istates b = some s) :
    h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧
    h.dstates b = none ∧ h.bytes b = none ∧ h.gzstates b = none := by
  have bound := unique b lower
  simp only [get, cnt_some] at bound
  exact ⟨cnt_zero (by omega), cnt_zero (by omega), cnt_zero (by omega),
    cnt_zero (by omega), cnt_zero (by omega), cnt_zero (by omega)⟩

theorem UniqueFrom.freeWin {h : Heap} {first : Nat} (unique : UniqueFrom h first) (p : BPtr) :
    UniqueFrom (freeWin h p) first := by
  intro b lower
  have bound := unique b lower
  unfold Zlib.Inflate.Spec.freeWin
  split
  · rename_i w
    by_cases same : b = w
    · subst b
      simp only [upd_same, cnt_none]
      omega
    · simpa [upd_ne _ _ _ _ same] using bound
  · exact bound

theorem UniqueFrom.freeIst {h : Heap} {first : Nat} (unique : UniqueFrom h first) (zs : Nat) :
    UniqueFrom (freeIst h zs) first := by
  intro b lower
  have bound := unique b lower
  by_cases same : b = zs
  · subst b
    simp only [Zlib.Inflate.Spec.freeIst, upd_same, cnt_none]
    omega
  · simpa [Zlib.Inflate.Spec.freeIst, upd_ne _ _ _ _ same] using bound

/-- The real function execution needs Live and a valid window, without any
uniqueness requirement on caller storage. -/
theorem inflateEnd_live_run {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (live : Live h r zs z s) (window : WinInv h s) (free : z.zfree = .fn "zcfree") :
    C.run (inflateEnd (some r)) h =
      .ok (Z_OK, r.put (endHeap h zs s) { z with state := none }) := by
  have hz := live.hz
  have hs := live.hs
  unfold C.run inflateEnd
  rcases windowBlock window with null | ⟨w, a, pointer, bytes, ro⟩
  · isimp [stateCheck_live live, live.zst, hz, hs, null,
      zfrees_run hz free hs, endHeap, freeWin_null]
  · have hz2 : r.get (freeWin h (.ref (.blk w) 0)) = some z := by simpa using hz
    have hs2 : (freeWin h (.ref (.blk w) 0)).istates zs = some s := by simpa using hs
    have heap : endHeap h zs s = freeIst (freeWin h (.ref (.blk w) 0)) zs := by
      simp [endHeap, pointer]
    rw [heap]
    isimp [stateCheck_live live, live.zst, hz, hs, pointer,
      zfreeB_run hz free (Or.inr ⟨w, a, rfl, bytes, ro⟩), zfrees_run hz2 free hs2]

private theorem free_window_live {h : Heap} {first : Nat} {s : InflateState}
    (unique : UniqueFrom h first) (window : WinInv h s)
    (age : ∀ w, s.window = .ref (.blk w) 0 → first ≤ w) (b : Nat) :
    (freeWin h s.window).live b ↔ h.live b ∧ ¬ WinBlk s b := by
  rcases windowBlock window with null | ⟨w, a, pointer, bytes, _⟩
  · simp [null, freeWin_null, WinBlk]
  · obtain ⟨e1,e2,e3,e4,e5,e6⟩ := unique.bytes_only (age w pointer) bytes
    by_cases same : b = w
    · subst b
      simp [pointer, freeWin, Heap.live, WinBlk, e1,e2,e3,e4,e5,e6]
    · simp [pointer, freeWin, Heap.live, WinBlk, same, Ne.symm same]

private theorem free_state_live {h : Heap} {first zs : Nat} {s : InflateState}
    (unique : UniqueFrom h first) (age : first ≤ zs) (state : h.istates zs = some s) (b : Nat) :
    (freeIst h zs).live b ↔ h.live b ∧ b ≠ zs := by
  by_cases same : b = zs
  · subst b
    obtain ⟨e1,e2,e3,e4,e5,e6⟩ := unique.istates_only age state
    simp [freeIst, Heap.live, e1,e2,e3,e4,e5,e6]
  · simp [freeIst, Heap.live, same]

/-- Exact actual cleanup and allocation ledger. Only the decoder's private
root slots need unique types. Nothing is allocated and old caller collisions
are allowed. Root age comes from initialization and subsequent fresh windows. -/
theorem inflateEnd_local {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h first r zs z s)
    (roots : LocalRoots first r zs s) (free : z.zfree = .fn "zcfree") :
    ∃ after, C.run (inflateEnd (some r)) h = .ok (Z_OK, after) ∧
      after = r.put (endHeap h zs s) { z with state := none } ∧
      Fresh after ∧ UniqueFrom after first ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (InflateOwned zs s) ∧
      Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) ∧
      after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc := by
  let after := r.put (endHeap h zs s) { z with state := none }
  have get : r.get (endHeap h zs s) = some z := by simp [endHeap, good.live.hz]
  have shape := shape_put get { z with state := none }
  refine ⟨after, inflateEnd_live_run good.live good.inv.win free, rfl, ?_, ?_,
    by simpa [after] using ZStreamRef.get_put_same get { z with state := none }, ?_,
    InflateEndProof.end_frame good.live.hz (windowBlock good.inv.win), ?_, ?_⟩
  · exact shape.fresh (by simp [endHeap])
      (fresh_freeIst (fresh_freeWin good.fresh _) _)
  · have result : UniqueFrom (r.put (endHeap h zs s) { z with state := none }) first := by
      intro b lower
      obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := shape b
      have bound : UniqueFrom (endHeap h zs s) first :=
        (good.unique.freeWin s.window).freeIst zs
      have atBlock := bound b lower
      simpa only [cnt, e0,e1,e2,e3,e4,e5,e6] using atBlock
    exact result
  · intro b
    have state : (freeWin h s.window).istates zs = some s := by simpa using good.live.hs
    have stateLive := free_state_live (good.unique.freeWin s.window) roots.state state b
    have windowLive := free_window_live good.unique good.inv.win roots.window b
    have putLive := shape.live b
    change after.live b ↔ _
    rw [putLive, show endHeap h zs s = freeIst (freeWin h s.window) zs from rfl,
      stateLive, windowLive]
    simp only [InflateOwned, WinBlk, not_or, or_false]
    constructor
    · rintro ⟨⟨live, window⟩, state⟩
      exact ⟨live, state, window⟩
    · rintro ⟨live, state, window⟩
      exact ⟨⟨live, window⟩, state⟩
  · simp only [after, ZStreamRef.put_nextBlk, endHeap, freeIst_nextBlk, freeWin_nextBlk]
  · simp only [after, ZStreamRef.put_nalloc, endHeap, freeIst]
    unfold freeWin
    split <;> rfl

/-- Every live caller object older than the private allocation boundary keeps
all seven typed table entries and its read-only flag after the actual cleanup. -/
theorem end_old_caller_slots {h : Heap} {first : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h first r zs z s)
    (roots : LocalRoots first r zs s) (b : Nat) (old : b < first) (live : h.live b) :
    let after := r.put (endHeap h zs s) { z with state := none }
    after.bytes b = h.bytes b ∧ after.words b = h.words b ∧
    after.streams b = h.streams b ∧ after.gzheaders b = h.gzheaders b ∧
    after.dstates b = h.dstates b ∧ after.istates b = h.istates b ∧
    after.gzstates b = h.gzstates b ∧ after.ro b = h.ro b := by
  apply (InflateEndProof.end_frame good.live.hz (windowBlock good.inv.win)).2.2.2.2.2 b live
  rintro (stream | state | window)
  · have lower := roots.stream b stream
    omega
  · subst b
    have lower := roots.state
    omega
  · have lower := roots.window b window
    omega

#print axioms end_old_caller_slots
#print axioms inflateEnd_live_run
#print axioms inflateEnd_local
end Zlib.Inflate.Local
