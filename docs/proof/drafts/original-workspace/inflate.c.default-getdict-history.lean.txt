import ZlibF.Proof.«inflate.c.default-byte-view»
import ZlibF.Proof.«inflate.c.public-getdict»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A caller range cannot target the decoder's owned window, even at a
disjoint offset in the same byte allocation. -/
theorem callerRange_getdict_window_distinct {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {dest : BRef} {off n : Nat} {w : Nat}
    (good : Good h r zs z s) (range : CallerRange h r (.ref dest off) n true)
    (window : s.window = .ref (.blk w) 0) : dest ≠ .blk w := by
  rcases range with impossible | ⟨_, _, unowned⟩
  · cases impossible
  intro same
  subst dest
  have root : ByteRoot (.ref (.blk w) off) w := by simp [ByteRoot]
  have owned : StreamOwned h r w := (good.streamOwned_iff w).mpr (Or.inr window)
  exact unowned w root owned

/-- The actual dictionary query writes only the caller's permitted byte
range and retains the complete default decoder relation. -/
theorem inflateGetDictionary_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (dest : BPtr) (dl : Option UInt32)
    (range : CallerRange h r dest s.whave.toNat true) :
    ∃ value after, C.run (inflateGetDictionary (some r) dest dl) h = .ok (value, after) ∧
      DefaultStateJ after r zs z s := by
  by_cases null : dest = .null
  · subst dest
    refine ⟨(Z_OK, dl.map (fun _ => s.whave)), h, ?_, invariant⟩
    unfold C.run inflateGetDictionary
    simp [stateCheck_live invariant.good.live, ldZ_eq, ldI_eq,
      invariant.good.live.hz, invariant.good.live.zst, castI, invariant.good.live.hs]
    cases dl <;> rfl
  by_cases empty : s.whave = 0
  · refine ⟨(Z_OK, dl.map (fun _ => s.whave)), h, ?_, invariant⟩
    unfold C.run inflateGetDictionary
    simp [stateCheck_live invariant.good.live, ldZ_eq, ldI_eq,
      invariant.good.live.hz, invariant.good.live.zst, castI, invariant.good.live.hs,
      empty]
    cases dl <;> rfl
  obtain ⟨w, a, window, windowGet, _, _⟩ :
      ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
        h.ro w = false ∧ a.size = 2 ^ s.wbits.toNat := by
    rcases invariant.good.inv.win.block with windowNull | windowBlock
    · have zero := invariant.good.inv.win.nullws windowNull
      have bound := invariant.good.inv.win.hv
      rw [zero] at bound
      simp at bound
      have : s.whave = 0 := UInt32.toNat_inj.mp (by simpa using bound)
      exact False.elim (empty this)
    · exact windowBlock
  cases dest with
  | null => exact False.elim (null rfl)
  | ref destRef off =>
    have writable : Writable h (.ref destRef off) s.whave.toNat := by
      rcases range with impossible | ⟨_, writable, _⟩
      · cases impossible
      · exact writable rfl
    rcases writable with impossible | ⟨rd, od, D, pointer, get, write, fit⟩
    · cases impossible.1
    cases pointer
    have distinct := callerRange_getdict_window_distinct invariant.good range window
    have nextBound : s.wnext.toNat ≤ s.whave.toNat := by
      rcases Nat.lt_or_ge s.whave.toNat s.wsize.toNat with less | full
      · have := invariant.good.inv.win.eq less; omega
      · have := invariant.good.inv.win.wn
        have := invariant.good.inv.win.hv
        omega
    have haveBound : s.whave.toNat ≤ a.size := by
      have := invariant.good.inv.win.hv
      have := invariant.good.inv.win.ws
      omega
    have run := inflateGetDictionary_copy_general (dl := dl) invariant.good.live
      window windowGet get write distinct empty nextBound haveBound fit
    let array := getDictBytes D a off s.wnext.toNat s.whave.toNat
    have size : array.size = D.size := by simp [array, getDictBytes, size_copyRange]
    have separate : ∀ w', s.window = .ref (.blk w') 0 → destRef ≠ .blk w' := by
      intro w' pointer
      have same : w' = w := by rw [window] at pointer; cases pointer; rfl
      subst w'
      exact distinct
    have current := invariant.byte_view_put get write separate array size
    exact ⟨(Z_OK, dl.map (fun _ => s.whave)), Space.put h destRef array,
      by simpa [C.run, array] using run, current⟩

/-- Public dictionary-read arguments establish the writable caller range.
The translated call preserves J and extends the actual stream history. -/
theorem inflateGetDictionary_default_history {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (reachable : StreamReachable .inflate h r)
    (invariant : DefaultStateJ h r zs z s) (dest : BPtr) (dl : Option UInt32)
    (arguments : StreamArguments h r (.inflateGetDictionary (some r) dest dl)) :
    ∃ value after, C.run (inflateGetDictionary (some r) dest dl) h = .ok (value, after) ∧
      DefaultStateJ after r zs z s ∧ StreamReachable .inflate after r := by
  have admissible := arguments
  obtain ⟨z0, zs0, s0, hz0, zst0, hs0, range⟩ := arguments
  have sameStream : z0 = z := Option.some.inj (hz0.symm.trans invariant.good.live.hz)
  subst z0
  have sameStateId : zs0 = zs := by
    have equal := zst0.symm.trans invariant.good.live.zst
    cases equal
    rfl
  subst zs0
  have sameState : s0 = s := Option.some.inj (hs0.symm.trans invariant.good.live.hs)
  subst s0
  obtain ⟨value, after, run, current⟩ :=
    inflateGetDictionary_default_state invariant dest dl range
  have executed : (Call.inflateGetDictionary (some r) dest dl).execute default h =
      .ok ((value, default), after) := by
    change inflateGetDictionary (some r) dest dl h = _ at run
    simp only [Call.execute, heapCall, run]
  have operation : StreamOperation .inflate r (.inflateGetDictionary (some r) dest dl) := by
    simp [StreamOperation]
  exact ⟨value, after, run, current,
    StreamReachable.step reachable operation admissible executed⟩

end Zlib.Inflate.Proofs
