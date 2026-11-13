import ZlibF.Proof.«inflate.c.completes-keep-run»
import ZlibF.Proof.«inflate.c.completes-interface»

/-!
# inflate.c: the three per-call decoder facts

`MemErrorAllocates`, `InflateKeepsObjectSize` and `CallKeepsControl` are proved,
with `call_keeps_havedict` (a call keeps `havedict`),
from `call_inflate`, a theorem about every successful run of the translated
`inflate` (`inflate.c.completes-keep-run`). No representation invariant is
needed for the run itself; `Good` only names the decoder record and gives
`Fresh`.
-/

namespace Zlib.Inflate.Proofs
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.KeepProofs
set_option autoImplicit false

/-- `InflateKeepsObjectSize`: a call keeps every byte object below `2^63` bytes. -/
theorem inflate_keeps_object_size : InflateKeepsObjectSize := by
  intro h r i z s flush rc after _ _ fit _ _ run
  have k := call_inflate (some r) flush h rc after run
  intro ref a g
  cases ref with
  | str j =>
    by_cases lt : j < strTable.size
    · rw [C.LibcBorrow.source_view after j lt] at g
      exact fit (.str j) a (by rw [C.LibcBorrow.source_view h j lt]; exact g)
    · have := C.LibcBorrow.external_view_size (Nat.le_of_not_lt lt) g
      unfold ZlibF.PlatformMemory.byteObjectLimit
      omega
  | _ =>
    rcases k.sizes _ (fun _ e => by cases e) a g with ⟨a0, g0, e0⟩ | sm
    · rw [e0]; exact fit _ a0 g0
    · unfold ZlibF.PlatformMemory.byteObjectLimit
      unfold small at sm
      omega

/-- `CallKeepsControl`. -/
theorem call_keeps_control : CallKeepsControl := by
  intro h r i z s flush rc after z' s' _ good run good'
  have k := call_inflate (some r) flush h rc after run
  obtain ⟨s0, g0, c⟩ := k.states i s' good'.live.hs
  rw [good.live.hs] at g0
  cases g0
  refine ⟨c.sync, ?_, c.head, ?_, ?_⟩
  · intro m
    rcases c.mem m with m0 | ⟨r0, _⟩
    · exact Or.inr m0
    · exact Or.inl r0
  · rintro b (e | w)
    · exact Or.inl e
    · right
      rw [c.win (by rw [w]; intro n; cases n)]
      exact w
  · rintro b (e | w)
    · exact Or.inl (Or.inl e)
    · rcases c.fresh with same | ⟨v, wv, le⟩
      · exact Or.inl (Or.inr (same ▸ w))
      · right
        rw [wv] at w
        cases w
        exact good.fresh b le

/-- `MemErrorAllocates`. -/
theorem mem_error_allocates : MemErrorAllocates := by
  intro h r i z s flush after z' s' good notMem run good' mem
  have k := call_inflate (some r) flush h Z_MEM_ERROR after run
  obtain ⟨s0, g0, c⟩ := k.states i s' good'.live.hs
  rw [good.live.hs] at g0
  cases g0
  rcases c.mem mem with m0 | ⟨_, f⟩
  · exact absurd m0 notMem
  · exact f

/-- A call never writes `havedict`: only `inflateResetKeep` and
`inflateSetDictionary` do. -/
theorem call_keeps_havedict {h after : Heap} {r : ZStreamRef} {i : Nat} {z z' : ZStream}
    {s s' : InflateState} {flush rc : Int32} (good : Zlib.Inflate.Spec.Good h r i z s)
    (run : C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after))
    (good' : Zlib.Inflate.Spec.Good after r i z' s') : s'.havedict = s.havedict := by
  have k := call_inflate (some r) flush h rc after run
  obtain ⟨s0, g0, c⟩ := k.states i s' good'.live.hs
  rw [good.live.hs] at g0
  cases g0
  exact c.dict

#print axioms call_keeps_havedict
#print axioms inflate_keeps_object_size
#print axioms call_keeps_control
#print axioms mem_error_allocates
end Zlib.Inflate.Proofs
