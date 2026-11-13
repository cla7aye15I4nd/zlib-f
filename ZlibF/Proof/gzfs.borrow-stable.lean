import ZlibF.Proof.«gzfs.borrowed-error»
import ZlibF.Proof.LibcBorrowPrimitives

namespace C.LibcBorrow
open Zlib.GzFs

theorem StableM.ub {α : Type} (what : String) : StableM (C.ub what : M α) := by
  intro h value after hr
  cases hr

theorem StableM.ite {α : Type} (p : Prop) [Decidable p] {a b : M α}
    (ha : StableM a) (hb : StableM b) : StableM (if p then a else b) := by
  split <;> assumption

theorem stable_ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : StableM (p.add k) := by
  intro h value after hr
  unfold Ptr.add at hr
  split at hr
  · split at hr
    · cases hr; rfl
    · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem stable_ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : StableM (Ptr.load p : M T) := by
  intro h value after hr
  unfold Ptr.load at hr
  split at hr
  · contradiction
  · split at hr
    · contradiction
    · split at hr
      · cases hr; rfl
      · contradiction

theorem stable_index8 (p : BPtr) (i : Int) : StableM (index8 p i) := by
  unfold index8 Ptr.index
  exact StableM.bind (stable_ptr_add _ _) (fun _ => stable_ptr_load _)

/-- The actual string reader copies bytes into a local value and never
advances or invalidates the external borrow while reading it. -/
theorem stable_cstring (p : BPtr) : StableM (cstring p) := by
  unfold cstring
  apply StableM.bind (stable_strlenB p)
  intro n
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply StableM.bind
  · apply StableM.list_forIn
    intro value _ current
    apply StableM.bind (stable_index8 _ _)
    intro byte
    exact StableM.pure _
  · intro result
    exact StableM.pure _

/-- The formatter only observes strings. The raw model expression returns its
input heap on all successful format results, independent of formatting content. -/
theorem stable_formatBytes (f : Array UInt8) (args : List VaArg) : StableM (formatBytes f args) := by
  intro h value after hr
  unfold formatBytes at hr
  split at hr
  · cases hr; rfl
  · contradiction

/-- The actual temporary block, destination copy, and temporary free retain
borrow metadata. No ownership exemption for the temporary is used. -/
theorem stable_storeBytes (p : BPtr) (bs : Array UInt8) : StableM (storeBytes p bs) := by
  unfold storeBytes
  apply StableM.ite
  · exact StableM.pure _
  · apply StableM.bind (stable_allocBytes _)
    intro tmp
    apply StableM.bind (stable_memcpyB _ _ _)
    intro _
    exact stable_freeB _

/-- The actual formatter's complete returning execution keeps the borrowed
text live until its synchronous copy finishes, including its byte store. -/
theorem stable_snprintf (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) :
    StableM (snprintf dst size fmt args) := by
  unfold snprintf
  apply StableM.bind (stable_cstring _)
  intro f
  apply StableM.bind (stable_formatBytes _ _)
  intro out
  dsimp only
  apply StableM.ite
  · apply StableM.bind (stable_storeBytes _ _)
    intro _
    apply StableM.bind (stable_ptr_add _ _)
    intro q
    apply StableM.bind (stable_store8 _ _)
    intro _
    exact StableM.pure _
  · exact StableM.pure _

#print axioms stable_cstring
#print axioms stable_formatBytes
#print axioms stable_storeBytes
#print axioms stable_snprintf
end C.LibcBorrow
