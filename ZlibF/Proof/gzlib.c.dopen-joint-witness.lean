import ZlibF.Proof.«gzlib.c.dopen-complete»
import ZlibF.Proof.«gzlib.c.dopen-init»

/-!
# gzlib.c: a concrete joint-domain witness for the complete descriptor goal

The constant tables use the actual build initializers. All original caller
premises hold simultaneously, with no LibraryGlobals or other hypothesis.
The actual successful execution and every public postcondition use the same
concrete returned heap and file world.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- Exactly the library tables required by the original public caller domain. -/
def descriptorJointStatics : Statics :=
  Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static))

def descriptorJointHeap : Heap := openDirectWitnessHeap descriptorJointStatics

def descriptorJointAfter : Heap := dopenDirectWitnessAfter descriptorJointStatics

/-- Both caller byte allocations lie strictly below the actual next identity. -/
theorem descriptorJoint_fresh : Fresh descriptorJointHeap := by
  intro b hb hl
  have hb2 : 2 ≤ b := hb
  have hn : [some #[(112 : UInt8), 0], some #[119, 84, 0]][b]? = none :=
    List.getElem?_eq_none (by change 2 ≤ b; omega)
  simp [Heap.live, descriptorJointHeap, openDirectWitnessHeap, openWriteWitnessHeap,
    Heap.empty, Tbl.get, Tbl.empty, Array.getD_eq_getD_getElem?, default, hn] at hl

/-- Each caller identity occupies just its one byte-object table. -/
theorem descriptorJoint_uniq : Uniq descriptorJointHeap := by
  intro b
  have hc : b = 0 ∨ b = 1 ∨ 2 ≤ b := by omega
  rcases hc with rfl | rfl | hb
  all_goals simp (disch := omega) [descriptorJointHeap, openDirectWitnessHeap,
    openWriteWitnessHeap, Heap.empty, Tbl.get, Tbl.empty, cnt,
    Array.getD_eq_getD_getElem?, List.getElem?_eq_none, default]
  all_goals first | decide | split <;> omega

/-- The actual initialization expression supplies the public constant tables. -/
theorem descriptorJoint_globals : ZlibF.Spec.Public.LibraryGlobals descriptorJointHeap := rfl

/-- The concrete supplied descriptor refers to a real ordinary writable file.
Every original public file-world premise holds on this same world. -/
theorem descriptorJoint_filesystem : ZlibF.Spec.Public.FileSystem openWriteWitnessFs := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro path node hm
    simp [openWriteWitnessFs] at hm
    rcases hm with ⟨rfl, rfl⟩
    decide
  · intro i file hi
    have hr : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i := by omega
    rcases hr with rfl | rfl | rfl | rfl | hb
    · simp [openWriteWitnessFs] at hi
    · simp [openWriteWitnessFs] at hi
    · simp [openWriteWitnessFs] at hi
    · simp [openWriteWitnessFs] at hi
      subst file
      refine ⟨by decide, by decide, ?_⟩
      intro node hn
      simp [openWriteWitnessFs] at hn
      subst node
      simp
    · have hn : openWriteWitnessFs.fds[i]? = none :=
        Array.getElem?_eq_none (by change 4 ≤ i; exact hb)
      rw [hn] at hi
      contradiction
  · intro i node hi
    by_cases he : i = 0
    · subst i
      simp [openWriteWitnessFs] at hi
      subst node
      decide
    · have hb : 1 ≤ i := by omega
      have hn : openWriteWitnessFs.nodes[i]? = none :=
        Array.getElem?_eq_none (by change 1 ≤ i; exact hb)
      rw [hn] at hi
      contradiction

/-- The caller mode is a real allocated terminated string. -/
theorem descriptorJoint_mode :
    ZlibF.Spec.Public.CString descriptorJointHeap (.ref (.blk 1) 0) [119, 84] := by
  exact ⟨Or.inr ⟨.blk 1, 0, #[119, 84, 0], rfl, rfl, by decide, rfl⟩,
    by decide, by decide⟩

/-- No assumptions: every original Goal.gzdopen caller premise, the actual
successful function execution, and all its original public postconditions
hold together on this one concrete caller/result pair. -/
theorem gzdopen_joint_witness :
    Fresh descriptorJointHeap ∧ Uniq descriptorJointHeap ∧
    ZlibF.Spec.Public.LibraryGlobals descriptorJointHeap ∧
    ZlibF.Spec.Public.FileSystem openWriteWitnessFs ∧
    0 ≤ (3 : Int32).toInt ∧
    ZlibF.Spec.Public.CString descriptorJointHeap (.ref (.blk 1) 0) [119, 84] ∧
    ((.ref (.blk 1) 0 : BPtr) ≠ .null →
      ZlibF.Spec.Public.CString descriptorJointHeap (.ref (.blk 1) 0) [119, 84]) ∧
    gzdopen 3 (.ref (.blk 1) 0) openWriteWitnessFs descriptorJointHeap =
      .ok ((some (.in_gzstate_x 4), openWriteWitnessFs), descriptorJointAfter) ∧
    ZlibF.Spec.Public.Frame descriptorJointHeap descriptorJointAfter (fun _ => False) ∧
    ∃ s mode level strategy direct,
      ZlibF.Spec.Public.parsedMode [119, 84] = some (mode, level, strategy, direct) ∧
      ZlibF.Spec.Public.OpenState descriptorJointAfter 4 s mode level strategy direct 3
        (String.toUTF8 ("<fd:" ++ toString (3 : Int32).toInt ++ ">")).toList ∧
      ZlibF.Spec.Public.OpenWorld descriptorJointHeap openWriteWitnessFs openWriteWitnessFs []
        [119, 84] mode (some 3) 3 s.start ∧
      ZlibF.Spec.Public.LiveChange descriptorJointHeap descriptorJointAfter
        (ZlibF.Spec.Public.GzOwned descriptorJointAfter 4 s) (fun _ => False) := by
  have hc : (.ref (.blk 1) 0 : BPtr) ≠ .null →
      ZlibF.Spec.Public.CString descriptorJointHeap (.ref (.blk 1) 0) [119, 84] :=
    fun _ => descriptorJoint_mode
  have hrun : gzdopen 3 (.ref (.blk 1) 0) openWriteWitnessFs descriptorJointHeap =
      .ok ((some (.in_gzstate_x 4), openWriteWitnessFs), descriptorJointAfter) :=
    gzdopen_direct_witness_run descriptorJointStatics
  obtain ⟨file, fs', after, hresult, hframe, hpost⟩ := gzdopen_complete.2
    descriptorJointHeap openWriteWitnessFs 3 (.ref (.blk 1) 0) [119, 84]
    descriptorJoint_fresh descriptorJoint_uniq descriptorJoint_globals descriptorJoint_filesystem
    (by decide) hc
  rw [hrun] at hresult
  cases hresult
  exact ⟨descriptorJoint_fresh, descriptorJoint_uniq, descriptorJoint_globals,
    descriptorJoint_filesystem, by decide, descriptorJoint_mode, hc, hrun, hframe, hpost⟩

#print axioms descriptorJoint_fresh
#print axioms descriptorJoint_uniq
#print axioms descriptorJoint_globals
#print axioms descriptorJoint_filesystem
#print axioms descriptorJoint_mode
#print axioms gzdopen_joint_witness
end Zlib.Gzlib.Proofs
