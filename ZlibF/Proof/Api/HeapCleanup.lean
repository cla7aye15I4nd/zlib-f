import ZlibF.Spec.Public.GzControl
import ZlibF.Spec.Functional.Api.Compress
namespace ZlibF.Spec.Public.Proofs
open C Zlib.GzFs Zlib.Gzlib

def messageState : GzState := { (default : GzState) with mode := GZ_READ, path := .ref (.blk 0) 0, msg := .ref (.blk 1) 0, want := 8, err := Z_OK }
def messageHeap : Heap := { Heap.empty with
  bytes := ⟨#[some #[0], some #[0]]⟩,
  gzstates := ⟨#[none, none, some messageState]⟩,
  nextBlk := 3,
  static := Zlib.Crc32.initStatics (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

theorem messageHeap_valid : GzValid messageHeap 2 messageState := by
  unfold GzValid
  refine ⟨rfl, Or.inl rfl, ?_, ?_, rfl, ?_, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · intro b hb
    change 3 ≤ b at hb
    have hbytes : (#[some #[0], some #[0]] : Array (Option (Array UInt8)))[b]? = none :=
      Array.getElem?_eq_none (by simp; omega)
    have hstates : (#[none, none, some messageState] : Array (Option GzState))[b]? = none :=
      Array.getElem?_eq_none (by simp; omega)
    simp [Heap.live, messageHeap, Heap.empty, Tbl.get, Tbl.empty, hbytes, hstates] <;> decide
  · intro b
    by_cases h0 : b = 0
    · subst b; decide
    by_cases h1 : b = 1
    · subst b; decide
    by_cases h2 : b = 2
    · subst b; decide
    have hb : 3 ≤ b := by omega
    have hbytes : (#[some #[0], some #[0]] : Array (Option (Array UInt8)))[b]? = none :=
      Array.getElem?_eq_none (by simp; omega)
    have hstates : (#[none, none, some messageState] : Array (Option GzState))[b]? = none :=
      Array.getElem?_eq_none (by simp; omega)
    simp [Zlib.Gzlib.Spec.cnt, messageHeap, Heap.empty, Tbl.get, Tbl.empty, hbytes, hstates] <;> decide
  · refine ⟨[], ?_, 0, #[0], rfl, rfl, rfl, by decide⟩
    exact ⟨Or.inr ⟨.blk 0, 0, #[0], rfl, rfl, by decide, rfl⟩, by simp, by decide⟩
  · right
    refine ⟨[], ?_, 1, #[0], rfl, rfl, rfl, by decide⟩
    exact ⟨Or.inr ⟨.blk 1, 0, #[0], rfl, rfl, by decide, rfl⟩, by simp, by decide⟩
  · intro he; cases he
  · intro he; exact (he rfl).elim
  · intro he; exact (he rfl).elim


def clearedMessageHeap : Heap :=
  putGz { messageHeap with bytes := upd messageHeap.bytes 1 none } 2
    { messageState with eof := 0, past := 0, err := Z_OK, msg := .null }

theorem clear_message_witness : C.run (gzclearerr (some (.in_gzstate_x 2))) messageHeap = .ok ((), clearedMessageHeap) := by
  rfl


/-- The source allocator's free operation removes only bytes. It does not resize or clear
the read-only table. This covers the byte-block effect shared by reset and message cleanup. -/
theorem free_writable_matches_dropWindow (h : Heap) (p : BPtr) (valid : WindowAllocation h p) :
    C.run (freeB p) h = .ok ((), dropWindow h p) := by
  rcases valid with rfl | ⟨b, bytes, rfl, hb, hr⟩
  · rfl
  · simp [C.run, freeB, dropWindow, hb, hr]

/-- Freeze the former mistaken update solely to retain the counterexample. -/
def legacyDropWindow (h : Heap) : BPtr → Heap
  | .ref (.blk b) 0 => { h with bytes := upd h.bytes b none, ro := upd h.ro b false }
  | _ => h

/-- The corrected contract agrees with the actual function on a valid public-domain heap. -/
theorem clear_message_matches_contract :
    C.run (gzclearerr (some (.in_gzstate_x 2))) messageHeap =
      .ok ((), putGz (dropWindow messageHeap messageState.msg) 2
        { messageState with eof := 0, past := 0, err := Z_OK, msg := .null }) := by
  rfl

/-- The legacy whole-heap equality fails although all public-domain preconditions hold. -/
theorem clear_message_rejects_legacy_update :
    C.run (gzclearerr (some (.in_gzstate_x 2))) messageHeap ≠
      .ok ((), putGz (legacyDropWindow messageHeap messageState.msg) 2
        { messageState with eof := 0, past := 0, err := Z_OK, msg := .null }) := by
  intro he
  rw [clear_message_witness] at he
  have hh := congrArg (fun p : Unit × Heap => p.2) (Except.ok.inj he)
  have sizes := congrArg (fun h : Heap => h.ro.arr.size) hh
  change 0 = 2 at sizes
  omega

end ZlibF.Spec.Public.Proofs
