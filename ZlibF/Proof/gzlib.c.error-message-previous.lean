import ZlibF.Proof.«gzlib.c.error»
import ZlibF.Proof.«gzlib.c.error-message-refusal»
import ZlibF.Proof.«gzlib.c.error-message-copy»

/-! # Actual previous-message cleanup before an errno report

The public memory invariant supplies this minimal clearable-message condition.
Inactive input/output pointers are not required to be live. The real prefix
frees the old owned message, clears its pointer and sets the error. Replaying
the real handler from that same cleared heap is an exact source execution.
-/
namespace Zlib.Gzlib.MessagePrevious
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.Gzlib.MessageRefusal Zlib.Gzlib.MessageCopy

def ClearableMessage (h : Heap) (s : GzState) : Prop :=
  s.msg = .null ∨ ∃ b a, s.msg = .ref (.blk b) 0 ∧ h.bytes b = some a ∧
    h.ro b = false ∧ s.err ≠ Z_MEM_ERROR

def clearedMessageState (s : GzState) : GzState := { s with msg := .null, err := Z_ERRNO }
def clearedMessageHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  setS (freeStr h s.msg) i (clearedMessageState s)

/-- The existing public invariant is a producer, not an extra caller premise. -/
theorem clearable_of_valid {h : Heap} {i : Nat} {s : GzState} (hv : GzValid h i s) :
    ClearableMessage h s := by
  rcases hv with ⟨_,_,_,_,_,_,hmsg,hmem,_⟩
  rcases hmsg with hn | ⟨text, _, hm⟩
  · exact Or.inl hn
  · obtain ⟨b,a,hp,hb,hr,_⟩ := hm
    refine Or.inr ⟨b,a,hp,hb,hr,?_⟩
    intro he
    have hn := hmem he
    rw [hp] at hn
    cases hn

/-- The real NULL-message prefix includes freeing, not merely a record update. -/
theorem gz_error_clear_previous_run {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) :
    gz_error (some (.tab i)) Z_ERRNO .null h = .ok ((), clearedMessageHeap h i s) := by
  unfold gz_error
  rcases hc with hm | ⟨b,a,hm,hb,hr,he⟩
  · gsimp [hs, hm, clearedMessageHeap, clearedMessageState, setS, upd_upd]
  · have hfree := C.freeB_ok hb hr
    gsimp [hs, hm, he, hfree, clearedMessageHeap, clearedMessageState, freeStr, setS, upd_upd]

/-- Exact whole-function execution equivalence, after the actual successful
cleanup. The RHS is still the real handler, not an assumed tail contract. -/
theorem gz_error_from_cleared {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (msg : BPtr) :
    gz_error (some (.tab i)) Z_ERRNO msg h =
      gz_error (some (.tab i)) Z_ERRNO msg (clearedMessageHeap h i s) := by
  unfold gz_error
  rcases hc with hm | ⟨b,a,hm,hb,hr,he⟩
  · gsimp [hs, hm, clearedMessageHeap, clearedMessageState, setS, upd_upd]
  · have hfree := C.freeB_ok hb hr
    gsimp [hs, hm, he, hfree, clearedMessageHeap, clearedMessageState, freeStr, setS, upd_upd]

/-- The cleanup keeps the active borrowed text and both allocation counters. -/
theorem cleared_message_metadata (h : Heap) (i : Nat) (s : GzState) :
    (clearedMessageHeap h i s).libcErrorBorrow = h.libcErrorBorrow ∧
    (clearedMessageHeap h i s).nextBlk = h.nextBlk ∧
    (clearedMessageHeap h i s).nalloc = h.nalloc := by
  cases hp : s.msg with
  | null => simp [clearedMessageHeap, freeStr, setS, hp]
  | ref r off => cases r <;> simp [clearedMessageHeap, freeStr, setS, hp]

theorem cleared_message_fresh {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hf : Fresh h) :
    Fresh (clearedMessageHeap h i s) := by
  rcases hc with hm | ⟨b,a,hm,_,_,_⟩
  · simpa [clearedMessageHeap, hm] using Shape.fresh (shape_setS hs (clearedMessageState s)) rfl hf
  · have hsf : ({ h with bytes := upd h.bytes b none } : Heap).gzstates i = some s := hs
    have hf0 := Fresh.freeBytes hf b
    simpa [clearedMessageHeap, hm, freeStr] using
      Shape.fresh (shape_setS hsf (clearedMessageState s)) rfl hf0

/-- The exact old owned-message root is removed. No other object disappears. -/
theorem cleared_message_live {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hu : Zlib.Gzlib.Spec.Uniq h) :
    LiveChange h (clearedMessageHeap h i s) (fun _ => False)
      (fun b => s.msg = .ref (.blk b) 0) := by
  rcases hc with hm | ⟨b,a,hm,hb,_,_⟩
  · intro j
    simpa [clearedMessageHeap, hm] using Shape.live (shape_setS hs (clearedMessageState s)) j
  · intro j
    have hsf : ({ h with bytes := upd h.bytes b none } : Heap).gzstates i = some s := hs
    have hrecord := Shape.live (shape_setS hsf (clearedMessageState s)) j
    have hfree := live_freeBytes hu hb j
    simpa [clearedMessageHeap, hm, freeStr, eq_comm] using hrecord.trans hfree

/-- Original public gzip ownership covers the complete real cleanup footprint. -/
theorem cleared_message_owned_frame {h : Heap} {i : Nat} {s : GzState}
    (hc : ClearableMessage h s) : Frame h (clearedMessageHeap h i s) (GzOwned h i s) := by
  have hmeta : h.static = (clearedMessageHeap h i s).static ∧
      h.allocOk = (clearedMessageHeap h i s).allocOk ∧
      h.garbage = (clearedMessageHeap h i s).garbage ∧
      h.nextBlk = (clearedMessageHeap h i s).nextBlk ∧
      h.nalloc = (clearedMessageHeap h i s).nalloc := by
    cases hp : s.msg with
    | null => simp [clearedMessageHeap, freeStr, setS, hp]
    | ref r off => cases r <;> simp [clearedMessageHeap, freeStr, setS, hp]
  refine ⟨hmeta.1,hmeta.2.1,hmeta.2.2.1,
    Nat.le_of_eq hmeta.2.2.2.1,Nat.le_of_eq hmeta.2.2.2.2,?_⟩
  intro j hl ho
  have hi : j ≠ i := fun he => ho (Or.inl he)
  have hmroot : s.msg ≠ .ref (.blk j) 0 := fun he => ho (Or.inr (Or.inr (Or.inl he)))
  rcases hc with hm | ⟨b,a,hm,_,_,_⟩
  · simp [clearedMessageHeap, hm, setS, hi]
  · have hb : j ≠ b := by intro he; subst j; exact hmroot hm
    simp [clearedMessageHeap, hm, freeStr, setS, hi, hb]

/-- Resetting only err/msg keeps the embedded codec and its ownership. The
old message root is the only ownership clause removed from the state. -/
theorem cleared_owned_subset {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (j : Nat) :
    GzOwned (clearedMessageHeap h i s) i (clearedMessageState s) j → GzOwned h i s j := by
  have hstream : StreamOwned (clearedMessageHeap h i s) (.in_gzstate_strm i) j ↔
      StreamOwned h (.in_gzstate_strm i) j := by
    rcases hc with hm | ⟨b,a,hm,_,_,_⟩
    all_goals simp [StreamOwned, ZStreamRef.get, clearedMessageHeap, clearedMessageState,
      freeStr, setS, hm, hs]
  intro owned
  unfold GzOwned at owned ⊢
  rcases owned with hi | hp | hm | hbuf
  · exact Or.inl hi
  · exact Or.inr (Or.inl hp)
  · cases hm
  · refine Or.inr (Or.inr (Or.inr ?_))
    rcases hbuf with ⟨hsize, hin | ⟨hmode,hout | hstreamOwned⟩⟩
    · exact ⟨hsize, Or.inl hin⟩
    · exact ⟨hsize, Or.inr ⟨hmode, Or.inl hout⟩⟩
    · exact ⟨hsize, Or.inr ⟨hmode, Or.inr (hstream.1 hstreamOwned)⟩⟩

private theorem clear_oracle (h : Heap) (i : Nat) (s : GzState) (hc : ClearableMessage h s) :
    (clearedMessageHeap h i s).allocOk (clearedMessageHeap h i s).nalloc = h.allocOk h.nalloc := by
  rw [← (cleared_message_owned_frame hc).2.1, (cleared_message_metadata h i s).2.2]

/-- Actual full handler with previous-message cleanup and refused new malloc.
Strings are observed on the real post-cleanup heap, never as a callee contract. -/
theorem gz_error_replace_refusal_run {h : Heap} {i : Nat} {s : GzState} {msg : BPtr}
    {xs es : List UInt8} (hs : h.gzstates i = some s) (hc : ClearableMessage h s)
    (hp : CString (clearedMessageHeap h i s) s.path xs)
    (he : CString (clearedMessageHeap h i s) msg es) (ha : h.allocOk h.nalloc = false) :
    gz_error (some (.tab i)) Z_ERRNO msg h = .ok ((),
      refusedMessageHeap (clearedMessageHeap h i s) i (clearedMessageState s)) := by
  rw [gz_error_from_cleared hs hc msg]
  apply gz_error_errno_refusal_run
  · simp [clearedMessageHeap]
  · rfl
  · exact hp
  · exact he
  · rw [clear_oracle h i s hc]; exact ha

/-- Actual full handler with previous-message cleanup and successful new copy. -/
theorem gz_error_replace_copy_run {h : Heap} {i : Nat} {s : GzState} {msg : BPtr}
    {xs es : List UInt8} (hs : h.gzstates i = some s) (hc : ClearableMessage h s)
    (hp : CString (clearedMessageHeap h i s) s.path xs)
    (he : CString (clearedMessageHeap h i s) msg es) (hf : Fresh h)
    (ha : h.allocOk h.nalloc = true) (hmax : xs.length + es.length + 2 ≤ 2147483647) :
    gz_error (some (.tab i)) Z_ERRNO msg h = .ok ((),
      copiedMessageHeap (clearedMessageHeap h i s) i (clearedMessageState s) xs es) := by
  rw [gz_error_from_cleared hs hc msg]
  apply gz_error_errno_copy_run
  · simp [clearedMessageHeap]
  · rfl
  · exact hp
  · exact he
  · exact cleared_message_fresh hs hc hf
  · rw [clear_oracle h i s hc]; exact ha
  · exact hmax

/-- The complete refusal ledger removes exactly the old owned message root. -/
theorem replace_refusal_live {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hu : Zlib.Gzlib.Spec.Uniq h) :
    LiveChange h (refusedMessageHeap (clearedMessageHeap h i s) i (clearedMessageState s))
      (fun _ => False) (fun b => s.msg = .ref (.blk b) 0) := by
  have hstate : (clearedMessageHeap h i s).gzstates i = some (clearedMessageState s) := by
    simp [clearedMessageHeap]
  intro j
  have hl := refused_message_live (clearedMessageHeap h i s) i (clearedMessageState s) hstate j
  simp only [not_false_eq_true, and_true, or_false] at hl
  exact hl.trans (cleared_message_live hs hc hu j)

/-- Successful replacement frees the old root and creates only its new owned
copy. The borrowed external view is absent from both malloc identity sets. -/
theorem replace_copy_live {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hu : Zlib.Gzlib.Spec.Uniq h) (hf : Fresh h) :
    LiveChange h (copiedMessageHeap (clearedMessageHeap h i s) i (clearedMessageState s) xs es)
      (fun b => b = h.nextBlk) (fun b => s.msg = .ref (.blk b) 0) := by
  have hstate : (clearedMessageHeap h i s).gzstates i = some (clearedMessageState s) := by
    simp [clearedMessageHeap]
  intro j
  have hl := copied_message_live (xs := xs) (es := es) hstate (cleared_message_fresh hs hc hf) j
  simp only [not_false_eq_true, and_true] at hl
  rw [(cleared_message_metadata h i s).2.1] at hl
  rw [hl, cleared_message_live hs hc hu j]
  simp

private theorem cleared_frame_compose {h final : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hu : Zlib.Gzlib.Spec.Uniq h)
    (tailFrame : Frame (clearedMessageHeap h i s) final
      (GzOwned (clearedMessageHeap h i s) i (clearedMessageState s))) :
    Frame h final (GzOwned h i s) := by
  obtain ⟨a1,a2,a3,a4,a5,af⟩ := cleared_message_owned_frame hc
  obtain ⟨b1,b2,b3,b4,b5,bf⟩ := tailFrame
  refine ⟨a1.trans b1,a2.trans b2,a3.trans b3,Nat.le_trans a4 b4,Nat.le_trans a5 b5,?_⟩
  intro j hl ho
  have noOld : s.msg ≠ .ref (.blk j) 0 := fun hp => ho (Or.inr (Or.inr (Or.inl hp)))
  have hlClear : (clearedMessageHeap h i s).live j :=
    (cleared_message_live hs hc hu j).2 (Or.inl ⟨hl,noOld⟩)
  have noClear : ¬GzOwned (clearedMessageHeap h i s) i (clearedMessageState s) j :=
    fun owned => ho (cleared_owned_subset hs hc j owned)
  obtain ⟨x1,x2,x3,x4,x5,x6,x7,x8⟩ := af j hl ho
  obtain ⟨y1,y2,y3,y4,y5,y6,y7,y8⟩ := bf j hlClear noClear
  exact ⟨y1.trans x1,y2.trans x2,y3.trans x3,y4.trans x4,
    y5.trans x5,y6.trans x6,y7.trans x7,y8.trans x8⟩

theorem replace_refusal_owned_frame {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hu : Zlib.Gzlib.Spec.Uniq h) :
    Frame h (refusedMessageHeap (clearedMessageHeap h i s) i (clearedMessageState s)) (GzOwned h i s) := by
  exact cleared_frame_compose hs hc hu (refused_message_owned_frame _ _ _)

theorem replace_copy_owned_frame {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hc : ClearableMessage h s) (hu : Zlib.Gzlib.Spec.Uniq h) (hf : Fresh h) :
    Frame h (copiedMessageHeap (clearedMessageHeap h i s) i (clearedMessageState s) xs es) (GzOwned h i s) := by
  have hstate : (clearedMessageHeap h i s).gzstates i = some (clearedMessageState s) := by
    simp [clearedMessageHeap]
  exact cleared_frame_compose hs hc hu (copied_message_owned_frame hstate (cleared_message_fresh hs hc hf))

#print axioms gz_error_clear_previous_run
#print axioms gz_error_from_cleared
#print axioms cleared_message_fresh
#print axioms cleared_message_live
#print axioms cleared_message_owned_frame
#print axioms gz_error_replace_refusal_run
#print axioms gz_error_replace_copy_run
#print axioms replace_refusal_live
#print axioms replace_copy_live
#print axioms replace_refusal_owned_frame
#print axioms replace_copy_owned_frame
end Zlib.Gzlib.MessagePrevious
