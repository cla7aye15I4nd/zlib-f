import ZlibF.Proof.«gzfs.error-message-store»
import ZlibF.Proof.«gzlib.c.base»
import ZlibF.Spec.Public.GzState
import ZlibF.Spec.Functional.Api.Compress

/-! # Actual successful owned error-message production

The initial message is NULL. Both input strings are admitted original CString
views. The formatter's existing successful-output INT_MAX domain is explicit;
it is not a new public caller restriction. Actual malloc, formatting, copied
bytes, terminating NUL and temporary cleanup use one execution and heap.
-/
namespace Zlib.Gzlib.MessageCopy
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs
open ZlibF.Spec.Public Zlib.GzFs.MessageStore

def messageLength (xs es : List UInt8) : Nat := xs.length + es.length + 3
def messageChars (xs es : List UInt8) : Array UInt8 := (xs ++ [58,32] ++ es).toArray

def messageGarbage (h : Heap) (xs es : List UInt8) : Array UInt8 :=
  Array.ofFn (n := messageLength xs es) fun i => Junk.of (h.garbage h.nalloc i.val)

def preMessageHeap (h : Heap) (i : Nat) (s : GzState) : Heap :=
  setS h i { s with err := Z_ERRNO }

def mallocMessageHeap (h : Heap) (i : Nat) (s : GzState) (xs es : List UInt8) : Heap :=
  { preMessageHeap h i s with
    bytes := upd h.bytes h.nextBlk (some (messageGarbage h xs es))
    ro := upd h.ro h.nextBlk false
    nextBlk := h.nextBlk + 1
    nalloc := h.nalloc + 1 }

def copiedMessageState (h : Heap) (s : GzState) : GzState :=
  { s with err := Z_ERRNO, msg := .ref (.blk h.nextBlk) 0 }

def messageReadyHeap (h : Heap) (i : Nat) (s : GzState) (xs es : List UInt8) : Heap :=
  setS (mallocMessageHeap h i s xs es) i (copiedMessageState h s)

def copiedMessageHeap (h : Heap) (i : Nat) (s : GzState) (xs es : List UInt8) : Heap :=
  storedMessageHeap (messageReadyHeap h i s xs es) h.nextBlk
    (messageGarbage h xs es) (messageChars xs es)

private theorem CString_with_views {h after : Heap} {p : BPtr} {xs : List UInt8}
    (hc : CString h p xs)
    (views : ∀ (r : BRef) (a : Array UInt8), Space.get h r = some a → Space.get after r = some a) :
    CString after p xs := by
  refine ⟨?_, hc.2⟩
  rcases hc.1 with hn | ⟨r, off, a, hp, ha, hf, he⟩
  · exact Or.inl hn
  · exact Or.inr ⟨r, off, a, hp, views r a ha, hf, he⟩

private theorem view_preMessage (h : Heap) (i : Nat) (s : GzState) (r : BRef) :
    Space.get (preMessageHeap h i s) r = Space.get h r := by
  cases r <;> rfl

private theorem ready_preserves_view {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hf : Fresh h) (r : BRef) (a : Array UInt8) (ha : Space.get h r = some a) :
    Space.get (messageReadyHeap h i s xs es) r = some a := by
  cases r with
  | blk b =>
    have hne : b ≠ h.nextBlk := by
      intro he
      subst b
      have hl : h.live h.nextBlk := Or.inl (by rw [show h.bytes h.nextBlk = some a from ha]; intro hn; cases hn)
      exact hf h.nextBlk (Nat.le_refl _) hl
    simpa [messageReadyHeap, mallocMessageHeap, preMessageHeap, setS, hne] using ha
  | str j => exact ha
  | dstate_depth j => exact ha
  | st_dist_code => exact ha
  | st_length_code => exact ha

/-- Freshness of the actual message malloc also supplies its formatter's
separate scratch allocation; both fresh identities are below the final cursor. -/
theorem ready_fresh {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) : Fresh (messageReadyHeap h i s xs es) := by
  have hi : i < h.nextBlk := by
    by_cases ht : i < h.nextBlk
    · exact ht
    · exact False.elim (hf i (by omega) (by simp [Heap.live, hs]))
  intro j hj hl
  have hjn : j ≠ h.nextBlk := by change h.nextBlk + 1 ≤ j at hj; omega
  have hji : j ≠ i := by change h.nextBlk + 1 ≤ j at hj; omega
  apply hf j (by change h.nextBlk + 1 ≤ j at hj; omega)
  simpa [Heap.live, messageReadyHeap, mallocMessageHeap, preMessageHeap, setS, hjn, hji] using hl

private theorem cstring_nonnull {h : Heap} {p : BPtr} {xs : List UInt8} (hc : CString h p xs) : p ≠ .null := by
  intro hp
  rcases hc.1 with hn | ⟨r, off, a, he, _⟩
  · have := hn.2.1; omega
  · rw [hp] at he; cases he

/-- Whole actual gz_error successful message allocation and formatting. No
callee specification is assumed; the real formatter theorem supplies its run. -/
theorem gz_error_errno_copy_run {h : Heap} {i : Nat} {s : GzState} {msg : BPtr}
    {xs es : List UInt8} (hs : h.gzstates i = some s) (hm : s.msg = .null)
    (hp : CString h s.path xs) (he : CString h msg es) (hf : Fresh h)
    (ha : h.allocOk h.nalloc = true) (hmax : xs.length + es.length + 2 ≤ 2147483647) :
    gz_error (some (.tab i)) Z_ERRNO msg h = .ok ((), copiedMessageHeap h i s xs es) := by
  have hpPre : CString (preMessageHeap h i s) s.path xs :=
    CString_with_views hp (fun r a hv => (view_preMessage h i s r).trans hv)
  have hePre : CString (preMessageHeap h i s) msg es :=
    CString_with_views he (fun r a hv => (view_preMessage h i s r).trans hv)
  have hpLen := Zlib.GzFs.Proofs.strlenB_of_CString hpPre
  have heLen := Zlib.GzFs.Proofs.strlenB_of_CString hePre
  have hpReady : CString (messageReadyHeap h i s xs es) s.path xs :=
    CString_with_views hp (ready_preserves_view hf)
  have heReady : CString (messageReadyHeap h i s xs es) msg es :=
    CString_with_views he (ready_preserves_view hf)
  have hpLenReady := Zlib.GzFs.Proofs.strlenB_of_CString hpReady
  have heLenReady := Zlib.GzFs.Proofs.strlenB_of_CString heReady
  have hsum : UInt64.ofNat xs.length + UInt64.ofNat es.length + 3 = UInt64.ofNat (messageLength xs es) := by
    apply UInt64.toNat_inj.1
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    unfold messageLength
    rw [show (3 : UInt64).toNat = 3 by decide]
    omega
  have hnum : (UInt64.ofNat (messageLength xs es)).toNat = messageLength xs es :=
    UInt64.toNat_ofNat_of_lt' (by change xs.length + es.length + 3 < 2^64; omega)
  have hfPre : Fresh (preMessageHeap h i s) := Shape.fresh (shape_setS hs _) rfl hf
  have hmalloc : allocB (messageLength xs es) (preMessageHeap h i s) =
      .ok (.ref (.blk h.nextBlk) 0, mallocMessageHeap h i s xs es) := by
    exact allocB_some _ ha (by unfold messageLength C.mallocLimit; omega) (Fresh.slotUsed_next hfPre)
  have hready : (messageReadyHeap h i s xs es).gzstates i = some (copiedMessageState h s) := by
    simp [messageReadyHeap]
  have hprint := snprintf_error_copy_run hpReady heReady
    (show (messageReadyHeap h i s xs es).bytes h.nextBlk = some (messageGarbage h xs es) by
      simp [messageReadyHeap, mallocMessageHeap, setS])
    (show (messageReadyHeap h i s xs es).ro h.nextBlk = false by
      simp [messageReadyHeap, mallocMessageHeap, setS])
    (show (messageGarbage h xs es).size = xs.length + es.length + 3 by simp [messageGarbage, messageLength])
    hmax (Fresh.slotUsed_next (ready_fresh hs hf))
  have hxs : xs.length % 2^64 = xs.length := Nat.mod_eq_of_lt (by omega)
  have hes : es.length % 2^64 = es.length := Nat.mod_eq_of_lt (by omega)
  have hlenmod : (xs.length + es.length + 3) % 2^64 = messageLength xs es := by
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  simp only [preMessageHeap, messageReadyHeap, mallocMessageHeap, copiedMessageState,
    setS, upd_upd, hm, Z_ERRNO] at hpLen heLen hpLenReady heLenReady hmalloc hprint
  have hn := cstring_nonnull he
  unfold gz_error
  simp [bind_app, ldS_eq, updS_eq, hs, hm, hn, hpLen, heLen, hpLenReady, heLenReady,
    hsum, hnum, hxs, hes, hlenmod, hmalloc, hready, error_format_literal, error_separator_literal,
    hprint, copiedMessageHeap, messageChars, copiedMessageState, preMessageHeap,
    mallocMessageHeap, messageReadyHeap, Z_ERRNO, Z_MEM_ERROR, setS, upd_upd]
  dsimp only [messageLength]
  rw [hprint]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Actual message malloc preserves every original live allocation. Only its
new message root is created; the existing gzip record remains the same object. -/
theorem ready_message_live {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    LiveChange h (messageReadyHeap h i s xs es) (fun b => b = h.nextBlk) (fun _ => False) := by
  intro j
  by_cases ht : j = h.nextBlk
  · subst j
    simp [Heap.live, messageReadyHeap, mallocMessageHeap, preMessageHeap, setS]
  · by_cases hi : j = i
    · subst j
      simp [Heap.live, messageReadyHeap, mallocMessageHeap, preMessageHeap, setS, hs]
    · simp [Heap.live, messageReadyHeap, mallocMessageHeap, preMessageHeap, setS, ht, hi]

theorem ready_message_frame {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hf : Fresh h) : Frame h (messageReadyHeap h i s xs es) (fun b => b = i) := by
  refine ⟨rfl, rfl, rfl, by change h.nextBlk ≤ h.nextBlk + 1; omega,
    by change h.nalloc ≤ h.nalloc + 1; omega, ?_⟩
  intro j hl hi
  have ht : j ≠ h.nextBlk := by
    intro heq
    subst j
    exact hf h.nextBlk (Nat.le_refl _) hl
  simp [messageReadyHeap, mallocMessageHeap, preMessageHeap, setS, ht, hi]

/-- The real final byte array is path, colon-space, error text, then NUL.
Its temporary has gone, both counters are exact, and the external borrow stays
metadata independent of these owned bytes. -/
theorem copied_message_observations {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    (copiedMessageHeap h i s xs es).gzstates i = some (copiedMessageState h s) ∧
    (copiedMessageHeap h i s xs es).bytes h.nextBlk = some ((messageChars xs es).push 0) ∧
    (copiedMessageHeap h i s xs es).bytes (h.nextBlk + 1) = none ∧
    (copiedMessageHeap h i s xs es).nextBlk = h.nextBlk + 2 ∧
    (copiedMessageHeap h i s xs es).nalloc = h.nalloc + 1 ∧
    (copiedMessageHeap h i s xs es).libcErrorBorrow = h.libcErrorBorrow := by
  have hb : (messageReadyHeap h i s xs es).bytes h.nextBlk = some (messageGarbage h xs es) := by
    simp [messageReadyHeap, mallocMessageHeap, setS]
  have observed := stored_message_observations (out := messageChars xs es) hb (Fresh.slotUsed_next (ready_fresh hs hf))
  refine ⟨?_, observed.1, observed.2.1, ?_, observed.2.2.2.1, observed.2.2.2.2⟩
  · change (messageReadyHeap h i s xs es).gzstates i = some (copiedMessageState h s)
    simp [messageReadyHeap]
  · simpa [copiedMessageHeap, messageReadyHeap, mallocMessageHeap, preMessageHeap, setS, Nat.add_assoc] using observed.2.2.1

/-- The only net new live object is this very message block. It is owned by
this same returned gzip state; no external text or formatter temporary leaks. -/
theorem copied_message_live {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    LiveChange h (copiedMessageHeap h i s xs es) (fun b => b = h.nextBlk) (fun _ => False) := by
  have hb : (messageReadyHeap h i s xs es).bytes h.nextBlk = some (messageGarbage h xs es) := by
    simp [messageReadyHeap, mallocMessageHeap, setS]
  have hstore := stored_message_live (out := messageChars xs es) hb (Fresh.slotUsed_next (ready_fresh hs hf))
  intro j
  have hc : (copiedMessageHeap h i s xs es).live j ↔ (messageReadyHeap h i s xs es).live j := by
    simpa [LiveChange, copiedMessageHeap] using hstore j
  exact hc.trans (ready_message_live hs hf j)

/-- Compose two proved actual frames. The message destination and scratch
identity were not original caller objects, so the original gzip footprint
suffices without exempting readonly external storage. -/
theorem copied_message_owned_frame {h : Heap} {i : Nat} {s : GzState} {xs es : List UInt8}
    (hs : h.gzstates i = some s) (hf : Fresh h) :
    Frame h (copiedMessageHeap h i s xs es) (GzOwned h i s) := by
  have hb : (messageReadyHeap h i s xs es).bytes h.nextBlk = some (messageGarbage h xs es) := by
    simp [messageReadyHeap, mallocMessageHeap, setS]
  obtain ⟨pstatic, poracle, pgarbage, pnext, pcount, pobj⟩ := ready_message_frame (i := i) (s := s) (xs := xs) (es := es) hf
  obtain ⟨sstatic, soracle, sgarbage, snext, scount, sobj⟩ :=
    stored_message_frame (b := h.nextBlk) (a := messageGarbage h xs es) (out := messageChars xs es)
      (Fresh.slotUsed_next (ready_fresh hs hf))
  refine ⟨pstatic.trans sstatic, poracle.trans soracle, pgarbage.trans sgarbage,
    Nat.le_trans pnext snext, Nat.le_trans pcount scount, ?_⟩
  intro j hl ho
  have hi : j ≠ i := fun heq => ho (Or.inl heq)
  have ht : j ≠ h.nextBlk := by
    intro heq
    subst j
    exact hf h.nextBlk (Nat.le_refl _) hl
  have hlready : (messageReadyHeap h i s xs es).live j :=
    (ready_message_live hs hf j).2 (Or.inl ⟨hl, fun impossible => impossible⟩)
  obtain ⟨b1,w1,z1,g1,d1,i1,s1,r1⟩ := pobj j hl hi
  obtain ⟨b2,w2,z2,g2,d2,i2,s2,r2⟩ := sobj j hlready ht
  exact ⟨b2.trans b1,w2.trans w1,z2.trans z1,g2.trans g1,
    d2.trans d1,i2.trans i1,s2.trans s1,r2.trans r1⟩

theorem copied_message_is_owned (h : Heap) (i : Nat) (s : GzState) (xs es : List UInt8) :
    GzOwned (copiedMessageHeap h i s xs es) i (copiedMessageState h s) h.nextBlk :=
  Or.inr (Or.inr (Or.inl rfl))

#print axioms gz_error_errno_copy_run
#print axioms ready_fresh
#print axioms copied_message_observations
#print axioms copied_message_live
#print axioms copied_message_owned_frame
end Zlib.Gzlib.MessageCopy
