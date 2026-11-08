import ZlibF.Proof.«inffast.c.input-frame»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast
set_option autoImplicit false

/-- Match copying retains the two source goto-control flags. -/
def decodeControls (l : L) : Bool × Bool := (l.againD, l.againL)

theorem pull_decode_controls (l : L) :
    ValuePost (pull l) (fun result => decodeControls result = decodeControls l) := by
  unfold pull
  apply valuePost_bind_any; intro byte
  apply valuePost_bind_any; intro next
  apply valuePost_bind_any; intro shifted
  exact valuePost_pure rfl

theorem copy1_decode_controls (l : L) :
    ValuePost (copy1 l) (fun result => decodeControls result = decodeControls l) := by
  unfold copy1
  apply valuePost_bind_any; intro byte
  apply valuePost_bind_any; intro fromPtr
  apply valuePost_bind_any; intro stored
  apply valuePost_bind_any; intro out
  exact valuePost_pure rfl

theorem copyOp_decode_controls (l : L) :
    ValuePost (copyOp l) (fun result => decodeControls result = decodeControls l) := by
  apply cdoWhile_preserves_view decodeControls copy1
    (fun current => let op := current.op - 1; pure (op != 0, { current with op }))
    copy1_decode_controls
  intro current
  exact valuePost_pure rfl

theorem copyThree_decode_controls (l : L) :
    ValuePost (do
      let a ← copy1 l
      let b ← copy1 a
      let d ← copy1 b
      pure { d with len := d.len - 3 })
      (fun result => decodeControls result = decodeControls l) := by
  apply valuePost_bind (α := L) (β := L) (post := fun result => decodeControls result = decodeControls l) (copy1_decode_controls l); intro a ha
  apply valuePost_bind (α := L) (β := L) (post := fun result => decodeControls result = decodeControls l) (copy1_decode_controls a); intro b hb
  apply valuePost_bind (α := L) (β := L) (post := fun result => decodeControls result = decodeControls l) (copy1_decode_controls b); intro d hd
  exact valuePost_pure (hd.trans (hb.trans ha))

theorem copyMatch_window_loop_decode_controls (l : L) :
    ValuePost (cwhile (fun q : L => pure (q.len > 2, q))
      (fun q => do
        let a ← copy1 q
        let b ← copy1 a
        let d ← copy1 b
        pure { d with len := d.len - 3 }) l)
      (fun result => decodeControls result = decodeControls l) := by
  apply cwhile_preserves_view decodeControls _ _ (fun _ => valuePost_pure rfl)
    copyThree_decode_controls

theorem copyMatch_direct_loop_decode_controls (l : L) :
    ValuePost (cdoWhile
      (fun q => do
        let a ← copy1 q
        let b ← copy1 a
        let d ← copy1 b
        pure { d with len := d.len - 3 })
      (fun q : L => pure (q.len > 2, q)) l)
      (fun result => decodeControls result = decodeControls l) := by
  apply cdoWhile_preserves_view decodeControls _ _ copyThree_decode_controls
    (fun _ => valuePost_pure rfl)

set_option maxHeartbeats 100000 in
theorem copyMatch_decode_controls (c : Ctx) (l : L) :
    ValuePost (copyMatch c l) (fun result => decodeControls result = decodeControls l) := by
  unfold copyMatch
  repeat' first
    | dsimp only
    | apply valuePost_pure (α := L) (post := fun result => decodeControls result = decodeControls l); simp_all [decodeControls]
    | apply valuePost_ite (α := L) (post := fun result => decodeControls result = decodeControls l)
    | apply valuePost_bind (α := L) (β := L) (post := fun result => decodeControls result = decodeControls l) (copy1_decode_controls _); intro next frame
    | apply valuePost_bind (α := L) (β := L) (post := fun result => decodeControls result = decodeControls l) (copyOp_decode_controls _); intro next frame
    | apply valuePost_bind (α := L) (β := L) (post := fun result => decodeControls result = decodeControls l) (copyMatch_window_loop_decode_controls _); intro next frame
    | apply valuePost_bind (α := L) (β := L) (post := fun result => decodeControls result = decodeControls l) (copyMatch_direct_loop_decode_controls _); intro next frame
    | apply valuePost_bind_any (β := L) (post := fun result => decodeControls result = decodeControls l); intro next

#print axioms copyMatch_decode_controls
end Zlib.Inffast.Proofs
