import ZlibF.Proof.«compress.c.shadow-init-checkpoint»
import ZlibF.Proof.«compress.c.shadow-byte-views»

/-! # Initialization on a concrete caller with three old kinds at one ID -/
namespace ZlibF.Spec.Public.Proofs.CompressShadow
open C Zlib.Deflate.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000

def collidingSeed : Heap :=
  let h := ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap
  {h with bytes := upd h.bytes 0 (some #[1]),words := upd h.words 0 (some #[2])}

theorem colliding_seed_fresh : Fresh collidingSeed := by
  intro b large live
  have ne : b ≠ 0 := by change 2 ≤ b at large;omega
  apply ZlibF.Spec.Public.Proofs.DeflateInit.witness_fresh b large
  simpa only [collidingSeed,Heap.live,upd_ne _ _ _ _ ne] using live

theorem colliding_seed_not_unique : ¬Uniq collidingSeed := by
  intro unique
  have impossible := unique 0
  simp [collidingSeed,ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap,Heap.empty,cnt] at impossible

/-- Both complete default initializers really return from a Fresh caller
outside the old global-Uniq domain. This is an initialization witness,
not a compression-loop witness. -/
theorem nonunique_initialization_checkpoint_witness :
    Fresh collidingSeed ∧ ¬Uniq collidingSeed ∧
      ∃ original shadow,SeedInitPair collidingSeed original shadow := by
  exact ⟨colliding_seed_fresh,colliding_seed_not_unique,
    successful_initialization_checkpoint colliding_seed_fresh rfl (by intro _ _;rfl)⟩

#print axioms nonunique_initialization_checkpoint_witness
end ZlibF.Spec.Public.Proofs.CompressShadow
