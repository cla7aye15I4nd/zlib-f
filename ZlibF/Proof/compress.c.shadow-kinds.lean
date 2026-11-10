import ZlibF.Proof.«compress.c.caller»

/-! # A kind-separated heap for the actual automatic-stream seed

This construction is restricted to the initialization seed. Old records
retain their original values, including pointers that initialization does
not read. It is not a simulation of arbitrary future caller operations.
-/
namespace ZlibF.Spec.Public.Proofs.CompressShadow
open C Zlib.Deflate.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000

def spread {α : Type} [Inhabited α] (table : Tbl α) (cut tag : Nat) : Tbl α :=
  ⟨Array.ofFn (n := 7*cut) fun i => if i.val%7 = tag then table (i.val/7) else default⟩

theorem spread_get {α : Type} [Inhabited α] (table : Tbl α) (cut tag x : Nat) :
    spread table cut tag x =
      if x < 7*cut ∧ x%7 = tag then table (x/7) else default := by
  by_cases small : x < 7*cut <;>
    simp [spread,Tbl.get,Array.getD_eq_getD_getElem?,small]

theorem spread_option_get {α : Type} (table : Tbl (Option α)) (cut tag x : Nat) :
    spread table cut tag x =
      if x < 7*cut ∧ x%7 = tag then table (x/7) else none := spread_get table cut tag x

theorem spread_at {α : Type} [Inhabited α] (table : Tbl α) {cut b tag : Nat}
    (old : b < cut) (kind : tag < 7) : spread table cut tag (7*b+tag) = table b := by
  rw [spread_get]
  have small : 7*b+tag < 7*cut := by omega
  have rem : (7*b+tag)%7 = tag := by omega
  have quo : (7*b+tag)/7 = b := by omega
  simp only [small,rem,and_self,ite_true,quo]

def rename (cut tag b : Nat) : Nat := if b < cut then 7*b+tag else b+6*cut

def seedShadow (h : Heap) : Heap :=
  {h with
    bytes := spread h.bytes h.nextBlk 0
    words := spread h.words h.nextBlk 1
    streams := spread h.streams h.nextBlk 2
    gzheaders := spread h.gzheaders h.nextBlk 3
    dstates := spread h.dstates h.nextBlk 4
    istates := spread h.istates h.nextBlk 5
    gzstates := spread h.gzstates h.nextBlk 6
    ro := spread h.ro h.nextBlk 0
    nextBlk := 7*h.nextBlk
    byteBase := fun ref => match ref with
      | .dstate_depth b =>
        h.byteBase (.dstate_depth (if b < 7*h.nextBlk then b/7 else b-6*h.nextBlk))
      | other => h.byteBase other }

theorem seed_fresh (h : Heap) : Fresh (seedShadow h) := by
  intro b large live
  have outside : ¬ b < 7*h.nextBlk := by change 7*h.nextBlk ≤ b at large;omega
  simpa [seedShadow,Heap.live,spread_option_get,outside] using live

theorem seed_unique (h : Heap) : Uniq (seedShadow h) := by
  intro b
  have rem : b%7 < 7 := Nat.mod_lt _ (by decide)
  have count {α : Type} (value : Option α) : cnt value ≤ 1 := by cases value <;> simp [cnt]
  have cases : b%7 = 0 ∨ b%7 = 1 ∨ b%7 = 2 ∨ b%7 = 3 ∨ b%7 = 4 ∨ b%7 = 5 ∨ b%7 = 6 := by omega
  by_cases small : b < 7*h.nextBlk
  · rcases cases with r | r | r | r | r | r | r
    · simpa [seedShadow,spread_option_get,r,small] using count (h.bytes (b/7))
    · simpa [seedShadow,spread_option_get,r,small] using count (h.words (b/7))
    · simpa [seedShadow,spread_option_get,r,small] using count (h.streams (b/7))
    · simpa [seedShadow,spread_option_get,r,small] using count (h.gzheaders (b/7))
    · simpa [seedShadow,spread_option_get,r,small] using count (h.dstates (b/7))
    · simpa [seedShadow,spread_option_get,r,small] using count (h.istates (b/7))
    · simpa [seedShadow,spread_option_get,r,small] using count (h.gzstates (b/7))
  · simp [seedShadow,spread_option_get,small]

theorem seed_globals {h : Heap} (globals : LibraryGlobals h) : LibraryGlobals (seedShadow h) := globals

/-- Every old typed byte block remains byte-for-byte accessible at its
byte-kind identifier. This does not claim a single global live-ID map. -/
theorem seed_old_bytes {h : Heap} {b : Nat} {a : Array UInt8}
    (fresh : Fresh h) (get : h.bytes b = some a) :
    (seedShadow h).bytes (rename h.nextBlk 0 b) = some a ∧
      (seedShadow h).ro (rename h.nextBlk 0 b) = h.ro b := by
  have old : b < h.nextBlk := fresh.lt (Or.inl (by rw [get];simp))
  simp only [seedShadow,rename,old,ite_true]
  exact ⟨(spread_at h.bytes old (by decide)).trans get,spread_at h.ro old (by decide)⟩

theorem automatic_shadow_domain {h : Heap} (globals : LibraryGlobals h) :
    InitDomain (CompressCaller.localHeap (seedShadow h)) (.tab (7*h.nextBlk)) (.ref (.str 57) 0) := by
  exact CompressCaller.automatic_stream_domain (seedShadow h) (seed_fresh h)
    (by simpa only [Zlib.Inflate.Spec.Uniq,Zlib.Inflate.Spec.cnt,Uniq,cnt] using seed_unique h)
    (seed_globals globals)

#print axioms seed_unique
#print axioms automatic_shadow_domain
end ZlibF.Spec.Public.Proofs.CompressShadow
