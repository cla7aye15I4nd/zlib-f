import ZlibF.Proof.«inflate.c.head-gzip-state»
import ZlibF.Proof.«inflate.c.default-view-dispatch-rank»

/-!
# inflate.c: what one gzip header dispatch can return

Observers of single dispatches (return codes, normal modes, dictionary
requests) use these two facts for `HEAD` with gzip allowed and for the
gzip header modes: the dispatch returns normally or leaves, and the
decoder lands in a known set of modes.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem gzip_head_dispatch_observe {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = HEAD) (gzip : GzipAllowed s.wrap)
    (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    (returned.mode = HEAD ∨ returned.mode = FLAGS ∨ returned.mode = BAD ∨ returned.mode = TYPE ∨
      returned.mode = DICTID) ∧ (outcome = .error Ex.leave ∨ outcome = .ok ()) := by
  obtain ⟨outcome2, regs2, after2, stream2, state2, _, _, run2, final, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, modes, _, _, _, progress⟩ :=
    inflate_dispatch_HEAD_gzip_state_rank E invariant buffers mode gzip
      (local_ (by rw [mode]; decide) (by rw [mode]; decide)) incoming
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  have stateEq : state2 = returned := Option.some.inj (final.good.live.hs.symm.trans get)
  subst returned
  refine ⟨modes, ?_⟩
  rcases progress with leave | ⟨normal, _⟩
  · exact Or.inl leave
  · exact Or.inr normal

theorem gzip_header_dispatch_observe {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (header : GzipHeaderMode s)
    (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some returned) :
    ((FLAGS ≤ returned.mode ∧ returned.mode ≤ HCRC) ∨ returned.mode = TYPE ∨ returned.mode = BAD) ∧
      (outcome = .error Ex.leave ∨ outcome = .ok ()) := by
  have low : HEAD ≤ s.mode := by
    have flagsLow := header.1
    rw [UInt32.le_iff_toNat_le] at flagsLow ⊢
    change 16181 ≤ s.mode.toNat at flagsLow
    change 16180 ≤ s.mode.toNat
    omega
  obtain ⟨outcome2, regs2, after2, stream2, state2, _, _, run2, final, _, _, _, _, _, _, _, _, _, _, _, _, _,
    modes, _, _, progress⟩ :=
    inflate_dispatch_gzip_header_state_rank E invariant buffers header (local_ low header.2.1) incoming
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  have stateEq : state2 = returned := Option.some.inj (final.good.live.hs.symm.trans get)
  subst returned
  refine ⟨modes, ?_⟩
  rcases progress with leave | ⟨normal, _⟩
  · exact Or.inl leave
  · exact Or.inr normal


/-- A gzip `HEAD` or header-mode dispatch never returns a code directly. -/
theorem gzip_dispatch_outcome {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {bs : List UInt8} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (gzipPhase : (s.mode = HEAD ∧ GzipAllowed s.wrap) ∨ GzipHeaderMode s)
    (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    outcome = .error Ex.leave ∨ outcome = .ok () := by
  obtain ⟨_, _, _, _, state, _, _, _, run2, final, _, _, _, _, _, _, _, _⟩ :=
    inflate_dispatch_default_view_state_rank E invariant buffers local_ incoming
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  rcases gzipPhase with ⟨mode, gzip⟩ | header
  · exact (gzip_head_dispatch_observe E invariant buffers mode gzip local_ incoming run final.good.live.hs).2
  · exact (gzip_header_dispatch_observe E invariant buffers header local_ incoming run final.good.live.hs).2

end Zlib.Inflate.Proofs
