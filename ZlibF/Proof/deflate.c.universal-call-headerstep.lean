import ZlibF.Proof.«deflate.c.universal-call-headerphase»
import ZlibF.Proof.«deflate.c.universal-call-headerentry»
import ZlibF.Proof.«deflate.c.universal-call-stageframe»

/-!
# deflate.c: the header phase of one call, at the invariant level

Owner 2 of the deflate split (`deflate_call`). From a header state (`INIT_STATE` to `HCRC_STATE`)
with the invariant, batch C's `header_phase` either returns `Z_OK` or continues in `BUSY_STATE`
with nothing pending. Here `DInv`, `HeaderInv` and `CallFacts` are carried to its result with
`DInv.lift_empty` (a header state records no symbol).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The header states. -/
def Writing (d : DeflateState) : Prop :=
  d.status = INIT_STATE ∨ d.status = GZIP_STATE ∨ d.status = EXTRA_STATE ∨ d.status = NAME_STATE ∨
    d.status = COMMENT_STATE ∨ d.status = HCRC_STATE

theorem Writing.not_finish {d : DeflateState} (w : Writing d) : d.status ≠ FINISH_STATE := by
  intro e
  rcases w with x | x | x | x | x | x <;> rw [e] at x <;> exact absurd x (by decide)

/-- What the header step concludes about its result. -/
def HeaderOut (h : Heap) (r : ZStreamRef) (ds pb : Nat) (z : ZStream) (d : DeflateState)
    (run : Except Fault (Int32 × Heap)) (k : M Int32) : Prop :=
  ∃ (after : Heap) (z' : ZStream) (d' : DeflateState) (produced : Nat),
    DInv after r ds z' d' ∧ HeaderInv d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
    StageFrame h after r ds pb d z z' produced ∧ (∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b) ∧
    z'.next_out ≠ .null ∧ d'.lit_bufsize = d.lit_bufsize ∧
    ((run = .ok (Z_OK, after) ∧ d'.last_flush = -1 ∧ d'.pending ≠ 0 ∧
        CallFacts d' ∧ z'.avail_out = 0) ∨
     (run = k after ∧ d'.status = BUSY_STATE ∧ d'.pending = 0 ∧ d'.pending_out = d'.pending_buf ∧
        d'.last_flush = d.last_flush ∧ CallFacts d'))

/-- **The header phase keeps the invariant** from a header state. `lastFlush`: the entry phase has
stored the flush value, so `last_flush` is not the reset value. -/
theorem header_step {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (inv : DInv h r ds z d) (hinv : HeaderInv d)
    (trees : TreesInvAt h ds d pb buf) (pbuf : d.pending_buf = .ref (.blk pb) 0)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (out : z.next_out ≠ .null)
    (lastFlush : d.last_flush ≠ -2) (writing : Writing d) (entry : HeaderEntry h z d ds pb buf)
    (flush : Int32) (k : M Int32) :
    HeaderOut h r ds pb z d (headerPhase (some r) (some (.tab ds)) flush k h) k := by
  have low : d.bi_valid.toInt < 8 := by have := inv.shape.biValid; omega
  have done := (header_phase inv.good trees buffers cursor low out inv.globals entry flush k).resolve_right
    (fun ⟨fin, _⟩ => writing.not_finish fin)
  obtain ⟨after, z', d', produced, good', _, buffers', acc, frame, low', _, shape, hinvf, out', branch⟩ := done
  obtain ⟨_, _, _, static, win, prv, hd, pres⟩ := StageFrame.call_facts frame inv.good buffers pbuf out
  have fields := HeaderShape.fields shape
  have own : ∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b := by
    obtain ⟨_, _, _, _, _, _, _, _, e⟩ := shape
    intro b; rw [e]; exact Iff.rfl
  have empty : d.sym_next = 0 := hinv.empty writing
  have hinv' := hinvf hinv
  have symEq : d'.sym_next = d.sym_next := HeaderShape.sym_next shape
  have wrapEq : d'.wrap = d.wrap := by
    obtain ⟨_, _, _, _, _, _, _, _, eq⟩ := shape
    rw [eq]
  have alloc : DefAlloc z' := by
    obtain ⟨za, zf⟩ := inv.alloc
    exact ⟨acc.2.2.2.2.2.2.2.1.trans za, acc.2.2.2.2.2.2.2.2.1.trans zf⟩
  have trailer : d'.wrap.toInt < 0 → d'.status = FINISH_STATE := by
    intro neg
    rw [wrapEq] at neg
    exact absurd (inv.shape.trailer neg) writing.not_finish
  have bits : d'.bi_valid.toInt ≤ 7 := by omega
  have litEq : d'.lit_bufsize = d.lit_bufsize := by
    have f := HeaderShape.fields shape; unfold HeaderFields at f; rw [f]
  have lfRange := inv.shape.lastFlush
  rcases branch with ⟨run, lf, pend, nf, full0⟩ | ⟨run, busy, pend, cur, lf⟩
  · have shape' : Shape d' := Shape.of_fields inv.shape fields
      ⟨by rw [lf]; decide, by rw [lf]; decide⟩ (fun _ => Or.inr lf) trailer bits (fun e => absurd e pend)
    have inv' := inv.lift_empty good' alloc static shape' fields empty win prv hd pres
    refine ⟨after, z', d', produced, inv', hinv', buffers', acc, frame, own, out', litEq, Or.inl ⟨run, lf, pend, ?_, full0⟩⟩
    exact { fresh := fun e => absurd (lf.symm.trans e) (by decide),
            freshStart := fun e => absurd (lf.symm.trans e) (by decide),
            finishSym := fun _ => symEq.trans empty,
            finishLook := fun e => absurd e nf,
            finishBits := fun e => absurd e nf }
  · have shape' : Shape d' := Shape.of_fields inv.shape fields
      (by rw [lf]; exact lfRange) (fun st => by rw [busy] at st; rcases st with e | e <;> exact absurd e (by decide))
      trailer bits (fun _ => cur)
    have inv' := inv.lift_empty good' alloc static shape' fields empty win prv hd pres
    refine ⟨after, z', d', produced, inv', hinv', buffers', acc, frame, own, out', litEq, Or.inr ⟨run, busy, pend, cur, lf, ?_⟩⟩
    exact { fresh := fun e => absurd (lf.symm.trans e) lastFlush,
            freshStart := fun e => absurd (lf.symm.trans e) lastFlush,
            finishSym := fun e => by rw [busy] at e; exact absurd e (by decide),
            finishLook := fun e => by rw [busy] at e; exact absurd e (by decide),
            finishBits := fun e => by rw [busy] at e; exact absurd e (by decide) }

/-- A record shape of the entry followed by the header stages' record shape. -/
theorem HeaderFields.then_shape {d0 d d' : DeflateState} (fields : HeaderFields d0 d) (shape : HeaderShape d d') :
    HeaderFields d0 d' := by
  obtain ⟨st, p, po, bb, bv, bu, gi, lf, e⟩ := shape
  subst e
  unfold HeaderFields at fields ⊢
  rw [fields]

/-- **The header phase from a mid-call state**: the invariant is lifted once, from the state
before the call (`inv0`), to the result of the header phase. Between them only header and flush
fields of the record changed (`fields0`), and the heap kept the static tables, the window, `prev`,
`head` and the `pending_buf` block. -/
theorem header_step_mid {h0 h : Heap} {r : ZStreamRef} {ds pb : Nat} {z0 z : ZStream} {d0 d : DeflateState}
    {buf : Array UInt8} (inv0 : DInv h0 r ds z0 d0) (hinv0 : HeaderInv d0)
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (pbuf : d.pending_buf = .ref (.blk pb) 0)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) (out : z.next_out ≠ .null)
    (alloc : DefAlloc z) (fields0 : HeaderFields d0 d) (status0 : d.status = d0.status) (wrap0 : d.wrap = d0.wrap)
    (static0 : h.static = h0.static)
    (win0 : ∀ w, d0.window = .ref (.blk w) 0 → h.bytes w = h0.bytes w)
    (prv0 : ∀ p, d0.prev = .ref (.blk p) 0 → h.words p = h0.words p)
    (hd0 : ∀ q, d0.head = .ref (.blk q) 0 → h.words q = h0.words q)
    (low : d.bi_valid.toInt < 8) (lfRange : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5)
    (lfNot : d.last_flush ≠ -2) (writing : Writing d) (entry : HeaderEntry h z d ds pb buf)
    (flush : Int32) (k : M Int32) :
    HeaderOut h r ds pb z d (headerPhase (some r) (some (.tab ds)) flush k h) k := by
  have globals : LibraryGlobals h := by
    have g := inv0.globals
    unfold LibraryGlobals at g ⊢
    rw [static0]; exact g
  have done := (header_phase good trees buffers cursor low out globals entry flush k).resolve_right
    (fun ⟨fin, _⟩ => writing.not_finish fin)
  obtain ⟨after, z', d', produced, good', _, buffers', acc, frame, low', _, shape, hinvf, out', branch⟩ := done
  obtain ⟨_, _, _, static, win, prv, hd, pres⟩ := StageFrame.call_facts frame good buffers pbuf out
  have fields : HeaderFields d0 d' := fields0.then_shape shape
  have own : ∀ b, DeflateOwned ds d' b ↔ DeflateOwned ds d b := by
    obtain ⟨_, _, _, _, _, _, _, _, e⟩ := shape
    intro b; rw [e]; exact Iff.rfl
  have writing0 : Writing d0 := by unfold Writing at *; rw [← status0]; exact writing
  have empty : d0.sym_next = 0 := hinv0.empty writing0
  have hinv' : HeaderInv d' := hinvf (HeaderInv.of_fields hinv0 fields0 status0)
  have symEq : d'.sym_next = d0.sym_next := by unfold HeaderFields at fields; rw [fields]
  have wrapEq : d'.wrap = d0.wrap := by
    have w1 : d'.wrap = d.wrap := by obtain ⟨_, _, _, _, _, _, _, _, eq⟩ := shape; rw [eq]
    exact w1.trans wrap0
  have alloc' : DefAlloc z' := by
    obtain ⟨za, zf⟩ := alloc
    exact ⟨acc.2.2.2.2.2.2.2.1.trans za, acc.2.2.2.2.2.2.2.2.1.trans zf⟩
  have keepW : ∀ w, d0.window = .ref (.blk w) 0 → after.bytes w = h0.bytes w := fun w e =>
    (win w (by unfold HeaderFields at fields0; rw [fields0]; exact e)).trans (win0 w e)
  have keepP : ∀ p, d0.prev = .ref (.blk p) 0 → after.words p = h0.words p := fun p e =>
    (prv p (by unfold HeaderFields at fields0; rw [fields0]; exact e)).trans (prv0 p e)
  have keepH : ∀ q, d0.head = .ref (.blk q) 0 → after.words q = h0.words q := fun q e =>
    (hd q (by unfold HeaderFields at fields0; rw [fields0]; exact e)).trans (hd0 q e)
  have keepB : ∀ b, d0.pending_buf = .ref (.blk b) 0 → ∃ a', after.bytes b = some a' := fun b e =>
    pres b (by unfold HeaderFields at fields0; rw [fields0]; exact e)
  have trailer : d'.wrap.toInt < 0 → d'.status = FINISH_STATE := by
    intro neg
    rw [wrapEq] at neg
    exact absurd (inv0.shape.trailer neg) writing0.not_finish
  have bits : d'.bi_valid.toInt ≤ 7 := by omega
  have litEq : d'.lit_bufsize = d.lit_bufsize := by
    have f := HeaderShape.fields shape; unfold HeaderFields at f; rw [f]
  rcases branch with ⟨run, lf, pend, nf, full0⟩ | ⟨run, busy, pend, cur, lf⟩
  · have shape' : Shape d' := Shape.of_fields inv0.shape fields
      ⟨by rw [lf]; decide, by rw [lf]; decide⟩ (fun _ => Or.inr lf) trailer bits (fun e => absurd e pend)
    have inv' := inv0.lift_empty good' alloc' (static.trans static0) shape' fields empty keepW keepP keepH keepB
    refine ⟨after, z', d', produced, inv', hinv', buffers', acc, frame, own, out', litEq, Or.inl ⟨run, lf, pend, ?_, full0⟩⟩
    exact { fresh := fun e => absurd (lf.symm.trans e) (by decide),
            freshStart := fun e => absurd (lf.symm.trans e) (by decide),
            finishSym := fun _ => symEq.trans empty,
            finishLook := fun e => absurd e nf,
            finishBits := fun e => absurd e nf }
  · have shape' : Shape d' := Shape.of_fields inv0.shape fields
      (by rw [lf]; exact lfRange) (fun st => by rw [busy] at st; rcases st with e | e <;> exact absurd e (by decide))
      trailer bits (fun _ => cur)
    have inv' := inv0.lift_empty good' alloc' (static.trans static0) shape' fields empty keepW keepP keepH keepB
    refine ⟨after, z', d', produced, inv', hinv', buffers', acc, frame, own, out', litEq, Or.inr ⟨run, busy, pend, cur, lf, ?_⟩⟩
    exact { fresh := fun e => absurd (lf.symm.trans e) lfNot,
            freshStart := fun e => absurd (lf.symm.trans e) lfNot,
            finishSym := fun e => by rw [busy] at e; exact absurd e (by decide),
            finishLook := fun e => by rw [busy] at e; exact absurd e (by decide),
            finishBits := fun e => by rw [busy] at e; exact absurd e (by decide) }

end Zlib.Deflate.Universal.Call
