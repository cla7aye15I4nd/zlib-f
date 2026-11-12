import ZlibF.Proof.«public-compress-safe-loop»
import ZlibF.Proof.«public-deflate-end»

/-!
# compress.c: safety, the cleanup

After `deflateInit` fails, `compress2_z` frees the automatic `z_stream`. After the loop it
computes the output length, calls `deflateEnd` and frees the automatic `z_stream`. In both
cases the final heap holds the caller's objects, with the output written, and nothing else
(`SameObjectsUpToTableShape`).
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Compress Zlib.Deflate
open ZlibF.Spec.Public.Proofs.Uncompress hiding measure
open Zlib.Deflate.Spec (DGood)
variable {R : Heap → ZStreamRef → Prop}
set_option autoImplicit false

/-- The seven object tables agree at a block. -/
def Tables (E F : Heap) (b : Nat) : Prop :=
  F.bytes b = E.bytes b ∧ F.words b = E.words b ∧ F.streams b = E.streams b ∧
  F.gzheaders b = E.gzheaders b ∧ F.dstates b = E.dstates b ∧ F.istates b = E.istates b ∧
  F.gzstates b = E.gzstates b

theorem Tables.trans {E F G : Heap} {b : Nat} (a : Tables E F b) (c : Tables F G b) : Tables E G b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := c
  exact ⟨c1.trans a1, c2.trans a2, c3.trans a3, c4.trans a4, c5.trans a5, c6.trans a6, c7.trans a7⟩

theorem upto_of {E F : Heap} (tables : ∀ b, Tables E F b) (ro : ∀ b, E.live b → F.ro b = E.ro b)
    (gs : F.static = E.static) (ga : F.allocOk = E.allocOk) (gg : F.garbage = E.garbage)
    (nb : E.nextBlk ≤ F.nextBlk) (na : E.nalloc ≤ F.nalloc) : SameObjectsUpToTableShape E F :=
  ⟨fun b => (tables b).1, fun b => (tables b).2.1, ro, fun b => (tables b).2.2.1,
    fun b => (tables b).2.2.2.1, fun b => (tables b).2.2.2.2.1, fun b => (tables b).2.2.2.2.2.1,
    fun b => (tables b).2.2.2.2.2.2, gs, ga, gg, nb, na⟩

/-- A block that is not live has no object. -/
theorem tables_dead {E F : Heap} {b : Nat} (e : ¬ E.live b) (f : ¬ F.live b) : Tables E F b := by
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at e f
  exact ⟨f.1.trans e.1.symm, f.2.1.trans e.2.1.symm, f.2.2.1.trans e.2.2.1.symm,
    f.2.2.2.1.trans e.2.2.2.1.symm, f.2.2.2.2.1.trans e.2.2.2.2.1.symm,
    f.2.2.2.2.2.1.trans e.2.2.2.2.2.1.symm, f.2.2.2.2.2.2.trans e.2.2.2.2.2.2.symm⟩

/-- The stream block after freeing the record: no object when the heap had only the record there. -/
theorem tables_freed {E X : Heap} {k : Nat} {z : ZStream} (u : Zlib.Deflate.Spec.Uniq X) (hz : X.streams k = some z)
    (e : ¬ E.live k) : Tables E { X with streams := upd X.streams k none } k := by
  have only := uniq_streams_only (H := X) (by exact u) hz
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at e
  refine ⟨only.1.trans e.1.symm, only.2.1.trans e.2.1.symm, by simp [e.2.2.1], only.2.2.1.trans e.2.2.2.1.symm,
    only.2.2.2.1.trans e.2.2.2.2.1.symm, only.2.2.2.2.1.trans e.2.2.2.2.2.1.symm,
    only.2.2.2.2.2.trans e.2.2.2.2.2.2.symm⟩

theorem freed_live {X : Heap} {k b : Nat} (ne : b ≠ k) :
    ({ X with streams := upd X.streams k none } : Heap).live b ↔ X.live b := by
  simp [Heap.live, upd_ne _ _ _ _ ne]

theorem freed_tables {X : Heap} {k b : Nat} (ne : b ≠ k) :
    Tables X { X with streams := upd X.streams k none } b := by
  exact ⟨rfl, rfl, by simp [upd_ne _ _ _ _ ne], rfl, rfl, rfl, rfl⟩

/-- `deflateInit` failed: freeing the automatic stream leaves the caller heap. -/
theorem init_failure_heap {h after : Heap} (fresh : Fresh h) (u : Zlib.Deflate.Spec.Uniq after)
    (live : ∀ b, after.live b ↔ (cHeap h).live b) (frame : Frame (cHeap h) after (StreamRoot (.tab h.nextBlk)))
    {z' : ZStream} (hz : after.streams h.nextBlk = some z') :
    SameObjectsUpToTableShape h { after with streams := upd after.streams h.nextBlk none } := by
  obtain ⟨fs, fa, fg, fn, fna, fb⟩ := frame
  have k0 : ¬ h.live h.nextBlk := fresh _ (Nat.le_refl _)
  refine upto_of ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro b
    by_cases bk : b = h.nextBlk
    · subst bk; exact tables_freed u hz k0
    · refine Tables.trans ?_ (freed_tables bk)
      by_cases lb : h.live b
      · have cl : (cHeap h).live b := (cHeap_live h b).2 (Or.inl lb)
        obtain ⟨t1, t2, t3, t4, t5, t6, t7, -⟩ := fb b cl (by simp only [StreamRoot]; exact bk)
        simp only [cHeap, upd_ne _ _ _ _ bk] at t1 t2 t3 t4 t5 t6 t7
        exact ⟨t1, t2, t3, t4, t5, t6, t7⟩
      · exact tables_dead lb (fun la => by
          rcases (cHeap_live h b).1 ((live b).1 la) with x | x
          · exact lb x
          · exact bk x)
  · intro b lb
    have bk : b ≠ h.nextBlk := fun e => k0 (e ▸ lb)
    have := (fb b ((cHeap_live h b).2 (Or.inl lb)) (by simp only [StreamRoot]; exact bk)).2.2.2.2.2.2.2
    simpa [cHeap] using this
  · simpa [cHeap] using fs.symm
  · simpa [cHeap] using fa.symm
  · simpa [cHeap] using fg.symm
  · simp only [cHeap] at fn; simp; omega
  · simp only [cHeap] at fna; simpa using fna

/-- The cleanup after the loop: the output length, `deflateEnd`, and freeing the automatic
stream leave the caller heap with the output written. -/
theorem epilogue {e : CEnv} (ok : COK e) {st : Loop} {H : Heap} {out : List UInt8} {used : Nat}
    {z : ZStream} {s : DeflateState} (cs : CState R e st H out used z s) :
    ∃ d rcE H2, ptrDiff z.next_out e.dest H = .ok (d, H) ∧
      deflateEnd (some e.r) H = .ok (rcE, H2) ∧
      freeZStream (some e.r) H2 = .ok ((), { H2 with streams := upd H2.streams e.k none }) ∧
      Store e.h₀ e.dest out (writeOut e.h₀ e.dest out) ∧
      SameObjectsUpToTableShape (writeOut e.h₀ e.dest out) { H2 with streams := upd H2.streams e.k none } ∧
      out.length ≤ e.cap := by
  have outC := cs.outCount
  have outLe : out.length ≤ e.cap := by omega
  have k0 : ¬ e.h₀.live e.k := ok.fresh e.k (Nat.le_refl _)
  have destBlocks := caller_view_blocks (Or.inr ok.destW)
  -- the output length
  have wH : Writable H e.dest e.cap := cs.agree.writable (writable_writeOut ok.destW outLe ok.destW) destBlocks
  have diff : ∃ d, ptrDiff z.next_out e.dest H = .ok (d, H) := by
    rw [cs.nextOut]
    rcases wH with ⟨h0, c0⟩ | ⟨r, i, a, hq, g, -, fit⟩
    · rw [h0]; exact ⟨0, by simp [ptrDiff, advance]⟩
    · rw [hq]
      refine ⟨Int64.ofInt (((i + out.length : Nat) : Int) - ((i : Nat) : Int)), ?_⟩
      have b1 : i + out.length ≤ a.size := by omega
      have b2 : i ≤ a.size := by omega
      have lt : out.length < 2 ^ 63 := by have := ok.capBound; omega
      have nn : ¬ ((advance (Ptr.ref r i) out.length == Ptr.null && (Ptr.ref r i : BPtr) == Ptr.null) = true) := by
        intro c; cases c
      unfold ptrDiff
      rw [if_neg nn]
      simp only [advance, Ptr.diff]
      rw [if_pos trivial]
      simp only [g]
      rw [if_pos ⟨b1, b2⟩, if_pos (by omega)]
  obtain ⟨d, diffRun⟩ := diff
  -- deflateEnd
  obtain ⟨-, -, -, -, -, H2s, run1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, uniq2, -, -⟩ :=
    Zlib.Deflate.Proofs.deflateEnd_safe cs.good cs.zfree
  obtain ⟨H2, run2, get2, liveC, frame, -, next2⟩ :=
    ZlibF.Spec.Public.DeflateEndProof.deflate_end_public H e.r (e.k + 1) z s cs.good cs.zfree
  have same := Except.ok.inj (run1.symm.trans run2)
  simp only [Prod.mk.injEq] at same
  obtain ⟨-, rfl⟩ := same
  have hz2 : H2s.streams e.k = some { z with state := none } := get2
  obtain ⟨fs, fa, fg, -, fna, fb⟩ := frame
  have wOut : Writable e.h₀ e.dest out.length := by
    have := writable_sub (c := 0) (m := out.length) ok.destW (by omega)
    rwa [advance_zero] at this
  refine ⟨d, _, H2s, diffRun, run2, ?_, store_writeOut wOut, ?_, outLe⟩
  · show freeZStream (some (.tab e.h₀.nextBlk)) H2s = _
    simp only [freeZStream]
    rw [show H2s.streams.get e.h₀.nextBlk = some { z with state := none } from hz2]
    rfl
  · have eLive : ∀ b, (writeOut e.h₀ e.dest out).live b ↔ e.h₀.live b := fun b => writeOut_live b
    have hLive : ∀ b, e.h₀.live b → H.live b := by
      intro b lb
      have el : (writeOut e.h₀ e.dest out).live b := (eLive b).2 lb
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := cs.agree.blocks b lb
      simp only [Heap.live] at el ⊢
      rw [s1, s2, s3, s4, s5, s6, s7]; exact el
    have notChanged : ∀ b, e.h₀.live b → ¬ (StreamRoot e.r b ∨ DeflateOwned (e.k + 1) s b) := by
      intro b lb ch
      have lt : b < e.k := ok.fresh.lt lb
      rcases ch with ch | ch
      · simp only [StreamRoot, CEnv.r] at ch; exact absurd ch (by simp only [CEnv.k] at lt; omega)
      · rw [cs.owned b] at ch; omega
    have kLive : H.live e.k := by
      have hz : H.streams e.k = some z := cs.good.live.hz
      simp [Heap.live, hz]
    have kLt : e.k < H.nextBlk := cs.good.fresh.lt kLive
    have eg := writeOut_globals e.h₀ e.dest out
    refine upto_of ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro b
      by_cases bk : b = e.k
      · subst bk; exact tables_freed uniq2 hz2 (fun l => k0 ((eLive _).1 l))
      · refine Tables.trans ?_ (freed_tables bk)
        by_cases lb : e.h₀.live b
        · obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := cs.agree.blocks b lb
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, -⟩ := fb b (hLive b lb) (notChanged b lb)
          exact ⟨t1.trans s1, t2.trans s2, t3.trans s3, t4.trans s4, t5.trans s5, t6.trans s6, t7.trans s7⟩
        · refine tables_dead (fun l => lb ((eLive b).1 l)) (fun l2 => ?_)
          rcases (liveC b).1 l2 with ⟨l1, notOwned⟩ | f
          · rcases cs.liveOnly b l1 with x | x | x
            · exact lb x
            · exact bk x
            · exact notOwned ((cs.owned b).2 x)
          · exact f
    · intro b lE
      have lb := (eLive b).1 lE
      have bk : b ≠ e.k := fun x => k0 (x ▸ lb)
      have t := (fb b (hLive b lb) (notChanged b lb)).2.2.2.2.2.2.2
      have s8 := (cs.agree.blocks b lb).2.2.2.2.2.2.2
      show H2s.ro b = _
      rw [t, s8]
    · show H2s.static = _
      rw [← fs, cs.agree.static]
    · show H2s.allocOk = _
      rw [← fa, cs.agree.allocOk]
    · show H2s.garbage = _
      rw [← fg, cs.agree.garbage]
    · show (writeOut e.h₀ e.dest out).nextBlk ≤ H2s.nextBlk
      rw [eg.2.2.2.1, next2]
      simp only [CEnv.k] at kLt
      omega
    · show (writeOut e.h₀ e.dest out).nalloc ≤ H2s.nalloc
      rw [eg.2.2.2.2.1]
      exact Nat.le_trans cs.nalloc fna

end ZlibF.Spec.Public.Proofs.Compress
