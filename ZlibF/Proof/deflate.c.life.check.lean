import ZlibF.Proof.«deflate.c.base»

/-!
# deflate.c: `deflateTune`, `deflateSetHeader`, `deflateUsed`, `deflatePending`

The four small functions that read or set a few fields of an initialised stream. Each starts with the stream check
(`deflateStateCheck`); on a stream the check refuses it returns `Z_STREAM_ERROR` and changes nothing.
-/

namespace Zlib.Deflate.Spec
open C

/-- The state record after `deflateTune`: the four tuning fields are the arguments (`int` to `unsigned` for three of
them, which wraps; `nice_match` is an `int`). -/
def tuneD (d : DeflateState) (good_length max_lazy nice_length max_chain : Int32) : DeflateState :=
  { d with good_match := good_length.toUInt32, max_lazy_match := max_lazy.toUInt32, nice_match := nice_length,
           max_chain_length := max_chain.toUInt32 }

/-- The state record after `deflateSetHeader` on a gzip stream: the header pointer is stored. -/
def setHeaderD (d : DeflateState) (head : GzHeaderPtr) : DeflateState := { d with gzhead := head }

end Zlib.Deflate.Spec

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec

/-! ### deflateTune -/

theorem deflateTune_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (g m n c : Int32) :
    deflateTune (some r) g m n c h = .ok (Z_OK, setD h ds (tuneD d g m n c)) := by
  unfold deflateTune
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, tuneD]

theorem _root_.Zlib.Deflate.Spec.DStInv.tune {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d) (g m n c : Int32) :
    DStInv h ds (tuneD d g m n c) :=
  { hI with blocks := hI.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }

/-- **deflateTune, safety and specification.** On an initialised stream (any `int` arguments, including negative ones,
which `zlib.h` leaves to the caller) the call returns `Z_OK` and never faults. It changes the four tuning fields of the
state record and nothing else: `good_match`, `max_lazy_match` and `max_chain_length` become the arguments converted to
`unsigned`, `nice_match` the argument. The stream is initialised again with the invariants intact, and the live
blocks are the same (no allocation, no free). -/
theorem deflateTune_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (g m n c : Int32) :
    ∃ h', C.run (deflateTune (some r) g m n c) h = .ok (Z_OK, h') ∧ h' = setD h ds (tuneD d g m n c) ∧
      DGood h' r ds z (tuneD d g m n c) ∧ (∀ b, h'.live b ↔ h.live b) := by
  refine ⟨_, deflateTune_run hG.live g m n c, rfl, ?_, ?_⟩
  · exact hG.setD' (d' := tuneD d g m n c) rfl hG.live.status (hG.inv.tune g m n c) (by trkeep)
  · intro b; exact (shape_setD hG.live.hs _).live b

/-- **deflateTune, refusal.** On a stream the check refuses (including `NULL`), the call returns `Z_STREAM_ERROR` and
changes nothing. -/
theorem deflateTune_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (g m n c : Int32) : C.run (deflateTune strm g m n c) h = .ok (Z_STREAM_ERROR, h) := by
  unfold deflateTune
  exact check_refuse hD hN _ _


/-! ### deflateSetHeader -/

theorem deflateSetHeader_run_gz {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hw : d.wrap = 2) (head : GzHeaderPtr) :
    deflateSetHeader (some r) head h = .ok (Z_OK, setD h ds (setHeaderD d head)) := by
  unfold deflateSetHeader
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, setHeaderD, hw]

theorem deflateSetHeader_run_other {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hw : d.wrap ≠ 2) (head : GzHeaderPtr) :
    deflateSetHeader (some r) head h = .ok (Z_STREAM_ERROR, h) := by
  unfold deflateSetHeader
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, hw]

theorem _root_.Zlib.Deflate.Spec.DStInv.setHeader {h : Heap} {ds : Nat} {d : DeflateState} (hI : DStInv h ds d)
    (head : GzHeaderPtr) (hg : GzOk h head) : DStInv h ds (setHeaderD d head) :=
  { hI with blocks := hI.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, gz := hg }

/-- **deflateSetHeader, safety and specification (gzip stream).** On an initialised stream whose wrapper is gzip
(`wrap = 2`) and for a header pointer that is `NULL` or a live `gz_header` record, the call returns `Z_OK`, never
faults, and stores the pointer in the state (`gzhead`); nothing else changes. The stream is initialised again with the
invariants intact; no block is allocated or freed. (`zlib.h` requires the header to stay valid until the header has
been written; that concerns the later calls of `deflate`, not this one.) -/
theorem deflateSetHeader_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (hw : d.wrap = 2) (head : GzHeaderPtr) (hg : GzOk h head) :
    ∃ h', C.run (deflateSetHeader (some r) head) h = .ok (Z_OK, h') ∧ h' = setD h ds (setHeaderD d head) ∧
      DGood h' r ds z (setHeaderD d head) ∧ (∀ b, h'.live b ↔ h.live b) := by
  refine ⟨_, deflateSetHeader_run_gz hG.live hw head, rfl, ?_, ?_⟩
  · exact hG.setD' (d' := setHeaderD d head) rfl hG.live.status (hG.inv.setHeader head hg) (by trkeep)
  · intro b; exact (shape_setD hG.live.hs _).live b

/-- **deflateSetHeader on a stream that is not gzip.** `Z_STREAM_ERROR`, nothing changes. -/
theorem deflateSetHeader_not_gzip {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hw : d.wrap ≠ 2) (head : GzHeaderPtr) :
    C.run (deflateSetHeader (some r) head) h = .ok (Z_STREAM_ERROR, h) :=
  deflateSetHeader_run_other hL hw head

/-- **deflateSetHeader, refusal.** On a stream the check refuses (including `NULL`): `Z_STREAM_ERROR`, nothing changes. -/
theorem deflateSetHeader_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (head : GzHeaderPtr) : C.run (deflateSetHeader strm head) h = .ok (Z_STREAM_ERROR, h) := by
  unfold deflateSetHeader
  exact check_refuse hD hN _ _

/-! ### deflateUsed -/

theorem deflateUsed_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hasBits : Bool) :
    deflateUsed (some r) hasBits h = .ok ((Z_OK, if hasBits then some d.bi_used else none), h) := by
  unfold deflateUsed
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs]

/-- **deflateUsed, safety and specification.** On an initialised stream the call returns `Z_OK` and, when the pointer
`bits` is not `NULL` (`hasBits`), the value `bi_used` that would be stored through it; the heap is unchanged. -/
theorem deflateUsed_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hasBits : Bool) :
    C.run (deflateUsed (some r) hasBits) h = .ok ((Z_OK, if hasBits then some d.bi_used else none), h) :=
  deflateUsed_run hL hasBits

/-- **deflateUsed, refusal.** `Z_STREAM_ERROR`, no value stored, nothing changes. -/
theorem deflateUsed_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (hasBits : Bool) : C.run (deflateUsed strm hasBits) h = .ok ((Z_STREAM_ERROR, none), h) := by
  unfold deflateUsed
  exact check_refuse hD hN _ _

/-! ### deflatePending -/

/-- What `deflatePending` returns for the state record `d`: the pending count does not fit `unsigned` only if
`pending >= 2^32`, in which case the C stores `(unsigned)-1` and returns `Z_BUF_ERROR`. -/
def pendingResult (d : DeflateState) (hasPending hasBits : Bool) : Int32 × Option UInt32 × Option Int32 :=
  let bits := if hasBits then some d.bi_valid else none
  if hasPending then
    if d.pending.toUInt32.toUInt64 != d.pending then (Z_BUF_ERROR, some 0xffffffff, bits)
    else (Z_OK, some d.pending.toUInt32, bits)
  else (Z_OK, none, bits)

theorem deflatePending_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (hasPending hasBits : Bool) :
    deflatePending (some r) hasPending hasBits h = .ok (pendingResult d hasPending hasBits, h) := by
  unfold deflatePending
  cases hasPending <;> cases hasBits <;> dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, pendingResult] <;>
    split <;> simp_all

/-- **deflatePending, safety and specification.** On an initialised stream with the invariant the call never faults
and returns `Z_OK`; the count stored through `pending` (when it is not `NULL`) is exactly the number of pending output
bytes, and the value stored through `bits` is `bi_valid`. The heap is unchanged. (The count is at most
`4 * lit_bufsize <= 2^17`, so the overflow case of the C, `Z_BUF_ERROR` with `(unsigned)-1`, cannot happen.) -/
theorem deflatePending_safe {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hG : DGood h r ds z d) (hasPending hasBits : Bool) :
    C.run (deflatePending (some r) hasPending hasBits) h =
      .ok ((Z_OK, (if hasPending then some d.pending.toUInt32 else none), (if hasBits then some d.bi_valid else none)), h) ∧
    (hasPending = true → d.pending.toUInt32.toNat = d.pending.toNat) := by
  have hI := hG.inv
  obtain ⟨w, p, q, b, hB⟩ := hI.blocks
  obtain ⟨off, -, hpl⟩ := hB.pout
  have hlit : d.lit_bufsize.toNat ≤ 32768 := by
    have := hI.lit; have := hI.hsize; have := hI.hbits_hi
    have : 2 ^ d.hash_bits.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hI.hbits_hi
    omega
  have hpend : d.pending.toNat < 2 ^ 32 := by
    have := hB.psize; omega
  have e1 : d.pending.toUInt32.toUInt64 = d.pending := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    exact Nat.mod_eq_of_lt hpend
  have e2 : d.pending.toUInt32.toNat = d.pending.toNat := by
    rw [UInt64.toNat_toUInt32]; exact Nat.mod_eq_of_lt hpend
  refine ⟨?_, fun _ => e2⟩
  have := deflatePending_run hG.live hasPending hasBits
  rw [C.run, this]
  simp [pendingResult, e1]
  cases hasPending <;> cases hasBits <;> simp

/-- **deflatePending, refusal.** `Z_STREAM_ERROR`, no value stored, nothing changes. -/
theorem deflatePending_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (hasPending hasBits : Bool) :
    C.run (deflatePending strm hasPending hasBits) h = .ok ((Z_STREAM_ERROR, none, none), h) := by
  unfold deflatePending
  exact check_refuse hD hN _ _

end Zlib.Deflate.Proofs
