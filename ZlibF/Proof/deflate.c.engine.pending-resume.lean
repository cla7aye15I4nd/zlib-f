import ZlibF.Proof.«deflate.c.engine.pending-block-output»
import ZlibF.Proof.«deflate.c.engine.rebuffer»

/-! # Lossless pending publication at an advanced cursor

A partial flush does not compact pending bytes. Resumption therefore uses
its actual cursor, including after a legal caller buffer replacement.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The public pending relation has exactly the bytes at its actual cursor. -/
theorem pending_bits_cursor_value {h : Heap} {d : DeflateState} {pb po : Nat}
    {buf : Array UInt8} {bits : List Bool}
    (pointer : d.pending_out = .ref (.blk pb) po) (get : h.bytes pb = some buf)
    (pending : PendingBits h d bits) :
    bits = ZlibF.Spec.bytesToBits ((buf.toList.drop po).take d.pending.toNat) ++
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat := by
  obtain ⟨bytes, data, equal⟩ := pending
  have byteValue : bytes = (buf.toList.drop po).take d.pending.toNat := by
    rcases data with ⟨null, _, _⟩ | ⟨ref, off, a, ptr, read, _, value⟩
    · rw [pointer] at null
      cases null
    · rw [pointer] at ptr
      have same : .blk pb = ref ∧ po = off := Ptr.ref.inj ptr
      rcases same with ⟨rfl, rfl⟩
      have array : a = buf := Option.some.inj (read.symm.trans get)
      subst a
      exact value
  rw [equal, byteValue, pending_word_bits]

/-- The exact pending-copy heap consumes a prefix of the bytes at po,
without treating previously published bytes as pending again. -/
theorem pending_copy_cursor_bits {h : Heap} {r : ZStreamRef} {ds pb po ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8} {before : List Bool}
    (base : d.pending_buf = .ref (.blk pb) 0) (cursor : d.pending_out = .ref (.blk pb) po)
    (get : h.bytes pb = some buf) (sourceBound : po + d.pending.toNat ≤ buf.size)
    (pending : PendingBits h d before) (pointer : z.next_out = .ref (.blk ob) oo)
    (separate : ob ≠ pb) (outBound : oo + z.avail_out.toNat ≤ output.size) :
    let n := pendingLen d.pending z.avail_out
    let after := pendingCopyHeap h r ds pb po ob oo z d buf output n
    let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
    ∃ written remaining,
      Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before := by
  let n := pendingLen d.pending z.avail_out
  let after := pendingCopyHeap h r ds pb po ob oo z d buf output n
  let result := pendingState d (.ref (.blk pb) (po + n.toNat)) n
  let off := if d.pending - n.toUInt64 == 0 then 0 else po + n.toNat
  let remainingBytes := (buf.toList.drop off).take result.pending.toNat
  let tailBits := Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat
  change ∃ written remaining, Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
    ZlibF.Spec.bytesToBits written ++ remaining = before
  have count : result.pending.toNat + n.toNat = d.pending.toNat := (pending_copy_counts d.pending z.avail_out).1
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have getPending : after.bytes pb = some buf := by
    simpa only [after, pendingCopyHeap, setD_bytes, ZStreamRef.put_bytes,
      upd_ne _ _ _ _ (Ne.symm separate)] using get
  have getOutput : after.bytes ob = some (copyRange output buf oo po n.toNat) := by simp [after, pendingCopyHeap]
  have resultPtr : result.pending_out = .ref (.blk pb) off := by
    dsimp only [result, pendingState, off]
    split <;> simp only [base]
  have remainingBound : off + result.pending.toNat ≤ buf.size := by
    dsimp only [off]
    split <;> omega
  have kept := pending_bits_slice resultPtr getPending remainingBound
  have copied : ((copyRange output buf oo po n.toNat).toList.drop oo).take n.toNat =
      (buf.toList.drop po).take n.toNat := by
    rw [← seg_eq_take_drop _ _ _ (by rw [size_copyRange]; omega),
      seg_copyRange output buf oo po n.toNat (by omega), seg_eq_take_drop buf po n.toNat (by omega)]
  have slice : remainingBytes = ((buf.toList.drop po).drop n.toNat).take result.pending.toNat := by
    dsimp only [remainingBytes, off]
    split
    · rename_i empty
      have zero : result.pending.toNat = 0 := by
        have value : d.pending - n.toUInt64 = 0 := beq_iff_eq.mp empty
        simpa only [result, pendingState, value, UInt64.toNat_zero]
      simp only [zero, List.take_zero]
    · rw [List.drop_drop]
  have splitBytes : (buf.toList.drop po).take d.pending.toNat =
      (buf.toList.drop po).take n.toNat ++ remainingBytes := by
    rw [slice, ← List.take_add, show n.toNat + result.pending.toNat = d.pending.toNat by omega]
  refine ⟨(buf.toList.drop po).take n.toNat, ZlibF.Spec.bytesToBits remainingBytes ++ tailBits,
    Or.inr ⟨.blk ob, oo, copyRange output buf oo po n.toNat, pointer, getOutput,
      by rw [size_copyRange]; omega, copied.symm⟩, kept, ?_⟩
  rw [pending_bits_cursor_value cursor get pending, splitBytes]
  simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc, tailBits]

/-- `local void flush_pending(z_streamp strm)` (resumed low-bit phase).
DGood supplies the actual pending allocation and advanced cursor. For
arbitrary raw-output capacity, actual execution preserves ownership,
caller ranges and the complete public pending sequence. No base-cursor
or block-output-room premise is needed in this phase. -/
theorem flush_pending_resume_raw_bits {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (pending : PendingBits h d before) :
    ∃ pb produced after z' result written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result.bi_valid.toInt < 8 ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      (0 < produced → result.pending.toNat = 0 → result.pending_out = result.pending_buf) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
  obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers pointer
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf))))
  let n := pendingLen d.pending z.avail_out
  have count : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  by_cases empty : n = 0
  · have run := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low empty
    refine ⟨pb, 0, h, z, d, [], before, blocks.pbuf, run, good, buffers, stream_accounting_zero z,
      ⟨fun _ _ read => ⟨_, read, rfl⟩, fun _ => rfl⟩, OutputStorage.refl h r ds pb ob,
      ?_, by omega, low, rfl, (by omega), ?_, pending, rfl⟩
    · rw [empty] at count
      exact count
    · exact Or.inr ⟨.blk ob, oo, output, pointer, outGet, by omega, by simp⟩
  · have run := flush_pending_low_raw good.live.hz good.live.zst good.live.hs low pointer cursor
      outGet get writable separate outBound sourceBound empty
    obtain ⟨written, remaining, bytes, pendingA, bits⟩ :=
      pending_copy_cursor_bits (r := r) (ds := ds) blocks.pbuf cursor get sourceBound pending pointer separate outBound
    have goodA := pending_copy_good (pending := buf) (oo := oo) good blocks.pbuf cursor outGet
    have sizes := pending_copy_sizes (r := r) (z := z) (pb := pb) (po := po) (pending := buf) (oo := oo) n good.live.hs outGet
    have account := pending_copy_accounting (d := d) pointer
    have fields : pendingState d (.ref (.blk pb) (po + n.toNat)) n =
        { d with
          pending := (pendingState d (.ref (.blk pb) (po + n.toNat)) n).pending,
          pending_out := (pendingState d (.ref (.blk pb) (po + n.toNat)) n).pending_out } := rfl
    have owned : ∀ b, StreamOwned (pendingCopyHeap h r ds pb po ob oo z d buf output n) r b ↔ StreamOwned h r b := by
      intro b
      rw [stream_owned_deflate goodA, stream_owned_deflate good]
      rfl
    have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account
    refine ⟨pb, n.toNat, pendingCopyHeap h r ds pb po ob oo z d buf output n,
      pendingStream z (.ref (.blk ob) (oo + n.toNat)) n,
      pendingState d (.ref (.blk pb) (po + n.toNat)) n, written, remaining,
      blocks.pbuf, run, goodA, buffersA, account, sizes, pending_copy_storage n good.live.hz good.live.hs outGet,
      count, (pending_copy_counts _ _).1, low, fields, ?_, bytes, pendingA, bits⟩
    intro _positive zero
    have eq : d.pending - n.toUInt64 = 0 := UInt64.toNat_inj.mp zero
    simp only [pendingState, eq, BEq.rfl, ite_true]


/-- Legal caller replacement preserves the complete public pending
sequence, including an advanced private cursor. No caller bytes are
part of that private sequence. -/
theorem rebuffer_pending_bits {h g : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {bits : List Bool}
    (good : DGood h r ds z d) (edit : Rebuffer h g r) (pending : PendingBits h d bits) :
    PendingBits g d bits := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  have slot := rebuffer_owned good edit (x := pb) (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf))))
  rw [pending_bits_cursor_value cursor get pending]
  exact pending_bits_slice cursor (slot.1.trans get) (by rw [size, ← blocks.psize]; exact bound)

/-- `local void flush_pending(z_streamp strm)` (publication and resume).
The first actual call publishes complete buffered bytes. Every legal
caller replacement with raw output can continue from the returned cursor.
The two observed output lists and the remaining public pending relation
concatenate to the original bits, for arbitrary capacities in both calls.
The default no-gzip-header condition supports the existing rebuffer proof.
This is an internal two-call composition, not the public deflate theorem. -/
theorem flush_pending_publish_resume {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (header : d.gzhead = none)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    ∃ produced after z' result written remaining,
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ OutputStorage h after r ds pb ob ∧
      produced = min (d.pending.toNat + d.bi_valid.toInt.toNat / 8) z.avail_out.toNat ∧
      result.pending.toNat + produced = d.pending.toNat + d.bi_valid.toInt.toNat / 8 ∧
      result.bi_valid.toInt < 8 ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ∧
      ∀ g zg ob' oo', Rebuffer after g r → StreamBuffers g r → r.get g = some zg →
        zg.next_out = .ref (.blk ob') oo' →
        ∃ produced' final zf df written' rest,
          flush_pending (some r) g = .ok ((), final) ∧ DGood final r ds zf df ∧ StreamBuffers final r ∧
          StreamAccounting zg zf 0 produced' ∧ OutputStorage g final r ds pb ob' ∧
          produced' = min result.pending.toNat zg.avail_out.toNat ∧
          df.pending.toNat + produced + produced' = d.pending.toNat + d.bi_valid.toInt.toNat / 8 ∧
          df.bi_valid.toInt < 8 ∧ Bytes final zg.next_out produced' written' ∧ PendingBits final df rest ∧
          ZlibF.Spec.bytesToBits (written ++ written') ++ rest = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨produced, after, z', result, written, remaining, run, goodA, buffersA, account, _sizes, storage,
    count, remainingCount, low, _valid, fields, bytes, pending, bits⟩ :=
    flush_pending_raw_bits good trees buffers pointer cursor room
  refine ⟨produced, after, z', result, written, remaining, run, goodA, buffersA, account, storage,
    count, remainingCount, low, bytes, pending, bits, ?_⟩
  intro g zg ob' oo' edit buffersG getZ pointerG
  have headerA : result.gzhead = none := by rw [fields]; exact header
  obtain ⟨other, getOther, _changed, goodG⟩ := rebuffer_good_no_header goodA edit headerA
  have same : other = zg := Option.some.inj (getOther.symm.trans getZ)
  subst other
  have pendingG := rebuffer_pending_bits goodA edit pending
  obtain ⟨pb', produced', final, zf, df, written', rest, base, runF, goodF, buffersF, accountF,
    _sizesF, storageF, countF, pendingCountF, lowF, _fieldsF, _reset, bytesF, pendingF, bitsF⟩ :=
    flush_pending_resume_raw_bits goodG buffersG pointerG low pendingG
  have baseA : result.pending_buf = .ref (.blk pb) 0 := by rw [fields]; exact trees.base.pbuf
  have key : pb' = pb := by simpa only [baseA, Ptr.ref.injEq, BRef.blk.injEq, and_true] using base.symm
  subst pb'
  refine ⟨produced', final, zf, df, written', rest, runF, goodF, buffersF, accountF, storageF,
    countF, by omega, lowF, bytesF, pendingF, ?_⟩
  have appendBits : ZlibF.Spec.bytesToBits (written ++ written') =
      ZlibF.Spec.bytesToBits written ++ ZlibF.Spec.bytesToBits written' := List.flatMap_append
  rw [appendBits, List.append_assoc, bitsF, bits]

end Zlib.Deflate.Engine.Proofs
