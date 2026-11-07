import ZlibF.Proof.«deflate.c.engine.ordinary-call-full-storage»

/-! # Exact raw caller output intervals and public buffer frames -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- Restoring the caller byte allocation removes it from a complete heap
frame. Heap shape and type uniqueness retain its other object slots. -/
theorem frame_restore_raw_output {h g : Heap} {ob : Nat} {before : Array UInt8} {changed : Nat → Prop}
    (frame : Frame h g (fun b => changed b ∨ b = ob)) (shape : Shape h g) (unique : Uniq h)
    (get : h.bytes ob = some before) (readonly : g.ro ob = h.ro ob) :
    Frame h (Zlib.Trees.Proofs.Out.setB g ob before) changed := by
  obtain ⟨static, alloc, garbage, next, count, slots⟩ := frame
  refine ⟨static, alloc, garbage, next, count, ?_⟩
  intro b live outside
  by_cases same : b = ob
  · subst b
    have old := unique.bytes_only get
    have present := shape ob
    have absent {α : Type} {x y : Option α} (eq : x.isSome = y.isSome) (none : y = .none) : x = .none := by
      rw [none] at eq
      cases x <;> simp_all
    have words := absent present.2.1 old.1
    have streams := absent present.2.2.1 old.2.1
    have headers := absent present.2.2.2.1 old.2.2.1
    have dstates := absent present.2.2.2.2.1 old.2.2.2.1
    have istates := absent present.2.2.2.2.2.1 old.2.2.2.2.1
    have gzstates := absent present.2.2.2.2.2.2 old.2.2.2.2.2
    simp only [Zlib.Trees.Proofs.Out.setB, upd_same, words, streams, headers, dstates,
      istates, gzstates, old.1, old.2.1, old.2.2.1, old.2.2.2.1, old.2.2.2.2.1, old.2.2.2.2.2, get, readonly, and_self]
  · have kept : SlotSame h g b := slots b live (fun yes => yes.elim outside same)
    apply kept.trans
    simp [SlotSame, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ same]

/-- The complete heap frame plus the actual output-array interval effect
establishes the public BufferFrame for that raw caller output range. -/
theorem raw_buffer_frame_of_interval {h g : Heap} {ob offset produced : Nat}
    {before after : Array UInt8} {changed : Nat → Prop}
    (frame : Frame h g (fun b => changed b ∨ b = ob)) (shape : Shape h g) (unique : Uniq h)
    (getBefore : h.bytes ob = some before) (getAfter : g.bytes ob = some after)
    (readonly : g.ro ob = h.ro ob) (size : after.size = before.size)
    (untouched : ∀ j, j < before.size → ¬ (offset ≤ j ∧ j < offset + produced) → after[j]? = before[j]?) :
    BufferFrame h g changed [⟨.ref (.blk ob) offset, produced⟩] := by
  constructor
  · change Frame h (match h.bytes ob with
      | none => g
      | some a => Zlib.Trees.Proofs.Out.setB g ob a) changed
    rw [getBefore]
    exact frame_restore_raw_output frame shape unique getBefore readonly
  · intro region member r off a pointer get
    simp only [List.mem_singleton] at member
    subst region
    obtain ⟨sameRef, sameOffset⟩ := Ptr.ref.inj pointer
    subst r
    subst off
    have sameArray : a = before := Option.some.inj (get.symm.trans getBefore)
    subst a
    refine ⟨after, getAfter, size, ?_⟩
    intro j bound outside
    apply untouched j bound
    intro inside
    apply outside
    exact ⟨⟨.ref (.blk ob) offset, produced⟩, by simp, offset, rfl, inside.1, inside.2⟩
/-- The current raw caller output allocation is outside both the stream
record and its private allocations, even when caller ranges share an array. -/
theorem caller_raw_output_outside {h : Heap} {r : ZStreamRef} {ds ob offset : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) offset) : ¬ (StreamRoot r ob ∨ DeflateOwned ds d ob) := by
  obtain ⟨output, get, _ro, _bound, outside⟩ := caller_raw_output good buffers pointer
  have absent := good.uniq.bytes_only get
  have root : ¬ StreamRoot r ob := by
    cases r with
    | tab i =>
      intro eq
      change ob = i at eq
      have live := good.live.hz
      simp only [ZStreamRef.get, ← eq, absent.2.1] at live
      contradiction
    | in_gzstate_strm i =>
      intro eq
      change ob = i at eq
      have live := good.live.hz
      simp only [ZStreamRef.get, ← eq, absent.2.2.2.2.2, Option.map_none] at live
      contradiction
  exact fun yes => yes.elim root outside

/-- A private-only stage retains the complete raw caller output array
and its read-only flag. No range-disjoint-allocation assumption is added. -/
theorem private_frame_raw_output_same {h g : Heap} {r : ZStreamRef} {ds ob offset : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) offset)
    (frame : Frame h g (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    g.bytes ob = h.bytes ob ∧ g.ro ob = h.ro ob := by
  obtain ⟨output, get, _ro, _bound, _outside⟩ := caller_raw_output good buffers pointer
  have live : h.live ob := by simp [Heap.live, get]
  obtain ⟨_static, _alloc, _garbage, _next, _count, slots⟩ := frame
  obtain ⟨bytes, _words, _streams, _headers, _dstates, _istates, _gzstates, ro⟩ :=
    slots ob live (caller_raw_output_outside good buffers pointer)
  exact ⟨bytes, ro⟩

/-- Two consecutive output intervals compose at the actual advanced
cursor. Every byte outside their combined interval retains its old value. -/
theorem raw_output_interval_compose (before middle after : Array UInt8) (offset first second : Nat)
    (size1 : middle.size = before.size) (size2 : after.size = middle.size)
    (one : ∀ j, j < before.size → ¬ (offset ≤ j ∧ j < offset + first) → middle[j]? = before[j]?)
    (two : ∀ j, j < middle.size → ¬ (offset + first ≤ j ∧ j < (offset + first) + second) → after[j]? = middle[j]?) :
    after.size = before.size ∧
      ∀ j, j < before.size → ¬ (offset ≤ j ∧ j < offset + (first + second)) → after[j]? = before[j]? := by
  refine ⟨size2.trans size1, ?_⟩
  intro j bound outside
  have firstOutside : ¬ (offset ≤ j ∧ j < offset + first) := by omega
  have secondOutside : ¬ (offset + first ≤ j ∧ j < offset + first + second) := by omega
  exact (two j (by omega) secondOutside).trans (one j bound firstOutside)

/-- The actual low-bit pending publication changes exactly its accounted raw output interval, retaining all bytes on either side. -/
theorem flush_pending_low_run_output_interval {h after : Heap} {r : ZStreamRef} {ds ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState} {before : Array UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) (getBefore : h.bytes ob = some before) :
    ∃ next, after.bytes ob = some next ∧ next.size = before.size ∧
      ∀ j, j < before.size → ¬ (oo ≤ j ∧ j < oo + produced) → next[j]? = before[j]? := by
  by_cases zero : pendingLen d.pending z.avail_out = 0
  · have run0 := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low zero
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    rw [← heaps]
    exact ⟨before, getBefore, rfl, fun _ _ _ => rfl⟩
  · obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
    obtain ⟨buf, get, size⟩ := blocks.ba
    obtain ⟨po, cursor, bound⟩ := blocks.pout
    have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
    obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers pointer
    have array : output = before := Option.some.inj (outGet.symm.trans getBefore)
    subst output
    have separate : ob ≠ pb := by
      intro same
      subst ob
      exact outside (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf))))
    let n := pendingLen d.pending z.avail_out
    let expected := pendingCopyHeap h r ds pb po ob oo z d buf before n
    have run0 : flush_pending (some r) h = .ok ((), expected) :=
      flush_pending_low_raw good.live.hz good.live.zst good.live.hs low pointer cursor outGet get writable
        separate outBound sourceBound zero
    have good0 := pending_copy_good (pending := buf) (oo := oo) good blocks.pbuf cursor outGet
    have heaps : expected = after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have streams : pendingStream z (.ref (.blk ob) (oo + n.toNat)) n = z' := by
      have get0 := good0.live.hz
      change r.get expected = some _ at get0
      rw [heaps] at get0
      exact Option.some.inj (get0.symm.trans live)
    rw [← streams] at account
    have account0 := pending_copy_accounting (d := d) pointer
    have amount : produced = n.toNat := (stream_accounting_counts_unique account account0).2
    rw [amount, ← heaps]
    refine ⟨copyRange before buf oo po n.toNat, ?_, size_copyRange _ _ _ _ _, ?_⟩
    · simp only [expected, pendingCopyHeap, setD_bytes, ZStreamRef.put_bytes, upd_same]
    · intro j _bound untouched
      have count : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
      have fit : oo + n.toNat ≤ before.size := by omega
      rw [getElem?_copyRange before buf oo po n.toNat j fit, ite_eq_right untouched]

/-- Bit preparation writes only the private pending allocation. The
complete actual pending call therefore changes just its accounted raw
caller output interval, including short and zero copies. -/
theorem flush_pending_run_output_interval {h after : Heap} {r : ZStreamRef} {ds pb ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState} {buf before : Array UInt8}
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) (getBefore : h.bytes ob = some before) :
    ∃ next, after.bytes ob = some next ∧ next.size = before.size ∧
      ∀ j, j < before.size → ¬ (oo ≤ j ∧ j < oo + produced) → next[j]? = before[j]? := by
  obtain ⟨next, prepared, _bitRun, goodP, treesP, _bits, low, size, fields, _pending, _valid, sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size fields treesP
  obtain ⟨_output, _get, _writable, _bound, outside⟩ := caller_raw_output good buffers pointer
  have different : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have getP : (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds prepared).bytes ob = some before := by
    simp only [setD_bytes, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ different, getBefore]
  exact flush_pending_low_run_output_interval goodP buffersP pointer low (sameRun.symm.trans run) live account getP

/-- Complete pending publication establishes the exact public BufferFrame,
not only a frame allowing arbitrary changes to the caller allocation. -/
theorem flush_pending_run_buffer_frame {h after : Heap} {r : ZStreamRef} {ds pb ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] := by
  obtain ⟨_amount, other, _ze, _de, _written, _remaining, tested, _goodA, _buffersA, _accountA,
      sizes, storage, _rest⟩ := flush_pending_raw_bits good trees buffers pointer cursor room
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [eq] at sizes storage
  obtain ⟨before, get, _writable, _bound, _outside⟩ := caller_raw_output good buffers pointer
  obtain ⟨next, getNext, size, untouched⟩ := flush_pending_run_output_interval good trees buffers pointer cursor room run live account get
  have frame : Frame h after (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b = ob) := by
    apply full_frame_weaken (storage.private_frame trees.base.pbuf)
    intro b changed
    rcases changed with root | owned | output
    · exact Or.inl (Or.inl root)
    · exact Or.inl (Or.inr owned)
    · exact Or.inr output
  have readonly : after.ro ob = h.ro ob := sizes.ro (.blk ob)
  rw [pointer]
  exact raw_buffer_frame_of_interval frame storage.shape good.uniq get getNext readonly size untouched

end Zlib.Deflate.Engine.Proofs
