import ZlibF.Proof.«deflate.c.universal-call-entry-all»
import ZlibF.Proof.«deflate.c.universal-call-clauses»
import ZlibF.Proof.«deflate.c.engine.full-storage»
import ZlibF.Proof.«deflate.c.engine.read-zlib»
import ZlibF.Proof.«inflate.c.fast-writeback-frame»
import ZlibF.Proof.«deflate.c.universal-stored-io»

/-!
# deflate.c: the early returns of one `deflate` call

Owner 2 of the deflate split (`deflate_call`). The calls that return from the entry phase
without using input or writing output: an invalid flush value (nothing changes), a refusal
(`Z_STREAM_ERROR`, `msg` set) and a full output (`Z_BUF_ERROR`, `msg` set). Each gives `DInv`
afterwards and every clause of `CallClauses`.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-! ## Frames of a change that leaves every byte view -/

theorem frame_mono {h h' : Heap} {small large : Nat → Prop} (frame : Frame h h' small)
    (sub : ∀ b, small b → large b) : Frame h h' large := by
  obtain ⟨a, b, c, d, e, f⟩ := frame
  exact ⟨a, b, c, d, e, fun x live out => f x live (fun s => out (sub x s))⟩

theorem frame_self (h : Heap) (changed : Nat → Prop) : Frame h h changed :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- A frame that leaves every byte view is a buffer frame for any regions. -/
theorem buffer_frame_views {h after : Heap} {changed : Nat → Prop} {regions : List Region}
    (frame : Frame h after changed) (views : ∀ ref : BRef, Space.get after ref = Space.get h ref) :
    BufferFrame h after changed regions := by
  refine ⟨?_, fun region _ ref off a _ get => ⟨a, (views ref).trans get, rfl, fun _ _ _ => rfl⟩⟩
  rw [Zlib.Inflate.Proofs.restoreRegions_unchanged views]
  exact frame

/-- An empty range at a caller pointer. -/
theorem bytes_empty {h : Heap} {p : BPtr} {n : Nat} (range : p = .null ∨ ∃ xs, Bytes h p n xs) :
    Bytes h p 0 [] := by
  rcases range with null | ⟨xs, bytes⟩
  · exact Or.inl ⟨null, rfl, rfl⟩
  · rcases bytes with ⟨null, _, _⟩ | ⟨ref, i, a, ptr, get, size, _⟩
    · exact Or.inl ⟨null, rfl, rfl⟩
    · exact Or.inr ⟨ref, i, a, ptr, get, by omega, by simp⟩

theorem bytes_views {h after : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} (bytes : Bytes h p n xs)
    (views : ∀ ref : BRef, Space.get after ref = Space.get h ref) : Bytes after p n xs := by
  rcases bytes with null | ⟨ref, i, a, ptr, get, size, values⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, i, a, ptr, (views ref).trans get, size, values⟩

/-- The heap facts of an early return: no input used, no output, only `msg` of the stream record
changed, and a change that keeps every byte view and the allocations. -/
theorem early_frame {h after : Heap} {r : ZStreamRef} {z z' : ZStream} {changed : Nat → Prop}
    (buffers : StreamBuffers h r) (hz : r.get h = some z) (frame : Frame h after changed)
    (views : ∀ ref : BRef, Space.get after ref = Space.get h ref)
    (live : ∀ b, after.live b ↔ h.live b) (nalloc : after.nalloc = h.nalloc)
    (same : z' = { z with msg := z'.msg }) :
    StreamAccounting z z' 0 ([] : List UInt8).length ∧ Bytes after z.next_out ([] : List UInt8).length [] ∧
    z'.total_in = z.total_in + UInt64.ofNat 0 ∧
    z'.total_out = z.total_out + UInt64.ofNat ([] : List UInt8).length ∧
    (z'.data_type = z.data_type ∨ (z.data_type = Z_UNKNOWN ∧ (z'.data_type = Z_BINARY ∨ z'.data_type = Z_TEXT))) ∧
    BufferFrame h after changed [⟨z.next_out, ([] : List UInt8).length⟩] ∧
    LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc := by
  obtain ⟨z0, get0, _, outRange, _⟩ := buffers
  have zEq : z0 = z := Option.some.inj (get0.symm.trans hz)
  subst zEq
  rw [same]
  refine ⟨?_, ?_, by simp, by simp, Or.inl rfl, buffer_frame_views frame views, fun b => ?_, nalloc⟩
  · refine ⟨by simp, by simp, by simp, by simp, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · cases z0.next_in <;> rfl
    · cases z0.next_out <;> rfl
  · have range : z0.next_out = .null ∨ ∃ xs, Bytes h z0.next_out z0.avail_out.toNat xs := by
      rcases outRange with null | ⟨bytes, _, _⟩
      · exact Or.inl null
      · exact Or.inr bytes
    exact bytes_views (bytes_empty range) views
  · rw [live b]; simp

/-- The invariant after a change of the stream record that keeps its pointers and allocators,
on a heap with the same bytes, words and static tables. -/
theorem _root_.Zlib.Deflate.Universal.DInv.restream {h h' : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (good' : DGood h' r ds z' d) (alloc : DefAlloc z')
    (static : h'.static = h.static) (bytes : h'.bytes = h.bytes) (words : h'.words = h.words) :
    DInv h' r ds z' d := by
  obtain ⟨_, _, globals, shape, hashing, symbols⟩ := inv
  refine ⟨good', alloc, ?_, shape, ?_, ?_⟩
  · unfold LibraryGlobals at *; rw [static]; exact globals
  · obtain ⟨chains, slid, rolling⟩ := hashing
    refine ⟨fun zero => ?_, fun one => ?_, fun s2 s3 three => ?_⟩
    · obtain ⟨w, p, q, wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := chains zero
      exact ⟨w, p, q, wa, pa, qa, ew, ep, eq, by rw [bytes]; exact hw, by rw [words]; exact hp,
        by rw [words]; exact hq, H⟩
    · obtain ⟨w, p, q, wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := slid one
      exact ⟨w, p, q, wa, pa, qa, ew, ep, eq, by rw [bytes]; exact hw, by rw [words]; exact hp,
        by rw [words]; exact hq, H⟩
    · obtain ⟨w, wa, ew, hw, form⟩ := rolling s2 s3 three
      exact ⟨w, wa, ew, by rw [bytes]; exact hw, form⟩
  · obtain ⟨⟨xs, ⟨b, a, pbuf, hb, ledger⟩, near⟩, clear, below⟩ := symbols
    exact ⟨⟨xs, ⟨b, a, pbuf, by rw [bytes]; exact hb, ledger⟩, near⟩, clear, below⟩

/-- The invariant after `ERR_RETURN`, which stores only `msg`. -/
theorem _root_.Zlib.Deflate.Universal.DInv.message {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (m : BPtr) : DInv (r.put h { z with msg := m }) r ds { z with msg := m } d :=
  inv.restream (Zlib.Deflate.Engine.Proofs.good_stream_put inv.good _ rfl rfl rfl) inv.alloc
    (ZStreamRef.put_static h r _) (ZStreamRef.put_bytes h r _) (ZStreamRef.put_words h r _)

/-- The heap facts of a store of `msg`. -/
theorem message_heap {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (m : BPtr) :
    Frame h (r.put h { z with msg := m }) (StreamRoot r) ∧
    (∀ ref : BRef, Space.get (r.put h { z with msg := m }) ref = Space.get h ref) ∧
    (∀ b, (r.put h { z with msg := m }).live b ↔ h.live b) ∧ (r.put h { z with msg := m }).nalloc = h.nalloc := by
  refine ⟨stream_store_full_frame h r _, fun ref => byte_get_stream_put h r _ ref, fun b => ?_, by simp⟩
  have := full_shape_live_change (shape_put hz { z with msg := m }) b
  simpa using this

/-! ## The three early returns -/

theorem ne_codes : Z_STREAM_ERROR ≠ Z_OK ∧ Z_STREAM_ERROR ≠ Z_STREAM_END ∧ Z_STREAM_ERROR ≠ Z_BUF_ERROR ∧
    Z_BUF_ERROR ≠ Z_OK ∧ Z_BUF_ERROR ≠ Z_STREAM_END ∧ Z_BUF_ERROR ≠ Z_STREAM_ERROR := by decide

/-- **An invalid flush value**: `Z_STREAM_ERROR`, nothing changes. -/
theorem call_invalid {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (bad : flush.toInt < 0 ∨ 5 < flush.toInt) :
    C.run (deflate (some r) flush) h = .ok (Z_STREAM_ERROR, h) ∧ DInv h r ds z d ∧
      CallClauses h r ds z d flush Z_STREAM_ERROR h z d 0 [] := by
  obtain ⟨se_ok, se_end, se_buf, _, _, _⟩ := ne_codes
  have refuses : DeflateRefuses z d flush := by
    rcases bad with b | b
    · exact Or.inl b
    · exact Or.inr (Or.inl b)
  have run : C.run (deflate (some r) flush) h = .ok (Z_STREAM_ERROR, h) := by
    rw [C.run, deflate_phases]; exact entry_invalid inv.good bad _
  obtain ⟨acc, bytes, tin, tout, data, frame, live, nalloc⟩ :=
    early_frame (z' := z) (changed := fun b => StreamRoot r b ∨ DeflateOwned ds d b) buffers inv.good.live.hz
      (frame_self h _) (fun _ => rfl) (fun _ => Iff.rfl) rfl rfl
  refine ⟨run, inv, ⟨acc, bytes, tin, tout, Or.inr (Or.inr (Or.inl rfl)), ⟨fun _ => refuses, fun _ => rfl⟩,
    fun _ => ⟨rfl, rfl⟩, fun e => absurd e se_end, fun e => absurd e se_buf, fun nr => absurd refuses nr,
    fun nr => absurd refuses nr, fun _ nr => absurd refuses nr,
    fun e => by rcases e with e | e; exact absurd e se_ok; exact absurd e se_end,
    fun e => absurd e se_buf, fun _ lo hi => absurd bad (by omega), data, frame, live, nalloc⟩,
    fun _ => Iff.rfl, fun nr => absurd refuses nr⟩

/-- **A refused call with a valid flush value**: `Z_STREAM_ERROR`, only `msg` changes. -/
theorem call_refused {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (lower : 0 ≤ flush.toInt) (upper : flush.toInt ≤ 5)
    (refuses : DeflateRefuses z d flush) :
    ∃ m, C.run (deflate (some r) flush) h = .ok (Z_STREAM_ERROR, r.put h { z with msg := m }) ∧
      DInv (r.put h { z with msg := m }) r ds { z with msg := m } d ∧
      CallClauses h r ds z d flush Z_STREAM_ERROR (r.put h { z with msg := m }) { z with msg := m } d 0 [] := by
  obtain ⟨se_ok, se_end, se_buf, _, _, _⟩ := ne_codes
  obtain ⟨i, entry, text⟩ := entry_refused inv.good lower upper refuses
    (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))
  have run : C.run (deflate (some r) flush) h = .ok (Z_STREAM_ERROR, r.put h { z with msg := .ref (.str i) 0 }) := by
    rw [C.run, deflate_phases]; exact entry
  obtain ⟨fr, views, lv, na⟩ := message_heap inv.good.live.hz (.ref (.str i) 0)
  obtain ⟨acc, bytes, tin, tout, data, frame, live, nalloc⟩ :=
    early_frame (z' := { z with msg := .ref (.str i) 0 }) buffers inv.good.live.hz
      (frame_mono fr (fun b e => Or.inl (b := DeflateOwned ds d b) e)) views lv na rfl
  refine ⟨.ref (.str i) 0, run, inv.message _, ⟨acc, bytes, tin, tout, Or.inr (Or.inr (Or.inl rfl)),
    ⟨fun _ => refuses, fun _ => rfl⟩,
    fun b => absurd b (by omega), fun e => absurd e se_end, fun e => absurd e se_buf, fun nr => absurd refuses nr,
    fun nr => absurd refuses nr, fun _ nr => absurd refuses nr,
    fun e => by rcases e with e | e; exact absurd e se_ok; exact absurd e se_end,
    fun e => absurd e se_buf, fun _ _ _ => static_of_table _ text, data, frame, live, nalloc⟩,
    fun _ => Iff.rfl, fun nr => absurd refuses nr⟩

/-- **An accepted call with a full output**: `Z_BUF_ERROR`, only `msg` changes. -/
theorem call_full {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (accepted : ¬ DeflateRefuses z d flush)
    (full : z.avail_out = 0) :
    ∃ m, C.run (deflate (some r) flush) h = .ok (Z_BUF_ERROR, r.put h { z with msg := m }) ∧
      DInv (r.put h { z with msg := m }) r ds { z with msg := m } d ∧
      CallClauses h r ds z d flush Z_BUF_ERROR (r.put h { z with msg := m }) { z with msg := m } d 0 [] := by
  obtain ⟨_, _, _, buf_ok, buf_end, buf_se⟩ := ne_codes
  obtain ⟨i, entry, text⟩ := entry_full inv.good accepted full
    (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))
  have run : C.run (deflate (some r) flush) h = .ok (Z_BUF_ERROR, r.put h { z with msg := .ref (.str i) 0 }) := by
    rw [C.run, deflate_phases]; exact entry
  obtain ⟨fr, views, lv, na⟩ := message_heap inv.good.live.hz (.ref (.str i) 0)
  obtain ⟨acc, bytes, tin, tout, data, frame, live, nalloc⟩ :=
    early_frame (z' := { z with msg := .ref (.str i) 0 }) buffers inv.good.live.hz
      (frame_mono fr (fun b e => Or.inl (b := DeflateOwned ds d b) e)) views lv na rfl
  have invalid : ¬ (flush.toInt < 0 ∨ 5 < flush.toInt) := fun b => accepted (by
    rcases b with b | b
    · exact Or.inl b
    · exact Or.inr (Or.inl b))
  refine ⟨.ref (.str i) 0, run, inv.message _, ⟨acc, bytes, tin, tout, Or.inr (Or.inr (Or.inr rfl)),
    ⟨fun e => absurd e buf_se, fun rf => absurd rf accepted⟩,
    fun b => absurd b invalid, fun e => absurd e buf_end, fun _ => ⟨rfl, Or.inl rfl⟩, fun _ _ => rfl,
    fun _ ne => absurd full ne, fun _ _ ne => absurd full ne,
    fun e => by rcases e with e | e; exact absurd e buf_ok; exact absurd e buf_end,
    fun _ => static_of_table _ text, fun e => absurd e buf_se, data, frame, live, nalloc⟩,
    fun _ => Iff.rfl, fun _ ne => absurd full ne⟩

end Zlib.Deflate.Universal.Call
