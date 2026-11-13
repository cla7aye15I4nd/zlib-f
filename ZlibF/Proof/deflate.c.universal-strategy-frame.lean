import ZlibF.Proof.«deflate.c.universal-strategies»
import ZlibF.Proof.«deflate.c.universal-outframe»
import ZlibF.Proof.«deflate.c.engine.raw-output-interval»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-buffer-frame-adjacent»

/-!
# deflate.c: the call frame of the strategies (batch B)

`deflate_call` needs, from each strategy, the frame of `CallFrame`: the input and output counts
and totals, and a heap frame in which only the stream record, the stream's own blocks and the
written part `[next_out, next_out + produced)` of the caller's output change. This file composes
such frames: adjacent output intervals, steps that write no output (`fill_window`), and steps that
change only the stream's own storage.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- What a part of a strategy contributes to its call frame: the call frame and the heap shape. -/
def StratFrame (h after : Heap) (r : ZStreamRef) (ds : Nat) (d : DeflateState) (z z' : ZStream)
    (used produced : Nat) : Prop :=
  CallFrame h after r ds d z z' used produced ∧ Zlib.Deflate.Proofs.Shape h after

theorem live_change_none_trans {h m k : Heap} (one : LiveChange h m (fun _ => False) (fun _ => False))
    (two : LiveChange m k (fun _ => False) (fun _ => False)) : LiveChange h k (fun _ => False) (fun _ => False) := by
  intro b
  rw [two b, one b]
  simp

/-- Two adjacent parts of a strategy run compose; the second may start from a state with the same
owned blocks. -/
theorem StratFrame.trans {h m k : Heap} {r : ZStreamRef} {ds : Nat} {d d1 : DeflateState}
    {z z1 z2 : ZStream} {u1 p1 u2 p2 : Nat}
    (one : StratFrame h m r ds d z z1 u1 p1) (two : StratFrame m k r ds d1 z1 z2 u2 p2)
    (owned : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b) (unique : Uniq h)
    (target : z.next_out = .null ∨
      (∃ ob oo arr, z.next_out = .ref (.blk ob) oo ∧ h.bytes ob = some arr ∧
        ¬ (StreamRoot r ob ∨ DeflateOwned ds d ob)) ∨
      (∃ owner oo foreign, z.next_out = .ref (.dstate_depth owner) oo ∧ h.dstates owner = some foreign ∧
        ¬ (StreamRoot r owner ∨ DeflateOwned ds d owner))) :
    StratFrame h k r ds d z z2 (u1 + u2) (p1 + p2) := by
  obtain ⟨⟨acc1, tin1, tout1, buf1, live1, alloc1⟩, shape1⟩ := one
  obtain ⟨⟨acc2, tin2, tout2, buf2, live2, alloc2⟩, shape2⟩ := two
  have same : (fun b => StreamRoot r b ∨ DeflateOwned ds d1 b) = (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
    funext b; rw [owned b]
  rw [same] at buf2
  have next1 : z1.next_out = advance z.next_out p1 := acc1.2.2.2.2.2.1
  rw [next1] at buf2
  refine ⟨⟨stream_accounting_trans acc1 acc2, ?_, ?_, ?_, live_change_none_trans live1 live2, alloc2.trans alloc1⟩,
    shape1.trans shape2⟩
  · rw [tin2, tin1, UInt64.ofNat_add, UInt64.add_assoc]
  · rw [tout2, tout1, UInt64.ofNat_add, UInt64.add_assoc]
  · rcases target with null | ⟨ob, oo, arr, ptr, get, outside⟩ | ⟨owner, oo, foreign, ptr, get, outside⟩
    · rw [null] at buf1 buf2 ⊢
      have f1 : Frame h m (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        simpa only [restoreRegions, List.foldl_cons, List.foldl_nil] using buf1.1
      have f2 : Frame m k (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, advance] using buf2.1
      exact null_output_buffer_frame (full_frame_trans_shape f1 f2 shape1)
    · rw [ptr] at buf1 buf2 ⊢
      exact raw_buffer_frame_adjacent buf1 buf2 shape1 shape2 unique get outside
    · rw [ptr] at buf1 buf2 ⊢
      exact foreign_buffer_frame_adjacent buf1 buf2 shape1 shape2 unique get outside

/-- A part that writes no output and changes only the stream record and the stream's own blocks. -/
theorem strat_frame_private {h after : Heap} {r : ZStreamRef} {ds : Nat} {d : DeflateState} {z z' : ZStream}
    {used : Nat} (account : StreamAccounting z z' used 0)
    (totalIn : z'.total_in = z.total_in + UInt64.ofNat used) (totalOut : z'.total_out = z.total_out)
    (frame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b))
    (shape : Zlib.Deflate.Proofs.Shape h after) (live : LiveChange h after (fun _ => False) (fun _ => False))
    (nalloc : after.nalloc = h.nalloc) (unique : Uniq h)
    (target : z.next_out = .null ∨
      (∃ ob oo arr, z.next_out = .ref (.blk ob) oo ∧ h.bytes ob = some arr ∧
        ¬ (StreamRoot r ob ∨ DeflateOwned ds d ob)) ∨
      (∃ owner oo foreign, z.next_out = .ref (.dstate_depth owner) oo ∧ h.dstates owner = some foreign ∧
        ¬ (StreamRoot r owner ∨ DeflateOwned ds d owner))) :
    StratFrame h after r ds d z z' used 0 := by
  refine ⟨⟨account, totalIn, by rw [totalOut]; simp, ?_, live, nalloc⟩, shape⟩
  have slots := frame.2.2.2.2.2
  rcases target with null | ⟨ob, oo, arr, ptr, get, outside⟩ | ⟨owner, oo, foreign, ptr, get, outside⟩
  · rw [null]; exact null_output_buffer_frame frame
  · rw [ptr]
    have liveOb : h.live ob := by simp [Heap.live, get]
    obtain ⟨b1, _, _, _, _, _, _, ro1⟩ := slots ob liveOb outside
    exact raw_buffer_frame_of_interval (full_frame_weaken frame (fun _ c => Or.inl c)) shape unique get
      (by rw [b1]; exact get) ro1 rfl (fun _ _ _ => rfl)
  · rw [ptr]
    have liveO : h.live owner := by simp [Heap.live, get]
    obtain ⟨_, _, _, _, ds1, _, _, ro1⟩ := slots owner liveO outside
    refine foreign_buffer_frame_of_fields (full_frame_weaken frame (fun _ c => Or.inl c)) shape unique get
      (fun f g => ⟨f, by rw [ds1]; exact g, rfl⟩) ro1 ?_
    intro before g
    refine ⟨before, ?_, rfl, fun _ _ _ => rfl⟩
    change (after.dstates owner).map (·.depth) = some before
    rw [ds1]; exact g

/-- **`fill_window` in the call frame**: it reads input and writes no output. -/
theorem fill_strat_frame {roll : Prop} {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d result : DeflateState} (good : DGood h r ds z d) (post : FillPost roll h after r ds z z' d result)
    (buffers : StreamBuffers h r) :
    ∃ used, StratFrame h after r ds d z z' used 0 := by
  obtain ⟨used, account, _⟩ := post.account
  have totals : z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out := by
    rcases post.stream with same | ⟨n, ref, io, ia, pointer, data, bound, count, value⟩
    · subst same
      have : used = 0 := by have := account.2.2.1; omega
      subst this
      exact ⟨by simp, rfl⟩
    · have a2 := read_stream_accounting z n ref io
        (checksumValue d.wrap z.adler ((ia.toList.drop io).take n.toNat)) pointer count
      rw [← value] at a2
      have : used = n.toNat := by have := account.2.2.1; have := a2.2.2.1; omega
      subst this
      rw [value]
      exact ⟨by simp [readStream], rfl⟩
  exact ⟨used, strat_frame_private account totals.1 totals.2 post.frame post.shape post.live post.nalloc
    good.uniq (output_target good buffers)⟩

end Zlib.Deflate.Universal
