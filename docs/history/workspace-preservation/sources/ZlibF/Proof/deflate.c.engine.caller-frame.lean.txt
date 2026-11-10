import ZlibF.Proof.«deflate.c.engine.rebuffer»
import ZlibF.Spec.Public.Streams

/-! # Caller byte ranges survive private compressor writes

The relation covers raw arrays, static tables and embedded depth arrays.
It is a proved heap relation, not an assumed callee specification.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

structure ByteFrame (before after : Heap) (changed : Nat → Prop) : Prop where
  static : after.static = before.static
  bytes : ∀ i, ¬ changed i → after.bytes i = before.bytes i
  dstates : ∀ i, ¬ changed i → after.dstates i = before.dstates i
  ro : ∀ i, ¬ changed i → after.ro i = before.ro i

theorem ByteFrame.refl (h : Heap) (changed : Nat → Prop) : ByteFrame h h changed :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem ByteFrame.trans {h g j : Heap} {changed : Nat → Prop}
    (first : ByteFrame h g changed) (second : ByteFrame g j changed) : ByteFrame h j changed :=
  ⟨second.static.trans first.static,
    fun i outside => (second.bytes i outside).trans (first.bytes i outside),
    fun i outside => (second.dstates i outside).trans (first.dstates i outside),
    fun i outside => (second.ro i outside).trans (first.ro i outside)⟩

theorem ByteFrame.weaken {h g : Heap} {small large : Nat → Prop}
    (frame : ByteFrame h g small) (includes : ∀ i, small i → large i) : ByteFrame h g large :=
  ⟨frame.static, fun i outside => frame.bytes i (fun hi => outside (includes i hi)),
    fun i outside => frame.dstates i (fun hi => outside (includes i hi)),
    fun i outside => frame.ro i (fun hi => outside (includes i hi))⟩

theorem byte_frame_setD (h : Heap) (ds : Nat) (d : DeflateState) :
    ByteFrame h (setD h ds d) (fun i => i = ds) := by
  refine ⟨rfl, fun _ _ => rfl, ?_, fun _ _ => rfl⟩
  intro i outside
  simp only [setD, upd_ne _ _ _ _ outside]

theorem byte_frame_setW (h : Heap) (q : Nat) (a : Array UInt16) (changed : Nat → Prop) :
    ByteFrame h (setW h q a) changed :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem byte_frame_setB (h : Heap) (b : Nat) (a : Array UInt8) :
    ByteFrame h (Zlib.Trees.Proofs.Out.setB h b a) (fun i => i = b) := by
  refine ⟨rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  intro i outside
  simp only [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ outside]

theorem byte_frame_put (h : Heap) (r : ZStreamRef) (z : ZStream) (changed : Nat → Prop) :
    ByteFrame h (r.put h z) changed := by
  exact ⟨by simp, by intro _ _; simp, by intro _ _; simp, by intro _ _; simp⟩

theorem ByteFrame.get {h g : Heap} {changed : Nat → Prop} (frame : ByteFrame h g changed)
    (ref : BRef) (off : Nat) (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b) :
    Space.get g ref = Space.get h ref := by
  cases ref with
  | blk b => exact frame.bytes b (outside b rfl)
  | dstate_depth b =>
    change (g.dstates b).map (·.depth) = (h.dstates b).map (·.depth)
    rw [frame.dstates b (outside b rfl)]
  | str i => rfl
  | st_dist_code => change some g.static.dist_code = some h.static.dist_code; rw [frame.static]
  | st_length_code => change some g.static.length_code = some h.static.length_code; rw [frame.static]

theorem ByteFrame.readonly {h g : Heap} {changed : Nat → Prop} (frame : ByteFrame h g changed)
    (ref : BRef) (off : Nat) (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b) :
    Space.ro g ref = Space.ro h ref := by
  cases ref with
  | blk b => exact frame.ro b (outside b rfl)
  | dstate_depth b => rfl
  | str i => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

/-- DGood identifies the exact private ownership graph. A fresh ownership
witness cannot introduce a different compressor state for this stream. -/
theorem stream_owned_deflate {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (b : Nat) : StreamOwned h r b ↔ DeflateOwned ds d b := by
  constructor
  · rintro ⟨z0, get, cases⟩
    have equal : z0 = z := Option.some.inj (get.symm.trans good.live.hz)
    subst z0
    rcases cases with ⟨i, s, kind, _, _⟩ | ⟨i, s, kind, state, owned⟩
    · rw [good.live.zst] at kind
      cases kind
    · have equal : ds = i := by simpa only [good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using kind
      subst i
      have equal : s = d := Option.some.inj (state.symm.trans good.live.hs)
      subst s
      exact owned
  · intro owned
    exact ⟨z, good.live.hz, Or.inr ⟨ds, d, good.live.zst, good.live.hs, owned⟩⟩

/-- The same five object keys retain ownership after scalar, symbol and
window updates. No stronger public buffer separation is imposed. -/
theorem stream_owned_keys {h g : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d result : DeflateState}
    (before : DGood h r ds z d) (after : DGood g r ds z' result)
    (window : result.window = d.window) (prev : result.prev = d.prev)
    (head : result.head = d.head) (pending : result.pending_buf = d.pending_buf) :
    ∀ b, StreamOwned g r b ↔ StreamOwned h r b := by
  intro b
  rw [stream_owned_deflate after, stream_owned_deflate before]
  simp only [DeflateOwned, window, prev, head, pending]

/-- Advancing an input cursor retains exactly a suffix of its admitted
range. All byte-reference variants keep their original object identity. -/
theorem caller_range_advance {h g : Heap} {r : ZStreamRef} {changed : Nat → Prop}
    {p : BPtr} {n used remaining : Nat} {write : Bool}
    (range : CallerRange h r p n write) (frame : ByteFrame h g changed)
    (ownedWrites : ∀ b, changed b → StreamOwned h r b)
    (owned : ∀ b, StreamOwned g r b ↔ StreamOwned h r b)
    (bound : used + remaining ≤ n) :
    CallerRange g r (advance p used) remaining write := by
  rcases range with null | ⟨⟨xs, bytes⟩, writable, unowned⟩
  · subst p
    exact Or.inl rfl
  · cases p with
    | null => exact Or.inl rfl
    | ref ref off =>
      have outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b := by
        intro b root change
        exact unowned b root (ownedWrites b change)
      have getFrame := frame.get ref off outside
      have roFrame := frame.readonly ref off outside
      rcases bytes with ⟨null, _, _⟩ | ⟨ref0, off0, a, pointer, get, size, values⟩
      · cases null
      · have equal : ref0 = ref ∧ off0 = off := by simpa only [Ptr.ref.injEq] using pointer.symm
        rcases equal with ⟨refEq, offEq⟩
        subst ref0 off0
        refine Or.inr ⟨⟨(a.toList.drop (off + used)).take remaining,
          Or.inr ⟨ref, off + used, a, rfl, getFrame.trans get, by omega, rfl⟩⟩, ?_, ?_⟩
        · intro yes
          rcases writable yes with ⟨null, _⟩ | ⟨ref1, off1, a1, pointer1, get1, ro, size1⟩
          · cases null
          · have equal : ref1 = ref ∧ off1 = off := by simpa only [Ptr.ref.injEq] using pointer1.symm
            rcases equal with ⟨refEq, offEq⟩
            subst ref1 off1
            exact Or.inr ⟨ref, off + used, a1, rfl, getFrame.trans get1, roFrame.trans ro, by omega⟩
        · intro b root
          have original : ByteRoot (.ref ref off) b := by cases ref <;> exact root
          intro now
          exact unowned b original ((owned b).mp now)

theorem separate_advance_left {p q : BPtr} {n m used remaining : Nat}
    (separate : Separate p n q m) (bound : used + remaining ≤ n) :
    Separate (advance p used) remaining q m := by
  rcases separate with empty | empty | disjoint
  · left
    omega
  · exact Or.inr (Or.inl empty)
  · right; right
    cases p <;> cases q <;> simp only [Separate, advance] at disjoint ⊢
    rcases disjoint with apart | before | after
    · exact Or.inl apart
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

theorem advance_zero (p : BPtr) : advance p 0 = p := by cases p <;> rfl

/-- Public input/output buffers are available again after a private-only
step that accepts input and produces no output. This is the transport
needed by the next non-flushing strategy iteration. -/
theorem stream_buffers_private_read {h g : Heap} {r : ZStreamRef} {z z' : ZStream}
    {changed : Nat → Prop} {used : Nat}
    (get : r.get h = some z) (getA : r.get g = some z')
    (buffers : StreamBuffers h r) (frame : ByteFrame h g changed)
    (ownedWrites : ∀ b, changed b → StreamOwned h r b)
    (owned : ∀ b, StreamOwned g r b ↔ StreamOwned h r b)
    (account : StreamAccounting z z' used 0) : StreamBuffers g r := by
  obtain ⟨old, get0, input, output, separate⟩ := buffers
  have equal : old = z := Option.some.inj (get0.symm.trans get)
  subst old
  have inputA := caller_range_advance (used := used) (remaining := z'.avail_in.toNat) input frame ownedWrites owned (by have count := account.2.2.1; omega)
  have outputA := caller_range_advance output frame ownedWrites owned (used := 0) (remaining := z'.avail_out.toNat)
    (by have count := account.2.2.2.1; omega)
  have inputPtr := account.2.2.2.2.1
  have outputPtr := account.2.2.2.2.2.1
  refine ⟨z', getA, ?_, ?_, ?_⟩
  · rw [inputPtr]
    exact inputA
  · rw [outputPtr]
    simpa only [advance] using outputA
  · have outputCount : z'.avail_out.toNat = z.avail_out.toNat := by
      have count := account.2.2.2.1
      omega
    rw [inputPtr, outputPtr, advance_zero, outputCount]
    exact separate_advance_left (used := used) (remaining := z'.avail_in.toNat) separate (by have count := account.2.2.1; omega)

/-- Successful actual insertion changes words and the one private state
record. It leaves every caller byte array and other state record alone. -/
theorem insert_string_byte_frame {h after : Heap} {ds w q p : Nat} {d : DeflateState}
    {wa : Array UInt8} {qa pa : Array UInt16} {value : UInt32}
    (state : h.dstates ds = some d) (env : HashEnv h d w q p wa qa pa)
    (str : UInt32) (fit : str.toNat + 2 < wa.size) (small : str.toNat + 2 < 2 ^ 32)
    (run : INSERT_STRING (some (.tab ds)) str h = .ok (value, after)) :
    ByteFrame h after (fun i => i = ds) := by
  obtain ⟨key, _, _, actual⟩ := INSERT_STRING_ok state env str fit small
  have same := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
  change after = _ at same
  rw [same]
  exact ⟨rfl, fun _ _ => rfl, fun i outside => by simp [upd_ne _ _ _ _ outside], fun _ _ => rfl⟩

theorem stream_accounting_zero (z : ZStream) : StreamAccounting z z 0 0 := by
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · cases z.next_in <;> rfl
  · cases z.next_out <;> rfl

/-- A real tally writes its pending byte array and its private state. -/
theorem pending_state_byte_frame (h : Heap) (ds b : Nat) (d result : DeflateState) (bytes : Array UInt8)
    (pending : d.pending_buf = .ref (.blk b) 0) :
    ByteFrame h (setD (Zlib.Trees.Proofs.Out.setB h b bytes) ds result) (DeflateOwned ds d) := by
  have pendingFrame : ByteFrame h (Zlib.Trees.Proofs.Out.setB h b bytes) (DeflateOwned ds d) :=
    (byte_frame_setB h b bytes).weaken (fun i equal => by
      subst i
      exact Or.inr (Or.inr (Or.inr (Or.inr pending))))
  exact pendingFrame.trans ((byte_frame_setD _ ds result).weaken (fun _ equal => Or.inl equal))

end Zlib.Deflate.Engine.Proofs
