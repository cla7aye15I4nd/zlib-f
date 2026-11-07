import ZlibF.Proof.«trees.c.arrays»
import ZlibF.Proof.«trees.c.emit»
import ZlibF.Proof.«trees.c.runs»
import ZlibF.Proof.«trees.c.monad»

/-! # trees.c: exact heap/output states between actual bit-writing calls -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- Direct state facts for a prefix of actual bit-writing calls. There are
no called-function contracts in this representation. -/
structure EmitState (id b : Nat) (h0 : Heap) (d0 : DeflateState) (buf0 : Array UInt8)
    (w : List Bool) (h : Heap) (d : DeflateState) (buf : Array UInt8) : Prop where
  heap : h = setD (setB h0 b buf) id d
  inv : TreesInvAt h id d b buf
  bits : outBits buf d = outBits buf0 d0 ++ w
  size : buf.size = buf0.size
  frame : ∀ i, (i < d0.pending.toNat ∨ d.pending.toNat ≤ i) → buf.getD i 0 = buf0.getD i 0
  lower : d0.pending.toNat ≤ d.pending.toNat
  fields : BitsDiff d0 d

/-- Start a trace at the actual caller heap. -/
theorem EmitState.start {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) : EmitState id b h d buf [] h d buf := by
  refine ⟨?_, hI, by simp, rfl, fun _ _ => rfl, Nat.le_refl _, BitsDiff.refl d⟩
  rw [setB_self hI.base.bytes, setD_self hI.base.dstate]

/-- Compose a proved actual emission with the already recorded prefix. -/
theorem EmitState.step {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w v : List Bool} {m : M Unit} {k : Nat} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (he : Emit id b m h d buf v k) :
    ∃ h' d' buf', m h = .ok ((), h') ∧ EmitState id b h0 d0 buf0 (w ++ v) h' d' buf' := by
  obtain ⟨buf', d', hr, hi, ho, hs, hf, hlo, hhi, hd⟩ := he
  refine ⟨_, d', buf', hr, ?_, hi, ?_, hs.trans ht.size, ?_, by have := ht.lower; omega, ht.fields.trans hd⟩
  · rw [ht.heap, setB_setD, setB_setB, setD_setD]
  · rw [ho, ht.bits, List.append_assoc]
  · intro i hidx
    rw [hf i (by have := ht.lower; omega), ht.frame i (by omega)]

/-- The source record arrays remain exactly those of the initial heap. -/
theorem EmitState.tree_arrays {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) :
    d.dyn_ltree = d0.dyn_ltree ∧ d.dyn_dtree = d0.dyn_dtree ∧ d.bl_tree = d0.bl_tree := by
  obtain ⟨p, a, v, u, he⟩ := ht.fields
  rw [he]
  exact ⟨rfl, rfl, rfl⟩

/-- Transport a total bit-room bound to an actual intermediate state. -/
theorem EmitState.room {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (n total : Nat)
    (hp : w.length + n ≤ total)
    (hr : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + total ≤ 8 * buf0.size) :
    8 * d.pending.toNat + d.bi_valid.toInt.toNat + n ≤ 8 * buf.size := by
  have hc := congrArg List.length ht.bits
  simp only [outBits_length, List.length_append] at hc
  rw [ht.size]
  omega

/-- Turn a complete actual run and its trace into the existing emission
relation. The byte bound follows from exact output length. -/
theorem EmitState.emit {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} {m : M Unit} (ht : EmitState id b h0 d0 buf0 w h d buf)
    (hr : m h0 = .ok ((), h)) :
    Emit id b m h0 d0 buf0 w (d0.bi_valid.toInt.toNat + w.length) := by
  have hc := congrArg List.length ht.bits
  simp only [outBits_length, List.length_append] at hc
  refine ⟨buf, d, ?_, ?_, ht.bits, ht.size, ht.frame, ht.lower, by omega, ht.fields⟩
  · rw [← ht.heap]
    exact hr
  · rw [← ht.heap]
    exact ht.inv

/-- A terminating actual computation and its returned value/heap facts. -/
def EWP {α : Type} (m : M α) (h : Heap) (Q : α → Heap → Prop) : Prop :=
  ∃ a h', m h = .ok (a, h') ∧ Q a h'

theorem EWP.pure {α : Type} {h : Heap} {a : α} {Q : α → Heap → Prop}
    (hq : Q a h) : EWP (pure a) h Q := ⟨a, h, rfl, hq⟩

theorem EWP.bind {α β : Type} {h : Heap} {m : M α} {f : α → M β}
    {P : α → Heap → Prop} {Q : β → Heap → Prop}
    (hm : EWP m h P) (hf : ∀ a h', P a h' → EWP (f a) h' Q) :
    EWP (m >>= f) h Q := by
  obtain ⟨a, h', hr, hp⟩ := hm
  obtain ⟨v, h'', hs, hq⟩ := hf a h' hp
  exact ⟨v, h'', by rw [bind_app, hr]; exact hs, hq⟩

theorem EWP.read {α β : Type} {h : Heap} {m : M α} {f : α → M β} {a : α}
    {Q : β → Heap → Prop} (hr : m h = .ok (a, h)) (hf : EWP (f a) h Q) :
    EWP (m >>= f) h Q := by
  refine EWP.bind (P := fun a' h' => a' = a ∧ h' = h) ⟨a, h, hr, rfl, rfl⟩ ?_
  rintro _ _ ⟨rfl, rfl⟩
  exact hf

theorem EWP.mono {α : Type} {h : Heap} {m : M α} {P Q : α → Heap → Prop}
    (hm : EWP m h P) (hf : ∀ a h', P a h' → Q a h') : EWP m h Q := by
  obtain ⟨a, h', hr, hp⟩ := hm
  exact ⟨a, h', hr, hf a h' hp⟩

/-- Stored code words and lengths, observed without changing them. -/
def blWords (d : DeflateState) (k : Nat) : UInt16 × UInt16 :=
  (d.bl_tree[k]!.fc, d.bl_tree[k]!.dl)

/-- Only scalar code data, not a called-function contract. -/
def CodeFits (t : Nat → UInt16 × UInt16) (k : Nat) : Prop :=
  (t k).2.toNat ≤ 15 ∧ (t k).1.toNat < 2 ^ (t k).2.toNat

/-- The actual bit-length-tree pointer and both entry loads are executed.
Source arrays are transported by the recorded write frame. -/
theorem EmitState.bl_code {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (k : Nat) (hk : k < 19)
    (hc : CodeFits (blWords d0) k)
    (hr : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + (blWords d0 k).2.toNat ≤ 8 * buf.size) :
    EWP (do send_code (some (.tab id)) (k : Int) (← pBltree (some (.tab id)))) h
      (fun _ h' => ∃ d' buf', EmitState id b h0 d0 buf0 (w ++ codeBits (blWords d0) k) h' d' buf') := by
  have hB : 19 ≤ d.bl_tree.size := by have := ht.inv.base.wf.2.2.1; omega
  have heq := ht.tree_arrays.2.2
  have hdl := getDl_sel ht.inv.base.dstate .bl (i := k) (by exact Nat.lt_of_lt_of_le hk hB)
  have hfc := getFc_sel ht.inv.base.dstate .bl (i := k) (by exact Nat.lt_of_lt_of_le hk hB)
  change getDl (.ref (.dstate_bl_tree id) 0) (k : Int) h = .ok (d.bl_tree[k]!.dl, h) at hdl
  change getFc (.ref (.dstate_bl_tree id) 0) (k : Int) h = .ok (d.bl_tree[k]!.fc, h) at hfc
  rw [heq] at hdl hfc
  obtain ⟨h', d', buf', hs, ht'⟩ := ht.step
    (send_code_emit ht.inv (k : Int) (.ref (.dstate_bl_tree id) 0) _ _ hdl hfc hc.1 hc.2 hr)
  refine ⟨(), h', ?_, d', buf', ht'⟩
  rw [bind_app, pBltree_run ht.inv.base.dstate]
  exact hs

/-- Actual extra-bit emission preserves the same exact heap frame. -/
theorem EmitState.extra_bits {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (value len : Int32) (V L : Nat)
    (hV : v16 value = V) (hL : len.toInt.toNat = L) (hl0 : 0 ≤ len.toInt) (hl15 : len.toInt ≤ 15)
    (hfit : V < 2 ^ L)
    (hr : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + L ≤ 8 * buf.size) :
    EWP (send_bits (some (.tab id)) value len) h
      (fun _ h' => ∃ d' buf', EmitState id b h0 d0 buf0 (w ++ natBits V L) h' d' buf') := by
  have he := send_bits_emit ht.inv value len hl0 hl15 (by rwa [hV, hL]) (by rwa [hL])
  rw [hV, hL] at he
  obtain ⟨h', d', buf', hs, ht'⟩ := ht.step he
  exact ⟨(), h', hs, d', buf', ht'⟩

end Zlib.Trees.Proofs.Out
