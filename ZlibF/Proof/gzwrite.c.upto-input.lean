import ZlibF.Proof.«gzwrite.c.init»
import ZlibF.Proof.«gzlib.c.error-borrow»

/-!
# gzwrite.c: the writer invariant up to the pending input, and `gz_error` on it

`gz_comp`, `gz_write`, `gz_zero` and `gz_vacate` work on a handle whose embedded deflate stream may have pending
input in a caller region: `next_in` points into the caller's buffer and `avail_in ≠ 0`. The full invariant `GzInv`
does not hold then (its writer part wants the input inside the handle's `in` buffer). The invariant they keep is
`GzInvUpToInput`: `GzInv` of the record with no pending input (`clearIn`), and `next_in` NULL with no pending
input, or the pending input inside a region `src`, which is the `in` buffer or a caller region the handle does not
own. `GzInvUpToInputWeak` drops the readability of a caller region (what holds after a failed write, `gz_comp`).

On their error paths these functions call `gz_error`. The fact on `gz_error` (`GzErrorSpec`, with its no-grab fact
`GzErrorOwn`) takes `GzInv` on the actual heap. This file transfers it.

1. **Commutation.** `gz_error` never reads or writes the field `strm` of the record: it reads `err`, `msg`, `path`,
   writes `err` and `msg`, and its library calls (`strlen`, `malloc`, `free`, `snprintf`) do not touch a gz record.
   So a run on a heap whose record `i` has another `strm` is the same run, with that `strm` put back
   (`gz_error_setStrm`). The proof steps through the translation statement by statement.
2. **Interface.** `gz_error_upToInput` and `gz_error_upToInputWeak`: `gz_error` keeps the invariant up to the
   pending input, with the frame, the allocation ledger and the no-grab fact of `GzErrorSpec` and `GzErrorOwn`.
   The caller region keeps its bytes: `gz_error` frees only the old message, which the region is not in, and it
   does not change the `strerror` borrow (`gz_error_borrow_stable`).

`GzErrorSpec` and `GzErrorOwn` are premises, as in `gzwrite.c.init`.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public Zlib.Gzwrite.SafeInit
set_option autoImplicit false

/-! ## The shared definitions of the write side -/

/-- The record with no pending input (`avail_in = 0`, `next_in` NULL), which meets W4 whatever `next_in` was. -/
def clearIn (s : GzState) : GzState := { s with strm := { s.strm with avail_in := 0, next_in := .null } }

/-- **The writer invariant up to the pending input**: `GzInv` of the record with no pending input, and the pending
input lies in `src`, which is the `in` buffer or a caller region the handle does not own. -/
def GzInvUpToInput (h : Heap) (i : Nat) (s : GzState) (src : Region) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearIn s)) i (clearIn s) ∧ s.mode = GZ_WRITE ∧
  ((s.strm.next_in = .null ∧ s.strm.avail_in = 0) ∨
    ∃ a, s.strm.next_in = padv src.pointer a ∧ a + s.strm.avail_in.toNat ≤ src.length) ∧
  (src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨
    (∃ xs, Bytes h src.pointer src.length xs) ∧ ∀ b, ByteRoot src.pointer b → ¬ GzOwned h i s b)

/-- `GzInvUpToInput` without the readability of a caller region: what holds after `gz_comp` fails. A failed write
calls `gz_error(Z_ERRNO, zstrerror())`, and `zstrerror` invalidates a borrowed `strerror` view, which a caller may
have passed as the input region; the C does not read the input after `-1` (`gz_write` resets `next_in` to `in`). -/
def GzInvUpToInputWeak (h : Heap) (i : Nat) (s : GzState) (src : Region) : Prop :=
  h.gzstates i = some s ∧ GzInv (putGz h i (clearIn s)) i (clearIn s) ∧ s.mode = GZ_WRITE ∧
  ((s.strm.next_in = .null ∧ s.strm.avail_in = 0) ∨
    ∃ a, s.strm.next_in = padv src.pointer a ∧ a + s.strm.avail_in.toNat ≤ src.length) ∧
  (src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨ ∀ b, ByteRoot src.pointer b → ¬ GzOwned h i s b)

/-! ## Replacing the stream of record `i` -/

/-- The table with the stream of record `i` replaced by `z` (no record is created). -/
def strmAt (i : Nat) (z : ZStream) (g : Tbl (Option GzState)) : Tbl (Option GzState) :=
  upd g i ((g i).map fun v => { v with strm := z })

/-- The heap with the stream of record `i` replaced by `z`. -/
def setStrm (i : Nat) (z : ZStream) (h : Heap) : Heap := { h with gzstates := strmAt i z h.gzstates }

/-- A result with the stream of record `i` replaced by `z` in its heap. -/
def liftR {α : Type} (i : Nat) (z : ZStream) : Except Fault (α × Heap) → Except Fault (α × Heap)
  | .ok (a, h) => .ok (a, setStrm i z h)
  | .error e => .error e

/-- `m` neither reads nor writes the stream of record `i`: its run on a heap with the stream replaced is its run
with the stream replaced. -/
def Comm {α : Type} (i : Nat) (z : ZStream) (m : M α) : Prop :=
  ∀ h, m (setStrm i z h) = liftR i z (m h)

section Comm
variable {i : Nat} {z : ZStream}

@[simp] theorem setStrm_bytes (h : Heap) : (setStrm i z h).bytes = h.bytes := rfl
@[simp] theorem setStrm_ro (h : Heap) : (setStrm i z h).ro = h.ro := rfl
@[simp] theorem setStrm_nextBlk (h : Heap) : (setStrm i z h).nextBlk = h.nextBlk := rfl
@[simp] theorem setStrm_nalloc (h : Heap) : (setStrm i z h).nalloc = h.nalloc := rfl
@[simp] theorem setStrm_allocOk (h : Heap) : (setStrm i z h).allocOk = h.allocOk := rfl
@[simp] theorem setStrm_garbage (h : Heap) : (setStrm i z h).garbage = h.garbage := rfl

theorem strmAt_isSome (g : Tbl (Option GzState)) (b : Nat) : (strmAt i z g b).isSome = (g b).isSome := by
  unfold strmAt
  rw [upd_apply]
  by_cases hb : b = i
  · subst hb
    rw [if_pos rfl]
    cases g b <;> rfl
  · simp only [hb, if_false]

theorem slotUsed_setStrm (h : Heap) (b : Nat) : (setStrm i z h).slotUsed b = h.slotUsed b := by
  simp only [Heap.slotUsed, setStrm, strmAt_isSome]

theorem get_setStrm (h : Heap) (r : BRef) : Space.get (setStrm i z h) r = Space.get h r := by
  cases r <;> rfl

theorem ro_setStrm (h : Heap) (r : BRef) : Space.ro (setStrm i z h) r = Space.ro h r := by
  cases r <;> rfl

theorem modify_setStrm (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) :
    Space.modify (setStrm i z h) r f = setStrm i z (Space.modify h r f) := by
  cases r <;> rfl

theorem setStrm_gz_same (h : Heap) :
    (setStrm i z h).gzstates i = (h.gzstates i).map (fun v => { v with strm := z }) := by
  simp [setStrm, strmAt]

/-! ### Combinators -/

theorem Comm.pure {α : Type} (a : α) : Comm i z (pure a : M α) := fun _ => rfl

theorem Comm.bind {α β : Type} {m : M α} {f : α → M β} (hm : Comm i z m) (hf : ∀ a, Comm i z (f a)) :
    Comm i z (m >>= f) := by
  intro h
  simp only [bind_app]
  rw [hm h]
  cases m h with
  | error e => rfl
  | ok p =>
    obtain ⟨a, h1⟩ := p
    exact hf a h1

theorem Comm.ite {α : Type} (p : Prop) [Decidable p] {a b : M α} (ha : Comm i z a) (hb : Comm i z b) :
    Comm i z (if p then a else b) := by
  split <;> assumption

theorem Comm.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (comm : ∀ value member state, Comm i z (body value member state))
    (initial : β) : Comm i z (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact Comm.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply Comm.bind (comm head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact Comm.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => comm value (by simp [member]) state) next

/-! ### Library primitives -/

theorem comm_strlenB (p : BPtr) : Comm i z (strlenB p) := by
  intro h
  cases p with
  | null => rfl
  | ref r off =>
    simp only [strlenB, get_setStrm]
    cases Space.get h r with
    | none => rfl
    | some a =>
      dsimp only
      cases strlenFrom a off with
      | none => rfl
      | some j => rfl

theorem comm_strLitRef (s : String) : Comm i z (strLitRef s) := by
  intro h
  unfold strLitRef
  cases strIndex s <;> rfl

theorem comm_strLit (s : String) : Comm i z (Zlib.GzFs.strLit s) := comm_strLitRef s

theorem comm_allocB (n : Nat) : Comm i z (allocB n) := by
  intro h
  by_cases hn : n < mallocLimit
  · simp only [allocB, hn, and_true, setStrm_allocOk, setStrm_nalloc, setStrm_nextBlk, slotUsed_setStrm]
    cases h.allocOk h.nalloc <;> cases h.slotUsed h.nextBlk <;> rfl
  · simp only [allocB, hn, and_false, ite_false, setStrm_allocOk, setStrm_nalloc, setStrm_nextBlk]
    rfl

theorem comm_allocBytes (a : Array UInt8) : Comm i z (allocBytes a) := by
  intro h
  simp only [allocBytes, setStrm_nextBlk, slotUsed_setStrm]
  cases h.slotUsed h.nextBlk <;> rfl

theorem comm_freeB (p : BPtr) : Comm i z (freeB p) := by
  intro h
  cases p with
  | null => rfl
  | ref r off =>
    cases r with
    | blk b =>
      cases off with
      | zero =>
        simp only [freeB, setStrm_bytes, setStrm_ro]
        cases h.bytes b with
        | none => rfl
        | some a =>
          dsimp only
          by_cases hro : h.ro b = true
          · simp only [hro, if_true]; rfl
          · simp only [hro, if_false]; rfl
      | succ k => rfl
    | str _ => rfl
    | dstate_depth _ => rfl
    | st_dist_code => rfl
    | st_length_code => rfl

theorem comm_add (p : BPtr) (k : Int) : Comm i z (p.add k) := by
  intro h
  cases p with
  | null =>
    by_cases hk : k = 0
    · simp only [Ptr.add, hk, if_true]; rfl
    · simp only [Ptr.add, hk, if_false]; rfl
  | ref r off =>
    simp only [Ptr.add, get_setStrm]
    cases Space.get h r with
    | none => rfl
    | some a =>
      dsimp only
      by_cases hk : 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int)
      · simp only [hk, and_self, if_true]; rfl
      · simp only [hk, if_false]; rfl

theorem comm_load (p : BPtr) : Comm i z (Ptr.load p : M UInt8) := by
  intro h
  cases p with
  | null => rfl
  | ref r off =>
    simp only [Ptr.load, get_setStrm]
    cases Space.get h r with
    | none => rfl
    | some a =>
      dsimp only
      by_cases hk : off < a.size
      · simp only [hk, dite_true]; rfl
      · simp only [hk, dite_false]; rfl

theorem comm_index8 (p : BPtr) (k : Int) : Comm i z (index8 p k) := by
  unfold index8 Ptr.index
  exact Comm.bind (comm_add _ _) (fun _ => comm_load _)

theorem comm_store8 (p : BPtr) (v : UInt8) : Comm i z (store8 p v) := by
  intro h
  cases p with
  | null => rfl
  | ref r off =>
    simp only [store8, Ptr.store, get_setStrm, ro_setStrm, modify_setStrm]
    cases Space.get h r with
    | none => rfl
    | some a =>
      dsimp only
      cases Space.ro h r with
      | true => rfl
      | false =>
        by_cases hk : off < a.size
        · simp only [hk, if_true, Bool.false_eq_true, if_false]; rfl
        · simp only [hk, if_false, Bool.false_eq_true]; rfl

theorem comm_memcpyB (dst src : BPtr) (n : Nat) : Comm i z (memcpyB dst src n) := by
  intro h
  cases dst with
  | null => cases src <;> rfl
  | ref rd od =>
    cases src with
    | null => rfl
    | ref rs os =>
      simp only [memcpyB, Ptr.memcpy, get_setStrm, ro_setStrm, modify_setStrm]
      cases Space.get h rd with
      | none => cases Space.get h rs <;> rfl
      | some da =>
        cases Space.get h rs with
        | none => rfl
        | some sa =>
          dsimp only
          by_cases c1 : (Space.ro h rd && decide (n ≠ 0)) = true
          · simp only [c1, if_true]; rfl
          · simp only [c1, if_false]
            by_cases c2 : od + n ≤ da.size ∧ os + n ≤ sa.size
            · simp only [c2, and_self, if_true]
              by_cases c3 : rd ≠ rs ∨ od + n ≤ os ∨ os + n ≤ od
              · simp only [c3, if_true]; rfl
              · simp only [c3, if_false]; rfl
            · simp only [c2, if_false]; rfl

theorem comm_cstring (p : BPtr) : Comm i z (cstring p) := by
  unfold cstring
  apply Comm.bind (comm_strlenB p)
  intro n
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply Comm.bind
  · apply Comm.list_forIn
    intro value _ current
    apply Comm.bind (comm_index8 _ _)
    intro byte
    exact Comm.pure _
  · intro result
    exact Comm.pure _

theorem heapStr_setStrm (h : Heap) : heapStr (setStrm i z h) = heapStr h := by
  funext p
  unfold heapStr
  rw [comm_cstring p h]
  cases cstring p h with
  | error e => rfl
  | ok q => rfl

theorem comm_formatBytes (f : Array UInt8) (args : List VaArg) : Comm i z (formatBytes f args) := by
  intro h
  simp only [formatBytes, heapStr_setStrm]
  cases formatGo f (heapStr h) (f.size + 1) 0 args #[] <;> rfl

theorem comm_storeBytes (p : BPtr) (bs : Array UInt8) : Comm i z (storeBytes p bs) := by
  unfold storeBytes
  apply Comm.ite
  · exact Comm.pure _
  · apply Comm.bind (comm_allocBytes _)
    intro tmp
    apply Comm.bind (comm_memcpyB _ _ _)
    intro _
    exact comm_freeB _

theorem comm_snprintf (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) :
    Comm i z (snprintf dst size fmt args) := by
  unfold snprintf
  apply Comm.bind (comm_cstring _)
  intro f
  apply Comm.bind (comm_formatBytes _ _)
  intro out
  dsimp only
  apply Comm.ite
  · apply Comm.bind (comm_storeBytes _ _)
    intro _
    apply Comm.bind (comm_add _ _)
    intro q
    apply Comm.bind (comm_store8 _ _)
    intro _
    exact Comm.pure _
  · exact Comm.pure _

/-! ### The record `i` -/

/-- A load of record `i` sees the replaced stream; a continuation that does not read `strm` cannot tell. -/
theorem comm_ldS_bind {β : Type} {f : GzState → M β} (hf : ∀ v, Comm i z (f v))
    (hfz : ∀ v, f { v with strm := z } = f v) : Comm i z (ldS (some (.tab i)) >>= f) := by
  intro h
  simp only [bind_app]
  unfold ldS ldGzState
  simp only [GzStateRef.get, setStrm_gz_same]
  cases hg : h.gzstates i with
  | none => rfl
  | some v => exact (congrFun (hfz v) _).trans (hf v h)

/-- A write of record `i` through a field update that commutes with the replacement of `strm`. -/
theorem comm_updS (f : GzState → GzState) (hf : ∀ v, f { v with strm := z } = { f v with strm := z }) :
    Comm i z (updS (some (.tab i)) f) := by
  intro h
  rw [Zlib.Gzlib.Proofs.updS_eq, Zlib.Gzlib.Proofs.updS_eq, setStrm_gz_same]
  cases hg : h.gzstates i with
  | none => rfl
  | some v =>
    show Except.ok ((), Zlib.Gzlib.Spec.setS (setStrm i z h) i (f { v with strm := z })) =
      Except.ok ((), setStrm i z (Zlib.Gzlib.Spec.setS h i (f v)))
    rw [hf v]
    simp only [Zlib.Gzlib.Spec.setS, setStrm, strmAt, upd_upd, upd_same, Option.map]

theorem comm_updS_msg (m : BPtr) : Comm i z (updS (some (.tab i)) fun s => { s with msg := m }) :=
  comm_updS _ (fun _ => rfl)

theorem comm_updS_err (e : Int32) : Comm i z (updS (some (.tab i)) fun s => { s with err := e }) :=
  comm_updS _ (fun _ => rfl)

/-- Steps through a statement sequence of `gz_error`, one primitive at a time. -/
local macro "commstep" : tactic => `(tactic| repeat (first
  | with_reducible exact Comm.pure _
  | with_reducible exact comm_freeB _
  | with_reducible exact comm_updS_msg _
  | with_reducible exact comm_updS_err _
  | with_reducible exact comm_snprintf _ _ _ _
  | with_reducible apply Comm.ite
  | (with_reducible refine comm_ldS_bind (fun _ => ?_) (fun _ => by with_reducible rfl))
  | (with_reducible apply Comm.bind (comm_updS_msg _); intro _)
  | (with_reducible apply Comm.bind (comm_updS_err _); intro _)
  | (with_reducible apply Comm.bind (comm_strlenB _); intro _)
  | (with_reducible apply Comm.bind (comm_allocB _); intro _)
  | (with_reducible apply Comm.bind (comm_strLit _); intro _)
  | (with_reducible apply Comm.bind (comm_strLitRef _); intro _)
  | (with_reducible apply Comm.bind (comm_snprintf _ _ _ _); intro _)
  | (with_reducible apply Comm.bind (comm_freeB _); intro _)
  | dsimp only))

/-- **`gz_error` does not read or write `strm`.** Its run on a heap whose record `i` has the stream `z` is its run
on the heap, with the stream of the resulting record replaced by `z`: the same faults, the same results. -/
theorem gz_error_comm (e : Int32) (msg : BPtr) : Comm i z (Zlib.Gzlib.gz_error (some (.tab i)) e msg) := by
  unfold Zlib.Gzlib.gz_error
  commstep

end Comm

/-! ## Heaps with the record put back -/

theorem setStrm_putGz (h : Heap) (i : Nat) (z : ZStream) (v : GzState) :
    setStrm i z (putGz h i v) = putGz h i { v with strm := z } := by
  simp [setStrm, strmAt, putGz, upd_upd]

theorem putGz_self {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) : putGz h i s = h := by
  unfold putGz
  rw [upd_self _ _ _ hs]

theorem putGz_putGz (h : Heap) (i : Nat) (v w : GzState) : putGz (putGz h i v) i w = putGz h i w := by
  simp [putGz, upd_upd]

/-- **The commutation, as runs.** On a heap whose record `i` is `s`, `gz_error` runs as on the heap with the record
cleared of its pending input (`clearIn`), and the stream `s.strm` is put back. -/
theorem gz_error_setStrm {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (e : Int32) (msg : BPtr) :
    C.run (Zlib.Gzlib.gz_error (gzSt i) e msg) h =
      liftR i s.strm (C.run (Zlib.Gzlib.gz_error (gzSt i) e msg) (putGz h i (clearIn s))) := by
  have key := gz_error_comm (i := i) (z := s.strm) e msg (putGz h i (clearIn s))
  have back : setStrm i s.strm (putGz h i (clearIn s)) = h := by
    rw [setStrm_putGz]
    exact putGz_self hs
  rw [back] at key
  exact key

theorem get_putGz (h : Heap) (i : Nat) (v : GzState) (r : BRef) : Space.get (putGz h i v) r = Space.get h r := by
  cases r <;> rfl

theorem bytes_putGz (h : Heap) (i : Nat) (v : GzState) (p : BPtr) (n : Nat) (xs : List UInt8) :
    Bytes (putGz h i v) p n xs ↔ Bytes h p n xs := by
  unfold Bytes
  simp only [get_putGz]

theorem cstring_putGz (h : Heap) (i : Nat) (v : GzState) (p : BPtr) (xs : List UInt8) :
    CString (putGz h i v) p xs ↔ CString h p xs := by
  unfold CString
  rw [bytes_putGz]

theorem live_putGz {h : Heap} {i : Nat} {v : GzState} (hv : h.gzstates i = some v) (w : GzState) (b : Nat) :
    (putGz h i w).live b ↔ h.live b := by
  unfold Heap.live putGz
  by_cases hb : b = i
  · subst hb
    simp [hv]
  · simp only [upd_ne _ _ _ _ hb]

theorem streamOwned_clearIn {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (b : Nat) :
    StreamOwned (putGz h i (clearIn s)) (.in_gzstate_strm i) b ↔ StreamOwned h (.in_gzstate_strm i) b := by
  unfold StreamOwned
  simp [ZStreamRef.get, putGz, hs, clearIn]

theorem owned_clearIn {h : Heap} {i : Nat} {s : GzState} (hs : h.gzstates i = some s) (b : Nat) :
    GzOwned (putGz h i (clearIn s)) i (clearIn s) b ↔ GzOwned h i s b := by
  unfold GzOwned
  rw [streamOwned_clearIn hs]
  exact Iff.rfl

/-- The block of a byte pointer whose range is readable is live. -/
theorem root_live_of_bytes {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8} (hb : Bytes h p n xs) {b : Nat}
    (hr : ByteRoot p b) : h.live b := by
  rcases hb with ⟨rfl, -, -⟩ | ⟨r, o, a, rfl, hg, -, -⟩
  · exact absurd hr (by simp [ByteRoot])
  · cases r with
    | blk c =>
      simp only [ByteRoot] at hr
      subst hr
      left
      change h.bytes b = some a at hg
      simp [hg]
    | dstate_depth d =>
      simp only [ByteRoot] at hr
      subst hr
      right; right; right; right; left
      change (h.dstates b).map (·.depth) = some a at hg
      intro hn
      simp [hn] at hg
    | str _ => exact absurd hr (by simp [ByteRoot])
    | st_dist_code => exact absurd hr (by simp [ByteRoot])
    | st_length_code => exact absurd hr (by simp [ByteRoot])

/-- A frame over the blocks of a byte reference, with the `strerror` borrow kept, keeps what the reference reads. -/
theorem get_of_frame {a b : Heap} {C : Nat → Prop} (fr : Frame a b C)
    (hbor : b.libcErrorBorrow = a.libcErrorBorrow) (r : BRef) (o : Nat)
    (hroot : ∀ x, ByteRoot (.ref r o) x → a.live x ∧ ¬ C x) : Space.get b r = Space.get a r := by
  obtain ⟨hst, -, -, -, -, keep⟩ := fr
  cases r with
  | blk c =>
    obtain ⟨hl, hc⟩ := hroot c rfl
    exact (keep c hl hc).1
  | dstate_depth d =>
    obtain ⟨hl, hc⟩ := hroot d rfl
    change (b.dstates d).map (·.depth) = (a.dstates d).map (·.depth)
    rw [(keep d hl hc).2.2.2.2.1]
  | str k =>
    change staticStringBytes b k = staticStringBytes a k
    unfold staticStringBytes
    rw [hbor]
  | st_dist_code =>
    change some b.static.dist_code = some a.static.dist_code
    rw [hst]
  | st_length_code =>
    change some b.static.length_code = some a.static.length_code
    rw [hst]

theorem setStrm_of {h : Heap} {i : Nat} {v : GzState} (hv : h.gzstates i = some v) (z : ZStream) :
    setStrm i z h = putGz h i { v with strm := z } := by
  unfold setStrm putGz strmAt
  rw [hv]
  rfl

/-- The owned message is the start of a block the handle owns (W9 of the invariant of the cleared record). -/
theorem msg_owned {h : Heap} {i : Nat} {s : GzState} (invC : GzInv (putGz h i (clearIn s)) i (clearIn s)) (x : Nat)
    (hx : blkOf s.msg = some x) : GzOwned h i s x := by
  rcases invC.common.msg with hn | ⟨m, -, b0, a, hp, -⟩
  · change s.msg = .null at hn
    rw [hn] at hx
    simp [blkOf] at hx
  · change s.msg = .ref (.blk b0) 0 at hp
    rw [hp] at hx
    simp only [blkOf, Option.some.injEq] at hx
    subst hx
    exact Or.inr (Or.inr (Or.inl hp))

/-! ## `gz_error` on the invariant up to the pending input -/

/-- The common part of the two interface lemmas: the run, the new record, the transferred facts. -/
theorem gz_error_upTo_core (err : GzErrorSpec) (errOwn : GzErrorOwn) {h : Heap} {i : Nat} {s : GzState}
    (hs : h.gzstates i = some s) (invC : GzInv (putGz h i (clearIn s)) i (clearIn s)) (e : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) (he : e ≠ Z_STREAM_END) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) e msg) h = .ok ((), after) ∧
      after.gzstates i = some s' ∧ GzInv (putGz after i (clearIn s')) i (clearIn s') ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ (s'.err = e ∨ (s'.err = Z_MEM_ERROR ∧ s'.msg = .null)) ∧
      Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b) ∧
      (∀ b, GzOwned after i s' b → h.live b → GzOwned h i s b) ∧
      (∀ r o, (∀ x, ByteRoot (.ref r o) x → h.live x ∧ ¬ GzOwned h i s x) → Space.get after r = Space.get h r) := by
  have hmsg' : msg = .null ∨ ∃ t, CString (putGz h i (clearIn s)) msg t ∧
      ∀ b, ByteRoot msg b → ¬ GzOwned (putGz h i (clearIn s)) i (clearIn s) b := by
    rcases hmsg with hn | ⟨t, ct, no⟩
    · exact Or.inl hn
    · exact Or.inr ⟨t, (cstring_putGz _ _ _ _ _).2 ct, fun b hb => by rw [owned_clearIn hs]; exact no b hb⟩
  obtain ⟨A, s0, run, invA, eq0, errs, frameA, liveA⟩ := err invC e msg hmsg' he
  have hA : A.gzstates i = some s0 := invA.common.record
  have ownA := errOwn _ _ _ _ _ _ invC hmsg' he run s0 hA
  have bor : A.libcErrorBorrow = (putGz h i (clearIn s)).libcErrorBorrow :=
    C.LibcBorrow.gz_error_borrow_stable (gzSt i) e msg _ () A run
  generalize s0.err = e0 at eq0 errs
  generalize s0.msg = m0 at eq0 errs
  subst eq0
  have hrec : (putGz A i { s with err := e0, msg := m0 }).gzstates i = some { s with err := e0, msg := m0 } := by
    simp [putGz]
  have back : putGz (putGz A i { s with err := e0, msg := m0 }) i (clearIn { s with err := e0, msg := m0 }) = A := by
    rw [putGz_putGz]
    exact putGz_self hA
  refine ⟨putGz A i { s with err := e0, msg := m0 }, { s with err := e0, msg := m0 }, ?_, hrec, ?_, rfl, errs,
    ?_, ?_, ?_, ?_⟩
  · rw [gz_error_setStrm hs, run]
    show Except.ok ((), setStrm i s.strm A) = _
    rw [setStrm_of hA]
    rfl
  · rw [back]
    exact invA
  · obtain ⟨f1, f2, f3, f4, f5, f6⟩ := frameA
    refine ⟨f1, f2, f3, f4, f5, fun b hl hc => ?_⟩
    have hb : b ≠ i := fun eb => hc (Or.inl eb)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := f6 b ((live_putGz hs _ b).2 hl) hc
    refine ⟨g1, g2, g3, g4, g5, g6, ?_, g8⟩
    simp only [putGz, upd_ne _ _ _ _ hb] at g7 ⊢
    exact g7
  · intro b
    have hb := liveA b
    simp only [live_putGz hs] at hb
    rw [live_putGz hA]
    exact hb
  · intro b ho hl
    have hoA := (owned_clearIn hrec b).2 ho
    rw [back] at hoA
    exact (owned_clearIn hs b).1 (ownA b hoA ((live_putGz hs _ b).2 hl))
  · intro r o hroot
    rw [get_putGz, get_of_frame frameA bor r o, get_putGz]
    intro x hx
    obtain ⟨hl, no⟩ := hroot x hx
    refine ⟨(live_putGz hs _ x).2 hl, ?_⟩
    rintro (rfl | hm)
    · exact no (Or.inl rfl)
    · exact no (msg_owned invC x hm)

/-- A readable caller range keeps its bytes across `gz_error` when the handle does not own its block. -/
theorem bytes_after {h after : Heap} {i : Nat} {s : GzState} {p : BPtr} {n : Nat} {xs : List UInt8}
    (hb : Bytes h p n xs) (no : ∀ b, ByteRoot p b → ¬ GzOwned h i s b)
    (get : ∀ r o, (∀ x, ByteRoot (.ref r o) x → h.live x ∧ ¬ GzOwned h i s x) → Space.get after r = Space.get h r) :
    Bytes after p n xs := by
  rcases id hb with hn | ⟨r, o, a, hp, hg, hlen, hx⟩
  · exact Or.inl hn
  · refine Or.inr ⟨r, o, a, hp, ?_, hlen, hx⟩
    rw [get r o (fun x hx' => ⟨root_live_of_bytes hb (hp ▸ hx'), no x (hp ▸ hx')⟩)]
    exact hg

/-- **`gz_error` keeps the writer invariant up to the pending input.** The message is NULL, or a string the handle
does not own (a literal, a borrowed `strerror` view, a caller string). The caller region keeps its bytes: its blocks
are live and not owned, and `gz_error` changes only the record and the old owned message. -/
theorem gz_error_upToInput (err : GzErrorSpec) (errOwn : GzErrorOwn) {h : Heap} {i : Nat} {s : GzState}
    {src : Region} (inv : GzInvUpToInput h i s src) (e : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) (he : e ≠ Z_STREAM_END) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) e msg) h = .ok ((), after) ∧ GzInvUpToInput after i s' src ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b) ∧
      (∀ b, GzOwned after i s' b → h.live b → GzOwned h i s b) := by
  obtain ⟨hs, invC, hmode, hin, hreg⟩ := inv
  obtain ⟨after, s', run, hrec, invA, eq', -, frame, live, own, get⟩ :=
    gz_error_upTo_core err errOwn hs invC e msg hmsg he
  have hmode' : s'.mode = s.mode := by rw [eq']
  have hz : s'.strm = s.strm := by rw [eq']
  have hinb : s'.«in» = s.«in» := by rw [eq']
  have hsz : s'.size = s.size := by rw [eq']
  refine ⟨after, s', run, ⟨hrec, invA, hmode'.trans hmode, hz ▸ hin, ?_⟩, eq', frame, live, own⟩
  rcases hreg with ⟨hp, hl⟩ | ⟨⟨xs, hb⟩, no⟩
  · exact Or.inl ⟨hinb ▸ hp, hsz ▸ hl⟩
  · exact Or.inr ⟨⟨xs, bytes_after hb no get⟩,
      fun b hr ho => no b hr (own b ho (root_live_of_bytes hb hr))⟩

/-- **`gz_error` keeps the weak writer invariant up to the pending input.** As `gz_error_upToInput`. A caller
region the handle does not own must have live blocks, or be the `in` buffer (`hlive`): `gz_error` may allocate a
new message block, which differs from the region's blocks only when they are live. The strong invariant implies
`hlive` (a readable range has live blocks). -/
theorem gz_error_upToInputWeak (err : GzErrorSpec) (errOwn : GzErrorOwn) {h : Heap} {i : Nat} {s : GzState}
    {src : Region} (inv : GzInvUpToInputWeak h i s src) (e : Int32) (msg : BPtr)
    (hmsg : msg = .null ∨ ∃ t, CString h msg t ∧ ∀ b, ByteRoot msg b → ¬ GzOwned h i s b) (he : e ≠ Z_STREAM_END)
    (hlive : src.pointer = s.«in» ∧ src.length ≤ 2 * s.size.toNat ∨ ∀ b, ByteRoot src.pointer b → h.live b) :
    ∃ after s', C.run (Zlib.Gzlib.gz_error (gzSt i) e msg) h = .ok ((), after) ∧
      GzInvUpToInputWeak after i s' src ∧
      s' = { s with err := s'.err, msg := s'.msg } ∧ Frame h after (fun b => b = i ∨ blkOf s.msg = some b) ∧
      LiveChange h after (fun b => blkOf s'.msg = some b ∧ ¬ h.live b) (fun b => blkOf s.msg = some b) ∧
      (∀ b, GzOwned after i s' b → h.live b → GzOwned h i s b) := by
  obtain ⟨hs, invC, hmode, hin, hreg⟩ := inv
  obtain ⟨after, s', run, hrec, invA, eq', -, frame, live, own, -⟩ :=
    gz_error_upTo_core err errOwn hs invC e msg hmsg he
  have hmode' : s'.mode = s.mode := by rw [eq']
  have hz : s'.strm = s.strm := by rw [eq']
  have hinb : s'.«in» = s.«in» := by rw [eq']
  have hsz : s'.size = s.size := by rw [eq']
  refine ⟨after, s', run, ⟨hrec, invA, hmode'.trans hmode, hz ▸ hin, ?_⟩, eq', frame, live, own⟩
  rcases hreg with ⟨hp, hl⟩ | no
  · exact Or.inl ⟨hinb ▸ hp, hsz ▸ hl⟩
  · rcases hlive with ⟨hp, hl⟩ | hl
    · exact Or.inl ⟨hinb ▸ hp, hsz ▸ hl⟩
    · exact Or.inr fun b hr ho => no b hr (own b ho (hl b hr))

end ZlibF.Spec.Public.GzSkeleton
