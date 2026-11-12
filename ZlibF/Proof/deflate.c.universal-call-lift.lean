import ZlibF.Proof.«deflate.c.universal-call-early»

/-!
# deflate.c: carrying the invariant across the phases of one call

Owner 2 of the deflate split (`deflate_call`). The header stages, the flushes and the flush
markers write `pending_buf` only in its pending area, below `lit_bufsize`; the recorded symbols
sit from `lit_bufsize` on. These lemmas carry `Symbols` and `HeaderInv` across such a change.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Packed symbols only read their own bytes. -/
theorem packed_symbols_agree {a b : Array UInt8} {base : Nat} {xs : List Symbol}
    (packed : PackedSymbols a base xs)
    (same : ∀ j, base ≤ j → j < base + 3 * xs.length → bfn b j = bfn a j) : PackedSymbols b base xs := by
  intro i s get
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp get).1
  obtain ⟨e0, e1, e2⟩ := packed i s get
  refine ⟨?_, ?_, ?_⟩
  · rw [same _ (by omega) (by omega)]; exact e0
  · rw [same _ (by omega) (by omega)]; exact e1
  · rw [same _ (by omega) (by omega)]; exact e2

/-- **`Symbols` across a change of the pending area.** The new state keeps the symbol fields, and
the new heap keeps the bytes of `pending_buf` from `lit_bufsize` on; `below` is the pending
bound of the new state. -/
theorem Symbols.pending_change {h h' : Heap} {d d' : DeflateState} (symbols : Symbols h d)
    (pbuf : d'.pending_buf = d.pending_buf) (count : d'.sym_next = d.sym_next)
    (lit : d'.lit_bufsize = d.lit_bufsize) (ltree : d'.dyn_ltree = d.dyn_ltree)
    (dtree : d'.dyn_dtree = d.dyn_dtree) (wsize : d'.w_size = d.w_size)
    (bl : d'.bl_tree = d.bl_tree) (opt : d'.opt_len = d.opt_len) (fixed : d'.static_len = d.static_len)
    (bytes : ∀ b a, d.pending_buf = .ref (.blk b) 0 → h.bytes b = some a →
      ∃ a', h'.bytes b = some a' ∧ ∀ j, d.lit_bufsize.toNat ≤ j → bfn a' j = bfn a j)
    (below : ∀ b off, d'.pending_out = .ref (.blk b) off → d'.sym_next ≠ 0 →
      off + d'.pending.toNat ≤ d'.lit_bufsize.toNat) : Symbols h' d' := by
  obtain ⟨⟨xs, ⟨b, a, ptr, get, ledger⟩, near⟩, clear, _⟩ := symbols
  obtain ⟨a', get', same⟩ := bytes b a ptr get
  refine ⟨⟨xs, ⟨b, a', by rw [pbuf]; exact ptr, get', ?_⟩, by rw [wsize]; exact near⟩, ?_, below⟩
  · refine ⟨by rw [count]; exact ledger.count, ledger.valid, ?_, by rw [ltree]; exact ledger.literal,
      by rw [dtree]; exact ledger.distance⟩
    rw [lit]
    exact packed_symbols_agree ledger.packed (fun j low _ => same j low)
  · exact ⟨by rw [bl]; exact clear.bl, by rw [opt]; exact clear.opt, by rw [fixed]; exact clear.fixed⟩

/-- `HeaderInv` across a change of `last_flush`. -/
theorem HeaderInv.lastFlush {d : DeflateState} (header : HeaderInv d) (v : Int32) :
    HeaderInv { d with last_flush := v } :=
  header.keep rfl rfl rfl

/-- The record shape of a phase that writes only the header and flush fields. -/
def HeaderFields (d d' : DeflateState) : Prop :=
  d' = { d with status := d'.status, pending := d'.pending, pending_out := d'.pending_out,
                bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used,
                last_flush := d'.last_flush, gzindex := d'.gzindex, wrap := d'.wrap }

/-- **`DInv` across a phase that writes only the header and flush fields**, given `DGood` and
`Shape` of the new state, the window, `prev` and `head` blocks unchanged, and the symbol area of
`pending_buf` kept. -/
theorem _root_.Zlib.Deflate.Universal.DInv.lift {h h' : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d d' : DeflateState} (inv : DInv h r ds z d) (good' : DGood h' r ds z' d') (alloc : DefAlloc z')
    (static : h'.static = h.static) (shape' : Shape d') (fields : HeaderFields d d')
    (win : ∀ w, d.window = .ref (.blk w) 0 → h'.bytes w = h.bytes w)
    (prv : ∀ p, d.prev = .ref (.blk p) 0 → h'.words p = h.words p)
    (hd : ∀ q, d.head = .ref (.blk q) 0 → h'.words q = h.words q)
    (bytes : ∀ b a, d.pending_buf = .ref (.blk b) 0 → h.bytes b = some a →
      ∃ a', h'.bytes b = some a' ∧ ∀ j, d.lit_bufsize.toNat ≤ j → bfn a' j = bfn a j)
    (below : ∀ b off, d'.pending_out = .ref (.blk b) off → d'.sym_next ≠ 0 →
      off + d'.pending.toNat ≤ d'.lit_bufsize.toNat) :
    DInv h' r ds z' d' := by
  obtain ⟨_, _, globals, _, hashing, symbols⟩ := inv
  have sym' : Symbols h' d' := by
    unfold HeaderFields at fields
    exact Symbols.pending_change symbols (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields])
      (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields]) bytes below
  refine ⟨good', alloc, ?_, shape', ?_, sym'⟩
  · unfold LibraryGlobals at *; rw [static]; exact globals
  · unfold HeaderFields at fields
    rw [fields]
    obtain ⟨chains, slid, rolling⟩ := hashing
    refine ⟨fun zero => ?_, fun one => ?_, fun s2 s3 three => ?_⟩
    · obtain ⟨w, p, q, wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := chains zero
      exact ⟨w, p, q, wa, pa, qa, ew, ep, eq, (win w ew).trans hw, (prv p ep).trans hp, (hd q eq).trans hq, H⟩
    · obtain ⟨w, p, q, wa, pa, qa, ew, ep, eq, hw, hp, hq, H⟩ := slid one
      exact ⟨w, p, q, wa, pa, qa, ew, ep, eq, (win w ew).trans hw, (prv p ep).trans hp, (hd q eq).trans hq, H⟩
    · obtain ⟨w, wa, ew, hw, form⟩ := rolling s2 s3 three
      exact ⟨w, wa, ew, (win w ew).trans hw, form⟩

/-- `HeaderInv` across a phase that keeps the symbol count and the header record; with the status
it may change, the caller supplies the header facts of the new status. -/
theorem HeaderInv.of_fields {d d' : DeflateState} (header : HeaderInv d) (fields : HeaderFields d d')
    (status : d'.status = d.status) : HeaderInv d' := by
  unfold HeaderFields at fields
  exact header.keep status (by rw [fields]) (by rw [fields])

/-- `Shape` of a state that differs only in the header and flush fields: the clauses that read
those fields are premises, every other clause carries over. -/
theorem Shape.of_fields {d d' : DeflateState} (shape : Shape d) (fields : HeaderFields d d')
    (lastFlush : -2 ≤ d'.last_flush.toInt ∧ d'.last_flush.toInt ≤ 5)
    (headerFlush : d'.status = INIT_STATE ∨ d'.status = GZIP_STATE → d'.last_flush = -2 ∨ d'.last_flush = -1)
    (trailer : d'.wrap.toInt < 0 → d'.status = FINISH_STATE) (biValid : d'.bi_valid.toInt ≤ 7)
    (cursor : d'.pending = 0 → d'.pending_out = d'.pending_buf) : Shape d' := by
  unfold HeaderFields at fields
  rw [fields] at lastFlush headerFlush trailer biValid cursor ⊢
  exact { shape with lastFlush, headerFlush, trailer, biValid, cursor }

end Zlib.Deflate.Universal.Call
