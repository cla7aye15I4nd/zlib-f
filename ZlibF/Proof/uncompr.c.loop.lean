import ZlibF.Proof.«uncompr.c.entry»
import ZlibF.Proof.«inflate.c.default-public-memory-contract»

/-!
# The actual uncompress2_z loop

A definitional equation anchors the named loop to the complete translated wrapper.
The representation is preserved by real refills. The real decoder theorem gives
exact counts, observed output, memory frame, allocation ledger and strict OK progress
on that same iteration. Wrapper initialization, full scalar writeback, full cleanup,
independent format semantics and whole-wrapper completion remain separate obligations.
-/

namespace Zlib.Uncompr.Proof.Loop
open C Zlib.Gzguts
open Zlib.Inflate (inflateInit_ inflate inflateEnd)

/-- The exact body passed to cdoWhile by the source wrapper. -/
def loopBody (stream : ZStreamPtr) (l : UncLoop) : M UncLoop := do
  let max : UInt32 := 0xFFFFFFFF
  let mut l := l
  -- if (stream.avail_out == 0) { stream.avail_out = left > (z_size_t)max ? max : (uInt)left; left -= stream.avail_out; }
  if (← ldZ stream).avail_out == 0 then
    let a : UInt32 := if l.left > max.toUInt64 then max else l.left.toUInt32
    updZ stream fun z => { z with avail_out := a }
    l := { l with left := l.left - a.toUInt64 }
  -- if (stream.avail_in == 0) { stream.avail_in = len > (z_size_t)max ? max : (uInt)len; len -= stream.avail_in; }
  if (← ldZ stream).avail_in == 0 then
    let a : UInt32 := if l.len > max.toUInt64 then max else l.len.toUInt32
    updZ stream fun z => { z with avail_in := a }
    l := { l with len := l.len - a.toUInt64 }
  -- err = inflate(&stream, Z_NO_FLUSH);
  let err ← inflate stream Z_NO_FLUSH
  return { l with err }

def loopCondition (l : UncLoop) : M (Bool × UncLoop) := pure (l.err == Z_OK, l)

def decomposed (dest : BPtr) (destLen : BPtr) (source : BPtr) (sourceLen : BPtr) : M Int32 := do
  -- z_stream stream; int err; const uInt max = (uInt)-1; z_size_t len, left;
  let stream ← allocLocalZ
  let reserved ← allocLocal 8
  let free : M Unit := do
    freeB reserved
    freeZStream stream
  -- if (sourceLen == Z_NULL || (*sourceLen > 0 && source == Z_NULL) || destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL))
  --   return Z_STREAM_ERROR;
  let mut bad := false
  if sourceLen == .null then bad := true
  else if (← load64 sourceLen) > 0 && source == .null then bad := true
  else if destLen == .null then bad := true
  else if (← load64 destLen) > 0 && dest == .null then bad := true
  if bad then
    free
    return Z_STREAM_ERROR
  -- len = *sourceLen; left = *destLen;
  let len ← load64 sourceLen
  let left ← load64 destLen
  -- if (left == 0 && dest == Z_NULL) dest = (Bytef *)&stream.reserved;
  let dest := if left == 0 && dest == .null then reserved else dest
  -- stream.next_in = (z_const Bytef *)source; stream.avail_in = 0; zalloc, zfree, opaque = 0;
  updZ stream fun z => { z with next_in := source, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null }
  -- err = inflateInit(&stream); if (err != Z_OK) return err;
  let ver ← Zlib.GzFs.strLit ZLIB_VERSION
  let err ← inflateInit_ stream ver 112
  if err != Z_OK then
    free
    return err
  -- stream.next_out = dest; stream.avail_out = 0;
  updZ stream fun z => { z with next_out := dest, avail_out := 0 }
  -- do { ... } while (err == Z_OK);
  let l ← cdoWhile (loopBody stream) loopCondition { err, len, left }
  -- len += stream.avail_in; left += stream.avail_out; *sourceLen -= len; *destLen -= left;
  let z ← ldZ stream
  let len := l.len + z.avail_in.toUInt64
  let left := l.left + z.avail_out.toUInt64
  store64 sourceLen ((← load64 sourceLen) - len)
  store64 destLen ((← load64 destLen) - left)
  -- inflateEnd(&stream);
  let _ ← inflateEnd stream
  -- return err == Z_STREAM_END ? Z_OK : err == Z_NEED_DICT ? Z_DATA_ERROR : err == Z_BUF_ERROR && len == 0 ? Z_DATA_ERROR : err;
  let err := l.err
  let r : Int32 :=
    if err == Z_STREAM_END then Z_OK
    else if err == Z_NEED_DICT then Z_DATA_ERROR
    else if err == Z_BUF_ERROR && len == 0 then Z_DATA_ERROR
    else err
  free
  return r


/-- The entire real wrapper, including argument checks, init, stores and cleanup,
uses exactly this named loop body and condition. -/
theorem uncompress2_z_decomposition : uncompress2_z = decomposed := by
  unfold uncompress2_z decomposed loopBody loopCondition
  with_reducible rfl


def chunk (n : UInt64) : UInt32 :=
  if n > (0xFFFFFFFF : UInt32).toUInt64 then 0xFFFFFFFF else n.toUInt32

theorem chunk_toNat (n : UInt64) : (chunk n).toNat = min n.toNat (2 ^ 32 - 1) := by
  by_cases hm : n > (0xFFFFFFFF : UInt32).toUInt64
  · have hn : 4294967295 < n.toNat := hm
    simp only [chunk, ite_eq_left hm]
    change 4294967295 = min n.toNat 4294967295
    omega
  · have hn : n.toNat ≤ 4294967295 := by
      change ¬ 4294967295 < n.toNat at hm
      omega
    simp only [chunk, ite_eq_right hm, UInt64.toNat_toUInt32]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Nat.min_eq_left hn |>.symm

theorem chunk_le (n : UInt64) : (chunk n).toUInt64 ≤ n := by
  apply UInt64.le_iff_toNat_le.mpr
  rw [UInt32.toNat_toUInt64, chunk_toNat]
  exact Nat.min_le_left _ _

theorem chunk_sub_exact (n : UInt64) :
    (n - (chunk n).toUInt64).toNat + (chunk n).toNat = n.toNat := by
  rw [UInt64.toNat_sub_of_le _ _ (chunk_le n)]
  have hn := UInt64.le_iff_toNat_le.mp (chunk_le n)
  simp only [UInt32.toNat_toUInt64] at hn ⊢
  omega

def refilledStream (z : ZStream) (l : UncLoop) : ZStream :=
  { z with
    avail_out := if z.avail_out == 0 then chunk l.left else z.avail_out
    avail_in := if z.avail_in == 0 then chunk l.len else z.avail_in }

def refilledLocals (z : ZStream) (l : UncLoop) : UncLoop :=
  { l with
    left := if z.avail_out == 0 then l.left - (chunk l.left).toUInt64 else l.left
    len := if z.avail_in == 0 then l.len - (chunk l.len).toUInt64 else l.len }

/-- One source loop iteration passes this exact refilled heap to the actual inflate.
The result is an equation over the real call, with no callee specification hypothesis. -/
theorem loopBody_run (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop)
    (hz : h.streams b = some z) :
    C.run (loopBody (some (.tab b)) l) h =
      match inflate (some (.tab b)) Z_NO_FLUSH
        { h with streams := upd h.streams b (some (refilledStream z l)) } with
      | .ok (err, after) => .ok ({ refilledLocals z l with err }, after)
      | .error fault => .error fault := by
  have he := upd_self h.streams b z hz
  by_cases ho : z.avail_out = 0 <;> by_cases hi : z.avail_in = 0 <;>
    simp [C.run, loopBody, ldZ, updZ, ldZStream, stZStream, ZStreamRef.get,
      ZStreamRef.put, ZStreamRef.isRo, hz, ho, hi, refilledStream,
      refilledLocals, chunk, upd_upd, he] <;> split <;> simp_all


/-- The complete fueled loop unfolds to this real inflate call and its exact
continuation. Any non-OK result stops immediately; a fault is propagated. -/
theorem loop_go_succ (steps : Nat) (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop)
    (hz : h.streams b = some z) :
    C.run (cdoWhile.go (loopBody (some (.tab b))) loopCondition (steps + 1) l) h =
      match inflate (some (.tab b)) Z_NO_FLUSH
        { h with streams := upd h.streams b (some (refilledStream z l)) } with
      | .ok (err, after) =>
          let next := { refilledLocals z l with err }
          if err == Z_OK then
            cdoWhile.go (loopBody (some (.tab b))) loopCondition steps next after
          else .ok (next, after)
      | .error fault => .error fault := by
  have he := loopBody_run h b z l hz
  simp only [C.run] at he
  cases hr : inflate (some (.tab b)) Z_NO_FLUSH
    { h with streams := upd h.streams b (some (refilledStream z l)) } with
  | error fault =>
      simp [hr] at he
      simp [C.run, cdoWhile.go, he]
  | ok pair =>
      rcases pair with ⟨err, after⟩
      simp [hr] at he
      simp [C.run, cdoWhile.go, he, loopCondition]
      split <;> rfl

/-- Refilling redistributes the same finite input remainder between the outer UInt64
counter and the inner UInt32 availability. Neither narrowing nor subtraction wraps. -/
theorem refill_input_count (z : ZStream) (l : UncLoop) :
    (refilledLocals z l).len.toNat + (refilledStream z l).avail_in.toNat =
      l.len.toNat + z.avail_in.toNat := by
  by_cases hi : z.avail_in = 0
  · simpa [refilledLocals, refilledStream, hi] using chunk_sub_exact l.len
  · simp [refilledLocals, refilledStream, hi]

theorem refill_output_count (z : ZStream) (l : UncLoop) :
    (refilledLocals z l).left.toNat + (refilledStream z l).avail_out.toNat =
      l.left.toNat + z.avail_out.toNat := by
  by_cases ho : z.avail_out = 0
  · simpa [refilledLocals, refilledStream, ho] using chunk_sub_exact l.left
  · simp [refilledLocals, refilledStream, ho]

/-- The final stored count is the exact natural difference, not a wrapped result,
whenever the loop's remaining bytes are bounded by the original length. -/
theorem final_count_exact (original remaining : UInt64) (available : UInt32)
    (hb : remaining.toNat + available.toNat ≤ original.toNat) :
    (remaining + available.toUInt64).toNat = remaining.toNat + available.toNat ∧
    (original - (remaining + available.toUInt64)).toNat =
      original.toNat - (remaining.toNat + available.toNat) := by
  have hlim := original.toNat_lt
  have hadd : (remaining + available.toUInt64).toNat = remaining.toNat + available.toNat := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hadd, ?_⟩
  have hle : remaining + available.toUInt64 ≤ original := by
    apply UInt64.le_iff_toNat_le.mpr
    simpa [hadd] using hb
  rw [UInt64.toNat_sub_of_le _ _ hle, hadd]

/-- Exact availability deltas suffice for the wrapper's natural count equation,
including an inflate result that has already written partial output before an error. -/
theorem iteration_count (z : ZStream) (l : UncLoop) (z' : ZStream) (used made : Nat)
    (hin : z'.avail_in.toNat + used = (refilledStream z l).avail_in.toNat)
    (hout : z'.avail_out.toNat + made = (refilledStream z l).avail_out.toNat) :
    (refilledLocals z l).len.toNat + z'.avail_in.toNat +
      (refilledLocals z l).left.toNat + z'.avail_out.toNat + used + made =
      l.len.toNat + z.avail_in.toNat + l.left.toNat + z.avail_out.toNat := by
  have hi := refill_input_count z l
  have ho := refill_output_count z l
  omega

theorem iteration_strict_progress (z : ZStream) (l : UncLoop) (z' : ZStream) (used made : Nat)
    (hin : z'.avail_in.toNat + used = (refilledStream z l).avail_in.toNat)
    (hout : z'.avail_out.toNat + made = (refilledStream z l).avail_out.toNat)
    (progress : used ≠ 0 ∨ made ≠ 0) :
    (refilledLocals z l).len.toNat + z'.avail_in.toNat +
      (refilledLocals z l).left.toNat + z'.avail_out.toNat <
      l.len.toNat + z.avail_in.toNat + l.left.toNat + z.avail_out.toNat := by
  have he := iteration_count z l z' used made hin hout
  omega

/-- The platform object-size restriction gives enough fuel for the outer loop:
input plus capacity is strictly below 2^64, even though they use separate objects. -/
theorem two_object_loop_budget (input capacity : Nat)
    (hi : input < 2 ^ 63) (ho : capacity < 2 ^ 63) :
    input + capacity + 1 < C.fuel := by
  unfold C.fuel
  omega

def refilledHeap (h : Heap) (b : Nat) (z : ZStream) (l : UncLoop) : Heap :=
  { h with streams := upd h.streams b (some (refilledStream z l)) }

theorem refilledDefaultStateJ (h : Heap) (b zs : Nat) (z : ZStream) (l : UncLoop)
    (s : InflateState)
    (invariant : Zlib.Inflate.Proofs.DefaultStateJ h (.tab b) zs z s) :
    Zlib.Inflate.Proofs.DefaultStateJ (refilledHeap h b z l) (.tab b) zs (refilledStream z l) s := by
  have hz : h.streams b = some z := invariant.good.live.hz
  have shape := Zlib.Inflate.Proofs.shape_put invariant.good.live.hz (refilledStream z l)
  have put : ZStreamRef.put h (.tab b) (refilledStream z l) = refilledHeap h b z l := by
    simp [ZStreamRef.put, hz, refilledHeap]
  rw [put] at shape
  have win : Zlib.Inflate.Spec.WinInv (refilledHeap h b z l) s := by
    refine { invariant.good.inv.win with block := ?_ }
    simpa only [refilledHeap] using invariant.good.inv.win.block
  have inv : Zlib.Inflate.Spec.StInv (refilledHeap h b z l) zs s :=
    { invariant.good.inv with win := win }
  have tables : Zlib.Inflate.Spec.DataTableInvariant (refilledHeap h b z l) s := by
    intro mode
    exact Zlib.Inflate.Proofs.dataTablesSafe_of_state_static
      (before := h) (after := refilledHeap h b z l) invariant.good.inv.ptr
      rfl rfl (invariant.tables mode)
  have good : Zlib.Inflate.Spec.Good (refilledHeap h b z l) (.tab b) zs (refilledStream z l) s := by
    refine ⟨?_, inv, shape.uniq invariant.good.uniq,
      shape.fresh (by rfl) invariant.good.fresh⟩
    exact ⟨by simp [refilledHeap, ZStreamRef.get], invariant.good.live.hs,
      invariant.good.live.zst, invariant.good.live.back, invariant.good.live.mode,
      invariant.good.live.zalloc, invariant.good.live.zfree⟩
  have platform : ZlibF.PlatformMemory.ByteObjectsFit (refilledHeap h b z l) := by
    intro ref a get
    apply invariant.platform ref a
    cases ref <;> simpa only [Space.get, refilledHeap] using get
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths,
    invariant.headerLengths, invariant.held, invariant.window, invariant.wrapper,
    invariant.header, invariant.modes, invariant.trailer, invariant.globals, platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

/-- The actual wrapper iteration uses the existing proved decoder theorem. The
incoming representation is preserved by the real refills; it is not a callee contract.
This is not yet a theorem that wrapper initialization establishes that representation. -/
theorem loop_iteration_memory (h : Heap) (b zs : Nat) (z : ZStream) (l : UncLoop)
    (s : InflateState)
    (invariant : Zlib.Inflate.Proofs.DefaultStateJ h (.tab b) zs z s)
    (allocator : Zlib.Inflate.Spec.DefAlloc z)
    (buffers : ZlibF.Spec.Public.StreamBuffers (refilledHeap h b z l) (.tab b)) :
    ∃ rc after stream state used output,
      C.run (loopBody (some (.tab b)) l) h =
        .ok ({ refilledLocals z l with err := rc }, after) ∧
      Zlib.Inflate.Proofs.DefaultStateJ after (.tab b) zs stream state ∧
      Zlib.Inflate.Spec.DefAlloc stream ∧
      ZlibF.Spec.Public.StreamAccounting (refilledStream z l) stream used output.length ∧
      ZlibF.Spec.Public.Bytes after z.next_out output.length output ∧
      Zlib.Inflate.Proofs.PublicInflateCode rc ∧
      ZlibF.Spec.Public.BufferFrame (refilledHeap h b z l) after
        (fun x => ZlibF.Spec.Public.StreamRoot (.tab b) x ∨
          ZlibF.Spec.Public.InflateOwned zs s x) [⟨z.next_out, output.length⟩] ∧
      ZlibF.Spec.Public.LiveChange (refilledHeap h b z l) after
        (fun x => ZlibF.Spec.Public.InflateOwned zs state x ∧
          ¬ (refilledHeap h b z l).live x) (fun _ => False) ∧
      ((refilledLocals z l).len.toNat + stream.avail_in.toNat +
        (refilledLocals z l).left.toNat + stream.avail_out.toNat + used + output.length =
        l.len.toNat + z.avail_in.toNat + l.left.toNat + z.avail_out.toNat) ∧
      (rc = Z_OK →
        (refilledLocals z l).len.toNat + stream.avail_in.toNat +
          (refilledLocals z l).left.toNat + stream.avail_out.toNat <
          l.len.toNat + z.avail_in.toNat + l.left.toNat + z.avail_out.toNat) := by
  obtain ⟨rc, after, stream, state, used, output, run, current, finalAllocator,
    _freed, account, observed, _totals, progress, codes, _memoryTotals, _modes,
    frame, ledger⟩ :=
    Zlib.Inflate.Proofs.inflate_default_view_public_memory_contract
      (refilledDefaultStateJ h b zs z l s invariant) allocator buffers Z_NO_FLUSH
  have run' := run
  simp only [C.run, refilledHeap] at run'
  have body := loopBody_run h b z l invariant.good.live.hz
  rw [run'] at body
  refine ⟨rc, after, stream, state, used, output, body, current, finalAllocator,
    account, ?_, codes, ?_, ledger, iteration_count z l stream used output.length account.2.2.1 account.2.2.2.1, ?_⟩
  · simpa only [refilledStream] using observed
  · simpa only [refilledStream] using frame
  · intro ok
    have changed : used ≠ 0 ∨ output.length ≠ 0 := by
      rcases (progress ok).1 with input | made
      · exact Or.inl input
      · exact Or.inr (fun zero => made (List.eq_nil_of_length_eq_zero zero))
    exact iteration_strict_progress z l stream used output.length account.2.2.1 account.2.2.2.1 changed

#print axioms uncompress2_z_decomposition
#print axioms loopBody_run
#print axioms refilledDefaultStateJ
#print axioms loop_iteration_memory
#print axioms loop_go_succ
#print axioms iteration_strict_progress
#print axioms two_object_loop_budget
#print axioms refill_input_count
#print axioms refill_output_count
#print axioms final_count_exact

end Zlib.Uncompr.Proof.Loop
