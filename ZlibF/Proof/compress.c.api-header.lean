import ZlibF.Proof.«compress.c.init-outcomes»

/-! # The actual default header satisfies the utility API metadata -/
namespace ZlibF.Spec.Public.Proofs.CompressApi
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressPrefix
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressTail
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The actual default trace emits CMF=120 and FLG=156 before data.
A completed independently valid output excludes the empty and one-byte
header phases. The API's announced window=15 and absent-dictionary bit
therefore follow from real emitted bytes, not from independent validity
alone. -/
theorem trace_api_valid {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) (ended : log.result = Z_STREAM_END) :
    (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid log.output log.input := by
  obtain ⟨ds, z, d, config, state, completed⟩ := history.encoding
  have valid := completed ended
  have header : ∃ payload, log.output = [120,156] ++ payload := by
    rcases state.phase with ⟨_input, output, _rest⟩ | ⟨_input, output, _rest⟩ |
      ⟨_input, _origin, _base, _xs, published, output, _rest⟩ | ⟨published, output, _rest⟩
    · obtain ⟨cmf, flg, pre, stream, shape, _⟩ := valid
      rw [output] at shape
      cases shape
    · obtain ⟨cmf, flg, pre, stream, shape, _⟩ := valid
      rw [output] at shape
      cases shape
    · exact ⟨published, output⟩
    · exact ⟨published, output⟩
  obtain ⟨payload, output⟩ := header
  change ZlibF.Spec.Zlib.Decodes [] log.output log.input ∧
    log.output.head?.map (fun b => b.toNat / 16 + 8) = some 15 ∧
    ∃ cmf flg rest, log.output = cmf :: flg :: rest ∧
      (flg.toNat / 32 % 2 = 1 ↔ ([] : List UInt8) ≠ [])
  refine ⟨valid, ?_, 120, 156, payload, ?_, ?_⟩
  · rw [output]
    rfl
  · exact output
  · decide

/-- The real finite loop's END output meets the API's complete format
and metadata relation for the entire original source. -/
theorem prefix_end_api_valid {slot ob oo k : Nat} {start after : Heap} {last : Locals}
    {first : ZStream} {left sourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {}) (get : start.streams slot = some first)
    (ranges : Ranges start (.tab slot) first left sourceLen source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (execution : ActualPrefix slot start (Z_OK, left, sourceLen) k after last)
    (ended : last.1 = Z_STREAM_END) :
    ∃ used log z, PrefixAccount slot first left sourceLen source k after last used log z ∧
      (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid log.output source := by
  obtain ⟨used, log, z, sound⟩ := actual_prefix_sound history get ranges pointer execution
  have positive : 0 < k := by
    cases execution with
    | nil => exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) ended)
    | step => omega
  have consumed := sound.ended ended
  have size := caller_bytes_length ranges.snapshot
  have count := sound.inputCount
  rw [consumed.1, consumed.2] at count
  simp only [UInt64.toNat_zero, UInt32.toNat_zero, Nat.zero_add] at count
  have all : used = source.length := by omega
  have input : log.input = source := by rw [sound.input, all, List.take_length]
  have valid := trace_api_valid sound.history ((sound.result positive).trans ended)
  rw [input] at valid
  exact ⟨used, log, z, sound, valid⟩


/-- A successful real utility execution has the API's exact header and
metadata relation. The input/output lists are connected to the returned
scalar and final physical output of that same execution. -/
theorem actual_success_api_valid {h after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen written : UInt64} {xs output : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo)
    (actual : C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
      .ok ((Z_OK, some written), after))
    (physical : Bytes after dest written.toNat output) :
    (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid output xs := by
  obtain ⟨f, u, g, v, old, oldGet, alloc, _null⟩ := automatic_stream_domain h fresh unique globals
  obtain ⟨initRc, initialized, actualInit, allowed⟩ := default_initialization_total f u g oldGet alloc v
  rcases allowed with initOK | initMemory
  · subst initRc
    obtain ⟨ready, last, loopHeap, setup, actualLoop, stopped, _valid⟩ :=
      original_buffers_loop_total fresh unique globals objects bytes writable separate pointer actualInit
    obtain ⟨ready0, first, setup0, history, get, ranges, out, _in, outAvail, inAvail⟩ :=
      successful_default_seed fresh unique globals bytes writable separate actualInit
    have readyEq : ready0 = ready := (Prod.mk.inj (Except.ok.inj (setup0.symm.trans setup))).2
    subst ready0
    have raw := out.trans pointer
    obtain ⟨k, positive, _fuel, execution⟩ := loop_go_prefix (slot := h.nextBlk) rfl actualLoop
    obtain ⟨used, log, returned, sound⟩ := actual_prefix_sound history get ranges raw execution
    obtain ⟨buffers, _input⟩ := ranges_current (r := .tab h.nextBlk) sound.get sound.remaining
    have cursor : returned.next_out = .ref (.blk ob) (oo + log.output.length) := by
      rw [sound.outputPtr, raw]
      rfl
    have outputBytes : Bytes loopHeap (.ref (.blk ob) oo) log.output.length log.output := by
      rw [←raw]
      exact sound.outputBytes
    have fits : log.output.length ≤ capacity.toNat := by
      have count := sound.outputCount
      rw [outAvail] at count
      simp only [UInt32.toNat_zero, Nat.zero_add] at count
      omega
    have capacityBound : capacity.toNat < 2^63 := by
      rcases writable with ⟨impossible, _⟩ | ⟨ref, offset, a, _eq, getA, _ro, bound⟩
      · rw [pointer] at impossible
        cases impossible
      · have size := objects ref a getA
        change a.size < 2^63 at size
        omega
    obtain ⟨ds, d, computed, _good, tailRun, finalBytes, _dead, _live, _frame, _count, _next, wordNat⟩ :=
      tail_nonnull_exact sound.history sound.get buffers cursor outputBytes (by omega) last.1
    have nonnull : dest ≠ .null := by rw [pointer]; intro bad; cases bad
    have computedRun := run_of_successful_stages fresh bytes nonnull actualInit setup actualLoop
      (by rw [pointer]; exact tailRun)
    have events := Prod.mk.inj (Except.ok.inj (computedRun.symm.trans actual))
    have code := congrArg Prod.fst events.1
    have scalar := Option.some.inj (congrArg Prod.snd events.1)
    have heapEq := events.2
    have ended : last.1 = Z_STREAM_END := by
      by_cases eq : last.1 = Z_STREAM_END
      · exact eq
      · have bad : last.1 = Z_OK := by simpa only [beq_iff_eq, eq, ite_false] using code
        exact False.elim (stopped bad)
    have consumed := sound.ended ended
    have size := caller_bytes_length bytes
    have count := sound.inputCount
    rw [consumed.1, consumed.2, inAvail] at count
    simp only [UInt64.toNat_zero, UInt32.toNat_zero, Nat.zero_add] at count
    have all : used = xs.length := by omega
    have fullInput : log.input = xs := by rw [sound.input, all, List.take_length]
    have api := trace_api_valid sound.history ((sound.result positive).trans ended)
    rw [fullInput] at api
    have sameLength : written.toNat = log.output.length := by rw [←scalar]; exact wordNat
    have physicalLog : Bytes after dest written.toNat log.output := by
      rw [sameLength, pointer, ←heapEq]
      exact finalBytes
    have sameOutput := observed_bytes_unique physicalLog physical
    rwa [sameOutput] at api
  · subst initRc
    obtain ⟨computed, failure, _rest⟩ := memory_failure_wrapper fresh unique globals bytes writable pointer actualInit
    have impossible : Z_MEM_ERROR = Z_OK := congrArg Prod.fst (Prod.mk.inj (Except.ok.inj (failure.symm.trans actual))).1
    cases impossible

/-- The family-level totality theorem with the exact API header and
metadata conclusion added on OK returns. Every allocator outcome remains
included on the same actual run and physical output. -/
theorem default_wrapper_api_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat)
    (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after,
      C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
        .ok ((rc, some (UInt64.ofNat output.length)), after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧
      (rc = Z_OK → (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid output xs) ∧
      (∀ b, after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc, output, after, actual, length, fits, physical, _valid, live, dead⟩ :=
    default_wrapper_total fresh unique globals objects bytes writable separate pointer
  refine ⟨rc, output, after, actual, length, fits, physical, ?_, live, dead⟩
  intro okay
  subst rc
  exact actual_success_api_valid fresh unique globals objects bytes writable separate pointer actual
    (by rw [length]; exact physical)

end ZlibF.Spec.Public.Proofs.CompressApi
