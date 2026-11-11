import ZlibF.Proof.«inflate.c.wrap-public-history»
import ZlibF.Proof.«inflate.c.low-dictionary-phase»

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem dictionary_success_in_DICT
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {p : BPtr} {n : UInt32} (good : Good h r zs z s) (wrapped : s.wrap = 5)
    (actual : C.run (inflateSetDictionary (some r) p n) h = .ok (Z_OK, after)) : s.mode = DICT := by
  apply Classical.byContradiction
  intro different
  have source := inflateSetDictionary_refused_any good.live p n
    (Or.inr ⟨by rw [wrapped]; decide, different⟩)
  have code := congrArg Prod.fst (Except.ok.inj (source.symm.trans actual))
  exact (by decide : Z_STREAM_ERROR ≠ Z_OK) code

theorem suffix_append_output {α : Type} {logical physical : List α}
    (suffix : logical <:+ physical) (output : List α) : logical ++ output <:+ physical ++ output := by
  obtain ⟨older, values⟩ := suffix
  exact ⟨older, by rw [← List.append_assoc, values]⟩

theorem suffix_retained {α : Type} {logical physical : List α} (suffix : logical <:+ physical)
    (capacity : Nat) :
    logical.drop (logical.length - capacity) <:+ physical.drop (physical.length - capacity) := by
  have eq := List.suffix_iff_eq_drop.mp suffix
  have value : logical.drop (logical.length - capacity) =
      physical.drop ((physical.length - logical.length) + (logical.length - capacity)) := by
    calc
      _ = (physical.drop (physical.length - logical.length)).drop (logical.length - capacity) :=
        congrArg (fun xs : List α => xs.drop (logical.length - capacity)) eq
      _ = _ := List.drop_drop
  rw [value]
  exact List.drop_suffix_drop_left _ (by have bound := suffix.length_le; omega)

/-- Default source-only data histories keep the real wrapper enabled and
have emitted no output while still in header/dictionary parsing. The
logical dictionary plus output is a suffix of physical history, including
repeated short dictionary installation. -/
theorem DataHistory.logical_suffix
    {r : ZStreamRef} {h : Heap} {log : DataLog} {history : List UInt8}
    (trace : DataHistory r h log history) :
    ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧
      (s.mode < CHECK → InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) ∧
      s.wrap = 5 ∧ (s.mode ≤ DICT → log.output = []) ∧ (log.dictionary ++ log.output) <:+ history := by
  induction trace with
  | @init before after version domain platform allocation actual =>
    obtain ⟨computed, z, s, run, initial, current, _reachable⟩ :=
      inflate_default_state_initial before r version domain platform allocation
    have source : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, computed) := by
      simpa only [inflateInit_, DEF_WBITS] using run
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    obtain ⟨otherZ, otherS, good, alloc, free, _head, null, _bits, _reqbits, wrap, _rest⟩ := initial
    have sameZ : otherZ = z := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
    have sameS : otherS = s := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
    subst otherZ otherS
    refine ⟨before.nextBlk, z, s, current, ⟨alloc, free⟩, ?_, wrap, (fun _ => rfl), ⟨[], rfl⟩⟩
    intro _active
    simpa using null_dictionary_empty current.good null
  | @caller before after log history _prior edit platform ih =>
    obtain ⟨zs, z, s, current, allocator, dictionary, wrap, low, suffix⟩ := ih
    obtain ⟨stream, final, finalAllocator, retained⟩ :=
      rebuffer_default_history current allocator edit platform dictionary
    exact ⟨zs, stream, s, final, finalAllocator, retained, wrap, low, suffix⟩
  | @step before after log history flush rc input output used _prior _fit actual ih =>
    obtain ⟨zs, z, s, current, allocator, dictionary, wrap, low, suffix⟩ := ih
    have entry : EntryHeaderFacts before r s z := EntryHeaderFacts.of_zlib current (Or.inr wrap)
    obtain ⟨stream, state, final, finalAllocator, retained⟩ := dataStep_history current allocator entry actual dictionary
    have nextWrap : state.wrap = 5 := (dataStep_wrap_unchanged current allocator entry actual final.good).trans wrap
    have nextLow : state.mode ≤ DICT → log.output ++ output = [] := by
      intro nextLow
      obtain ⟨beforeLow, empty⟩ := ActiveSourceCut.dataStep_low_output_empty current allocator entry actual final.good nextLow
      rw [low beforeLow, empty]
      rfl
    refine ⟨zs, stream, state, final, finalAllocator, retained, nextWrap, nextLow, ?_⟩
    simpa only [List.append_assoc] using suffix_append_output suffix output
  | @dictionary before after log history p n bytes rc _prior _fit args input actual ih =>
    obtain ⟨zs, z, s, current, allocator, dictionary, wrap, low, suffix⟩ := ih
    obtain ⟨code, heap, state, run, final, retained⟩ := dictionary_history_guarded current allocator args input dictionary
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    obtain ⟨wrapEq, modes⟩ := dictionary_call_fields current allocator args input actual final.good.live.hs
    have nextWrap := wrapEq.trans wrap
    have nextLow : state.mode ≤ DICT → log.output = [] := by
      intro nextLow
      rcases modes with mode | mem
      · exact low (by simpa only [mode] using nextLow)
      · rw [mem] at nextLow
        exact False.elim ((by decide : ¬ MEM ≤ DICT) nextLow)
    refine ⟨zs, z, state, final, allocator, retained, nextWrap, nextLow, ?_⟩
    by_cases success : rc = Z_OK
    · have mode := dictionary_success_in_DICT current.good wrap (by simpa only [success] using actual)
      have empty := low (by rw [mode]; exact UInt32.le_refl _)
      simp only [success, ite_true, empty, List.append_nil]
      exact ⟨history, rfl⟩
    · simpa only [if_neg success] using suffix

/-- A default data history decodes a zlib stream, so no gzip header record
is attached and the per-call header facts hold. -/
theorem DataHistory.entry {r : ZStreamRef} {h : Heap} {log : DataLog} {history : List UInt8}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (trace : DataHistory r h log history) (current : DefaultStateJ h r zs z s) :
    EntryHeaderFacts h r s z := by
  obtain ⟨zs', z', s', current', _, _, wrap, _⟩ := trace.logical_suffix
  have sameZ : z' = z := Option.some.inj (current'.good.live.hz.symm.trans current.good.live.hz)
  subst z'
  have sameIndex : zs' = zs := by simpa using current'.good.live.zst.symm.trans current.good.live.zst
  subst zs'
  have sameS : s' = s := Option.some.inj (current'.good.live.hs.symm.trans current.good.live.hs)
  subst s'
  exact EntryHeaderFacts.of_zlib current (Or.inr wrap)

/-- The logical history needed by valid back references is a suffix of
the actual saved window. Extra bytes from earlier dictionary installation
are retained explicitly rather than assumed absent. -/
theorem DataHistory.saved_logical_suffix
    {r : ZStreamRef} {h : Heap} {log : DataLog} {history : List UInt8}
    (trace : DataHistory r h log history) :
    ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧ s.wrap = 5 ∧
      (s.mode ≤ DICT → log.output = []) ∧
      (s.mode < CHECK →
        (s.window = .null ∧ s.whave = 0 ∧
          (log.dictionary ++ log.output).drop
            ((log.dictionary ++ log.output).length - 2 ^ s.wbits.toNat) = []) ∨
        ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧
          a.size = 2 ^ s.wbits.toNat ∧
          (log.dictionary ++ log.output).drop
            ((log.dictionary ++ log.output).length - 2 ^ s.wbits.toNat) <:+
            Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat s.whave.toNat 0) := by
  obtain ⟨zs, z, s, current, allocator, dictionary, wrap, low, suffix⟩ := trace.logical_suffix
  have kept := suffix_retained suffix (2 ^ s.wbits.toNat)
  refine ⟨zs, z, s, current, allocator, wrap, low, ?_⟩
  intro active
  rcases dictionary_saved_or_lazy current.good (dictionary active) with lazy | ⟨w, a, pointer, get, ro, size, saved⟩
  · rw [lazy.2.2] at kept
    exact Or.inl ⟨lazy.1, lazy.2.1, List.IsSuffix.eq_of_length_le kept (by simp)⟩
  · exact Or.inr ⟨w, a, pointer, get, ro, size, by simpa only [saved] using kept⟩

#print axioms dictionary_success_in_DICT
#print axioms suffix_append_output
#print axioms suffix_retained
#print axioms DataHistory.logical_suffix
#print axioms DataHistory.saved_logical_suffix
end Zlib.Inflate.Proofs.WindowHistory
