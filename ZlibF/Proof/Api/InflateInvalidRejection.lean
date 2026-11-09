import ZlibF.Proof.Api.Inflate

/-! This proves a property of the existing heap-free model. The model's
fixed-lag error-detection clause is a premise of its call relation. No
claim of implementation refinement, or validity of the lag for C, follows. -/
namespace ZlibF.Spec.Api.Proofs.InvalidRejection
open ZlibF.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem needsDict_take_two {w : Wrap} {b : Nat} {x y : List UInt8}
    (same : x.take 2 = y.take 2) (need : HdrNeedsDict w b x) : HdrNeedsDict w b y := by
  obtain ⟨hw,cmf,flg,rest,rfl,header,flag,fit⟩ := need
  cases y with
  | nil => simp at same
  | cons a ys =>
    cases ys with
    | nil => simp at same
    | cons f tail =>
      simp only [List.take_succ_cons,List.take_zero,List.cons.injEq,and_true] at same
      obtain ⟨rfl,rfl⟩ := same
      exact ⟨hw,cmf,flg,tail,rfl,header,flag,by simpa only [ZlibFits,List.head?_cons] using fit⟩

theorem needsDict_prefix {w : Wrap} {b : Nat} {x z : List UInt8}
    (pref : x <+: z) (need : HdrNeedsDict w b x) : HdrNeedsDict w b z := by
  have size : 2 ≤ x.length := by obtain ⟨_,_,_,_,rfl,_⟩ := need; simp
  obtain ⟨tail,rfl⟩ := pref
  exact needsDict_take_two (by simp [List.take_append_of_le_length size]) need

theorem viable_dictionary_irrelevant {w : Wrap} {b : Nat} {d1 d2 x z : List UInt8}
    (wrapped : w ≠ .raw) (pref : x <+: z) (noDict : ¬HdrNeedsDict w b z)
    (viable : Layer.Viable w b d1 x) : Layer.Viable w b d2 x := by
  rcases viable with short | ⟨tail,out,n,decoded⟩
  · exact Or.inl short
  · by_cases short : x.length < hdrLag w
    · exact Or.inl short
    · refine Or.inr ⟨tail,out,n,layer_decodes_dictionary_irrelevant wrapped ?_ decoded⟩
      intro need
      have xn : 2 ≤ x.length := by cases w <;> simp_all [hdrLag] <;> omega
      have nn : 2 ≤ n := by
        have cn : 2 ≤ ((x++tail).take n).length := by
          obtain ⟨_,_,_,_,same,_⟩ := need
          rw [same];simp
        simp only [List.length_take] at cn
        omega
      have same : ((x++tail).take n).take 2 = x.take 2 := by
        rw [List.take_take]
        simp [Nat.min_eq_left nn,List.take_append_of_le_length xn]
      exact noDict (needsDict_prefix pref (needsDict_take_two same need))

theorem detectable_dictionary_irrelevant {w : Wrap} {b : Nat} {d1 d2 z : List UInt8}
    (wrapped : w ≠ .raw) (noDict : ¬HdrNeedsDict w b z)
    (bad : Layer.Detectable w b d1 z) : Layer.Detectable w b d2 z := by
  obtain ⟨m,room,nonviable⟩ := bad
  exact ⟨m,room,fun viable => nonviable
    (viable_dictionary_irrelevant wrapped (List.take_prefix m z) noDict viable)⟩

theorem detectable_no_decoded_prefix {w : Wrap} {b : Nat} {d z part out : List UInt8}
    (bad : Layer.Detectable w b d z) (pref : part <+: z)
    (decoded : Layer.Decodes w b d part out) : False := by
  obtain ⟨m,_,nonviable⟩ := bad
  apply nonviable
  obtain ⟨tail,rfl⟩ := pref
  refine Or.inr ⟨(part++tail).drop m,out,part.length,?_⟩
  simpa only [List.take_append_drop,List.take_append_of_le_length (Nat.le_refl _),List.take_length] using decoded

def TraceInv (w : Wrap) (b : Nat) (d z : List UInt8) (s : InflState) : Prop :=
  s.wrap = w ∧ s.wbits = b ∧ s.Exact ∧ s.seen <+: z ∧
  (s.dict = some d ∨ (s.dict = none ∧ s.wrap ≠ .raw)) ∧
  (s.phase = .done → ∃ out,Layer.Decodes w b d s.seen out)

theorem dict_preserves {w : Wrap} {b : Nat} {d z : List UInt8} {s t : InflState} {rc : Int}
    (inv : TraceInv w b d z s) (call : InflSetDict s d rc t) : TraceInv w b d z t := by
  cases hw : s.wrap <;> simp only [InflSetDict,hw] at call
  · obtain ⟨_,(⟨_,rfl⟩ | ⟨_,rfl⟩)⟩ := call
    · obtain ⟨wrap,bits,ex,pref,_,done⟩ := inv
      exact ⟨by simpa only [hw] using wrap,bits,ex,pref,Or.inl rfl,done⟩
    · obtain ⟨wrap,bits,ex,pref,dict,_⟩ := inv
      exact ⟨by simpa only [hw] using wrap,bits,ex,pref,by simpa only [hw] using dict,by simp⟩
  all_goals
    split at call
    · rename_i need
      split at call
      · obtain ⟨_,rfl⟩ | ⟨_,rfl⟩ := call
        · obtain ⟨wrap,bits,ex,pref,_,_⟩ := inv
          exact ⟨by simpa only [hw] using wrap,bits,ex,pref,Or.inl rfl,by simp⟩
        · obtain ⟨wrap,bits,ex,pref,dict,_⟩ := inv
          exact ⟨by simpa only [hw] using wrap,bits,ex,pref,by simpa only [hw] using dict,by simp⟩
      · obtain ⟨_,rfl⟩ := call;exact inv
    · obtain ⟨_,rfl⟩ := call;exact inv

theorem inflate_preserves {w : Wrap} {b : Nat} {d z : List UInt8}
    {s t : InflState} {c : InflCall} {o : InflOut}
    (noDict : ¬HdrNeedsDict w b z) (inv : TraceInv w b d z s)
    (input : c.inp <+: z.drop s.seen.length) (call : InflStep s c o t) : TraceInv w b d z t := by
  obtain ⟨wrap,bits,ex,pref,dict,done⟩ := inv
  have offered : s.seen ++ c.inp <+: z := by
    obtain ⟨tail,eq⟩ := input
    refine ⟨tail,?_⟩
    rw [List.append_assoc,eq]
    obtain ⟨tail',rfl⟩ := pref
    simp
  have seenPrefix : s.seen ++ c.inp.take o.consumed <+: z := by
    apply List.IsPrefix.trans (l₂ := s.seen ++ c.inp) _ offered
    refine ⟨c.inp.drop o.consumed,?_⟩
    simp only [List.append_assoc,List.take_append_drop]
  cases hb : c.badBuf with
  | true =>
    rw [(call.1 hb).2.2.2]
    exact ⟨wrap,bits,ex,pref,dict,done⟩
  | false =>
    have run := call.2 hb
    cases phase : s.phase with
    | done | bad | mem | needDict | syncing =>
      simp only [phase] at run
      rw [run.2.2.2]
      exact ⟨wrap,bits,ex,pref,dict,done⟩
    | running =>
      simp only [phase] at run
      rcases run with run | run
      · rcases run with ⟨_,_,seen,_,_,_,wrap',bits',dict',precise,validate,_,_,_,codes,
          ok,buf,ended,bad,need,_,decoded,_,_,_,_,_,_,_,_⟩
        have fixed : t.dict = some d ∨ (t.dict = none ∧ t.wrap ≠ .raw) := by
          simpa only [dict',wrap'] using dict
        refine ⟨wrap'.trans wrap,bits'.trans bits,⟨precise.trans ex.1,validate.trans ex.2⟩,
          by simpa only [seen] using seenPrefix,fixed,?_⟩
        intro done'
        have code : o.rc = Z.streamEnd := by
          rcases codes with h | h | h | h | h
          · have p := (ok h).2.2;rw [p] at done';cases done'
          · exact h
          · have p := (need h).1;rw [p] at done';cases done'
          · have p := bad h;rw [p] at done';cases done'
          · have p := (buf h).2;rw [p] at done';cases done'
        have format : Layer.Decodes w b s.dictEff (s.seen++c.inp.take o.consumed) (s.out++o.produced) := by
          simpa only [wrap,bits] using decoded ex code
        have original : Layer.Decodes w b d (s.seen++c.inp.take o.consumed) (s.out++o.produced) := by
          rcases dict with known | ⟨unknown,wrapped⟩
          · simpa only [InflState.dictEff,known,Option.getD_some] using format
          · apply layer_decodes_dictionary_irrelevant (by simpa only [wrap] using wrapped) ?_ format
            intro asks
            exact noDict (needsDict_prefix seenPrefix asks)
        exact ⟨s.out++o.produced,by simpa only [seen] using original⟩
      · rcases run with ⟨_,_,_,_,phase',seen,_,_,_,_,wrap',bits',dict',precise,validate,_,_,_,_,_,_⟩
        refine ⟨wrap'.trans wrap,bits'.trans bits,⟨precise.trans ex.1,validate.trans ex.2⟩,
          by simpa only [seen] using seenPrefix,?_,?_⟩
        · simpa only [dict',wrap'] using dict
        · intro h;rw [phase'] at h;cases h

theorem trace_fields {w : Wrap} {b : Nat} {d z : List UInt8} {s : InflState}
    (noDict : ¬HdrNeedsDict w b z) (trace : InflTrace z d (InflStart w b d) s) :
    TraceInv w b d z s := by
  have keep : ∀ {a t}, InflTrace z d a t → TraceInv w b d z a → TraceInv w b d z t := by
    intro a t hist
    induction hist with
    | nil => exact id
    | step input call _ ih => intro hi;exact ih (inflate_preserves noDict hi input call.1)
    | dict call _ ih => intro hi;exact ih (dict_preserves hi call)
  apply keep trace
  cases w <;> simp [TraceInv,InflStart,InflState.fresh,InflState.Exact]

/-- The original fixed goal follows in the abstract model because its call
relation already assumes the fixed-lag detection condition. This theorem
does not establish that condition for the translated C implementation. -/
theorem inflate_rejects_invalid : Goal.inflate_rejects_invalid := by
  intro w b d z s _ detectable noDict trace
  obtain ⟨wrap,bits,ex,pref,dict,done⟩ := trace_fields noDict trace
  refine ⟨?_,?_⟩
  · intro completed
    obtain ⟨out,decoded⟩ := done completed
    exact detectable_no_decoded_prefix detectable pref decoded
  · intro running c r t buffers input flush call spare
    have allInput : s.seen ++ c.inp = z := by
      rw [input]
      obtain ⟨tail,eq⟩ := pref
      rw [←eq,List.drop_left]
    have sameBad : Layer.Detectable s.wrap s.wbits s.dictEff (s.seen++c.inp) := by
      rw [wrap,bits,allInput]
      rcases dict with known | ⟨unknown,wrapped⟩
      · simpa only [InflState.dictEff,known,Option.getD_some] using detectable
      · exact detectable_dictionary_irrelevant (by simpa only [wrap] using wrapped) noDict detectable
    have run : InflRun s c r.out t := by
      simpa only [running] using call.1.2 buffers
    rcases run with ordinary | memory
    · rcases ordinary with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,detect,_,_,_,_⟩
      left
      apply call.2.trans
      exact detect ex flush (fun _ => by simpa only [wrap,bits,allInput] using noDict) sameBad spare
    · exact Or.inr (call.2.trans memory.1)

#print axioms inflate_rejects_invalid

/-- The invalid-input domain is inhabited in the original model: a bad
method header followed by eight bytes meets the original detection lag. -/
theorem invalid_rejection_domain_witness :
    let z : List UInt8 := [0,0,0,0,0,0,0,0,0,0]
    InflCfg .zlib 15 ∧ Layer.Detectable .zlib 15 [] z ∧
      ¬HdrNeedsDict .zlib 15 z ∧
      InflTrace z [] (InflStart .zlib 15 []) (InflStart .zlib 15 []) ∧
      (InflStart .zlib 15 []).phase = .running := by
  dsimp only
  refine ⟨⟨15,by decide⟩,?_,?_,.nil,rfl⟩
  · refine ⟨2,by decide,?_⟩
    change ¬Layer.Viable .zlib 15 [] [0,0]
    intro viable
    rcases viable with short | ⟨tail,out,n,decoded⟩
    · exact absurd short (by decide)
    · obtain ⟨⟨cmf,flg,pre,body,same,header,_⟩,_⟩ := decoded
      cases n with
      | zero => simp at same
      | succ n =>
        cases n with
        | zero => simp at same
        | succ n =>
          simp only [List.cons_append,List.take_succ_cons,List.cons.injEq] at same
          have cmfZero := same.1.symm
          subst cmf
          exact absurd header.1 (by decide)
  · intro needs
    obtain ⟨_,cmf,flg,tail,same,header,_⟩ := needs
    simp only [List.cons.injEq] at same
    have cmfZero := same.1.symm
    subst cmf
    exact absurd header.1 (by decide)

#print axioms invalid_rejection_domain_witness

/-- A concrete call in the model witnesses the non-memory-error branch.
This is a relation witness, not execution of the translated decoder. -/
theorem model_bad_header_call :
    InflRunOk (InflStart .zlib 15 [])
      ⟨[0,0,0,0,0,0,0,0,0,0],1,.noFlush,false⟩ ⟨2,[],Z.dataError⟩
      {InflStart .zlib 15 [] with seen := [0,0],phase := .bad,totalIn := 2} := by
  have nonviable (dictionary : List UInt8) : ¬Layer.Viable .zlib 15 dictionary [0,0] := by
    intro viable
    rcases viable with short | ⟨tail,out,n,decoded⟩
    · exact absurd short (by decide)
    · obtain ⟨⟨cmf,flg,pre,body,same,header,_⟩,_⟩ := decoded
      cases n with
      | zero => simp at same
      | succ n =>
        cases n with
        | zero => simp at same
        | succ n =>
          simp only [List.cons_append,List.take_succ_cons,List.cons.injEq] at same
          have cmfZero := same.1.symm
          subst cmf
          exact absurd header.1 (by decide)
  simp only [InflRunOk,InflStart,InflState.fresh]
  simp only [List.take_succ_cons,List.take_zero,List.append_nil]
  simp [Z.ok,Z.streamEnd,Z.needDict,Z.dataError,Z.bufError,InflState.Exact,
    InflOut.Progress,InflHdrClause,checkValue,HdrNeedsDict,Zlib.HeaderOK]
  constructor
  · exact fun _ dictionary _ => nonviable dictionary
  · intro _ n _ out decoded
    have bad := invalid_rejection_domain_witness.2.1
    exact False.elim (detectable_no_decoded_prefix bad (List.take_prefix n _) (by
      simpa only [InflState.dictEff,Option.getD_none] using decoded))

#print axioms model_bad_header_call
end ZlibF.Spec.Api.Proofs.InvalidRejection
