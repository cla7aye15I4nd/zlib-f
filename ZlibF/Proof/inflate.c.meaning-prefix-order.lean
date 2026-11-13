import ZlibF.Proof.«inflate.c.meaning»
import ZlibF.Proof.Format.Deflate
import ZlibF.Proof.Format.Token
import ZlibF.Proof.«inffast.c.sig»

/-!
# inflate.c: a parse position on a valid stream is on its parse

Heap-free. If the deflate grammar of the format meaning (`DeflateParsed`)
reaches a position on the bits `bits`, and `bits ++ more` is parsed by the
format specification (`Blocks`), then the rest `more` is parsed from that
position (`Resid`): the position lies on the one parse of the stream. Hence
its output is a beginning of the decoding, and the end of the last block is
the end of the specification's blocks.
-/

namespace Zlib.Inflate.Proofs
open C ZlibF.Spec ZlibF.Spec.Proofs
set_option autoImplicit false

/-! ## History only grows -/

theorem copyBack_prefix (dict : List UInt8) (dist : Nat) :
    ∀ (n : Nat) (h : List UInt8), h <+: copyBack dict dist n h
  | 0, h => List.prefix_refl h
  | n + 1, h => (List.prefix_append h _).trans (copyBack_prefix dict dist n _)

theorem _root_.ZlibF.Spec.Symbols.history {L D : List Nat} {dict h : List UInt8} {inp rest : List Bool}
    {out : List UInt8} (parse : Symbols L D dict h inp rest out) : h <+: out := by
  induction parse with
  | eob => exact List.prefix_refl _
  | lit _ _ _ ih => exact (List.prefix_append _ _).trans ih
  | copy _ _ _ _ _ _ _ _ _ ih => exact (copyBack_prefix _ _ _ _).trans ih

theorem _root_.ZlibF.Spec.Body.history {dict : List UInt8} {bt : Nat} {h : List UInt8} {inp rest : List Bool}
    {out : List UInt8} (parse : Body dict bt h inp rest out) : h <+: out := by
  cases parse with
  | stored => exact List.prefix_append _ _
  | fixed symbols => exact symbols.history
  | dynamic _ _ _ _ _ _ _ _ _ _ symbols => exact symbols.history

theorem _root_.ZlibF.Spec.Blocks.history {dict h : List UInt8} {inp rest : List Bool} {out : List UInt8}
    (parse : Blocks dict h inp rest out) : h <+: out := by
  induction parse with
  | last _ _ body => exact body.history
  | more _ _ body _ ih => exact body.history.trans ih

/-! ## One token is determined by its bits -/

theorem _root_.ZlibF.Spec.Token.Step.det {L D : List Nat} {dict h : List UInt8} {inp r1 r2 : List Bool}
    {o1 o2 : List UInt8} {f1 f2 : Bool} (s1 : Token.Step L D dict h inp r1 o1 f1)
    (s2 : Token.Step L D dict h inp r2 o2 f2) : r1 = r2 ∧ o1 = o2 ∧ f1 = f2 := by
  cases s1 with
  | literal d1 lt1 =>
    cases s2 with
    | literal d2 _ =>
      rw [d1] at d2
      cases d2
      exact ⟨rfl, rfl, rfl⟩
    | copy d2 lo _ =>
      rw [d1] at d2
      cases d2
      omega
    | eob d2 =>
      rw [d1] at d2
      cases d2
      omega
  | copy d1 lo1 hi1 x1 e1 ds1 y1 _ =>
    cases s2 with
    | literal d2 lt2 =>
      rw [d1] at d2
      cases d2
      omega
    | copy d2 _ _ x2 e2 _ y2 _ =>
      rw [d1] at d2
      cases d2
      rw [x1] at x2
      cases x2
      rw [e1] at e2
      cases e2
      rw [y1] at y2
      cases y2
      exact ⟨rfl, rfl, rfl⟩
    | eob d2 =>
      rw [d1] at d2
      cases d2
      omega
  | eob d1 =>
    cases s2 with
    | literal d2 lt2 =>
      rw [d1] at d2
      cases d2
      omega
    | copy d2 lo _ =>
      rw [d1] at d2
      cases d2
      omega
    | eob d2 =>
      rw [d1] at d2
      cases d2
      exact ⟨rfl, rfl, rfl⟩

theorem _root_.ZlibF.Spec.Token.Step.append {L D : List Nat} {dict h : List UInt8} {inp rest : List Bool}
    {out : List UInt8} {finished : Bool} (hL : Ext L) (hD : Ext D)
    (step : Token.Step L D dict h inp rest out finished) (X : List Bool) :
    Token.Step L D dict h (inp ++ X) (rest ++ X) out finished := by
  cases step with
  | literal d lt => exact .literal (hL _ _ _ X d) lt
  | copy d lo hi x e ds y bound =>
    exact .copy (hL _ _ _ X d) lo hi (readBits_append _ _ _ _ X x) (hD _ _ _ X e) ds
      (readBits_append _ _ _ _ X y) bound
  | eob d => exact .eob (hL _ _ _ X d)

#print axioms ZlibF.Spec.Symbols.history
#print axioms ZlibF.Spec.Blocks.history
#print axioms ZlibF.Spec.Token.Step.det
#print axioms ZlibF.Spec.Token.Step.append

/-! ## Bits of fixed fields -/

theorem natToBitsLSB_eq_bitsOfNat (n v : Nat) :
    natToBitsLSB n v = Zlib.Inffast.Proofs.bitsOfNat v n := by
  apply List.ext_getElem
  · simp [natToBitsLSB, Zlib.Inffast.Proofs.bitsOfNat]
  · intro i _ _
    simp only [natToBitsLSB, Zlib.Inffast.Proofs.bitsOfNat, List.getElem_map, List.getElem_range]
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with z | o <;> simp [*]

theorem readBits_natToBitsLSB {n v : Nat} (small : v < 2 ^ n) (X : List Bool) :
    readBits n (natToBitsLSB n v ++ X) = some (v, X) := by
  rw [natToBitsLSB_eq_bitsOfNat, Zlib.Inffast.Proofs.readBits_bitsOfNat n n v X (Nat.le_refl _)]
  simp [Nat.mod_eq_of_lt small, Zlib.Inffast.Proofs.bitsOfNat_zero]

theorem readBits_byteBits (byte : UInt8) (X : List Bool) :
    readBits 8 (byteBits byte ++ X) = some (byte.toNat, X) := by
  change readBits 8 (Zlib.Inffast.Proofs.bitsOfNat byte.toNat 8 ++ X) = _
  simpa only [show 2 ^ 8 = (256 : Nat) from rfl, Nat.mod_eq_of_lt byte.toNat_lt,
    Nat.sub_self, Zlib.Inffast.Proofs.bitsOfNat_zero, List.nil_append] using
    Zlib.Inffast.Proofs.readBits_bitsOfNat 8 8 byte.toNat X (by omega)

theorem readBits_one (b : Bool) (X : List Bool) :
    readBits 1 (b :: X) = some ((if b then 1 else 0), X) := by
  cases b <;> rfl

theorem readBits_two (b1 b2 : Bool) (X : List Bool) :
    readBits 2 (b1 :: b2 :: X) = some ((if b1 then 1 else 0) + 2 * (if b2 then 1 else 0), X) := by
  cases b1 <;> cases b2 <;> rfl

/-! ## The rest of a stream from a position -/

/-- After a block that ends with output `h` at bits `r`: the end of the
stream if the block was final, else more blocks. -/
def Cont (dict : List UInt8) (final : Bool) (h : List UInt8) (r tail : List Bool)
    (outF : List UInt8) : Prop :=
  if final then r = tail ∧ h = outF else Blocks dict h r tail outF

theorem Cont.history {dict : List UInt8} {final : Bool} {h : List UInt8} {r tail : List Bool}
    {outF : List UInt8} (cont : Cont dict final h r tail outF) : h <+: outF := by
  unfold Cont at cont
  split at cont
  · rw [cont.2]
    exact List.prefix_refl _
  · exact cont.history

/-- The specification parses the bits `more` after the position: they
complete its block (or token) and the rest of the stream, ending at `tail`
with output `outF`. Positions inside a token carry no rest. -/
def Resid (dict : List UInt8) (pos : DeflatePos) (more tail : List Bool) (outF : List UInt8) :
    Prop :=
  match pos with
  | ⟨out, _, .boundary⟩ => Blocks dict out more tail outF
  | ⟨out, final, .storedHeader⟩ =>
      ∃ r h', Body dict 0 out more r h' ∧ Cont dict final h' r tail outF
  | ⟨out, final, .stored remaining⟩ =>
      ∃ bs r, readBytes remaining more = some (bs, r) ∧ Cont dict final (out ++ bs) r tail outF
  | ⟨out, final, .dynamicHeader header⟩ =>
      ∃ r h', Body dict 2 out (header ++ more) r h' ∧ Cont dict final h' r tail outF
  | ⟨out, final, .codes L D .none⟩ =>
      Ext L ∧ Ext D ∧ ∃ r h', Symbols L D dict out more r h' ∧ Cont dict final h' r tail outF
  | ⟨_, _, .codes _ _ _⟩ => True
  | ⟨out, _, .finished⟩ => more = tail ∧ out = outF

/-- The three header bits of a block select its body. -/
theorem blocks_header {dict out : List UInt8} {b0 b1 b2 : Bool} {more tail : List Bool}
    {outF : List UInt8} (blocks : Blocks dict out (b0 :: b1 :: b2 :: more) tail outF) :
    ∃ r h', Body dict ((if b1 then 1 else 0) + 2 * (if b2 then 1 else 0)) out more r h' ∧
      Cont dict b0 h' r tail outF := by
  cases blocks with
  | last one two body =>
    rw [readBits_one] at one
    cases b0 with
    | false => simp at one
    | true =>
      simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at one
      obtain ⟨_, rfl⟩ := one
      rw [readBits_two] at two
      simp only [Option.some.injEq, Prod.mk.injEq] at two
      obtain ⟨rfl, rfl⟩ := two
      exact ⟨_, _, body, by simp [Cont]⟩
  | more one two body rest =>
    rw [readBits_one] at one
    cases b0 with
    | true => simp at one
    | false =>
      simp only [Option.some.injEq, Prod.mk.injEq] at one
      obtain ⟨_, rfl⟩ := one
      rw [readBits_two] at two
      simp only [Option.some.injEq, Prod.mk.injEq] at two
      obtain ⟨rfl, rfl⟩ := two
      exact ⟨_, _, body, by simpa [Cont] using rest⟩

/-- A stored body read after its padding: the padding is the bits before the
next byte boundary. -/
theorem stored_drop_pad {pad rest : List Bool} (padSmall : pad.length < 8)
    (aligned : rest.length % 8 = 0) : (pad ++ rest).drop ((pad ++ rest).length % 8) = rest := by
  have : (pad ++ rest).length % 8 = pad.length := by
    rw [List.length_append]
    omega
  rw [this, List.drop_left]

#print axioms readBits_natToBitsLSB
#print axioms blocks_header

/-! ## Every position reached on a valid stream lies on its parse -/

theorem deflateParsed_resid {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) :
    ∀ more tail outF, (bits ++ more).length % 8 = 0 →
      Blocks dict [] (bits ++ more) tail outF → Resid dict pos more tail outF := by
  induction parsed with
  | start =>
    intro more tail outF _ blocks
    simpa [Resid] using blocks
  | @storedStart consumed out final prev ih =>
    intro more tail outF aligned blocks
    obtain ⟨r, h', body, cont⟩ := blocks_header
      (ih ([final, false, false] ++ more) tail outF (by simpa [List.append_assoc] using aligned)
        (by simpa [List.append_assoc] using blocks))
    exact ⟨r, h', by simpa using body, cont⟩
  | @storedPad consumed out final pad prev padLength ih =>
    intro more tail outF aligned blocks
    obtain ⟨r, h', body, cont⟩ := ih (pad ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    have moreAligned : more.length % 8 = 0 := by
      simp only [List.length_append] at aligned
      omega
    refine ⟨r, h', ?_, cont⟩
    cases body with
    | stored one two comp bytes =>
      rw [stored_drop_pad (by omega) moreAligned] at one
      exact .stored (by rwa [moreAligned, List.drop_zero]) two comp bytes
  | @storedLength consumed out final pad len prev padLength small ih =>
    intro more tail outF aligned blocks
    obtain ⟨r, h', body, cont⟩ :=
      ih (pad ++ (natToBitsLSB 16 len ++ (natToBitsLSB 16 (65535 - len) ++ more))) tail outF
        (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    have restAligned :
        (natToBitsLSB 16 len ++ (natToBitsLSB 16 (65535 - len) ++ more)).length % 8 = 0 := by
      simp only [List.length_append] at aligned ⊢
      simp only [natToBitsLSB, List.length_map, List.length_range] at aligned ⊢
      omega
    cases body with
    | stored one two comp bytes =>
      rw [stored_drop_pad (by omega) restAligned, readBits_natToBitsLSB (by omega)] at one
      simp only [Option.some.injEq, Prod.mk.injEq] at one
      obtain ⟨rfl, rfl⟩ := one
      rw [readBits_natToBitsLSB (by omega)] at two
      simp only [Option.some.injEq, Prod.mk.injEq] at two
      obtain ⟨_, rfl⟩ := two
      exact ⟨_, _, bytes, cont⟩
  | @storedByte consumed out final remaining byte prev ih =>
    intro more tail outF aligned blocks
    obtain ⟨bs, r, read, cont⟩ := ih (byteBits byte ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    simp only [readBytes, readBits_byteBits] at read
    cases rest : readBytes remaining more with
    | none => simp [rest] at read
    | some pair =>
      obtain ⟨bs', r'⟩ := pair
      simp only [rest, Option.some.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      refine ⟨bs', r', rest, ?_⟩
      have byteEq : byte.toNat.toUInt8 = byte := UInt8.toNat.inj (by simp)
      simpa [byteEq, List.append_assoc] using cont
  | @storedEnd consumed out prev ih =>
    intro more tail outF aligned blocks
    obtain ⟨bs, r, read, cont⟩ := ih more tail outF aligned blocks
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    simpa [Cont, Resid] using cont
  | @storedFinal consumed out prev ih =>
    intro more tail outF aligned blocks
    obtain ⟨bs, r, read, cont⟩ := ih more tail outF aligned blocks
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    simpa [Cont, Resid] using cont
  | @fixedHeader consumed out final prev ih =>
    intro more tail outF aligned blocks
    obtain ⟨r, h', body, cont⟩ := blocks_header
      (ih ([final, true, false] ++ more) tail outF (by simpa [List.append_assoc] using aligned)
        (by simpa [List.append_assoc] using blocks))
    have body : Body dict 1 out more r h' := by simpa using body
    cases body with
    | fixed symbols => exact ⟨ext_fixedLit, ext_fixedDist, r, h', symbols, cont⟩
  | @dynamicStart consumed out final prev ih =>
    intro more tail outF aligned blocks
    obtain ⟨r, h', body, cont⟩ := blocks_header
      (ih ([final, false, true] ++ more) tail outF (by simpa [List.append_assoc] using aligned)
        (by simpa [List.append_assoc] using blocks))
    exact ⟨r, h', by simpa using body, cont⟩
  | @dynamicBits consumed header out final moreBits prev ih =>
    intro more tail outF aligned blocks
    obtain ⟨r, h', body, cont⟩ := ih (moreBits ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    exact ⟨r, h', by simpa [List.append_assoc] using body, cont⟩
  | @dynamicDone consumed header out final L D prev dyn ih =>
    intro more tail outF aligned blocks
    obtain ⟨r, h', body, cont⟩ := ih more tail outF aligned blocks
    obtain ⟨hlit, hdist, hclen, r1, r2, r3, r4, cl, lens, e1, e2, e3, counts, e4, acc, codeLens,
      eob, accL, accD, rfl, rfl⟩ := dyn
    cases body with
    | dynamic f1 f2 f3 _ f4 _ codeLens' _ _ _ symbols =>
      rw [readBits_append _ _ _ _ more e1] at f1
      simp only [Option.some.injEq, Prod.mk.injEq] at f1
      obtain ⟨rfl, rfl⟩ := f1
      rw [readBits_append _ _ _ _ more e2] at f2
      simp only [Option.some.injEq, Prod.mk.injEq] at f2
      obtain ⟨rfl, rfl⟩ := f2
      rw [readBits_append _ _ _ _ more e3] at f3
      simp only [Option.some.injEq, Prod.mk.injEq] at f3
      obtain ⟨rfl, rfl⟩ := f3
      rw [readCodeLenLens_append _ _ _ _ more e4] at f4
      simp only [Option.some.injEq, Prod.mk.injEq] at f4
      obtain ⟨rfl, rfl⟩ := f4
      have extended := codeLens.append (ext_acceptable acc) more
      obtain ⟨restEq, lensEq⟩ := codeLens'.det extended
      simp only [List.nil_append] at restEq
      subst restEq lensEq
      exact ⟨ext_acceptable accL, ext_acceptable accD, r, h', symbols, cont⟩
  | @token consumed tokenBits out out' final L D prev step ih =>
    intro more tail outF aligned blocks
    obtain ⟨extL, extD, r, h', symbols, cont⟩ := ih (tokenBits ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    have long := step.append extL extD more
    obtain ⟨rest, next, fin, exposed, outcome⟩ := ZlibF.Spec.Token.symbols_exposes_step _ _ _ _ _ _ _ symbols
    obtain ⟨restEq, nextEq, finEq⟩ := exposed.det long
    subst restEq nextEq finEq
    rcases outcome with ⟨impossible, _, _⟩ | ⟨_, following⟩
    · cases impossible
    · exact ⟨extL, extD, r, h', by simpa using following, cont⟩
  | @endOfBlock consumed tokenBits out L D prev step ih =>
    intro more tail outF aligned blocks
    obtain ⟨extL, extD, r, h', symbols, cont⟩ := ih (tokenBits ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    have long := step.append extL extD more
    obtain ⟨rest, next, fin, exposed, outcome⟩ := ZlibF.Spec.Token.symbols_exposes_step _ _ _ _ _ _ _ symbols
    obtain ⟨restEq, nextEq, finEq⟩ := exposed.det long
    subst restEq nextEq finEq
    rcases outcome with ⟨_, restR, nextH⟩ | ⟨impossible, _⟩
    · subst restR nextH
      simpa [Cont, Resid] using cont
    · cases impossible
  | @endOfFinal consumed tokenBits out L D prev step ih =>
    intro more tail outF aligned blocks
    obtain ⟨extL, extD, r, h', symbols, cont⟩ := ih (tokenBits ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    have long := step.append extL extD more
    obtain ⟨rest, next, fin, exposed, outcome⟩ := ZlibF.Spec.Token.symbols_exposes_step _ _ _ _ _ _ _ symbols
    obtain ⟨restEq, nextEq, finEq⟩ := exposed.det long
    subst restEq nextEq finEq
    rcases outcome with ⟨_, restR, nextH⟩ | ⟨impossible, _⟩
    · subst restR nextH
      simpa [Cont, Resid] using cont
    · cases impossible
  | @partialToken consumed out final L D pending pbits prev pp ih =>
    intro more tail outF aligned blocks
    cases pending with
    | none =>
      have empty : pbits = [] := pp
      subst empty
      simpa using ih more tail outF (by simpa using aligned) (by simpa using blocks)
    | _ => trivial
  | partialCopy => intro _ _ _ _ _; trivial
  | partialLiteral => intro _ _ _ _ _; trivial

#print axioms deflateParsed_resid

/-- The output of a position outside a token is a beginning of the decoding. -/
theorem Resid.output {dict out : List UInt8} {final : Bool} {stage : BlockStage}
    {more tail : List Bool} {outF : List UInt8}
    (settled : ∀ L D p, stage = .codes L D p → p = .none)
    (resid : Resid dict ⟨out, final, stage⟩ more tail outF) : out <+: outF := by
  cases stage with
  | boundary => exact Blocks.history resid
  | storedHeader =>
    obtain ⟨_, _, body, cont⟩ := resid
    exact body.history.trans cont.history
  | stored remaining =>
    obtain ⟨_, _, _, cont⟩ := resid
    exact (List.prefix_append _ _).trans cont.history
  | dynamicHeader header =>
    obtain ⟨_, _, body, cont⟩ := resid
    exact body.history.trans cont.history
  | codes L D p =>
    have none := settled L D p rfl
    subst none
    obtain ⟨_, _, _, _, symbols, cont⟩ := resid
    exact symbols.history.trans cont.history
  | finished =>
    obtain ⟨_, eq⟩ := resid
    rw [eq]
    exact List.prefix_refl _

/-- A complete token from a position on the parse continues the parse. -/
theorem Resid.token {dict out out' : List UInt8} {final : Bool} {L D : List Nat}
    {tokenBits more tail : List Bool} {outF : List UInt8}
    (resid : Resid dict ⟨out, final, .codes L D .none⟩ (tokenBits ++ more) tail outF)
    (step : Token.Step L D dict out tokenBits [] out' false) :
    Resid dict ⟨out', final, .codes L D .none⟩ more tail outF := by
  obtain ⟨extL, extD, r, h', symbols, cont⟩ := resid
  have long := step.append extL extD more
  obtain ⟨rest, next, fin, exposed, outcome⟩ :=
    ZlibF.Spec.Token.symbols_exposes_step _ _ _ _ _ _ _ symbols
  obtain ⟨restEq, nextEq, finEq⟩ := exposed.det long
  subst restEq nextEq finEq
  rcases outcome with ⟨impossible, _, _⟩ | ⟨_, following⟩
  · cases impossible
  · exact ⟨extL, extD, r, h', by simpa using following, cont⟩

/-- On a valid stream, the output of every reached position is a beginning
of the decoding. -/
theorem deflateParsed_output {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) {more tail : List Bool} {outF : List UInt8}
    (aligned : (bits ++ more).length % 8 = 0) (blocks : Blocks dict [] (bits ++ more) tail outF) :
    pos.out <+: outF := by
  have resid := deflateParsed_resid parsed more tail outF aligned blocks
  cases parsed with
  | @partialToken consumed out final L D pending pbits prev pp =>
    exact Resid.output (fun _ _ _ eq => by cases eq; rfl)
      (deflateParsed_resid prev (pbits ++ more) tail outF (by simpa [List.append_assoc] using aligned)
        (by simpa [List.append_assoc] using blocks))
  | @partialCopy consumed tokenBits out out' final L D dist written prev step _ _ _ _ _ =>
    have before := deflateParsed_resid prev (tokenBits ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks)
    exact (List.take_prefix _ _).trans
      (Resid.output (fun _ _ _ eq => by cases eq; rfl) (before.token step))
  | @partialLiteral consumed tokenBits out final L D byte prev step =>
    exact Resid.output (fun _ _ _ eq => by cases eq; rfl)
      (deflateParsed_resid prev (tokenBits ++ more) tail outF
        (by simpa [List.append_assoc] using aligned) (by simpa [List.append_assoc] using blocks))
  | start => exact Resid.output (by simp) resid
  | storedStart => exact Resid.output (by simp) resid
  | storedPad => exact Resid.output (by simp) resid
  | storedLength => exact Resid.output (by simp) resid
  | storedByte => exact Resid.output (by simp) resid
  | storedEnd => exact Resid.output (by simp) resid
  | storedFinal => exact Resid.output (by simp) resid
  | fixedHeader => exact Resid.output (fun _ _ _ eq => by cases eq; rfl) resid
  | dynamicStart => exact Resid.output (by simp) resid
  | dynamicBits => exact Resid.output (by simp) resid
  | dynamicDone => exact Resid.output (fun _ _ _ eq => by cases eq; rfl) resid
  | token => exact Resid.output (fun _ _ _ eq => by cases eq; rfl) resid
  | endOfBlock => exact Resid.output (by simp) resid
  | endOfFinal => exact Resid.output (by simp) resid

/-- The end of the last block is the end of the specification's blocks. -/
theorem deflateParsed_finished {dict : List UInt8} {bits : List Bool} {out : List UInt8}
    (parsed : DeflateParsed dict bits ⟨out, true, .finished⟩) {more tail : List Bool}
    {outF : List UInt8} (aligned : (bits ++ more).length % 8 = 0)
    (blocks : Blocks dict [] (bits ++ more) tail outF) : more = tail ∧ out = outF :=
  deflateParsed_resid parsed more tail outF aligned blocks

#print axioms deflateParsed_output
#print axioms deflateParsed_finished

/-! ## Conversely, a parse that reaches the end is a specification parse -/

/-- The codes of a Huffman position extend by any bits. -/
theorem deflateParsed_codes_ext {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) :
    ∀ L D p, pos.stage = .codes L D p → Ext L ∧ Ext D := by
  induction parsed with
  | fixedHeader =>
    intro L D p eq
    cases eq
    exact ⟨ext_fixedLit, ext_fixedDist⟩
  | dynamicDone _ dyn =>
    intro L D p eq
    cases eq
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, accL, accD, rfl, rfl⟩ := dyn
    exact ⟨ext_acceptable accL, ext_acceptable accD⟩
  | token _ _ ih => intro L D p eq; cases eq; exact ih _ _ _ rfl
  | partialToken _ _ _ ih => intro L D p eq; cases eq; exact ih _ _ _ rfl
  | partialCopy _ _ _ _ _ _ _ ih => intro L D p eq; cases eq; exact ih _ _ _ rfl
  | partialLiteral _ _ ih => intro L D p eq; cases eq; exact ih _ _ _ rfl
  | _ => intro L D p eq; cases eq

/-- A block header with its body and continuation is a parse of blocks. -/
theorem blocks_of_header {dict out : List UInt8} {b0 b1 b2 : Bool} {more r tail : List Bool}
    {h' outF : List UInt8}
    (body : Body dict ((if b1 then 1 else 0) + 2 * (if b2 then 1 else 0)) out more r h')
    (cont : Cont dict b0 h' r tail outF) : Blocks dict out (b0 :: b1 :: b2 :: more) tail outF := by
  cases b0 with
  | true =>
    obtain ⟨rfl, rfl⟩ : r = tail ∧ h' = outF := by simpa [Cont] using cont
    exact .last (readBits_one true _) (readBits_two b1 b2 _) body
  | false =>
    have rest : Blocks dict h' r tail outF := by simpa [Cont] using cont
    exact .more (readBits_one false _) (readBits_two b1 b2 _) body rest

theorem deflateParsed_sound {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) :
    ∀ more tail outF, (bits ++ more).length % 8 = 0 →
      (∀ L D p, pos.stage = .codes L D p → p = .none) →
      Resid dict pos more tail outF → Blocks dict [] (bits ++ more) tail outF := by
  induction parsed with
  | start =>
    intro more tail outF _ _ resid
    simpa [Resid] using resid
  | @storedStart consumed out final prev ih =>
    intro more tail outF aligned _ resid
    obtain ⟨r, h', body, cont⟩ := resid
    have := ih ([final, false, false] ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simp)
      (blocks_of_header (b1 := false) (b2 := false) (by simpa using body) cont)
    simpa [List.append_assoc] using this
  | @storedPad consumed out final pad prev padLength ih =>
    intro more tail outF aligned _ resid
    obtain ⟨r, h', body, cont⟩ := resid
    have moreAligned : more.length % 8 = 0 := by
      simp only [List.length_append] at aligned
      omega
    have body' : Body dict 0 out (pad ++ more) r h' := by
      cases body with
      | stored one two comp bytes =>
        rw [moreAligned, List.drop_zero] at one
        exact .stored (by rwa [stored_drop_pad (by omega) moreAligned]) two comp bytes
    have := ih (pad ++ more) tail outF (by simpa [List.append_assoc] using aligned) (by simp)
      ⟨r, h', body', cont⟩
    simpa [List.append_assoc] using this
  | @storedLength consumed out final pad len prev padLength small ih =>
    intro more tail outF aligned _ resid
    obtain ⟨bs, r, read, cont⟩ := resid
    have restAligned :
        (natToBitsLSB 16 len ++ (natToBitsLSB 16 (65535 - len) ++ more)).length % 8 = 0 := by
      simp only [List.length_append] at aligned ⊢
      simp only [natToBitsLSB, List.length_map, List.length_range] at aligned ⊢
      omega
    have body : Body dict 0 out (pad ++ (natToBitsLSB 16 len ++ (natToBitsLSB 16 (65535 - len) ++
        more))) r (out ++ bs) :=
      .stored (by rw [stored_drop_pad (by omega) restAligned, readBits_natToBitsLSB (by omega)])
        (readBits_natToBitsLSB (by omega) more) rfl read
    have := ih _ tail outF (by simpa [List.append_assoc] using aligned) (by simp) ⟨r, _, body, cont⟩
    simpa [List.append_assoc] using this
  | @storedByte consumed out final remaining byte prev ih =>
    intro more tail outF aligned _ resid
    obtain ⟨bs, r, read, cont⟩ := resid
    have read' : readBytes (remaining + 1) (byteBits byte ++ more) = some (byte :: bs, r) := by
      have byteEq : byte.toNat.toUInt8 = byte := UInt8.toNat.inj (by simp)
      simp [readBytes, readBits_byteBits, read, byteEq]
    have := ih (byteBits byte ++ more) tail outF (by simpa [List.append_assoc] using aligned)
      (by simp) ⟨_, r, read', by simpa [List.append_assoc] using cont⟩
    simpa [List.append_assoc] using this
  | @storedEnd consumed out prev ih =>
    intro more tail outF aligned _ resid
    exact ih more tail outF aligned (by simp) ⟨[], more, rfl, by simpa [Cont, Resid] using resid⟩
  | @storedFinal consumed out prev ih =>
    intro more tail outF aligned _ resid
    obtain ⟨rfl, rfl⟩ := resid
    exact ih more more out aligned (by simp) ⟨[], more, rfl, by simp [Cont]⟩
  | @fixedHeader consumed out final prev ih =>
    intro more tail outF aligned _ resid
    obtain ⟨_, _, r, h', symbols, cont⟩ := resid
    have := ih ([final, true, false] ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simp)
      (blocks_of_header (b1 := true) (b2 := false) (by simpa using Body.fixed symbols) cont)
    simpa [List.append_assoc] using this
  | @dynamicStart consumed out final prev ih =>
    intro more tail outF aligned _ resid
    obtain ⟨r, h', body, cont⟩ := resid
    have := ih ([final, false, true] ++ more) tail outF
      (by simpa [List.append_assoc] using aligned) (by simp)
      (blocks_of_header (b1 := false) (b2 := true) (by simpa using body) cont)
    simpa [List.append_assoc] using this
  | @dynamicBits consumed header out final moreBits prev ih =>
    intro more tail outF aligned _ resid
    obtain ⟨r, h', body, cont⟩ := resid
    have := ih (moreBits ++ more) tail outF (by simpa [List.append_assoc] using aligned) (by simp)
      ⟨r, h', by simpa [List.append_assoc] using body, cont⟩
    simpa [List.append_assoc] using this
  | @dynamicDone consumed header out final L D prev dyn ih =>
    intro more tail outF aligned _ resid
    obtain ⟨_, _, r, h', symbols, cont⟩ := resid
    obtain ⟨hlit, hdist, hclen, r1, r2, r3, r4, cl, lens, e1, e2, e3, counts, e4, acc, codeLens,
      eob, accL, accD, rfl, rfl⟩ := dyn
    have body : Body dict 2 out (header ++ more) r h' :=
      .dynamic (readBits_append _ _ _ _ more e1) (readBits_append _ _ _ _ more e2)
        (readBits_append _ _ _ _ more e3) counts (readCodeLenLens_append _ _ _ _ more e4) acc
        (by simpa using codeLens.append (ext_acceptable acc) more) eob accL accD symbols
    exact ih more tail outF aligned (by simp) ⟨r, h', body, cont⟩
  | @token consumed tokenBits out out' final L D prev step ih =>
    intro more tail outF aligned _ resid
    obtain ⟨extL, extD, r, h', symbols, cont⟩ := resid
    have long := step.append extL extD more
    have composed := (ZlibF.Spec.Token.step_composes_symbols _ _ _ _ _ _ _ _ long).2 rfl r h'
      (by simpa using symbols)
    have := ih (tokenBits ++ more) tail outF (by simpa [List.append_assoc] using aligned) (by simp)
      ⟨extL, extD, r, h', composed, cont⟩
    simpa [List.append_assoc] using this
  | @endOfBlock consumed tokenBits out L D prev step ih =>
    intro more tail outF aligned _ resid
    obtain ⟨extL, extD⟩ := deflateParsed_codes_ext prev L D .none rfl
    have long := step.append extL extD more
    have ended := ((ZlibF.Spec.Token.step_composes_symbols _ _ _ _ _ _ _ _ long).1 rfl).2
    have := ih (tokenBits ++ more) tail outF (by simpa [List.append_assoc] using aligned) (by simp)
      ⟨extL, extD, more, out, by simpa using ended, by simpa [Cont, Resid] using resid⟩
    simpa [List.append_assoc] using this
  | @endOfFinal consumed tokenBits out L D prev step ih =>
    intro more tail outF aligned _ resid
    obtain ⟨rfl, rfl⟩ := resid
    obtain ⟨extL, extD⟩ := deflateParsed_codes_ext prev L D .none rfl
    have long := step.append extL extD more
    have ended := ((ZlibF.Spec.Token.step_composes_symbols _ _ _ _ _ _ _ _ long).1 rfl).2
    have := ih (tokenBits ++ more) more out (by simpa [List.append_assoc] using aligned) (by simp)
      ⟨extL, extD, more, out, by simpa using ended, by simp [Cont]⟩
    simpa [List.append_assoc] using this
  | @partialToken consumed out final L D pending pbits prev pp ih =>
    intro more tail outF aligned settled resid
    have none := settled L D pending rfl
    subst none
    have empty : pbits = [] := pp
    subst empty
    simpa using ih more tail outF (by simpa using aligned) (by simp) resid
  | partialCopy =>
    intro _ _ _ _ settled _
    exact absurd (settled _ _ _ rfl) (by simp)
  | partialLiteral =>
    intro _ _ _ _ settled _
    exact absurd (settled _ _ _ rfl) (by simp)

/-- A parse that reaches the end of the last block, followed by any bits that
end on a byte boundary, is a specification parse that leaves those bits. -/
theorem deflateParsed_blocks {dict : List UInt8} {bits : List Bool} {out : List UInt8}
    (parsed : DeflateParsed dict bits ⟨out, true, .finished⟩) {more : List Bool}
    (aligned : (bits ++ more).length % 8 = 0) : Blocks dict [] (bits ++ more) more out :=
  deflateParsed_sound parsed more more out aligned (by simp) ⟨rfl, rfl⟩

#print axioms deflateParsed_sound
#print axioms deflateParsed_blocks

end Zlib.Inflate.Proofs
