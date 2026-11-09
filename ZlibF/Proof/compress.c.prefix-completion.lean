import ZlibF.Proof.«compress.c.return-modes»
import ZlibF.Math.DeflateFixedBlock
import ZlibF.Math.DeflateZlibEncoding
import ZlibF.Math.InflatePrefixes

/-! # Independent completion of actual nonfinal compressor prefixes -/
namespace ZlibF.Spec.Public.Proofs.CompressCompletion
open C ZlibF.Spec
open Zlib.Trees Zlib.Trees.Proofs Zlib.Trees.Proofs.Out
open ZlibF.Math.DeflateEncoding ZlibF.Math.DeflateSymbols
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false
set_option maxRecDepth 100000

def byteFromBits (a b c d e f g h : Bool) : UInt8 := UInt8.ofNat
  ((if a then 1 else 0)+(if b then 2 else 0)+(if c then 4 else 0)+(if d then 8 else 0)+
   (if e then 16 else 0)+(if f then 32 else 0)+(if g then 64 else 0)+(if h then 128 else 0))

private theorem byte_from_bits (a b c d e f g h : Bool) :
    byteBits (byteFromBits a b c d e f g h) = [a,b,c,d,e,f,g,h] := by
  cases a <;>cases b <;>cases c <;>cases d <;>cases e <;>cases f <;>cases g <;>cases h <;>decide +kernel

def packBits : List Bool → List UInt8
  | a::b::c::d::e::f::g::h::rest => byteFromBits a b c d e f g h :: packBits rest
  | _ => []


/-- Byte-aligned finite bit sequences have an exact byte representation. -/
theorem pack_bits_wire (bits : List Bool) (aligned : bits.length % 8 = 0) :
    bytesToBits (packBits bits) = bits := by
  induction bits using packBits.induct with
  | case1 a b c d e f g h rest ih =>
    have tailAligned : rest.length % 8 = 0 := by
      simp only [List.length_cons] at aligned
      omega
    simp only [packBits,bytesToBits,List.flatMap_cons,byte_from_bits]
    change [a,b,c,d,e,f,g,h] ++ bytesToBits (packBits rest) = a::b::c::d::e::f::g::h::rest
    rw [ih tailAligned]
    rfl
  | case2 t noEight =>
    have short : t.length < 8 := by
      cases t with
      | nil => simp
      | cons a r1 =>
        cases r1 with
        | nil => simp
        | cons b r2 =>
          cases r2 with
          | nil => simp
          | cons c r3 =>
            cases r3 with
            | nil => simp
            | cons d r4 =>
              cases r4 with
              | nil => simp
              | cons e r5 =>
                cases r5 with
                | nil => simp
                | cons f r6 =>
                  cases r6 with
                  | nil => simp
                  | cons g r7 =>
                    cases r7 with
                    | nil => simp
                    | cons h r8 =>
                      exact False.elim (noEight a b c d e f g h r8 rfl)
    have empty : t = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    subst t
    rfl

/-- Literal-only fixed payloads complete arbitrary finite byte strings;
no engine block-size limit is imposed on the independent format. -/
def literalPayload (bytes : List UInt8) : List Bool :=
  bytes.flatMap (fun b => codeBits fixedLiteralWords b.toNat) ++ codeBits fixedLiteralWords 256

theorem literal_payload_grammar (history bytes : List UInt8) (suffix : List Bool) :
    Body [] 1 history (literalPayload bytes ++ suffix) suffix (history ++ bytes) := by
  apply Body.fixed
  induction bytes generalizing history with
  | nil => simpa only [literalPayload,List.flatMap_nil,List.nil_append,List.append_nil] using
      (Symbols.eob (h := history) (fixed_literal_decode 256 (by decide) suffix))
  | cons byte rest ih =>
    have next := ih (history ++ [byte])
    have parse := Symbols.lit
      (fixed_literal_decode byte.toNat (by have bound := byte.toNat_lt;omega)
        (literalPayload rest ++ suffix)) byte.toNat_lt (by simpa only [UInt8.ofNat_toNat] using next)
    simpa only [literalPayload,List.flatMap_cons,List.append_assoc,List.singleton_append] using parse

/-- A nonfinal parser prefix can be completed to any finite byte string
extending its already decoded history. The final literal block is a format
witness; it need not be the compressor's next block choice. -/
theorem nonfinal_prefix_completion {history target published : List UInt8} {encoded : List Bool}
    (meaning : BlockPrefix [] 0 [] encoded history)
    (wirePrefix : bytesToBits published <+: encoded) (content : history <+: target) :
    ∃ raw, Deflate.Valid target raw ∧ published <+: raw := by
  obtain ⟨rest,rfl⟩ := content
  let body := literalPayload rest
  let unpadded := encoded ++ fixedTag true ++ body
  let padding := List.replicate ((8-unpadded.length%8)%8) false
  have padBound : padding.length < 8 := by simp only [padding,List.length_replicate];exact Nat.mod_lt _ (by decide)
  have aligned : (unpadded ++ padding).length % 8 = 0 := by
    simp only [List.length_append,padding,List.length_replicate]
    omega
  let raw := packBits (unpadded ++ padding)
  have packed : bytesToBits raw = encoded ++ natBits 1 1 ++ natBits 1 2 ++ body ++ padding := by
    rw [show bytesToBits raw = unpadded ++ padding from pack_bits_wire _ aligned]
    simp only [unpadded,fixedTag_wire,if_true,List.append_assoc]
  have grammar : Body [] 1 history (body ++ padding) padding (history ++ rest) := literal_payload_grammar history rest padding
  have valid := block_prefix_terminal_valid meaning (by decide : 1 < 4) padBound packed grammar
  have encodedPrefix : encoded <+: bytesToBits raw := by
    rw [packed]
    exact ⟨natBits 1 1 ++ natBits 1 2 ++ body ++ padding,by simp only [List.append_assoc]⟩
  have publishedPrefix := ZlibF.Spec.Api.Proofs.bytesToBits_prefix_reflect (wirePrefix.trans encodedPrefix)
  exact ⟨raw,valid,publishedPrefix⟩

private theorem api_valid_header {input payload : List UInt8}
    (valid : Zlib.Valid input ([120,156] ++ payload)) :
    (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid ([120,156] ++ payload) input := by
  change Zlib.Decodes [] ([120,156] ++ payload) input ∧
    ([120,156] ++ payload).head?.map (fun (b : UInt8) => b.toNat/16+8) = some 15 ∧
    ∃(cmf flg : UInt8) (rest : List UInt8), [120,156] ++ payload = cmf::flg::rest ∧ (flg.toNat/32%2=1 ↔ ([] : List UInt8) ≠ [])
  exact ⟨valid,rfl,120,156,payload,rfl,by decide⟩

private theorem literal_zlib_completion (input : List UInt8) :
    ∃ payload, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid ([120,156] ++ payload) input := by
  obtain ⟨raw,valid,_prefix⟩ := nonfinal_prefix_completion
    (block_prefix_empty ([] : List UInt8) [] 0) (published := []) ⟨[],rfl⟩ ⟨input,rfl⟩
  exact ⟨raw ++ be32 (adler32 input).toNat,api_valid_header (by simpa only [List.append_assoc,List.nil_append] using raw_valid_zlib_grammar valid)⟩

private theorem input_prefix_prefix (input : Nat → UInt8) {base limit : Nat} (bound : base ≤ limit) :
    inputPrefix input base <+: inputPrefix input limit := by
  have take : (inputPrefix input limit).take base = inputPrefix input base := by
    simp only [inputPrefix]
    rw [←List.map_take,List.take_range,Nat.min_eq_left bound]
  exact ⟨(inputPrefix input limit).drop base,by rw [←take,List.take_append_drop]⟩

/-- The actual encoding state can extend its emitted bytes to the complete
original source. Working phases append an independent final literal block,
so even an unoffered source suffix larger than UInt32 is included. Finishing
phases require the explicit fact that the entire target was accepted. -/
theorem encoding_target_completion {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {accepted observed target : List UInt8}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (content : accepted <+: target) (finished : d.status = FINISH_STATE → accepted = target) :
    ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete target ∧ observed <+: complete := by
  rcases state.phase with ⟨_input,output,_rest⟩ | ⟨_input,output,_rest⟩ |
    ⟨input,origin,base,xs,published,output,boundary,_busy,raw,inputEq⟩ |
    ⟨published,output,phase,encoding⟩
  · obtain ⟨payload,valid⟩ := literal_zlib_completion target
    exact ⟨[120,156]++payload,valid,⟨[120,156]++payload,by rw [output];rfl⟩⟩
  · obtain ⟨payload,valid⟩ := literal_zlib_completion target
    exact ⟨[120,156]++payload,valid,⟨156::payload,by rw [output];rfl⟩⟩
  · have bound : base ≤ origin+fillEnd d := by
      have counted := boundary.accounted
      dsimp only [fillEnd]
      omega
    have decodedPrefix := input_prefix_prefix input bound
    rw [inputEq] at decodedPrefix
    have fullContent := decodedPrefix.trans content
    obtain ⟨remaining,encoded,_pending,wire,meaning⟩ := raw
    obtain ⟨rawBytes,valid,publishedPrefix⟩ := nonfinal_prefix_completion meaning ⟨remaining,wire⟩ fullContent
    let trailer := be32 (adler32 target).toNat
    have wrapped : (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid
        ([120,156]++(rawBytes++trailer)) target :=
      api_valid_header (by simpa only [List.append_assoc] using raw_valid_zlib_grammar valid)
    obtain ⟨tail,equal⟩ := publishedPrefix
    refine ⟨[120,156]++(rawBytes++trailer),wrapped,tail++trailer,?_⟩
    rw [output]
    simpa only [List.append_assoc] using congrArg (fun bytes => [120,156]++(bytes++trailer)) equal
  · have all := finished phase.status
    subst target
    obtain ⟨tail,_physical,meaning⟩ := encoding.data
    rcases meaning with ⟨_wrap,rawValid⟩ | ⟨_wrap,zlibValid⟩
    · let trailer := be32 (adler32 accepted).toNat
      have wrapped : (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid
          ([120,156]++((published++tail)++trailer)) accepted :=
        api_valid_header (by simpa only [List.append_assoc] using raw_valid_zlib_grammar rawValid)
      refine ⟨[120,156]++((published++tail)++trailer),wrapped,tail++trailer,?_⟩
      rw [output]
      simp only [List.append_assoc]
    · have wrapped := api_valid_header (by simpa only [List.append_assoc] using zlibValid)
      refine ⟨[120,156]++(published++tail),wrapped,tail,?_⟩
      rw [output]
      simp only [List.append_assoc]

/-- An actual wrapper prefix still in INIT/BUSY has a format-correct
completion for the entire original source, including every unoffered byte.
The concrete not-finishing case is explicit; finishing is separate. -/
theorem actual_working_prefix_completion {slot ob oo k : Nat} {start after : Heap} {last : ZlibF.Spec.Public.Proofs.CompressLoop.Locals}
    {first current : ZStream} {d : DeflateState} {ds : Nat} {capacity n : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {}) (get : start.streams slot = some first)
    (ranges : ZlibF.Spec.Public.Proofs.CompressCaller.Ranges start (.tab slot) first capacity n source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (execution : ZlibF.Spec.Public.Proofs.CompressPrefix.ActualPrefix slot start (Z_OK,capacity,n) k after last)
    (getAfter : after.streams slot = some current) (kind : current.state = some (.deflate ds)) (stateGet : after.dstates ds = some d)
    (working : d.status ≠ FINISH_STATE) :
    ∃ used log, ZlibF.Spec.Public.Proofs.CompressPrefix.PrefixAccount slot first capacity n source k after last used log current ∧
      ∃ complete, (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid complete source ∧ log.output <+: complete := by
  obtain ⟨used,log,z,sound⟩ := ZlibF.Spec.Public.Proofs.CompressPrefix.actual_prefix_sound history get ranges pointer execution
  have sameZ : z = current := Option.some.inj (sound.get.symm.trans getAfter)
  subst z
  obtain ⟨actualDs,encodingZ,actualD,config,encoding,_valid⟩ := sound.history.encoding
  have sameEncodingZ : encodingZ = current := Option.some.inj (encoding.protocol.good.live.hz.symm.trans getAfter)
  subst encodingZ
  have sameDs : actualDs = ds := StateRef.deflate.inj (Option.some.inj (encoding.protocol.good.live.zst.symm.trans kind))
  subst actualDs
  have sameD : actualD = d := Option.some.inj (encoding.protocol.good.live.hs.symm.trans stateGet)
  subst actualD
  have content : log.input <+: source := by
    rw [sound.input]
    exact ⟨source.drop used,List.take_append_drop _ _⟩
  exact ⟨used,log,sound,encoding_target_completion encoding content (fun status => False.elim (working status))⟩

end ZlibF.Spec.Public.Proofs.CompressCompletion
