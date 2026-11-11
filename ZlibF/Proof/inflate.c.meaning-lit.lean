import ZlibF.Proof.«inflate.c.meaning-write»
import ZlibF.Proof.«inflate.c.literal-step»

/-!
# inflate.c: `LIT` keeps the format meaning

`case LIT` writes the decoded literal held in `length` when there is output
room, and goes to `LEN`; with no room it leaves. The parse position moves
from the pending literal to the boundary after the token.
-/

namespace Zlib.Inflate.Proofs.MeaningLit
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningWrite
set_option autoImplicit false

/-- A pending literal was reached by a complete literal token. -/
theorem parsed_literal_inv {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    {L D : List Nat} {byte : UInt8}
    (parsed : DeflateParsed dict bits ⟨out, final, .codes L D (.literal byte)⟩) :
    ∃ c0 tb, bits = c0 ++ tb ∧ DeflateParsed dict c0 ⟨out, final, .codes L D .none⟩ ∧
      Token.Step L D dict out tb [] (out ++ [byte]) false := by
  cases parsed with
  | partialLiteral prev step => exact ⟨_, _, rfl, prev, step⟩
  | partialToken _ _ pp => exact absurd pp (by simp [PendingParsed])

/-- The modes of a dynamic header position. -/
theorem dynamic_mode {h : Heap} {s : InflateState} {header : List Bool}
    (dyn : DynamicMatches h s header) : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS := by
  rcases dyn with ⟨m, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨m, _⟩ | ⟨m, _⟩⟩
  · exact Or.inl m
  · exact Or.inr (Or.inl m)
  · exact Or.inr (Or.inr m)

/-- The only stage a `LIT` state can stand for. -/
theorem stage_of_lit {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (lit : s.mode = LIT) :
    ∃ header out final L D byte,
      stage = .body header ⟨out, final, .codes L D (.literal byte)⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [lit] at lo hi
    exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rw [lit] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m, _⟩ := body
      rw [lit] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [lit] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [lit] at m
      exact absurd m (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m | m | m <;> (rw [lit] at m; exact absurd m (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rw [lit] at rest; rcases rest.1 with m | m <;> exact absurd m (by decide)
      · rw [lit] at rest; exact absurd rest.1 (by decide)
      · rw [lit] at rest; exact absurd rest.1 (by decide)
      · rw [lit] at rest; exact absurd rest.1 (by decide)
      · rw [lit] at rest; exact absurd rest.1 (by decide)
      · exact ⟨header, out, final, L, D, byte, rfl⟩
    · obtain ⟨m, _⟩ := body
      rw [lit] at m
      exact absurd m (by decide)
  · obtain ⟨m, _⟩ := stageFacts
    rw [lit] at m
    rcases m with m | m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageFacts
    rw [lit] at m
    exact absurd m (by decide)

/-! ## Heap facts of an output write followed by a state update -/

theorem code_get_after {h : Heap} {zs : Nat} {s s' : InflateState} (hs : h.istates zs = some s)
    (codes : s'.codes = s.codes) (dest : BRef) (a : Array UInt8) (cref : CodeRef) :
    (Space.get (setI (Space.put h dest a) zs s') cref : Option (Array Code)) = Space.get h cref := by
  cases cref with
  | istate_codes id =>
      by_cases same : id = zs
      · subst same
        simp [Space.get, setI, byte_view_put_istates, hs, codes]
      · simp [Space.get, setI, upd, Tbl.get_set, same, byte_view_put_istates]
  | st_lenfix => cases dest <;> simp [Space.get, setI, Space.put] <;> split <;> rfl
  | st_distfix => cases dest <;> simp [Space.get, setI, Space.put] <;> split <;> rfl

theorem table_after {h : Heap} {zs : Nat} {s s' : InflateState} (hs : h.istates zs = some s)
    (codes : s'.codes = s.codes) (dest : BRef) (a : Array UInt8)
    {pointer : CodePtr} {root type : UInt32} {lens : List Nat}
    (table : TableMeaning h pointer root type lens) :
    TableMeaning (setI (Space.put h dest a) zs s') pointer root type lens := by
  obtain ⟨ref, offset, codesArr, used, ptr, get, inv, stable⟩ := table
  exact ⟨ref, offset, codesArr, used, ptr, by rw [code_get_after hs codes]; exact get, inv, stable⟩

theorem bytes_setI {h : Heap} {zs : Nat} {s : InflateState} {p : BPtr} {n : Nat} {xs : List UInt8}
    (view : Bytes h p n xs) : Bytes (setI h zs s) p n xs := by
  rcases view with null | ⟨r, i, a, ptr, get, fits, eq⟩
  · exact Or.inl null
  · exact Or.inr ⟨r, i, a, ptr, by rw [byte_view_get_setI]; exact get, fits, eq⟩

theorem bitInv_setI {h : Heap} {zs : Nat} {s : InflateState} {l : IL} {bs : List UInt8}
    (inv : BitInv h l bs) : BitInv (setI h zs s) l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨r, a, off, next, get, fits, view⟩
  · exact Or.inl empty
  · exact Or.inr ⟨r, a, off, next, by rw [byte_view_get_setI]; exact get, fits, view⟩

theorem dictionary_transfer {h h' : Heap} {s s' : InflateState} {xs : List UInt8}
    (window : s'.window = s.window) (wsize : s'.wsize = s.wsize) (wnext : s'.wnext = s.wnext)
    (whave : s'.whave = s.whave)
    (gets : ∀ r : BRef, (Space.get h' r : Option (Array UInt8)) = Space.get h r)
    (dictionary : InflateDictionary h s xs) : InflateDictionary h' s' xs := by
  unfold InflateDictionary at dictionary ⊢
  rw [window, wsize, wnext, whave]
  rcases dictionary with empty | ⟨r, off, a, w, g, f, c⟩
  · exact Or.inl empty
  · exact Or.inr ⟨r, off, a, w, (gets r).trans g, f, c⟩

/-! ## The step -/

theorem body_codes_none {h : Heap} {s : InflateState} {out : List UInt8} {final : Bool}
    {L D : List Nat} (last : s.last = (if final then 1 else 0))
    (lt : TableMeaning h s.lencode s.lenbits LENS L) (dt : TableMeaning h s.distcode s.distbits DISTS D)
    (m : s.mode = LEN) (bits : s.bits.toNat < 8) : BodyMatches h s ⟨out, final, .codes L D .none⟩ :=
  ⟨last, lt, dt, Or.inr m, Or.inl bits⟩

theorem take_after_push (A c : List UInt8) (b : UInt8) (p : Nat) (hp : p ≤ c.length) :
    (A ++ (c ++ [b])).take ((A ++ (c ++ [b])).length - (p + 1)) =
      (A ++ c).take ((A ++ c).length - p) := by
  rw [← List.append_assoc]
  rw [List.take_append_of_le_length (by simp; omega)]
  congr 1
  simp
  omega

set_option maxHeartbeats 1000000 in
/-- `case LIT` keeps the format meaning: with no output room it leaves with
nothing changed; otherwise it writes the pending literal, the output and the
parse position grow by that byte, and no input is read. The safety facts are
the stream record (for `Env`) and the window bounds. -/
theorem lit_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (lit : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LIT)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) :
    ∃ result l' h', runX (inflate_LIT c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ l' = l ∧ h' = h) ∨
       (result = .ok () ∧ loopRead l' = loopRead l ∧ LoopMatches c f h' l')) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe, pendLe,
    putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM, wrapM,
    outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = LIT := lit zs s st hs
  by_cases empty : l.left = 0
  · exact ⟨_, _, _, inflate_LIT_full c l h empty, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rcases writable with ⟨_, zero⟩ | ⟨dest, off, array, put, get, write, room⟩
  · exact absurd (UInt32.toNat_inj.mp (by simpa using zero)) empty
  have leftPos : 1 ≤ l.left.toNat := by
    have nz : l.left.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp (by simpa using zero))
    omega
  have leftSub : (l.left - 1).toNat = l.left.toNat - 1 :=
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using leftPos)
  have run := inflate_LIT_view_run E empty put get write (by omega)
  refine ⟨_, _, _, run, Or.inr ⟨rfl, rfl, ?_⟩⟩
  obtain ⟨header, out, final, L, D, byte, rfl⟩ := stage_of_lit stageM mode
  obtain ⟨body, window, check⟩ := stageM
  obtain ⟨last, lenTable, distTable, pendingFacts⟩ := body
  obtain ⟨_, lengthEq, bitsLt⟩ := pendingFacts
  have byteEq : s.length.toUInt8 = byte := by
    apply UInt8.toNat_inj.mp
    simp only [loopState] at lengthEq
    rw [UInt32.toNat_toUInt8, lengthEq]
    exact Nat.mod_eq_of_lt byte.toNat_lt
  -- the output start is in the written array
  obtain ⟨o0, startEq, offEq⟩ : ∃ o0, f.start = .ref dest o0 ∧ off = o0 + callOut.length := by
    rw [put] at putEq
    cases hst : f.start with
    | null => rw [hst] at putEq; simp [inputAdvance] at putEq
    | ref d o =>
        rw [hst] at putEq
        simp only [inputAdvance, Ptr.ref.injEq] at putEq
        obtain ⟨rfl, rfl⟩ := putEq
        exact ⟨o, rfl, rfl⟩
  rw [startEq] at outBytes sepOutIn
  rw [put] at sepIn sepWin
  let s' : InflateState := { s with mode := LEN }
  let h1 := Space.put h dest (array.set! off s.length.toUInt8)
  have gets : ∀ q : BRef, (Space.get (setI h1 zs s') q : Option (Array UInt8)) = Space.get h1 q :=
    fun q => byte_view_get_setI h1 zs s' q
  obtain ⟨bodyDict, bits, wrapHeader, consumedEq, deflate⟩ := parsed
  obtain ⟨c0, tb, bitsEq0, prev, tokenStep⟩ := parsed_literal_inv deflate
  refine ⟨zs, s', callOut ++ [byte], consumed, held,
    .body header ⟨out ++ [byte], final, .codes L D .none⟩, st, setI_istates_same _ _ _, retOk,
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show LEN ≠ SYNC by decide⟩, haveLe, inLen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, bitsEq, ?_, ?_, ?_, ?_, ?_⟩
  · -- the unread input
    have b2 := bitInv_setI (zs := zs) (s := s')
      (bitInv_after_store s.length.toUInt8 get write (separate_point sepIn leftPos) binv)
    exact ⟨b2.have_eq, b2.next, b2.hold_lt⟩
  · show (l.left - 1).toNat ≤ l.out_.toNat
    rw [leftSub]
    omega
  · show loopPending { l with put := _, left := l.left - 1 } ≤ (callOut ++ [byte]).length
    simp only [loopPending, List.length_append, List.length_singleton, leftSub]
    simp only [loopPending] at pendLe
    omega
  · rw [startEq, offEq]
    simp [inputAdvance, Nat.add_assoc]
  · rw [byteEq.symm, offEq, startEq]
    simp only [List.length_append, List.length_singleton]
    exact bytes_setI (bytes_extend s.length.toUInt8 get write (by omega) outBytes)
  · -- the output room
    refine Or.inr ⟨dest, off + 1, array.set! off s.length.toUInt8, rfl, ?_, ?_, ?_⟩
    · rw [gets]; exact byte_view_get_put get write _
    · rw [byte_view_ro_setI, byte_view_ro_put]; exact write
    · rw [set_size, leftSub]
      omega
  · show Separate (.ref dest (off + 1)) (l.left - 1).toNat l.next l.have_.toNat
    rw [leftSub]
    exact separate_shrink sepIn leftPos
  · show Separate (.ref dest (off + 1)) (l.left - 1).toNat s.window s.wsize.toNat
    rw [leftSub]
    exact separate_shrink sepWin leftPos
  · simp only [List.length_append, List.length_singleton]
    rw [offEq] at sepIn
    rw [startEq]
    exact separate_grow sepOutIn sepIn leftPos
  · exact heldBits
  · refine ⟨bodyDict, bits, wrapHeader, consumedEq, ?_⟩
    rw [bitsEq0]
    exact DeflateParsed.token prev tokenStep
  · -- stage facts
    refine ⟨?_, ?_, ?_⟩
    · have lt' : TableMeaning (setI h1 zs s') s.lencode s.lenbits LENS L :=
        table_after (s' := s') hs rfl dest _ lenTable
      have dt' : TableMeaning (setI h1 zs s') s.distcode s.distbits DISTS D :=
        table_after (s' := s') hs rfl dest _ distTable
      have last' : s.last = (if final then 1 else 0) := last
      have mode' : (loopState s' { l with put := Ptr.ref dest (off + 1), left := l.left - 1 }).mode =
          LEN := rfl
      exact body_codes_none last' lt' dt' mode' bitsLt
    · rcases window with ⟨nonzero, dictionary⟩ | empty
      · have stored := dictionary_after_store s.length.toUInt8 get write (bounds zs s st hs)
          (separate_point sepWin leftPos) (s := loopState s l) dictionary
        have moved : InflateDictionary (setI h1 zs s')
            (loopState s' { l with put := Ptr.ref dest (off + 1), left := l.left - 1 })
            ((f.dict ++ f.logOut).drop ((f.dict ++ f.logOut).length - s.wsize.toNat)) :=
          dictionary_transfer rfl rfl rfl rfl gets stored
        exact Or.inl ⟨nonzero, moved⟩
      · exact Or.inr empty
    · have pend : loopPending { l with put := Ptr.ref dest (off + 1), left := l.left - 1 } =
          loopPending l + 1 := by
        simp only [loopPending, leftSub]
        omega
      rw [pend, take_after_push _ _ _ _ pendLe]
      exact check
  · exact wrapM
  · simp only [WrapStage.output] at outputEq ⊢
    rw [outputEq, List.append_assoc]

end Zlib.Inflate.Proofs.MeaningLit
