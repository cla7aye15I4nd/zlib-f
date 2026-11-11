import ZlibF.Proof.«inflate.c.completes-room-frame»

/-!
# inflate.c: a leave for want of output room holds output (modes)

Every mode of the decoder loop leaves through `inf_leave` only for a
`RoomCause`. The three room stops are `case LIT` and `case MATCH`, entered with
the decoder record in their mode (from the dispatch, or `DISTEXT` after it sets
`MATCH`), and `case COPY` with bytes left (from the dispatch, or `COPY_`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.KeepProofs
set_option autoImplicit false

theorem roomX_inflate_DONE (c : Ctx) : RoomX c.flush c.st (inflate_DONE c) := by
  intro l
  unfold inflate_DONE
  repeat' first
    | room_step

theorem roomX_inflate_LENGTH (c : Ctx) : RoomX c.flush c.st (inflate_LENGTH c) := by
  intro l
  unfold inflate_LENGTH
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_inflate_DONE _ _
    | room_step

/-- `case LIT`: entered with the decoder record in `LIT`. -/
theorem roomP_inflate_LIT (c : Ctx) (l : IL) : RoomP c.flush c.st (Holding c.st) l (inflate_LIT c) := by
  unfold inflate_LIT
  room_source

/-- `case MATCH`: entered with the decoder record in `MATCH`. -/
theorem roomP_inflate_MATCH (c : Ctx) (l : IL) :
    RoomP c.flush c.st (Holding c.st) l (inflate_MATCH c) := by
  unfold inflate_MATCH
  repeat' first
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | room_step

/-- `setMode` leaves the decoder record in the mode it sets. -/
theorem setMode_holds {q : InflateStatePtr} {m : UInt32} {h h1 : Heap} {u : Unit}
    (run : setMode q m h = .ok (u, h1)) :
    ∃ i s, q = some (.tab i) ∧ h1.istates i = some s ∧ s.mode = m := by
  unfold setMode at run
  cases q with
  | none => simp [wrS, ldInflateState, bind_app] at run
  | some r =>
    cases r with
    | tab i =>
      cases g : h.istates i with
      | none =>
        have e : ldInflateState (some (.tab i)) h =
            .error (.ub "access through a dangling pointer (inflate_state)") := by
          simp [ldInflateState, InflateStateRef.get, g]
        simp [wrS, bind_app, e] at run
      | some s =>
        have eq := wrS_eq g run
        subst eq
        exact ⟨i, { s with mode := m }, rfl, by simp [upd_apply], rfl⟩

/-- `DISTEXT` falls through to `MATCH` after setting the mode. -/
theorem roomP_setMode_MATCH (c : Ctx) (pre : Heap → Prop) (l : IL) :
    RoomP c.flush c.st pre l ((monadLift (setMode c.st MATCH) : X Unit) >>= fun _ => inflate_MATCH c) := by
  apply roomP_bind (roomP_lift _)
  intro h value middle heap _ run
  rw [runX_lift] at run
  cases source : setMode c.st MATCH h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value1, heap1⟩ := pair
    obtain ⟨i, s, st, get, mode⟩ := setMode_holds source
    simp only [source] at run
    cases run
    exact fun result regs after run =>
      roomP_inflate_MATCH c l _ result regs after ⟨i, s, st, get, Or.inr (Or.inl mode)⟩ run

theorem roomX_inflate_DISTEXT (c : Ctx) : RoomX c.flush c.st (inflate_DISTEXT c) := by
  intro l
  unfold inflate_DISTEXT
  repeat' first
    | with_reducible exact roomX_PULLBYTE _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomP_setMode_MATCH _ _ _
    | room_step

theorem roomX_inflate_DIST (c : Ctx) : RoomX c.flush c.st (inflate_DIST c) := by
  intro l
  unfold inflate_DIST
  repeat' first
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_lookup1 _ _ _ _ _
    | with_reducible exact roomX_lookup2 _ _ _ _ _
    | with_reducible exact roomX_inflate_DISTEXT _ _
    | room_step

theorem roomX_inflate_LENEXT (c : Ctx) : RoomX c.flush c.st (inflate_LENEXT c) := by
  intro l
  unfold inflate_LENEXT
  repeat' first
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_inflate_DIST _ _
    | room_step

theorem roomX_inflate_LEN (c : Ctx) : RoomX c.flush c.st (inflate_LEN c) := by
  intro l
  unfold inflate_LEN
  repeat' first
    | with_reducible exact roomX_LOAD _ _ _ _ _
    | with_reducible exact roomX_RESTORE _ _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_lookup1 _ _ _ _ _
    | with_reducible exact roomX_lookup2 _ _ _ _ _
    | with_reducible exact roomX_inflate_LENEXT _ _
    | room_step

theorem roomX_inflate_LEN_ (c : Ctx) : RoomX c.flush c.st (inflate_LEN_ c) := by
  intro l
  unfold inflate_LEN_
  repeat' first
    | with_reducible exact roomX_inflate_LEN _ _
    | room_step

theorem roomX_inflate_CODELENS (c : Ctx) : RoomX c.flush c.st (inflate_CODELENS c) := by
  intro l
  unfold inflate_CODELENS
  repeat' first
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_lookup1 _ _ _ _ _
    | with_reducible exact roomX_inflate_LEN_ _ _
    | room_step

theorem roomX_inflate_LENLENS (c : Ctx) : RoomX c.flush c.st (inflate_LENLENS c) := by
  intro l
  unfold inflate_LENLENS
  repeat' first
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_inflate_CODELENS _ _
    | room_step

theorem roomX_inflate_TABLE (c : Ctx) : RoomX c.flush c.st (inflate_TABLE c) := by
  intro l
  unfold inflate_TABLE
  repeat' first
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_inflate_LENLENS _ _
    | room_step

/-- The decoder record is in `COPY`. -/
def CopyEntry (q : InflateStatePtr) (h : Heap) : Prop :=
  ∃ i s, q = some (.tab i) ∧ h.istates i = some s ∧ s.mode = COPY

/-- `case COPY`: no room while the stored block has bytes left. -/
theorem roomCause_left_copy {flush : Int32} {q : InflateStatePtr} {l : IL} {s : InflateState}
    (test : (l.left == 0) = true) (more : (s.length != 0) = true) :
    ∀ h, (CopyEntry q h ∧ ldInflateState q h = .ok (s, h)) → RoomCause flush q l h := by
  intro h ⟨⟨i, s0, st, get, mode⟩, load⟩
  subst st
  have g' : (InflateStateRef.tab i).get h = some s0 := get
  rw [ldInflateState_ok g'] at load
  cases load
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by simpa only [beq_iff_eq] using test, i, _, rfl, get,
    Or.inr (Or.inr ⟨mode, ?_⟩)⟩)))
  simpa only [bne_iff_ne, ne_eq] using more

theorem roomP_inflate_COPY (c : Ctx) (l : IL) :
    RoomP c.flush c.st (CopyEntry c.st) l (inflate_COPY c) := by
  unfold inflate_COPY
  refine roomP_ld_bind (fun s => ?_)
  repeat' first
    | with_reducible exact room_imp (roomCause_left_copy ‹_› ‹_›)
    | room_step

/-- `COPY_` falls through to `COPY` after setting the mode. -/
theorem roomP_setMode_COPY (c : Ctx) (pre : Heap → Prop) (l : IL) :
    RoomP c.flush c.st pre l ((monadLift (setMode c.st COPY) : X Unit) >>= fun _ => inflate_COPY c) := by
  apply roomP_bind (roomP_lift _)
  intro h value middle heap _ run
  rw [runX_lift] at run
  cases source : setMode c.st COPY h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value1, heap1⟩ := pair
    have entry := setMode_holds source
    simp only [source] at run
    cases run
    exact fun result regs after run =>
      roomP_inflate_COPY c l _ result regs after entry run

theorem roomX_inflate_COPY_ (c : Ctx) : RoomX c.flush c.st (inflate_COPY_ c) := by
  intro l
  unfold inflate_COPY_
  repeat' first
    | with_reducible exact roomP_setMode_COPY _ _ _
    | room_step

theorem roomX_inflate_STORED (c : Ctx) : RoomX c.flush c.st (inflate_STORED c) := by
  intro l
  unfold inflate_STORED
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BYTEBITS _ _ _
    | with_reducible exact roomX_inflate_COPY_ _ _
    | room_step

theorem roomX_inflate_TYPEDO (c : Ctx) : RoomX c.flush c.st (inflate_TYPEDO c) := by
  intro l
  unfold inflate_TYPEDO
  repeat' first
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_BYTEBITS _ _ _
    | room_step

theorem roomX_inflate_TYPE (c : Ctx) : RoomX c.flush c.st (inflate_TYPE c) := by
  intro l
  unfold inflate_TYPE
  repeat' first
    | with_reducible exact roomX_inflate_TYPEDO _ _
    | room_step

theorem roomX_inflate_DICT (c : Ctx) : RoomX c.flush c.st (inflate_DICT c) := by
  intro l
  unfold inflate_DICT
  repeat' first
    | with_reducible exact roomX_RESTORE _ _ _ _ _
    | with_reducible exact roomX_inflate_TYPE _ _
    | room_step

theorem roomX_inflate_DICTID (c : Ctx) : RoomX c.flush c.st (inflate_DICTID c) := by
  intro l
  unfold inflate_DICTID
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_inflate_DICT _ _
    | room_step

theorem roomX_inflate_HCRC (c : Ctx) : RoomX c.flush c.st (inflate_HCRC c) := by
  intro l
  unfold inflate_HCRC
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | room_step

/-- The gzip string and extra-field modes leave through `inf_leave` only with no
input left: their copy loop stops with `copy == have` whenever the field goes
on (`len != 0`, `length != 0`). Register facts of the loop; open here (batch 2
proves the loop under the header invariant, `gz_strLoop`). -/
abbrev GzipFieldLeaves : Prop :=
  ∀ c : Ctx, RoomX c.flush c.st (inflate_EXTRA c) ∧ RoomX c.flush c.st (inflate_NAME c) ∧
    RoomX c.flush c.st (inflate_COMMENT c)

theorem roomX_inflate_EXLEN (gz : GzipFieldLeaves) (c : Ctx) : RoomX c.flush c.st (inflate_EXLEN c) := by
  intro l
  unfold inflate_EXLEN
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_BYTEBITS _ _ _
    | with_reducible exact roomX_CRC2 _ _ _ _
    | with_reducible exact roomX_CRC4 _ _ _ _
    | with_reducible exact roomX_PULLBYTE _ _ _
    | with_reducible exact roomX_LOAD _ _ _ _ _
    | with_reducible exact roomX_RESTORE _ _ _ _ _
    | with_reducible exact (gz _).1 _
    | room_step

theorem roomX_inflate_OS (gz : GzipFieldLeaves) (c : Ctx) : RoomX c.flush c.st (inflate_OS c) := by
  intro l
  unfold inflate_OS
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_BYTEBITS _ _ _
    | with_reducible exact roomX_CRC2 _ _ _ _
    | with_reducible exact roomX_CRC4 _ _ _ _
    | with_reducible exact roomX_PULLBYTE _ _ _
    | with_reducible exact roomX_LOAD _ _ _ _ _
    | with_reducible exact roomX_RESTORE _ _ _ _ _
    | with_reducible exact roomX_inflate_EXLEN gz _ _
    | room_step

theorem roomX_inflate_TIME (gz : GzipFieldLeaves) (c : Ctx) : RoomX c.flush c.st (inflate_TIME c) := by
  intro l
  unfold inflate_TIME
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_BYTEBITS _ _ _
    | with_reducible exact roomX_CRC2 _ _ _ _
    | with_reducible exact roomX_CRC4 _ _ _ _
    | with_reducible exact roomX_PULLBYTE _ _ _
    | with_reducible exact roomX_LOAD _ _ _ _ _
    | with_reducible exact roomX_RESTORE _ _ _ _ _
    | with_reducible exact roomX_inflate_OS gz _ _
    | room_step

theorem roomX_inflate_FLAGS (gz : GzipFieldLeaves) (c : Ctx) : RoomX c.flush c.st (inflate_FLAGS c) := by
  intro l
  unfold inflate_FLAGS
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_BYTEBITS _ _ _
    | with_reducible exact roomX_CRC2 _ _ _ _
    | with_reducible exact roomX_CRC4 _ _ _ _
    | with_reducible exact roomX_PULLBYTE _ _ _
    | with_reducible exact roomX_LOAD _ _ _ _ _
    | with_reducible exact roomX_RESTORE _ _ _ _ _
    | with_reducible exact roomX_inflate_TIME gz _ _
    | room_step

theorem roomX_inflate_HEAD (gz : GzipFieldLeaves) (c : Ctx) : RoomX c.flush c.st (inflate_HEAD c) := by
  intro l
  unfold inflate_HEAD
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_BITS _ _ _ _
    | with_reducible exact roomX_DROPBITS _ _ _ _
    | with_reducible exact roomX_CRC2 _ _ _ _
    | with_reducible exact roomX_inflate_FLAGS gz _ _
    | room_step

theorem roomX_inflate_CHECK (c : Ctx) : RoomX c.flush c.st (inflate_CHECK c) := by
  intro l
  unfold inflate_CHECK
  repeat' first
    | with_reducible exact roomX_INITBITS _ _ _
    | with_reducible exact roomX_NEEDBITS _ _ _ _
    | with_reducible exact roomX_inflate_LENGTH _ _
    | room_step

/-- The dispatch leaves only for a `RoomCause`: the mode read from the heap
selects `LIT`, `MATCH` or `COPY` with the decoder record in that mode. -/
theorem roomX_inflate_dispatch (gz : GzipFieldLeaves) (c : Ctx) :
    RoomX c.flush c.st (inflate_dispatch c) := by
  intro l
  unfold inflate_dispatch
  apply roomP_bind (roomP_lift _)
  intro h m l1 h1 _ run
  rw [runX_lift] at run
  cases source : rdS c.st (·.mode) h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨m', h2⟩ := pair
    simp only [source] at run
    cases run
    obtain ⟨rfl, i, s, st, get, rfl⟩ := rdS_ok source
    by_cases lit : s.mode = LIT
    · rw [lit]
      simp (config := { decide := true }) only [↓reduceIte]
      exact fun result regs after run =>
        roomP_inflate_LIT c l _ result regs after ⟨i, s, st, get, Or.inl lit⟩ run
    by_cases match_ : s.mode = MATCH
    · rw [match_]
      simp (config := { decide := true }) only [↓reduceIte]
      exact fun result regs after run =>
        roomP_inflate_MATCH c l _ result regs after ⟨i, s, st, get, Or.inr (Or.inl match_)⟩ run
    by_cases copy : s.mode = COPY
    · rw [copy]
      simp (config := { decide := true }) only [↓reduceIte]
      exact fun result regs after run =>
        roomP_inflate_COPY c l _ result regs after ⟨i, s, st, get, copy⟩ run
    have b1 : (s.mode == LIT) = false := by simpa only [beq_eq_false_iff_ne] using lit
    have b2 : (s.mode == MATCH) = false := by simpa only [beq_eq_false_iff_ne] using match_
    have b3 : (s.mode == COPY) = false := by simpa only [beq_eq_false_iff_ne] using copy
    simp only [b1, b2, b3, Bool.false_eq_true, ↓reduceIte]
    refine fun result regs after run =>
      (?_ : RoomP c.flush c.st (fun _ => True) l _) _ result regs after trivial run
    repeat' first
        | with_reducible exact roomX_inflate_HEAD gz _ _
        | with_reducible exact roomX_inflate_HCRC _ _
        | with_reducible exact roomX_inflate_DICTID _ _
        | with_reducible exact roomX_inflate_DICT _ _
        | with_reducible exact roomX_inflate_TYPE _ _
        | with_reducible exact roomX_inflate_TYPEDO _ _
        | with_reducible exact roomX_inflate_STORED _ _
        | with_reducible exact roomX_inflate_COPY_ _ _
        | with_reducible exact roomX_inflate_TABLE _ _
        | with_reducible exact roomX_inflate_LENLENS _ _
        | with_reducible exact roomX_inflate_CODELENS _ _
        | with_reducible exact roomX_inflate_LEN_ _ _
        | with_reducible exact roomX_inflate_LEN _ _
        | with_reducible exact roomX_inflate_LENEXT _ _
        | with_reducible exact roomX_inflate_DIST _ _
        | with_reducible exact roomX_inflate_DISTEXT _ _
        | with_reducible exact roomX_inflate_CHECK _ _
        | with_reducible exact roomX_inflate_LENGTH _ _
        | with_reducible exact roomX_inflate_DONE _ _
        | with_reducible exact roomX_inflate_FLAGS gz _ _
        | with_reducible exact roomX_inflate_TIME gz _ _
        | with_reducible exact roomX_inflate_OS gz _ _
        | with_reducible exact roomX_inflate_EXLEN gz _ _
        | with_reducible exact (gz _).1 _
        | with_reducible exact (gz _).2.1 _
        | with_reducible exact (gz _).2.2 _
        | room_step

/-- The loop of `inflate()` leaves only for a `RoomCause`. -/
theorem roomX_inflate_run (gz : GzipFieldLeaves) (c : Ctx) : RoomX c.flush c.st (inflate_run c) := by
  intro l
  unfold inflate_run
  repeat' first
    | with_reducible exact roomX_LOAD _ _ _ _ _
    | with_reducible exact roomX_inflate_dispatch gz _
    | room_step

#print axioms roomX_inflate_run

end Zlib.Inflate.Proofs
