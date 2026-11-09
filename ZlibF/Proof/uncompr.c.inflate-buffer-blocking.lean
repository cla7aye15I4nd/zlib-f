import ZlibF.Proof.«uncompr.c.inflate-buffer-cause»
import ZlibF.Proof.«uncompr.c.inflate-basic-blocked»

namespace Zlib.Uncompr.Proof.InflateBufferBlocking
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def Blocked (l : IL) : Prop := l.have_ = 0 ∨ l.left = 0

def BlockedExit (exit : Ex) (l : IL) (_h : Heap) : Prop := exit = .leave → Blocked l

macro "blocked_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact exitPostX_pure _
    | with_reducible exact exitPostX_lift _
    | with_reducible exact exitPostX_get
    | with_reducible exact exitPostX_set _
    | with_reducible exact exitPostX_modify _
    | with_reducible apply exitPostX_ite
    | with_reducible apply exitPostX_xwhile
    | with_reducible apply exitPostX_xwhileBrk
    | with_reducible apply exitPostX_xloopBrk
    | with_reducible apply exitPostX_xdoWhile
    | with_reducible refine exitPostX_bind ?_ (fun _ => ?_))

theorem pullByte_blocked : ExitPostX BlockedExit PULLBYTE := by
  intro l h outcome regs after run exit selected
  simp only [PULLBYTE, runX_bind, runX_get] at run
  by_cases empty : l.have_ = 0
  · simp only [empty, beq_self_eq_true, ite_true] at run
    cases run
    cases selected
    exact fun _ => Or.inl empty
  · have rest : ExitPostX BlockedExit (do
        set { l with have_ := l.have_ - 1 }
        let b ← load8 l.next
        let nx ← l.next.add 1
        let sh ← shl64 b.toUInt64 l.bits
        set { l with have_ := l.have_ - 1, next := nx, hold := l.hold + sh, bits := l.bits + 8 }) := by
      blocked_source
    simp only [beq_iff_eq, empty, ite_false] at run
    exact rest _ _ _ _ _ run _ selected

theorem needBits_blocked (n : UInt32) : ExitPostX BlockedExit (NEEDBITS n) := by
  unfold NEEDBITS
  apply exitPostX_xwhile
  · blocked_source
  · exact pullByte_blocked

theorem leftGuard_blocked {α : Type} (next : IL → X α)
    (rest : ∀ l, ExitPostX BlockedExit (next l)) :
    ExitPostX BlockedExit (do
      let l ← get
      if l.left == 0 then throw Ex.leave
      next l) := by
  intro l h outcome regs after run exit selected
  simp only [runX_bind, runX_get] at run
  by_cases empty : l.left = 0
  · simp only [empty, beq_self_eq_true, ite_true] at run
    cases run
    cases selected
    exact fun _ => Or.inr empty
  · simp only [beq_iff_eq, empty, ite_false] at run
    exact rest l _ _ _ _ _ run _ selected

theorem lit_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_LIT c) := by
  unfold inflate_LIT
  apply leftGuard_blocked
  intro l
  blocked_source

theorem match_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_MATCH c) := by
  unfold inflate_MATCH
  apply leftGuard_blocked
  intro l
  blocked_source

theorem lookup1_blocked (c : Ctx) (dist : Bool) : ExitPostX BlockedExit (lookup1 c dist) := by
  unfold lookup1 BITS
  have pull := pullByte_blocked
  blocked_source

theorem lookup2_blocked (c : Ctx) (dist : Bool) : ExitPostX BlockedExit (lookup2 c dist) := by
  unfold lookup2 BITS
  have pull := pullByte_blocked
  blocked_source

theorem bits_blocked (n : UInt32) : ExitPostX BlockedExit (BITS n) := by
  unfold BITS
  blocked_source

theorem dropBits_blocked (n : UInt32) : ExitPostX BlockedExit (DROPBITS n) := by
  unfold DROPBITS
  blocked_source

theorem distExtra_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_DISTEXT c) := by
  unfold inflate_DISTEXT
  have needs := needBits_blocked
  have bits := bits_blocked
  have drops := dropBits_blocked
  have matching := match_blocked c
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem dist_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_DIST c) := by
  unfold inflate_DIST
  have one := lookup1_blocked c true
  have two := lookup2_blocked c true
  have drops := dropBits_blocked
  have extra := distExtra_blocked c
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem lenExtra_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_LENEXT c) := by
  unfold inflate_LENEXT
  have needs := needBits_blocked
  have bits := bits_blocked
  have drops := dropBits_blocked
  have distance := dist_blocked c
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem len_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_LEN c) := by
  unfold inflate_LEN RESTORE LOAD
  have one := lookup1_blocked c false
  have two := lookup2_blocked c false
  have drops := dropBits_blocked
  have extra := lenExtra_blocked c
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem lenStart_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_LEN_ c) := by
  unfold inflate_LEN_
  have length := len_blocked c
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem codes_blocked (c : Ctx) (flush : c.flush = Z_NO_FLUSH) :
    ExitPostX BlockedExit (inflate_CODELENS c) := by
  unfold inflate_CODELENS
  simp only [flush, show (Z_NO_FLUSH == Z_TREES) = false from rfl, Bool.false_eq_true, ite_false]
  have one := lookup1_blocked c false
  have length := lenStart_blocked c
  have needs := needBits_blocked
  have bits := bits_blocked
  have drops := dropBits_blocked
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem lenlens_blocked (c : Ctx) (flush : c.flush = Z_NO_FLUSH) :
    ExitPostX BlockedExit (inflate_LENLENS c) := by
  unfold inflate_LENLENS
  have codes := codes_blocked c flush
  have needs := needBits_blocked
  have bits := bits_blocked
  have drops := dropBits_blocked
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem table_blocked (c : Ctx) (flush : c.flush = Z_NO_FLUSH) :
    ExitPostX BlockedExit (inflate_TABLE c) := by
  unfold inflate_TABLE
  have lengths := lenlens_blocked c flush
  have needs := needBits_blocked
  have bits := bits_blocked
  have drops := dropBits_blocked
  blocked_source
  all_goals first | exact needs _ | exact bits _ | exact drops _

theorem copy_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_COPY c) := by
  intro l h outcome regs after run exit selected
  rw [inflate_COPY, runX_bind] at run
  cases load : ldInflateState c.st h with
  | error fault =>
    rw [runX_lift, load] at run
    cases run
  | ok pair =>
    obtain ⟨s, heap⟩ := pair
    rw [runX_lift_ok load] at run
    by_cases empty : s.length = 0
    · simp only [empty, bne_self_eq_false, Bool.false_eq_true, ite_false] at run
      have rest : ExitPostX BlockedExit (do
          modify fun l => { l with copy := (0 : UInt32) }
          setMode c.st TYPE) := by blocked_source
      exact rest _ _ _ _ _ run _ selected
    · simp only [bne_iff_ne, ite_eq_left empty, runX_bind, runX_get] at run
      have normal (n : UInt32) : ExitPostX BlockedExit (do
          memcpyB l.put l.next n.toNat
          let nx ← l.next.add (n.toNat : Int)
          let pt ← l.put.add (n.toNat : Int)
          set { l with copy := n, have_ := l.have_ - n, next := nx, left := l.left - n, put := pt }
          wrS c.st fun s => { s with length := s.length - n }
          pure ()) := by blocked_source
      by_cases first : s.length > l.have_
      · simp only [first, ite_true] at run
        by_cases second : l.have_ > l.left
        · simp only [second, ite_true] at run
          by_cases zero : l.left = 0
          · simp only [zero, beq_self_eq_true, ite_true, runX_bind, runX_set] at run
            cases run
            cases selected
            exact fun _ => Or.inr rfl
          · simp only [beq_iff_eq, zero, ite_false] at run
            exact normal l.left _ _ _ _ _ run _ selected
        · simp only [second, ite_false] at run
          by_cases zero : l.have_ = 0
          · simp only [zero, beq_self_eq_true, ite_true, runX_bind, runX_set] at run
            cases run
            cases selected
            exact fun _ => Or.inl rfl
          · simp only [beq_iff_eq, zero, ite_false] at run
            exact normal l.have_ _ _ _ _ _ run _ selected
      · simp only [first, ite_false] at run
        by_cases second : s.length > l.left
        · simp only [second, ite_true] at run
          by_cases zero : l.left = 0
          · simp only [zero, beq_self_eq_true, ite_true, runX_bind, runX_set] at run
            cases run
            cases selected
            exact fun _ => Or.inr rfl
          · simp only [beq_iff_eq, zero, ite_false] at run
            exact normal l.left _ _ _ _ _ run _ selected
        · simp only [second, ite_false, beq_iff_eq, empty, ite_false] at run
          exact normal s.length _ _ _ _ _ run _ selected

theorem copyStart_blocked (c : Ctx) : ExitPostX BlockedExit (inflate_COPY_ c) := by
  unfold inflate_COPY_
  have copied := copy_blocked c
  blocked_source

theorem stored_blocked (c : Ctx) (flush : c.flush = Z_NO_FLUSH) :
    ExitPostX BlockedExit (inflate_STORED c) := by
  unfold inflate_STORED BYTEBITS INITBITS
  simp only [flush, show (Z_NO_FLUSH == Z_TREES) = false from rfl, Bool.false_eq_true, ite_false]
  have copied := copyStart_blocked c
  have needs := needBits_blocked
  blocked_source
  all_goals exact needs _

/-- The actual stored, table-construction and data branches can leave under
NO_FLUSH only after input or output is exhausted. These are source observers,
not assumed callee contracts, and they admit every successful actual run. -/
theorem complex_dispatch_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL}
    (E : Env c h r zs z s) (flush : c.flush = Z_NO_FLUSH)
    (mode : (s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) ∨
      (s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) ∨ DataTableMode s.mode)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after)) : Blocked regs := by
  rcases mode with stored | construction | data
  · rcases stored with mode | mode | mode
    · exact stored_blocked c flush _ _ _ _ _ ((inflate_dispatch_STORED E l mode).symm.trans run) _ rfl rfl
    · exact copyStart_blocked c _ _ _ _ _ ((inflate_dispatch_COPY_start E l mode).symm.trans run) _ rfl rfl
    · exact copy_blocked c _ _ _ _ _ ((inflate_dispatch_COPY E l mode).symm.trans run) _ rfl rfl
  · rcases construction with mode | mode | mode
    · exact table_blocked c flush _ _ _ _ _ ((inflate_dispatch_TABLE E l mode).symm.trans run) _ rfl rfl
    · exact lenlens_blocked c flush _ _ _ _ _ ((inflate_dispatch_LENLENS E l mode).symm.trans run) _ rfl rfl
    · exact codes_blocked c flush _ _ _ _ _ ((inflate_dispatch_CODELENS E l mode).symm.trans run) _ rfl rfl
  · rcases data with mode | mode | mode | mode | mode | mode | mode
    · exact lenStart_blocked c _ _ _ _ _ ((inflate_dispatch_LEN_start E l mode).symm.trans run) _ rfl rfl
    · exact len_blocked c _ _ _ _ _ ((inflate_dispatch_LEN E l mode).symm.trans run) _ rfl rfl
    · exact lenExtra_blocked c _ _ _ _ _ ((inflate_dispatch_LENEXT E l mode).symm.trans run) _ rfl rfl
    · exact dist_blocked c _ _ _ _ _ ((inflate_dispatch_DIST E l mode).symm.trans run) _ rfl rfl
    · exact distExtra_blocked c _ _ _ _ _ ((inflate_dispatch_DISTEXT E l mode).symm.trans run) _ rfl rfl
    · exact match_blocked c _ _ _ _ _ ((inflate_dispatch_MATCH E l mode).symm.trans run) _ rfl rfl
    · exact lit_blocked c _ _ _ _ _ ((inflate_dispatch_LIT E l mode).symm.trans run) _ rfl rfl

/-- All default mode groups have the same actual ordinary-OK wait cause. -/
theorem dispatch_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) (get : after.istates zs = some returned) : Blocked regs := by
  rcases defaultMode_cases invariant.modes with head | dictionary | type | stored | construction | data | trailer | terminal
  · exact Or.inl (Zlib.Uncompr.Proof.InflateBasicBlocked.basic_dispatch_leave_blocked
      E invariant buffers flush (Or.inl head) run ret get)
  · rcases dictionary with mode | mode
    · exact Or.inl (Zlib.Uncompr.Proof.InflateBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inl mode)) run ret get)
    · exact Or.inl (Zlib.Uncompr.Proof.InflateBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inl mode))) run ret get)
  · rcases type with mode | mode
    · exact Or.inl (Zlib.Uncompr.Proof.InflateBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inr (Or.inl mode)))) run ret get)
    · exact Or.inl (Zlib.Uncompr.Proof.InflateBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl mode))))) run ret get)
  · exact complex_dispatch_leave_blocked E flush (Or.inl stored) run
  · exact complex_dispatch_leave_blocked E flush (Or.inr (Or.inl construction)) run
  · exact complex_dispatch_leave_blocked E flush (Or.inr (Or.inr data)) run
  · rcases trailer with check | length
    · exact Or.inl (Zlib.Uncompr.Proof.InflateBasicBlocked.basic_dispatch_leave_blocked
        E invariant buffers flush (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr check))))) run ret get)
    · obtain ⟨source, _⟩ := inflate_LENGTH_default_state_boundary E invariant buffers length
      have actual := (inflate_dispatch_LENGTH E l length).trans source
      have fixed := xrun_regs_eq actual run
      have ended : regs.ret = Z_STREAM_END := by rw [←fixed]
      rw [ret] at ended
      contradiction
  · have actual := inflate_dispatch_terminal_run E l terminal
    have outcome := xrun_outcome_eq actual run
    have fixed := xrun_regs_eq actual run
    rcases terminal with done | bad | mem | sync
    · have ended : regs.ret = Z_STREAM_END := by rw [←fixed]; simp [terminalRegs, done]
      rw [ret] at ended; contradiction
    · have failed : regs.ret = Z_DATA_ERROR := by rw [←fixed]; simp [terminalRegs, bad, show BAD ≠ DONE from by decide]
      rw [ret] at failed; contradiction
    · simp [terminalExit, mem, show MEM ≠ DONE from by decide, show MEM ≠ BAD from by decide] at outcome
    · simp [terminalExit, sync, show SYNC ≠ DONE from by decide, show SYNC ≠ BAD from by decide,
        show SYNC ≠ MEM from by decide] at outcome

private def BlockingInv (r : ZStreamRef) (zs : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h r zs z s ∧ DispatchBuffers h r l bs ∧ l.bits.toNat ≤ 39

/-- The actual complete mode loop carries the last executed dispatch's
blocking cause to its ordinary OK leave. -/
theorem inflate_run_leave_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {regs : IL}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, regs), after))
    (ret : regs.ret = Z_OK) : Blocked regs := by
  obtain ⟨entryHeap, entryState, bs, cut, current, _, packet, bits, _, _, _⟩ :=
    inflate_run_default_view_entry E invariant buffers nonnull inputValid
  have start : BlockingInv r zs (dispatchRegs z entryState) entryHeap :=
    ⟨z, entryState, bs, current, packet, bits⟩
  have step : ∀ before heap outcome finalRegs finalHeap, BlockingInv r zs before heap →
      runX (inflate_dispatch c) before heap = .ok ((outcome, finalRegs), finalHeap) →
      match outcome with
      | .ok () => BlockingInv r zs finalRegs finalHeap
      | .error exit => exit = Ex.leave → finalRegs.ret = Z_OK → Blocked finalRegs := by
    intro before heap outcome finalRegs finalHeap valid actual
    obtain ⟨stream, state, remaining, j, packet, incoming⟩ := valid
    have env : Env c heap r zs stream state := ⟨E.strm, E.st, j.good.live.hz, j.good.live.hs⟩
    obtain ⟨_, _, _, nextZ, nextS, used, _, _, source, final, nextBuffers,
      _, _, _, _, _, nextBits, _⟩ := inflate_dispatch_default_view_state_rank env j packet incoming
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    cases outcome with
    | ok value => cases value; exact ⟨nextZ, nextS, remaining.drop used, final, nextBuffers, nextBits⟩
    | error exit =>
      intro selected ok
      subst exit
      exact dispatch_leave_blocked env j packet flush actual ok final.good.live.hs
  rw [cut] at run
  exact xwhile_success_control_post _ _ step start run rfl ret

private theorem buffer_ret_ok {c : Ctx} {l : IL} (ret : PublicLeaveRet l)
    (selected : Z_BUF_ERROR = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) : l.ret = Z_OK := by
  by_cases condition : ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
      l.ret == Z_OK) = true
  · have selectedOK : (l.ret == Z_OK) = true := (Bool.and_eq_true_iff.mp condition).2
    exact beq_iff_eq.mp selectedOK
  · rw [ite_eq_right condition] at selected
    rcases ret with ok | ended | bad
    · exact ok
    · rw [ended] at selected; contradiction
    · rw [bad] at selected; contradiction

/-- The same actual complete body returning BUF has an exhausted final
caller cursor. Both direct-return exclusions and real leave bookkeeping
are proved from execution, including allocation failure. -/
theorem inflate_body_buffer_blocked
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (flush : c.flush = Z_NO_FLUSH)
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_BUF_ERROR, after))
    (good : Good after r zs stream state) : stream.avail_in = 0 ∨ stream.avail_out = 0 := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, _, _, _, run, current,
    packet, bits, _, _, _, _, _, _, loopAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  rw [bind_app, run] at body
  cases exit with
  | ret code =>
    change (Except.ok (code, loopHeap) : Except Fault (Int32 × Heap)) = .ok (Z_BUF_ERROR, after) at body
    have selected : code = Z_BUF_ERROR := congrArg Prod.fst (Except.ok.inj body)
    have codes := inflate_run_direct_codes run
    rw [selected] at codes
    exact False.elim (by rcases codes with codes | codes | codes <;> revert codes <;> decide)
  | leave =>
    change inflate_leave c regs loopHeap = .ok (Z_BUF_ERROR, after) at body
    have env : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, heap1, returned, privateState, actual, final, _, _, inAvail, _, outAvail, outcome⟩ :=
      inflate_leave_default_public_accounting env current loopAllocator packet bits
    have same := Except.ok.inj (actual.symm.trans body)
    have selected : rc = Z_BUF_ERROR := congrArg Prod.fst same
    have heaps : heap1 = after := congrArg Prod.snd same
    subst heap1
    have streams : returned = stream := Option.some.inj (final.good.live.hz.symm.trans good.live.hz)
    subst returned
    rcases outcome with ordinary | memory
    · have ret := inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run
      rw [selected] at ordinary
      have retOK := buffer_ret_ok (c := c) ret ordinary.1
      have blocked := inflate_run_leave_blocked E invariant buffers nonnull inputValid flush run retOK
      rcases blocked with input | output
      · exact Or.inl (inAvail.trans input)
      · exact Or.inr (outAvail.trans output)
    · exact False.elim ((by decide : Z_BUF_ERROR ≠ Z_MEM_ERROR) (selected.symm.trans memory.1))

/-- The public call's real temporary cleanup does not change its returned
stream cursors. An actual NO_FLUSH BUF therefore exposes an exhausted one. -/
theorem inflate_public_buffer_final_blocked
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (Z_BUF_ERROR, after))
    (good : Good after r zs stream state) : stream.avail_in = 0 ∨ stream.avail_out = 0 := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, Z_NO_FLUSH⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true
  · unfold C.run inflate at run
    rw [bind_app, allocLocalB_run h invariant.good.fresh] at run
    simp only [] at run
    rw [bind_app] at run
    simp only [bind_app, stateCheck_live allocated.good.live,
      bne_self_eq_false, Bool.false_eq_true, ite_false,
      ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app] at run
    dsimp only [syncBuf] at run
    rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)] at run
    have impossible := congrArg Prod.fst (Except.ok.inj run)
    exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_BUF_ERROR) impossible)
  · have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by intro null; exact rejected (by simp [null])
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    have localBuffers := streamBuffers_syncAlloc invariant.good.fresh buffers
    obtain ⟨rc, heap1, bodyStream, bodyState, bytes, bodyRun, current, _, get, size, ro⟩ :=
      inflate_default_view_local_state_return env allocated allocator localBuffers nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have actual : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (rc, freeWin heap1 (syncBuf h)) := by
      unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
      rw [bind_app] at bodyRun
      unfold runX at bodyRun
      dsimp only [c] at bodyRun
      erw [bodyRun]
      simp only []
      change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
      rw [bind_app]
      dsimp only [syncBuf]
      rw [freeBuf_run get ro]
      rfl
    have same := Except.ok.inj (actual.symm.trans run)
    have code : rc = Z_BUF_ERROR := congrArg Prod.fst same
    have heapEq : freeWin heap1 (syncBuf h) = after := congrArg Prod.snd same
    rw [code] at bodyRun
    have final := current.free_local get size
    have finalGet : r.get (freeWin heap1 (syncBuf h)) = some stream := by rw [heapEq]; exact good.live.hz
    have sameStream : bodyStream = stream := Option.some.inj (final.good.live.hz.symm.trans finalGet)
    rw [←sameStream]
    exact inflate_body_buffer_blocked env allocated allocator localBuffers nonnull inputValid rfl bodyRun current.good

/-- `int inflate(z_streamp strm, int flush)`.
On the same actual default NO_FLUSH BUF run, zero whole-call progress and
actual blocking imply that the original offered input or output was empty.
No callee contract or new public precondition is assumed. -/
theorem inflate_public_buffer_blocked
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream}
    {s state : InflateState} {used made : Nat}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) Z_NO_FLUSH) h = .ok (Z_BUF_ERROR, after))
    (good : Good after r zs stream state) (accounting : StreamAccounting z stream used made) :
    z.avail_in = 0 ∨ z.avail_out = 0 := by
  obtain ⟨usedZero, madeZero⟩ := Zlib.Uncompr.Proof.InflateBufferCause.inflate_public_buffer_zero
    invariant allocator buffers run good accounting
  have inputCount := accounting.2.2.1
  have outputCount := accounting.2.2.2.1
  rw [usedZero] at inputCount
  rw [madeZero] at outputCount
  rcases inflate_public_buffer_final_blocked invariant allocator buffers run good with input | output
  · left
    rw [input] at inputCount
    exact UInt32.toNat_inj.mp (by omega)
  · right
    rw [output] at outputCount
    exact UInt32.toNat_inj.mp (by omega)

#print axioms complex_dispatch_leave_blocked
#print axioms inflate_run_leave_blocked
#print axioms inflate_public_buffer_blocked
end Zlib.Uncompr.Proof.InflateBufferBlocking
