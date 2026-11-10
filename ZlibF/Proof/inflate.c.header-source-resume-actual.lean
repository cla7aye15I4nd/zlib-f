import ZlibF.Proof.«inflate.c.header-code-source-credit»
import ZlibF.Proof.«inflate.c.leave-causal-frame»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Interpret an actual public result with the closed leave theorem.
Every parser scalar frame is derived from translated code, including
window success/failure, rather than selected as a desired after-fact. -/
theorem observed_leave_parser_fields
    {c : Ctx} {h publicHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {l : IL} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (actual : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
    (get : publicHeap.istates zs = some state) :
    rc = Z_MEM_ERROR ∨
    (state.ncode = s.ncode ∧ state.nlen = s.nlen ∧ state.ndist = s.ndist ∧
      state.lens = s.lens ∧ state.«have» = s.«have» ∧ state.codes = s.codes ∧ state.lenbits = s.lenbits ∧
      state.hold = l.hold ∧ state.bits = l.bits) := by
  by_cases memory : rc = Z_MEM_ERROR
  · exact Or.inl memory
  · have frame := inflate_leave_causal_frame_of_run E origin.toDefaultStateJ allocator buffers bits actual memory get
    apply Or.inr
    rw [frame]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Full actual CODELENS leave/caller/load continuation. No public parser
scalar or desired source-prefix postcondition is a caller premise. -/
theorem CodeSourceTrace.resume_actual
    {c : Ctx} {h publicHeap callerHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {z callerZ : ZStream} {s : InflateState} {l : IL} {bs input : List UInt8}
    {alphabet : List Nat} {rc : Int32} {log : DataLog} {word : List Bool}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (leave : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
    (source : CausalInput.AtPublic publicHeap r log word) (owner : source.zs = zs)
    (edit : Rebuffer publicHeap callerHeap r) (streamGet : r.get callerHeap = some callerZ)
    (inputBytes : Bytes callerHeap callerZ.next_in callerZ.avail_in.toNat input) :
    rc = Z_MEM_ERROR ∨
    (∃ next : CausalInput.AtPublic callerHeap r log word,
      next.zs = zs ∧ next.state = source.state ∧ next.z = callerZ ∧
      ∃ regs, runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) ∧
        CodeSourceTrace r zs callerHeap callerZ source.state regs input alphabet) := by
  have get : publicHeap.istates zs = some source.state := by rw [← owner]; exact source.good.live.hs
  rcases observed_leave_parser_fields E origin allocator buffers bits leave get with memory | fields
  · exact Or.inl memory
  apply Or.inr
  obtain ⟨_code, lit, dist, lens, haveEq, codes, rootBits, _hold, _bits⟩ := fields
  have values : actualLengthPrefix source.state = actualLengthPrefix s := by
    simp only [actualLengthPrefix, lens, haveEq]
  exact trace.resume_credited E.strm E.st leave source owner lit dist values codes rootBits haveEq edit streamGet inputBytes

/-- Full actual LENLENS leave/caller/load continuation, with the cumulative
count/alphabet word and exact credited source preserved automatically. -/
theorem CountReadSource.resume_actual
    {c : Ctx} {h publicHeap callerHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs input : List UInt8} {received : List Bool}
    {callerZ : ZStream} {rc : Int32} {log : DataLog} {committed : List Bool}
    (data : CountReadSource s received bs) (progress : LenlensProgress s l.hold l.bits received)
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (leave : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
    (source : CausalInput.AtPublic publicHeap r log committed) (owner : source.zs = zs)
    (edit : Rebuffer publicHeap callerHeap r) (streamGet : r.get callerHeap = some callerZ)
    (inputBytes : Bytes callerHeap callerZ.next_in callerZ.avail_in.toNat input) :
    rc = Z_MEM_ERROR ∨
    (∃ next : CausalInput.AtPublic callerHeap r log committed,
      next.zs = zs ∧ next.state = source.state ∧ next.z = callerZ ∧
      ∃ regs, runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) ∧
        LenlensProgress source.state regs.hold regs.bits received ∧
        ∃ word, data.body = word ++ received ++ bytesBits bs ∧
          ∃ nextCount : CountReadSource source.state received input,
            nextCount.body = word ++ received ++ bytesBits input) := by
  have get : publicHeap.istates zs = some source.state := by rw [← owner]; exact source.good.live.hs
  rcases observed_leave_parser_fields E origin allocator buffers bits leave get with memory | fields
  · exact Or.inl memory
  apply Or.inr
  obtain ⟨code, lit, dist, lens, haveEq, _codes, _rootBits, hold, savedBits⟩ := fields
  exact data.resume_credited progress E.strm E.st leave source owner lit dist code lens haveEq hold savedBits edit streamGet inputBytes

/-- Build the public credited-input observation from the actual leave,
rather than requesting the desired public source relation as an input. -/
theorem publish_credited_source
    {c : Ctx} {h publicHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {rc : Int32} {log : DataLog} {word : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (credit : CausalInput.Credited log.input word l.bits l.hold)
    (actual : C.run (inflate_leave c l) h = .ok (rc, publicHeap)) :
    rc = Z_MEM_ERROR ∨ ∃ source : CausalInput.AtPublic publicHeap r log word, source.zs = zs := by
  by_cases memory : rc = Z_MEM_ERROR
  · exact Or.inl memory
  obtain ⟨rc0, heap0, stream0, state0, run0, current, _allocator⟩ :=
    inflate_leave_default_state E origin.toDefaultStateJ allocator buffers bits
  have sameRun := Except.ok.inj (run0.symm.trans actual)
  cases sameRun
  have frame := inflate_leave_causal_frame_of_run E origin.toDefaultStateJ allocator buffers bits actual memory current.good.live.hs
  have publicCredit : CausalInput.Credited log.input word state0.bits state0.hold := by
    rw [frame]
    exact credit
  exact Or.inr ⟨⟨zs, stream0, state0, current.good, publicCredit⟩, rfl⟩

/-- Execute the complete parser-source handoff from an actual private
credit equation through real leave, caller edit and LOAD. No desired
public source or parser scalar postcondition is a premise. -/
theorem CodeSourceTrace.resume_from_credit
    {c : Ctx} {h publicHeap callerHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {z callerZ : ZStream} {s : InflateState} {l : IL} {bs input : List UInt8}
    {alphabet : List Nat} {rc : Int32} {log : DataLog} {word : List Bool}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (credit : CausalInput.Credited log.input word l.bits l.hold)
    (leave : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
    (edit : Rebuffer publicHeap callerHeap r) (streamGet : r.get callerHeap = some callerZ)
    (inputBytes : Bytes callerHeap callerZ.next_in callerZ.avail_in.toNat input) :
    rc = Z_MEM_ERROR ∨
      ∃ next : CausalInput.AtPublic callerHeap r log word, next.zs = zs ∧ next.z = callerZ ∧
        ∃ regs, runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) ∧
          CodeSourceTrace r zs callerHeap callerZ next.state regs input alphabet := by
  rcases publish_credited_source E origin allocator buffers bits credit leave with memory | source
  · exact Or.inl memory
  obtain ⟨source, owner⟩ := source
  rcases trace.resume_actual E origin allocator buffers bits leave source owner edit streamGet inputBytes with memory | resumed
  · exact Or.inl memory
  obtain ⟨next, nextOwner, sameState, nextZ, regs, loaded, nextTrace⟩ := resumed
  refine Or.inr ⟨next, nextOwner, nextZ, regs, loaded, ?_⟩
  rw [sameState]
  exact nextTrace

/-- The same actual publication/rebuffer handoff for partial alphabet
reads. Public credit and parser-field preservation are derived jointly. -/
theorem CountReadSource.resume_from_credit
    {c : Ctx} {h publicHeap callerHeap : Heap} {r : ZStreamRef} {zs : Nat}
    {z callerZ : ZStream} {s : InflateState} {l : IL} {bs input : List UInt8}
    {received : List Bool} {rc : Int32} {log : DataLog} {word : List Bool}
    (data : CountReadSource s received bs) (progress : LenlensProgress s l.hold l.bits received)
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (credit : CausalInput.Credited log.input word l.bits l.hold)
    (leave : C.run (inflate_leave c l) h = .ok (rc, publicHeap))
    (edit : Rebuffer publicHeap callerHeap r) (streamGet : r.get callerHeap = some callerZ)
    (inputBytes : Bytes callerHeap callerZ.next_in callerZ.avail_in.toNat input) :
    rc = Z_MEM_ERROR ∨
      ∃ next : CausalInput.AtPublic callerHeap r log word, next.zs = zs ∧ next.z = callerZ ∧
        ∃ regs, runX (LOAD c.strm c.st) IL.init callerHeap = .ok ((.ok (), regs), callerHeap) ∧
          LenlensProgress next.state regs.hold regs.bits received ∧
          ∃ countWord, data.body = countWord ++ received ++ bytesBits bs ∧
            ∃ nextCount : CountReadSource next.state received input,
              nextCount.body = countWord ++ received ++ bytesBits input := by
  rcases publish_credited_source E origin allocator buffers bits credit leave with memory | source
  · exact Or.inl memory
  obtain ⟨source, owner⟩ := source
  rcases data.resume_actual progress E origin allocator buffers bits leave source owner edit streamGet inputBytes with memory | resumed
  · exact Or.inl memory
  obtain ⟨next, nextOwner, sameState, nextZ, regs, loaded, nextProgress, countWord, oldBody, nextCount, nextBody⟩ := resumed
  refine Or.inr ⟨next, nextOwner, nextZ, regs, loaded, ?_⟩
  rw [sameState]
  exact ⟨nextProgress, countWord, oldBody, nextCount, nextBody⟩

#print axioms observed_leave_parser_fields
#print axioms CodeSourceTrace.resume_actual
#print axioms CountReadSource.resume_actual
#print axioms publish_credited_source
#print axioms CodeSourceTrace.resume_from_credit
#print axioms CountReadSource.resume_from_credit
end Zlib.Inflate.Proofs.ActualHeader
