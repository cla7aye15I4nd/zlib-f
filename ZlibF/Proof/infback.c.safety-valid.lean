import ZlibF.Proof.«infback.c.safety-frame»

/-!
# infback.c: a valid state survives a call-back

`BackValid` (the stream record, the state record, the window as a writable range, the heap
invariants) holds again after a call of `in` or `out` that keeps the caller protocol: the
call-back changes only its own blocks (`ExternalFrame`), which exclude the stream record and the
state record, and keeps the window slice (`SameBytePrefix`); a block that stays live keeps its
read-only flag.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A frame keeps a stream record whose root is unchanged. -/
theorem ZStreamRef.get_frame {h h' : Heap} {changed : Nat → Prop} (frame : Frame h h' changed)
    {r : ZStreamRef} {z : ZStream} (get : r.get h = some z) (outside : ∀ b, StreamRoot r b → ¬ changed b) :
    r.get h' = some z := by
  obtain ⟨_, _, _, _, _, slots⟩ := frame
  cases r with
  | tab j =>
    change h.streams j = some z at get
    have live : h.live j := Or.inr (Or.inr (Or.inl (by rw [get]; simp)))
    obtain ⟨-, -, streams, -⟩ := slots j live (outside j rfl)
    change h'.streams j = some z
    rw [streams, get]
  | in_gzstate_strm j =>
    change (h.gzstates j).map (·.strm) = some z at get
    cases present : h.gzstates j with
    | none => rw [present] at get; cases get
    | some g =>
      have live : h.live j :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [present]; simp))))))
      obtain ⟨-, -, -, -, -, -, gzstates, -⟩ := slots j live (outside j rfl)
      change (h'.gzstates j).map (·.strm) = some z
      rw [gzstates, present]
      rw [present] at get
      exact get

/-- A frame keeps a state record outside the changed blocks. -/
theorem istates_frame {h h' : Heap} {changed : Nat → Prop} (frame : Frame h h' changed) {i : Nat}
    {s : InflateState} (get : h.istates i = some s) (outside : ¬ changed i) : h'.istates i = some s := by
  obtain ⟨_, _, _, _, _, slots⟩ := frame
  have live : h.live i := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [get]; simp))))))
  obtain ⟨-, -, -, -, -, istates, -⟩ := slots i live outside
  rw [istates, get]

/-- **A valid state survives a call-back of the protocol.** -/
theorem backValid_callback {h h' : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    {own : Nat → Prop} (valid : BackValid h r i z s) (frame : ExternalFrame own h h')
    (stateOut : ¬ own i) (rootOut : ∀ b, StreamRoot r b → ¬ own b)
    (window : SameBytePrefix h h' s.window s.window s.wsize.toNat) : BackValid h' r i z s := by
  obtain ⟨hz, hs, zst, za, zf, wf, lo, hi, ws, nn, wr, -, -, globals⟩ := valid
  obtain ⟨fr, fresh', uniq', -, ro⟩ := frame
  refine ⟨ZStreamRef.get_frame fr hz rootOut, istates_frame fr hs stateOut, zst, za, zf, wf, lo, hi, ws, nn, ?_,
    fresh', uniq', ?_⟩
  · obtain ⟨xs, -, after⟩ := window
    rcases after with ⟨null, -, -⟩ | ⟨ref, off, a, ptr, get, room, -⟩
    · exact absurd null nn
    · rcases wr with ⟨null, -⟩ | ⟨ref0, off0, a0, ptr0, get0, ro0, -⟩
      · exact absurd null nn
      · rw [ptr] at ptr0
        injection ptr0 with e1 e2
        subst e1 e2
        refine Or.inr ⟨ref, off, a, ptr, get, ?_, room⟩
        cases ref with
        | blk b =>
          change h'.ro b = false
          change h.ro b = false at ro0
          have liveB : h.live b := Or.inl (by change h.bytes b = some a0 at get0; rw [get0]; simp)
          have liveB' : h'.live b := Or.inl (by change h'.bytes b = some a at get; rw [get]; simp)
          rw [ro b liveB liveB']
          exact ro0
        | _ => exact ro0
  · unfold LibraryGlobals at globals ⊢
    rw [← fr.1]
    exact globals

/-- A frame over a smaller changed set is a frame over a larger one. -/
theorem Frame.mono {h h' : Heap} {small large : Nat → Prop} (frame : Frame h h' small)
    (sub : ∀ b, small b → large b) : Frame h h' large := by
  obtain ⟨st, al, ga, ne, co, slots⟩ := frame
  exact ⟨st, al, ga, ne, co, fun b live outside => slots b live (fun inside => outside (sub b inside))⟩

/-- **A call-back step is a frame of the call**: it changes only its own blocks, and when the
window is outside them, it changes nothing of the window's block. -/
theorem callbackFrame_of_external {h h' : Heap} {own : Nat → Prop} {r : ZStreamRef} {i : Nat} {window : BPtr}
    {n : Nat} (frame : ExternalFrame own h h') (writable : Writable h window n) :
    CallbackFrame own h h' r i window n := by
  classical
  have fr := frame.1
  refine ⟨Frame.mono fr (fun b o => Or.inr (Or.inr (Or.inl o))), fun disjoint => ?_⟩
  obtain ⟨st, al, ga, ne, co, slots⟩ := fr
  obtain ⟨statics, allocs, garbages, nexts, counts, words, streams, gzheaders, istates, gzstates, ro⟩ :=
    restoreRegions_other h h' [⟨window, n⟩]
  refine ⟨⟨st.trans statics.symm, al.trans allocs.symm, ga.trans garbages.symm, by rw [nexts]; exact ne,
    by rw [counts]; exact co, ?_⟩, ?_⟩
  · intro x live outside
    have notOwn : ¬ own x := fun o => outside (Or.inr (Or.inr o))
    obtain ⟨bx, wx, sx, gx, dx, ix, zx, rx⟩ := slots x live notOwn
    refine ⟨?_, by rw [words, wx], by rw [streams, sx], by rw [gzheaders, gx], ?_, by rw [istates, ix],
      by rw [gzstates, zx], by rw [ro, rx]⟩
    · rw [restoreRegions_bytes]; split
      · rfl
      · exact bx
    · rw [restoreRegions_dstates]; split
      · rw [dx]; cases h.dstates x with
        | none => rfl
        | some d => rfl
      · exact dx
  · intro region member ref off a pointer get
    simp only [List.mem_singleton] at member
    subst member
    refine ⟨a, ?_, rfl, fun _ _ _ => rfl⟩
    cases ref with
    | blk b =>
      have notOwn : ¬ own b := disjoint b (by have p : window = .ref (.blk b) off := pointer; rw [p]; rfl)
      change h.bytes b = some a at get
      have live : h.live b := Or.inl (by rw [get]; simp)
      obtain ⟨bx, -⟩ := slots b live notOwn
      change h'.bytes b = some a
      rw [bx, get]
    | dstate_depth b =>
      have notOwn : ¬ own b := disjoint b (by have p : window = .ref (.dstate_depth b) off := pointer; rw [p]; rfl)
      change (h.dstates b).map (·.depth) = some a at get
      cases present : h.dstates b with
      | none => rw [present] at get; cases get
      | some d =>
        have live : h.live b := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [present]; simp)))))
        obtain ⟨-, -, -, -, dx, -⟩ := slots b live notOwn
        change (h'.dstates b).map (·.depth) = some a
        rw [dx, ← get]
    | _ =>
      exfalso
      rcases writable with ⟨null, -⟩ | ⟨ref0, off0, a0, ptr0, -, ro0, -⟩
      · rw [null] at pointer; cases pointer
      · rw [ptr0] at pointer
        injection pointer with e _
        subst e
        cases ro0

end Zlib.Infback.Safety
