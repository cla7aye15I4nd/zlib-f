import ZlibF.Math.UncompressStoredCopy
import ZlibF.Proof.«inflate.c.stored-views»
import ZlibF.Proof.«uncompr.c.stored-check-stream»

namespace Zlib.Uncompr.Proof.StoredCopyPayload
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Actual nonempty stored COPY fills the payload destination and leaves
the physical Adler trailer readable at the returned cursor. This starts
at the stored COPY cutpoint, before CHECK, on the same actual heap. -/
theorem copy_payload {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (payload : List UInt8) (small : payload.length < 65536) (nonempty : payload ≠ [])
    (input : BitInv h l (payload ++ be32 (ZlibF.Spec.adler32 payload).toNat))
    (length : s.length = UInt32.ofNat payload.length) (left : l.left = UInt32.ofNat payload.length)
    (put : l.put = .ref (.blk db) 0) (output : Array UInt8) (get : h.bytes db = some output)
    (size : output.size = payload.length) (write : h.ro db = false)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃ regs,
      runX (inflate_COPY c) l h = .ok ((.ok (),regs),
        setI (Space.put h (BRef.blk db) payload.toArray) zs {s with length := 0}) ∧
      BitInv (setI (Space.put h (BRef.blk db) payload.toArray) zs {s with length := 0}) regs
        (be32 (ZlibF.Spec.adler32 payload).toNat) ∧
      regs.next = inputAdvance l.next payload.length ∧
      regs.put = .ref (.blk db) payload.length ∧ regs.left = 0 ∧
      regs.hold = l.hold ∧ regs.bits = l.bits ∧ regs.out_ = l.out_ := by
  let n := UInt32.ofNat payload.length
  have nNat : n.toNat = payload.length := by
    exact UInt32.toNat_ofNat_of_lt' (by change payload.length < 4294967296; omega)
  have nCount : (UInt32.ofNat payload.length).toNat = payload.length := nNat
  have positive : n ≠ 0 := by
    intro zero
    have eq := congrArg UInt32.toNat zero
    change n.toNat = 0 at eq
    rw [nNat] at eq
    exact nonempty (List.length_eq_zero_iff.mp eq)
  have haveCount : l.have_.toNat = payload.length+4 := by
    simpa only [List.length_append,be32,List.length_cons,List.length_nil] using input.have_eq
  have amount : copyAmt s.length l.have_ l.left = n := by
    unfold copyAmt
    rw [length,left]
    change (let c := if n > l.have_ then l.have_ else n; if c > n then n else c) = n
    have bound : ¬ n > l.have_ := by rw [gt_iff_lt,UInt32.lt_iff_toNat_lt,nNat]; omega
    simp only [bound,ite_false]
    split <;> rfl
  have sourceNonempty : payload ++ be32 (ZlibF.Spec.adler32 payload).toNat ≠ [] := by
    intro nil
    have := congrArg List.length nil
    simp [be32] at this
  obtain ⟨source,array,off,next,sourceGet,sourceRoom,content⟩ := input.next.resolve_left sourceNonempty
  have sourceFit : off+payload.length ≤ array.size := by
    simp only [List.length_append,be32,List.length_cons,List.length_nil] at sourceRoom
    omega
  have slice : payload = (array.toList.drop off).take payload.length := by
    have taken :=  congrArg (fun xs => xs.take payload.length) content
    simpa [List.take_take,Nat.min_eq_left (show payload.length ≤ (payload ++ be32 (ZlibF.Spec.adler32 payload).toNat).length by simp)] using taken
  have outputGet : Space.get h (BRef.blk db) = some output := get
  have readonly : Space.ro h (BRef.blk db) = false := write
  have positions := input.output_positions put (by rw [left];exact positive) separate
  have postInput := input.stored_copy (input := array) (io := off) (oo := 0) (n := payload.length)
    outputGet readonly sourceFit (by omega) (by simpa only [left,nCount] using positions)
  have disjoint : (.blk db:BRef) ≠ source ∨ payload.length ≤ off ∨ off+payload.length ≤ 0 := by
    have sep := separate
    rw [next,put,left] at sep
    simp only [nCount] at sep
    rcases sep with noIn | noOut | different | before | later
    · omega
    · exact False.elim (nonempty (List.length_eq_zero_iff.mp noOut))
    · exact Or.inl (Ne.symm different)
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
  have copied := StoredCopyMath.copied_payload output array off payload size sourceFit slice
  let regs := copyRegs l n (.ref source (off+payload.length)) (.ref (.blk db) payload.length)
  have cursor : regs.next = inputAdvance l.next payload.length := by rw [next];rfl
  have inputCount : regs.have_.toNat + payload.length = l.have_.toNat := by
    change (l.have_-n).toNat + payload.length = l.have_.toNat
    rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr;omega),nNat]
    omega
  have advanced := postInput.advance_bytes (regs := regs) (used := payload.length)
    (by simp) cursor inputCount (by rfl) (by rfl)
  have packet := advanced.decode_update zs {s with length := 0}
  rw [copied] at packet
  refine ⟨regs,?_,by simpa using packet,cursor,rfl,?_,rfl,rfl,rfl⟩
  · have run := inflate_COPY_views_run E l (by rw [length];exact positive)
      (by rw [amount];exact positive) next put sourceGet outputGet readonly
      (by simpa only [amount,nNat] using sourceFit) (by simp [amount,nNat,size])
      (by simpa only [amount,nNat,Nat.zero_add] using disjoint)
    dsimp only at run
    rw [amount,nNat,copied] at run
    have sub : s.length-n=0 := by rw [length];exact UInt32.sub_self n
    simpa only [sub,Nat.zero_add,regs] using run
  · change l.left - n = 0
    rw [left]
    exact UInt32.sub_self n

#print axioms copy_payload
end Zlib.Uncompr.Proof.StoredCopyPayload
