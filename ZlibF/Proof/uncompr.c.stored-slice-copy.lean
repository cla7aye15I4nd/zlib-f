import ZlibF.Math.InflateStoredSlice
import ZlibF.Proof.«inflate.c.stored-views»
import ZlibF.Proof.«uncompr.c.stored-slice-check-stream»

namespace Zlib.Uncompr.Proof.StoredSliceCopy
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

def patched (output : Array UInt8) (off : Nat) (payload : List UInt8) : Array UInt8 :=
  output.extract 0 off ++ payload.toArray ++ output.extract (off+payload.length) output.size

/-- Real COPY on a nonempty payload accepts any output capacity at least
its length and any output byte offset. Both untouched sides of the output
object and the physical trailer input are retained exactly. -/
theorem copy_slice {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (payload : List UInt8) (small : payload.length < 65536) (nonempty : payload ≠ [])
    (input : BitInv h l (payload ++ be32 (ZlibF.Spec.adler32 payload).toNat))
    (capacity : UInt32) (enough : payload.length≤capacity.toNat)
    (length : s.length=UInt32.ofNat payload.length) (left : l.left=capacity)
    (oo : Nat) (put : l.put=.ref (.blk db) oo) (output : Array UInt8) (get : h.bytes db=some output)
    (room : oo+capacity.toNat≤output.size) (write : h.ro db=false)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃ regs,
      runX (inflate_COPY c) l h = .ok ((.ok (),regs),
        setI (Space.put h (BRef.blk db) (patched output oo payload)) zs {s with length := 0}) ∧
      BitInv (setI (Space.put h (BRef.blk db) (patched output oo payload)) zs {s with length := 0}) regs
        (be32 (ZlibF.Spec.adler32 payload).toNat) ∧
      regs.next = inputAdvance l.next payload.length ∧
      regs.put = .ref (.blk db) (oo+payload.length) ∧ regs.left = capacity-UInt32.ofNat payload.length ∧
      regs.hold=l.hold ∧ regs.bits=l.bits ∧ regs.out_=l.out_ ∧
      (patched output oo payload).size=output.size ∧
      ((patched output oo payload).toList.drop oo).take payload.length=payload ∧
      (∀i,i<oo ∨ oo+payload.length≤i → (patched output oo payload)[i]?=output[i]?) := by
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
    change (let c := if n > l.have_ then l.have_ else n; if c > capacity then capacity else c) = n
    have bound : ¬ n > l.have_ := by rw [gt_iff_lt,UInt32.lt_iff_toNat_lt,nNat]; omega
    have outputBound : ¬ n>capacity := by rw [gt_iff_lt,UInt32.lt_iff_toNat_lt,nNat];omega
    simp only [bound,outputBound,ite_false]
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
  have positiveCapacity : capacity≠0 := by
    intro zero
    have zeroNat := congrArg UInt32.toNat zero
    change capacity.toNat=0 at zeroNat
    have size0 : payload.length=0 := by omega
    exact nonempty (List.length_eq_zero_iff.mp size0)
  have positions := input.output_positions put (by rw [left];exact positiveCapacity) separate
  have outputFit : oo+payload.length≤output.size := by omega
  have postInput := input.stored_copy (input:=array) (io:=off) (oo:=oo) (n:=payload.length)
    outputGet readonly sourceFit outputFit (by
      rcases positions with empty|positions
      · exact Or.inl empty
      · right
        intro i ptr
        rcases positions i ptr with before|later
        · exact Or.inl before
        · exact Or.inr (by rw [left] at later;omega))
  have disjoint : (BRef.blk db)≠source ∨ oo+payload.length≤off ∨ off+payload.length≤oo := by
    have sep := separate
    rw [next,put,left] at sep
    rcases sep with noIn|noOut|different|before|later
    · omega
    · have zeroNat : capacity.toNat=0 := noOut
      have size0 : payload.length=0 := by omega
      exact False.elim (nonempty (List.length_eq_zero_iff.mp size0))
    · exact Or.inl (Ne.symm different)
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inl (by omega))
  have copied : copyRange output array oo off payload.length=patched output oo payload :=
    StoredSliceMath.copied_array output array oo off payload outputFit sourceFit slice
  have copiedSlice := StoredSliceMath.copied_slice output array oo off payload outputFit sourceFit slice
  have copiedSize : (patched output oo payload).size=output.size := by rw [←copied];exact size_copyRange ..
  have copiedOutside : ∀i,i<oo ∨ oo+payload.length≤i → (patched output oo payload)[i]?=output[i]? := by
    intro i bound
    rw [←copied]
    exact StoredSliceMath.copied_outside output array oo off payload outputFit sourceFit i bound
  let regs := copyRegs l n (.ref source (off+payload.length)) (.ref (.blk db) (oo+payload.length))
  have cursor : regs.next = inputAdvance l.next payload.length := by rw [next];rfl
  have inputCount : regs.have_.toNat + payload.length = l.have_.toNat := by
    change (l.have_-n).toNat + payload.length = l.have_.toNat
    rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr;omega),nNat]
    omega
  have advanced := postInput.advance_bytes (regs := regs) (used := payload.length)
    (by simp) cursor inputCount (by rfl) (by rfl)
  have packet := advanced.decode_update zs {s with length := 0}
  rw [copied] at packet
  refine ⟨regs,?_,by simpa using packet,cursor,rfl,?_,rfl,rfl,rfl,copiedSize,?_,copiedOutside⟩
  · have run := inflate_COPY_views_run E l (by rw [length];exact positive)
      (by rw [amount];exact positive) next put sourceGet outputGet readonly
      (by simpa only [amount,nNat] using sourceFit) (by simpa only [amount,nNat] using outputFit)
      (by simpa only [amount,nNat] using disjoint)
    dsimp only at run
    rw [amount,nNat,copied] at run
    have sub : s.length-n=0 := by rw [length];exact UInt32.sub_self n
    simpa only [sub,regs] using run
  · change l.left-n=capacity-UInt32.ofNat payload.length
    rw [left]
  · simpa only [copied] using copiedSlice

#print axioms copy_slice
end Zlib.Uncompr.Proof.StoredSliceCopy
