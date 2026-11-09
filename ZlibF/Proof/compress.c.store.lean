import ZlibF.Proof.«compress.c.output-frame»

/-! # Reconstruct the exact public store from actual interval effects -/
namespace ZlibF.Spec.Public.Proofs.CompressMemory
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressTail
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Exact observed slice plus unchanged bytes on both sides determines
the complete updated array, including an empty slice at one-past end. -/
theorem array_of_interval {before next : Array UInt8} {offset : Nat} {output : List UInt8}
    (bound : offset + output.length ≤ before.size) (size : next.size = before.size)
    (slice : output = (next.toList.drop offset).take output.length)
    (outside : ∀ j, j < before.size → ¬(offset ≤ j ∧ j < offset+output.length) → next[j]? = before[j]?) :
    next = before.extract 0 offset ++ output.toArray ++ before.extract (offset+output.length) before.size := by
  have offsetBound : offset ≤ before.size := by omega
  let replaced := before.extract 0 offset ++ output.toArray ++ before.extract (offset+output.length) before.size
  have replacedSize : replaced.size = before.size := by
    simp only [replaced,Array.size_append,Array.size_extract,List.size_toArray,Nat.min_self,
      Nat.min_eq_left offsetBound,Nat.sub_zero]
    omega
  apply Array.ext_getElem?
  intro j
  by_cases present : j < before.size
  · by_cases first : j < offset
    · have same := outside j present (by omega)
      rw [same]
      simp only [Array.getElem?_append,Array.getElem?_extract,Array.size_append,Array.size_extract,List.size_toArray,
        Nat.min_self,Nat.min_eq_left offsetBound,Nat.sub_zero]
      simp only [if_pos (show j < offset+output.length by omega),if_pos first,Nat.zero_add]
    · by_cases middle : j < offset+output.length
      · have index : j-offset < output.length := by omega
        have indexEq : offset+(j-offset) = j := by omega
        have byte := congrArg (fun xs : List UInt8 => xs[j-offset]?) slice
        simp only [List.getElem?_take,if_pos index,List.getElem?_drop,Array.getElem?_toList,indexEq] at byte
        simp only [Array.getElem?_append,Array.getElem?_extract,Array.size_append,Array.size_extract,List.size_toArray,
          Nat.min_self,Nat.min_eq_left offsetBound,Nat.sub_zero,if_pos middle,if_neg first,
          List.getElem?_toArray]
        exact byte.symm
      · have same := outside j present (by omega)
        rw [same]
        simp only [Array.getElem?_append,Array.getElem?_extract,Array.size_append,Array.size_extract,List.size_toArray,
          Nat.min_self,Nat.min_eq_left offsetBound,Nat.sub_zero,if_neg middle]
        rw [if_pos (show j-(offset+output.length) < before.size-(offset+output.length) by omega)]
        congr 1
        omega
  · have left : next[j]? = none := Array.getElem?_eq_none (by omega)
    have right : replaced[j]? = none := Array.getElem?_eq_none (by omega)
    exact left.trans right.symm

/-- The public Store is reconstructed on the original heap. The actual
final output array equals that exact store; its physical bytes and both
untouched sides are all required, so content outside the result is retained. -/
theorem raw_store_of_interval {h after : Heap} {ob oo : Nat} {output : List UInt8}
    (writable : Writable h (.ref (.blk ob) oo) output.length)
    (physical : Bytes after (.ref (.blk ob) oo) output.length output)
    (effect : RawOutputInterval h after ob oo output.length) :
    ∃ expected, Store h (.ref (.blk ob) oo) output expected ∧ after.bytes ob = expected.bytes ob := by
  rcases writable with ⟨impossible,_⟩ | ⟨ref,off,before,equal,get,_ro,bound⟩
  · cases impossible
  · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj equal
    obtain ⟨next,getNext,size,untouched⟩ := effect before get
    rcases physical with ⟨impossible,_⟩ | ⟨ref,off,a,equal,getA,_bound,slice⟩
    · cases impossible
    · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj equal
      have arrays : a = next := Option.some.inj (getA.symm.trans getNext)
      subst a
      have exactArray := array_of_interval bound size slice untouched
      let expected := Space.put h (BRef.blk ob) (before.extract 0 oo ++ output.toArray ++ before.extract (oo+output.length) before.size)
      refine ⟨expected,Or.inr ⟨.blk ob,oo,before,rfl,get,_ro,bound,rfl⟩,?_⟩
      simpa only [expected,Space.put,upd_same] using getNext.trans (congrArg some exactArray)


/-- The exact Store normalizes the full caller-object frame. After this
normalization every original caller slot, including the output owner's
other typed tables and permission flag, is unchanged. This is a pointwise
frame and does not assert structural equality of dead table capacities. -/
theorem raw_store_with_frame {h after : Heap} {ob oo : Nat} {output : List UInt8}
    (initialUnique : Uniq h) (finalUnique : Uniq after)
    (writable : Writable h (.ref (.blk ob) oo) output.length)
    (physical : Bytes after (.ref (.blk ob) oo) output.length output)
    (effect : RawOutputInterval h after ob oo output.length)
    (frame : Frame h after (fun b => b = ob)) (readonly : after.ro ob = h.ro ob) :
    ∃ expected, Store h (.ref (.blk ob) oo) output expected ∧ Frame expected after (fun _ => False) := by
  rcases writable with ⟨impossible,_⟩ | ⟨ref,off,before,equal,get,ro,bound⟩
  · cases impossible
  · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj equal
    change h.bytes ob = some before at get
    obtain ⟨next,getNext,size,untouched⟩ := effect before get
    rcases physical with ⟨impossible,_⟩ | ⟨ref,off,a,equal,getA,_bound,slice⟩
    · cases impossible
    · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj equal
      have arrays : a = next := Option.some.inj (getA.symm.trans getNext)
      subst a
      let data := before.extract 0 oo ++ output.toArray ++ before.extract (oo+output.length) before.size
      have arrayEq : next = data := array_of_interval bound size slice untouched
      let expected := Space.put h (BRef.blk ob) data
      refine ⟨expected,Or.inr ⟨.blk ob,oo,before,rfl,get,ro,bound,rfl⟩,?_⟩
      refine ⟨frame.1,frame.2.1,frame.2.2.1,frame.2.2.2.1,frame.2.2.2.2.1,?_⟩
      intro b live _outside
      by_cases same : b = ob
      · subst b
        obtain ⟨w,s,g,d,i,z⟩ := initialUnique.bytes_only get
        obtain ⟨wa,sa,ga,da,ia,za⟩ := finalUnique.bytes_only getNext
        simp only [expected,Space.put,SlotSame,upd_same,getNext,arrayEq,w,s,g,d,i,z,
          wa,sa,ga,da,ia,za,readonly,and_self]
      · have oldLive : h.live b := by
          simpa only [expected,Space.put,Heap.live,upd_ne _ _ _ _ same] using live
        have kept := frame.2.2.2.2.2 b oldLive same
        simpa only [expected,Space.put,upd_ne _ _ _ _ same] using kept

/-- The same actual default utility execution has exact scalar length,
physical bytes, API header/format correctness, the precise original Store,
a complete caller frame after that Store, and the original live ledger.
All allocation oracles and legal capacities remain included in the explicit
internal Uniq/nonnull-raw-output/per-object-size domain. -/
theorem default_wrapper_store_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
        .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ output.length ≤ capacity.toNat ∧
      Bytes after dest output.length output ∧ Store h dest output expected ∧
      Frame expected after (fun _ => False) ∧
      (rc = Z_OK → (Api.DeflState.fresh (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)).Valid output xs) ∧
      (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,actual,length,fits,physical,valid,live,dead⟩ :=
    CompressApi.default_wrapper_api_total fresh unique globals objects bytes writable separate pointer
  obtain ⟨frame,effect,uniqueAfter,readonly⟩ := actual_memory fresh unique globals objects bytes writable separate pointer actual
  rw [length] at effect
  have short : Writable h dest output.length := by
    rcases writable with ⟨null,zero⟩ | ⟨ref,off,a,equal,get,ro,bound⟩
    · exact Or.inl ⟨null,by omega⟩
    · exact Or.inr ⟨ref,off,a,equal,get,ro,by omega⟩
  obtain ⟨expected,store,normalized⟩ := raw_store_with_frame unique uniqueAfter
    (by rw [←pointer];exact short) (by rw [←pointer];exact physical) effect frame readonly
  refine ⟨rc,output,after,expected,actual,length,fits,physical,?_,normalized,valid,live,dead⟩
  rw [pointer]
  exact store

end ZlibF.Spec.Public.Proofs.CompressMemory
