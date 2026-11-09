import ZlibF.Proof.«compress.c.large-prefix-bound»

/-! # The unchanged utility capacity contract on the default raw-output domain

Small complete offers and large cumulative histories are joined here.
The actual default initialization, original input object, real wrapper loop
and original cleanup all refer to the same execution. The full public
Fresh-only/generic-output goal remains separate from this internal scope.
-/
namespace ZlibF.Spec.Public.Proofs.CompressCapacity
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open ZlibF.Spec.Public.Proofs.CompressCaller ZlibF.Spec.Public.Proofs.CompressTail
open ZlibF.Spec.Public.Proofs.CompressMemory ZlibF.Spec.Public.Proofs.CompressModes
open ZlibF.Spec.Public.Proofs.CompressBuffer ZlibF.Spec.Public.Proofs.CompressSmall
open ZlibF.Spec.Public.Proofs.CompressLarge
set_option autoImplicit false

/-- Adequate compressBound capacity makes every actual successful default
initialization complete the whole original source. Both source-size branches
use proved real engine executions, including exact terminal exhaustion. -/
theorem sufficient_default_capacity {h initialized : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (room : Api.compressBound xs.length ≤ capacity.toNat)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK,initialized)) :
    ∃ output after,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h =
        .ok ((Z_OK,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ Bytes after dest output.length output ∧
      output.length ≤ Api.compressBound xs.length := by
  by_cases small : xs.length < 2^25
  · exact sufficient_small_capacity fresh unique globals bytes writable separate pointer small room actualInit
  · have large : 33554432 ≤ xs.length := by change ¬xs.length < 33554432 at small;omega
    obtain ⟨output,after,run,word,physical,budget⟩ :=
      sufficient_large_capacity fresh unique globals objects bytes writable separate pointer large room actualInit
    exact ⟨output,after,run,word,physical,Nat.le_of_lt budget⟩

/-- All original source lengths admitted by the explicit byte-object scope
satisfy the unchanged full Compress2Z API relation on this internal default
Uniq/non-null raw-output domain. This includes both capacity clauses, all
allocator outcomes, exact physical length, Store, normalized caller Frame
and restored live-object ledger. No callee contract is an input premise. -/
theorem default_wrapper_capacity_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ Bytes after dest output.length output ∧
      Store h dest output expected ∧ Frame expected after (fun _ => False) ∧
      Api.Compress2Z
        {source := xs,capacity := capacity.toNat,level := Z_DEFAULT_COMPRESSION.toInt,
          sourceNull := source == .null,destNull := dest == .null,lengthNull := false}
        {rc := rc.toInt,produced := output,storedLength := (some (UInt64.ofNat output.length)).map UInt64.toNat} ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) ∧ (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,expected,actual,word,fits,physical,store,frame,allowed,memory,valid,buffer,live,dead⟩ :=
    default_wrapper_buffer_total fresh unique globals objects bytes writable separate pointer
  have nonnull : dest ≠ .null := by rw [pointer];intro bad;cases bad
  have capacityClauses : output.length ≤ Api.compressBound xs.length ∧
      (rc = Z_BUF_ERROR → capacity.toNat < Api.compressBound xs.length) := by
    by_cases below : capacity.toNat < Api.compressBound xs.length
    · exact ⟨by omega,fun _ => below⟩
    · have room : Api.compressBound xs.length ≤ capacity.toNat := by omega
      obtain ⟨f,u,g,v,old,get,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
      obtain ⟨initRc,initialized,actualInit,initAllowed⟩ := default_initialization_total f u g get alloc v
      rcases initAllowed with okay | mem
      · subst initRc
        obtain ⟨completed,final,completedRun,completedWord,_completedBytes,budget⟩ :=
          sufficient_default_capacity fresh unique globals objects bytes writable separate pointer room actualInit
        have events := Prod.mk.inj (Except.ok.inj (completedRun.symm.trans actual))
        have code := congrArg Prod.fst events.1
        have scalar := Option.some.inj (congrArg Prod.snd events.1)
        have lengths := congrArg UInt64.toNat scalar
        rw [completedWord,word] at lengths
        exact ⟨by omega,fun buf => False.elim ((by decide : Z_OK ≠ Z_BUF_ERROR) (code.trans buf))⟩
      · subst initRc
        obtain ⟨code,_scalar,_failed⟩ := memory_return_effects fresh unique globals bytes nonnull actualInit actual
        have empty := (memory code).1
        rw [empty,List.length_nil]
        exact ⟨Nat.zero_le _,fun buf => False.elim ((by decide : Z_MEM_ERROR ≠ Z_BUF_ERROR) (code.symm.trans buf))⟩
  have api := small_api_relation bytes nonnull word fits capacityClauses.1 allowed memory valid buffer capacityClauses.2
  exact ⟨rc,output,after,expected,actual,word,physical,store,frame,api,fun error => (memory error).2,live,dead⟩

/-- All four original utility entry points inherit the complete default
capacity contract, exact original-caller Store/Frame and real cleanup on
this explicit internal domain, for every admitted source size and oracle. -/
theorem default_capacity_family_total {h : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity n : UInt64} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo) :
    ∃ rc output after expected,
      C.run (compress2_z dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      C.run (compress_z dest (some capacity) source n) h = .ok ((rc,some (UInt64.ofNat output.length)),after) ∧
      C.run (compress2 dest (some capacity) source n Z_DEFAULT_COMPRESSION) h = .ok ((rc,UInt64.ofNat output.length),after) ∧
      C.run (compress dest (some capacity) source n) h = .ok ((rc,UInt64.ofNat output.length),after) ∧
      (UInt64.ofNat output.length).toNat = output.length ∧ Bytes after dest output.length output ∧
      Store h dest output expected ∧ Frame expected after (fun _ => False) ∧
      Api.Compress2Wrapper
        {source := xs,capacity := capacity.toNat,level := Z_DEFAULT_COMPRESSION.toInt,
          sourceNull := source == .null,destNull := dest == .null,lengthNull := false}
        {rc := rc.toInt,produced := output,storedLength := (some (UInt64.ofNat output.length)).map UInt64.toNat} ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) ∧ (∀ b,after.live b ↔ h.live b) ∧ after.streams h.nextBlk = none := by
  obtain ⟨rc,output,after,expected,actual,word,physical,store,frame,api,memory,live,dead⟩ :=
    default_wrapper_capacity_total fresh unique globals objects bytes writable separate pointer
  have compat := compatibility_run_of_z actual
  exact ⟨rc,output,after,expected,actual,actual,compat,compat,word,physical,store,frame,⟨rfl,api⟩,memory,live,dead⟩

end ZlibF.Spec.Public.Proofs.CompressCapacity
