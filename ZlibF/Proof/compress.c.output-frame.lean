import ZlibF.Proof.«compress.c.api-header»

/-! # Exact original caller frames through the real compressor loop -/
namespace ZlibF.Spec.Public.Proofs.CompressMemory
open C Zlib.Compress Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Spec.Public.Proofs.CompressLoop ZlibF.Spec.Public.Proofs.CompressCaller
open ZlibF.Spec.Public.Proofs.CompressPrefix ZlibF.Spec.Public.Proofs.CompressTail
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Complete old-object frames compose using their own retained slots;
allocations in the permitted footprint need no global shape assumption. -/
theorem frame_trans {h mid after : Heap} {changed : Nat → Prop}
    (one : Frame h mid changed) (two : Frame mid after changed) : Frame h after changed := by
  obtain ⟨s1, a1, g1, n1, c1, slots1⟩ := one
  obtain ⟨s2, a2, g2, n2, c2, slots2⟩ := two
  refine ⟨s1.trans s2, a1.trans a2, g1.trans g2, Nat.le_trans n1 n2, Nat.le_trans c1 c2, ?_⟩
  intro b live outside
  have first : SlotSame h mid b := slots1 b live outside
  exact first.trans (slots2 b (first.live.mpr live) outside)

private theorem frame_refl (h : Heap) (changed : Nat → Prop) : Frame h h changed :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

private theorem trace_calls {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) : DeflateCore.Calls r h := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ get raw observed ih =>
    obtain ⟨z, _z', getZ, _getA, buffers, _active, _snapshot, _used, _written, run⟩ := observed
    have same : z = _ := Option.some.inj (getZ.symm.trans get)
    subst z
    exact .step ih get buffers raw run

/-- The actual refill and actual engine call preserve every old slot
outside the fixed private keys and the caller output allocation. -/
theorem body_frame {h after : Heap} {slot ds ob oo : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {old : Int32} {left sourceLen : UInt64} {source : List UInt8} {last : Locals}
    (boundary : DefaultFinishBoundary h (.tab slot) ds z d config) (globals : LibraryGlobals h)
    (ranges : Ranges h (.tab slot) z left sourceLen source) (pointer : z.next_out = .ref (.blk ob) oo)
    (actual : body (some (.tab slot)) (old, left, sourceLen) h = .ok (last, after)) :
    Frame h after (fun b => b = slot ∨ configOwned ds config b ∨ b = ob) := by
  have get : h.streams slot = some z := boundary.good.live.hz
  have edit := prepare_rebuffer boundary.good globals left sourceLen
  obtain ⟨zp, getP, boundaryP⟩ := boundary.rebuffer edit
  have sameP : zp = CompressLoop.preparedStream z left sourceLen :=
    Option.some.inj (getP.symm.trans (prepare_get h slot z left sourceLen get))
  subst zp
  have rangesP := prepare_ranges boundary.good ranges
  obtain ⟨buffersP, _snapshot⟩ := ranges_current getP rangesP
  have pointerP : (CompressLoop.preparedStream z left sourceLen).next_out = .ref (.blk ob) oo := pointer
  let flush := if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH
  have flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH := by unfold flush; split <;> simp
  obtain ⟨used, written, rc, computed, z', result, engineRun, _rest⟩ :=
    boundaryP.all_scalar_request_contract flush buffersP (Or.inr ⟨ob, oo, pointerP⟩)
  have bodyRun : body (some (.tab slot)) (old, left, sourceLen) h =
      .ok ((rc, (prepare h slot z left sourceLen).1, (prepare h slot z left sourceLen).2.1), computed) := by
    rw [body_prepare h slot z old left sourceLen get]
    change deflate (some (.tab slot))
      (if (prepare h slot z left sourceLen).2.1 != 0 then Z_NO_FLUSH else Z_FINISH)
      (prepare h slot z left sourceLen).2.2 = .ok (rc, computed) at engineRun
    rcases eq : prepare h slot z left sourceLen with ⟨l,n,prepared⟩
    simp only [eq] at engineRun ⊢
    simp only [bind_app, engineRun, pure_app]
  have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))).2
  subst computed
  have storage := boundaryP.ordinary_run_full_storage flag buffersP (Or.inr ⟨ob,oo,pointerP⟩) engineRun
  have preparedFrame : Frame h (prepare h slot z left sourceLen).2.2 (StreamRoot (.tab slot)) := by
    rw [prepare_eq_put h slot z left sourceLen get]
    exact Zlib.Deflate.Proofs.DefaultInit.frame_put _ _ boundary.good.fresh
  have a : Frame h (prepare h slot z left sourceLen).2.2
      (fun b => b = slot ∨ configOwned ds config b ∨ b = ob) :=
    full_frame_weaken preparedFrame (fun _ root => Or.inl root)
  have b : Frame (prepare h slot z left sourceLen).2.2 after
      (fun b => b = slot ∨ configOwned ds config b ∨ b = ob) := by
    apply full_frame_weaken storage.2.1
    intro b changed
    rcases changed with root | own | output
    · exact Or.inl root
    · exact Or.inr (Or.inl (by rw [←boundary_owned_config boundaryP]; exact own))
    · exact Or.inr (Or.inr (by simpa only [pointerP, ByteRoot] using output))
  exact frame_trans a b

/-- Every finite actual loop execution has the complete fixed-footprint
old-object frame. No auxiliary execution replaces its concrete body. -/
theorem prefix_frame {slot ds ob oo k : Nat} {start after : Heap} {last : Locals}
    {first : ZStream} {d : DeflateState} {config : EngineConfig}
    {left sourceLen : UInt64} {source : List UInt8}
    (history : DefaultDataTrace (.tab slot) start {})
    (initial : DefaultFinishBoundary start (.tab slot) ds first d config)
    (ranges : Ranges start (.tab slot) first left sourceLen source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (execution : ActualPrefix slot start (Z_OK, left, sourceLen) k after last) :
    Frame start after (fun b => b = slot ∨ configOwned ds config b ∨ b = ob) := by
  induction execution with
  | nil => exact frame_refl _ _
  | @step k h after current next previous _guard actual ih =>
    obtain ⟨currentZ, currentD, boundary, _shape, _count, _next⟩ :=
      prefix_resources history initial ranges pointer previous
    obtain ⟨used, log, observedZ, sound⟩ :=
      actual_prefix_sound history initial.good.live.hz ranges pointer previous
    have same : currentZ = observedZ := Option.some.inj (boundary.good.live.hz.symm.trans sound.get)
    subst currentZ
    have raw : observedZ.next_out = .ref (.blk ob) (oo + log.output.length) := by
      rw [sound.outputPtr, pointer]
      rfl
    have globals := ZlibF.Spec.Public.Proofs.DeflateCore.calls_globals (trace_calls sound.history)
    rcases current with ⟨old,l,n⟩
    exact frame_trans ih (body_frame boundary globals sound.remaining raw actual)

/-- The physical output changes only the cumulative interval at the
original destination. Every byte before and after it keeps its old value. -/
theorem prefix_interval {slot ob oo k : Nat} {start after : Heap} {last : Locals}
    {first finalZ : ZStream} {left sourceLen : UInt64} {source : List UInt8} {used : Nat} {log : DataLog}
    (history : DefaultDataTrace (.tab slot) start {}) (get : start.streams slot = some first)
    (ranges : Ranges start (.tab slot) first left sourceLen source)
    (pointer : first.next_out = .ref (.blk ob) oo)
    (execution : ActualPrefix slot start (Z_OK, left, sourceLen) k after last)
    (account : PrefixAccount slot first left sourceLen source k after last used log finalZ) :
    RawOutputInterval start after ob oo log.output.length := by
  induction execution generalizing used log finalZ with
  | nil => exact RawOutputInterval.of_same rfl
  | @step k h after current next previous guard actual ih =>
    obtain ⟨already, oldLog, currentZ, known⟩ := actual_prefix_sound history get ranges pointer previous
    have one := ih known
    have raw : currentZ.next_out = .ref (.blk ob) (oo + oldLog.output.length) := by
      rw [known.outputPtr, pointer]
      rfl
    rcases current with ⟨old,l,n⟩
    obtain ⟨taken, written, rc, computed, returned, run, _traceA, getA, _rangesA, _inputCount,
      outputCount, _inputPtr, _outputPtr, _outputBytes, effect, _ended⟩ :=
      body_observed_step known.history known.get old l n (source.drop already) known.remaining raw
    obtain ⟨states, heaps⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
    subst computed next
    have same : returned = finalZ := Option.some.inj (getA.symm.trans account.get)
    subst returned
    have countOld := known.outputCount
    have countFinal := account.outputCount
    dsimp only at countOld countFinal
    have total : log.output.length = oldLog.output.length + written.length := by omega
    rw [total]
    exact one.trans effect


/-- Automatic storage, real successful init and the actual buffer stores
retain every original caller object, including all its record metadata. -/
theorem setup_frame {h initialized ready : Heap} {dest source : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized))
    (actualSetup : C.run (zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source)) initialized = .ok ((), ready)) :
    Frame h ready (fun _ => False) := by
  have domain := automatic_stream_domain h fresh unique globals
  let p := ZlibF.Spec.Public.Proofs.DeflateInit.settings 6
  have params : Api.deflInit? Z_DEFAULT_COMPRESSION.toInt 8 15 8 0 = some p := by decide +kernel
  obtain ⟨zf, sf, _start, initial, _rest⟩ := common_observed_initialization_first_ordinary_encoding
    domain params (by decide +kernel) (by decide +kernel) actualInit
  obtain ⟨zi, si, good, _alloc, _free, _level, _strategy, _bits, _hash, _wrap,
    _start, _look, _pending, _valid, _header, _tin, _tout, _msg, frameI, _live, _owned⟩ := initial
  have get : initialized.streams h.nextBlk = some zi := good.live.hz
  have setupRun : C.run (zwr (some (.tab h.nextBlk)) (fun z => bindings z dest source)) initialized =
      .ok ((), (ZStreamRef.tab h.nextBlk).put initialized (bindings zi dest source)) := by
    simp [C.run,zwr,ldZStream,stZStream,ZStreamRef.get,ZStreamRef.isRo,get]
  have readyEq := (Prod.mk.inj (Except.ok.inj (setupRun.symm.trans actualSetup))).2
  have frameS : Frame initialized ready (StreamRoot (.tab h.nextBlk)) := by
    rw [←readyEq]
    exact Zlib.Deflate.Proofs.DefaultInit.frame_put _ _ good.fresh
  have frameLocal : Frame h (localHeap h) (StreamRoot (.tab h.nextBlk)) := by
    refine ⟨rfl,rfl,rfl,by simp [localHeap],by simp [localHeap],?_⟩
    intro b live outside
    have different : b ≠ h.nextBlk := outside
    simp [SlotSame,localHeap,upd_ne _ _ _ _ different]
  have total := frame_trans frameLocal (frame_trans frameI frameS)
  refine ⟨total.1,total.2.1,total.2.2.1,total.2.2.2.1,total.2.2.2.2.1,?_⟩
  intro b live _outside
  exact total.2.2.2.2.2 b live (by
    intro same
    change b = h.nextBlk at same
    subst b
    exact fresh _ (Nat.le_refl _) live)

private theorem release_unique {h : Heap} (unique : Uniq h) (slot : Nat) : Uniq (releaseLocal h slot) := by
  intro b
  by_cases same : b = slot
  · subst b
    have old := unique slot
    simp only [Uniq,releaseLocal,upd_same,cnt_none] at ⊢
    omega
  · simpa only [releaseLocal,upd_ne _ _ _ _ same] using unique b

private theorem tail_unique {h after : Heap} {slot : Nat} {log : DataLog} {z : ZStream}
    {dest : BPtr} {err rc : Int32} {stored : Option UInt64} {n : Int64}
    (history : DefaultDataTrace (.tab slot) h log) (get : h.streams slot = some z)
    (difference : ptrDiff z.next_out dest h = .ok (n,h))
    (actual : tail (some (.tab slot)) dest err h = .ok ((rc,stored),after)) : Uniq after := by
  obtain ⟨ds,current,d,ended,good,endRun,getEnd,_live,_frame,_count,_next⟩ := history.cleanup
  have same : current = z := Option.some.inj (good.live.hz.symm.trans get)
  subst current
  obtain ⟨za,getA,alloc⟩ := history.allocators
  have sameZ : za = z := Option.some.inj (getA.symm.trans get)
  subst za
  obtain ⟨w,p,q,b,blocks⟩ := good.inv.blocks
  have canonicalEnd := deflateEnd_run good.live alloc.2 blocks
  have endEq : ended = endHeap h (.tab slot) ds z d := by
    have events : (.ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK),ended) :
        Except Fault (Int32×Heap)) = .ok ((if d.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),endHeap h (.tab slot) ds z d) :=
      endRun.symm.trans canonicalEnd
    exact (Prod.mk.inj (Except.ok.inj events)).2
  have uniqueEnd : Uniq ended := by rw [endEq]; exact endHeap_uniq blocks good.uniq good.live.hz
  have canonical : tail (some (.tab slot)) dest err h =
      .ok ((if err == Z_STREAM_END then Z_OK else err,some n.toUInt64),releaseLocal ended slot) := by
    change deflateEnd (some (.tab slot)) h = _ at endRun
    simp only [tail,bind_app,zrd_eq,ZStreamRef.get,get,pure_app,difference,endRun]
    have endedStream : ended.streams slot = some {z with state := none} := getEnd
    simp [freeZStream,endedStream,releaseLocal]
  have heapEq := (Prod.mk.inj (Except.ok.inj (canonical.symm.trans actual))).2
  rw [←heapEq]
  exact release_unique uniqueEnd slot

/-- The whole actually returning successful-init execution retains all
original object slots outside its caller output allocation and changes
only the exact emitted interval inside that allocation. Both facts refer
to the same original h and final after as the real scalar return. -/
theorem successful_memory {h initialized after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen written : UInt64} {rc : Int32} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_OK, initialized))
    (actual : C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
      .ok ((rc, some written), after)) :
    Frame h after (fun b => b = ob) ∧ RawOutputInterval h after ob oo written.toNat ∧
      Uniq after ∧ after.ro ob = h.ro ob := by
  obtain ⟨ready, last, loopHeap, setup, actualLoop, _stopped, _valid⟩ :=
    original_buffers_loop_total fresh unique globals objects bytes writable separate pointer actualInit
  obtain ⟨ready0, first, setup0, history, get, ranges, out, _in, outAvail, _inAvail⟩ :=
    successful_default_seed fresh unique globals bytes writable separate actualInit
  have readyEq := (Prod.mk.inj (Except.ok.inj (setup0.symm.trans setup))).2
  subst ready0
  obtain ⟨initialZ, initialD, initial, _initLive, initOwned, _initCount, _initNext⟩ :=
    setup_resources (dest := dest) (source := source) fresh unique globals actualInit setup
  have firstEq : initialZ = first := Option.some.inj (initial.good.live.hz.symm.trans get)
  subst initialZ
  have raw := out.trans pointer
  obtain ⟨k, _positive, _fuel, execution⟩ := loop_go_prefix (slot := h.nextBlk) rfl actualLoop
  obtain ⟨used, log, returned, sound⟩ := actual_prefix_sound history get ranges raw execution
  obtain ⟨endZ, endD, boundary, _shape, _count, _next⟩ := prefix_resources history initial ranges raw execution
  have sameZ : endZ = returned := Option.some.inj (boundary.good.live.hz.symm.trans sound.get)
  subst endZ
  obtain ⟨buffers, _input⟩ := ranges_current (r := .tab h.nextBlk) sound.get sound.remaining
  have cursor : returned.next_out = .ref (.blk ob) (oo + log.output.length) := by
    rw [sound.outputPtr, raw]
    rfl
  have outputBytes : Bytes loopHeap (.ref (.blk ob) oo) log.output.length log.output := by
    rw [←raw]
    exact sound.outputBytes
  have fits : log.output.length ≤ capacity.toNat := by
    have count := sound.outputCount
    rw [outAvail] at count
    simp only [UInt32.toNat_zero,Nat.zero_add] at count
    omega
  have capacityBound : capacity.toNat < 2^63 := by
    rcases writable with ⟨impossible,_⟩ | ⟨ref,offset,a,_eq,getA,_ro,bound⟩
    · rw [pointer] at impossible
      cases impossible
    · have size := objects ref a getA
      change a.size < 2^63 at size
      omega
  obtain ⟨ds,d,computed,good,tailRun,_finalBytes,_dead,_live,tailFrame,_count,_next,word⟩ :=
    tail_nonnull_exact sound.history sound.get buffers cursor outputBytes (by omega) last.1
  have dsEq : ds = (localHeap h).nextBlk := StateRef.deflate.inj
    (Option.some.inj (good.live.zst.symm.trans boundary.good.live.zst))
  subst ds
  have dEq : d = endD := Option.some.inj (good.live.hs.symm.trans boundary.good.live.hs)
  subst d
  have nonnull : dest ≠ .null := by rw [pointer]; intro bad; cases bad
  have computedRun := run_of_successful_stages fresh bytes nonnull actualInit setup actualLoop
    (by rw [pointer]; exact tailRun)
  have events := Prod.mk.inj (Except.ok.inj (computedRun.symm.trans actual))
  have scalar := Option.some.inj (congrArg Prod.snd events.1)
  have heapEq := events.2
  have length : written.toNat = log.output.length := by rw [←scalar]; exact word
  have own : DeflateOwned (localHeap h).nextBlk endD = configOwned (localHeap h).nextBlk (engineConfig initialD) :=
    boundary_owned_config boundary
  let changed := fun b => b = h.nextBlk ∨ configOwned (localHeap h).nextBlk (engineConfig initialD) b ∨ b = ob
  have beforeFrame := setup_frame fresh unique globals actualInit setup
  have a : Frame h ready changed := full_frame_weaken beforeFrame (fun _ bad => False.elim bad)
  have b : Frame ready loopHeap changed := prefix_frame history initial ranges raw execution
  have c : Frame loopHeap computed changed := by
    apply full_frame_weaken tailFrame
    intro b changedHere
    rcases changedHere with root | owned
    · exact Or.inl root
    · exact Or.inr (Or.inl (by rw [←own]; exact owned))
  have total := frame_trans a (frame_trans b c)
  have slotFrame : Frame h after (fun b => b = ob) := by
    rw [←heapEq]
    refine ⟨total.1,total.2.1,total.2.2.1,total.2.2.2.1,total.2.2.2.2.1,?_⟩
    intro b live outside
    apply total.2.2.2.2.2 b live
    intro changedHere
    rcases changedHere with root | owned | output
    · exact fresh _ (by omega) (root ▸ live)
    · have freshKey := (initOwned b).mp owned
      have lower := freshKey.1
      exact fresh b (by change h.nextBlk+1 ≤ b at lower; omega) live
    · exact outside output
  have getOutput : ∃ a, h.bytes ob = some a := by
    rw [pointer] at writable
    rcases writable with ⟨impossible,_⟩ | ⟨ref,off,a,equal,getA,_ro,_bound⟩
    · cases impossible
    · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj equal
      exact ⟨a,getA⟩
  obtain ⟨original,getOriginal⟩ := getOutput
  have outputLive : h.live ob := by simp [Heap.live,getOriginal]
  have getReady : ready.bytes ob = h.bytes ob := (beforeFrame.2.2.2.2.2 ob outputLive (fun bad => bad)).1
  have firstInterval : RawOutputInterval h ready ob oo 0 := RawOutputInterval.of_same getReady
  have middle := prefix_interval history get ranges raw execution sound
  have lastInterval : RawOutputInterval loopHeap computed ob (oo+log.output.length) 0 :=
    RawOutputInterval.of_same (private_frame_raw_output_same good buffers cursor tailFrame).1
  have interval : RawOutputInterval h computed ob oo log.output.length := by
    have combined : RawOutputInterval h loopHeap ob oo log.output.length := by
      simpa only [Nat.zero_add] using firstInterval.trans middle
    simpa only [Nat.add_zero] using combined.trans lastInterval
  have difference := raw_ptrdiff_exact outputBytes (show log.output.length < 2^63 by omega)
  rw [←cursor] at difference
  have uniqueFinal := tail_unique sound.history sound.get difference tailRun
  obtain ⟨_output,_getLoop,loopRo,_boundLoop,_outsideLoop⟩ := caller_raw_output good buffers cursor
  have originalRo : h.ro ob = false := by
    rw [pointer] at writable
    rcases writable with ⟨impossible,_⟩ | ⟨ref,off,a,equal,_get,ro,_bound⟩
    · cases impossible
    · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj equal
      exact ro
  have finalRo := (private_frame_raw_output_same good buffers cursor tailFrame).2
  refine ⟨slotFrame,?_,?_,?_⟩
  · rw [←heapEq,length]
    exact interval
  · rw [←heapEq]
    exact uniqueFinal
  · rw [←heapEq,finalRo,loopRo,originalRo]

private theorem same_objects_frame {h after : Heap} (same : SameObjects h after) : Frame h after (fun _ => False) := by
  obtain ⟨bytes,words,ro,streams,headers,dstates,istates,gzstates,static,alloc,garbage,next,count⟩ := same
  refine ⟨static.symm,alloc.symm,garbage.symm,next,count,?_⟩
  intro b live _outside
  exact ⟨congrArg (fun t => t b) bytes,congrArg (fun t => t b) words,
    congrArg (fun t => t b) streams,congrArg (fun t => t b) headers,
    congrArg (fun t => t b) dstates,congrArg (fun t => t b) istates,
    congrArg (fun t => t b) gzstates,ro b live⟩

/-- Real initialization failure preserves all old slots outside its root,
including rollback of every successfully allocated private buffer. -/
theorem initialization_failure_frame {h after : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (get : r.get h = some z) (allocators : DefaultOrNull z) (valid : VersionValue h version (some 49))
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_MEM_ERROR, after)) :
    Frame h after (StreamRoot r) := by
  obtain ⟨rc,computed,run,post⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
      h r z version fresh unique globals get allocators valid
  have events := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  rw [events.1,events.2] at post
  change (if h.allocOk h.nalloc = false then
      Z_MEM_ERROR = Z_MEM_ERROR ∧ after.nalloc = h.nalloc+1 ∧ SameObjects (r.put h (ZlibF.Spec.Public.preparedStream z)) after
    else after.nalloc = h.nalloc+5 ∧
      if (List.range 5).all (fun j => h.allocOk (h.nalloc+j)) then
        Z_MEM_ERROR = Z_OK ∧ DeflateInitial h after r (ZlibF.Spec.Public.Proofs.DeflateInit.settings 6)
      else Z_MEM_ERROR = Z_MEM_ERROR ∧ (∃z',r.get after = some z' ∧ z'.state = none) ∧
        LiveChange h after (fun _ => False) (fun _ => False) ∧ Frame h after (StreamRoot r)) at post
  by_cases first : h.allocOk h.nalloc = false
  · simp only [first,ite_true] at post
    exact frame_trans (Zlib.Deflate.Proofs.DefaultInit.frame_put r _ fresh)
      (full_frame_weaken (same_objects_frame post.2.2) (fun _ bad => False.elim bad))
  · simp only [first,ite_false] at post
    by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc+j)) = true
    · simp only [all,ite_true] at post
      cases post.2.1
    · simp only [all,Bool.false_eq_true,ite_false] at post
      exact post.2.2.2.2

/-- The actual early MEM_ERROR return retains every old caller slot;
the automatic stream is freed on this same return. -/
theorem failure_memory {h initialized after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen written : UInt64} {rc : Int32} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (bytes : Bytes h source sourceLen.toNat xs) (pointer : dest = .ref (.blk ob) oo)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112) (localHeap h) = .ok (Z_MEM_ERROR, initialized))
    (actual : C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
      .ok ((rc,some written),after)) :
    Frame h after (fun _ => False) ∧ written = 0 ∧ Uniq after := by
  obtain ⟨f,u,g,v,old,oldGet,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
  have shape := memory_failure_shape f u g oldGet alloc v actualInit
  have someStream : ∃z,initialized.streams h.nextBlk = some z := by
    have present := (shape h.nextBlk).2.2.1
    change (initialized.streams h.nextBlk).isSome = ((localHeap h).streams h.nextBlk).isSome at present
    simp only [localHeap,upd_same,Option.isSome_some] at present
    cases eq : initialized.streams h.nextBlk with
    | none => simp only [eq,Option.isSome_none,Bool.false_eq_true] at present
    | some z => exact ⟨z,rfl⟩
  obtain ⟨z,get⟩ := someStream
  have guard : ((sourceLen>0 && source == .null) || (capacity>0 && dest == .null)) = false := by
    apply Bool.eq_false_iff.mpr
    intro bad
    have cases : (sourceLen>0 ∧ source = .null) ∨ (capacity>0 ∧ dest = .null) := by
      simpa only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using bad
    rcases cases with ⟨positive,null⟩ | ⟨_positive,null⟩
    · rw [null] at bytes
      rcases bytes with ⟨_,zero,_⟩ | ⟨_,_,_,impossible,_⟩
      · have gt := UInt64.lt_iff_toNat_lt.mp positive
        change 0 < sourceLen.toNat at gt
        omega
      · cases impossible
    · rw [pointer] at null
      cases null
  have automatic : preInit h = .ok ((some (.tab h.nextBlk),.ref (.str 57) 0),localHeap h) := automatic_stream_run h fresh
  have free : freeZStream (some (.tab h.nextBlk)) initialized = .ok ((),releaseLocal initialized h.nextBlk) := by
    simp [freeZStream,get,releaseLocal]
  have canonical : C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
      .ok ((Z_MEM_ERROR,some 0),releaseLocal initialized h.nextBlk) := by
    rw [compress2_z_stages]
    change deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 (localHeap h) = _ at actualInit
    simp only [C.run,sizeof_z_stream,guard,Bool.false_eq_true,ite_false,bind_app,automatic,actualInit,
      show (Z_MEM_ERROR != Z_OK) = true from rfl,ite_true,free,pure_app]
  have events := Prod.mk.inj (Except.ok.inj (canonical.symm.trans actual))
  have heapEq := events.2
  have scalar := Option.some.inj (congrArg Prod.snd events.1)
  have frameL : Frame h (localHeap h) (StreamRoot (.tab h.nextBlk)) := by
    refine ⟨rfl,rfl,rfl,by simp [localHeap],by simp [localHeap],?_⟩
    intro b _live outside
    have different : b ≠ h.nextBlk := outside
    simp [SlotSame,localHeap,upd_ne _ _ _ _ different]
  have frameI := initialization_failure_frame f u g oldGet alloc v actualInit
  have frameF : Frame initialized (releaseLocal initialized h.nextBlk) (StreamRoot (.tab h.nextBlk)) := by
    refine ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,?_⟩
    intro b _live outside
    have different : b ≠ h.nextBlk := outside
    simp [SlotSame,releaseLocal,upd_ne _ _ _ _ different]
  have total := frame_trans frameL (frame_trans frameI frameF)
  have finalFrame : Frame h after (fun _ => False) := by
    rw [←heapEq]
    refine ⟨total.1,total.2.1,total.2.2.1,total.2.2.2.1,total.2.2.2.2.1,?_⟩
    intro b live _outside
    exact total.2.2.2.2.2 b live (by intro same; change b = h.nextBlk at same; subst b; exact fresh _ (Nat.le_refl _) live)
  have finalUnique : Uniq after := by
    rw [←heapEq]
    exact release_unique (shape.uniq u) _
  exact ⟨finalFrame,scalar.symm,finalUnique⟩

/-- Every actual return has the original caller-object frame and exact
output-array interval, for all allocation oracles. The returned scalar
indexes that same physical interval. -/
theorem actual_memory {h after : Heap} {dest source : BPtr} {ob oo : Nat}
    {capacity sourceLen written : UInt64} {rc : Int32} {xs : List UInt8}
    (fresh : Fresh h) (unique : Uniq h) (globals : LibraryGlobals h)
    (objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (bytes : Bytes h source sourceLen.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source sourceLen.toNat dest capacity.toNat) (pointer : dest = .ref (.blk ob) oo)
    (actual : C.run (compress2_z dest (some capacity) source sourceLen Z_DEFAULT_COMPRESSION) h =
      .ok ((rc,some written),after)) :
    Frame h after (fun b => b = ob) ∧ RawOutputInterval h after ob oo written.toNat ∧
      Uniq after ∧ after.ro ob = h.ro ob := by
  obtain ⟨f,u,g,v,old,get,alloc,_null⟩ := automatic_stream_domain h fresh unique globals
  obtain ⟨initRc,initialized,actualInit,allowed⟩ := default_initialization_total f u g get alloc v
  rcases allowed with ok | memory
  · subst initRc
    exact successful_memory fresh unique globals objects bytes writable separate pointer actualInit actual
  · subst initRc
    obtain ⟨frame,zero,uniqueFinal⟩ := failure_memory fresh unique globals bytes pointer actualInit actual
    have readonly : after.ro ob = h.ro ob := by
      rw [pointer] at writable
      rcases writable with ⟨impossible,_⟩ | ⟨ref,off,a,equal,getA,_ro,_bound⟩
      · cases impossible
      · obtain ⟨rfl,rfl⟩ := Ptr.ref.inj equal
        have live : h.live ob := by simp [Heap.live,show h.bytes ob = some a from getA]
        exact (frame.2.2.2.2.2 ob live (fun bad => bad)).2.2.2.2.2.2.2
    refine ⟨full_frame_weaken frame (fun _ bad => False.elim bad),?_,uniqueFinal,readonly⟩
    rw [zero]
    intro before getBefore
    have live : h.live ob := by simp [Heap.live,getBefore]
    have same := (frame.2.2.2.2.2 ob live (fun bad => bad)).1
    exact ⟨before,same.trans getBefore,rfl,fun _ _ _ => rfl⟩

end ZlibF.Spec.Public.Proofs.CompressMemory
