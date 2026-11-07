import ZlibF.Proof.«public-crc-updates»
import ZlibF.Spec.Public.Domains

/-!
# Static-byte-view CRC regression

The witness and 47-byte input are identical to the former address-model
counterexample. Both actual public entries now return the independent CRC
update and preserve the same heap.
-/
open C Zlib.Crc32 Zlib.Crc32.Proofs ZlibF.Spec.Public

def crcWitness : Heap := witnessHeap

def crcWitnessBytes : List UInt8 := (crcWitness.static.dist_code.toList.drop 0).take 47

theorem crc_witness_globals : CrcGlobals crcWitness := by
  simp [CrcGlobals, crcWitness, witnessHeap, Zlib.Crc32.initStatics]

theorem crc_witness_buffer :
    BufferBytes crcWitness (.ref .st_dist_code 0) 47 crcWitnessBytes := by
  right
  refine ⟨.st_dist_code, 0, crcWitness.static.dist_code, rfl, ?_, ?_, rfl⟩
  · rfl
  · decide +kernel


/-- The unchanged static-view witness has the exact independent checksum. -/
theorem crc_witness_correct :
    C.run (crc32_z 0 (.ref .st_dist_code 0) 47) crcWitness =
      .ok ((ZlibF.Spec.crc32Update 0 crcWitnessBytes).toUInt64,crcWitness) := by
  have result := ZlibF.Spec.Public.Proofs.crc32_z crcWitness 0 (.ref .st_dist_code 0) 47
    crcWitnessBytes crc_witness_globals crc_witness_buffer
  simpa only [reduceCtorEq,ite_false,show (0 : UInt64).toUInt32 = (0 : UInt32) by decide] using result

/-- The 32-bit-length compatibility entry returns the same exact value. -/
theorem crc32_witness_correct :
    C.run (crc32 0 (.ref .st_dist_code 0) 47) crcWitness =
      .ok ((ZlibF.Spec.crc32Update 0 crcWitnessBytes).toUInt64,crcWitness) := by
  have result := ZlibF.Spec.Public.Proofs.crc32 crcWitness 0 (.ref .st_dist_code 0) 47
    crcWitnessBytes crc_witness_globals crc_witness_buffer
  simpa only [reduceCtorEq,ite_false,show (0 : UInt64).toUInt32 = (0 : UInt32) by decide] using result

#print axioms crc_witness_correct
#print axioms crc32_witness_correct
