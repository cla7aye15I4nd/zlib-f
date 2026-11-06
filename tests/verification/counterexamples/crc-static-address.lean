/- Diagnostic for the current address-model blocker. This is outside the library import closure
   and theorem registry. Repair the translation model before attempting the public CRC goals. -/
import ZlibF.Spec.Public.Domains
import ZlibF.Proof.«crc32.c»
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

theorem crc_witness_fault :
    C.run (crc32_z 0 (.ref .st_dist_code 0) 47) crcWitness =
      .error (.ub "address of a pointer that is not into a heap block is not modelled") := by
  rfl

theorem crc_public_false : ¬ Goal.crc32_z := by
  intro goal
  have h := goal crcWitness 0 (.ref .st_dist_code 0) 47 crcWitnessBytes crc_witness_globals crc_witness_buffer
  rw [crc_witness_fault] at h
  cases h

theorem crc32_witness_fault :
    C.run (crc32 0 (.ref .st_dist_code 0) 47) crcWitness =
      .error (.ub "address of a pointer that is not into a heap block is not modelled") := by
  rfl

theorem crc32_public_false : ¬ Goal.crc32 := by
  intro goal
  have h := goal crcWitness 0 (.ref .st_dist_code 0) 47 crcWitnessBytes crc_witness_globals crc_witness_buffer
  rw [crc32_witness_fault] at h
  cases h

#print axioms crc_public_false
#print axioms crc32_public_false
