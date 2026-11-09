import ZlibF.Spec.Format.Checksum
namespace ZlibF.Spec.ConfiguredWindowChecksum
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem dict512 : adler32 (List.replicate 512 (0x41 : UInt8)) = 0x4a9e8201 := by decide +kernel
#print axioms dict512
end ZlibF.Spec.ConfiguredWindowChecksum
