import ZlibF.Proof.Format.Huffman
namespace ZlibF.Spec.SmallCmfTinyToken
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem length257 (tail : List Bool) :
    decodeSym fixedLitLens ([false,false,false,false,false,false,true] ++ tail) = some (257, tail) := by
  simpa only [List.nil_append] using ZlibF.Spec.Proofs.ext_fixedLit _ _ _ tail
    (by decide +kernel : decodeSym fixedLitLens [false,false,false,false,false,false,true] = some (257, []))

theorem distance16 (tail : List Bool) :
    decodeSym fixedDistLens ([true,false,false,false,false] ++ tail) = some (16, tail) := by
  simpa only [List.nil_append] using ZlibF.Spec.Proofs.ext_fixedDist _ _ _ tail
    (by decide +kernel : decodeSym fixedDistLens [true,false,false,false,false] = some (16, []))

#print axioms length257
#print axioms distance16
end ZlibF.Spec.SmallCmfTinyToken
