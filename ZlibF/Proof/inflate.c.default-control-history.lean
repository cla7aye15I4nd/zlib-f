import ZlibF.Proof.«inflate.c.default-public-memory-contract»
import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«inflate.c.prime-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default initialization, processing and selected control calls.
Every edge records the translated execution, never its desired contract.
Rebuffered caller objects satisfy the explicit platform scope. Reset2 is
selected at fifteen bits. Copy, sync and dictionary transitions must still
be added before this covers the entire public history relation. -/
inductive DefaultControlHistory : Heap → ZStreamRef → Prop where
  | init {h after r version} :
      InitDomain h r version → ZlibF.PlatformMemory.ByteObjectsFit h →
      h.allocOk h.nalloc = true →
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) → DefaultControlHistory after r
  | rebuffer {h after r} : DefaultControlHistory h r → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → DefaultControlHistory after r
  | inflate {h after r rc flush} : DefaultControlHistory h r → StreamBuffers h r →
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) → DefaultControlHistory after r
  | resetKeep {h after r rc} : DefaultControlHistory h r →
      C.run (inflateResetKeep (some r)) h = .ok (rc, after) → DefaultControlHistory after r
  | reset {h after r rc} : DefaultControlHistory h r →
      C.run (inflateReset (some r)) h = .ok (rc, after) → DefaultControlHistory after r
  | reset2 {h after r rc} : DefaultControlHistory h r →
      C.run (inflateReset2 (some r) 15) h = .ok (rc, after) → DefaultControlHistory after r
  | prime {h after r rc bits value} : DefaultControlHistory h r →
      C.run (inflatePrime (some r) bits value) h = .ok (rc, after) → DefaultControlHistory after r
  | validate {h after r rc check} : DefaultControlHistory h r →
      C.run (inflateValidate (some r) check) h = .ok (rc, after) → DefaultControlHistory after r
  | getHeader {h after r rc head} : DefaultControlHistory h r →
      HeaderMemory h r head true → head ≠ none →
      C.run (inflateGetHeader (some r) head) h = .ok (rc, after) → DefaultControlHistory after r
  | undermine {h after r rc subvert} : DefaultControlHistory h r →
      C.run (inflateUndermine (some r) subvert) h = .ok (rc, after) → DefaultControlHistory after r

end Zlib.Inflate.Proofs
