import ZlibF.Proof.«inflate.c.local-public-resources-public-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Attach the exact original output prefix frame to an already identified
actual public call and its actual accounting. Every returning source branch
is included, including entry rejection, dictionary requests and late failure. -/
theorem inflate_default_view_public_frame_of_run
    {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {flush rc : Int32} {used made : Nat}
    (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r)
    (run : C.run (inflate (some r) flush) h = .ok (rc, after))
    (final : LocalGood after cutoff r zs stream state)
    (account : StreamAccounting z stream used made) :
    BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) [⟨z.next_out, made⟩] := by
  obtain ⟨rc2, after2, stream2, state2, used2, made2, run2, current2, _, _, _, _, account2, frame⟩ :=
    inflate_default_view_public_exact_frame invariant allocator buffers flush
  have same := Except.ok.inj (run2.symm.trans run)
  cases same
  have streams : stream2 = stream := Option.some.inj (current2.good.live.hz.symm.trans final.live.hz)
  subst stream2
  have first := account.2.2.2.1
  have second := account2.2.2.2.1
  have madeEq : made2 = made := by omega
  simpa only [madeEq] using frame

#print axioms inflate_default_view_public_frame_of_run
end Zlib.Inflate.Local
