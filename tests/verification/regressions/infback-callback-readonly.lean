import ZlibF.Spec.Public.Back

open C ZlibF.Spec.Public

/-! A call-back of `inflateBack` is any heap function that keeps `ExternalFrame`. Before the
correction, `ExternalFrame own` left everything about the call-back's own blocks free, including the
model's read-only flag `ro`. The window may lie in a call-back's own block (a descriptor that shares
the window's allocation), so a call-back could mark the window read-only, and the next store of the
decoder into the window would fault in the model. C code cannot make memory read-only, so that call-back
does not exist in C: the frame now keeps `ro` of every block that stays live. This regression fails if
the frame loses that clause again. -/
namespace InfbackCallbackReadonlyRegression

theorem external_frame_keeps_ro {own : Nat → Prop} {h after : Heap} (frame : ExternalFrame own h after)
    {b : Nat} (before : h.live b) (still : after.live b) : after.ro b = h.ro b :=
  frame.2.2.2.2 b before still

end InfbackCallbackReadonlyRegression
