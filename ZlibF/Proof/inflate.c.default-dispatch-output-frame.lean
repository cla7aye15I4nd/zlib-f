import ZlibF.Proof.«inflate.c.construction-output-frame»
import ZlibF.Proof.«inflate.c.stored-mode-output-frame»

/-!
# inflate.c: the per-mode output frames of one dispatch

The exact output frames of the metadata, stored, construction, data, `HEAD`
and terminal modes are in the imported modules. `inflate.c.call-dispatch-frame`
combines them with the gzip header footprints into the frame of one dispatch
of a public call.
-/
