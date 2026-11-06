import ZlibF.Zlib.«gzread.c»
import ZlibF.Zlib.«gzwrite.c»

/-!
# gzclose.c — faithful translation

`NO_GZCOMPRESS` is undefined, so the `#ifndef NO_GZCOMPRESS` branch is live.
-/

namespace Zlib.Gzclose
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib

/-- `int ZEXPORT gzclose(gzFile file)` -/
def gzclose (file : GzFilePtr) : G Int32 := do
  -- if (file == NULL) return Z_STREAM_ERROR;
  if file.isNone then return Z_STREAM_ERROR
  -- state = (gz_statep)file;
  let state := castState file
  -- return state->mode == GZ_READ ? gzclose_r(file) : gzclose_w(file);
  if (← ldS state).mode == GZ_READ then Zlib.Gzread.gzclose_r file else Zlib.Gzwrite.gzclose_w file

end Zlib.Gzclose
