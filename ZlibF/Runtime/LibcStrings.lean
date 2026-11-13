import ZlibF.Runtime.Space

/-!
# Borrowed external error text

This function-backed table covers every Int32 errno value of the existing
Linux external model. Its entries are not source literals or malloc objects.
Using an entry beyond one immediate error-copy continuation requires a separate
lifetime argument; these views do not model thread or locale transitions.
-/

namespace C

/-- The fixed-locale external error text (glibc 2.43, C locale), without a heap effect. A number outside the
table gives glibc's `"Unknown error N"` (`string/strerror_l.c`); glibc's out-of-memory fallback `"Unknown error"`
is not modelled. -/
def libcErrnoText (e : Int32) : String :=
  if e == 0 then "Success"
  else if e == 2 then "No such file or directory"
  else if e == 4 then "Interrupted system call"
  else if e == 5 then "Input/output error"
  else if e == 9 then "Bad file descriptor"
  else if e == 11 then "Resource temporarily unavailable"
  else if e == 13 then "Permission denied"
  else if e == 17 then "File exists"
  else if e == 21 then "Is a directory"
  else if e == 22 then "Invalid argument"
  else if e == 27 then "File too large"
  else if e == 28 then "No space left on device"
  else if e == 29 then "Illegal seek"
  else if e == 75 then "Value too large for defined data type"
  else s!"Unknown error {e.toInt}"

/-- A function-backed table, not a materialized array with 2^32 entries.
Every Int32 bit pattern has one entry; indices outside that range are invalid. -/
def libcErrnoTable (j : Nat) : Option String :=
  if j < 4294967296 then some (libcErrnoText (UInt32.ofNat j).toInt32) else none

end C
