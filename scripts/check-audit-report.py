#!/usr/bin/env python3
"""Compare a completed declaration audit with the reviewed semantic locks."""

from pathlib import Path
import sys

from verification import Rejected, check_locks

try:
    if len(sys.argv) != 2:
        raise Rejected("expected one audit report")
    check_locks(Path(sys.argv[1]))
except (Rejected, OSError, ValueError, KeyError) as error:
    sys.exit(f"REJECTED: {error}")
