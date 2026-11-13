#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash docs/findings/gz-next-dangling-after-direct-read/run.sh
# Same builds and probe as ../gz-reset-next-uninitialised/run.sh (patches/*.patch without and
# with 0005, under ASan and UBSan), running dangling.c instead. Before the fix the probe must
# see x.next, pointing into the freed caller buffer, evaluated with n == 0 in gzseek64 and
# gz_skip_have; after the fix it must see no such evaluation. Neither build may get a sanitizer
# report.
here=$(cd "$(dirname "$0")" && pwd)
PROG=dangling PROGDIR=$here WORK=${WORK:-$here/../../../tests/build/gz-next-dangling-after-direct-read} \
  exec bash "$here/../gz-reset-next-uninitialised/run.sh"
