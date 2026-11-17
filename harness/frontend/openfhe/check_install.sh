#!/usr/bin/env bash
# check_install.sh INSTALL : exit 1, with the rebuild instruction, unless the OpenFHE install prefix
# INSTALL was built with THIS checkout's fhecheck-tracer.h (a stale install writes traces the
# extractors refuse: "trace written by a different fhecheck tracer"). Used by the scripts that
# compile programs against the traced install.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
H="$1/include/openfhe/pke/utils/fhecheck-tracer.h"
[ -f "$H" ] || { echo "$1 has no utils/fhecheck-tracer.h: build the traced OpenFHE with harness/frontend/openfhe/build_openfhe.sh" >&2; exit 1; }
cmp -s "$H" "$HERE/fhecheck-tracer.h" || {
  echo "$1 was built with another fhecheck-tracer.h than harness/frontend/openfhe/fhecheck-tracer.h (stale install;" \
       "its traces would be refused): rebuild OpenFHE with harness/frontend/openfhe/build_openfhe.sh" >&2; exit 1; }
