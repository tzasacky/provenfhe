#!/usr/bin/env bash
# The algorithm-level comparisons (FHE/Pin/Algo*.lean, check family `algo.*`) are part of
# `openfhe_pin` (`--with-algo`, `--only algo`, `--algo-mutate`, ...): this script only builds that
# executable (`lake build openfhe_pin`, through ../lean/build_lean.sh) and prints its path. The
# separate development executable `algo_pin` and its scratch Lake project no longer exist.
set -euo pipefail
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/../lean/build_lean.sh"
