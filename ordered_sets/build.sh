#!/bin/sh
# Builds every benchmark binary that bench/run.py runs.
set -e
cd "$(dirname "$0")"
export BEND_NO_TELEMETRY=1
cc -std=c11 -O3 -o c/treap c/treap.c
cc -std=c11 -O3 -o c/arrays c/arrays.c
cc -std=c11 -O3 -o c/treap_par c/treap_par.c -lpthread
(cd bend && bend bench.bend -o bench && bend bench_shared.bend -o bench_shared && bend bench_layout.bend -o bench_layout && bend bench_mixed.bend -o bench_mixed)
(cd lean && lake build && lake build bench_fresh)
echo "built; run: python3 bench/run.py --D 22 --reps 3 --threads 1 16 18"
