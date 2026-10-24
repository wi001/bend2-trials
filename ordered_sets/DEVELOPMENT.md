# Development record

## Why this project

Started 24 October 2026, after `../busy_beaver` showed that Bend's checker is
slow on proofs that compute (Coq ran the BB(5) champion check 70 times
faster; Bend's kernel could not run it at all), while its checker is fast on
large explicit proofs and its compiled code runs near C speed with free
parallelism. This project tests Bend where those strengths should combine:
proofs by structural induction about code that does heavy, evenly split,
parallel work. If Bend does not land on the Pareto frontier of verified and
fast here, it is probably too immature to be used for anything yet; each
criterion it misses shows where it needs work.

## The task

Join-based treap set operations (union, intersection, difference) and a
parallel set builder, specified exactly in `spec/ALGORITHM.md`, so that every
implementation computes the same trees and prints the same sizes and sums.
The laws (`bend/LAWS.bend`, restated in `lean/Check.lean`): each result is a
search tree, and membership in it is the expected Boolean combination of
membership in the inputs; the built sets are search trees.

## Implementations

- Bend: `bend/` (laws and specification fixed; implementation and proofs by an
  agent).
- Lean 4.35.0: `lean/` (specification and `Check.lean` fixed; implementation
  and proofs by a second agent with the same brief).
- C: `c/treap.c` (the same algorithm, unverified, one thread) and
  `c/arrays.c` (sorted arrays and linear merges, the practical speed
  ceiling). Added after the criteria, for information only: `c/treap_par.c`,
  the same treap with the left recursive call on a new thread in the top 8
  levels (cutoffs 4, 6 and 8 tried at D = 22; 8 was fastest).
- `bench/run.py` runs every implementation, takes medians, and marks any
  configuration whose sizes and sums differ from the C treap's.

## Baselines measured before the Bend and Lean versions existed

D = 22, one run each: C treap build 3,340 ms, union 135 ms, inter 120 ms,
diff 120 ms; C sorted arrays union 18 ms; C treap parallel union 37 ms,
build 506 ms. All agree on every size and sum.

## Criteria, fixed before any implementation existed

1. Verified: `bend PROOF.bend --verdict` prints ALL PROOFS CHECK, with no
   unsafe or foreign code behind the laws.
2. Faster than Lean: Bend's union on one thread takes at most half the time
   of Lean's verified union on one thread.
3. Parallel: Bend's union on 16 threads is at least 8 times faster than on one.
4. Near C: Bend's union on one thread takes at most 3 times as long as the
   same algorithm in C.
5. Agent effort: the Bend agent spends at most twice the tokens of the Lean
   agent, and both finish.

Benchmark size D = 22 (two sets from 2^22 draws each), Apple M5 Pro. Union is
the headline operation; intersection, difference and building are reported
too. A missed criterion is a finding about where Bend needs work: 1 about
proofs, 2 to 4 about the compiler and runtime, 5 about writing Bend.

## Fairness notes

- Both agents start fresh, get the same task text, and may read anything in
  `../` (which includes the Busy Beaver proofs, useful Bend examples). The
  Bend brief adds the language lessons recorded in `../busy_beaver`, as a
  project's notes would.
- Lean may use its core tactics (simp, omega, decide, grind); Mathlib is not
  installed. Lean's parallel version uses `Task.spawn` inside the proven
  functions if the agent manages it; otherwise its sequential version runs.
- The fixed files' SHA-256 sums are recorded in `spec/FIXED.sha256`.
- The two briefs are in `spec/AGENT_BRIEFS.md`.

## Results (24 October 2026)

### The two agents

| | Bend | Lean |
|---|---|---|
| Gate | `--verdict`: ALL PROOFS CHECK (0.13 s) | `lake build` + `Check.lean`: standard axioms only (proof files re-check in 0.8 s) |
| Tokens, tool calls, time | 312,897, 49, 31.6 min | 114,331, 32, 9.7 min |
| Lines written | sets 244, proofs 1,383, bench 128 | sets 127, proofs 277, bench 43 |
| Rejections before the final version (self-reported) | 3; the full proof checked on its first complete run | about 5 |

Both kept the fixed files unchanged (checked against `spec/FIXED.sha256`), use
no unsafe, foreign, `sorry`, `native_decide` or extern code, and reproduce the
C treap's sizes and sums exactly. The kernel's statement of each Bend law
(`bend PROOF.bend -o`) uses `spec.valid`, `spec.elem` and `sets.union` etc. as
written. Lean's proofs lean on `fun_induction`, `simp_all` and `grind`; Bend's
proof is written out by hand, much of it generated truth-table rows for small
Bool lemmas.

Design notes from the implementations:
- Bend: union, inter and diff share one recursion `op` selected by a mode.
  Because a recursive def cannot branch on a computed value, `join`, `join2`,
  `split` and `op` take a phase argument: one step computes the comparison and
  calls itself with it, rebuilding the node unchanged; the next acts on it.
  The generated C writes the node back into the same cell and computes the
  comparison with two machine comparisons, so the extra step allocates
  nothing.
  `bench.bend` gives every operation fresh, unshared copies of A and B, made
  outside the timed sections, because a shared tree makes every node carry a
  reference count.
- Lean: the proven functions themselves spawn the right-hand recursive call as
  a `Task` while a depth budget lasts (6 in the benchmark; 0 runs on one
  thread). Its agent found `Task.pure` objects and blocked `Task.get` calls
  costly, which caps its parallel speedup.
- The Lean agent noted that the laws cover order and membership, not balance:
  an unbalanced implementation would pass them. Matching sizes and sums, and
  the timings, are what show both run the specified treap.

Coordinator variants for like-for-like conditions: `bend/bench_shared.bend`
(A and B shared by all three operations, as in Lean and C),
`bend/bench_layout.bend` (fresh copies, then shared: separates memory layout
from sharing) and `lean/MainFresh.lean` (`bench_fresh`: fresh copies per
operation, as in Bend).

### Times at D = 22 (medians of 3 runs, ms; `bench/results-D22.json`)

| | build | union | inter | diff |
|---|---|---|---|---|
| C treap, 1 thread | 3,327 | 136 | 121 | 121 |
| C sorted arrays, 1 thread | 56 | 18 | 17 | 15 |
| C treap, parallel | 488 | 36 | 33 | 33 |
| Bend, 1 thread | 5,760 | 428 | 476 | 486 |
| Bend, 16 threads | 596 | 86 | 95 | 96 |
| Bend, 18 threads | 555 | 73 | 79 | 80 |
| Bend shared, 1 thread | 9,203 | 1,071 | 995 | 1,187 |
| Bend shared, 18 threads | 993 | 175 | 165 | 186 |
| Lean, 1 thread | 6,388 | 293 | 270 | 269 |
| Lean, parallel | 1,178 | 84 | 63 | 194 |
| Lean fresh, 1 thread | 6,352 | 294 | 271 | 273 |
| Lean fresh, parallel | 1,164 | 134 | 53 | 164 |

### The criteria

1. Verified: passed.
2. Faster than Lean (Bend's one-thread union at most half of Lean's): failed.
   Bend 428 ms against Lean 293 ms, 1.46 times slower; with shared inputs
   1,071 ms, 3.7 times slower.
3. Parallel (16 threads at least 8 times faster than one, on union): failed,
   5.0 times (5.9 times on 18 threads). Building scales 9.7 times on 16.
4. Near C (one-thread union at most 3 times the same algorithm in C): failed
   narrowly, 3.1 times; 7.9 times with shared inputs.
5. Agent effort (at most twice Lean's tokens): failed, 2.7 times the tokens,
   3.2 times the time, 5 times the proof lines.

What each miss points at:
- Proofs (5): Bend's proofs are correct and check fast, and the agent got its
  full proof right on the first complete run, but with no automation it wrote
  five times the lines Lean needed.
- Single-thread speed (2, 4): not the phase pattern, which compiles to an
  in-place loop step. Part of the gap to C is the C baseline's arena, which
  never frees: with `malloc` the same C union takes 190 ms, so Bend's 428 ms
  is 2.25 times that and Lean's 293 ms 1.5 times. The rest is not attributed
  here.
- Sharing: keeping the inputs alive, as Lean and C do, costs Bend about 2.1
  times on union (fresh copies consumed: 440 ms; fresh copies kept alive,
  `bench_layout.bend`: 920 ms), and the scattered layout of the original trees
  another 1.2 times (shared originals: 1,100 ms). Lean shows no difference
  (293 against 294 ms). In the generated code a shared node is opened through
  `ctr_take` (an atomic load and reference-count updates) and new nodes are
  allocated instead of reusing the inputs' cells; which of these dominates was
  not isolated.
- Parallelism (3): Bend parallelises well relative to its own single thread
  on building (9.7 times) and better than Lean's tasks; union is partly memory
  bound (C's own parallel treap gains 3.8 times). Among verified
  implementations Bend's parallel build is fastest (555 ms against Lean's
  1,178 ms) and its parallel union slightly faster (73 against 84 ms), but
  parallel C is twice as fast again.

### Rerun on Bend 2.0.39 (25 October 2026)

2.0.39 shipped during the evaluation. From a fresh clone of the published
repository, with 2.0.39 installed beside 2.0.38: the Bend gate passes, and the
Bend timings are within noise of 2.0.38 (one-thread union 442 ms, 16 threads
88, 18 threads 73; shared one thread 1,087). Layout against sharing, one
thread, 3 runs each: fresh copies consumed 438 to 442 ms, fresh copies shared
907 to 930 ms, originals shared 1,092 to 1,123 ms.
