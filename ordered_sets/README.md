# Verified parallel ordered sets: Bend against Lean and C

A pre-registered comparison on the task where Bend should be strongest:
proofs by structural induction about code that does heavy, evenly split,
parallel work. Join-based treap union, intersection and difference
(`spec/ALGORITHM.md`), each proven to return a search tree with the right
members, implemented in Bend and in Lean by two agents with the same brief,
against the same algorithm in C.

- `spec/`: the algorithm, benchmark, fixed-file checksums and the agents' briefs.
- `bend/`: specification and laws (fixed), the agent's `sets.bend`,
  `PROOF.bend`, `bench.bend`; `bench_shared.bend` is a coordinator variant.
- `lean/`: specification and `Check.lean` (fixed), the agent's Lake package;
  `MainFresh.lean` is a coordinator variant.
- `c/`: the same treap in C (one thread and parallel) and sorted arrays.
- `bench/run.py`: runs everything and checks that all answers agree.

```sh
cd bend && bend PROOF.bend --verdict                      # Bend gate
cd lean && lake build && lake env lean Check.lean          # Lean gate
./build.sh && python3 bench/run.py --D 22 --reps 3 --threads 1 16 18   # benchmark
```

Result: Bend's proofs pass, but it misses the other four criteria. See
`DEVELOPMENT.md` for the criteria, every number and what each miss means.
