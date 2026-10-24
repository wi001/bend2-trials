# Bend 2 trials

Two experiments testing the claims of [Bend 2](https://github.com/bendlang/bend)
(version 2.0.38, October 2026): that machine-checked laws make code
trustworthy without reading it, that Bend's checker is much faster than other
proof assistants, and that its compiled code runs near C speed with free
parallelism. Measured on an Apple M5 Pro against Coq/Rocq, Lean 4 and C.

The code was written by Claude (Anthropic's model) working with William
Isaksson: `busy_beaver/` by one session, the Bend and Lean implementations in
`ordered_sets/` by two separate agents from the briefs in
`ordered_sets/spec/AGENT_BRIEFS.md`, and the C baselines and harness by the
coordinating session.

## `busy_beaver/`: BB(2) = 6, proven in Bend

A decider that proves Turing machines never halt, its soundness proof, and a
reflective proof over all 6,561 two-state machines. `bend PROOF.bend
--verdict` checks BB(2) = 6 on Bend's Lean-proven kernel in about 2.6 s
(Coq-BB5's BB(2) proof: about 4.5 s). Proof by heavy computation is where Bend
falls behind: certifying the BB(5) champion's 47,176,870 steps took Bend's
checker 7.8 minutes and 22.7 GB against Coq's 6.6 s, and Bend's kernel cannot
do it within its reduction budget. See `busy_beaver/DEVELOPMENT.md`.

## `ordered_sets/`: verified parallel set operations, Bend against Lean and C

A pre-registered comparison on the task where Bend should be strongest:
join-based treap union, intersection and difference, proven to return search
trees with the right members, running in parallel. Bend's proofs pass and
check fast, but it misses the other criteria: its union on one thread is 1.5
times slower than Lean's and 3.1 times slower than the same algorithm in C,
sharing a tree costs a further 2.6 times, it scales 5 to 6 times on 16 to 18
threads, and its agent used 2.7 times the tokens of the Lean agent. In
parallel it is the fastest of the verified implementations. See
`ordered_sets/DEVELOPMENT.md`.

## Reproducing

Requirements: Bend 2.0.38 (`curl -fsSL https://bend-lang.com/install.sh | sh`),
Lean 4.35.0 and Lean 4.34.0 (for Bend's `--verdict` kernel) via elan, a C
compiler, Python 3. The Coq-BB5 timings used Rocq 9.3.0 and Coq-BB5 commit
9142e21.

```sh
cd busy_beaver && bend PROOF.bend --verdict          # BB(2) = 6
cd ordered_sets/bend && bend PROOF.bend --verdict    # Bend laws
cd ordered_sets/lean && lake build && lake env lean Check.lean   # Lean laws
ordered_sets/build.sh && python3 ordered_sets/bench/run.py --D 22 --reps 3 --threads 1 16 18
```

## License

MIT. See `LICENSE`.
