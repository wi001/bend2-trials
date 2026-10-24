# Development record

## Why this project

Started 24 October 2026, after a session evaluating Bend 2 (2.0.38). Bend's
pitch is that laws plus machine-checked proofs let you trust code without
reading it, and that its checker is orders of magnitude faster than other
proof assistants. An earlier Game of Life project (not in this repository)
did not test that: 512 exhaustive cases already covered its rule, and its
proofs went to Lean. Busy Beaver is the opposite case. Non-halting cannot be observed by
running a machine, only proven, so every non-halting claim needs a proof. It
also has known answers to measure against: BB(2) = 6, BB(3) = 21, BB(4) = 107,
BB(5) = 47,176,870, all proven in Coq by Coq-BB5 (bbchallenge, 2024).

## Conventions

Those of bbchallenge: two symbols, start in state A on an all-zero tape, the
halting transition counts as a step and writes 1. Machines are written in
their notation, e.g. `1RB1LB_1LA1RZ` (per state: symbol, direction, next
state on 0, then on 1; Z halts).

## How BB(2) = 6 is proven

`bb2_champion` (the champion halts at step 6) and `bb2_bound` (no two-state
machine halts after step 6) together give BB(2) = 6. `bb2_bound` is proven by
reflection, in four layers:

1. The decider (`abs.bend`). An abstract configuration fixes the state, the
   head symbol and up to k exact cells on each side; past them a side is all
   zeros (closed) or unknown (open). `decided(m, k, S)` checks that the set S
   covers the start, never meets a Stop rule and covers every abstract
   successor of its members. `search` finds S by breadth-first search; it is
   not trusted, because `decided` checks whatever it returns.
2. Soundness (`sound.bend`, `logic.bend`). `never_halts`: a decided machine's
   run never halts, for any fuel. `run_det`: a machine that halts at step j
   with some fuel halts at step j or not at all with any other fuel.
   `check_sound` combines them: `A.check(m, bound, k, fuel) == True` implies
   that every halting run of m halts at step bound or earlier.
3. Enumeration (`bb2.bend`). `check2` checks one machine (halts by step 6, or
   decided with one exact cell per side). `all_a0(1n)` checks all 9^4 = 6,561
   two-state machines through nested two-way conjunctions.
4. Elimination (`bb2_elim.bend`). Walks those conjunctions back down:
   `all_a0(u) == True` yields `check2(u, a0, a1, b0, b1) == True` for any four
   rules.

`PROOF.bend` proves `all_a0(1n) == True` by computation (the checker runs
all 6,561 checks), picks the given machine's check with the elimination
lemmas and applies `check_sound`. `gen_bb2.py` generates `bb2.bend` and
`bb2_elim.bend`.

## Design decisions

- Symbols are `Bool`, states `Nat`, a machine a list of rows. A state past the
  table's end stops on both symbols.
- The tape is a zipper of two `Bool` lists; an empty list stands for zeros.
- `exec(f, m)` takes at most 1 + f transitions. `halt_time(f, m)` is
  `Some{k}` when m halts at step k within that bound, else `None`.
- `bb2_bound` quantifies over four `Rule2` values. A `Rule2` names its next
  state with a `Bool`, so the quantifier covers exactly the 6,561 two-state
  machines and no validity side-condition is needed.
- `run` takes the previous step's result as an argument, because Bend rejects
  matching on a computed value and rejects mutual recursion. The same two
  rules shape the proofs: a case split on a computed Bool goes through a
  `.fin` helper that takes the value and its defining equation, with the
  recursive call passed in as a function.
- The decider's predicates are Bool functions (`matches`, `side_ok`, `sub`),
  and the soundness lemmas move between them with transitivity lemmas, so
  only one rewrite is needed (state and head symbol in `step_ok`).
- `check2` takes a gate `u` that keeps every check unevaluated until `u` is a
  number. Without it the proven kernel evaluated the closed checks inside the
  elimination lemmas' types and failed with "out of fuel", while Bend's
  TypeScript checker accepted the same file.
- The four rule variables in `bb2_bound` are marked `+` because the proof
  uses each more than once. This changes no meaning.
- `fast.bend` runs long computations in the checker with a binary step counter
  and doubling fuel, because `Nat` is unary in the checker.

## Reviewing laws

These rules for `LAWS.bend` come from Bend issues reproduced on 2.0.38 during
the evaluation:

- Helpers come from imported modules, declared above their use. A helper
  declared below a law can be redefined by `PROOF.bend`, which then changes
  what the law means (bendlang/bend#1236, open).
- Constructors are written qualified. A bare constructor name in a match
  pattern in an importing file silently becomes a catch-all variable
  (bendlang/bend#1328, open).
- Proof content stays out of erased fields. An erased field may hold a junk
  term by design (bendlang/bend#1176).
- `bend PROOF.bend` runs Bend's unproven TypeScript checker. Only
  `bend PROOF.bend --verdict` re-checks with the Lean-proven kernel, so the
  gate is `--verdict`.

Checked for `bb2_bound`: `bend PROOF.bend -o PROOF.bendtt` shows the kernel
certifying `∀ x0..x3 : tm.Rule2, ∀ x4 : Nat, tm.within(6, tm.halt_time(x4,
tm.machine2(x0, x1, x2, x3))) == True`, with `tm.bend`'s own definitions.

## Measurements

24 October 2026, Apple M5 Pro, Bend 2.0.38, Rocq 9.3.0 (Homebrew; Coq-BB5
targets Coq 8.20.1 and built with deprecation warnings only), Lean 4.35.0.

Native runs:
- All four champions reproduce their known steps and ones. The BB(5)
  champion's 47,176,870 steps run in 117–144 ms on one thread.
- `survey.bend`: of the 6,561 two-state machines, 1,165 halt (latest at
  step 6), the decider proves the other 5,396 never halt, none are left. This
  matches the Python prototype exactly.

The BB(2) proof:
- Full gate: `bend PROOF.bend` 1.2 s; `bend PROOF.bend --verdict` 2.6 s,
  ALL PROOFS CHECK. Evaluating `all_a0` alone: 0.75 s (TypeScript checker),
  2.3 s (kernel).
- Mutation tests: claiming BB(2) <= 5 fails inside the reflective computation
  (expected False, observed True); a decider that ignores the 1 an unknown
  tail may hold breaks the soundness proof at that case.

Against Coq-BB5 (single job, per-file compile times summed):
- BB(2): Coq 4.5 s (8.5 s wall with build overhead); Bend 2.6 s.
- BB(3): Coq 4.5 s. BB(4): Coq 64 s, of which 57 s is the decider run in
  `BB4_TNF_Enumeration.v`. Bend has no BB(3) or BB(4) proof yet.
- BB(5) champion's halting time, the same computation in both: Coq
  `vm_compute` 3.4 s plus 3.2 s for the kernel re-check at `Qed`. Bend's
  kernel cannot do it: its budget (`FUEL`, 400 million reductions per check
  in `bendtt.lean`) runs out at 2^20 machine steps. Bend's TypeScript checker
  with `fast.bend`: 2^20 steps 6.5 s (0.5 GB), 2^22 steps 25 s (1.5 GB), full
  run ALL PROOFS CHECK in 468 s with 22.7 GB peak memory, about 70 times
  Coq's 6.6 s. The full-run law and proof are not in `LAWS.bend`, because
  `--verdict` cannot pass them.
- Bend's own checker benchmarks (`bench/checker` in the Bend repository),
  rerun here: `defs_12800` Bend 0.27 s, Lean 38.1 s; `trees_400` Bend 0.76 s,
  Lean 1.23 s. These reproduce Bend's published numbers.

Reading: Bend checks large files of explicit definitions and proofs much
faster than Lean, as advertised. On proof by computation, which Busy Beaver
proofs rely on, it is slower than Coq: on par for BB(2), where fixed costs
dominate, and far slower or out of budget for heavy runs.

## BB(3): what it would take

- The window decider leaves 74 machines of a tree-normal-form enumeration
  undecided, with windows up to 12 cells. An n-gram closed position set
  (NGramCPS) without history leaves 26; with each cell also recording the
  state that last wrote it, 14. The remaining ones are binary counters.
- Coq-BB5 decides BB(3) with loop detection plus NGramCPS over an alphabet
  augmented with the last two transitions (`NGramCPS_decider_impl1 2 2 2
  1600`).
- In Bend this needs a machine model over a general alphabet, a soundness
  proof for NGramCPS and for the history augmentation, and either a checked
  enumeration of all 13^6 (about 4.8 million) three-state machines or a
  proof that tree-normal-form enumeration covers every machine.

## Plan

1. Done: simulator, champions, existence laws for BB(2) to BB(4).
2. Done: `bb2_bound`, so BB(2) = 6, under `--verdict`.
3. BB(3) = 21: the items above.
4. BB(4) = 107, timed against Coq-BB5's 64 s.
5. BB(5) lower bound under `--verdict`: split the run into lemmas of under
   2^20 steps, each stating its end configuration.

## Sources

- bbchallenge, "We have proved BB(5) = 47,176,870", 2 July 2024:
  https://discuss.bbchallenge.org/t/july-2nd-2024-we-have-proved-bb-5-47-176-870/237
- Coq-BB5, which also proves BB(2), BB(3) and BB(4), commit 9142e21:
  https://github.com/ccz181078/Coq-BB5
- The bbchallenge Collaboration's 2025 paper: https://arxiv.org/abs/2509.12337
- Champion descriptions were checked by a throwaway Python simulator before
  being encoded, then reproduced natively by `main.bend`.
