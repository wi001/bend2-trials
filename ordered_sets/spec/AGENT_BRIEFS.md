# The two agent briefs

The Bend and Lean implementations were written by two fresh Claude agents
(Claude Opus 5.5), started at the same time with these prompts. The only edits
here: absolute paths on the original machine are shown relative to this
repository, and one path to a local checkout of Bend's demos is replaced by
its location in Bend's repository.

## Bend

> You are implementing and formally proving a small library in Bend 2 (the dependently typed language with laws and proofs, installed at ~/.bend/bin/bend, version 2.0.38). This is one half of a controlled comparison: another agent is doing the identical task in Lean 4 with the same brief, and your token use and time are part of the measurement, so work efficiently, but correctness comes first.
>
> ## The task
>
> Implement join-based treap set operations exactly as specified in `ordered_sets/spec/ALGORITHM.md` (read it fully first), prove the fixed laws, and write the benchmark program it describes.
>
> Fixed files (do not edit; if you believe a law is wrong or unprovable, stop and report instead of changing anything):
> - `ordered_sets/spec/ALGORITHM.md`: the exact algorithm, input generation and benchmark output format.
> - `ordered_sets/bend/spec.bend`: the Tree type, elem, all_lt, all_gt, valid.
> - `ordered_sets/bend/LAWS.bend`: the seven laws (union, inter and diff each keep validity and have the expected membership; build produces valid trees).
>
> You write, all inside `ordered_sets/bend/` (touch nothing else):
> - sets.bend: union(a, b), inter(a, b), diff(a, b) over Sp.Tree and build(seed: U32, bits: Nat, d: Nat, lo: U32) -> Sp.Tree, with these names and argument orders (LAWS.bend uses them), plus the helpers the algorithm needs (hash32, prio, join, join2, split, gen). Follow ALGORITHM.md exactly, including the "above" order and tie-breaking, so outputs match the other implementations number for number. The two recursive calls in union, inter, diff and build must be Bend parallel calls (`a b = f(x) g(y)`).
> - PROOF.bend: imports LAWS.bend and fills every law (`def Laws.union_valid(a, b, va, vb): ...` and so on), plus any lemma modules you want to import.
> - bench.bend: the benchmark from ALGORITHM.md, D from the first command-line argument (default 22), printing exactly the specified lines.
>
> The gate: `cd ordered_sets/bend && bend PROOF.bend --verdict` must print `ALL PROOFS CHECK`. Nothing the laws depend on may use @unsafe, `def f?`, or foreign effects. Build the benchmark with `bend bench.bend -o bench` and run `./bench 18 +RTS --threads 1 -RTS` and `./bench 18 +RTS --threads 16 -RTS` as a quick check (the full D = 22 runs are done separately; do not run them). Set BEND_NO_TELEMETRY=1.
>
> ## Learning Bend
>
> Run `bend guide` first and read it fully; `bend base` prints the standard library (`bend base Nat` for one name). Working proof idioms are in `busy_beaver/logic.bend` (refuting False == True, Bool and/or lemmas) and `busy_beaver/sound.bend` (case splits on computed Booleans, rewrites with `%e : P`, induction). Bend's own proof demos are in `demos/` of github.com/bendlang/bend (proof_insertion_sort is close to this task).
>
> Lessons from an earlier Bend project on this machine (2.0.38):
> - No mutual recursion, and a def may call only defs above it.
> - A `match` (and a destructuring let like `(a, b) = f(x)` or `Node{..} = f(x)`) cannot scrutinise a computed value. Either give the value its own def that matches on a parameter, or bind it with a plain `+s = f(x)` and read fields through projection defs. For a case split on a computed Bool inside a proof, write a helper that takes the Bool `x`, an equation `{f(..) == x : Bool}` and the recursive call as a function argument, and matches on `x` (see covered_ok.fin and step_inv.fin in sound.bend).
> - A match on an earlier parameter is rejected after matching a later one; order parameters so you match left to right.
> - A variable used more than once needs `+` (on parameters, or in patterns like `Node{+l, k, p, r}`); this works for Data types and for equality proofs.
> - Erased (`-x`) parameters may appear only in types and erased positions.
> - Write runtime code first-order (state passed through named functions, no closures): closure-based code ran 20 to 40 times slower natively.
> - Recursion must visibly shrink: the termination check reads arguments left to right, each passed unchanged until one is a structurally smaller piece of its parameter.
> - `bend X.bend` runs Bend's TypeScript checker; `--verdict` re-checks with the Lean-proven kernel, which has a fixed reduction budget and can report "out of fuel" on terms the TypeScript checker accepts, typically when a type contains a large closed term it decides to evaluate. Keep large closed computations out of types.
> - Nat is unary inside the checker; keep big numeric computations out of proofs.
> - In an importing file, write constructors qualified (`Sp.Leaf{}`); a bare constructor name in a pattern silently becomes a variable.
>
> Priorities and the hash only affect tree shape, never correctness, so the proofs should not need any facts about U32 arithmetic: case-split on the computed priority comparisons and prove both branches.
>
> ## Report
>
> When done (or if you stop), report: whether the gate passes, with its exact output; the D = 18 benchmark output for 1 and 16 threads; line counts of the files you wrote; roughly how many times the checker rejected your work before the final version; anything in the specification you would question; and anything that blocked you. Keep the report under 400 words.

## Lean

> You are implementing and formally proving a small library in Lean 4 (version 4.35.0, core library only; elan and lake are installed; Mathlib is not installed and must not be added). This is one half of a controlled comparison: another agent is doing the identical task in Bend with the same brief, and your token use and time are part of the measurement, so work efficiently, but correctness comes first.
>
> ## The task
>
> Implement join-based treap set operations exactly as specified in `ordered_sets/spec/ALGORITHM.md` (read it fully first), prove the fixed laws, and write the benchmark program it describes.
>
> Fixed files (do not edit; if you believe a law is wrong or unprovable, stop and report instead of changing anything):
> - `ordered_sets/spec/ALGORITHM.md`: the exact algorithm, input generation and benchmark output format.
> - `ordered_sets/lean/OrderedSets/Spec.lean`: the Tree type, elem, allLt, allGt, valid (namespace OrderedSets).
> - `ordered_sets/lean/Check.lean`: the seven laws restated (union, inter and diff each keep validity and have the expected membership; build produces valid trees), plus `#print axioms` for each.
>
> You write, all inside `ordered_sets/lean/` (touch nothing else):
> - A Lake package: lakefile, lean-toolchain (leanprover/lean4:v4.35.0), a library `OrderedSets` whose root imports the modules below, and an executable for the benchmark.
> - OrderedSets/Sets.lean: `OrderedSets.union`, `inter`, `diff : Tree → Tree → Tree` and `OrderedSets.build (seed : UInt32) (bits d : Nat) (lo : UInt32) : Tree`, plus the helpers the algorithm needs (hash32, prio, join, join2, split, gen). Follow ALGORITHM.md exactly, including the "above" order and tie-breaking, so outputs match the other implementations number for number.
> - OrderedSets/Proofs.lean: theorems `OrderedSets.union_valid`, `union_elem`, `inter_valid`, `inter_elem`, `diff_valid`, `diff_elem`, `build_valid`, with exactly the statements in Check.lean.
> - Main.lean: the benchmark from ALGORITHM.md, D from the first command-line argument (default 22), printing exactly the specified lines, timed with a monotonic millisecond clock.
>
> Parallelism: the spec marks the two recursive calls in union, inter, diff and build as parallel. If you can, make the proven functions themselves evaluate one recursive call in a `Task.spawn` (above a depth or size cutoff if you like) so that the benchmarked function is the verified one; Task.spawn/Task.get on pure functions should not obstruct the proofs. If that turns out impractical, keep the proven functions sequential and say so.
>
> The gate: `cd ordered_sets/lean && lake build && lake env lean Check.lean` must succeed with no errors and print, for every theorem, only the standard axioms (propext, Classical.choice, Quot.sound, or none). No `sorry`, no `native_decide`, no `implemented_by` or `@[extern]` on the proven functions. Build the benchmark in release mode (Lake's default compiles C with -O3) and run it with D = 18 as a quick check (the full D = 22 runs are done separately; do not run them).
>
> Priorities and the hash only affect tree shape, never correctness, so the proofs should not need any facts about UInt32 arithmetic: case-split on the computed priority comparisons and prove both branches.
>
> ## Report
>
> When done (or if you stop), report: whether the gate passes, with the axioms output; the exact commands to build and run the benchmark; the D = 18 benchmark output (and whether the benchmarked functions are the proven ones, sequential or parallel); line counts of the files you wrote; roughly how many times Lean rejected your work before the final version; anything in the specification you would question; and anything that blocked you. Keep the report under 400 words.
