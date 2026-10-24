/-
Added by the coordinator for a like-for-like comparison with bend/bench.bend:
Main.lean, except that each operation gets fresh, unshared deep copies of A
and B, made outside the timed section (so the operation may reuse their
memory in place, as Bend's does).
-/
import OrderedSets
open OrderedSets

def OrderedSets.Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ _ r => l.size + 1 + r.size

def OrderedSets.Tree.sum : Tree → Nat
  | .leaf => 0
  | .node l k _ r => l.sum + k + r.sum

/-- a fresh copy of every node -/
def OrderedSets.Tree.copy : Tree → Tree
  | .leaf => .leaf
  | .node l k p r => .node l.copy k p r.copy

@[noinline] def touch (a b : Tree) : IO Unit := do
  match a, b with
  | .leaf, .leaf => IO.eprintln "both trees empty"
  | _, _ => pure ()

def main (args : List String) : IO Unit := do
  let D := ((args[0]?).bind String.toNat?).getD 22
  let n := ((args[1]?).bind String.toNat?).getD parDepth
  IO.println s!"D {D}"
  let t0 ← IO.monoMsNow
  let A := buildGo n 0 (D + 1) D 0
  let B := buildGo n 1 (D + 1) D 0
  touch A B
  let t1 ← IO.monoMsNow
  IO.println s!"build_ms {t1 - t0} sizes {A.size} {B.size}"
  let (a, b) := (A.copy, B.copy)
  touch a b
  let t0 ← IO.monoMsNow
  let U := unionGo n a b
  touch U U
  let t1 ← IO.monoMsNow
  IO.println s!"union_ms {t1 - t0} size {U.size} sum {U.sum}"
  let (a, b) := (A.copy, B.copy)
  touch a b
  let t0 ← IO.monoMsNow
  let I := interGo n a b
  touch I I
  let t1 ← IO.monoMsNow
  IO.println s!"inter_ms {t1 - t0} size {I.size} sum {I.sum}"
  let (a, b) := (A.copy, B.copy)
  touch a b
  let t0 ← IO.monoMsNow
  let X := diffGo n a b
  touch X X
  let t1 ← IO.monoMsNow
  IO.println s!"diff_ms {t1 - t0} size {X.size} sum {X.sum}"
