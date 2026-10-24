import OrderedSets
open OrderedSets

def OrderedSets.Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ _ r => l.size + 1 + r.size

def OrderedSets.Tree.sum : Tree → Nat
  | .leaf => 0
  | .node l k _ r => l.sum + k + r.sum

/-- inspects both trees, so they are computed before the clock is read again -/
@[noinline] def touch (a b : Tree) : IO Unit := do
  match a, b with
  | .leaf, .leaf => IO.eprintln "both trees empty"
  | _, _ => pure ()

def main (args : List String) : IO Unit := do
  let D := ((args[0]?).bind String.toNat?).getD 22
  -- optional depth budget for spawning tasks; 0 runs everything on one thread
  let n := ((args[1]?).bind String.toNat?).getD parDepth
  IO.println s!"D {D}"
  let t0 ← IO.monoMsNow
  let A := buildGo n 0 (D + 1) D 0
  let B := buildGo n 1 (D + 1) D 0
  touch A B
  let t1 ← IO.monoMsNow
  IO.println s!"build_ms {t1 - t0} sizes {A.size} {B.size}"
  let t0 ← IO.monoMsNow
  let U := unionGo n A B
  touch U U
  let t1 ← IO.monoMsNow
  IO.println s!"union_ms {t1 - t0} size {U.size} sum {U.sum}"
  let t0 ← IO.monoMsNow
  let I := interGo n A B
  touch I I
  let t1 ← IO.monoMsNow
  IO.println s!"inter_ms {t1 - t0} size {I.size} sum {I.sum}"
  let t0 ← IO.monoMsNow
  let X := diffGo n A B
  touch X X
  let t1 ← IO.monoMsNow
  IO.println s!"diff_ms {t1 - t0} size {X.size} sum {X.sum}"
