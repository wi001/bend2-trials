/-
Join-based treap set operations, exactly as in spec/ALGORITHM.md.
The recursive calls marked parallel there run one side in a `Task.spawn`
while the depth budget `n` is positive.
-/
import OrderedSets.Spec

namespace OrderedSets

/-- lowbias32 -/
def hash32 (x : UInt32) : UInt32 :=
  let x := x ^^^ (x >>> 16)
  let x := x * 0x7feb352d
  let x := x ^^^ (x >>> 15)
  let x := x * 0x846ca68b
  x ^^^ (x >>> 16)

def prio (k : Nat) : UInt32 := hash32 k.toUInt32

/-- node (p1, k1) is above node (p2, k2) -/
@[inline] def above (p1 : UInt32) (k1 : Nat) (p2 : UInt32) (k2 : Nat) : Bool :=
  p1 > p2 || (p1 == p2 && k1 > k2)

/-- `join l k r` with the middle key's priority `pk` passed in -/
def joinP : Tree → Nat → UInt32 → Tree → Tree
  | .leaf, k, pk, .leaf => .node .leaf k pk .leaf
  | l@(.node ll lk lp lr), k, pk, .leaf =>
    if above lp lk pk k then .node ll lk lp (joinP lr k pk .leaf)
    else .node l k pk .leaf
  | .leaf, k, pk, r@(.node rl rk rp rr) =>
    if above rp rk pk k then .node (joinP .leaf k pk rl) rk rp rr
    else .node .leaf k pk r
  | l@(.node ll lk lp lr), k, pk, r@(.node rl rk rp rr) =>
    if above lp lk rp rk then
      if above lp lk pk k then .node ll lk lp (joinP lr k pk r)
      else .node l k pk r
    else
      if above rp rk pk k then .node (joinP l k pk rl) rk rp rr
      else .node l k pk r
termination_by l _ _ r => sizeOf l + sizeOf r

def join (l : Tree) (k : Nat) (r : Tree) : Tree := joinP l k (prio k) r

def join2 : Tree → Tree → Tree
  | .leaf, r => r
  | l@(.node _ _ _ _), .leaf => l
  | l@(.node ll lk lp lr), r@(.node rl rk rp rr) =>
    if above lp lk rp rk then .node ll lk lp (join2 lr r)
    else .node (join2 l rl) rk rp rr
termination_by l r => sizeOf l + sizeOf r

def split (k : Nat) : Tree → Tree × Bool × Tree
  | .leaf => (.leaf, false, .leaf)
  | .node l k' p r =>
    if k < k' then
      let (lo, f, hi) := split k l
      (lo, f, .node hi k' p r)
    else if k' < k then
      let (lo, f, hi) := split k r
      (.node l k' p lo, f, hi)
    else (l, true, r)

/-- depth budget for spawning tasks -/
def parDepth : Nat := 6

/-- While the depth budget `n` is positive, the right recursive call runs in
a new task. The sequential branch creates no task object at all. -/
def unionGo (n : Nat) : Tree → Tree → Tree
  | .leaf, b => b
  | a@(.node _ _ _ _), .leaf => a
  | .node l1 k1 _ r1, b@(.node _ _ _ _) =>
    let (l2, _, r2) := split k1 b
    if n = 0 then join (unionGo 0 l1 l2) k1 (unionGo 0 r1 r2)
    else
      let t := Task.spawn fun _ => unionGo (n - 1) r1 r2
      let L := unionGo (n - 1) l1 l2
      join L k1 t.get

def interGo (n : Nat) : Tree → Tree → Tree
  | .leaf, _ => .leaf
  | .node _ _ _ _, .leaf => .leaf
  | .node l1 k1 _ r1, b@(.node _ _ _ _) =>
    let (l2, f, r2) := split k1 b
    if n = 0 then
      let L := interGo 0 l1 l2
      let R := interGo 0 r1 r2
      if f then join L k1 R else join2 L R
    else
      let t := Task.spawn fun _ => interGo (n - 1) r1 r2
      let L := interGo (n - 1) l1 l2
      if f then join L k1 t.get else join2 L t.get

def diffGo (n : Nat) : Tree → Tree → Tree
  | .leaf, _ => .leaf
  | a@(.node _ _ _ _), .leaf => a
  | .node l1 k1 _ r1, b@(.node _ _ _ _) =>
    let (l2, f, r2) := split k1 b
    if n = 0 then
      let L := diffGo 0 l1 l2
      let R := diffGo 0 r1 r2
      if f then join2 L R else join L k1 R
    else
      let t := Task.spawn fun _ => diffGo (n - 1) r1 r2
      let L := diffGo (n - 1) l1 l2
      if f then join2 L t.get else join L k1 t.get

def union (a b : Tree) : Tree := unionGo parDepth a b
def inter (a b : Tree) : Tree := interGo parDepth a b
def diff (a b : Tree) : Tree := diffGo parDepth a b

def gen (seed : UInt32) (bits : Nat) (i : UInt32) : Nat :=
  (hash32 (2 * i + seed)).toNat % 2 ^ bits

/-- `build` whose top `n` levels run in parallel (and whose unions get depth budget `n`) -/
def buildGo (n : Nat) (seed : UInt32) (bits : Nat) : Nat → UInt32 → Tree
  | 0, lo => let k := gen seed bits lo; .node .leaf k (prio k) .leaf
  | e + 1, lo =>
    let lo' := lo + (2 ^ e).toUInt32
    if n = 0 then unionGo 0 (buildGo 0 seed bits e lo) (buildGo 0 seed bits e lo')
    else
      let t := Task.spawn fun _ => buildGo (n - 1) seed bits e lo'
      let L := buildGo (n - 1) seed bits e lo
      unionGo n L t.get

def build (seed : UInt32) (bits d : Nat) (lo : UInt32) : Tree := buildGo parDepth seed bits d lo

end OrderedSets
