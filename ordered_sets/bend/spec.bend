# The specification shared with the Lean version: trees, membership and
# validity. Fixed; implementations import it.
import Base

type Tree is Data:
  Leaf{}
  Node{left: Tree, key: Nat, prio: U32, right: Tree}

# x occurs somewhere in t, whatever t's order
def elem(+x: Nat, t: Tree) -> Bool:
  match t:
    case Leaf{}:
      False{}
    case Node{l, k, p, r}:
      Bool.or(Nat.is_eq(x, k), Bool.or(elem(x, l), elem(x, r)))

# every key in t is below b
def all_lt(t: Tree, +b: Nat) -> Bool:
  match t:
    case Leaf{}:
      True{}
    case Node{l, k, p, r}:
      Bool.and(Nat.is_lt(k, b), Bool.and(all_lt(l, b), all_lt(r, b)))

# every key in t is above b
def all_gt(t: Tree, +b: Nat) -> Bool:
  match t:
    case Leaf{}:
      True{}
    case Node{l, k, p, r}:
      Bool.and(Nat.is_gt(k, b), Bool.and(all_gt(l, b), all_gt(r, b)))

# a search tree: at every node, the left keys are below the key and the right keys above it
def valid(t: Tree) -> Bool:
  match t:
    case Leaf{}:
      True{}
    case Node{+l, +k, p, +r}:
      Bool.and(all_lt(l, k), Bool.and(all_gt(r, k), Bool.and(valid(l), valid(r))))
