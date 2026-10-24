/-
The specification shared with the Bend version (bend/spec.bend): trees,
membership and validity. Fixed; implementations import it.
-/
namespace OrderedSets

inductive Tree where
  | leaf
  | node (l : Tree) (k : Nat) (p : UInt32) (r : Tree)
  deriving Inhabited

/-- x occurs somewhere in t, whatever t's order -/
def Tree.elem (x : Nat) : Tree → Bool
  | .leaf => false
  | .node l k _ r => (x == k) || (l.elem x || r.elem x)

/-- every key in t is below b -/
def Tree.allLt (b : Nat) : Tree → Bool
  | .leaf => true
  | .node l k _ r => decide (k < b) && (l.allLt b && r.allLt b)

/-- every key in t is above b -/
def Tree.allGt (b : Nat) : Tree → Bool
  | .leaf => true
  | .node l k _ r => decide (k > b) && (l.allGt b && r.allGt b)

/-- a search tree: at every node, the left keys are below the key and the right keys above it -/
def Tree.valid : Tree → Bool
  | .leaf => true
  | .node l k _ r => l.allLt k && (r.allGt k && (l.valid && r.valid))

end OrderedSets
