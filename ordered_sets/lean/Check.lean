/-
The laws, restated against the implementation. Fixed: each `example` only
checks if the corresponding theorem in OrderedSets.Proofs has exactly this
statement. Run after `lake build` with `lake env lean Check.lean`.
-/
import OrderedSets.Proofs
open OrderedSets

example : ∀ (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.union a b).valid = true := OrderedSets.union_valid
example : ∀ (x : Nat) (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.union a b).elem x = (a.elem x || b.elem x) := OrderedSets.union_elem
example : ∀ (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.inter a b).valid = true := OrderedSets.inter_valid
example : ∀ (x : Nat) (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.inter a b).elem x = (a.elem x && b.elem x) := OrderedSets.inter_elem
example : ∀ (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.diff a b).valid = true := OrderedSets.diff_valid
example : ∀ (x : Nat) (a b : Tree), a.valid = true → b.valid = true →
    (OrderedSets.diff a b).elem x = (a.elem x && !b.elem x) := OrderedSets.diff_elem
example : ∀ (seed : UInt32) (bits d : Nat) (lo : UInt32),
    (OrderedSets.build seed bits d lo).valid = true := OrderedSets.build_valid

#print axioms OrderedSets.union_valid
#print axioms OrderedSets.union_elem
#print axioms OrderedSets.inter_valid
#print axioms OrderedSets.inter_elem
#print axioms OrderedSets.diff_valid
#print axioms OrderedSets.diff_elem
#print axioms OrderedSets.build_valid
