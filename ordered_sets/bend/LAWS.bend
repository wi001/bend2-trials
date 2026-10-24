# The laws. Fixed; PROOF.bend must prove each one. The operations come from
# sets.bend (written to spec/ALGORITHM.md), validity and membership from
# spec.bend.
import Base
import ./spec.bend as Sp
import ./sets.bend as S

# LAW: the union of two search trees is a search tree
law union_valid:
  for +a: Sp.Tree
  for +b: Sp.Tree
  for +va: {Sp.valid(a) == True{} : Bool}
  for +vb: {Sp.valid(b) == True{} : Bool}
  {Sp.valid(S.union(a, b)) == True{} : Bool}

# LAW: x is in the union exactly when it is in a or in b
law union_elem:
  for +x: Nat
  for +a: Sp.Tree
  for +b: Sp.Tree
  for +va: {Sp.valid(a) == True{} : Bool}
  for +vb: {Sp.valid(b) == True{} : Bool}
  {Sp.elem(x, S.union(a, b)) == Bool.or(Sp.elem(x, a), Sp.elem(x, b)) : Bool}

# LAW: the intersection of two search trees is a search tree
law inter_valid:
  for +a: Sp.Tree
  for +b: Sp.Tree
  for +va: {Sp.valid(a) == True{} : Bool}
  for +vb: {Sp.valid(b) == True{} : Bool}
  {Sp.valid(S.inter(a, b)) == True{} : Bool}

# LAW: x is in the intersection exactly when it is in a and in b
law inter_elem:
  for +x: Nat
  for +a: Sp.Tree
  for +b: Sp.Tree
  for +va: {Sp.valid(a) == True{} : Bool}
  for +vb: {Sp.valid(b) == True{} : Bool}
  {Sp.elem(x, S.inter(a, b)) == Bool.and(Sp.elem(x, a), Sp.elem(x, b)) : Bool}

# LAW: the difference of two search trees is a search tree
law diff_valid:
  for +a: Sp.Tree
  for +b: Sp.Tree
  for +va: {Sp.valid(a) == True{} : Bool}
  for +vb: {Sp.valid(b) == True{} : Bool}
  {Sp.valid(S.diff(a, b)) == True{} : Bool}

# LAW: x is in the difference exactly when it is in a and not in b
law diff_elem:
  for +x: Nat
  for +a: Sp.Tree
  for +b: Sp.Tree
  for +va: {Sp.valid(a) == True{} : Bool}
  for +vb: {Sp.valid(b) == True{} : Bool}
  {Sp.elem(x, S.diff(a, b)) == Bool.and(Sp.elem(x, a), Bool.not(Sp.elem(x, b))) : Bool}

# LAW: the benchmark's input sets are search trees
law build_valid:
  for +seed: U32
  for +bits: Nat
  for +d: Nat
  for +lo: U32
  {Sp.valid(S.build(seed, bits, d, lo)) == True{} : Bool}
