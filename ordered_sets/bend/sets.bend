# Join-based treap set operations, written to ../spec/ALGORITHM.md.
#
# A match cannot inspect a computed value, so a recursive def that branches
# on a comparison takes the comparison as a parameter: a phase argument `ph`
# runs each step twice. At 1n+q the step opens its trees, computes the
# comparison and calls itself at q with it (the trees rebuilt unchanged); at
# 0n it acts on the comparison and recurses at 1n on smaller trees. Callers
# start at 1n. No tree is ever shared, so trees carry no reference counts.
import Base
import ./spec.bend as Sp

# Hash and priority
# -----------------

# lowbias32
def hash32(+x: U32) -> U32:
  +a = (x .^. (x >> 16n) : U32)
  +b = (a * 2146121005 : U32)
  +c = (b .^. (b >> 15n) : U32)
  +d = (c * 2221713035 : U32)
  (d .^. (d >> 16n) : U32)

def prio(k: Nat) -> U32:
  hash32(U32.from_nat(k))

# node a (priority pa, key ka) is above node b
def above(+pa: U32, ka: Nat, +pb: U32, kb: Nat) -> Bool:
  Bool.or(U32.is_gt(pa, pb), Bool.and(U32.is_eq(pa, pb), Nat.is_gt(ka, kb)))

# Join
# ----

def cmp_if(c: Bool, x: Cmp, y: Cmp) -> Cmp:
  match c:
    case True{}:
      x
    case False{}:
      y

# the top of join among l's root, k and r's root: LT l's, EQ k, GT r's
# (lk_: l above k, lr_: l above r, rk_: r above k)
def top3(lk_: Bool, lr_: Bool, rk_: Bool) -> Cmp:
  match lk_:
    case True{}:
      cmp_if(lr_, LT{}, GT{})
    case False{}:
      cmp_if(rk_, GT{}, EQ{})

# join(l, k, r) with k's priority pk; c is the top (phase 0n)
def join.go(l: Sp.Tree, r: Sp.Tree, ph: Nat, +k: Nat, +pk: U32, c: Cmp) -> Sp.Tree:
  match l r ph:
    case Sp.Leaf{} Sp.Leaf{} q:
      Sp.Node{Sp.Leaf{}, k, pk, Sp.Leaf{}}
    case Sp.Node{ll, +lk, +lp, lr} Sp.Leaf{} 1n+q:
      join.go(Sp.Node{ll, lk, lp, lr}, Sp.Leaf{}, q, k, pk, cmp_if(above(lp, lk, pk, k), LT{}, EQ{}))
    case Sp.Node{ll, lk, lp, lr} Sp.Leaf{} 0n:
      match c:
        case LT{}:
          Sp.Node{ll, lk, lp, join.go(lr, Sp.Leaf{}, 1n, k, pk, EQ{})}
        case EQ{}:
          Sp.Node{Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Leaf{}}
        case GT{}:
          Sp.Node{Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Leaf{}}
    case Sp.Leaf{} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join.go(Sp.Leaf{}, Sp.Node{rl, rk, rp, rr}, q, k, pk, cmp_if(above(rp, rk, pk, k), GT{}, EQ{}))
    case Sp.Leaf{} Sp.Node{rl, rk, rp, rr} 0n:
      match c:
        case LT{}:
          Sp.Node{Sp.Leaf{}, k, pk, Sp.Node{rl, rk, rp, rr}}
        case EQ{}:
          Sp.Node{Sp.Leaf{}, k, pk, Sp.Node{rl, rk, rp, rr}}
        case GT{}:
          Sp.Node{join.go(Sp.Leaf{}, rl, 1n, k, pk, EQ{}), rk, rp, rr}
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join.go(Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, k, pk,
        top3(above(lp, lk, pk, k), above(lp, lk, rp, rk), above(rp, rk, pk, k)))
    case Sp.Node{ll, lk, lp, lr} Sp.Node{rl, rk, rp, rr} 0n:
      match c:
        case LT{}:
          Sp.Node{ll, lk, lp, join.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{})}
        case EQ{}:
          Sp.Node{Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Node{rl, rk, rp, rr}}
        case GT{}:
          Sp.Node{join.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{}), rk, rp, rr}

# for keys l < k < r
def join(l: Sp.Tree, +k: Nat, r: Sp.Tree) -> Sp.Tree:
  join.go(l, r, 1n, k, prio(k), EQ{})

# join2(l, r); c is "l's root is above r's root" (phase 0n)
def join2.go(l: Sp.Tree, r: Sp.Tree, ph: Nat, c: Bool) -> Sp.Tree:
  match l r ph:
    case Sp.Leaf{} r0 q:
      r0
    case Sp.Node{ll, lk, lp, lr} Sp.Leaf{} q:
      Sp.Node{ll, lk, lp, lr}
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join2.go(Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, above(lp, lk, rp, rk))
    case Sp.Node{ll, lk, lp, lr} Sp.Node{rl, rk, rp, rr} 0n:
      match c:
        case True{}:
          Sp.Node{ll, lk, lp, join2.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, False{})}
        case False{}:
          Sp.Node{join2.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, False{}), rk, rp, rr}

# for keys l < r
def join2(l: Sp.Tree, r: Sp.Tree) -> Sp.Tree:
  join2.go(l, r, 1n, False{})

# Split
# -----

type Split is Data:
  Split{lo: Sp.Tree, found: Bool, hi: Sp.Tree}

def split.lo(s: Split, k2: Nat, p: U32, r: Sp.Tree) -> Split:
  match s:
    case Split{a, f, b}:
      Split{a, f, Sp.Node{b, k2, p, r}}

def split.hi(l: Sp.Tree, k2: Nat, p: U32, s: Split) -> Split:
  match s:
    case Split{a, f, b}:
      Split{Sp.Node{l, k2, p, a}, f, b}

# split(k, t); c is Nat.cmp(k, key of t) (phase 0n)
def split.go(+k: Nat, t: Sp.Tree, ph: Nat, c: Cmp) -> Split:
  match t ph:
    case Sp.Leaf{} q:
      Split{Sp.Leaf{}, False{}, Sp.Leaf{}}
    case Sp.Node{l, +k2, p, r} 1n+q:
      split.go(k, Sp.Node{l, k2, p, r}, q, Nat.cmp(k, k2))
    case Sp.Node{l, k2, p, r} 0n:
      match c:
        case LT{}:
          split.lo(split.go(k, l, 1n, EQ{}), k2, p, r)
        case EQ{}:
          Split{l, True{}, r}
        case GT{}:
          split.hi(l, k2, p, split.go(k, r, 1n, EQ{}))

def split(k: Nat, t: Sp.Tree) -> Split:
  split.go(k, t, 1n, EQ{})

# Union, intersection, difference
# -------------------------------

# the three operations share one recursion, op, which a Mode selects
type Mode is Data:
  U{}
  I{}
  D{}

# op's second argument: b before the split (phase 1n), split(key of a, b) after
type Arg is Data:
  Raw{b: Sp.Tree}
  Cut{s: Split}

# the result when a is a leaf
def leaf_a(m: Mode, x: Arg) -> Sp.Tree:
  match m x:
    case U{} Raw{b}:
      b
    case U{} Cut{s}:
      Sp.Leaf{}
    case I{} x0:
      Sp.Leaf{}
    case D{} x0:
      Sp.Leaf{}

# the result when b is a leaf
def leaf_b(m: Mode, a: Sp.Tree) -> Sp.Tree:
  match m:
    case U{}:
      a
    case I{}:
      Sp.Leaf{}
    case D{}:
      a

# whether a's root key, found or not in b, stays
def keep(m: Mode, f: Bool) -> Bool:
  match m:
    case U{}:
      True{}
    case I{}:
      f
    case D{}:
      Bool.not(f)

def combine(c: Bool, l: Sp.Tree, k: Nat, r: Sp.Tree) -> Sp.Tree:
  match c:
    case True{}:
      join(l, k, r)
    case False{}:
      join2(l, r)

def op(a: Sp.Tree, ph: Nat, +m: Mode, x: Arg) -> Sp.Tree:
  match a ph:
    case Sp.Leaf{} q:
      leaf_a(m, x)
    case Sp.Node{l1, +k1, p1, r1} 1n+q:
      match x:
        case Raw{b}:
          match b:
            case Sp.Leaf{}:
              leaf_b(m, Sp.Node{l1, k1, p1, r1})
            case Sp.Node{bl, bk, bp, br}:
              op(Sp.Node{l1, k1, p1, r1}, q, m, Cut{split(k1, Sp.Node{bl, bk, bp, br})})
        case Cut{s}:
          Sp.Leaf{}
    case Sp.Node{l1, k1, p1, r1} 0n:
      match x:
        case Raw{b}:
          Sp.Leaf{}
        case Cut{s}:
          match s:
            case Split{l2, f, r2}:
              lt rt = op(l1, 1n, m, Raw{l2}) op(r1, 1n, m, Raw{r2})
              combine(keep(m, f), lt, k1, rt)

def union(a: Sp.Tree, b: Sp.Tree) -> Sp.Tree:
  op(a, 1n, U{}, Raw{b})

def inter(a: Sp.Tree, b: Sp.Tree) -> Sp.Tree:
  op(a, 1n, I{}, Raw{b})

def diff(a: Sp.Tree, b: Sp.Tree) -> Sp.Tree:
  op(a, 1n, D{}, Raw{b})

# Building the input sets
# -----------------------

def gen(seed: U32, bits: Nat, i: U32) -> Nat:
  U32.to_nat((hash32((2 * i + seed : U32)) .&. ((1 << bits : U32) - 1 : U32) : U32))

def build(+seed: U32, +bits: Nat, d: Nat, +lo: U32) -> Sp.Tree:
  match d:
    case 0n:
      +k = gen(seed, bits, lo)
      Sp.Node{Sp.Leaf{}, k, prio(k), Sp.Leaf{}}
    case 1n+(+e):
      lt rt = build(seed, bits, e, lo) build(seed, bits, e, (lo + (1 << e : U32) : U32))
      union(lt, rt)
