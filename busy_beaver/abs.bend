# The decider: abstract configurations that prove a machine never halts.
#
# An abstract configuration fixes the state, the head symbol and, on each side,
# the cells next to the head; past them a side is either all zeros (closed) or
# unknown (open). A set S of them that covers the start, never reaches a Stop
# rule and covers every abstract successor of its members proves the machine
# never halts (sound.bend). Sides keep at most k exact cells: pushing past k
# drops the far cell and opens the side.
import Base
import ./tm.bend as TM

# Equality tests the checker can run
# ----------------------------------

def beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case False{} False{}:
      True{}
    case False{} True{}:
      False{}
    case True{} False{}:
      False{}
    case True{} True{}:
      True{}

def neq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+q:
      False{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      neq(p, q)

def all0(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(beq(x, False{}), all0(t))

# Abstract configurations
# -----------------------

type Side is Data:
  Side{cells: List<&2, Bool>, open: Bool}

type Abs is Data:
  Abs{state: Nat, head: Bool, left: Side, right: Side}

def start() -> Abs:
  Abs{0n, False{}, Side{Nil{}, False{}}, Side{Nil{}, False{}}}

# What a concrete configuration fitting an abstract one means
# -----------------------------------------------------------

def tail_ok(op: Bool, xs: List<&2, Bool>) -> Bool:
  match op:
    case True{}:
      True{}
    case False{}:
      all0(xs)

# xs fits the side with exact cells cs and tail op; an empty xs reads as zeros
def side_ok(cs: List<&2, Bool>, xs: List<&2, Bool>, op: Bool) -> Bool:
  match cs xs:
    case Nil{} ys:
      tail_ok(op, ys)
    case Con{c, t} Nil{}:
      Bool.and(beq(c, False{}), side_ok(t, Nil{}, op))
    case Con{c, t} Con{x, ys}:
      Bool.and(beq(c, x), side_ok(t, ys, op))

def fits(s: Side, xs: List<&2, Bool>) -> Bool:
  Side{cs, op} = s
  side_ok(cs, xs, op)

def matches(c: TM.Conf, a: Abs) -> Bool:
  TM.Conf{s, t} = c
  TM.Tape{l, h, r} = t
  Abs{sa, ha, la, ra} = a
  Bool.and(neq(s, sa), Bool.and(beq(h, ha), Bool.and(fits(la, l), fits(ra, r))))

# some member of S fits c
def in_set(S: List<&2, Abs>, +c: TM.Conf) -> Bool:
  match S:
    case Nil{}:
      False{}
    case Con{b, rest}:
      Bool.or(matches(c, b), in_set(rest, c))

# Covering: b covers a when every configuration fitting a fits b
# --------------------------------------------------------------

def tail_sub(bo: Bool, ao: Bool, xs: List<&2, Bool>) -> Bool:
  match bo:
    case True{}:
      True{}
    case False{}:
      Bool.and(Bool.not(ao), all0(xs))

def side_sub(bc: List<&2, Bool>, ac: List<&2, Bool>, bo: Bool, ao: Bool) -> Bool:
  match bc ac:
    case Nil{} xs:
      tail_sub(bo, ao, xs)
    case Con{c, t} Nil{}:
      match ao:
        case True{}:
          False{}
        case False{}:
          Bool.and(beq(c, False{}), side_sub(t, Nil{}, bo, False{}))
    case Con{c, t} Con{x, xs}:
      Bool.and(beq(c, x), side_sub(t, xs, bo, ao))

def side_covers(b: Side, a: Side) -> Bool:
  Side{bc, bo} = b
  Side{ac, ao} = a
  side_sub(bc, ac, bo, ao)

def sub(b: Abs, a: Abs) -> Bool:
  Abs{sb, hb, lb, rb} = b
  Abs{sa, ha, la, ra} = a
  Bool.and(neq(sa, sb), Bool.and(beq(ha, hb), Bool.and(side_covers(lb, la), side_covers(rb, ra))))

def covered(S: List<&2, Abs>, +a: Abs) -> Bool:
  match S:
    case Nil{}:
      False{}
    case Con{b, rest}:
      Bool.or(sub(b, a), covered(rest, a))

# Pushing a written cell onto a side
# ----------------------------------

def cons_side(x: Bool, s: Side) -> Side:
  Side{cs, op} = s
  Side{x <> cs, op}

# keep at most k exact cells; dropping a cell opens the side
def trunc(k: Nat, cs: List<&2, Bool>, op: Bool) -> Side:
  match k cs:
    case 0n Nil{}:
      Side{Nil{}, op}
    case 0n Con{x, t}:
      Side{Nil{}, True{}}
    case 1n+j Nil{}:
      Side{Nil{}, op}
    case 1n+j Con{x, t}:
      cons_side(x, trunc(j, t, op))

# a zero pushed onto an all-zero side leaves it all zeros
def push.blank(k: Nat, w: Bool) -> Side:
  match w:
    case False{}:
      Side{Nil{}, False{}}
    case True{}:
      trunc(k, [True{}], False{})

def push.go(k: Nat, w: Bool, cs: List<&2, Bool>, op: Bool) -> Side:
  match cs op:
    case Nil{} False{}:
      push.blank(k, w)
    case Nil{} True{}:
      trunc(k, [w], True{})
    case Con{x, t} o:
      trunc(k, w <> x <> t, o)

def push(k: Nat, w: Bool, s: Side) -> Side:
  Side{cs, op} = s
  push.go(k, w, cs, op)

# Successors are covered
# ----------------------

# moving left pops the left side (lc, lo); other is the new right side
def cover_l(+S: List<&2, Abs>, +n: Nat, lc: List<&2, Bool>, lo: Bool, +other: Side) -> Bool:
  match lc lo:
    case Con{x, t} o:
      covered(S, Abs{n, x, Side{t, o}, other})
    case Nil{} False{}:
      covered(S, Abs{n, False{}, Side{Nil{}, False{}}, other})
    case Nil{} True{}:
      Bool.and(covered(S, Abs{n, False{}, Side{Nil{}, True{}}, other}),
        covered(S, Abs{n, True{}, Side{Nil{}, True{}}, other}))

# moving right pops the right side (rc, ro); other is the new left side
def cover_r(+S: List<&2, Abs>, +n: Nat, rc: List<&2, Bool>, ro: Bool, +other: Side) -> Bool:
  match rc ro:
    case Con{x, t} o:
      covered(S, Abs{n, x, other, Side{t, o}})
    case Nil{} False{}:
      covered(S, Abs{n, False{}, other, Side{Nil{}, False{}}})
    case Nil{} True{}:
      Bool.and(covered(S, Abs{n, False{}, other, Side{Nil{}, True{}}}),
        covered(S, Abs{n, True{}, other, Side{Nil{}, True{}}}))

def cover_l.side(+S: List<&2, Abs>, n: Nat, s: Side, other: Side) -> Bool:
  Side{lc, lo} = s
  cover_l(S, n, lc, lo, other)

def cover_r.side(+S: List<&2, Abs>, n: Nat, s: Side, other: Side) -> Bool:
  Side{rc, ro} = s
  cover_r(S, n, rc, ro, other)

def succ_go(+S: List<&2, Abs>, k: Nat, w: Bool, d: TM.Dir, n: Nat, ls: Side, rs: Side) -> Bool:
  match d:
    case TM.L{}:
      cover_l.side(S, n, ls, push(k, w, rs))
    case TM.R{}:
      cover_r.side(S, n, rs, push(k, w, ls))

def succ_rule(ru: TM.Rule, +S: List<&2, Abs>, k: Nat, ls: Side, rs: Side) -> Bool:
  match ru:
    case TM.Stop{}:
      False{}
    case TM.Go{w, d, n}:
      succ_go(S, k, w, d, n, ls, rs)

def succ_ok(+m: List<&2, TM.Row>, +S: List<&2, Abs>, k: Nat, a: Abs) -> Bool:
  Abs{s, h, ls, rs} = a
  succ_rule(TM.rule(TM.row(m, s), h), S, k, ls, rs)

# every member of S has all its successors covered by all
def closed(+m: List<&2, TM.Row>, +all: List<&2, Abs>, +k: Nat, S: List<&2, Abs>) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{a, rest}:
      Bool.and(succ_ok(m, all, k, a), closed(m, all, k, rest))

def decided(+m: List<&2, TM.Row>, k: Nat, +S: List<&2, Abs>) -> Bool:
  Bool.and(closed(m, S, k, S), covered(S, start()))

# Finding S (not trusted: decided checks whatever this returns)
# --------------------------------------------------------------

def succ_l(+n: Nat, lc: List<&2, Bool>, lo: Bool, +other: Side) -> List<&2, Abs>:
  match lc lo:
    case Con{x, t} o:
      [Abs{n, x, Side{t, o}, other}]
    case Nil{} False{}:
      [Abs{n, False{}, Side{Nil{}, False{}}, other}]
    case Nil{} True{}:
      [Abs{n, False{}, Side{Nil{}, True{}}, other}, Abs{n, True{}, Side{Nil{}, True{}}, other}]

def succ_r(+n: Nat, rc: List<&2, Bool>, ro: Bool, +other: Side) -> List<&2, Abs>:
  match rc ro:
    case Con{x, t} o:
      [Abs{n, x, other, Side{t, o}}]
    case Nil{} False{}:
      [Abs{n, False{}, other, Side{Nil{}, False{}}}]
    case Nil{} True{}:
      [Abs{n, False{}, other, Side{Nil{}, True{}}}, Abs{n, True{}, other, Side{Nil{}, True{}}}]

def succs.go(k: Nat, w: Bool, d: TM.Dir, n: Nat, ls: Side, rs: Side) -> List<&2, Abs>:
  match d:
    case TM.L{}:
      Side{lc, lo} = ls
      succ_l(n, lc, lo, push(k, w, rs))
    case TM.R{}:
      Side{rc, ro} = rs
      succ_r(n, rc, ro, push(k, w, ls))

def succs.rule(ru: TM.Rule, k: Nat, ls: Side, rs: Side) -> List<&2, Abs>:
  match ru:
    case TM.Stop{}:
      Nil{}
    case TM.Go{w, d, n}:
      succs.go(k, w, d, n, ls, rs)

def succs(+m: List<&2, TM.Row>, k: Nat, a: Abs) -> List<&2, Abs>:
  Abs{s, h, ls, rs} = a
  succs.rule(TM.rule(TM.row(m, s), h), k, ls, rs)

# the configurations found so far, and those whose successors are still unseen
type Work is Data:
  Work{seen: List<&2, Abs>, todo: List<&2, Abs>}

def add.go(new: Bool, +a: Abs, w: Work) -> Work:
  match new w:
    case True{} Work{seen, todo}:
      Work{a <> seen, a <> todo}
    case False{} v:
      v

def add.one(+a: Abs, w: Work) -> Work:
  Work{+seen, todo} = w
  add.go(Bool.not(covered(seen, a)), a, Work{seen, todo})

def add(xs: List<&2, Abs>, w: Work) -> Work:
  match xs:
    case Nil{}:
      w
    case Con{a, rest}:
      add(rest, add.one(a, w))

# breadth-first search for the abstract configurations reachable from the start
def explore(fuel: Nat, +m: List<&2, TM.Row>, +k: Nat, w: Work) -> List<&2, Abs>:
  match fuel w:
    case 0n Work{seen, todo}:
      seen
    case 1n+p Work{seen, Nil{}}:
      seen
    case 1n+p Work{seen, Con{a, rest}}:
      explore(p, m, k, add(succs(m, k, a), Work{seen, rest}))

def search(fuel: Nat, +m: List<&2, TM.Row>, +k: Nat) -> List<&2, Abs>:
  explore(fuel, m, k, Work{[start()], [start()]})

# Checking one machine
# --------------------
# A machine passes when it halts within 1 + bound steps at step bound or
# earlier, or when the decider, with k exact cells per side and fuel search
# steps, finds a closed set of abstract configurations.

def check.go(+m: List<&2, TM.Row>, bound: Nat, +k: Nat, fuel: Nat, t: Maybe<&2, Nat>) -> Bool:
  match t:
    case Some{j}:
      Nat.is_le(j, bound)
    case None{}:
      decided(m, k, search(fuel, m, k))

def check(+m: List<&2, TM.Row>, +bound: Nat, k: Nat, fuel: Nat) -> Bool:
  check.go(m, bound, k, fuel, TM.halt_time(bound, m))
