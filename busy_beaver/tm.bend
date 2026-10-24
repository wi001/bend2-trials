# Turing machines with two symbols, run from a blank tape.
#
# Conventions (as in bbchallenge): the machine starts in state 0 (A) on an
# all-zero tape; a Stop rule writes 1 and halts; the halting transition counts
# as a step. Under these conventions BB(2) = 6, BB(3) = 21, BB(4) = 107.
import Base

type Dir is Data:
  L{}
  R{}

# What a state does on reading a symbol: halt, or write, move and switch state.
type Rule is Data:
  Stop{}
  Go{write: Bool, dir: Dir, next: Nat}

# A state's two rules: on reading 0 and on reading 1.
type Row is Data:
  Row{on0: Rule, on1: Rule}

# The tape around the head. Both lists start next to the head; an empty list
# stands for the rest of the tape, all zeros.
type Tape is Data:
  Tape{left: List<&2, Bool>, head: Bool, right: List<&2, Bool>}

type Conf is Data:
  Conf{state: Nat, tape: Tape}

# The result of one transition.
type Step is Data:
  Halted{tape: Tape}
  Next{conf: Conf}

# The result of a bounded run, with the number of transitions taken.
type Outcome is Data:
  Stopped{steps: Nat, tape: Tape}
  Running{steps: Nat, conf: Conf}

# Moving
# ------

def pop(xs: List<&2, Bool>) -> Bool & List<&2, Bool>:
  match xs:
    case Nil{}:
      (False{}, Nil{})
    case Con{h, t}:
      (h, t)

def shift.l(p: Bool & List<&2, Bool>, w: Bool, r: List<&2, Bool>) -> Tape:
  (h, l) = p
  Tape{l, h, w <> r}

def shift.r(p: Bool & List<&2, Bool>, w: Bool, l: List<&2, Bool>) -> Tape:
  (h, r) = p
  Tape{w <> l, h, r}

# write w under the head, then move one cell
def shift(d: Dir, w: Bool, l: List<&2, Bool>, r: List<&2, Bool>) -> Tape:
  match d:
    case L{}:
      shift.l(pop(l), w, r)
    case R{}:
      shift.r(pop(r), w, l)

# Stepping
# --------

# the row for state s; a state past the table's end stops on both symbols
def row(m: List<&2, Row>, s: Nat) -> Row:
  match m s:
    case Nil{} k:
      Row{Stop{}, Stop{}}
    case Con{r, rest} 0n:
      r
    case Con{r, rest} 1n+p:
      row(rest, p)

def rule(r: Row, b: Bool) -> Rule:
  match r b:
    case Row{z, o} False{}:
      z
    case Row{z, o} True{}:
      o

def fire(ru: Rule, l: List<&2, Bool>, r: List<&2, Bool>) -> Step:
  match ru:
    case Stop{}:
      Halted{Tape{l, True{}, r}}
    case Go{w, d, n}:
      Next{Conf{n, shift(d, w, l, r)}}

def step(m: List<&2, Row>, c: Conf) -> Step:
  Conf{s, t} = c
  Tape{l, h, r} = t
  fire(rule(row(m, s), h), l, r)

# Running
# -------

# st is the result of transition number `steps`; fuel bounds the transitions
# still allowed after it
def run(fuel: Nat, +m: List<&2, Row>, st: Step, steps: Nat) -> Outcome:
  match fuel st:
    case 0n Halted{t}:
      Stopped{steps, t}
    case 0n Next{c}:
      Running{steps, c}
    case 1n+p Halted{t}:
      Stopped{steps, t}
    case 1n+p Next{c}:
      run(p, m, step(m, c), 1n+steps)

def blank() -> Conf:
  Conf{0n, Tape{Nil{}, False{}, Nil{}}}

# run m from the blank tape for at most 1 + fuel transitions
def exec(fuel: Nat, +m: List<&2, Row>) -> Outcome:
  run(fuel, m, step(m, blank()), 1n)

def time_of(o: Outcome) -> Maybe<&2, Nat>:
  match o:
    case Stopped{n, t}:
      Some{n}
    case Running{n, c}:
      None{}

# the step at which m halts, if it halts within 1 + fuel transitions
def halt_time(fuel: Nat, m: List<&2, Row>) -> Maybe<&2, Nat>:
  time_of(exec(fuel, m))

# Counting ones
# -------------

def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

def count1(xs: List<&2, Bool>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{b, t}:
      count1(t, bump(b, acc))

def ones(t: Tape) -> Nat:
  Tape{l, h, r} = t
  count1(r, count1(l, bump(h, 0n)))

# Bounds
# ------

# True when x is no halt, or a halt at step bound or earlier
def within(bound: Nat, x: Maybe<&2, Nat>) -> Bool:
  match x:
    case None{}:
      True{}
    case Some{k}:
      Nat.is_le(k, bound)

# Two-state machines
# ------------------
# Every two-state machine is machine2(a0, a1, b0, b1): the rules of state A on
# 0 and 1, then of state B. A Rule2 names its next state with a Bool, so the
# four arguments range over exactly the two-state machines.

type Rule2 is Data:
  Stop2{}
  Go2{write: Bool, dir: Dir, next: Bool}

def state2(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def lift2(x: Rule2) -> Rule:
  match x:
    case Stop2{}:
      Stop{}
    case Go2{w, d, n}:
      Go{w, d, state2(n)}

def machine2(a0: Rule2, a1: Rule2, b0: Rule2, b1: Rule2) -> List<&2, Row>:
  [Row{lift2(a0), lift2(a1)}, Row{lift2(b0), lift2(b1)}]
