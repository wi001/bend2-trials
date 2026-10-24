# Added by the coordinator for a like-for-like comparison with Lean and C:
# bench.bend, except that A and B are shared by all three operations instead
# of copied for each, so the operations must leave their inputs intact.
#   bend bench_shared.bend -o bench_shared && ./bench_shared [D]
import Base
import ./spec.bend as Sp
import ./sets.bend as S

type Two is Data:
  Two{a: Sp.Tree, b: Sp.Tree}

type Stat is Data:
  Stat{size: Nat, sum: Nat}

def copy.mk(x: Two, +k: Nat, +p: U32, y: Two) -> Two:
  match x y:
    case Two{l1, l2} Two{r1, r2}:
      Two{Sp.Node{l1, k, p, r1}, Sp.Node{l2, k, p, r2}}

# two copies of t
def copy(t: Sp.Tree) -> Two:
  match t:
    case Sp.Leaf{}:
      Two{Sp.Leaf{}, Sp.Leaf{}}
    case Sp.Node{l, k, p, r}:
      x y = copy(l) copy(r)
      copy.mk(x, k, p, y)

def stat.mk(x: Stat, k: Nat, y: Stat) -> Stat:
  match x y:
    case Stat{n1, s1} Stat{n2, s2}:
      Stat{1n+Nat.add(n1, n2), Nat.add(k, Nat.add(s1, s2))}

def stat(t: Sp.Tree) -> Stat:
  match t:
    case Sp.Leaf{}:
      Stat{0n, 0n}
    case Sp.Node{l, k, p, r}:
      x y = stat(l) stat(r)
      stat.mk(x, k, y)

def build2(+d: Nat) -> Two:
  a b = S.build(0, 1n+d, d, 0) S.build(1, 1n+d, d, 0)
  Two{a, b}

def arg_d(args: List<String>) -> Nat:
  match args:
    case Con{prog, rest}:
      match rest:
        case Con{s, more}:
          Maybe.default(&2, Nat, Nat.read(s), 22n)
        case Nil{}:
          22n
    case Nil{}:
      22n

def line(name: String, ms: Nat, st: Stat) -> String:
  match st:
    case Stat{n, s}:
      name ++ "_ms " ++ Nat.show(ms) ++ " size " ++ Nat.show(n) ++ " sum " ++ Nat.show(s)

def ops(+a: Sp.Tree, +b: Sp.Tree) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    u : Sp.Tree = S.union(a, b)
    t1 : Nat <- IO.now()
    IO.print(line("union", Nat.sub(t1, t0), stat(u)))
    t2 : Nat <- IO.now()
    i : Sp.Tree = S.inter(a, b)
    t3 : Nat <- IO.now()
    IO.print(line("inter", Nat.sub(t3, t2), stat(i)))
    t4 : Nat <- IO.now()
    x : Sp.Tree = S.diff(a, b)
    t5 : Nat <- IO.now()
    IO.print(line("diff", Nat.sub(t5, t4), stat(x)))

def report(ms: Nat, sa: Stat, sb: Stat, +a: Sp.Tree, +b: Sp.Tree) -> IO(Unit):
  match sa sb:
    case Stat{na, xa} Stat{nb, xb}:
      do IO<Unit>:
        IO.print("build_ms " ++ Nat.show(ms) ++ " sizes " ++ Nat.show(na) ++ " " ++ Nat.show(nb))
        ops(a, b)

def run.built(ms: Nat, ab: Two) -> IO(Unit):
  match ab:
    case Two{+a, +b}:
      report(ms, stat(a), stat(b), a, b)

def run(+d: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print("D " ++ Nat.show(d))
    t0 : Nat <- IO.now()
    ab : Two = build2(d)
    t1 : Nat <- IO.now()
    run.built(Nat.sub(t1, t0), ab)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(arg_d(args))
