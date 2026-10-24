# Counts how the 6,561 two-state machines fare: halted (and the latest halt),
# decided never to halt, or neither. Cross-checks bb2.bend natively.
#   bend survey.bend -o survey && ./survey
import Base
import ./tm.bend as TM
import ./abs.bend as A
import ./bb2.bend as B

def rules2() -> List<&2, TM.Rule2>:
  [TM.Stop2{},
   TM.Go2{False{}, TM.L{}, False{}}, TM.Go2{False{}, TM.L{}, True{}},
   TM.Go2{False{}, TM.R{}, False{}}, TM.Go2{False{}, TM.R{}, True{}},
   TM.Go2{True{}, TM.L{}, False{}}, TM.Go2{True{}, TM.L{}, True{}},
   TM.Go2{True{}, TM.R{}, False{}}, TM.Go2{True{}, TM.R{}, True{}}]

type Tally is Data:
  Tally{halted: Nat, latest: Nat, decided: Nat, open: Nat}

def tally.dec(ok: Bool, h: Nat, l: Nat, d: Nat, o: Nat) -> Tally:
  match ok:
    case True{}:
      Tally{h, l, 1n+d, o}
    case False{}:
      Tally{h, l, d, 1n+o}

def tally.go(t: Maybe<&2, Nat>, +m: List<&2, TM.Row>, acc: Tally) -> Tally:
  match t acc:
    case Some{j} Tally{h, l, d, o}:
      Tally{1n+h, Nat.max(j, l), d, o}
    case None{} Tally{h, l, d, o}:
      tally.dec(A.decided(m, 1n, A.search(100n, m, 1n)), h, l, d, o)

def tally.one(+m: List<&2, TM.Row>, acc: Tally) -> Tally:
  tally.go(TM.halt_time(6n, m), m, acc)

def t_b1(+a0: TM.Rule2, +a1: TM.Rule2, +b0: TM.Rule2, xs: List<&2, TM.Rule2>, acc: Tally) -> Tally:
  match xs:
    case Nil{}:
      acc
    case Con{b1, t}:
      t_b1(a0, a1, b0, t, tally.one(TM.machine2(a0, a1, b0, b1), acc))

def t_b0(+a0: TM.Rule2, +a1: TM.Rule2, xs: List<&2, TM.Rule2>, acc: Tally) -> Tally:
  match xs:
    case Nil{}:
      acc
    case Con{b0, t}:
      t_b0(a0, a1, t, t_b1(a0, a1, b0, rules2(), acc))

def t_a1(+a0: TM.Rule2, xs: List<&2, TM.Rule2>, acc: Tally) -> Tally:
  match xs:
    case Nil{}:
      acc
    case Con{a1, t}:
      t_a1(a0, t, t_b0(a0, a1, rules2(), acc))

def t_a0(xs: List<&2, TM.Rule2>, acc: Tally) -> Tally:
  match xs:
    case Nil{}:
      acc
    case Con{a0, t}:
      t_a0(t, t_a1(a0, rules2(), acc))

def show(t: Tally) -> String:
  match t:
    case Tally{h, l, d, o}:
      "halted " ++ Nat.show(h) ++ " (latest at step " ++ Nat.show(l) ++ "), decided "
        ++ Nat.show(d) ++ ", neither " ++ Nat.show(o)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(t_a0(rules2(), Tally{0n, 0n, 0n, 0n})))
    IO.print("all_a0: " ++ Bool.show(B.all_a0(1n)))
