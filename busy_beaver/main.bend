# Runs the four champions natively and prints their steps, ones and run time.
#   bend main.bend -o bb && ./bb
import Base
import ./tm.bend as TM
import ./champions.bend as C

def show(o: TM.Outcome) -> String:
  match o:
    case TM.Stopped{n, t}:
      "halted after " ++ Nat.show(n) ++ " steps with " ++ Nat.show(TM.ones(t)) ++ " ones"
    case TM.Running{n, c}:
      "still running after " ++ Nat.show(n) ++ " steps"

def report(name: String, o: TM.Outcome, ms: Nat) -> IO(Unit):
  IO.print(name ++ ": " ++ show(o) ++ " (" ++ Nat.show(ms) ++ " ms)")

def timed(name: String, fuel: Nat, m: List<&2, TM.Row>) -> IO(Unit):
  do IO<Unit>:
    start : Nat <- IO.now()
    o : TM.Outcome = TM.exec(fuel, m)
    end : Nat <- IO.now()
    report(name, o, Nat.sub(end, start))

def main() -> IO(Unit):
  do IO<Unit>:
    timed("BB(2) champion", 100n, C.bb2())
    timed("BB(3) champion", 100n, C.bb3())
    timed("BB(4) champion", 1000n, C.bb4())
    timed("BB(5) champion", 50000000n, C.bb5())
