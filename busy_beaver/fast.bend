# Long runs the checker can evaluate. Nat is unary in the checker, so a run of
# millions of steps uses a binary step counter (Bin) and doubling fuel: runp(k)
# allows 2^k transitions by running 2^(k-1) twice.
import Base
import ./tm.bend as TM

# little-endian binary numbers: B0{r} is 2r, B1{r} is 2r + 1
type Bin is Data:
  BZ{}
  B0{rest: Bin}
  B1{rest: Bin}

def inc(b: Bin) -> Bin:
  match b:
    case BZ{}:
      B1{BZ{}}
    case B0{r}:
      B1{r}
    case B1{r}:
      B0{inc(r)}

# the result of the latest transition, and its number
type Run is Data:
  Run{st: TM.Step, steps: Bin}

def one(+m: List<&2, TM.Row>, s: Run) -> Run:
  match s:
    case Run{TM.Halted{t}, n}:
      Run{TM.Halted{t}, n}
    case Run{TM.Next{c}, n}:
      Run{TM.step(m, c), inc(n)}

# allows 2^k further transitions; matching s forces each half before the next
def runp(+k: Nat, +m: List<&2, TM.Row>, s: Run) -> Run:
  match k s:
    case 0n v:
      one(m, v)
    case 1n+j Run{TM.Halted{t}, n}:
      Run{TM.Halted{t}, n}
    case 1n+j Run{TM.Next{c}, n}:
      runp(j, m, runp(j, m, Run{TM.Next{c}, n}))

def time_bin(r: Run) -> Maybe<&2, Bin>:
  match r:
    case Run{TM.Halted{t}, n}:
      Some{n}
    case Run{TM.Next{c}, n}:
      None{}

# the step at which m halts, if within 1 + 2^k transitions from the blank tape
def halt_bin(k: Nat, +m: List<&2, TM.Row>) -> Maybe<&2, Bin>:
  time_bin(runp(k, m, Run{TM.step(m, TM.blank()), B1{BZ{}}}))
