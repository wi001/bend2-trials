# The record holders, in bbchallenge's notation: per state, the rule on 0 then
# on 1, written as symbol, direction, next state (Z halts).
import Base
import ./tm.bend as TM

# 1RB1LB_1LA1RZ: halts after 6 steps with 4 ones
def bb2() -> List<&2, TM.Row>:
  [TM.Row{TM.Go{True{}, TM.R{}, 1n}, TM.Go{True{}, TM.L{}, 1n}},
   TM.Row{TM.Go{True{}, TM.L{}, 0n}, TM.Stop{}}]

# 1RB1RZ_1LB0RC_1LC1LA: halts after 21 steps with 5 ones
def bb3() -> List<&2, TM.Row>:
  [TM.Row{TM.Go{True{}, TM.R{}, 1n}, TM.Stop{}},
   TM.Row{TM.Go{True{}, TM.L{}, 1n}, TM.Go{False{}, TM.R{}, 2n}},
   TM.Row{TM.Go{True{}, TM.L{}, 2n}, TM.Go{True{}, TM.L{}, 0n}}]

# 1RB1LB_1LA0LC_1RZ1LD_1RD0RA: halts after 107 steps with 13 ones
def bb4() -> List<&2, TM.Row>:
  [TM.Row{TM.Go{True{}, TM.R{}, 1n}, TM.Go{True{}, TM.L{}, 1n}},
   TM.Row{TM.Go{True{}, TM.L{}, 0n}, TM.Go{False{}, TM.L{}, 2n}},
   TM.Row{TM.Stop{}, TM.Go{True{}, TM.L{}, 3n}},
   TM.Row{TM.Go{True{}, TM.R{}, 3n}, TM.Go{False{}, TM.R{}, 0n}}]

# 1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA: halts after 47,176,870 steps with 4098 ones
def bb5() -> List<&2, TM.Row>:
  [TM.Row{TM.Go{True{}, TM.R{}, 1n}, TM.Go{True{}, TM.L{}, 2n}},
   TM.Row{TM.Go{True{}, TM.R{}, 2n}, TM.Go{True{}, TM.R{}, 1n}},
   TM.Row{TM.Go{True{}, TM.R{}, 3n}, TM.Go{False{}, TM.L{}, 4n}},
   TM.Row{TM.Go{True{}, TM.L{}, 0n}, TM.Go{True{}, TM.L{}, 3n}},
   TM.Row{TM.Stop{}, TM.Go{False{}, TM.L{}, 0n}}]
