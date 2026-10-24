# The laws: what this project claims. William reviews every line here;
# PROOF.bend must prove each law.
#
# halt_time(f, m) is the step at which m halts when run from a blank tape,
# if it halts within 1 + f transitions (tm.bend).
import Base
import ./tm.bend as TM
import ./champions.bend as C

# LAW: the BB(2) champion halts at exactly step 6
law bb2_champion:
  {TM.halt_time(10n, C.bb2()) == Some{6n} : Maybe<&2, Nat>}

# LAW: the BB(3) champion halts at exactly step 21
law bb3_champion:
  {TM.halt_time(30n, C.bb3()) == Some{21n} : Maybe<&2, Nat>}

# LAW: the BB(4) champion halts at exactly step 107
law bb4_champion:
  {TM.halt_time(200n, C.bb4()) == Some{107n} : Maybe<&2, Nat>}

# LAW: no two-state machine halts after step 6.
# For every two-state machine and every amount of fuel, a run that halts
# halts at step 6 or earlier. With bb2_champion, this is BB(2) = 6.
law bb2_bound:
  for +a0: TM.Rule2
  for +a1: TM.Rule2
  for +b0: TM.Rule2
  for +b1: TM.Rule2
  for f: Nat
  {TM.within(6n, TM.halt_time(f, TM.machine2(a0, a1, b0, b1))) == True{} : Bool}
