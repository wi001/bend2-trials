# The proofs.
#
# Each champion law holds by computation: the checker runs the machine and
# both sides reduce to the same value.
#
# bb2_bound by reflection: all_ok has the checker run check2 on all 6,561
# two-state machines; bb2_elim.bend picks out the four given rules' check;
# sound.bend's check_sound turns a passed check into the bound.
import Base
import ./tm.bend as TM
import ./champions.bend as C
import ./bb2.bend as B
import ./bb2_elim.bend as E
import ./sound.bend as Sd
import ./LAWS.bend as Laws

def Laws.bb2_champion():
  {==}

def Laws.bb3_champion():
  {==}

def Laws.bb4_champion():
  {==}

def all_ok() -> {B.all_a0(1n) == True{} : Bool}:
  {==}

def Laws.bb2_bound(a0, a1, b0, b1, f):
  Sd.check_sound(TM.machine2(a0, a1, b0, b1), 6n, 1n, 100n, f,
    E.elim_b1(1n, a0, a1, b0, b1, E.elim_b0(1n, a0, a1, b0, E.elim_a1(1n, a0, a1, E.elim_a0(1n, a0, all_ok())))))
