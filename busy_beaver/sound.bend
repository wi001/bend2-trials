# Soundness of the decider: a closed set of abstract configurations proves a
# machine never halts. Also determinism of halting times, and check_sound,
# which turns A.check(m, bound, k, fuel) == True into a bound on m's halting.
import Base
import ./tm.bend as TM
import ./abs.bend as A
import ./logic.bend as Lg

# Equality tests
# --------------

def beq_refl(x: Bool) -> {A.beq(x, x) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def beq_sym(x: Bool, y: Bool, e: {A.beq(x, y) == True{} : Bool}) -> {A.beq(y, x) == True{} : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Lg.absurd({A.beq(True{}, False{}) == True{} : Bool}, e)
    case True{} False{}:
      Lg.absurd({A.beq(False{}, True{}) == True{} : Bool}, e)
    case True{} True{}:
      {==}

def beq_trans(x: Bool, y: Bool, z: Bool, e1: {A.beq(x, y) == True{} : Bool}, e2: {A.beq(y, z) == True{} : Bool}) -> {A.beq(x, z) == True{} : Bool}:
  match x y z:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      Lg.absurd({A.beq(False{}, True{}) == True{} : Bool}, e2)
    case False{} True{} z0:
      Lg.absurd({A.beq(False{}, z0) == True{} : Bool}, e1)
    case True{} False{} z0:
      Lg.absurd({A.beq(True{}, z0) == True{} : Bool}, e1)
    case True{} True{} False{}:
      Lg.absurd({A.beq(True{}, False{}) == True{} : Bool}, e2)
    case True{} True{} True{}:
      {==}

def beq_eq(x: Bool, y: Bool, e: {A.beq(x, y) == True{} : Bool}) -> {x == y : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Lg.absurd({False{} == True{} : Bool}, e)
    case True{} False{}:
      Lg.absurd({True{} == False{} : Bool}, e)
    case True{} True{}:
      {==}

def neq_refl(n: Nat) -> {A.neq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      neq_refl(p)

def neq_eq(a: Nat, b: Nat, e: {A.neq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Lg.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      Lg.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %neq_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def neq_trans(a: Nat, b: Nat, c: Nat, e1: {A.neq(a, b) == True{} : Bool}, e2: {A.neq(b, c) == True{} : Bool}) -> {A.neq(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      Lg.absurd({A.neq(0n, 1n+r) == True{} : Bool}, e2)
    case 0n 1n+q c0:
      Lg.absurd({A.neq(0n, c0) == True{} : Bool}, e1)
    case 1n+p 0n c0:
      Lg.absurd({A.neq(1n+p, c0) == True{} : Bool}, e1)
    case 1n+p 1n+q 0n:
      Lg.absurd({A.neq(1n+p, 0n) == True{} : Bool}, e2)
    case 1n+p 1n+q 1n+r:
      neq_trans(p, q, r, e1, e2)

# Sides
# -----

# an all-zero exact part over a closed tail fits only all-zero lists
def all0_fit(+ac: List<&2, Bool>, +xs: List<&2, Bool>, +h1: {A.all0(ac) == True{} : Bool},
    +h2: {A.side_ok(ac, xs, False{}) == True{} : Bool}) -> {A.all0(xs) == True{} : Bool}:
  match ac xs:
    case Nil{} ys:
      h2
    case Con{c, t} Nil{}:
      {==}
    case Con{c, t} Con{x, ys}:
      Lg.and_i(A.beq(x, False{}), A.all0(ys),
        beq_trans(x, c, False{},
          beq_sym(c, x, Lg.and_l(A.beq(c, x), A.side_ok(t, ys, False{}), h2)),
          Lg.and_l(A.beq(c, False{}), A.all0(t), h1)),
        all0_fit(t, ys, Lg.and_r(A.beq(c, False{}), A.all0(t), h1),
          Lg.and_r(A.beq(c, x), A.side_ok(t, ys, False{}), h2)))

# if side (bc, bo) covers side (ac, ao), every list fitting a fits b
def side_sub_ok(+bc: List<&2, Bool>, +ac: List<&2, Bool>, +xs: List<&2, Bool>, +bo: Bool, +ao: Bool,
    +h1: {A.side_sub(bc, ac, bo, ao) == True{} : Bool},
    +h2: {A.side_ok(ac, xs, ao) == True{} : Bool}) -> {A.side_ok(bc, xs, bo) == True{} : Bool}:
  match bc ac xs:
    case Nil{} ac0 xs0:
      match bo ao:
        case True{} ao0:
          {==}
        case False{} True{}:
          Lg.absurd({A.tail_ok(False{}, xs0) == True{} : Bool}, h1)
        case False{} False{}:
          all0_fit(ac0, xs0, h1, h2)
    case Con{c, t} Nil{} Nil{}:
      match ao:
        case True{}:
          Lg.absurd({A.side_ok(Con{c, t}, Nil{}, bo) == True{} : Bool}, h1)
        case False{}:
          Lg.and_i(A.beq(c, False{}), A.side_ok(t, Nil{}, bo),
            Lg.and_l(A.beq(c, False{}), A.side_sub(t, Nil{}, bo, False{}), h1),
            side_sub_ok(t, Nil{}, Nil{}, bo, False{},
              Lg.and_r(A.beq(c, False{}), A.side_sub(t, Nil{}, bo, False{}), h1), {==}))
    case Con{c, t} Nil{} Con{x, ys}:
      match ao:
        case True{}:
          Lg.absurd({A.side_ok(Con{c, t}, Con{x, ys}, bo) == True{} : Bool}, h1)
        case False{}:
          Lg.and_i(A.beq(c, x), A.side_ok(t, ys, bo),
            beq_trans(c, False{}, x,
              Lg.and_l(A.beq(c, False{}), A.side_sub(t, Nil{}, bo, False{}), h1),
              beq_sym(x, False{}, Lg.and_l(A.beq(x, False{}), A.all0(ys), h2))),
            side_sub_ok(t, Nil{}, ys, bo, False{},
              Lg.and_r(A.beq(c, False{}), A.side_sub(t, Nil{}, bo, False{}), h1),
              Lg.and_r(A.beq(x, False{}), A.all0(ys), h2)))
    case Con{c, t} Con{a1, at} Nil{}:
      Lg.and_i(A.beq(c, False{}), A.side_ok(t, Nil{}, bo),
        beq_trans(c, a1, False{},
          Lg.and_l(A.beq(c, a1), A.side_sub(t, at, bo, ao), h1),
          Lg.and_l(A.beq(a1, False{}), A.side_ok(at, Nil{}, ao), h2)),
        side_sub_ok(t, at, Nil{}, bo, ao,
          Lg.and_r(A.beq(c, a1), A.side_sub(t, at, bo, ao), h1),
          Lg.and_r(A.beq(a1, False{}), A.side_ok(at, Nil{}, ao), h2)))
    case Con{c, t} Con{a1, at} Con{x, ys}:
      Lg.and_i(A.beq(c, x), A.side_ok(t, ys, bo),
        beq_trans(c, a1, x,
          Lg.and_l(A.beq(c, a1), A.side_sub(t, at, bo, ao), h1),
          Lg.and_l(A.beq(a1, x), A.side_ok(at, ys, ao), h2)),
        side_sub_ok(t, at, ys, bo, ao,
          Lg.and_r(A.beq(c, a1), A.side_sub(t, at, bo, ao), h1),
          Lg.and_r(A.beq(a1, x), A.side_ok(at, ys, ao), h2)))

# Covering
# --------

def sub_ok(+b: A.Abs, +a: A.Abs, +c: TM.Conf, +h1: {A.sub(b, a) == True{} : Bool},
    +h2: {A.matches(c, a) == True{} : Bool}) -> {A.matches(c, b) == True{} : Bool}:
  match b a c:
    case A.Abs{sb, hb, A.Side{lbc, lbo}, A.Side{rbc, rbo}} A.Abs{sa, ha, A.Side{lac, lao}, A.Side{rac, rao}} TM.Conf{s, TM.Tape{l, h, r}}:
      Lg.mk4(A.neq(s, sb), A.beq(h, hb), A.side_ok(lbc, l, lbo), A.side_ok(rbc, r, rbo),
        neq_trans(s, sa, sb,
          Lg.c4_1(A.neq(s, sa), A.beq(h, ha), A.side_ok(lac, l, lao), A.side_ok(rac, r, rao), h2),
          Lg.c4_1(A.neq(sa, sb), A.beq(ha, hb), A.side_sub(lbc, lac, lbo, lao), A.side_sub(rbc, rac, rbo, rao), h1)),
        beq_trans(h, ha, hb,
          Lg.c4_2(A.neq(s, sa), A.beq(h, ha), A.side_ok(lac, l, lao), A.side_ok(rac, r, rao), h2),
          Lg.c4_2(A.neq(sa, sb), A.beq(ha, hb), A.side_sub(lbc, lac, lbo, lao), A.side_sub(rbc, rac, rbo, rao), h1)),
        side_sub_ok(lbc, lac, l, lbo, lao,
          Lg.c4_3(A.neq(sa, sb), A.beq(ha, hb), A.side_sub(lbc, lac, lbo, lao), A.side_sub(rbc, rac, rbo, rao), h1),
          Lg.c4_3(A.neq(s, sa), A.beq(h, ha), A.side_ok(lac, l, lao), A.side_ok(rac, r, rao), h2)),
        side_sub_ok(rbc, rac, r, rbo, rao,
          Lg.c4_4(A.neq(sa, sb), A.beq(ha, hb), A.side_sub(lbc, lac, lbo, lao), A.side_sub(rbc, rac, rbo, rao), h1),
          Lg.c4_4(A.neq(s, sa), A.beq(h, ha), A.side_ok(lac, l, lao), A.side_ok(rac, r, rao), h2)))

def covered_ok.fin(+b: A.Abs, -rest: List<&2, A.Abs>, +a: A.Abs, +c: TM.Conf, x: Bool,
    ex: {A.sub(b, a) == x : Bool}, hyp: {Bool.or(x, A.covered(rest, a)) == True{} : Bool},
    hm: {A.matches(c, a) == True{} : Bool},
    rec: {A.covered(rest, a) == True{} : Bool} -> {A.matches(c, a) == True{} : Bool} -> {A.in_set(rest, c) == True{} : Bool})
    -> {Bool.or(A.matches(c, b), A.in_set(rest, c)) == True{} : Bool}:
  match x:
    case True{}:
      Lg.or_il(A.matches(c, b), A.in_set(rest, c), sub_ok(b, a, c, ex, hm))
    case False{}:
      Lg.or_ir(A.matches(c, b), A.in_set(rest, c), rec(hyp, hm))

# a configuration fitting a covered abstract configuration fits a member of S
def covered_ok(+S: List<&2, A.Abs>, +a: A.Abs, +c: TM.Conf, hyp: {A.covered(S, a) == True{} : Bool},
    hm: {A.matches(c, a) == True{} : Bool}) -> {A.in_set(S, c) == True{} : Bool}:
  match S:
    case Nil{}:
      Lg.absurd({A.in_set(Nil{}, c) == True{} : Bool}, hyp)
    case Con{b, rest}:
      covered_ok.fin(b, rest, a, c, A.sub(b, a), {==}, hyp, hm, covered_ok(rest, a, c))

# Pushing
# -------

def cons_ok_nil(+c: Bool, +s: A.Side, hc: {A.beq(c, False{}) == True{} : Bool},
    hs: {A.fits(s, Nil{}) == True{} : Bool}) -> {A.fits(A.cons_side(c, s), Nil{}) == True{} : Bool}:
  match s:
    case A.Side{cs, op}:
      Lg.and_i(A.beq(c, False{}), A.side_ok(cs, Nil{}, op), hc, hs)

def cons_ok_con(+c: Bool, +s: A.Side, +y: Bool, +ys: List<&2, Bool>, hc: {A.beq(c, y) == True{} : Bool},
    hs: {A.fits(s, ys) == True{} : Bool}) -> {A.fits(A.cons_side(c, s), Con{y, ys}) == True{} : Bool}:
  match s:
    case A.Side{cs, op}:
      Lg.and_i(A.beq(c, y), A.side_ok(cs, ys, op), hc, hs)

def trunc_ok(+k: Nat, +cs: List<&2, Bool>, +xs: List<&2, Bool>, +op: Bool,
    +h: {A.side_ok(cs, xs, op) == True{} : Bool}) -> {A.fits(A.trunc(k, cs, op), xs) == True{} : Bool}:
  match k cs:
    case 0n Nil{}:
      h
    case 0n Con{x, t}:
      {==}
    case 1n+j Nil{}:
      h
    case 1n+j Con{c, t}:
      match xs:
        case Nil{}:
          cons_ok_nil(c, A.trunc(j, t, op),
            Lg.and_l(A.beq(c, False{}), A.side_ok(t, Nil{}, op), h),
            trunc_ok(j, t, Nil{}, op, Lg.and_r(A.beq(c, False{}), A.side_ok(t, Nil{}, op), h)))
        case Con{y, ys}:
          cons_ok_con(c, A.trunc(j, t, op), y, ys,
            Lg.and_l(A.beq(c, y), A.side_ok(t, ys, op), h),
            trunc_ok(j, t, ys, op, Lg.and_r(A.beq(c, y), A.side_ok(t, ys, op), h)))

# writing w and moving onto xs keeps the pushed side fitting
def push_ok(+k: Nat, +s: A.Side, +w: Bool, +xs: List<&2, Bool>,
    +h: {A.fits(s, xs) == True{} : Bool}) -> {A.fits(A.push(k, w, s), Con{w, xs}) == True{} : Bool}:
  match s:
    case A.Side{cs, op}:
      match cs op:
        case Nil{} False{}:
          match w:
            case False{}:
              h
            case True{}:
              trunc_ok(k, [True{}], Con{True{}, xs}, False{}, h)
        case Nil{} True{}:
          trunc_ok(k, [w], Con{w, xs}, True{},
            Lg.and_i(A.beq(w, w), A.side_ok(Nil{}, xs, True{}), beq_refl(w), {==}))
        case Con{x, t} o:
          trunc_ok(k, Con{w, Con{x, t}}, Con{w, xs}, o,
            Lg.and_i(A.beq(w, w), A.side_ok(Con{x, t}, xs, o), beq_refl(w), h))

# Stepping
# --------

def good(S: List<&2, A.Abs>, st: TM.Step) -> Bool:
  match st:
    case TM.Halted{t}:
      False{}
    case TM.Next{c}:
      A.in_set(S, c)

def fire_l(+S: List<&2, A.Abs>, +n: Nat, +lc: List<&2, Bool>, +lo: Bool, +l: List<&2, Bool>, +P: A.Side,
    +w: Bool, +r: List<&2, Bool>, hcov: {A.cover_l(S, n, lc, lo, P) == True{} : Bool},
    +hl: {A.side_ok(lc, l, lo) == True{} : Bool}, +hp: {A.fits(P, Con{w, r}) == True{} : Bool})
    -> {A.in_set(S, TM.Conf{n, TM.shift.l(TM.pop(l), w, r)}) == True{} : Bool}:
  match lc lo l:
    case Con{x, t} o Nil{}:
      covered_ok(S, A.Abs{n, x, A.Side{t, o}, P}, TM.Conf{n, TM.Tape{Nil{}, False{}, Con{w, r}}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(False{}, x), A.side_ok(t, Nil{}, o), A.fits(P, Con{w, r}),
          neq_refl(n),
          beq_sym(x, False{}, Lg.and_l(A.beq(x, False{}), A.side_ok(t, Nil{}, o), hl)),
          Lg.and_r(A.beq(x, False{}), A.side_ok(t, Nil{}, o), hl),
          hp))
    case Con{x, t} o Con{y, ys}:
      covered_ok(S, A.Abs{n, x, A.Side{t, o}, P}, TM.Conf{n, TM.Tape{ys, y, Con{w, r}}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(y, x), A.side_ok(t, ys, o), A.fits(P, Con{w, r}),
          neq_refl(n),
          beq_sym(x, y, Lg.and_l(A.beq(x, y), A.side_ok(t, ys, o), hl)),
          Lg.and_r(A.beq(x, y), A.side_ok(t, ys, o), hl),
          hp))
    case Nil{} False{} Nil{}:
      covered_ok(S, A.Abs{n, False{}, A.Side{Nil{}, False{}}, P}, TM.Conf{n, TM.Tape{Nil{}, False{}, Con{w, r}}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(False{}, False{}), A.side_ok(Nil{}, Nil{}, False{}), A.fits(P, Con{w, r}),
          neq_refl(n), {==}, {==}, hp))
    case Nil{} False{} Con{y, ys}:
      covered_ok(S, A.Abs{n, False{}, A.Side{Nil{}, False{}}, P}, TM.Conf{n, TM.Tape{ys, y, Con{w, r}}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(y, False{}), A.side_ok(Nil{}, ys, False{}), A.fits(P, Con{w, r}),
          neq_refl(n),
          Lg.and_l(A.beq(y, False{}), A.all0(ys), hl),
          Lg.and_r(A.beq(y, False{}), A.all0(ys), hl),
          hp))
    case Nil{} True{} Nil{}:
      covered_ok(S, A.Abs{n, False{}, A.Side{Nil{}, True{}}, P}, TM.Conf{n, TM.Tape{Nil{}, False{}, Con{w, r}}},
        Lg.and_l(A.covered(S, A.Abs{n, False{}, A.Side{Nil{}, True{}}, P}), A.covered(S, A.Abs{n, True{}, A.Side{Nil{}, True{}}, P}), hcov),
        Lg.mk4(A.neq(n, n), A.beq(False{}, False{}), A.side_ok(Nil{}, Nil{}, True{}), A.fits(P, Con{w, r}),
          neq_refl(n), {==}, {==}, hp))
    case Nil{} True{} Con{y, ys}:
      match y:
        case False{}:
          covered_ok(S, A.Abs{n, False{}, A.Side{Nil{}, True{}}, P}, TM.Conf{n, TM.Tape{ys, False{}, Con{w, r}}},
            Lg.and_l(A.covered(S, A.Abs{n, False{}, A.Side{Nil{}, True{}}, P}), A.covered(S, A.Abs{n, True{}, A.Side{Nil{}, True{}}, P}), hcov),
            Lg.mk4(A.neq(n, n), A.beq(False{}, False{}), A.side_ok(Nil{}, ys, True{}), A.fits(P, Con{w, r}),
              neq_refl(n), {==}, {==}, hp))
        case True{}:
          covered_ok(S, A.Abs{n, True{}, A.Side{Nil{}, True{}}, P}, TM.Conf{n, TM.Tape{ys, True{}, Con{w, r}}},
            Lg.and_r(A.covered(S, A.Abs{n, False{}, A.Side{Nil{}, True{}}, P}), A.covered(S, A.Abs{n, True{}, A.Side{Nil{}, True{}}, P}), hcov),
            Lg.mk4(A.neq(n, n), A.beq(True{}, True{}), A.side_ok(Nil{}, ys, True{}), A.fits(P, Con{w, r}),
              neq_refl(n), {==}, {==}, hp))

def fire_r(+S: List<&2, A.Abs>, +n: Nat, +rc: List<&2, Bool>, +ro: Bool, +r: List<&2, Bool>, +P: A.Side,
    +w: Bool, +l: List<&2, Bool>, hcov: {A.cover_r(S, n, rc, ro, P) == True{} : Bool},
    +hr: {A.side_ok(rc, r, ro) == True{} : Bool}, +hp: {A.fits(P, Con{w, l}) == True{} : Bool})
    -> {A.in_set(S, TM.Conf{n, TM.shift.r(TM.pop(r), w, l)}) == True{} : Bool}:
  match rc ro r:
    case Con{x, t} o Nil{}:
      covered_ok(S, A.Abs{n, x, P, A.Side{t, o}}, TM.Conf{n, TM.Tape{Con{w, l}, False{}, Nil{}}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(False{}, x), A.fits(P, Con{w, l}), A.side_ok(t, Nil{}, o),
          neq_refl(n),
          beq_sym(x, False{}, Lg.and_l(A.beq(x, False{}), A.side_ok(t, Nil{}, o), hr)),
          hp,
          Lg.and_r(A.beq(x, False{}), A.side_ok(t, Nil{}, o), hr)))
    case Con{x, t} o Con{y, ys}:
      covered_ok(S, A.Abs{n, x, P, A.Side{t, o}}, TM.Conf{n, TM.Tape{Con{w, l}, y, ys}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(y, x), A.fits(P, Con{w, l}), A.side_ok(t, ys, o),
          neq_refl(n),
          beq_sym(x, y, Lg.and_l(A.beq(x, y), A.side_ok(t, ys, o), hr)),
          hp,
          Lg.and_r(A.beq(x, y), A.side_ok(t, ys, o), hr)))
    case Nil{} False{} Nil{}:
      covered_ok(S, A.Abs{n, False{}, P, A.Side{Nil{}, False{}}}, TM.Conf{n, TM.Tape{Con{w, l}, False{}, Nil{}}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(False{}, False{}), A.fits(P, Con{w, l}), A.side_ok(Nil{}, Nil{}, False{}),
          neq_refl(n), {==}, hp, {==}))
    case Nil{} False{} Con{y, ys}:
      covered_ok(S, A.Abs{n, False{}, P, A.Side{Nil{}, False{}}}, TM.Conf{n, TM.Tape{Con{w, l}, y, ys}}, hcov,
        Lg.mk4(A.neq(n, n), A.beq(y, False{}), A.fits(P, Con{w, l}), A.side_ok(Nil{}, ys, False{}),
          neq_refl(n),
          Lg.and_l(A.beq(y, False{}), A.all0(ys), hr),
          hp,
          Lg.and_r(A.beq(y, False{}), A.all0(ys), hr)))
    case Nil{} True{} Nil{}:
      covered_ok(S, A.Abs{n, False{}, P, A.Side{Nil{}, True{}}}, TM.Conf{n, TM.Tape{Con{w, l}, False{}, Nil{}}},
        Lg.and_l(A.covered(S, A.Abs{n, False{}, P, A.Side{Nil{}, True{}}}), A.covered(S, A.Abs{n, True{}, P, A.Side{Nil{}, True{}}}), hcov),
        Lg.mk4(A.neq(n, n), A.beq(False{}, False{}), A.fits(P, Con{w, l}), A.side_ok(Nil{}, Nil{}, True{}),
          neq_refl(n), {==}, hp, {==}))
    case Nil{} True{} Con{y, ys}:
      match y:
        case False{}:
          covered_ok(S, A.Abs{n, False{}, P, A.Side{Nil{}, True{}}}, TM.Conf{n, TM.Tape{Con{w, l}, False{}, ys}},
            Lg.and_l(A.covered(S, A.Abs{n, False{}, P, A.Side{Nil{}, True{}}}), A.covered(S, A.Abs{n, True{}, P, A.Side{Nil{}, True{}}}), hcov),
            Lg.mk4(A.neq(n, n), A.beq(False{}, False{}), A.fits(P, Con{w, l}), A.side_ok(Nil{}, ys, True{}),
              neq_refl(n), {==}, hp, {==}))
        case True{}:
          covered_ok(S, A.Abs{n, True{}, P, A.Side{Nil{}, True{}}}, TM.Conf{n, TM.Tape{Con{w, l}, True{}, ys}},
            Lg.and_r(A.covered(S, A.Abs{n, False{}, P, A.Side{Nil{}, True{}}}), A.covered(S, A.Abs{n, True{}, P, A.Side{Nil{}, True{}}}), hcov),
            Lg.mk4(A.neq(n, n), A.beq(True{}, True{}), A.fits(P, Con{w, l}), A.side_ok(Nil{}, ys, True{}),
              neq_refl(n), {==}, hp, {==}))

# a covered rule fired on a fitting tape lands in S
def fire_ok(+ru: TM.Rule, +S: List<&2, A.Abs>, +k: Nat, +ls: A.Side, +rs: A.Side, +l: List<&2, Bool>,
    +r: List<&2, Bool>, h: {A.succ_rule(ru, S, k, ls, rs) == True{} : Bool},
    +hl: {A.fits(ls, l) == True{} : Bool}, +hr: {A.fits(rs, r) == True{} : Bool})
    -> {good(S, TM.fire(ru, l, r)) == True{} : Bool}:
  match ru:
    case TM.Stop{}:
      Lg.absurd({good(S, TM.fire(TM.Stop{}, l, r)) == True{} : Bool}, h)
    case TM.Go{w, d, n}:
      match d:
        case TM.L{}:
          match ls:
            case A.Side{lc, lo}:
              fire_l(S, n, lc, lo, l, A.push(k, w, rs), w, r, h, hl, push_ok(k, rs, w, r, hr))
        case TM.R{}:
          match rs:
            case A.Side{rc, ro}:
              fire_r(S, n, rc, ro, r, A.push(k, w, ls), w, l, h, hr, push_ok(k, ls, w, l, hl))

# one concrete step from a configuration fitting a member of S lands in S
def step_ok(+m: List<&2, TM.Row>, +S: List<&2, A.Abs>, +k: Nat, +a: A.Abs, +c: TM.Conf,
    h1: {A.succ_ok(m, S, k, a) == True{} : Bool}, +h2: {A.matches(c, a) == True{} : Bool})
    -> {good(S, TM.step(m, c)) == True{} : Bool}:
  match a c:
    case A.Abs{sa, ha, ls, rs} TM.Conf{s, TM.Tape{l, h, r}}:
      %Equal.sym(Nat, s, sa, neq_eq(s, sa, Lg.c4_1(A.neq(s, sa), A.beq(h, ha), A.fits(ls, l), A.fits(rs, r), h2))) : {good(S, TM.fire(TM.rule(TM.row(m, _), h), l, r)) == True{} : Bool}
      %Equal.sym(Bool, h, ha, beq_eq(h, ha, Lg.c4_2(A.neq(s, sa), A.beq(h, ha), A.fits(ls, l), A.fits(rs, r), h2))) : {good(S, TM.fire(TM.rule(TM.row(m, sa), _), l, r)) == True{} : Bool}
      fire_ok(TM.rule(TM.row(m, sa), ha), S, k, ls, rs, l, r, h1,
        Lg.c4_3(A.neq(s, sa), A.beq(h, ha), A.fits(ls, l), A.fits(rs, r), h2),
        Lg.c4_4(A.neq(s, sa), A.beq(h, ha), A.fits(ls, l), A.fits(rs, r), h2))

def step_inv.fin(+m: List<&2, TM.Row>, +all: List<&2, A.Abs>, +k: Nat, +b: A.Abs, -rest: List<&2, A.Abs>,
    +c: TM.Conf, x: Bool, ex: {A.matches(c, b) == x : Bool},
    +hcl: {Bool.and(A.succ_ok(m, all, k, b), A.closed(m, all, k, rest)) == True{} : Bool},
    hin: {Bool.or(x, A.in_set(rest, c)) == True{} : Bool},
    rec: {A.closed(m, all, k, rest) == True{} : Bool} -> {A.in_set(rest, c) == True{} : Bool} -> {good(all, TM.step(m, c)) == True{} : Bool})
    -> {good(all, TM.step(m, c)) == True{} : Bool}:
  match x:
    case True{}:
      step_ok(m, all, k, b, c, Lg.and_l(A.succ_ok(m, all, k, b), A.closed(m, all, k, rest), hcl), ex)
    case False{}:
      rec(Lg.and_r(A.succ_ok(m, all, k, b), A.closed(m, all, k, rest), hcl), hin)

# if every member of S has its successors covered by all, a step from a
# configuration fitting a member of S lands in all
def step_inv(+m: List<&2, TM.Row>, +all: List<&2, A.Abs>, +k: Nat, +S: List<&2, A.Abs>, +c: TM.Conf,
    hcl: {A.closed(m, all, k, S) == True{} : Bool}, hin: {A.in_set(S, c) == True{} : Bool})
    -> {good(all, TM.step(m, c)) == True{} : Bool}:
  match S:
    case Nil{}:
      Lg.absurd({good(all, TM.step(m, c)) == True{} : Bool}, hin)
    case Con{b, rest}:
      step_inv.fin(m, all, k, b, rest, c, A.matches(c, b), {==}, hcl, hin, step_inv(m, all, k, rest, c))

# Never halting
# -------------

def run_never(f: Nat, +m: List<&2, TM.Row>, +all: List<&2, A.Abs>, +k: Nat, +st: TM.Step, +n: Nat,
    +hcl: {A.closed(m, all, k, all) == True{} : Bool}, hg: {good(all, st) == True{} : Bool})
    -> {TM.time_of(TM.run(f, m, st, n)) == None{} : Maybe<&2, Nat>}:
  match f st:
    case 0n TM.Halted{t}:
      Lg.absurd({TM.time_of(TM.run(0n, m, TM.Halted{t}, n)) == None{} : Maybe<&2, Nat>}, hg)
    case 0n TM.Next{c}:
      {==}
    case 1n+p TM.Halted{t}:
      Lg.absurd({TM.time_of(TM.run(1n+p, m, TM.Halted{t}, n)) == None{} : Maybe<&2, Nat>}, hg)
    case 1n+p TM.Next{c}:
      run_never(p, m, all, k, TM.step(m, c), 1n+n, hcl, step_inv(m, all, k, all, c, hcl, hg))

# a decided machine never halts
def never_halts(+m: List<&2, TM.Row>, +k: Nat, +S: List<&2, A.Abs>, f: Nat,
    +h: {A.decided(m, k, S) == True{} : Bool}) -> {TM.halt_time(f, m) == None{} : Maybe<&2, Nat>}:
  run_never(f, m, S, k, TM.step(m, TM.blank()), 1n,
    Lg.and_l(A.closed(m, S, k, S), A.covered(S, A.start()), h),
    step_inv(m, S, k, S, TM.blank(), Lg.and_l(A.closed(m, S, k, S), A.covered(S, A.start()), h),
      covered_ok(S, A.start(), TM.blank(), Lg.and_r(A.closed(m, S, k, S), A.covered(S, A.start()), h), {==})))

# Halting at one time only
# ------------------------

# x is no halt, or a halt at step k
def compat(k: Nat, x: Maybe<&2, Nat>) -> Bool:
  match x:
    case None{}:
      True{}
    case Some{j}:
      A.neq(j, k)

# x is a halt at step k
def is_time(k: Nat, x: Maybe<&2, Nat>) -> Bool:
  match x:
    case None{}:
      False{}
    case Some{j}:
      A.neq(j, k)

# a run that halts at step k with some fuel halts at step k or not at all with any other fuel
def run_det(f: Nat, g: Nat, +m: List<&2, TM.Row>, st: TM.Step, +n: Nat, +k: Nat,
    h: {is_time(k, TM.time_of(TM.run(f, m, st, n))) == True{} : Bool})
    -> {compat(k, TM.time_of(TM.run(g, m, st, n))) == True{} : Bool}:
  match f g st:
    case 0n 0n TM.Halted{t}:
      h
    case 0n 0n TM.Next{c}:
      {==}
    case 0n 1n+q TM.Halted{t}:
      h
    case 0n 1n+q TM.Next{c}:
      Lg.absurd({compat(k, TM.time_of(TM.run(1n+q, m, TM.Next{c}, n))) == True{} : Bool}, h)
    case 1n+p 0n TM.Halted{t}:
      h
    case 1n+p 0n TM.Next{c}:
      {==}
    case 1n+p 1n+q TM.Halted{t}:
      h
    case 1n+p 1n+q TM.Next{c}:
      run_det(p, q, m, TM.step(m, c), 1n+n, k, h)

def compat_within(+j: Nat, +bd: Nat, x: Maybe<&2, Nat>, hc: {compat(j, x) == True{} : Bool},
    hj: {Nat.is_le(j, bd) == True{} : Bool}) -> {TM.within(bd, x) == True{} : Bool}:
  match x:
    case None{}:
      {==}
    case Some{i}:
      %Equal.sym(Nat, i, j, neq_eq(i, j, hc)) : {Nat.is_le(_, bd) == True{} : Bool}
      hj

def time_from(+m: List<&2, TM.Row>, +bd: Nat, +j: Nat, et: {TM.halt_time(bd, m) == Some{j} : Maybe<&2, Nat>})
    -> {is_time(j, TM.halt_time(bd, m)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, TM.halt_time(bd, m), Some{j}, et) : {is_time(j, _) == True{} : Bool}
  neq_refl(j)

# Checking a machine bounds its halting
# -------------------------------------

def check_go_sound(+m: List<&2, TM.Row>, +bd: Nat, +k: Nat, +fuel: Nat, +t: Maybe<&2, Nat>,
    et: {TM.halt_time(bd, m) == t : Maybe<&2, Nat>}, h: {A.check.go(m, bd, k, fuel, t) == True{} : Bool},
    +f: Nat) -> {TM.within(bd, TM.halt_time(f, m)) == True{} : Bool}:
  match t:
    case Some{j}:
      compat_within(j, bd, TM.halt_time(f, m),
        run_det(bd, f, m, TM.step(m, TM.blank()), 1n, j, time_from(m, bd, j, et)),
        h)
    case None{}:
      %Equal.sym(Maybe<&2, Nat>, TM.halt_time(f, m), None{}, never_halts(m, k, A.search(fuel, m, k), f, h)) : {TM.within(bd, _) == True{} : Bool}
      {==}

# a checked machine that halts, halts at step bound or earlier
def check_sound(+m: List<&2, TM.Row>, +bd: Nat, +k: Nat, +fuel: Nat, +f: Nat,
    h: {A.check(m, bd, k, fuel) == True{} : Bool}) -> {TM.within(bd, TM.halt_time(f, m)) == True{} : Bool}:
  check_go_sound(m, bd, k, fuel, TM.halt_time(bd, m), {==}, h, f)
