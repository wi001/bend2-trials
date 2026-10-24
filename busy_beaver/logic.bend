# Facts about Bool used by the proofs: refuting False == True, and taking
# conjunctions and disjunctions apart and putting them together.
import Base

def IsTrue(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def exfalso(-G: Type, x: Empty) -> G:
  match x:

def ft_empty(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : IsTrue(_)
  Unit{}

# any goal G holds in a branch where False == True
def absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  exfalso(G, ft_empty(e))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      absurd({False{} == True{} : Bool}, e)
    case True{}:
      {==}

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      absurd({b == True{} : Bool}, e)
    case True{}:
      e

def and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      absurd({Bool.and(False{}, b) == True{} : Bool}, ea)
    case True{}:
      eb

def or_il(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      absurd({Bool.or(False{}, b) == True{} : Bool}, e)
    case True{}:
      {==}

def or_ir(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      {==}

# Four-way conjunctions a && (b && (c && d))
# ------------------------------------------

def c4_1(+a: Bool, -b: Bool, -c: Bool, -d: Bool, e: {Bool.and(a, Bool.and(b, Bool.and(c, d))) == True{} : Bool}) -> {a == True{} : Bool}:
  and_l(a, Bool.and(b, Bool.and(c, d)), e)

def c4_2(+a: Bool, +b: Bool, -c: Bool, -d: Bool, e: {Bool.and(a, Bool.and(b, Bool.and(c, d))) == True{} : Bool}) -> {b == True{} : Bool}:
  and_l(b, Bool.and(c, d), and_r(a, Bool.and(b, Bool.and(c, d)), e))

def c4_3(+a: Bool, +b: Bool, +c: Bool, -d: Bool, e: {Bool.and(a, Bool.and(b, Bool.and(c, d))) == True{} : Bool}) -> {c == True{} : Bool}:
  and_l(c, d, and_r(b, Bool.and(c, d), and_r(a, Bool.and(b, Bool.and(c, d)), e)))

def c4_4(+a: Bool, +b: Bool, +c: Bool, -d: Bool, e: {Bool.and(a, Bool.and(b, Bool.and(c, d))) == True{} : Bool}) -> {d == True{} : Bool}:
  and_r(c, d, and_r(b, Bool.and(c, d), and_r(a, Bool.and(b, Bool.and(c, d)), e)))

def mk4(+a: Bool, +b: Bool, +c: Bool, -d: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool},
    ec: {c == True{} : Bool}, ed: {d == True{} : Bool}) -> {Bool.and(a, Bool.and(b, Bool.and(c, d))) == True{} : Bool}:
  and_i(a, Bool.and(b, Bool.and(c, d)), ea, and_i(b, Bool.and(c, d), eb, and_i(c, d, ec, ed)))
