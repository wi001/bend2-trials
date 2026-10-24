# Proofs of LAWS.bend. Structure: Bool and Nat facts; bounds (All) and
# membership facts about trees; then join, join2, split and op (the shared
# recursion of union, inter and diff), each with a membership lemma, a bound
# lemma (All is preserved) and a validity lemma; then the laws.
import Base
import ./spec.bend as Sp
import ./sets.bend as S
import ./LAWS.bend as Laws

# Bool
# ----

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

def tf_empty(e: {True{} == False{} : Bool}) -> Empty:
  %e : IsTrue(_)
  Unit{}

def absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  exfalso(G, ft_empty(e))

def absurd2(-G: Type, e: {True{} == False{} : Bool}) -> G:
  exfalso(G, tf_empty(e))

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

def c3_1(+a: Bool, -b: Bool, -c: Bool, e: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {a == True{} : Bool}:
  and_l(a, Bool.and(b, c), e)

def c3_2(+a: Bool, +b: Bool, -c: Bool, e: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {b == True{} : Bool}:
  and_l(b, c, and_r(a, Bool.and(b, c), e))

def c3_3(+a: Bool, +b: Bool, -c: Bool, e: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {c == True{} : Bool}:
  and_r(b, c, and_r(a, Bool.and(b, c), e))

def mk3(+a: Bool, +b: Bool, -c: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool},
    ec: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  and_i(a, Bool.and(b, c), ea, and_i(b, c, eb, ec))

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

def or_f(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_t(a: Bool) -> {a == Bool.and(a, True{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or3f(a: Bool, b: Bool, -c: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool},
    hc: {c == False{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == False{} : Bool}:
  match a b:
    case True{} b0:
      absurd2({Bool.or(True{}, Bool.or(b0, c)) == False{} : Bool}, ha)
    case False{} True{}:
      absurd2({Bool.or(False{}, Bool.or(True{}, c)) == False{} : Bool}, hb)
    case False{} False{}:
      hc

# Nat
# ---

def cswap(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def cmp_swap(a: Nat, b: Nat) -> {cswap(Nat.cmp(a, b)) == Nat.cmp(b, a) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cmp_swap(p, q)

def gl_c(c: Cmp) -> {Cmp.is_gt(c) == Cmp.is_lt(cswap(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lg_c(c: Cmp) -> {Cmp.is_lt(c) == Cmp.is_gt(cswap(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def gt_lt(+a: Nat, +b: Nat) -> {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}:
  %cmp_swap(a, b) : {Nat.is_gt(a, b) == Cmp.is_lt(_) : Bool}
  gl_c(Nat.cmp(a, b))

def lt_gt(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == Nat.is_gt(b, a) : Bool}:
  %cmp_swap(a, b) : {Nat.is_lt(a, b) == Cmp.is_gt(_) : Bool}
  lg_c(Nat.cmp(a, b))

def gt_of_lt(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_gt(b, a) == True{} : Bool}:
  %lt_gt(a, b) : {_ == True{} : Bool}
  h

def lt_of_gt(+a: Nat, +b: Nat, h: {Nat.is_gt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  %gt_lt(a, b) : {_ == True{} : Bool}
  h

def lt_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool},
    h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n c0:
      absurd({Nat.is_lt(0n, c0) == True{} : Bool}, h1)
    case 1n+p 0n c0:
      absurd({Nat.is_lt(1n+p, c0) == True{} : Bool}, h1)
    case 0n 1n+q 0n:
      absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      lt_trans(p, q, r, h1, h2)

def gt_trans(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_gt(a, b) == True{} : Bool},
    h2: {Nat.is_gt(b, c) == True{} : Bool}) -> {Nat.is_gt(a, c) == True{} : Bool}:
  gt_of_lt(c, a, lt_trans(c, b, a, lt_of_gt(b, c, h2), lt_of_gt(a, b, h1)))

def cl_ne(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, h)
    case GT{}:
      absurd({Cmp.is_eq(GT{}) == False{} : Bool}, h)

def cg_ne(c: Cmp, h: {Cmp.is_gt(c) == True{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      absurd({Cmp.is_eq(LT{}) == False{} : Bool}, h)
    case EQ{}:
      absurd({Cmp.is_eq(EQ{}) == False{} : Bool}, h)
    case GT{}:
      {==}

def lt_ne(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  cl_ne(Nat.cmp(a, b), h)

def gt_ne(+a: Nat, +b: Nat, h: {Nat.is_gt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  cg_ne(Nat.cmp(a, b), h)

def eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def eq_nat(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %eq_nat(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def lt_of_cmp(+a: Nat, +b: Nat, ec: {LT{} == Nat.cmp(a, b) : Cmp}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  %ec : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def gt_of_cmp(+a: Nat, +b: Nat, ec: {GT{} == Nat.cmp(a, b) : Cmp}) -> {Nat.is_gt(a, b) == True{} : Bool}:
  %ec : {Cmp.is_gt(_) == True{} : Bool}
  {==}

def eq_of_cmp(+a: Nat, +b: Nat, ec: {EQ{} == Nat.cmp(a, b) : Cmp}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %ec : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# Bounds: All(True{}, t, b) is all_lt(t, b), All(False{}, t, b) all_gt(t, b)
# ---------------------------------------------------------------------------

def All(dir: Bool, t: Sp.Tree, b: Nat) -> Bool:
  match dir:
    case True{}:
      Sp.all_lt(t, b)
    case False{}:
      Sp.all_gt(t, b)

def T(dir: Bool, k: Nat, b: Nat) -> Bool:
  match dir:
    case True{}:
      Nat.is_lt(k, b)
    case False{}:
      Nat.is_gt(k, b)

def all_leaf(dir: Bool, -b: Nat) -> {All(dir, Sp.Leaf{}, b) == True{} : Bool}:
  match dir:
    case True{}:
      {==}
    case False{}:
      {==}

def all_k(dir: Bool, +l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, +b: Nat,
    h: {All(dir, Sp.Node{l, k, p, r}, b) == True{} : Bool}) -> {T(dir, k, b) == True{} : Bool}:
  match dir:
    case True{}:
      c3_1(Nat.is_lt(k, b), Sp.all_lt(l, b), Sp.all_lt(r, b), h)
    case False{}:
      c3_1(Nat.is_gt(k, b), Sp.all_gt(l, b), Sp.all_gt(r, b), h)

def all_l(dir: Bool, +l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, +b: Nat,
    h: {All(dir, Sp.Node{l, k, p, r}, b) == True{} : Bool}) -> {All(dir, l, b) == True{} : Bool}:
  match dir:
    case True{}:
      c3_2(Nat.is_lt(k, b), Sp.all_lt(l, b), Sp.all_lt(r, b), h)
    case False{}:
      c3_2(Nat.is_gt(k, b), Sp.all_gt(l, b), Sp.all_gt(r, b), h)

def all_r(dir: Bool, +l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, +b: Nat,
    h: {All(dir, Sp.Node{l, k, p, r}, b) == True{} : Bool}) -> {All(dir, r, b) == True{} : Bool}:
  match dir:
    case True{}:
      c3_3(Nat.is_lt(k, b), Sp.all_lt(l, b), Sp.all_lt(r, b), h)
    case False{}:
      c3_3(Nat.is_gt(k, b), Sp.all_gt(l, b), Sp.all_gt(r, b), h)

def all_mk(dir: Bool, +l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, +b: Nat,
    hk: {T(dir, k, b) == True{} : Bool}, hl: {All(dir, l, b) == True{} : Bool},
    hr: {All(dir, r, b) == True{} : Bool}) -> {All(dir, Sp.Node{l, k, p, r}, b) == True{} : Bool}:
  match dir:
    case True{}:
      mk3(Nat.is_lt(k, b), Sp.all_lt(l, b), Sp.all_lt(r, b), hk, hl, hr)
    case False{}:
      mk3(Nat.is_gt(k, b), Sp.all_gt(l, b), Sp.all_gt(r, b), hk, hl, hr)

def T_trans(dir: Bool, +x: Nat, +k: Nat, +b: Nat, h1: {T(dir, x, k) == True{} : Bool},
    h2: {T(dir, k, b) == True{} : Bool}) -> {T(dir, x, b) == True{} : Bool}:
  match dir:
    case True{}:
      lt_trans(x, k, b, h1, h2)
    case False{}:
      gt_trans(x, k, b, h1, h2)

# a bound on t loosens along T
def mono(+dir: Bool, t: Sp.Tree, +k: Nat, +b: Nat, +h: {All(dir, t, k) == True{} : Bool},
    +hk: {T(dir, k, b) == True{} : Bool}) -> {All(dir, t, b) == True{} : Bool}:
  match t:
    case Sp.Leaf{}:
      all_leaf(dir, b)
    case Sp.Node{+l, +k2, +p, +r}:
      all_mk(dir, l, k2, p, r, b, T_trans(dir, k2, k, b, all_k(dir, l, k2, p, r, k, h), hk),
        mono(dir, l, k, b, all_l(dir, l, k2, p, r, k, h), hk),
        mono(dir, r, k, b, all_r(dir, l, k2, p, r, k, h), hk))

# x beyond b on the other side differs from every key bounded by b
def sep_ne(dir: Bool, +x: Nat, +k: Nat, +b: Nat, hk: {T(dir, k, b) == True{} : Bool},
    hx: {T(Bool.not(dir), x, b) == True{} : Bool}) -> {Nat.is_eq(x, k) == False{} : Bool}:
  match dir:
    case True{}:
      gt_ne(x, k, gt_trans(x, b, k, hx, gt_of_lt(k, b, hk)))
    case False{}:
      lt_ne(x, k, lt_trans(x, b, k, hx, lt_of_gt(k, b, hk)))

def self_ne(dir: Bool, +b: Nat, +k: Nat, hk: {T(dir, k, b) == True{} : Bool}) -> {Nat.is_eq(b, k) == False{} : Bool}:
  match dir:
    case True{}:
      gt_ne(b, k, gt_of_lt(k, b, hk))
    case False{}:
      lt_ne(b, k, lt_of_gt(k, b, hk))

def notin_far(+dir: Bool, +x: Nat, t: Sp.Tree, +b: Nat, +h: {All(dir, t, b) == True{} : Bool},
    +hx: {T(Bool.not(dir), x, b) == True{} : Bool}) -> {Sp.elem(x, t) == False{} : Bool}:
  match t:
    case Sp.Leaf{}:
      {==}
    case Sp.Node{+l, +k, +p, +r}:
      or3f(Nat.is_eq(x, k), Sp.elem(x, l), Sp.elem(x, r),
        sep_ne(dir, x, k, b, all_k(dir, l, k, p, r, b, h), hx),
        notin_far(dir, x, l, b, all_l(dir, l, k, p, r, b, h), hx),
        notin_far(dir, x, r, b, all_r(dir, l, k, p, r, b, h), hx))

def notin_eq(+dir: Bool, +b: Nat, t: Sp.Tree, +h: {All(dir, t, b) == True{} : Bool}) -> {Sp.elem(b, t) == False{} : Bool}:
  match t:
    case Sp.Leaf{}:
      {==}
    case Sp.Node{+l, +k, +p, +r}:
      or3f(Nat.is_eq(b, k), Sp.elem(b, l), Sp.elem(b, r),
        self_ne(dir, b, k, all_k(dir, l, k, p, r, b, h)),
        notin_eq(dir, b, l, all_l(dir, l, k, p, r, b, h)),
        notin_eq(dir, b, r, all_r(dir, l, k, p, r, b, h)))

# the parts of a valid node
def v_lt(+l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, h: {Sp.valid(Sp.Node{l, k, p, r}) == True{} : Bool}) -> {Sp.all_lt(l, k) == True{} : Bool}:
  c4_1(Sp.all_lt(l, k), Sp.all_gt(r, k), Sp.valid(l), Sp.valid(r), h)

def v_gt(+l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, h: {Sp.valid(Sp.Node{l, k, p, r}) == True{} : Bool}) -> {Sp.all_gt(r, k) == True{} : Bool}:
  c4_2(Sp.all_lt(l, k), Sp.all_gt(r, k), Sp.valid(l), Sp.valid(r), h)

def v_l(+l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, h: {Sp.valid(Sp.Node{l, k, p, r}) == True{} : Bool}) -> {Sp.valid(l) == True{} : Bool}:
  c4_3(Sp.all_lt(l, k), Sp.all_gt(r, k), Sp.valid(l), Sp.valid(r), h)

def v_r(+l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, h: {Sp.valid(Sp.Node{l, k, p, r}) == True{} : Bool}) -> {Sp.valid(r) == True{} : Bool}:
  c4_4(Sp.all_lt(l, k), Sp.all_gt(r, k), Sp.valid(l), Sp.valid(r), h)

def v_mk(+l: Sp.Tree, +k: Nat, -p: U32, +r: Sp.Tree, hlk: {Sp.all_lt(l, k) == True{} : Bool},
    hrk: {Sp.all_gt(r, k) == True{} : Bool}, hl: {Sp.valid(l) == True{} : Bool},
    hr: {Sp.valid(r) == True{} : Bool}) -> {Sp.valid(Sp.Node{l, k, p, r}) == True{} : Bool}:
  mk4(Sp.all_lt(l, k), Sp.all_gt(r, k), Sp.valid(l), Sp.valid(r), hlk, hrk, hl, hr)

# Join
# ----

# Bool rearrangements for join's two recursive shapes
def b_tl0(K: Bool, A: Bool, B: Bool, -C: Bool, -R: Bool)
    -> {Bool.or(K, Bool.or(Bool.or(A, Bool.or(B, C)), R)) == Bool.or(A, Bool.or(B, Bool.or(K, Bool.or(C, R)))) : Bool}:
  match K A B:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def b_tl(+K: Bool, +A: Bool, +B: Bool, +C: Bool, +R: Bool, -J: Bool, h: {Bool.or(K, Bool.or(C, R)) == J : Bool})
    -> {Bool.or(K, Bool.or(Bool.or(A, Bool.or(B, C)), R)) == Bool.or(A, Bool.or(B, J)) : Bool}:
  %h : {Bool.or(K, Bool.or(Bool.or(A, Bool.or(B, C)), R)) == Bool.or(A, Bool.or(B, _)) : Bool}
  b_tl0(K, A, B, C, R)

def b_tr0(K: Bool, L: Bool, Q: Bool, D: Bool, -E: Bool)
    -> {Bool.or(K, Bool.or(L, Bool.or(Q, Bool.or(D, E)))) == Bool.or(Q, Bool.or(Bool.or(K, Bool.or(L, D)), E)) : Bool}:
  match K L Q D:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

def b_tr(+K: Bool, +L: Bool, +Q: Bool, +D: Bool, +E: Bool, -J: Bool, h: {Bool.or(K, Bool.or(L, D)) == J : Bool})
    -> {Bool.or(K, Bool.or(L, Bool.or(Q, Bool.or(D, E)))) == Bool.or(Q, Bool.or(J, E)) : Bool}:
  %h : {Bool.or(K, Bool.or(L, Bool.or(Q, Bool.or(D, E)))) == Bool.or(Q, Bool.or(_, E)) : Bool}
  b_tr0(K, L, Q, D, E)

# membership: join.go(l, r, ..) holds the keys of the node (l, k, r)
def join_elem(+x: Nat, l: Sp.Tree, r: Sp.Tree, ph: Nat, +k: Nat, +pk: U32, c: Cmp)
    -> {Sp.elem(x, Sp.Node{l, k, pk, r}) == Sp.elem(x, S.join.go(l, r, ph, k, pk, c)) : Bool}:
  match l r ph:
    case Sp.Leaf{} Sp.Leaf{} q:
      {==}
    case Sp.Node{ll, +lk, +lp, lr} Sp.Leaf{} 1n+q:
      join_elem(x, Sp.Node{ll, lk, lp, lr}, Sp.Leaf{}, q, k, pk, S.cmp_if(S.above(lp, lk, pk, k), LT{}, EQ{}))
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Leaf{} 0n:
      match c:
        case LT{}:
          b_tl(Nat.is_eq(x, k), Nat.is_eq(x, lk), Sp.elem(x, ll), Sp.elem(x, lr), Sp.elem(x, Sp.Leaf{}),
            Sp.elem(x, S.join.go(lr, Sp.Leaf{}, 1n, k, pk, EQ{})), join_elem(x, lr, Sp.Leaf{}, 1n, k, pk, EQ{}))
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case Sp.Leaf{} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join_elem(x, Sp.Leaf{}, Sp.Node{rl, rk, rp, rr}, q, k, pk, S.cmp_if(S.above(rp, rk, pk, k), GT{}, EQ{}))
    case Sp.Leaf{} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          b_tr(Nat.is_eq(x, k), Sp.elem(x, Sp.Leaf{}), Nat.is_eq(x, rk), Sp.elem(x, rl), Sp.elem(x, rr),
            Sp.elem(x, S.join.go(Sp.Leaf{}, rl, 1n, k, pk, EQ{})), join_elem(x, Sp.Leaf{}, rl, 1n, k, pk, EQ{}))
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join_elem(x, Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, k, pk,
        S.top3(S.above(lp, lk, pk, k), S.above(lp, lk, rp, rk), S.above(rp, rk, pk, k)))
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case LT{}:
          b_tl(Nat.is_eq(x, k), Nat.is_eq(x, lk), Sp.elem(x, ll), Sp.elem(x, lr), Sp.elem(x, Sp.Node{rl, rk, rp, rr}),
            Sp.elem(x, S.join.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{})),
            join_elem(x, lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{}))
        case EQ{}:
          {==}
        case GT{}:
          b_tr(Nat.is_eq(x, k), Sp.elem(x, Sp.Node{ll, lk, lp, lr}), Nat.is_eq(x, rk), Sp.elem(x, rl), Sp.elem(x, rr),
            Sp.elem(x, S.join.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{})),
            join_elem(x, Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{}))

# bounds: a bound on l, k and r bounds join.go(l, r, ..)
def join_all(+dir: Bool, l: Sp.Tree, r: Sp.Tree, ph: Nat, +k: Nat, +pk: U32, c: Cmp, +b: Nat,
    +h1: {All(dir, l, b) == True{} : Bool}, +h2: {T(dir, k, b) == True{} : Bool},
    +h3: {All(dir, r, b) == True{} : Bool}) -> {All(dir, S.join.go(l, r, ph, k, pk, c), b) == True{} : Bool}:
  match l r ph:
    case Sp.Leaf{} Sp.Leaf{} q:
      all_mk(dir, Sp.Leaf{}, k, pk, Sp.Leaf{}, b, h2, h1, h3)
    case Sp.Node{ll, +lk, +lp, lr} Sp.Leaf{} 1n+q:
      join_all(dir, Sp.Node{ll, lk, lp, lr}, Sp.Leaf{}, q, k, pk, S.cmp_if(S.above(lp, lk, pk, k), LT{}, EQ{}), b, h1, h2, h3)
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Leaf{} 0n:
      match c:
        case LT{}:
          all_mk(dir, ll, lk, lp, S.join.go(lr, Sp.Leaf{}, 1n, k, pk, EQ{}), b,
            all_k(dir, ll, lk, lp, lr, b, h1), all_l(dir, ll, lk, lp, lr, b, h1),
            join_all(dir, lr, Sp.Leaf{}, 1n, k, pk, EQ{}, b, all_r(dir, ll, lk, lp, lr, b, h1), h2, h3))
        case EQ{}:
          all_mk(dir, Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Leaf{}, b, h2, h1, h3)
        case GT{}:
          all_mk(dir, Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Leaf{}, b, h2, h1, h3)
    case Sp.Leaf{} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join_all(dir, Sp.Leaf{}, Sp.Node{rl, rk, rp, rr}, q, k, pk, S.cmp_if(S.above(rp, rk, pk, k), GT{}, EQ{}), b, h1, h2, h3)
    case Sp.Leaf{} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case LT{}:
          all_mk(dir, Sp.Leaf{}, k, pk, Sp.Node{rl, rk, rp, rr}, b, h2, h1, h3)
        case EQ{}:
          all_mk(dir, Sp.Leaf{}, k, pk, Sp.Node{rl, rk, rp, rr}, b, h2, h1, h3)
        case GT{}:
          all_mk(dir, S.join.go(Sp.Leaf{}, rl, 1n, k, pk, EQ{}), rk, rp, rr, b,
            all_k(dir, rl, rk, rp, rr, b, h3),
            join_all(dir, Sp.Leaf{}, rl, 1n, k, pk, EQ{}, b, h1, h2, all_l(dir, rl, rk, rp, rr, b, h3)),
            all_r(dir, rl, rk, rp, rr, b, h3))
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join_all(dir, Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, k, pk,
        S.top3(S.above(lp, lk, pk, k), S.above(lp, lk, rp, rk), S.above(rp, rk, pk, k)), b, h1, h2, h3)
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case LT{}:
          all_mk(dir, ll, lk, lp, S.join.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{}), b,
            all_k(dir, ll, lk, lp, lr, b, h1), all_l(dir, ll, lk, lp, lr, b, h1),
            join_all(dir, lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{}, b, all_r(dir, ll, lk, lp, lr, b, h1), h2, h3))
        case EQ{}:
          all_mk(dir, Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Node{rl, rk, rp, rr}, b, h2, h1, h3)
        case GT{}:
          all_mk(dir, S.join.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{}), rk, rp, rr, b,
            all_k(dir, rl, rk, rp, rr, b, h3),
            join_all(dir, Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{}, b, h1, h2, all_l(dir, rl, rk, rp, rr, b, h3)),
            all_r(dir, rl, rk, rp, rr, b, h3))

# validity, for keys l < k < r
def join_valid(l: Sp.Tree, r: Sp.Tree, ph: Nat, +k: Nat, +pk: U32, c: Cmp,
    +hl: {Sp.valid(l) == True{} : Bool}, +hr: {Sp.valid(r) == True{} : Bool},
    +hlk: {Sp.all_lt(l, k) == True{} : Bool}, +hrk: {Sp.all_gt(r, k) == True{} : Bool})
    -> {Sp.valid(S.join.go(l, r, ph, k, pk, c)) == True{} : Bool}:
  match l r ph:
    case Sp.Leaf{} Sp.Leaf{} q:
      {==}
    case Sp.Node{ll, +lk, +lp, lr} Sp.Leaf{} 1n+q:
      join_valid(Sp.Node{ll, lk, lp, lr}, Sp.Leaf{}, q, k, pk, S.cmp_if(S.above(lp, lk, pk, k), LT{}, EQ{}), hl, hr, hlk, hrk)
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Leaf{} 0n:
      match c:
        case LT{}:
          v_mk(ll, lk, lp, S.join.go(lr, Sp.Leaf{}, 1n, k, pk, EQ{}),
            v_lt(ll, lk, lp, lr, hl),
            join_all(False{}, lr, Sp.Leaf{}, 1n, k, pk, EQ{}, lk, v_gt(ll, lk, lp, lr, hl),
              gt_of_lt(lk, k, all_k(True{}, ll, lk, lp, lr, k, hlk)), {==}),
            v_l(ll, lk, lp, lr, hl),
            join_valid(lr, Sp.Leaf{}, 1n, k, pk, EQ{}, v_r(ll, lk, lp, lr, hl), hr, all_r(True{}, ll, lk, lp, lr, k, hlk), hrk))
        case EQ{}:
          v_mk(Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Leaf{}, hlk, hrk, hl, hr)
        case GT{}:
          v_mk(Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Leaf{}, hlk, hrk, hl, hr)
    case Sp.Leaf{} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join_valid(Sp.Leaf{}, Sp.Node{rl, rk, rp, rr}, q, k, pk, S.cmp_if(S.above(rp, rk, pk, k), GT{}, EQ{}), hl, hr, hlk, hrk)
    case Sp.Leaf{} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case LT{}:
          v_mk(Sp.Leaf{}, k, pk, Sp.Node{rl, rk, rp, rr}, hlk, hrk, hl, hr)
        case EQ{}:
          v_mk(Sp.Leaf{}, k, pk, Sp.Node{rl, rk, rp, rr}, hlk, hrk, hl, hr)
        case GT{}:
          v_mk(S.join.go(Sp.Leaf{}, rl, 1n, k, pk, EQ{}), rk, rp, rr,
            join_all(True{}, Sp.Leaf{}, rl, 1n, k, pk, EQ{}, rk, {==},
              lt_of_gt(rk, k, all_k(False{}, rl, rk, rp, rr, k, hrk)), v_lt(rl, rk, rp, rr, hr)),
            v_gt(rl, rk, rp, rr, hr),
            join_valid(Sp.Leaf{}, rl, 1n, k, pk, EQ{}, hl, v_l(rl, rk, rp, rr, hr), hlk, all_l(False{}, rl, rk, rp, rr, k, hrk)),
            v_r(rl, rk, rp, rr, hr))
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join_valid(Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, k, pk,
        S.top3(S.above(lp, lk, pk, k), S.above(lp, lk, rp, rk), S.above(rp, rk, pk, k)), hl, hr, hlk, hrk)
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case LT{}:
          v_mk(ll, lk, lp, S.join.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{}),
            v_lt(ll, lk, lp, lr, hl),
            join_all(False{}, lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{}, lk, v_gt(ll, lk, lp, lr, hl),
              gt_of_lt(lk, k, all_k(True{}, ll, lk, lp, lr, k, hlk)),
              mono(False{}, Sp.Node{rl, rk, rp, rr}, k, lk, hrk, gt_of_lt(lk, k, all_k(True{}, ll, lk, lp, lr, k, hlk)))),
            v_l(ll, lk, lp, lr, hl),
            join_valid(lr, Sp.Node{rl, rk, rp, rr}, 1n, k, pk, EQ{}, v_r(ll, lk, lp, lr, hl), hr, all_r(True{}, ll, lk, lp, lr, k, hlk), hrk))
        case EQ{}:
          v_mk(Sp.Node{ll, lk, lp, lr}, k, pk, Sp.Node{rl, rk, rp, rr}, hlk, hrk, hl, hr)
        case GT{}:
          v_mk(S.join.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{}), rk, rp, rr,
            join_all(True{}, Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{}, rk,
              mono(True{}, Sp.Node{ll, lk, lp, lr}, k, rk, hlk, lt_of_gt(rk, k, all_k(False{}, rl, rk, rp, rr, k, hrk))),
              lt_of_gt(rk, k, all_k(False{}, rl, rk, rp, rr, k, hrk)), v_lt(rl, rk, rp, rr, hr)),
            v_gt(rl, rk, rp, rr, hr),
            join_valid(Sp.Node{ll, lk, lp, lr}, rl, 1n, k, pk, EQ{}, hl, v_l(rl, rk, rp, rr, hr), hlk, all_l(False{}, rl, rk, rp, rr, k, hrk)),
            v_r(rl, rk, rp, rr, hr))

# Join2
# -----

def b2_tl0(A: Bool, B: Bool, -C: Bool, -R: Bool)
    -> {Bool.or(Bool.or(A, Bool.or(B, C)), R) == Bool.or(A, Bool.or(B, Bool.or(C, R))) : Bool}:
  match A B:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def b2_tl(+A: Bool, +B: Bool, +C: Bool, +R: Bool, -J: Bool, h: {Bool.or(C, R) == J : Bool})
    -> {Bool.or(Bool.or(A, Bool.or(B, C)), R) == Bool.or(A, Bool.or(B, J)) : Bool}:
  %h : {Bool.or(Bool.or(A, Bool.or(B, C)), R) == Bool.or(A, Bool.or(B, _)) : Bool}
  b2_tl0(A, B, C, R)

def b2_tr0(L: Bool, Q: Bool, D: Bool, -E: Bool)
    -> {Bool.or(L, Bool.or(Q, Bool.or(D, E))) == Bool.or(Q, Bool.or(Bool.or(L, D), E)) : Bool}:
  match L Q D:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def b2_tr(+L: Bool, +Q: Bool, +D: Bool, +E: Bool, -J: Bool, h: {Bool.or(L, D) == J : Bool})
    -> {Bool.or(L, Bool.or(Q, Bool.or(D, E))) == Bool.or(Q, Bool.or(J, E)) : Bool}:
  %h : {Bool.or(L, Bool.or(Q, Bool.or(D, E))) == Bool.or(Q, Bool.or(_, E)) : Bool}
  b2_tr0(L, Q, D, E)

def join2_elem(+x: Nat, l: Sp.Tree, r: Sp.Tree, ph: Nat, c: Bool)
    -> {Bool.or(Sp.elem(x, l), Sp.elem(x, r)) == Sp.elem(x, S.join2.go(l, r, ph, c)) : Bool}:
  match l r ph:
    case Sp.Leaf{} r0 q:
      {==}
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Leaf{} q:
      or_f(Sp.elem(x, Sp.Node{ll, lk, lp, lr}))
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join2_elem(x, Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, S.above(lp, lk, rp, rk))
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case True{}:
          b2_tl(Nat.is_eq(x, lk), Sp.elem(x, ll), Sp.elem(x, lr), Sp.elem(x, Sp.Node{rl, rk, rp, rr}),
            Sp.elem(x, S.join2.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, False{})),
            join2_elem(x, lr, Sp.Node{rl, rk, rp, rr}, 1n, False{}))
        case False{}:
          b2_tr(Sp.elem(x, Sp.Node{ll, lk, lp, lr}), Nat.is_eq(x, rk), Sp.elem(x, rl), Sp.elem(x, rr),
            Sp.elem(x, S.join2.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, False{})),
            join2_elem(x, Sp.Node{ll, lk, lp, lr}, rl, 1n, False{}))

def join2_all(+dir: Bool, l: Sp.Tree, r: Sp.Tree, ph: Nat, c: Bool, +b: Nat,
    +h1: {All(dir, l, b) == True{} : Bool}, +h3: {All(dir, r, b) == True{} : Bool})
    -> {All(dir, S.join2.go(l, r, ph, c), b) == True{} : Bool}:
  match l r ph:
    case Sp.Leaf{} r0 q:
      h3
    case Sp.Node{ll, lk, lp, lr} Sp.Leaf{} q:
      h1
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join2_all(dir, Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, S.above(lp, lk, rp, rk), b, h1, h3)
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case True{}:
          all_mk(dir, ll, lk, lp, S.join2.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, False{}), b,
            all_k(dir, ll, lk, lp, lr, b, h1), all_l(dir, ll, lk, lp, lr, b, h1),
            join2_all(dir, lr, Sp.Node{rl, rk, rp, rr}, 1n, False{}, b, all_r(dir, ll, lk, lp, lr, b, h1), h3))
        case False{}:
          all_mk(dir, S.join2.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, False{}), rk, rp, rr, b,
            all_k(dir, rl, rk, rp, rr, b, h3),
            join2_all(dir, Sp.Node{ll, lk, lp, lr}, rl, 1n, False{}, b, h1, all_l(dir, rl, rk, rp, rr, b, h3)),
            all_r(dir, rl, rk, rp, rr, b, h3))

# validity, for keys l < m < r
def join2_valid(l: Sp.Tree, r: Sp.Tree, ph: Nat, c: Bool, +m: Nat,
    +hl: {Sp.valid(l) == True{} : Bool}, +hr: {Sp.valid(r) == True{} : Bool},
    +hlm: {Sp.all_lt(l, m) == True{} : Bool}, +hrm: {Sp.all_gt(r, m) == True{} : Bool})
    -> {Sp.valid(S.join2.go(l, r, ph, c)) == True{} : Bool}:
  match l r ph:
    case Sp.Leaf{} r0 q:
      hr
    case Sp.Node{ll, lk, lp, lr} Sp.Leaf{} q:
      hl
    case Sp.Node{ll, +lk, +lp, lr} Sp.Node{rl, +rk, +rp, rr} 1n+q:
      join2_valid(Sp.Node{ll, lk, lp, lr}, Sp.Node{rl, rk, rp, rr}, q, S.above(lp, lk, rp, rk), m, hl, hr, hlm, hrm)
    case Sp.Node{+ll, +lk, +lp, +lr} Sp.Node{+rl, +rk, +rp, +rr} 0n:
      match c:
        case True{}:
          v_mk(ll, lk, lp, S.join2.go(lr, Sp.Node{rl, rk, rp, rr}, 1n, False{}),
            v_lt(ll, lk, lp, lr, hl),
            join2_all(False{}, lr, Sp.Node{rl, rk, rp, rr}, 1n, False{}, lk, v_gt(ll, lk, lp, lr, hl),
              mono(False{}, Sp.Node{rl, rk, rp, rr}, m, lk, hrm, gt_of_lt(lk, m, all_k(True{}, ll, lk, lp, lr, m, hlm)))),
            v_l(ll, lk, lp, lr, hl),
            join2_valid(lr, Sp.Node{rl, rk, rp, rr}, 1n, False{}, m, v_r(ll, lk, lp, lr, hl), hr,
              all_r(True{}, ll, lk, lp, lr, m, hlm), hrm))
        case False{}:
          v_mk(S.join2.go(Sp.Node{ll, lk, lp, lr}, rl, 1n, False{}), rk, rp, rr,
            join2_all(True{}, Sp.Node{ll, lk, lp, lr}, rl, 1n, False{}, rk,
              mono(True{}, Sp.Node{ll, lk, lp, lr}, m, rk, hlm, lt_of_gt(rk, m, all_k(False{}, rl, rk, rp, rr, m, hrm))),
              v_lt(rl, rk, rp, rr, hr)),
            v_gt(rl, rk, rp, rr, hr),
            join2_valid(Sp.Node{ll, lk, lp, lr}, rl, 1n, False{}, m, hl, v_l(rl, rk, rp, rr, hr), hlm,
              all_l(False{}, rl, rk, rp, rr, m, hrm)),
            v_r(rl, rk, rp, rr, hr))

# Split
# -----

def lo(s: S.Split) -> Sp.Tree:
  match s:
    case S.Split{a, f, b}:
      a

def fnd(s: S.Split) -> Bool:
  match s:
    case S.Split{a, f, b}:
      f

def hi(s: S.Split) -> Sp.Tree:
  match s:
    case S.Split{a, f, b}:
      b

def lo_slo(s: S.Split, -k2: Nat, -p: U32, -r: Sp.Tree) -> {lo(s) == lo(S.split.lo(s, k2, p, r)) : Sp.Tree}:
  match s:
    case S.Split{a, f, b}:
      {==}

def fnd_slo(s: S.Split, -k2: Nat, -p: U32, -r: Sp.Tree) -> {fnd(s) == fnd(S.split.lo(s, k2, p, r)) : Bool}:
  match s:
    case S.Split{a, f, b}:
      {==}

def hi_slo(s: S.Split, -k2: Nat, -p: U32, -r: Sp.Tree) -> {Sp.Node{hi(s), k2, p, r} == hi(S.split.lo(s, k2, p, r)) : Sp.Tree}:
  match s:
    case S.Split{a, f, b}:
      {==}

def lo_shi(-l: Sp.Tree, -k2: Nat, -p: U32, s: S.Split) -> {Sp.Node{l, k2, p, lo(s)} == lo(S.split.hi(l, k2, p, s)) : Sp.Tree}:
  match s:
    case S.Split{a, f, b}:
      {==}

def fnd_shi(-l: Sp.Tree, -k2: Nat, -p: U32, s: S.Split) -> {fnd(s) == fnd(S.split.hi(l, k2, p, s)) : Bool}:
  match s:
    case S.Split{a, f, b}:
      {==}

def hi_shi(-l: Sp.Tree, -k2: Nat, -p: U32, s: S.Split) -> {hi(s) == hi(S.split.hi(l, k2, p, s)) : Sp.Tree}:
  match s:
    case S.Split{a, f, b}:
      {==}

# bounds on t bound both sides of any split of it
def sp_all_lo(+dir: Bool, +k: Nat, t: Sp.Tree, ph: Nat, c: Cmp, +b: Nat, +h: {All(dir, t, b) == True{} : Bool})
    -> {All(dir, lo(S.split.go(k, t, ph, c)), b) == True{} : Bool}:
  match t ph:
    case Sp.Leaf{} q:
      all_leaf(dir, b)
    case Sp.Node{l, +k2, p, r} 1n+q:
      sp_all_lo(dir, k, Sp.Node{l, k2, p, r}, q, Nat.cmp(k, k2), b, h)
    case Sp.Node{+l, +k2, +p, +r} 0n:
      match c:
        case LT{}:
          %lo_slo(S.split.go(k, l, 1n, EQ{}), k2, p, r) : {All(dir, _, b) == True{} : Bool}
          sp_all_lo(dir, k, l, 1n, EQ{}, b, all_l(dir, l, k2, p, r, b, h))
        case EQ{}:
          all_l(dir, l, k2, p, r, b, h)
        case GT{}:
          %lo_shi(l, k2, p, S.split.go(k, r, 1n, EQ{})) : {All(dir, _, b) == True{} : Bool}
          all_mk(dir, l, k2, p, lo(S.split.go(k, r, 1n, EQ{})), b, all_k(dir, l, k2, p, r, b, h),
            all_l(dir, l, k2, p, r, b, h), sp_all_lo(dir, k, r, 1n, EQ{}, b, all_r(dir, l, k2, p, r, b, h)))

def sp_all_hi(+dir: Bool, +k: Nat, t: Sp.Tree, ph: Nat, c: Cmp, +b: Nat, +h: {All(dir, t, b) == True{} : Bool})
    -> {All(dir, hi(S.split.go(k, t, ph, c)), b) == True{} : Bool}:
  match t ph:
    case Sp.Leaf{} q:
      all_leaf(dir, b)
    case Sp.Node{l, +k2, p, r} 1n+q:
      sp_all_hi(dir, k, Sp.Node{l, k2, p, r}, q, Nat.cmp(k, k2), b, h)
    case Sp.Node{+l, +k2, +p, +r} 0n:
      match c:
        case LT{}:
          %hi_slo(S.split.go(k, l, 1n, EQ{}), k2, p, r) : {All(dir, _, b) == True{} : Bool}
          all_mk(dir, hi(S.split.go(k, l, 1n, EQ{})), k2, p, r, b, all_k(dir, l, k2, p, r, b, h),
            sp_all_hi(dir, k, l, 1n, EQ{}, b, all_l(dir, l, k2, p, r, b, h)), all_r(dir, l, k2, p, r, b, h))
        case EQ{}:
          all_r(dir, l, k2, p, r, b, h)
        case GT{}:
          %hi_shi(l, k2, p, S.split.go(k, r, 1n, EQ{})) : {All(dir, _, b) == True{} : Bool}
          sp_all_hi(dir, k, r, 1n, EQ{}, b, all_r(dir, l, k2, p, r, b, h))

# both sides of any split of a valid tree are valid
def sp_vlo(+k: Nat, t: Sp.Tree, ph: Nat, c: Cmp, +vt: {Sp.valid(t) == True{} : Bool})
    -> {Sp.valid(lo(S.split.go(k, t, ph, c))) == True{} : Bool}:
  match t ph:
    case Sp.Leaf{} q:
      {==}
    case Sp.Node{l, +k2, p, r} 1n+q:
      sp_vlo(k, Sp.Node{l, k2, p, r}, q, Nat.cmp(k, k2), vt)
    case Sp.Node{+l, +k2, +p, +r} 0n:
      match c:
        case LT{}:
          %lo_slo(S.split.go(k, l, 1n, EQ{}), k2, p, r) : {Sp.valid(_) == True{} : Bool}
          sp_vlo(k, l, 1n, EQ{}, v_l(l, k2, p, r, vt))
        case EQ{}:
          v_l(l, k2, p, r, vt)
        case GT{}:
          %lo_shi(l, k2, p, S.split.go(k, r, 1n, EQ{})) : {Sp.valid(_) == True{} : Bool}
          v_mk(l, k2, p, lo(S.split.go(k, r, 1n, EQ{})), v_lt(l, k2, p, r, vt),
            sp_all_lo(False{}, k, r, 1n, EQ{}, k2, v_gt(l, k2, p, r, vt)), v_l(l, k2, p, r, vt),
            sp_vlo(k, r, 1n, EQ{}, v_r(l, k2, p, r, vt)))

def sp_vhi(+k: Nat, t: Sp.Tree, ph: Nat, c: Cmp, +vt: {Sp.valid(t) == True{} : Bool})
    -> {Sp.valid(hi(S.split.go(k, t, ph, c))) == True{} : Bool}:
  match t ph:
    case Sp.Leaf{} q:
      {==}
    case Sp.Node{l, +k2, p, r} 1n+q:
      sp_vhi(k, Sp.Node{l, k2, p, r}, q, Nat.cmp(k, k2), vt)
    case Sp.Node{+l, +k2, +p, +r} 0n:
      match c:
        case LT{}:
          %hi_slo(S.split.go(k, l, 1n, EQ{}), k2, p, r) : {Sp.valid(_) == True{} : Bool}
          v_mk(hi(S.split.go(k, l, 1n, EQ{})), k2, p, r,
            sp_all_hi(True{}, k, l, 1n, EQ{}, k2, v_lt(l, k2, p, r, vt)), v_gt(l, k2, p, r, vt),
            sp_vhi(k, l, 1n, EQ{}, v_l(l, k2, p, r, vt)), v_r(l, k2, p, r, vt))
        case EQ{}:
          v_r(l, k2, p, r, vt)
        case GT{}:
          %hi_shi(l, k2, p, S.split.go(k, r, 1n, EQ{})) : {Sp.valid(_) == True{} : Bool}
          sp_vhi(k, r, 1n, EQ{}, v_r(l, k2, p, r, vt))

# split(k, t) puts the keys below k low and those above k high
def sp_lt.fin(+k: Nat, +l: Sp.Tree, +k2: Nat, +p: U32, +r: Sp.Tree, c: Cmp, +ec: {c == Nat.cmp(k, k2) : Cmp},
    +vt: {Sp.valid(Sp.Node{l, k2, p, r}) == True{} : Bool},
    ihl: {Sp.all_lt(lo(S.split(k, l)), k) == True{} : Bool}, ihr: {Sp.all_lt(lo(S.split(k, r)), k) == True{} : Bool})
    -> {Sp.all_lt(lo(S.split.go(k, Sp.Node{l, k2, p, r}, 0n, c)), k) == True{} : Bool}:
  match c:
    case LT{}:
      %lo_slo(S.split(k, l), k2, p, r) : {Sp.all_lt(_, k) == True{} : Bool}
      ihl
    case EQ{}:
      %Equal.sym(Nat, k, k2, eq_nat(k, k2, eq_of_cmp(k, k2, ec))) : {Sp.all_lt(l, _) == True{} : Bool}
      v_lt(l, k2, p, r, vt)
    case GT{}:
      %lo_shi(l, k2, p, S.split(k, r)) : {Sp.all_lt(_, k) == True{} : Bool}
      mk3(Nat.is_lt(k2, k), Sp.all_lt(l, k), Sp.all_lt(lo(S.split(k, r)), k),
        lt_of_gt(k, k2, gt_of_cmp(k, k2, ec)),
        mono(True{}, l, k2, k, v_lt(l, k2, p, r, vt), lt_of_gt(k, k2, gt_of_cmp(k, k2, ec))), ihr)

def sp_lt(+k: Nat, t: Sp.Tree, +vt: {Sp.valid(t) == True{} : Bool}) -> {Sp.all_lt(lo(S.split(k, t)), k) == True{} : Bool}:
  match t:
    case Sp.Leaf{}:
      {==}
    case Sp.Node{+l, +k2, +p, +r}:
      sp_lt.fin(k, l, k2, p, r, Nat.cmp(k, k2), {==}, vt,
        sp_lt(k, l, v_l(l, k2, p, r, vt)), sp_lt(k, r, v_r(l, k2, p, r, vt)))

def sp_gt.fin(+k: Nat, +l: Sp.Tree, +k2: Nat, +p: U32, +r: Sp.Tree, c: Cmp, +ec: {c == Nat.cmp(k, k2) : Cmp},
    +vt: {Sp.valid(Sp.Node{l, k2, p, r}) == True{} : Bool},
    ihl: {Sp.all_gt(hi(S.split(k, l)), k) == True{} : Bool}, ihr: {Sp.all_gt(hi(S.split(k, r)), k) == True{} : Bool})
    -> {Sp.all_gt(hi(S.split.go(k, Sp.Node{l, k2, p, r}, 0n, c)), k) == True{} : Bool}:
  match c:
    case LT{}:
      %hi_slo(S.split(k, l), k2, p, r) : {Sp.all_gt(_, k) == True{} : Bool}
      mk3(Nat.is_gt(k2, k), Sp.all_gt(hi(S.split(k, l)), k), Sp.all_gt(r, k),
        gt_of_lt(k, k2, lt_of_cmp(k, k2, ec)), ihl,
        mono(False{}, r, k2, k, v_gt(l, k2, p, r, vt), gt_of_lt(k, k2, lt_of_cmp(k, k2, ec))))
    case EQ{}:
      %Equal.sym(Nat, k, k2, eq_nat(k, k2, eq_of_cmp(k, k2, ec))) : {Sp.all_gt(r, _) == True{} : Bool}
      v_gt(l, k2, p, r, vt)
    case GT{}:
      %hi_shi(l, k2, p, S.split(k, r)) : {Sp.all_gt(_, k) == True{} : Bool}
      ihr

def sp_gt(+k: Nat, t: Sp.Tree, +vt: {Sp.valid(t) == True{} : Bool}) -> {Sp.all_gt(hi(S.split(k, t)), k) == True{} : Bool}:
  match t:
    case Sp.Leaf{}:
      {==}
    case Sp.Node{+l, +k2, +p, +r}:
      sp_gt.fin(k, l, k2, p, r, Nat.cmp(k, k2), {==}, vt,
        sp_gt(k, l, v_l(l, k2, p, r, vt)), sp_gt(k, r, v_r(l, k2, p, r, vt)))

def drop_lr(Q: Bool, +L: Bool, R: Bool, hQ: {Q == False{} : Bool}, hR: {R == False{} : Bool})
    -> {Bool.or(Q, Bool.or(L, R)) == L : Bool}:
  match Q R:
    case True{} r0:
      absurd2({Bool.or(True{}, Bool.or(L, r0)) == L : Bool}, hQ)
    case False{} True{}:
      absurd2({Bool.or(False{}, Bool.or(L, True{})) == L : Bool}, hR)
    case False{} False{}:
      or_f(L)

def drop_ll(Q: Bool, L: Bool, -R: Bool, hQ: {Q == False{} : Bool}, hL: {L == False{} : Bool})
    -> {Bool.or(Q, Bool.or(L, R)) == R : Bool}:
  match Q L:
    case True{} l0:
      absurd2({Bool.or(True{}, Bool.or(l0, R)) == R : Bool}, hQ)
    case False{} True{}:
      absurd2({Bool.or(False{}, Bool.or(True{}, R)) == R : Bool}, hL)
    case False{} False{}:
      {==}

def or_il(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case False{}:
      absurd({Bool.or(False{}, b) == True{} : Bool}, e)
    case True{}:
      {==}

def lt_sub(+x: Nat, -k: Nat, -k2: Nat, hx: {Nat.is_lt(x, k) == True{} : Bool}, e: {k == k2 : Nat}) -> {Nat.is_lt(x, k2) == True{} : Bool}:
  %e : {Nat.is_lt(x, _) == True{} : Bool}
  hx

def gt_sub(+x: Nat, -k: Nat, -k2: Nat, hx: {Nat.is_gt(x, k) == True{} : Bool}, e: {k == k2 : Nat}) -> {Nat.is_gt(x, k2) == True{} : Bool}:
  %e : {Nat.is_gt(x, _) == True{} : Bool}
  hx

def keq(+k: Nat, +k2: Nat, ec: {EQ{} == Nat.cmp(k, k2) : Cmp}) -> {k == k2 : Nat}:
  eq_nat(k, k2, eq_of_cmp(k, k2, ec))

# membership in the low side: the keys of t below k
def sp_elem_lo.fin(+x: Nat, +k: Nat, +l: Sp.Tree, +k2: Nat, +p: U32, +r: Sp.Tree, c: Cmp, +ec: {c == Nat.cmp(k, k2) : Cmp},
    +vt: {Sp.valid(Sp.Node{l, k2, p, r}) == True{} : Bool}, +hx: {Nat.is_lt(x, k) == True{} : Bool},
    ihl: {Sp.elem(x, l) == Sp.elem(x, lo(S.split(k, l))) : Bool}, ihr: {Sp.elem(x, r) == Sp.elem(x, lo(S.split(k, r))) : Bool})
    -> {Sp.elem(x, Sp.Node{l, k2, p, r}) == Sp.elem(x, lo(S.split.go(k, Sp.Node{l, k2, p, r}, 0n, c))) : Bool}:
  match c:
    case LT{}:
      %lo_slo(S.split(k, l), k2, p, r) : {Sp.elem(x, Sp.Node{l, k2, p, r}) == Sp.elem(x, _) : Bool}
      %ihl : {Sp.elem(x, Sp.Node{l, k2, p, r}) == _ : Bool}
      drop_lr(Nat.is_eq(x, k2), Sp.elem(x, l), Sp.elem(x, r),
        lt_ne(x, k2, lt_trans(x, k, k2, hx, lt_of_cmp(k, k2, ec))),
        notin_far(False{}, x, r, k2, v_gt(l, k2, p, r, vt), lt_trans(x, k, k2, hx, lt_of_cmp(k, k2, ec))))
    case EQ{}:
      drop_lr(Nat.is_eq(x, k2), Sp.elem(x, l), Sp.elem(x, r),
        lt_ne(x, k2, lt_sub(x, k, k2, hx, keq(k, k2, ec))),
        notin_far(False{}, x, r, k2, v_gt(l, k2, p, r, vt), lt_sub(x, k, k2, hx, keq(k, k2, ec))))
    case GT{}:
      %lo_shi(l, k2, p, S.split(k, r)) : {Sp.elem(x, Sp.Node{l, k2, p, r}) == Sp.elem(x, _) : Bool}
      %ihr : {Sp.elem(x, Sp.Node{l, k2, p, r}) == Bool.or(Nat.is_eq(x, k2), Bool.or(Sp.elem(x, l), _)) : Bool}
      {==}

def sp_elem_lo(+x: Nat, +k: Nat, t: Sp.Tree, +vt: {Sp.valid(t) == True{} : Bool}, +hx: {Nat.is_lt(x, k) == True{} : Bool})
    -> {Sp.elem(x, t) == Sp.elem(x, lo(S.split(k, t))) : Bool}:
  match t:
    case Sp.Leaf{}:
      {==}
    case Sp.Node{+l, +k2, +p, +r}:
      sp_elem_lo.fin(x, k, l, k2, p, r, Nat.cmp(k, k2), {==}, vt, hx,
        sp_elem_lo(x, k, l, v_l(l, k2, p, r, vt), hx), sp_elem_lo(x, k, r, v_r(l, k2, p, r, vt), hx))

# membership in the high side: the keys of t above k
def sp_elem_hi.fin(+x: Nat, +k: Nat, +l: Sp.Tree, +k2: Nat, +p: U32, +r: Sp.Tree, c: Cmp, +ec: {c == Nat.cmp(k, k2) : Cmp},
    +vt: {Sp.valid(Sp.Node{l, k2, p, r}) == True{} : Bool}, +hx: {Nat.is_gt(x, k) == True{} : Bool},
    ihl: {Sp.elem(x, l) == Sp.elem(x, hi(S.split(k, l))) : Bool}, ihr: {Sp.elem(x, r) == Sp.elem(x, hi(S.split(k, r))) : Bool})
    -> {Sp.elem(x, Sp.Node{l, k2, p, r}) == Sp.elem(x, hi(S.split.go(k, Sp.Node{l, k2, p, r}, 0n, c))) : Bool}:
  match c:
    case LT{}:
      %hi_slo(S.split(k, l), k2, p, r) : {Sp.elem(x, Sp.Node{l, k2, p, r}) == Sp.elem(x, _) : Bool}
      %ihl : {Sp.elem(x, Sp.Node{l, k2, p, r}) == Bool.or(Nat.is_eq(x, k2), Bool.or(_, Sp.elem(x, r))) : Bool}
      {==}
    case EQ{}:
      drop_ll(Nat.is_eq(x, k2), Sp.elem(x, l), Sp.elem(x, r),
        gt_ne(x, k2, gt_sub(x, k, k2, hx, keq(k, k2, ec))),
        notin_far(True{}, x, l, k2, v_lt(l, k2, p, r, vt), gt_sub(x, k, k2, hx, keq(k, k2, ec))))
    case GT{}:
      %hi_shi(l, k2, p, S.split(k, r)) : {Sp.elem(x, Sp.Node{l, k2, p, r}) == Sp.elem(x, _) : Bool}
      %ihr : {Sp.elem(x, Sp.Node{l, k2, p, r}) == _ : Bool}
      drop_ll(Nat.is_eq(x, k2), Sp.elem(x, l), Sp.elem(x, r),
        gt_ne(x, k2, gt_trans(x, k, k2, hx, gt_of_cmp(k, k2, ec))),
        notin_far(True{}, x, l, k2, v_lt(l, k2, p, r, vt), gt_trans(x, k, k2, hx, gt_of_cmp(k, k2, ec))))

def sp_elem_hi(+x: Nat, +k: Nat, t: Sp.Tree, +vt: {Sp.valid(t) == True{} : Bool}, +hx: {Nat.is_gt(x, k) == True{} : Bool})
    -> {Sp.elem(x, t) == Sp.elem(x, hi(S.split(k, t))) : Bool}:
  match t:
    case Sp.Leaf{}:
      {==}
    case Sp.Node{+l, +k2, +p, +r}:
      sp_elem_hi.fin(x, k, l, k2, p, r, Nat.cmp(k, k2), {==}, vt, hx,
        sp_elem_hi(x, k, l, v_l(l, k2, p, r, vt), hx), sp_elem_hi(x, k, r, v_r(l, k2, p, r, vt), hx))

# found(split(k, t)) says whether k is in t
def sp_found.fin(+k: Nat, +l: Sp.Tree, +k2: Nat, +p: U32, +r: Sp.Tree, c: Cmp, +ec: {c == Nat.cmp(k, k2) : Cmp},
    +vt: {Sp.valid(Sp.Node{l, k2, p, r}) == True{} : Bool},
    ihl: {Sp.elem(k, l) == fnd(S.split(k, l)) : Bool}, ihr: {Sp.elem(k, r) == fnd(S.split(k, r)) : Bool})
    -> {Sp.elem(k, Sp.Node{l, k2, p, r}) == fnd(S.split.go(k, Sp.Node{l, k2, p, r}, 0n, c)) : Bool}:
  match c:
    case LT{}:
      %fnd_slo(S.split(k, l), k2, p, r) : {Sp.elem(k, Sp.Node{l, k2, p, r}) == _ : Bool}
      %ihl : {Sp.elem(k, Sp.Node{l, k2, p, r}) == _ : Bool}
      drop_lr(Nat.is_eq(k, k2), Sp.elem(k, l), Sp.elem(k, r), lt_ne(k, k2, lt_of_cmp(k, k2, ec)),
        notin_far(False{}, k, r, k2, v_gt(l, k2, p, r, vt), lt_of_cmp(k, k2, ec)))
    case EQ{}:
      or_il(Nat.is_eq(k, k2), Bool.or(Sp.elem(k, l), Sp.elem(k, r)), eq_of_cmp(k, k2, ec))
    case GT{}:
      %fnd_shi(l, k2, p, S.split(k, r)) : {Sp.elem(k, Sp.Node{l, k2, p, r}) == _ : Bool}
      %ihr : {Sp.elem(k, Sp.Node{l, k2, p, r}) == _ : Bool}
      drop_ll(Nat.is_eq(k, k2), Sp.elem(k, l), Sp.elem(k, r), gt_ne(k, k2, gt_of_cmp(k, k2, ec)),
        notin_far(True{}, k, l, k2, v_lt(l, k2, p, r, vt), gt_of_cmp(k, k2, ec)))

def sp_found(+k: Nat, t: Sp.Tree, +vt: {Sp.valid(t) == True{} : Bool}) -> {Sp.elem(k, t) == fnd(S.split(k, t)) : Bool}:
  match t:
    case Sp.Leaf{}:
      {==}
    case Sp.Node{+l, +k2, +p, +r}:
      sp_found.fin(k, l, k2, p, r, Nat.cmp(k, k2), {==}, vt,
        sp_found(k, l, v_l(l, k2, p, r, vt)), sp_found(k, r, v_r(l, k2, p, r, vt)))

# Union, intersection, difference
# -------------------------------

# the Boolean combination op(.., m, ..) computes
def comb(m: S.Mode, p: Bool, q: Bool) -> Bool:
  match m:
    case S.U{}:
      Bool.or(p, q)
    case S.I{}:
      Bool.and(p, q)
    case S.D{}:
      Bool.and(p, Bool.not(q))

def IsF(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def isf(b: Bool, h: {b == False{} : Bool}) -> IsF(b):
  match b:
    case True{}:
      absurd2(Empty, h)
    case False{}:
      Unit{}

def ist(b: Bool, h: {b == True{} : Bool}) -> IsTrue(b):
  match b:
    case True{}:
      Unit{}
    case False{}:
      absurd(Empty, h)

def and_f(a: Bool) -> {False{} == Bool.and(a, False{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def t_and(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_ff(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def combine_elem(+x: Nat, c: Bool, +l: Sp.Tree, +k: Nat, +r: Sp.Tree)
    -> {Bool.or(Bool.and(Nat.is_eq(x, k), c), Bool.or(Sp.elem(x, l), Sp.elem(x, r))) == Sp.elem(x, S.combine(c, l, k, r)) : Bool}:
  match c:
    case True{}:
      %and_t(Nat.is_eq(x, k)) : {Bool.or(_, Bool.or(Sp.elem(x, l), Sp.elem(x, r))) == Sp.elem(x, S.combine(True{}, l, k, r)) : Bool}
      join_elem(x, l, r, 1n, k, S.prio(k), EQ{})
    case False{}:
      %and_f(Nat.is_eq(x, k)) : {Bool.or(_, Bool.or(Sp.elem(x, l), Sp.elem(x, r))) == Sp.elem(x, S.combine(False{}, l, k, r)) : Bool}
      join2_elem(x, l, r, 1n, False{})

def combine_all(+dir: Bool, c: Bool, +l: Sp.Tree, +k: Nat, +r: Sp.Tree, +b: Nat,
    hl: {All(dir, l, b) == True{} : Bool}, hk: {T(dir, k, b) == True{} : Bool}, hr: {All(dir, r, b) == True{} : Bool})
    -> {All(dir, S.combine(c, l, k, r), b) == True{} : Bool}:
  match c:
    case True{}:
      join_all(dir, l, r, 1n, k, S.prio(k), EQ{}, b, hl, hk, hr)
    case False{}:
      join2_all(dir, l, r, 1n, False{}, b, hl, hr)

def combine_valid(c: Bool, +l: Sp.Tree, +k: Nat, +r: Sp.Tree, vl: {Sp.valid(l) == True{} : Bool},
    vr: {Sp.valid(r) == True{} : Bool}, hl: {Sp.all_lt(l, k) == True{} : Bool}, hr: {Sp.all_gt(r, k) == True{} : Bool})
    -> {Sp.valid(S.combine(c, l, k, r)) == True{} : Bool}:
  match c:
    case True{}:
      join_valid(l, r, 1n, k, S.prio(k), EQ{}, vl, vr, hl, hr)
    case False{}:
      join2_valid(l, r, 1n, False{}, k, vl, vr, hl, hr)

# op at phase 0n, after the split
def op_unfold(+l1: Sp.Tree, +k1: Nat, +p1: U32, +r1: Sp.Tree, +m: S.Mode, s: S.Split)
    -> {S.combine(S.keep(m, fnd(s)), S.op(l1, 1n, m, S.Raw{lo(s)}), k1, S.op(r1, 1n, m, S.Raw{hi(s)}))
        == S.op(Sp.Node{l1, k1, p1, r1}, 0n, m, S.Cut{s}) : Sp.Tree}:
  match s:
    case S.Split{a, f, b}:
      {==}

def op_all(+dir: Bool, a: Sp.Tree, b: Sp.Tree, +m: S.Mode, +bd: Nat, +ha: {All(dir, a, bd) == True{} : Bool},
    +hb: {All(dir, b, bd) == True{} : Bool}) -> {All(dir, S.op(a, 1n, m, S.Raw{b}), bd) == True{} : Bool}:
  match a:
    case Sp.Leaf{}:
      match m:
        case S.U{}:
          hb
        case S.I{}:
          all_leaf(dir, bd)
        case S.D{}:
          all_leaf(dir, bd)
    case Sp.Node{+l1, +k1, +p1, +r1}:
      match b:
        case Sp.Leaf{}:
          match m:
            case S.U{}:
              ha
            case S.I{}:
              all_leaf(dir, bd)
            case S.D{}:
              ha
        case Sp.Node{+bl, +bk, +bp, +br}:
          %op_unfold(l1, k1, p1, r1, m, S.split(k1, Sp.Node{bl, bk, bp, br})) : {All(dir, _, bd) == True{} : Bool}
          combine_all(dir, S.keep(m, fnd(S.split(k1, Sp.Node{bl, bk, bp, br}))), S.op(l1, 1n, m, S.Raw{lo(S.split(k1, Sp.Node{bl, bk, bp, br}))}), k1, S.op(r1, 1n, m, S.Raw{hi(S.split(k1, Sp.Node{bl, bk, bp, br}))}), bd,
            op_all(dir, l1, lo(S.split(k1, Sp.Node{bl, bk, bp, br})), m, bd, all_l(dir, l1, k1, p1, r1, bd, ha), sp_all_lo(dir, k1, Sp.Node{bl, bk, bp, br}, 1n, EQ{}, bd, hb)),
            all_k(dir, l1, k1, p1, r1, bd, ha),
            op_all(dir, r1, hi(S.split(k1, Sp.Node{bl, bk, bp, br})), m, bd, all_r(dir, l1, k1, p1, r1, bd, ha), sp_all_hi(dir, k1, Sp.Node{bl, bk, bp, br}, 1n, EQ{}, bd, hb)))

def op_valid(a: Sp.Tree, b: Sp.Tree, +m: S.Mode, +va: {Sp.valid(a) == True{} : Bool}, +vb: {Sp.valid(b) == True{} : Bool})
    -> {Sp.valid(S.op(a, 1n, m, S.Raw{b})) == True{} : Bool}:
  match a:
    case Sp.Leaf{}:
      match m:
        case S.U{}:
          vb
        case S.I{}:
          {==}
        case S.D{}:
          {==}
    case Sp.Node{+l1, +k1, +p1, +r1}:
      match b:
        case Sp.Leaf{}:
          match m:
            case S.U{}:
              va
            case S.I{}:
              {==}
            case S.D{}:
              va
        case Sp.Node{+bl, +bk, +bp, +br}:
          %op_unfold(l1, k1, p1, r1, m, S.split(k1, Sp.Node{bl, bk, bp, br})) : {Sp.valid(_) == True{} : Bool}
          combine_valid(S.keep(m, fnd(S.split(k1, Sp.Node{bl, bk, bp, br}))), S.op(l1, 1n, m, S.Raw{lo(S.split(k1, Sp.Node{bl, bk, bp, br}))}), k1, S.op(r1, 1n, m, S.Raw{hi(S.split(k1, Sp.Node{bl, bk, bp, br}))}),
            op_valid(l1, lo(S.split(k1, Sp.Node{bl, bk, bp, br})), m, v_l(l1, k1, p1, r1, va), sp_vlo(k1, Sp.Node{bl, bk, bp, br}, 1n, EQ{}, vb)),
            op_valid(r1, hi(S.split(k1, Sp.Node{bl, bk, bp, br})), m, v_r(l1, k1, p1, r1, va), sp_vhi(k1, Sp.Node{bl, bk, bp, br}, 1n, EQ{}, vb)),
            op_all(True{}, l1, lo(S.split(k1, Sp.Node{bl, bk, bp, br})), m, k1, v_lt(l1, k1, p1, r1, va), sp_lt(k1, Sp.Node{bl, bk, bp, br}, vb)),
            op_all(False{}, r1, hi(S.split(k1, Sp.Node{bl, bk, bp, br})), m, k1, v_gt(l1, k1, p1, r1, va), sp_gt(k1, Sp.Node{bl, bk, bp, br}, vb)))

# the Boolean cores of op's membership, by where x lies against a's key
def core_lt0(m: S.Mode, L1: Bool, EB: Bool, -K: Bool)
    -> {comb(m, Bool.or(False{}, Bool.or(L1, False{})), EB) == Bool.or(Bool.and(False{}, K), Bool.or(comb(m, L1, EB), comb(m, False{}, False{}))) : Bool}:
  match m L1 EB:
    case S.U{} True{} True{}:
      {==}
    case S.U{} True{} False{}:
      {==}
    case S.U{} False{} True{}:
      {==}
    case S.U{} False{} False{}:
      {==}
    case S.I{} True{} True{}:
      {==}
    case S.I{} True{} False{}:
      {==}
    case S.I{} False{} True{}:
      {==}
    case S.I{} False{} False{}:
      {==}
    case S.D{} True{} True{}:
      {==}
    case S.D{} True{} False{}:
      {==}
    case S.D{} False{} True{}:
      {==}
    case S.D{} False{} False{}:
      {==}

def core_lt(Q: Bool, R1: Bool, EHI: Bool, hQ: IsF(Q), hR1: IsF(R1), hEHI: IsF(EHI), +m: S.Mode, -K: Bool, +L1: Bool,
    +EB: Bool, -ELO: Bool, hB: {EB == ELO : Bool})
    -> {comb(m, Bool.or(Q, Bool.or(L1, R1)), EB) == Bool.or(Bool.and(Q, K), Bool.or(comb(m, L1, ELO), comb(m, R1, EHI))) : Bool}:
  match Q:
    case True{}:
      match hQ:
    case False{}:
      match R1:
        case True{}:
          match hR1:
        case False{}:
          match EHI:
            case True{}:
              match hEHI:
            case False{}:
              %hB : {comb(m, Bool.or(False{}, Bool.or(L1, False{})), EB) == Bool.or(Bool.and(False{}, K), Bool.or(comb(m, L1, _), comb(m, False{}, False{}))) : Bool}
              core_lt0(m, L1, EB, K)

def core_gt0(m: S.Mode, -R1: Bool, -EB: Bool, -K: Bool)
    -> {comb(m, Bool.or(False{}, Bool.or(False{}, R1)), EB) == Bool.or(Bool.and(False{}, K), Bool.or(comb(m, False{}, False{}), comb(m, R1, EB))) : Bool}:
  match m:
    case S.U{}:
      {==}
    case S.I{}:
      {==}
    case S.D{}:
      {==}

def core_gt(Q: Bool, L1: Bool, ELO: Bool, hQ: IsF(Q), hL1: IsF(L1), hELO: IsF(ELO), +m: S.Mode, -K: Bool, +R1: Bool,
    +EB: Bool, -EHI: Bool, hB: {EB == EHI : Bool})
    -> {comb(m, Bool.or(Q, Bool.or(L1, R1)), EB) == Bool.or(Bool.and(Q, K), Bool.or(comb(m, L1, ELO), comb(m, R1, EHI))) : Bool}:
  match Q:
    case True{}:
      match hQ:
    case False{}:
      match L1:
        case True{}:
          match hL1:
        case False{}:
          match ELO:
            case True{}:
              match hELO:
            case False{}:
              %hB : {comb(m, Bool.or(False{}, Bool.or(False{}, R1)), EB) == Bool.or(Bool.and(False{}, K), Bool.or(comb(m, False{}, False{}), comb(m, R1, _))) : Bool}
              core_gt0(m, R1, EB, K)

def core_eq0(m: S.Mode, EB: Bool)
    -> {comb(m, Bool.or(True{}, Bool.or(False{}, False{})), EB) == Bool.or(Bool.and(True{}, S.keep(m, EB)), Bool.or(comb(m, False{}, False{}), comb(m, False{}, False{}))) : Bool}:
  match m EB:
    case S.U{} True{}:
      {==}
    case S.U{} False{}:
      {==}
    case S.I{} True{}:
      {==}
    case S.I{} False{}:
      {==}
    case S.D{} True{}:
      {==}
    case S.D{} False{}:
      {==}

def core_eq(Q: Bool, L1: Bool, R1: Bool, ELO: Bool, EHI: Bool, hQ: IsTrue(Q), hL1: IsF(L1), hR1: IsF(R1), hELO: IsF(ELO),
    hEHI: IsF(EHI), +m: S.Mode, +EB: Bool, -Fd: Bool, hF: {EB == Fd : Bool})
    -> {comb(m, Bool.or(Q, Bool.or(L1, R1)), EB) == Bool.or(Bool.and(Q, S.keep(m, Fd)), Bool.or(comb(m, L1, ELO), comb(m, R1, EHI))) : Bool}:
  match Q:
    case False{}:
      match hQ:
    case True{}:
      match L1:
        case True{}:
          match hL1:
        case False{}:
          match R1:
            case True{}:
              match hR1:
            case False{}:
              match ELO:
                case True{}:
                  match hELO:
                case False{}:
                  match EHI:
                    case True{}:
                      match hEHI:
                    case False{}:
                      %hF : {comb(m, Bool.or(True{}, Bool.or(False{}, False{})), EB) == Bool.or(Bool.and(True{}, S.keep(m, _)), Bool.or(comb(m, False{}, False{}), comb(m, False{}, False{}))) : Bool}
                      core_eq0(m, EB)

def notin_at(+dir: Bool, +x: Nat, +b: Nat, +t: Sp.Tree, h: {All(dir, t, b) == True{} : Bool}, e: {x == b : Nat})
    -> {Sp.elem(x, t) == False{} : Bool}:
  %Equal.sym(Nat, x, b, e) : {Sp.elem(_, t) == False{} : Bool}
  notin_eq(dir, b, t, h)

def found_at(+x: Nat, +k1: Nat, +B: Sp.Tree, vb: {Sp.valid(B) == True{} : Bool}, e: {x == k1 : Nat})
    -> {Sp.elem(x, B) == fnd(S.split(k1, B)) : Bool}:
  %Equal.sym(Nat, x, k1, e) : {Sp.elem(_, B) == fnd(S.split(k1, B)) : Bool}
  sp_found(k1, B, vb)

def op_elem.fin(+x: Nat, +k1: Nat, +l1: Sp.Tree, +p1: U32, +r1: Sp.Tree, +B: Sp.Tree, +m: S.Mode, c: Cmp,
    +ec: {c == Nat.cmp(x, k1) : Cmp}, +va: {Sp.valid(Sp.Node{l1, k1, p1, r1}) == True{} : Bool},
    +vb: {Sp.valid(B) == True{} : Bool})
    -> {comb(m, Sp.elem(x, Sp.Node{l1, k1, p1, r1}), Sp.elem(x, B))
        == Bool.or(Bool.and(Nat.is_eq(x, k1), S.keep(m, fnd(S.split(k1, B)))),
             Bool.or(comb(m, Sp.elem(x, l1), Sp.elem(x, lo(S.split(k1, B)))), comb(m, Sp.elem(x, r1), Sp.elem(x, hi(S.split(k1, B)))))) : Bool}:
  match c:
    case LT{}:
      core_lt(Nat.is_eq(x, k1), Sp.elem(x, r1), Sp.elem(x, hi(S.split(k1, B))),
        isf(Nat.is_eq(x, k1), lt_ne(x, k1, lt_of_cmp(x, k1, ec))),
        isf(Sp.elem(x, r1), notin_far(False{}, x, r1, k1, v_gt(l1, k1, p1, r1, va), lt_of_cmp(x, k1, ec))),
        isf(Sp.elem(x, hi(S.split(k1, B))), notin_far(False{}, x, hi(S.split(k1, B)), k1, sp_gt(k1, B, vb), lt_of_cmp(x, k1, ec))),
        m, S.keep(m, fnd(S.split(k1, B))), Sp.elem(x, l1), Sp.elem(x, B), Sp.elem(x, lo(S.split(k1, B))),
        sp_elem_lo(x, k1, B, vb, lt_of_cmp(x, k1, ec)))
    case GT{}:
      core_gt(Nat.is_eq(x, k1), Sp.elem(x, l1), Sp.elem(x, lo(S.split(k1, B))),
        isf(Nat.is_eq(x, k1), gt_ne(x, k1, gt_of_cmp(x, k1, ec))),
        isf(Sp.elem(x, l1), notin_far(True{}, x, l1, k1, v_lt(l1, k1, p1, r1, va), gt_of_cmp(x, k1, ec))),
        isf(Sp.elem(x, lo(S.split(k1, B))), notin_far(True{}, x, lo(S.split(k1, B)), k1, sp_lt(k1, B, vb), gt_of_cmp(x, k1, ec))),
        m, S.keep(m, fnd(S.split(k1, B))), Sp.elem(x, r1), Sp.elem(x, B), Sp.elem(x, hi(S.split(k1, B))),
        sp_elem_hi(x, k1, B, vb, gt_of_cmp(x, k1, ec)))
    case EQ{}:
      core_eq(Nat.is_eq(x, k1), Sp.elem(x, l1), Sp.elem(x, r1), Sp.elem(x, lo(S.split(k1, B))), Sp.elem(x, hi(S.split(k1, B))),
        ist(Nat.is_eq(x, k1), eq_of_cmp(x, k1, ec)),
        isf(Sp.elem(x, l1), notin_at(True{}, x, k1, l1, v_lt(l1, k1, p1, r1, va), keq(x, k1, ec))),
        isf(Sp.elem(x, r1), notin_at(False{}, x, k1, r1, v_gt(l1, k1, p1, r1, va), keq(x, k1, ec))),
        isf(Sp.elem(x, lo(S.split(k1, B))), notin_at(True{}, x, k1, lo(S.split(k1, B)), sp_lt(k1, B, vb), keq(x, k1, ec))),
        isf(Sp.elem(x, hi(S.split(k1, B))), notin_at(False{}, x, k1, hi(S.split(k1, B)), sp_gt(k1, B, vb), keq(x, k1, ec))),
        m, Sp.elem(x, B), fnd(S.split(k1, B)),
        found_at(x, k1, B, vb, keq(x, k1, ec)))

def op_elem(+x: Nat, a: Sp.Tree, b: Sp.Tree, +m: S.Mode, +va: {Sp.valid(a) == True{} : Bool}, +vb: {Sp.valid(b) == True{} : Bool})
    -> {comb(m, Sp.elem(x, a), Sp.elem(x, b)) == Sp.elem(x, S.op(a, 1n, m, S.Raw{b})) : Bool}:
  match a:
    case Sp.Leaf{}:
      match m:
        case S.U{}:
          {==}
        case S.I{}:
          {==}
        case S.D{}:
          {==}
    case Sp.Node{+l1, +k1, +p1, +r1}:
      match b:
        case Sp.Leaf{}:
          match m:
            case S.U{}:
              or_f(Sp.elem(x, Sp.Node{l1, k1, p1, r1}))
            case S.I{}:
              and_ff(Sp.elem(x, Sp.Node{l1, k1, p1, r1}))
            case S.D{}:
              t_and(Sp.elem(x, Sp.Node{l1, k1, p1, r1}))
        case Sp.Node{+bl, +bk, +bp, +br}:
          %op_unfold(l1, k1, p1, r1, m, S.split(k1, Sp.Node{bl, bk, bp, br})) : {comb(m, Sp.elem(x, Sp.Node{l1, k1, p1, r1}), Sp.elem(x, Sp.Node{bl, bk, bp, br})) == Sp.elem(x, _) : Bool}
          %combine_elem(x, S.keep(m, fnd(S.split(k1, Sp.Node{bl, bk, bp, br}))), S.op(l1, 1n, m, S.Raw{lo(S.split(k1, Sp.Node{bl, bk, bp, br}))}), k1, S.op(r1, 1n, m, S.Raw{hi(S.split(k1, Sp.Node{bl, bk, bp, br}))})) : {comb(m, Sp.elem(x, Sp.Node{l1, k1, p1, r1}), Sp.elem(x, Sp.Node{bl, bk, bp, br})) == _ : Bool}
          %op_elem(x, l1, lo(S.split(k1, Sp.Node{bl, bk, bp, br})), m, v_l(l1, k1, p1, r1, va), sp_vlo(k1, Sp.Node{bl, bk, bp, br}, 1n, EQ{}, vb)) : {comb(m, Sp.elem(x, Sp.Node{l1, k1, p1, r1}), Sp.elem(x, Sp.Node{bl, bk, bp, br})) == Bool.or(Bool.and(Nat.is_eq(x, k1), S.keep(m, fnd(S.split(k1, Sp.Node{bl, bk, bp, br})))), Bool.or(_, Sp.elem(x, S.op(r1, 1n, m, S.Raw{hi(S.split(k1, Sp.Node{bl, bk, bp, br}))})))) : Bool}
          %op_elem(x, r1, hi(S.split(k1, Sp.Node{bl, bk, bp, br})), m, v_r(l1, k1, p1, r1, va), sp_vhi(k1, Sp.Node{bl, bk, bp, br}, 1n, EQ{}, vb)) : {comb(m, Sp.elem(x, Sp.Node{l1, k1, p1, r1}), Sp.elem(x, Sp.Node{bl, bk, bp, br})) == Bool.or(Bool.and(Nat.is_eq(x, k1), S.keep(m, fnd(S.split(k1, Sp.Node{bl, bk, bp, br})))), Bool.or(comb(m, Sp.elem(x, l1), Sp.elem(x, lo(S.split(k1, Sp.Node{bl, bk, bp, br})))), _)) : Bool}
          op_elem.fin(x, k1, l1, p1, r1, Sp.Node{bl, bk, bp, br}, m, Nat.cmp(x, k1), {==}, va, vb)

# The laws
# --------

def Laws.union_valid(a, b, va, vb):
  op_valid(a, b, S.U{}, va, vb)

def Laws.union_elem(x, a, b, va, vb):
  Equal.sym(Bool, comb(S.U{}, Sp.elem(x, a), Sp.elem(x, b)), Sp.elem(x, S.union(a, b)), op_elem(x, a, b, S.U{}, va, vb))

def Laws.inter_valid(a, b, va, vb):
  op_valid(a, b, S.I{}, va, vb)

def Laws.inter_elem(x, a, b, va, vb):
  Equal.sym(Bool, comb(S.I{}, Sp.elem(x, a), Sp.elem(x, b)), Sp.elem(x, S.inter(a, b)), op_elem(x, a, b, S.I{}, va, vb))

def Laws.diff_valid(a, b, va, vb):
  op_valid(a, b, S.D{}, va, vb)

def Laws.diff_elem(x, a, b, va, vb):
  Equal.sym(Bool, comb(S.D{}, Sp.elem(x, a), Sp.elem(x, b)), Sp.elem(x, S.diff(a, b)), op_elem(x, a, b, S.D{}, va, vb))

def Laws.build_valid(seed, bits, d, lo):
  match d:
    case 0n:
      {==}
    case 1n+(+e):
      Laws.union_valid(S.build(seed, bits, e, lo), S.build(seed, bits, e, U32.add(lo, U32.shln(1, e))),
        Laws.build_valid(seed, bits, e, lo), Laws.build_valid(seed, bits, e, U32.add(lo, U32.shln(1, e))))
