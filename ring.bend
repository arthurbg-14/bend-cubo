# Cubo -- a ring tactic for Nat, proven sound.
#
# Bend has no tactics: an equation between polynomials is proven by
# rewriting, one step at a time. This file turns that into computation.
# A polynomial is written as syntax (Ex, over variables numbered into an
# environment); norm brings it to a canonical sum of monomials; norm is
# proven to keep the value (norm_ok). So two expressions whose normal
# forms compute to the same term have the same value: eq. The
# checker runs norm on the syntax, which is concrete and small.
#
# A rewrite `%e : P` with e : {a == b} takes the goal P[b] to P[a].

import Base

# Nat, the basics
# ---------------

def add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(+a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %add_zero(b) : {_ == Nat.add(b, 0n) : Nat}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p))
        : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(+a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def mul_zero(+a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

# a (1 + b) == a + a b
def mul_succ(+a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      # 1 + (b + p(1+b)) == 1 + (p + (b + p b))
      %add_assoc(p, b, Nat.mul(p, b))
        : {1n+Nat.add(b, Nat.mul(p, 1n+b)) == 1n+_ : Nat}
      %add_comm(b, p) : {1n+Nat.add(b, Nat.mul(p, 1n+b)) == 1n+Nat.add(_, Nat.mul(p, b)) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(b, p), Nat.mul(p, b)), Nat.add(b, Nat.add(p, Nat.mul(p, b))),
        add_assoc(b, p, Nat.mul(p, b)))
        : {1n+Nat.add(b, Nat.mul(p, 1n+b)) == 1n+_ : Nat}
      %mul_succ(p, b) : {1n+Nat.add(b, Nat.mul(p, 1n+b)) == 1n+Nat.add(b, _) : Nat}
      {==}

def mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      %mul_zero(b) : {_ == Nat.mul(b, 0n) : Nat}
      {==}
    case 1n+p:
      # b + p b == b (1 + p)
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), mul_succ(b, p))
        : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

# (a + b) c == a c + b c
def mul_add_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
        Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))
        : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == _ : Nat}
      %mul_add_r(p, b, c) : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == Nat.add(c, _) : Nat}
      {==}

# c (a + b) == c a + c b
def mul_add_l(+c: Nat, +a: Nat, +b: Nat) -> {Nat.mul(c, Nat.add(a, b)) == Nat.add(Nat.mul(c, a), Nat.mul(c, b)) : Nat}:
  %mul_comm(a, c) : {Nat.mul(c, Nat.add(a, b)) == Nat.add(_, Nat.mul(c, b)) : Nat}
  %mul_comm(b, c) : {Nat.mul(c, Nat.add(a, b)) == Nat.add(Nat.mul(a, c), _) : Nat}
  %mul_add_r(a, b, c) : {Nat.mul(c, Nat.add(a, b)) == _ : Nat}
  mul_comm(c, Nat.add(a, b))

def mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      # (b + p b) c == b c + p (b c)
      %mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      mul_add_r(b, Nat.mul(p, b), c)

def mul_one(+a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_one(p) : {1n+Nat.mul(p, 1n) == 1n+_ : Nat}
      {==}

# 1 a == a
def one_mul(+a: Nat) -> {Nat.mul(1n, a) == a : Nat}:
  add_zero(a)

# u (v w) == v (u w)
def mul_left_comm(+u: Nat, +v: Nat, +w: Nat) -> {Nat.mul(u, Nat.mul(v, w)) == Nat.mul(v, Nat.mul(u, w)) : Nat}:
  %mul_assoc(u, v, w) : {_ == Nat.mul(v, Nat.mul(u, w)) : Nat}
  %mul_comm(v, u) : {Nat.mul(_, w) == Nat.mul(v, Nat.mul(u, w)) : Nat}
  mul_assoc(v, u, w)

# (a b)(c d) == (a c)(b d)
def mul_swap(+a: Nat, +b: Nat, +c: Nat, +d: Nat)
  -> {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, c), Nat.mul(b, d)), Nat.mul(a, Nat.mul(c, Nat.mul(b, d))),
    mul_assoc(a, c, Nat.mul(b, d))) : {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == _ : Nat}
  %mul_left_comm(b, c, d) : {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(a, _) : Nat}
  mul_assoc(a, b, Nat.mul(c, d))

# (a + b) + (c + d) == (a + c) + (b + d)
def add_swap(+a: Nat, +b: Nat, +c: Nat, +d: Nat)
  -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))),
    add_assoc(a, c, Nat.add(b, d))) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == _ : Nat}
  %add_assoc(c, b, d) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, _) : Nat}
  %add_comm(b, c) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, Nat.add(_, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(b, c), d), Nat.add(b, Nat.add(c, d)), add_assoc(b, c, d))
    : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, _) : Nat}
  add_assoc(a, b, Nat.add(c, d))

# u + (v + w) == v + (u + w)
def add_left_comm(+u: Nat, +v: Nat, +w: Nat) -> {Nat.add(u, Nat.add(v, w)) == Nat.add(v, Nat.add(u, w)) : Nat}:
  %add_assoc(u, v, w) : {_ == Nat.add(v, Nat.add(u, w)) : Nat}
  %add_comm(v, u) : {Nat.add(_, w) == Nat.add(v, Nat.add(u, w)) : Nat}
  add_assoc(v, u, w)

# Comparisons
# -----------

# EQ is neither LT nor GT
def NotEq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case LT{}:
      Unit
    case GT{}:
      Unit

def lt_ne(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : NotEq(_)
  Unit{}

def gt_ne(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : NotEq(_)
  Unit{}

def cmp_eq(+a: Nat, +b: Nat, h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, lt_ne(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, gt_ne(h))
    case 1n+p 1n+q:
      %cmp_eq(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# Syntax
# ------

type Ex is Data:
  V{i: Nat}
  N{n: Nat}
  Add{a: Ex, b: Ex}
  Mul{a: Ex, b: Ex}

def at(+env: List<&2, Nat>, i: Nat) -> Nat:
  match env i:
    case Nil{} _:
      0n
    case h <> t 0n:
      h
    case h <> t 1n+j:
      at(t, j)

def ev(+env: List<&2, Nat>, e: Ex) -> Nat:
  match e:
    case V{i}:
      at(env, i)
    case N{n}:
      n
    case Add{a, b}:
      Nat.add(ev(env, a), ev(env, b))
    case Mul{a, b}:
      Nat.mul(ev(env, a), ev(env, b))

# Normal forms
# ------------
# A monomial is a coefficient and its variables in order; a polynomial,
# its monomials in order of their variables.

type Mono is Data:
  M{c: Nat, vs: List<&2, Nat>}

def prod(+env: List<&2, Nat>, vs: List<&2, Nat>) -> Nat:
  match vs:
    case []:
      1n
    case i <> r:
      Nat.mul(at(env, i), prod(env, r))

def evm(+env: List<&2, Nat>, m: Mono) -> Nat:
  match m:
    case M{c, vs}:
      Nat.mul(c, prod(env, vs))

def evp(+env: List<&2, Nat>, p: List<&2, Mono>) -> Nat:
  match p:
    case []:
      0n
    case m <> r:
      Nat.add(evm(env, m), evp(env, r))

def lex(c: Cmp, r: Cmp) -> Cmp:
  match c:
    case EQ{}:
      r
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def vcmp(a: List<&2, Nat>, b: List<&2, Nat>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} y <> ys:
      LT{}
    case x <> xs Nil{}:
      GT{}
    case x <> xs y <> ys:
      lex(Nat.cmp(x, y), vcmp(xs, ys))

# how the heads of two polynomials compare
def hcmp(p: List<&2, Mono>, q: List<&2, Mono>) -> Cmp:
  match p q:
    case M{c1, v1} <> p1 M{c2, v2} <> q1:
      vcmp(v1, v2)
    case _ _:
      EQ{}

def padd.go(+p: List<&2, Mono>, +q: List<&2, Mono>, c: Cmp) -> List<&2, Mono>:
  match p q c:
    case Nil{} _ _:
      q
    case M{c1, v1} <> p1 Nil{} _:
      p
    case M{c1, v1} <> p1 M{c2, v2} <> q1 LT{}:
      M{c1, v1} <> padd.go(p1, q, hcmp(p1, q))
    case M{c1, v1} <> p1 M{c2, v2} <> q1 GT{}:
      M{c2, v2} <> padd.go(p, q1, hcmp(p, q1))
    case M{c1, v1} <> p1 M{c2, v2} <> q1 EQ{}:
      M{Nat.add(c1, c2), v1} <> padd.go(p1, q1, hcmp(p1, q1))

def padd(+p: List<&2, Mono>, +q: List<&2, Mono>) -> List<&2, Mono>:
  padd.go(p, q, hcmp(p, q))

# whether the head of a is at most the head of b
def hle(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case x <> xs y <> ys:
      Nat.is_le(x, y)
    case _ _:
      True{}

def vmerge.go(+a: List<&2, Nat>, +b: List<&2, Nat>, le: Bool) -> List<&2, Nat>:
  match a b le:
    case Nil{} _ _:
      b
    case x <> a1 Nil{} _:
      a
    case x <> a1 y <> b1 True{}:
      x <> vmerge.go(a1, b, hle(a1, b))
    case x <> a1 y <> b1 False{}:
      y <> vmerge.go(a, b1, hle(a, b1))

def vmerge(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  vmerge.go(a, b, hle(a, b))

def mmul(m1: Mono, m2: Mono) -> Mono:
  match m1 m2:
    case M{c1, v1} M{c2, v2}:
      M{Nat.mul(c1, c2), vmerge(v1, v2)}

def pmono(+m: Mono, q: List<&2, Mono>) -> List<&2, Mono>:
  match q:
    case []:
      []
    case n <> q1:
      padd([mmul(m, n)], pmono(m, q1))

def pmul(p: List<&2, Mono>, +q: List<&2, Mono>) -> List<&2, Mono>:
  match p:
    case []:
      []
    case m <> p1:
      padd(pmono(m, q), pmul(p1, q))

def num(n: Nat) -> List<&2, Mono>:
  match n:
    case 0n:
      []
    case 1n+k:
      [M{1n+k, []}]

def norm(e: Ex) -> List<&2, Mono>:
  match e:
    case V{i}:
      [M{1n, [i]}]
    case N{n}:
      num(n)
    case Add{a, b}:
      padd(norm(a), norm(b))
    case Mul{a, b}:
      pmul(norm(a), norm(b))

# Soundness
# ---------

def lex_eq_l(c: Cmp, -r: Cmp, h: {lex(c, r) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, lt_ne(h))
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, gt_ne(h))

def lex_eq_r(c: Cmp, -r: Cmp, h: {lex(c, r) == EQ{} : Cmp}) -> {r == EQ{} : Cmp}:
  match c:
    case EQ{}:
      h
    case LT{}:
      Empty.absurd({r == EQ{} : Cmp}, lt_ne(h))
    case GT{}:
      Empty.absurd({r == EQ{} : Cmp}, gt_ne(h))

def vcmp_eq(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {vcmp(a, b) == EQ{} : Cmp}) -> {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> ys:
      Empty.absurd({Nil{} == y <> ys : List<&2, Nat>}, lt_ne(h))
    case x <> xs Nil{}:
      Empty.absurd({x <> xs == Nil{} : List<&2, Nat>}, gt_ne(h))
    case x <> xs y <> ys:
      %cmp_eq(x, y, lex_eq_l(Nat.cmp(x, y), vcmp(xs, ys), h)) : {x <> xs == _ <> ys : List<&2, Nat>}
      %vcmp_eq(xs, ys, lex_eq_r(Nat.cmp(x, y), vcmp(xs, ys), h)) : {x <> xs == x <> _ : List<&2, Nat>}
      {==}

def add_zero_s(+a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  Equal.sym(Nat, Nat.add(a, 0n), a, add_zero(a))

def mul_one_s(+a: Nat) -> {a == Nat.mul(a, 1n) : Nat}:
  Equal.sym(Nat, Nat.mul(a, 1n), a, mul_one(a))

def one_mul_s(+a: Nat) -> {a == Nat.mul(1n, a) : Nat}:
  Equal.sym(Nat, Nat.mul(1n, a), a, one_mul(a))

# a c + b c == (a + b) c
def distr_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.add(a, b), c), Nat.add(Nat.mul(a, c), Nat.mul(b, c)), mul_add_r(a, b, c))

def padd_ok(+env: List<&2, Nat>, +p: List<&2, Mono>, +q: List<&2, Mono>, c: Cmp, +h: {hcmp(p, q) == c : Cmp})
  -> {Nat.add(evp(env, p), evp(env, q)) == evp(env, padd.go(p, q, c)) : Nat}:
  match p q c:
    case Nil{} _ _:
      {==}
    case M{c1, v1} <> p1 Nil{} _:
      add_zero(evp(env, M{c1, v1} <> p1))
    case M{c1, v1} <> p1 M{c2, v2} <> q1 LT{}:
      %padd_ok(env, p1, M{c2, v2} <> q1, hcmp(p1, M{c2, v2} <> q1), {==})
        : {Nat.add(Nat.add(evm(env, M{c1, v1}), evp(env, p1)), evp(env, M{c2, v2} <> q1))
           == Nat.add(evm(env, M{c1, v1}), _) : Nat}
      add_assoc(evm(env, M{c1, v1}), evp(env, p1), evp(env, M{c2, v2} <> q1))
    case M{c1, v1} <> p1 M{c2, v2} <> q1 GT{}:
      %padd_ok(env, M{c1, v1} <> p1, q1, hcmp(M{c1, v1} <> p1, q1), {==})
        : {Nat.add(evp(env, M{c1, v1} <> p1), Nat.add(evm(env, M{c2, v2}), evp(env, q1)))
           == Nat.add(evm(env, M{c2, v2}), _) : Nat}
      add_left_comm(evp(env, M{c1, v1} <> p1), evm(env, M{c2, v2}), evp(env, q1))
    case M{c1, v1} <> p1 M{c2, v2} <> q1 EQ{}:
      %padd_ok(env, p1, q1, hcmp(p1, q1), {==})
        : {Nat.add(Nat.add(Nat.mul(c1, prod(env, v1)), evp(env, p1)),
                   Nat.add(Nat.mul(c2, prod(env, v2)), evp(env, q1)))
           == Nat.add(Nat.mul(Nat.add(c1, c2), prod(env, v1)), _) : Nat}
      %vcmp_eq(v1, v2, h)
        : {Nat.add(Nat.add(Nat.mul(c1, prod(env, v1)), evp(env, p1)),
                   Nat.add(Nat.mul(c2, prod(env, _)), evp(env, q1)))
           == Nat.add(Nat.mul(Nat.add(c1, c2), prod(env, v1)), Nat.add(evp(env, p1), evp(env, q1))) : Nat}
      %distr_r(c1, c2, prod(env, v1))
        : {Nat.add(Nat.add(Nat.mul(c1, prod(env, v1)), evp(env, p1)),
                   Nat.add(Nat.mul(c2, prod(env, v1)), evp(env, q1)))
           == Nat.add(_, Nat.add(evp(env, p1), evp(env, q1))) : Nat}
      add_swap(Nat.mul(c1, prod(env, v1)), evp(env, p1), Nat.mul(c2, prod(env, v1)), evp(env, q1))

def vmerge_ok(+env: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, le: Bool)
  -> {Nat.mul(prod(env, a), prod(env, b)) == prod(env, vmerge.go(a, b, le)) : Nat}:
  match a b le:
    case Nil{} _ _:
      one_mul(prod(env, b))
    case x <> a1 Nil{} _:
      mul_one(prod(env, x <> a1))
    case x <> a1 y <> b1 True{}:
      %vmerge_ok(env, a1, y <> b1, hle(a1, y <> b1))
        : {Nat.mul(Nat.mul(at(env, x), prod(env, a1)), prod(env, y <> b1))
           == Nat.mul(at(env, x), _) : Nat}
      mul_assoc(at(env, x), prod(env, a1), prod(env, y <> b1))
    case x <> a1 y <> b1 False{}:
      %vmerge_ok(env, x <> a1, b1, hle(x <> a1, b1))
        : {Nat.mul(prod(env, x <> a1), Nat.mul(at(env, y), prod(env, b1)))
           == Nat.mul(at(env, y), _) : Nat}
      mul_left_comm(prod(env, x <> a1), at(env, y), prod(env, b1))

def mmul_ok(+env: List<&2, Nat>, m1: Mono, m2: Mono)
  -> {Nat.mul(evm(env, m1), evm(env, m2)) == evm(env, mmul(m1, m2)) : Nat}:
  match m1 m2:
    case M{+c1, +v1} M{+c2, +v2}:
      %vmerge_ok(env, v1, v2, hle(v1, v2))
        : {Nat.mul(Nat.mul(c1, prod(env, v1)), Nat.mul(c2, prod(env, v2)))
           == Nat.mul(Nat.mul(c1, c2), _) : Nat}
      mul_swap(c1, prod(env, v1), c2, prod(env, v2))

def pmono_ok(+env: List<&2, Nat>, +m: Mono, q: List<&2, Mono>)
  -> {Nat.mul(evm(env, m), evp(env, q)) == evp(env, pmono(m, q)) : Nat}:
  match q:
    case []:
      mul_zero(evm(env, m))
    case +n <> +q1:
      %padd_ok(env, [mmul(m, n)], pmono(m, q1), hcmp([mmul(m, n)], pmono(m, q1)), {==})
        : {Nat.mul(evm(env, m), Nat.add(evm(env, n), evp(env, q1))) == _ : Nat}
      %pmono_ok(env, m, q1)
        : {Nat.mul(evm(env, m), Nat.add(evm(env, n), evp(env, q1)))
           == Nat.add(Nat.add(evm(env, mmul(m, n)), 0n), _) : Nat}
      %mmul_ok(env, m, n)
        : {Nat.mul(evm(env, m), Nat.add(evm(env, n), evp(env, q1)))
           == Nat.add(Nat.add(_, 0n), Nat.mul(evm(env, m), evp(env, q1))) : Nat}
      %add_zero_s(Nat.mul(evm(env, m), evm(env, n)))
        : {Nat.mul(evm(env, m), Nat.add(evm(env, n), evp(env, q1)))
           == Nat.add(_, Nat.mul(evm(env, m), evp(env, q1))) : Nat}
      mul_add_l(evm(env, m), evm(env, n), evp(env, q1))

def pmul_ok(+env: List<&2, Nat>, p: List<&2, Mono>, +q: List<&2, Mono>)
  -> {Nat.mul(evp(env, p), evp(env, q)) == evp(env, pmul(p, q)) : Nat}:
  match p:
    case []:
      {==}
    case +m <> +p1:
      %padd_ok(env, pmono(m, q), pmul(p1, q), hcmp(pmono(m, q), pmul(p1, q)), {==})
        : {Nat.mul(Nat.add(evm(env, m), evp(env, p1)), evp(env, q)) == _ : Nat}
      %pmono_ok(env, m, q)
        : {Nat.mul(Nat.add(evm(env, m), evp(env, p1)), evp(env, q))
           == Nat.add(_, evp(env, pmul(p1, q))) : Nat}
      %pmul_ok(env, p1, q)
        : {Nat.mul(Nat.add(evm(env, m), evp(env, p1)), evp(env, q))
           == Nat.add(Nat.mul(evm(env, m), evp(env, q)), _) : Nat}
      mul_add_r(evm(env, m), evp(env, p1), evp(env, q))

def norm_ok(+env: List<&2, Nat>, e: Ex) -> {ev(env, e) == evp(env, norm(e)) : Nat}:
  match e:
    case V{+i}:
      %add_zero_s(Nat.mul(1n, Nat.mul(at(env, i), 1n))) : {at(env, i) == _ : Nat}
      %one_mul_s(Nat.mul(at(env, i), 1n)) : {at(env, i) == _ : Nat}
      mul_one_s(at(env, i))
    case N{+n}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          %add_zero_s(Nat.mul(1n+k, 1n)) : {1n+k == _ : Nat}
          mul_one_s(1n+k)
    case Add{+a, +b}:
      %padd_ok(env, norm(a), norm(b), hcmp(norm(a), norm(b)), {==})
        : {Nat.add(ev(env, a), ev(env, b)) == _ : Nat}
      %norm_ok(env, a) : {Nat.add(ev(env, a), ev(env, b)) == Nat.add(_, evp(env, norm(b))) : Nat}
      %norm_ok(env, b) : {Nat.add(ev(env, a), ev(env, b)) == Nat.add(ev(env, a), _) : Nat}
      {==}
    case Mul{+a, +b}:
      %pmul_ok(env, norm(a), norm(b))
        : {Nat.mul(ev(env, a), ev(env, b)) == _ : Nat}
      %norm_ok(env, a) : {Nat.mul(ev(env, a), ev(env, b)) == Nat.mul(_, evp(env, norm(b))) : Nat}
      %norm_ok(env, b) : {Nat.mul(ev(env, a), ev(env, b)) == Nat.mul(ev(env, a), _) : Nat}
      {==}

def eq_r(+env: List<&2, Nat>, +a: Ex, +b: Ex, h: {norm(b) == norm(a) : List<&2, Mono>})
  -> {ev(env, b) == evp(env, norm(a)) : Nat}:
  %h : {ev(env, b) == evp(env, _) : Nat}
  norm_ok(env, b)

# The tactic: equal normal forms, equal values. Use as
#   eq([x, y, ..], lhs, rhs, {==})
# where lhs and rhs are the two sides written over V{0n}, V{1n}, ..
def eq(+env: List<&2, Nat>, +a: Ex, +b: Ex, h: {norm(b) == norm(a) : List<&2, Mono>})
  -> {ev(env, a) == ev(env, b) : Nat}:
  Equal.trans(Nat, ev(env, a), evp(env, norm(a)), ev(env, b), norm_ok(env, a),
    Equal.sym(Nat, ev(env, b), evp(env, norm(a)), eq_r(env, a, b, h)))
