# Cubo -- the proofs. Every law of LAWS.bend, filled. Polynomial
# identities go through ring.bend's tactic (R.eq); the rest follows the
# code: every decision it makes is a Bool passed to a helper, and each
# lemma here takes that Bool as a parameter, with how it was computed.

import Base
import ./ring.bend as R
import ./phys.bend as P
import ./LAWS.bend as Laws

# Kit
# ---

# True is not False
def D(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def clash(e: {True{} == False{} : Bool}) -> Empty:
  %e : D(_)
  Unit{}

def clash2(e: {False{} == True{} : Bool}) -> Empty:
  clash(Equal.sym(Bool, False{}, True{}, e))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, clash2(e))

# a <= a + w
def le_add(+a: Nat, +w: Nat) -> {Nat.is_le(a, Nat.add(a, w)) == True{} : Bool}:
  match a:
    case 0n:
      match w:
        case 0n:
          {==}
        case 1n+v:
          {==}
    case 1n+p:
      le_add(p, w)

# x + w == y gives x <= y
def le_of(+x: Nat, +w: Nat, -y: Nat, h: {Nat.add(x, w) == y : Nat}) -> {Nat.is_le(x, y) == True{} : Bool}:
  %h : {Nat.is_le(x, _) == True{} : Bool}
  le_add(x, w)

def le_refl(+x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  le_of(x, 0n, x, R.add_zero(x))

# a <= b gives a + (b - a) == b
def sub_add(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, clash2(h))
    case 1n+p 1n+q:
      %sub_add(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

def eq_of(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, clash2(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, clash2(h))
    case 1n+p 1n+q:
      %eq_of(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# Pushes: momentum and energy
# ---------------------------
# A share's gate gives d = e + e + j and lo + d = hi; the sizes before are
# lo and hi (either order). Same direction: the two leave with lo + e and
# lo + e + j. Opposite: with e and e + j.

# the sign of a size
def Zs(pos: Bool, +n: Nat) -> P.Z:
  match pos:
    case True{}:
      P.Pos{n}
    case False{}:
      P.Neg{n}

# the momentum equation for a -> a2, b -> b2
def Mom(a: P.Z, b: P.Z, s: P.Z & P.Z) -> Type:
  {Nat.add(Nat.add(P.Z.pos(P.Share.fst(s)), P.Z.pos(P.Share.snd(s))), Nat.add(P.Z.neg(a), P.Z.neg(b)))
    == Nat.add(Nat.add(P.Z.pos(a), P.Z.pos(b)), Nat.add(P.Z.neg(P.Share.fst(s)), P.Z.neg(P.Share.snd(s)))) : Nat}

# the kinetic energy after is at most before
def Ken(a: P.Z, b: P.Z, s: P.Z & P.Z) -> Type:
  {Nat.is_le(Nat.add(P.Z.sq(P.Share.fst(s)), P.Z.sq(P.Share.snd(s))), Nat.add(P.Z.sq(a), P.Z.sq(b))) == True{} : Bool}

def same_core(+lo: Nat, +hi: Nat, +p: Nat, +q: Nat, +d: Nat, +e: Nat,
  ga: {Nat.add(Nat.add(e, e), Nat.sub(d, Nat.add(e, e))) == d : Nat}, gb: {Nat.add(lo, d) == hi : Nat},
  hpq: {Nat.add(lo, hi) == Nat.add(p, q) : Nat})
  -> {Nat.add(Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))) == Nat.add(p, q) : Nat}:
  %hpq : {Nat.add(Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))) == _ : Nat}
  %gb : {Nat.add(Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))) == Nat.add(lo, _) : Nat}
  %ga : {Nat.add(Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))) == Nat.add(lo, Nat.add(lo, _)) : Nat}
  R.eq([lo, e, Nat.sub(d, Nat.add(e, e))],
    R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}},
    R.Add{R.V{0n}, R.Add{R.V{0n}, R.Add{R.Add{R.V{1n}, R.V{1n}}, R.V{2n}}}},
    {==})

# lo + (e + (e + j)) == hi: what is left after opposite pushes
def opp_core(+lo: Nat, +hi: Nat, +d: Nat, +e: Nat,
  ga: {Nat.add(Nat.add(e, e), Nat.sub(d, Nat.add(e, e))) == d : Nat}, gb: {Nat.add(lo, d) == hi : Nat})
  -> {Nat.add(lo, Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))) == hi : Nat}:
  %gb : {Nat.add(lo, Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))) == _ : Nat}
  %ga : {Nat.add(lo, Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))) == Nat.add(lo, _) : Nat}
  R.eq([lo, e, Nat.sub(d, Nat.add(e, e))],
    R.Add{R.V{0n}, R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}},
    R.Add{R.V{0n}, R.Add{R.Add{R.V{1n}, R.V{1n}}, R.V{2n}}},
    {==})

# the gate passed: the sizes after add up to the sizes before
def same_gate(+p: Nat, +q: Nat, +lo: Nat, +hi: Nat, +d: Nat, +e: Nat,
  +eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)) == True{} : Bool},
  hpq: {Nat.add(lo, hi) == Nat.add(p, q) : Nat})
  -> {Nat.add(Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))) == Nat.add(p, q) : Nat}:
  same_core(lo, hi, p, q, d, e,
    sub_add(Nat.add(e, e), d, and_l(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok)),
    eq_of(Nat.add(lo, d), hi, and_r(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok)), hpq)

def same_chk_mom(ok: Bool, pos: Bool, +p: Nat, +q: Nat, +lo: Nat, +hi: Nat, +d: Nat, +e: Nat,
  eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)) == ok : Bool},
  hpq: {Nat.add(lo, hi) == Nat.add(p, q) : Nat})
  -> Mom(Zs(pos, p), Zs(pos, q), P.Share.sign(pos, P.Share.chk(ok, p, q, Nat.add(lo, e),
       Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))))):
  match ok pos:
    case True{} True{}:
      %same_gate(p, q, lo, hi, d, e, eok, hpq)
        : {Nat.add(Nat.add(Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))), 0n) == Nat.add(_, 0n) : Nat}
      {==}
    case True{} False{}:
      Equal.sym(Nat, Nat.add(Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))), Nat.add(p, q),
        same_gate(p, q, lo, hi, d, e, eok, hpq))
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def same_mom(le: Bool, pos: Bool, +p: Nat, +q: Nat) -> Mom(Zs(pos, p), Zs(pos, q), P.Share.same(le, pos, p, q)):
  match le:
    case True{}:
      same_chk_mom(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(q, p), 2n), Nat.div(Nat.sub(q, p), 2n)), Nat.sub(q, p)),
          Nat.is_eq(Nat.add(p, Nat.sub(q, p)), q)),
        pos, p, q, p, q, Nat.sub(q, p), Nat.div(Nat.sub(q, p), 2n), {==}, {==})
    case False{}:
      same_chk_mom(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(p, q), 2n), Nat.div(Nat.sub(p, q), 2n)), Nat.sub(p, q)),
          Nat.is_eq(Nat.add(q, Nat.sub(p, q)), p)),
        pos, p, q, q, p, Nat.sub(p, q), Nat.div(Nat.sub(p, q), 2n), {==}, R.add_comm(q, p))

# the gate passed, opposite directions: lo + (e + (e + j)) == hi
def opp_gate(+lo: Nat, +hi: Nat, +d: Nat, +e: Nat,
  +eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)) == True{} : Bool})
  -> {Nat.add(lo, Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))) == hi : Nat}:
  opp_core(lo, hi, d, e,
    sub_add(Nat.add(e, e), d, and_l(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok)),
    eq_of(Nat.add(lo, d), hi, and_r(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok)))

# +p against -q, p <= q: both leave backwards
def opp_tt_mom(ok: Bool, +p: Nat, +q: Nat, +d: Nat, +e: Nat,
  eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(p, d), q)) == ok : Bool})
  -> Mom(P.Pos{p}, P.Neg{q}, P.Share.flip(ok, False{}, True{}, p, q, e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))):
  match ok:
    case True{}:
      %opp_gate(p, q, d, e, eok)
        : {_ == Nat.add(Nat.add(p, 0n), Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))) : Nat}
      R.eq([p, e, Nat.sub(d, Nat.add(e, e))],
        R.Add{R.V{0n}, R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}},
        R.Add{R.Add{R.V{0n}, R.N{0n}}, R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}},
        {==})
    case False{}:
      {==}

# -p against +q, p <= q: both leave forwards
def opp_tf_mom(ok: Bool, +p: Nat, +q: Nat, +d: Nat, +e: Nat,
  eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(p, d), q)) == ok : Bool})
  -> Mom(P.Neg{p}, P.Pos{q}, P.Share.flip(ok, True{}, False{}, p, q, e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))):
  match ok:
    case True{}:
      %opp_gate(p, q, d, e, eok)
        : {Nat.add(Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e)))), Nat.add(p, 0n)) == Nat.add(_, 0n) : Nat}
      R.eq([p, e, Nat.sub(d, Nat.add(e, e))],
        R.Add{R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}, R.Add{R.V{0n}, R.N{0n}}},
        R.Add{R.Add{R.V{0n}, R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}}, R.N{0n}},
        {==})
    case False{}:
      {==}

# +p against -q, p > q: both leave forwards
def opp_ft_mom(ok: Bool, +p: Nat, +q: Nat, +d: Nat, +e: Nat,
  eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(q, d), p)) == ok : Bool})
  -> Mom(P.Pos{p}, P.Neg{q}, P.Share.flip(ok, True{}, True{}, p, q, e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))):
  match ok:
    case True{}:
      %opp_gate(q, p, d, e, eok)
        : {Nat.add(Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e)))), q) == Nat.add(Nat.add(_, 0n), 0n) : Nat}
      R.eq([q, e, Nat.sub(d, Nat.add(e, e))],
        R.Add{R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}, R.V{0n}},
        R.Add{R.Add{R.Add{R.V{0n}, R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}}, R.N{0n}}, R.N{0n}},
        {==})
    case False{}:
      {==}

# -p against +q, p > q: both leave backwards
def opp_ff_mom(ok: Bool, +p: Nat, +q: Nat, +d: Nat, +e: Nat,
  eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(q, d), p)) == ok : Bool})
  -> Mom(P.Neg{p}, P.Pos{q}, P.Share.flip(ok, False{}, False{}, p, q, e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))):
  match ok:
    case True{}:
      %opp_gate(q, p, d, e, eok)
        : {Nat.add(_, 0n) == Nat.add(q, Nat.add(e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))) : Nat}
      R.eq([q, e, Nat.sub(d, Nat.add(e, e))],
        R.Add{R.Add{R.V{0n}, R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}}, R.N{0n}},
        R.Add{R.V{0n}, R.Add{R.V{1n}, R.Add{R.V{1n}, R.V{2n}}}},
        {==})
    case False{}:
      {==}

def opp_mom(le: Bool, pos: Bool, +p: Nat, +q: Nat) -> Mom(Zs(pos, p), Zs(Bool.not(pos), q), P.Share.opp(le, pos, p, q)):
  match le pos:
    case True{} True{}:
      opp_tt_mom(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(q, p), 2n), Nat.div(Nat.sub(q, p), 2n)), Nat.sub(q, p)),
          Nat.is_eq(Nat.add(p, Nat.sub(q, p)), q)), p, q, Nat.sub(q, p), Nat.div(Nat.sub(q, p), 2n), {==})
    case True{} False{}:
      opp_tf_mom(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(q, p), 2n), Nat.div(Nat.sub(q, p), 2n)), Nat.sub(q, p)),
          Nat.is_eq(Nat.add(p, Nat.sub(q, p)), q)), p, q, Nat.sub(q, p), Nat.div(Nat.sub(q, p), 2n), {==})
    case False{} True{}:
      opp_ft_mom(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(p, q), 2n), Nat.div(Nat.sub(p, q), 2n)), Nat.sub(p, q)),
          Nat.is_eq(Nat.add(q, Nat.sub(p, q)), p)), p, q, Nat.sub(p, q), Nat.div(Nat.sub(p, q), 2n), {==})
    case False{} False{}:
      opp_ff_mom(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(p, q), 2n), Nat.div(Nat.sub(p, q), 2n)), Nat.sub(p, q)),
          Nat.is_eq(Nat.add(q, Nat.sub(p, q)), p)), p, q, Nat.sub(p, q), Nat.div(Nat.sub(p, q), 2n), {==})

def Laws.push_momentum(a, b):
  match a b:
    case P.Pos{+p} P.Pos{+q}:
      same_mom(Nat.is_le(p, q), True{}, p, q)
    case P.Neg{+p} P.Neg{+q}:
      same_mom(Nat.is_le(p, q), False{}, p, q)
    case P.Pos{+p} P.Neg{+q}:
      opp_mom(Nat.is_le(p, q), True{}, p, q)
    case P.Neg{+p} P.Pos{+q}:
      opp_mom(Nat.is_le(p, q), False{}, p, q)

# the energy a same-direction share spends: 2 e^2 + 2 e j
def Wsame(+e: Nat, +j: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(e, e), Nat.mul(e, e)), Nat.add(Nat.mul(e, j), Nat.mul(e, j)))

# and an opposite one: 2 lo^2 + 2 e^2 + 4 lo e + 2 lo j + 2 e j
def Wopp(+lo: Nat, +e: Nat, +j: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.mul(lo, lo), Nat.mul(lo, lo)), Nat.add(Nat.mul(e, e), Nat.mul(e, e))),
    Nat.add(Nat.add(Nat.add(Nat.mul(lo, e), Nat.mul(lo, e)), Nat.add(Nat.mul(lo, e), Nat.mul(lo, e))),
      Nat.add(Nat.add(Nat.mul(lo, j), Nat.mul(lo, j)), Nat.add(Nat.mul(e, j), Nat.mul(e, j)))))

def same_ken_eq(+lo: Nat, +hi: Nat, +p: Nat, +q: Nat, +d: Nat, +e: Nat,
  +eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)) == True{} : Bool},
  hsq: {Nat.add(Nat.mul(lo, lo), Nat.mul(hi, hi)) == Nat.add(Nat.mul(p, p), Nat.mul(q, q)) : Nat})
  -> {Nat.add(Nat.add(Nat.mul(Nat.add(lo, e), Nat.add(lo, e)),
        Nat.mul(Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))))),
        Wsame(e, Nat.sub(d, Nat.add(e, e))))
      == Nat.add(Nat.mul(p, p), Nat.mul(q, q)) : Nat}:
  %hsq : {Nat.add(Nat.add(Nat.mul(Nat.add(lo, e), Nat.add(lo, e)),
        Nat.mul(Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))))),
        Wsame(e, Nat.sub(d, Nat.add(e, e)))) == _ : Nat}
  %eq_of(Nat.add(lo, d), hi, and_r(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok))
    : {Nat.add(Nat.add(Nat.mul(Nat.add(lo, e), Nat.add(lo, e)),
        Nat.mul(Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))))),
        Wsame(e, Nat.sub(d, Nat.add(e, e)))) == Nat.add(Nat.mul(lo, lo), Nat.mul(_, _)) : Nat}
  %sub_add(Nat.add(e, e), d, and_l(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok))
    : {Nat.add(Nat.add(Nat.mul(Nat.add(lo, e), Nat.add(lo, e)),
        Nat.mul(Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))))),
        Wsame(e, Nat.sub(d, Nat.add(e, e)))) == Nat.add(Nat.mul(lo, lo), Nat.mul(Nat.add(lo, _), Nat.add(lo, _))) : Nat}
  R.eq([lo, e, Nat.sub(d, Nat.add(e, e))],
    R.Add{R.Add{R.Mul{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.V{0n}, R.V{1n}}},
                R.Mul{R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}, R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}}},
          R.Add{R.Add{R.Mul{R.V{1n}, R.V{1n}}, R.Mul{R.V{1n}, R.V{1n}}}, R.Add{R.Mul{R.V{1n}, R.V{2n}}, R.Mul{R.V{1n}, R.V{2n}}}}},
    R.Add{R.Mul{R.V{0n}, R.V{0n}},
          R.Mul{R.Add{R.V{0n}, R.Add{R.Add{R.V{1n}, R.V{1n}}, R.V{2n}}}, R.Add{R.V{0n}, R.Add{R.Add{R.V{1n}, R.V{1n}}, R.V{2n}}}}},
    {==})

def opp_ken_eq(+lo: Nat, +hi: Nat, +p: Nat, +q: Nat, +d: Nat, +e: Nat,
  +eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)) == True{} : Bool},
  hsq: {Nat.add(Nat.mul(lo, lo), Nat.mul(hi, hi)) == Nat.add(Nat.mul(p, p), Nat.mul(q, q)) : Nat})
  -> {Nat.add(Nat.add(Nat.mul(e, e),
        Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e))))
      == Nat.add(Nat.mul(p, p), Nat.mul(q, q)) : Nat}:
  %hsq : {Nat.add(Nat.add(Nat.mul(e, e),
        Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e)))) == _ : Nat}
  %eq_of(Nat.add(lo, d), hi, and_r(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok))
    : {Nat.add(Nat.add(Nat.mul(e, e),
        Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e)))) == Nat.add(Nat.mul(lo, lo), Nat.mul(_, _)) : Nat}
  %sub_add(Nat.add(e, e), d, and_l(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi), eok))
    : {Nat.add(Nat.add(Nat.mul(e, e),
        Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e)))) == Nat.add(Nat.mul(lo, lo), Nat.mul(Nat.add(lo, _), Nat.add(lo, _))) : Nat}
  R.eq([lo, e, Nat.sub(d, Nat.add(e, e))],
    R.Add{R.Add{R.Mul{R.V{1n}, R.V{1n}}, R.Mul{R.Add{R.V{1n}, R.V{2n}}, R.Add{R.V{1n}, R.V{2n}}}},
      R.Add{R.Add{R.Add{R.Mul{R.V{0n}, R.V{0n}}, R.Mul{R.V{0n}, R.V{0n}}}, R.Add{R.Mul{R.V{1n}, R.V{1n}}, R.Mul{R.V{1n}, R.V{1n}}}},
        R.Add{R.Add{R.Add{R.Mul{R.V{0n}, R.V{1n}}, R.Mul{R.V{0n}, R.V{1n}}}, R.Add{R.Mul{R.V{0n}, R.V{1n}}, R.Mul{R.V{0n}, R.V{1n}}}},
          R.Add{R.Add{R.Mul{R.V{0n}, R.V{2n}}, R.Mul{R.V{0n}, R.V{2n}}}, R.Add{R.Mul{R.V{1n}, R.V{2n}}, R.Mul{R.V{1n}, R.V{2n}}}}}}},
    R.Add{R.Mul{R.V{0n}, R.V{0n}},
          R.Mul{R.Add{R.V{0n}, R.Add{R.Add{R.V{1n}, R.V{1n}}, R.V{2n}}}, R.Add{R.V{0n}, R.Add{R.Add{R.V{1n}, R.V{1n}}, R.V{2n}}}}},
    {==})

def same_chk_ken(ok: Bool, pos: Bool, +p: Nat, +q: Nat, +lo: Nat, +hi: Nat, +d: Nat, +e: Nat,
  eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)) == ok : Bool},
  hsq: {Nat.add(Nat.mul(lo, lo), Nat.mul(hi, hi)) == Nat.add(Nat.mul(p, p), Nat.mul(q, q)) : Nat})
  -> Ken(Zs(pos, p), Zs(pos, q), P.Share.sign(pos, P.Share.chk(ok, p, q, Nat.add(lo, e),
       Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))))):
  match ok pos:
    case True{} True{}:
      le_of(Nat.add(Nat.mul(Nat.add(lo, e), Nat.add(lo, e)),
          Nat.mul(Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))))),
        Wsame(e, Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.mul(p, p), Nat.mul(q, q)), same_ken_eq(lo, hi, p, q, d, e, eok, hsq))
    case True{} False{}:
      le_of(Nat.add(Nat.mul(Nat.add(lo, e), Nat.add(lo, e)),
          Nat.mul(Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e))))),
        Wsame(e, Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.mul(p, p), Nat.mul(q, q)), same_ken_eq(lo, hi, p, q, d, e, eok, hsq))
    case False{} True{}:
      le_refl(Nat.add(Nat.mul(p, p), Nat.mul(q, q)))
    case False{} False{}:
      le_refl(Nat.add(Nat.mul(p, p), Nat.mul(q, q)))

def opp_chk_ken(ok: Bool, up: Bool, pos: Bool, +p: Nat, +q: Nat, +lo: Nat, +hi: Nat, +d: Nat, +e: Nat,
  eok: {Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)) == ok : Bool},
  hsq: {Nat.add(Nat.mul(lo, lo), Nat.mul(hi, hi)) == Nat.add(Nat.mul(p, p), Nat.mul(q, q)) : Nat})
  -> Ken(Zs(pos, p), Zs(Bool.not(pos), q), P.Share.flip(ok, up, pos, p, q, e, Nat.add(e, Nat.sub(d, Nat.add(e, e))))):
  match ok up pos:
    case True{} True{} True{}:
      le_of(Nat.add(Nat.mul(e, e), Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.mul(p, p), Nat.mul(q, q)), opp_ken_eq(lo, hi, p, q, d, e, eok, hsq))
    case True{} True{} False{}:
      le_of(Nat.add(Nat.mul(e, e), Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.mul(p, p), Nat.mul(q, q)), opp_ken_eq(lo, hi, p, q, d, e, eok, hsq))
    case True{} False{} True{}:
      le_of(Nat.add(Nat.mul(e, e), Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.mul(p, p), Nat.mul(q, q)), opp_ken_eq(lo, hi, p, q, d, e, eok, hsq))
    case True{} False{} False{}:
      le_of(Nat.add(Nat.mul(e, e), Nat.mul(Nat.add(e, Nat.sub(d, Nat.add(e, e))), Nat.add(e, Nat.sub(d, Nat.add(e, e))))),
        Wopp(lo, e, Nat.sub(d, Nat.add(e, e))), Nat.add(Nat.mul(p, p), Nat.mul(q, q)), opp_ken_eq(lo, hi, p, q, d, e, eok, hsq))
    case False{} _ True{}:
      le_refl(Nat.add(Nat.mul(p, p), Nat.mul(q, q)))
    case False{} _ False{}:
      le_refl(Nat.add(Nat.mul(p, p), Nat.mul(q, q)))

def same_ken(le: Bool, pos: Bool, +p: Nat, +q: Nat) -> Ken(Zs(pos, p), Zs(pos, q), P.Share.same(le, pos, p, q)):
  match le:
    case True{}:
      same_chk_ken(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(q, p), 2n), Nat.div(Nat.sub(q, p), 2n)), Nat.sub(q, p)),
          Nat.is_eq(Nat.add(p, Nat.sub(q, p)), q)),
        pos, p, q, p, q, Nat.sub(q, p), Nat.div(Nat.sub(q, p), 2n), {==}, {==})
    case False{}:
      same_chk_ken(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(p, q), 2n), Nat.div(Nat.sub(p, q), 2n)), Nat.sub(p, q)),
          Nat.is_eq(Nat.add(q, Nat.sub(p, q)), p)),
        pos, p, q, q, p, Nat.sub(p, q), Nat.div(Nat.sub(p, q), 2n), {==}, R.add_comm(Nat.mul(q, q), Nat.mul(p, p)))

def opp_ken(le: Bool, +pos: Bool, +p: Nat, +q: Nat) -> Ken(Zs(pos, p), Zs(Bool.not(pos), q), P.Share.opp(le, pos, p, q)):
  match le:
    case True{}:
      opp_chk_ken(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(q, p), 2n), Nat.div(Nat.sub(q, p), 2n)), Nat.sub(q, p)),
          Nat.is_eq(Nat.add(p, Nat.sub(q, p)), q)),
        Bool.xor(True{}, pos), pos, p, q, p, q, Nat.sub(q, p), Nat.div(Nat.sub(q, p), 2n), {==}, {==})
    case False{}:
      opp_chk_ken(Bool.and(Nat.is_le(Nat.add(Nat.div(Nat.sub(p, q), 2n), Nat.div(Nat.sub(p, q), 2n)), Nat.sub(p, q)),
          Nat.is_eq(Nat.add(q, Nat.sub(p, q)), p)),
        Bool.xor(False{}, pos), pos, p, q, q, p, Nat.sub(p, q), Nat.div(Nat.sub(p, q), 2n), {==},
        R.add_comm(Nat.mul(q, q), Nat.mul(p, p)))

def Laws.push_energy(a, b):
  match a b:
    case P.Pos{+p} P.Pos{+q}:
      same_ken(Nat.is_le(p, q), True{}, p, q)
    case P.Neg{+p} P.Neg{+q}:
      same_ken(Nat.is_le(p, q), False{}, p, q)
    case P.Pos{+p} P.Neg{+q}:
      opp_ken(Nat.is_le(p, q), True{}, p, q)
    case P.Neg{+p} P.Pos{+q}:
      opp_ken(Nat.is_le(p, q), False{}, p, q)

# Contact
# -------
# A tick records a contact (hit) as soon as a gate turns a move back, and
# nothing after clears it: so a tick that ends untouched took the free
# branch of every gate.

def hit_land(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +fl: Nat, +vx: P.Z, +vz: P.Z)
  -> {P.Body.hit(P.Move.land(ok, x, y, z, fl, vx, vz)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_rise(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z)
  -> {P.Body.hit(P.Move.rise(ok, x, y, z, p, vx, v, vz, True{})) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_fall(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +fl: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z)
  -> {P.Body.hit(P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, True{})) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      hit_land(Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), x, y, z, fl, vx, vz)

def hit_fly(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, st: P.Z & P.Z)
  -> {P.Body.hit(P.Move.fly(s, obs, x, y, z, vx, vz, True{}, st)) == True{} : Bool}:
  (v, d) = st
  match d:
    case P.Pos{+p}:
      hit_rise(P.Geo.free(s, x, Nat.add(y, p), z, obs), x, y, z, p, vx, v, vz)
    case P.Neg{+q}:
      hit_fall(s, Bool.and(Nat.is_le(Nat.add(P.Geo.floor(s, x, y, z, obs, 0n), q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)),
        obs, x, y, z, q, P.Geo.floor(s, x, y, z, obs, 0n), vx, v, vz)

def hit_y(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, gr: Bool)
  -> {P.Body.hit(P.Move.y(s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, True{}})) == True{} : Bool}:
  match gr:
    case True{}:
      {==}
    case False{}:
      hit_fly(s, obs, x, y, z, vx, vz, P.Fly.step(g, vy))

def hit_ty(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: {P.Body.hit(P.Tick.body(r)) == True{} : Bool})
  -> {P.Body.hit(P.Tick.body(P.Tick.y(s, g, r))) == True{} : Bool}:
  (b, +obs) = r
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, hit} = b
  match hit:
    case True{}:
      hit_y(s, g, obs, x, y, z, vx, vy, vz, gr)
    case False{}:
      Empty.absurd({P.Body.hit(P.Tick.body(P.Tick.y(s, g, (P.Body{x, y, z, vx, vy, vz, gr, False{}}, obs)))) == True{} : Bool},
        clash2(h))

def hit_zput(ok: Bool, +obs: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z, +gr: Bool)
  -> {P.Body.hit(P.Tick.body(P.Move.zput(ok, obs, cz, x, y, z, vx, vy, v, gr))) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_zhit(+s: Nat, r: P.Pushed, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +gr: Bool)
  -> {P.Body.hit(P.Tick.body(P.Move.zhit(s, r, x, y, z, vx, vy, gr))) == True{} : Bool}:
  P.Pushed{+v, +obs, at} = r
  match at:
    case None{}:
      {==}
    case Some{+cz}:
      hit_zput(P.Geo.free(s, x, y, cz, obs), obs, cz, x, y, z, vx, vy, v, gr)

def hit_xput(ok: Bool, +obs: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool)
  -> {P.Body.hit(P.Tick.body(P.Move.xput(ok, obs, cx, x, y, z, v, vy, vz, gr))) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_xhit(+s: Nat, r: P.Pushed, +x: Nat, +y: Nat, +z: Nat, +vy: P.Z, +vz: P.Z, +gr: Bool)
  -> {P.Body.hit(P.Tick.body(P.Move.xhit(s, r, x, y, z, vy, vz, gr))) == True{} : Bool}:
  P.Pushed{+v, +obs, at} = r
  match at:
    case None{}:
      {==}
    case Some{+cx}:
      hit_xput(P.Geo.free(s, cx, y, z, obs), obs, cx, x, y, z, v, vy, vz, gr)

def hit_zgo(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool) -> {P.Body.hit(P.Tick.body(P.Move.zgo(s, ok, obs, d, cz, x, y, z, vx, vy, vz, gr, True{}))) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      hit_zhit(s, P.Push.z(s, obs, d, x, y, cz, vz, P.Geo.head(s, x, y, cz, obs)), x, y, z, vx, vy, gr)

def hit_tz(+s: Nat, +g: Nat, +v0: P.Z, r: P.Body & List<&2, P.Body>, h: {P.Body.hit(P.Tick.body(r)) == True{} : Bool})
  -> {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0, r))) == True{} : Bool}:
  (b, +obs) = r
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, hit} = b
  match hit:
    case True{}:
      hit_ty(s, g, P.Move.z(s, obs, v0, P.Body{x, y, z, vx, vy, vz, gr, True{}}),
        hit_zgo(s, Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), obs)),
          obs, P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr))
    case False{}:
      Empty.absurd({P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0, (P.Body{x, y, z, vx, vy, vz, gr, False{}}, obs)))) == True{} : Bool},
        clash2(h))

# fl + q <= y gives q <= y
def le_addl(+fl: Nat, +q: Nat, +y: Nat, h: {Nat.is_le(Nat.add(fl, q), y) == True{} : Bool}) -> {Nat.is_le(q, y) == True{} : Bool}:
  le_of(q, Nat.add(fl, Nat.sub(y, Nat.add(fl, q))), y,
    %sub_add(Nat.add(fl, q), y, h) : {Nat.add(q, Nat.add(fl, Nat.sub(y, Nat.add(fl, q)))) == _ : Nat}
    R.eq([q, fl, Nat.sub(y, Nat.add(fl, q))],
      R.Add{R.V{0n}, R.Add{R.V{1n}, R.V{2n}}}, R.Add{R.Add{R.V{1n}, R.V{0n}}, R.V{2n}}, {==}))

# True == False from a hit that was True
def unhit(-a: Bool, h: {a == True{} : Bool}, f: {a == False{} : Bool}) -> Empty:
  clash(Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), f))

# The free path, in the air
# -------------------------
# An untouched tick in the air ends where the free moves put it, and none
# of them ran past the wall at 0.

def Free(+g: Nat, +x: Nat, +y: Nat, +z: Nat, +dx: P.Z, +dz: P.Z, +vx: P.Z, +vy: P.Z, +vz: P.Z) -> P.Body:
  P.Body{P.Z.shift(x, dx), P.Z.shift(y, P.Share.snd(P.Fly.step(g, vy))), P.Z.shift(z, dz), vx,
    P.Share.fst(P.Fly.step(g, vy)), vz, False{}, False{}}

def y_rise_eq(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  free: {P.Body.hit(P.Move.rise(ok, x, y, z, p, vx, v, vz, False{})) == False{} : Bool})
  -> {P.Body{x, Nat.add(y, p), z, vx, v, vz, False{}, False{}} == P.Move.rise(ok, x, y, z, p, vx, v, vz, False{}) : P.Body}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({P.Body{x, Nat.add(y, p), z, vx, v, vz, False{}, False{}} == P.Body{x, y, z, vx, P.Pos{0n}, vz, False{}, True{}} : P.Body},
        clash(free))

def y_fall_eq(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +fl: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  free: {P.Body.hit(P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, False{})) == False{} : Bool})
  -> {P.Body{x, Nat.sub(y, q), z, vx, v, vz, False{}, False{}} == P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, False{}) : P.Body}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({P.Body{x, Nat.sub(y, q), z, vx, v, vz, False{}, False{}}
          == P.Move.land(Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), x, y, z, fl, vx, vz) : P.Body},
        unhit(P.Body.hit(P.Move.land(Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), x, y, z, fl, vx, vz)),
          hit_land(Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), x, y, z, fl, vx, vz), free))

def y_eq(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, st: P.Z & P.Z,
  free: {P.Body.hit(P.Move.fly(s, obs, x, y, z, vx, vz, False{}, st)) == False{} : Bool})
  -> {P.Body{x, P.Z.shift(y, P.Share.snd(st)), z, vx, P.Share.fst(st), vz, False{}, False{}}
      == P.Move.fly(s, obs, x, y, z, vx, vz, False{}, st) : P.Body}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      y_rise_eq(P.Geo.free(s, x, Nat.add(y, p), z, obs), x, y, z, p, vx, v, vz, free)
    case P.Neg{+q}:
      y_fall_eq(s, Bool.and(Nat.is_le(Nat.add(P.Geo.floor(s, x, y, z, obs, 0n), q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)),
        obs, x, y, z, q, P.Geo.floor(s, x, y, z, obs, 0n), vx, v, vz, free)

def y_fall_ok(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +fl: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  eok: {Bool.and(Nat.is_le(Nat.add(fl, q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)) == ok : Bool},
  free: {P.Body.hit(P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, False{})) == False{} : Bool})
  -> {Nat.is_le(q, y) == True{} : Bool}:
  match ok:
    case True{}:
      le_addl(fl, q, y, and_l(Nat.is_le(Nat.add(fl, q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs), eok))
    case False{}:
      Empty.absurd({Nat.is_le(q, y) == True{} : Bool},
        unhit(P.Body.hit(P.Move.land(Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), x, y, z, fl, vx, vz)),
          hit_land(Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), x, y, z, fl, vx, vz), free))

def y_ok(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, st: P.Z & P.Z,
  free: {P.Body.hit(P.Move.fly(s, obs, x, y, z, vx, vz, False{}, st)) == False{} : Bool})
  -> {P.Z.fits(y, P.Share.snd(st)) == True{} : Bool}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      {==}
    case P.Neg{+q}:
      y_fall_ok(s, Bool.and(Nat.is_le(Nat.add(P.Geo.floor(s, x, y, z, obs, 0n), q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)),
        obs, x, y, z, q, P.Geo.floor(s, x, y, z, obs, 0n), vx, v, vz, {==}, free)

# the z move, untouched
def Fz(+g: Nat, +x: Nat, +y: Nat, +z: Nat, +dz: P.Z, +vx: P.Z, +vy: P.Z, +vz: P.Z) -> P.Body:
  P.Body{x, P.Z.shift(y, P.Share.snd(P.Fly.step(g, vy))), P.Z.shift(z, dz), vx, P.Share.fst(P.Fly.step(g, vy)), vz, False{}, False{}}

def z_air_eq(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, False{}, False{}))))
    == False{} : Bool})
  -> {Fz(g, x, y, z, dz, vx, vy, vz)
      == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, False{}, False{}))) : P.Body}:
  match ok:
    case True{}:
      y_eq(s, obs, x, y, P.Z.shift(z, dz), vx, vz, P.Fly.step(g, vy), free)
    case False{}:
      Empty.absurd({Fz(g, x, y, z, dz, vx, vy, vz)
          == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, False{}, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, False{}, False{}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz,
              P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, False{})))),
          hit_ty(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)),
              x, y, z, vx, vy, False{}),
            hit_zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, False{})),
          free))

# the x move, untouched
def x_air_eq(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, False{}, False{}))))
    == False{} : Bool})
  -> {Fz(g, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz)
      == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, False{}, False{}))) : P.Body}:
  match ok:
    case True{}:
      z_air_eq(s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, free)
    case False{}:
      Empty.absurd({Fz(g, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz)
          == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, False{}, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, False{}, False{}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx,
              P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, False{})))),
          hit_tz(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)),
              x, y, z, vy, vz, False{}),
            hit_xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, False{})),
          free))

def z_air_ok(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  eok: {Bool.and(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, False{}, False{}))))
    == False{} : Bool})
  -> {Bool.and(P.Z.fits(z, dz), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Bool, P.Z.fits(z, dz), True{}, and_l(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), obs), eok))
        : {Bool.and(_, P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))) == True{} : Bool}
      y_ok(s, obs, x, y, P.Z.shift(z, dz), vx, vz, P.Fly.step(g, vy), free)
    case False{}:
      Empty.absurd({Bool.and(P.Z.fits(z, dz), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))) == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz,
              P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, False{})))),
          hit_ty(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)),
              x, y, z, vx, vy, False{}),
            hit_zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, False{})),
          free))

def x_air_ok(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  eok: {Bool.and(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, False{}, False{}))))
    == False{} : Bool})
  -> {Bool.and(P.Z.fits(x, dx), Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))))) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Bool, P.Z.fits(x, dx), True{}, and_l(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, obs), eok))
        : {Bool.and(_, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))))) == True{} : Bool}
      z_air_ok(s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, {==}, free)
    case False{}:
      Empty.absurd({Bool.and(P.Z.fits(x, dx), Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))))
          == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx,
              P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, False{})))),
          hit_tz(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)),
              x, y, z, vy, vz, False{}),
            hit_xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, False{})),
          free))

# Energy in flight
# ----------------

def lt_false_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, clash(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_false_le(p, q, h)

def lt_true_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, clash2(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, clash2(h))
    case 1n+p 1n+q:
      lt_true_le(p, q, h)

# the vertical energy of a tick of gravity: A and C are the horizontal
# terms (vx^2, vz^2), untouched
def fly_turn_e(lt: Bool, +g: Nat, +y: Nat, +s: Nat, +A: Nat, +C: Nat,
  h1: {Nat.add(s, Nat.sub(g, s)) == g : Nat}, elt: {Nat.is_lt(s, Nat.sub(g, s)) == lt : Bool},
  fy: {P.Z.fits(y, P.Z.diff(lt, s, Nat.sub(g, s))) == True{} : Bool})
  -> {Nat.add(Nat.add(Nat.add(A, Nat.mul(Nat.sub(g, s), Nat.sub(g, s))), C), Nat.mul(g, P.Z.shift(y, P.Z.diff(lt, s, Nat.sub(g, s)))))
      == Nat.add(Nat.add(Nat.add(A, Nat.mul(s, s)), C), Nat.mul(g, y)) : Nat}:
  match lt:
    case False{}:
      %h1 : {Nat.add(Nat.add(Nat.add(A, Nat.mul(Nat.sub(g, s), Nat.sub(g, s))), C), Nat.mul(_, Nat.add(y, Nat.sub(s, Nat.sub(g, s)))))
             == Nat.add(Nat.add(Nat.add(A, Nat.mul(s, s)), C), Nat.mul(_, y)) : Nat}
      %sub_add(Nat.sub(g, s), s, lt_false_le(s, Nat.sub(g, s), elt))
        : {Nat.add(Nat.add(Nat.add(A, Nat.mul(Nat.sub(g, s), Nat.sub(g, s))), C),
             Nat.mul(Nat.add(_, Nat.sub(g, s)), Nat.add(y, Nat.sub(s, Nat.sub(g, s)))))
           == Nat.add(Nat.add(Nat.add(A, Nat.mul(_, _)), C), Nat.mul(Nat.add(_, Nat.sub(g, s)), y)) : Nat}
      R.eq([A, C, Nat.sub(g, s), Nat.sub(s, Nat.sub(g, s)), y],
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.V{2n}, R.V{2n}}}, R.V{1n}},
              R.Mul{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{2n}}, R.Add{R.V{4n}, R.V{3n}}}},
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.Add{R.V{2n}, R.V{3n}}, R.Add{R.V{2n}, R.V{3n}}}}, R.V{1n}},
              R.Mul{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{2n}}, R.V{4n}}},
        {==})
    case True{}:
      %sub_add(Nat.sub(Nat.sub(g, s), s), y, fy)
        : {Nat.add(Nat.add(Nat.add(A, Nat.mul(Nat.sub(g, s), Nat.sub(g, s))), C), Nat.mul(g, Nat.sub(y, Nat.sub(Nat.sub(g, s), s))))
           == Nat.add(Nat.add(Nat.add(A, Nat.mul(s, s)), C), Nat.mul(g, _)) : Nat}
      %h1 : {Nat.add(Nat.add(Nat.add(A, Nat.mul(Nat.sub(g, s), Nat.sub(g, s))), C), Nat.mul(_, Nat.sub(y, Nat.sub(Nat.sub(g, s), s))))
             == Nat.add(Nat.add(Nat.add(A, Nat.mul(s, s)), C),
                  Nat.mul(_, Nat.add(Nat.sub(Nat.sub(g, s), s), Nat.sub(y, Nat.sub(Nat.sub(g, s), s))))) : Nat}
      %sub_add(s, Nat.sub(g, s), lt_true_le(s, Nat.sub(g, s), elt))
        : {Nat.add(Nat.add(Nat.add(A, Nat.mul(_, _)), C), Nat.mul(Nat.add(s, _), Nat.sub(y, Nat.sub(Nat.sub(g, s), s))))
           == Nat.add(Nat.add(Nat.add(A, Nat.mul(s, s)), C),
                Nat.mul(Nat.add(s, _), Nat.add(Nat.sub(Nat.sub(g, s), s), Nat.sub(y, Nat.sub(Nat.sub(g, s), s))))) : Nat}
      R.eq([A, C, s, Nat.sub(Nat.sub(g, s), s), Nat.sub(y, Nat.sub(Nat.sub(g, s), s))],
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.Add{R.V{2n}, R.V{3n}}, R.Add{R.V{2n}, R.V{3n}}}}, R.V{1n}},
              R.Mul{R.Add{R.V{2n}, R.Add{R.V{2n}, R.V{3n}}}, R.V{4n}}},
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.V{2n}, R.V{2n}}}, R.V{1n}},
              R.Mul{R.Add{R.V{2n}, R.Add{R.V{2n}, R.V{3n}}}, R.Add{R.V{3n}, R.V{4n}}}},
        {==})

def fly_up_e(lt: Bool, +g: Nat, +y: Nat, +s: Nat, +A: Nat, +C: Nat, elt: {Nat.is_lt(s, g) == lt : Bool},
  fy: {P.Z.fits(y, P.Share.snd(P.Fly.up(lt, g, s))) == True{} : Bool})
  -> {Nat.add(Nat.add(Nat.add(A, P.Z.sq(P.Share.fst(P.Fly.up(lt, g, s)))), C), Nat.mul(g, P.Z.shift(y, P.Share.snd(P.Fly.up(lt, g, s)))))
      == Nat.add(Nat.add(Nat.add(A, Nat.mul(s, s)), C), Nat.mul(g, y)) : Nat}:
  match lt:
    case False{}:
      %sub_add(g, s, lt_false_le(s, g, elt))
        : {Nat.add(Nat.add(Nat.add(A, Nat.mul(Nat.sub(s, g), Nat.sub(s, g))), C), Nat.mul(g, Nat.add(y, Nat.add(_, Nat.sub(s, g)))))
           == Nat.add(Nat.add(Nat.add(A, Nat.mul(_, _)), C), Nat.mul(g, y)) : Nat}
      R.eq([A, C, g, y, Nat.sub(s, g)],
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.V{4n}, R.V{4n}}}, R.V{1n}}, R.Mul{R.V{2n}, R.Add{R.V{3n}, R.Add{R.Add{R.V{2n}, R.V{4n}}, R.V{4n}}}}},
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.Add{R.V{2n}, R.V{4n}}, R.Add{R.V{2n}, R.V{4n}}}}, R.V{1n}}, R.Mul{R.V{2n}, R.V{3n}}},
        {==})
    case True{}:
      fly_turn_e(Nat.is_lt(s, Nat.sub(g, s)), g, y, s, A, C, sub_add(s, g, lt_true_le(s, g, elt)), {==}, fy)

def fly_energy(+g: Nat, +y: Nat, +vy: P.Z, +A: Nat, +C: Nat,
  fy: {P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))) == True{} : Bool})
  -> {Nat.add(Nat.add(Nat.add(A, P.Z.sq(P.Share.fst(P.Fly.step(g, vy)))), C), Nat.mul(g, P.Z.shift(y, P.Share.snd(P.Fly.step(g, vy)))))
      == Nat.add(Nat.add(Nat.add(A, P.Z.sq(vy)), C), Nat.mul(g, y)) : Nat}:
  match vy:
    case P.Pos{+s}:
      fly_up_e(Nat.is_lt(s, g), g, y, s, A, C, {==}, fy)
    case P.Neg{+s}:
      %sub_add(Nat.add(Nat.add(s, s), g), y, fy)
        : {Nat.add(Nat.add(Nat.add(A, Nat.mul(Nat.add(s, g), Nat.add(s, g))), C), Nat.mul(g, Nat.sub(y, Nat.add(Nat.add(s, s), g))))
           == Nat.add(Nat.add(Nat.add(A, Nat.mul(s, s)), C), Nat.mul(g, _)) : Nat}
      R.eq([A, C, s, g, Nat.sub(y, Nat.add(Nat.add(s, s), g))],
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.Add{R.V{2n}, R.V{3n}}, R.Add{R.V{2n}, R.V{3n}}}}, R.V{1n}}, R.Mul{R.V{3n}, R.V{4n}}},
        R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.V{2n}, R.V{2n}}}, R.V{1n}},
              R.Mul{R.V{3n}, R.Add{R.Add{R.Add{R.V{2n}, R.V{2n}}, R.V{3n}}, R.V{4n}}}},
        {==})

# the tick's gate for the x move, from the body after driving (vx both)
def Ok1(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z) -> Bool:
  Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, obs))

# an untouched tick in the air, from the body (x, y, z, vx, vy, vz)
def FF(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z) -> Data:
  {P.Body.hit(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, vx), obs, P.Z.add(vx, vx),
    P.Z.shift(x, P.Z.add(vx, vx)), x, y, z, vx, vy, vz, False{}, False{})))) == False{} : Bool}

# its y move never ran past the floor
def ff_fy(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, free: FF(s, g, obs, x, y, z, vx, vy, vz))
  -> {P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))) == True{} : Bool}:
  and_r(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))),
    and_r(P.Z.fits(x, P.Z.add(vx, vx)), Bool.and(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))),
      x_air_ok(s, Ok1(s, obs, vx, x, y, z, vx), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, {==}, free)))

def ffe(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +hit: Bool,
  +free: FF(s, g, obs, x, y, z, vx, vy, vz))
  -> {P.Body.energy(g, P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, vx), obs, P.Z.add(vx, vx),
        P.Z.shift(x, P.Z.add(vx, vx)), x, y, z, vx, vy, vz, False{}, False{}))))
      == P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit}) : Nat}:
  %x_air_eq(s, Ok1(s, obs, vx, x, y, z, vx), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, free)
    : {P.Body.energy(g, _) == P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit}) : Nat}
  fly_energy(g, y, vy, P.Z.sq(vx), P.Z.sq(vz), ff_fy(s, g, obs, x, y, z, vx, vy, vz, free))

def Laws.free_flight_energy(k, obs, b, air, free):
  match k b:
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          Empty.absurd({P.Body.energy(g, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(),
              P.Body{x, y, z, vx, vy, vz, True{}, hit}))) == P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, True{}, hit}) : Nat},
            clash(air))
        case False{}:
          ffe(s, g, obs, x, y, z, vx, vy, vz, hit, free)

# Kinematics in flight
# --------------------

# v' + g == v, signs apart
def fly_turn_kv(lt: Bool, +g: Nat, +s: Nat, h1: {Nat.add(s, Nat.sub(g, s)) == g : Nat})
  -> {Nat.add(Nat.add(0n, 0n), g) == Nat.add(s, Nat.sub(g, s)) : Nat}:
  Equal.sym(Nat, Nat.add(s, Nat.sub(g, s)), g, h1)

def fly_up_kv(lt: Bool, +g: Nat, +s: Nat, elt: {Nat.is_lt(s, g) == lt : Bool})
  -> {Nat.add(Nat.add(P.Z.pos(P.Share.fst(P.Fly.up(lt, g, s))), 0n), g) == Nat.add(s, P.Z.neg(P.Share.fst(P.Fly.up(lt, g, s)))) : Nat}:
  match lt:
    case False{}:
      %sub_add(g, s, lt_false_le(s, g, elt)) : {Nat.add(Nat.add(Nat.sub(s, g), 0n), g) == Nat.add(_, 0n) : Nat}
      R.eq([g, Nat.sub(s, g)], R.Add{R.Add{R.V{1n}, R.N{0n}}, R.V{0n}}, R.Add{R.Add{R.V{0n}, R.V{1n}}, R.N{0n}}, {==})
    case True{}:
      Equal.sym(Nat, Nat.add(s, Nat.sub(g, s)), g, sub_add(s, g, lt_true_le(s, g, elt)))

def fly_kv(+g: Nat, +vy: P.Z)
  -> {Nat.add(Nat.add(P.Z.pos(P.Share.fst(P.Fly.step(g, vy))), P.Z.neg(vy)), g) == Nat.add(P.Z.pos(vy), P.Z.neg(P.Share.fst(P.Fly.step(g, vy)))) : Nat}:
  match vy:
    case P.Pos{+s}:
      fly_up_kv(Nat.is_lt(s, g), g, s, {==})
    case P.Neg{+s}:
      {==}

# y' == y + v + v', signs apart
def fly_turn_ky(lt: Bool, +g: Nat, +y: Nat, +s: Nat,
  h1: {Nat.add(s, Nat.sub(g, s)) == g : Nat}, elt: {Nat.is_lt(s, Nat.sub(g, s)) == lt : Bool},
  fy: {P.Z.fits(y, P.Z.diff(lt, s, Nat.sub(g, s))) == True{} : Bool})
  -> {Nat.add(Nat.add(P.Z.shift(y, P.Z.diff(lt, s, Nat.sub(g, s))), 0n), Nat.sub(g, s)) == Nat.add(Nat.add(y, s), 0n) : Nat}:
  match lt:
    case False{}:
      %sub_add(Nat.sub(g, s), s, lt_false_le(s, Nat.sub(g, s), elt))
        : {Nat.add(Nat.add(Nat.add(y, Nat.sub(s, Nat.sub(g, s))), 0n), Nat.sub(g, s)) == Nat.add(Nat.add(y, _), 0n) : Nat}
      R.eq([y, Nat.sub(g, s), Nat.sub(s, Nat.sub(g, s))],
        R.Add{R.Add{R.Add{R.V{0n}, R.V{2n}}, R.N{0n}}, R.V{1n}},
        R.Add{R.Add{R.V{0n}, R.Add{R.V{1n}, R.V{2n}}}, R.N{0n}}, {==})
    case True{}:
      %sub_add(Nat.sub(Nat.sub(g, s), s), y, fy)
        : {Nat.add(Nat.add(Nat.sub(y, Nat.sub(Nat.sub(g, s), s)), 0n), Nat.sub(g, s)) == Nat.add(Nat.add(_, s), 0n) : Nat}
      %sub_add(s, Nat.sub(g, s), lt_true_le(s, Nat.sub(g, s), elt))
        : {Nat.add(Nat.add(Nat.sub(y, Nat.sub(Nat.sub(g, s), s)), 0n), _)
           == Nat.add(Nat.add(Nat.add(Nat.sub(Nat.sub(g, s), s), Nat.sub(y, Nat.sub(Nat.sub(g, s), s))), s), 0n) : Nat}
      R.eq([s, Nat.sub(Nat.sub(g, s), s), Nat.sub(y, Nat.sub(Nat.sub(g, s), s))],
        R.Add{R.Add{R.V{2n}, R.N{0n}}, R.Add{R.V{0n}, R.V{1n}}},
        R.Add{R.Add{R.Add{R.V{1n}, R.V{2n}}, R.V{0n}}, R.N{0n}}, {==})

def fly_up_ky(lt: Bool, +g: Nat, +y: Nat, +s: Nat, elt: {Nat.is_lt(s, g) == lt : Bool},
  fy: {P.Z.fits(y, P.Share.snd(P.Fly.up(lt, g, s))) == True{} : Bool})
  -> {Nat.add(Nat.add(P.Z.shift(y, P.Share.snd(P.Fly.up(lt, g, s))), 0n), P.Z.neg(P.Share.fst(P.Fly.up(lt, g, s))))
      == Nat.add(Nat.add(y, s), P.Z.pos(P.Share.fst(P.Fly.up(lt, g, s)))) : Nat}:
  match lt:
    case False{}:
      R.eq([y, s, Nat.sub(s, g)],
        R.Add{R.Add{R.Add{R.V{0n}, R.Add{R.V{1n}, R.V{2n}}}, R.N{0n}}, R.N{0n}},
        R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}, {==})
    case True{}:
      fly_turn_ky(Nat.is_lt(s, Nat.sub(g, s)), g, y, s, sub_add(s, g, lt_true_le(s, g, elt)), {==}, fy)

def fly_ky(+g: Nat, +y: Nat, +vy: P.Z, fy: {P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))) == True{} : Bool})
  -> {Nat.add(Nat.add(P.Z.shift(y, P.Share.snd(P.Fly.step(g, vy))), P.Z.neg(vy)), P.Z.neg(P.Share.fst(P.Fly.step(g, vy))))
      == Nat.add(Nat.add(y, P.Z.pos(vy)), P.Z.pos(P.Share.fst(P.Fly.step(g, vy)))) : Nat}:
  match vy:
    case P.Pos{+s}:
      fly_up_ky(Nat.is_lt(s, g), g, y, s, {==}, fy)
    case P.Neg{+s}:
      %sub_add(Nat.add(Nat.add(s, s), g), y, fy)
        : {Nat.add(Nat.add(Nat.sub(y, Nat.add(Nat.add(s, s), g)), s), Nat.add(s, g)) == Nat.add(Nat.add(_, 0n), 0n) : Nat}
      R.eq([s, g, Nat.sub(y, Nat.add(Nat.add(s, s), g))],
        R.Add{R.Add{R.V{2n}, R.V{0n}}, R.Add{R.V{0n}, R.V{1n}}},
        R.Add{R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.V{0n}}, R.V{1n}}, R.V{2n}}, R.N{0n}}, R.N{0n}}, {==})

# x' == x + v0 + v1, same direction, signs apart
def hkin_pos(+x: Nat, +a: Nat, +b: Nat) -> {Nat.add(Nat.add(x, Nat.add(a, b)), 0n) == Nat.add(x, Nat.add(a, b)) : Nat}:
  R.add_zero(Nat.add(x, Nat.add(a, b)))

def hkin_neg(+x: Nat, +a: Nat, +b: Nat, fx: {Nat.is_le(Nat.add(a, b), x) == True{} : Bool})
  -> {Nat.add(Nat.sub(x, Nat.add(a, b)), Nat.add(a, b)) == Nat.add(x, 0n) : Nat}:
  %sub_add(Nat.add(a, b), x, fx) : {Nat.add(Nat.sub(x, Nat.add(a, b)), Nat.add(a, b)) == Nat.add(_, 0n) : Nat}
  R.eq([a, b, Nat.sub(x, Nat.add(a, b))],
    R.Add{R.V{2n}, R.Add{R.V{0n}, R.V{1n}}}, R.Add{R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}, R.N{0n}}, {==})

def hkin(+x: Nat, +v: P.Z, fx: {P.Z.fits(x, P.Z.add(v, v)) == True{} : Bool})
  -> {Nat.add(P.Z.shift(x, P.Z.add(v, v)), Nat.add(P.Z.neg(v), P.Z.neg(v))) == Nat.add(x, Nat.add(P.Z.pos(v), P.Z.pos(v))) : Nat}:
  match v:
    case P.Pos{+a}:
      hkin_pos(x, a, a)
    case P.Neg{+a}:
      hkin_neg(x, a, a, fx)

def ff_fx(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, free: FF(s, g, obs, x, y, z, vx, vy, vz))
  -> {P.Z.fits(x, P.Z.add(vx, vx)) == True{} : Bool}:
  and_l(P.Z.fits(x, P.Z.add(vx, vx)), Bool.and(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))),
    x_air_ok(s, Ok1(s, obs, vx, x, y, z, vx), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, {==}, free))

def ff_fz(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, free: FF(s, g, obs, x, y, z, vx, vy, vz))
  -> {P.Z.fits(z, P.Z.add(vz, vz)) == True{} : Bool}:
  and_l(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))),
    and_r(P.Z.fits(x, P.Z.add(vx, vx)), Bool.and(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))),
      x_air_ok(s, Ok1(s, obs, vx, x, y, z, vx), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, {==}, free)))

def Kin(+g: Nat, +b: P.Body, +b2: P.Body) -> Type:
  {Nat.add(Nat.add(P.Z.pos(P.Body.vy(b2)), P.Z.neg(P.Body.vy(b))), g)
    == Nat.add(P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b2))) : Nat}
  & {Nat.add(Nat.add(P.Body.y(b2), P.Z.neg(P.Body.vy(b))), P.Z.neg(P.Body.vy(b2)))
    == Nat.add(Nat.add(P.Body.y(b), P.Z.pos(P.Body.vy(b))), P.Z.pos(P.Body.vy(b2))) : Nat}
  & {P.Body.vx(b2) == P.Body.vx(b) : P.Z}
  & {P.Body.vz(b2) == P.Body.vz(b) : P.Z}
  & {Nat.add(P.Body.x(b2), Nat.add(P.Z.neg(P.Body.vx(b)), P.Z.neg(P.Body.vx(b))))
    == Nat.add(P.Body.x(b), Nat.add(P.Z.pos(P.Body.vx(b)), P.Z.pos(P.Body.vx(b)))) : Nat}
  & {Nat.add(P.Body.z(b2), Nat.add(P.Z.neg(P.Body.vz(b)), P.Z.neg(P.Body.vz(b))))
    == Nat.add(P.Body.z(b), Nat.add(P.Z.pos(P.Body.vz(b)), P.Z.pos(P.Body.vz(b)))) : Nat}

def ffk(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +hit: Bool,
  +free: FF(s, g, obs, x, y, z, vx, vy, vz))
  -> Kin(g, P.Body{x, y, z, vx, vy, vz, False{}, hit}, P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, vx), obs,
       P.Z.add(vx, vx), P.Z.shift(x, P.Z.add(vx, vx)), x, y, z, vx, vy, vz, False{}, False{})))):
  %x_air_eq(s, Ok1(s, obs, vx, x, y, z, vx), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, free)
    : Kin(g, P.Body{x, y, z, vx, vy, vz, False{}, hit}, _)
  (fly_kv(g, vy), fly_ky(g, y, vy, ff_fy(s, g, obs, x, y, z, vx, vy, vz, free)), {==}, {==},
    hkin(x, vx, ff_fx(s, g, obs, x, y, z, vx, vy, vz, free)), hkin(z, vz, ff_fz(s, g, obs, x, y, z, vx, vy, vz, free)))

def Laws.free_flight_kinematics(k, obs, b, air, free):
  match k b:
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          Empty.absurd(Kin(g, P.Body{x, y, z, vx, vy, vz, True{}, hit}, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs,
              P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit}))), clash(air))
        case False{}:
          ffk(s, g, obs, x, y, z, vx, vy, vz, hit, free)

# A whole flight
# --------------
# By induction on the ticks: free_flight_kinematics for the first, the
# rest of the flight after it, and a ring identity gluing the two (for the
# height, G = D + B + (2m+1) A), cancelling what both sides share.

def unsucc(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def add_cancel(c: Nat, -a: Nat, -b: Nat, h: {Nat.add(c, a) == Nat.add(c, b) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      h
    case 1n+p:
      add_cancel(p, a, b, Equal.cong(Nat, Nat, x => unsucc(x), 1n+Nat.add(p, a), 1n+Nat.add(p, b), h))

def fin2(+s: Nat, -t: Nat, -l: Nat, -r: Nat, id: {Nat.add(s, l) == Nat.add(t, r) : Nat}, e: {t == s : Nat})
  -> {Nat.add(s, l) == Nat.add(s, r) : Nat}:
  %e : {Nat.add(s, l) == Nat.add(_, r) : Nat}
  id

# s + l = t + r and t = s: l = r
def fin(+s: Nat, -t: Nat, -l: Nat, -r: Nat, id: {Nat.add(s, l) == Nat.add(t, r) : Nat}, e: {t == s : Nat}) -> {l == r : Nat}:
  add_cancel(s, l, r, fin2(s, t, l, r, id, e))

def cong2(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, ea: {a == a2 : Nat}, eb: {b == b2 : Nat})
  -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %ea : {Nat.add(a, b) == Nat.add(_, b2) : Nat}
  %eb : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

def congm(-q: Nat, -a: Nat, -a2: Nat, e: {a == a2 : Nat}) -> {Nat.mul(q, a) == Nat.mul(q, a2) : Nat}:
  %e : {Nat.mul(q, a) == Nat.mul(q, _) : Nat}
  {==}

def not_t(+x: Bool, h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, clash2(h))
    case False{}:
      {==}

# the vertical velocity: v' = v - g, then m ticks more
def vstep(+g: Nat, +m: Nat, +p: Nat, +n: Nat, +p1: Nat, +n1: Nat, +p2: Nat, +n2: Nat,
  a: {Nat.add(Nat.add(p1, n), g) == Nat.add(p, n1) : Nat},
  c: {Nat.add(Nat.add(p2, n1), Nat.mul(m, g)) == Nat.add(p1, n2) : Nat})
  -> {Nat.add(Nat.add(p2, n), Nat.mul(1n+m, g)) == Nat.add(p, n2) : Nat}:
  fin(Nat.add(Nat.add(p, n1), Nat.add(p1, n2)), Nat.add(Nat.add(Nat.add(p1, n), g), Nat.add(Nat.add(p2, n1), Nat.mul(m, g))),
    Nat.add(Nat.add(p2, n), Nat.mul(1n+m, g)), Nat.add(p, n2),
    R.eq([p, n, p1, n1, p2, n2, g, m],
      R.Add{R.Add{R.Add{R.V{0n}, R.V{3n}}, R.Add{R.V{2n}, R.V{5n}}}, R.Add{R.Add{R.V{4n}, R.V{1n}}, R.Mul{R.Add{R.N{1n}, R.V{7n}}, R.V{6n}}}},
      R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{1n}}, R.V{6n}}, R.Add{R.Add{R.V{4n}, R.V{3n}}, R.Mul{R.V{7n}, R.V{6n}}}}, R.Add{R.V{0n}, R.V{5n}}},
      {==}),
    cong2(Nat.add(Nat.add(p1, n), g), Nat.add(p, n1), Nat.add(Nat.add(p2, n1), Nat.mul(m, g)), Nat.add(p1, n2), a, c))

# the height: G = D + B + (2m+1) A
def ystep(+g: Nat, +m: Nat, +y: Nat, +y1: Nat, +y2: Nat, +p: Nat, +n: Nat, +p1: Nat, +n1: Nat,
  a: {Nat.add(Nat.add(p1, n), g) == Nat.add(p, n1) : Nat},
  b: {Nat.add(Nat.add(y1, n), n1) == Nat.add(Nat.add(y, p), p1) : Nat},
  d: {Nat.add(Nat.add(y2, Nat.mul(g, Nat.mul(m, m))), Nat.mul(Nat.mul(2n, m), n1)) == Nat.add(y1, Nat.mul(Nat.mul(2n, m), p1)) : Nat})
  -> {Nat.add(Nat.add(y2, Nat.mul(g, Nat.mul(1n+m, 1n+m))), Nat.mul(Nat.mul(2n, 1n+m), n))
      == Nat.add(y, Nat.mul(Nat.mul(2n, 1n+m), p)) : Nat}:
  fin(Nat.add(Nat.add(Nat.add(y1, Nat.mul(Nat.mul(2n, m), p1)), Nat.add(Nat.add(y, p), p1)),
        Nat.mul(Nat.add(Nat.mul(2n, m), 1n), Nat.add(p, n1))),
    Nat.add(Nat.add(Nat.add(Nat.add(y2, Nat.mul(g, Nat.mul(m, m))), Nat.mul(Nat.mul(2n, m), n1)), Nat.add(Nat.add(y1, n), n1)),
        Nat.mul(Nat.add(Nat.mul(2n, m), 1n), Nat.add(Nat.add(p1, n), g))),
    Nat.add(Nat.add(y2, Nat.mul(g, Nat.mul(1n+m, 1n+m))), Nat.mul(Nat.mul(2n, 1n+m), n)),
    Nat.add(y, Nat.mul(Nat.mul(2n, 1n+m), p)),
    R.eq([y, y1, y2, p, n, p1, n1, g, m],
      R.Add{R.Add{R.Add{R.Add{R.V{1n}, R.Mul{R.Mul{R.N{2n}, R.V{8n}}, R.V{5n}}}, R.Add{R.Add{R.V{0n}, R.V{3n}}, R.V{5n}}},
          R.Mul{R.Add{R.Mul{R.N{2n}, R.V{8n}}, R.N{1n}}, R.Add{R.V{3n}, R.V{6n}}}},
        R.Add{R.Add{R.V{2n}, R.Mul{R.V{7n}, R.Mul{R.Add{R.N{1n}, R.V{8n}}, R.Add{R.N{1n}, R.V{8n}}}}},
          R.Mul{R.Mul{R.N{2n}, R.Add{R.N{1n}, R.V{8n}}}, R.V{4n}}}},
      R.Add{R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.Mul{R.V{7n}, R.Mul{R.V{8n}, R.V{8n}}}}, R.Mul{R.Mul{R.N{2n}, R.V{8n}}, R.V{6n}}},
            R.Add{R.Add{R.V{1n}, R.V{4n}}, R.V{6n}}},
          R.Mul{R.Add{R.Mul{R.N{2n}, R.V{8n}}, R.N{1n}}, R.Add{R.Add{R.V{5n}, R.V{4n}}, R.V{7n}}}},
        R.Add{R.V{0n}, R.Mul{R.Mul{R.N{2n}, R.Add{R.N{1n}, R.V{8n}}}, R.V{3n}}}},
      {==}),
    cong2(Nat.add(Nat.add(Nat.add(y2, Nat.mul(g, Nat.mul(m, m))), Nat.mul(Nat.mul(2n, m), n1)), Nat.add(Nat.add(y1, n), n1)),
      Nat.add(Nat.add(y1, Nat.mul(Nat.mul(2n, m), p1)), Nat.add(Nat.add(y, p), p1)),
      Nat.mul(Nat.add(Nat.mul(2n, m), 1n), Nat.add(Nat.add(p1, n), g)), Nat.mul(Nat.add(Nat.mul(2n, m), 1n), Nat.add(p, n1)),
      cong2(Nat.add(Nat.add(y2, Nat.mul(g, Nat.mul(m, m))), Nat.mul(Nat.mul(2n, m), n1)), Nat.add(y1, Nat.mul(Nat.mul(2n, m), p1)),
        Nat.add(Nat.add(y1, n), n1), Nat.add(Nat.add(y, p), p1), d, b),
      congm(Nat.add(Nat.mul(2n, m), 1n), Nat.add(Nat.add(p1, n), g), Nat.add(p, n1), a)))

# a horizontal coordinate: x' = x + 2 v, then m ticks more
def hstep(+m: Nat, +x: Nat, +x1: Nat, +x2: Nat, +p: Nat, +n: Nat,
  t: {Nat.add(x1, Nat.add(n, n)) == Nat.add(x, Nat.add(p, p)) : Nat},
  i: {Nat.add(x2, Nat.mul(Nat.mul(2n, m), n)) == Nat.add(x1, Nat.mul(Nat.mul(2n, m), p)) : Nat})
  -> {Nat.add(x2, Nat.mul(Nat.mul(2n, 1n+m), n)) == Nat.add(x, Nat.mul(Nat.mul(2n, 1n+m), p)) : Nat}:
  fin(Nat.add(Nat.add(x1, Nat.mul(Nat.mul(2n, m), p)), Nat.add(x, Nat.add(p, p))),
    Nat.add(Nat.add(x2, Nat.mul(Nat.mul(2n, m), n)), Nat.add(x1, Nat.add(n, n))),
    Nat.add(x2, Nat.mul(Nat.mul(2n, 1n+m), n)), Nat.add(x, Nat.mul(Nat.mul(2n, 1n+m), p)),
    R.eq([x, x1, x2, p, n, m],
      R.Add{R.Add{R.Add{R.V{1n}, R.Mul{R.Mul{R.N{2n}, R.V{5n}}, R.V{3n}}}, R.Add{R.V{0n}, R.Add{R.V{3n}, R.V{3n}}}},
        R.Add{R.V{2n}, R.Mul{R.Mul{R.N{2n}, R.Add{R.N{1n}, R.V{5n}}}, R.V{4n}}}},
      R.Add{R.Add{R.Add{R.V{2n}, R.Mul{R.Mul{R.N{2n}, R.V{5n}}, R.V{4n}}}, R.Add{R.V{1n}, R.Add{R.V{4n}, R.V{4n}}}},
        R.Add{R.V{0n}, R.Mul{R.Mul{R.N{2n}, R.Add{R.N{1n}, R.V{5n}}}, R.V{3n}}}},
      {==}),
    cong2(Nat.add(x2, Nat.mul(Nat.mul(2n, m), n)), Nat.add(x1, Nat.mul(Nat.mul(2n, m), p)),
      Nat.add(x1, Nat.add(n, n)), Nat.add(x, Nat.add(p, p)), i, t))

# the rest of a flight, seen from the velocity it started with (the same)
def hmove(+m: Nat, +x1: Nat, +x2: Nat, -v1: P.Z, -v: P.Z, e: {v1 == v : P.Z},
  i: {Nat.add(x2, Nat.mul(Nat.mul(2n, m), P.Z.neg(v1))) == Nat.add(x1, Nat.mul(Nat.mul(2n, m), P.Z.pos(v1))) : Nat})
  -> {Nat.add(x2, Nat.mul(Nat.mul(2n, m), P.Z.neg(v))) == Nat.add(x1, Nat.mul(Nat.mul(2n, m), P.Z.pos(v))) : Nat}:
  %e : {Nat.add(x2, Nat.mul(Nat.mul(2n, m), P.Z.neg(_))) == Nat.add(x1, Nat.mul(Nat.mul(2n, m), P.Z.pos(_))) : Nat}
  i

# n ticks of flight from b to b2 are the parabola
def Par(+g: Nat, +n: Nat, +b: P.Body, +b2: P.Body) -> Type:
  {Nat.add(Nat.add(P.Z.pos(P.Body.vy(b2)), P.Z.neg(P.Body.vy(b))), Nat.mul(n, g))
    == Nat.add(P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b2))) : Nat}
  & {Nat.add(Nat.add(P.Body.y(b2), Nat.mul(g, Nat.mul(n, n))), Nat.mul(Nat.mul(2n, n), P.Z.neg(P.Body.vy(b))))
    == Nat.add(P.Body.y(b), Nat.mul(Nat.mul(2n, n), P.Z.pos(P.Body.vy(b)))) : Nat}
  & {P.Body.vx(b2) == P.Body.vx(b) : P.Z}
  & {P.Body.vz(b2) == P.Body.vz(b) : P.Z}
  & {Nat.add(P.Body.x(b2), Nat.mul(Nat.mul(2n, n), P.Z.neg(P.Body.vx(b))))
    == Nat.add(P.Body.x(b), Nat.mul(Nat.mul(2n, n), P.Z.pos(P.Body.vx(b)))) : Nat}
  & {Nat.add(P.Body.z(b2), Nat.mul(Nat.mul(2n, n), P.Z.neg(P.Body.vz(b))))
    == Nat.add(P.Body.z(b), Nat.mul(Nat.mul(2n, n), P.Z.pos(P.Body.vz(b)))) : Nat}

def par0(+g: Nat, +b: P.Body) -> Par(g, 0n, b, b):
  (R.eq([P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b)), g],
     R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Mul{R.N{0n}, R.V{2n}}}, R.Add{R.V{0n}, R.V{1n}}, {==}),
   R.eq([P.Body.y(b), g, P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b))],
     R.Add{R.Add{R.V{0n}, R.Mul{R.V{1n}, R.Mul{R.N{0n}, R.N{0n}}}}, R.Mul{R.Mul{R.N{2n}, R.N{0n}}, R.V{3n}}},
     R.Add{R.V{0n}, R.Mul{R.Mul{R.N{2n}, R.N{0n}}, R.V{2n}}}, {==}),
   {==}, {==},
   R.eq([P.Body.x(b), P.Z.pos(P.Body.vx(b)), P.Z.neg(P.Body.vx(b))],
     R.Add{R.V{0n}, R.Mul{R.Mul{R.N{2n}, R.N{0n}}, R.V{2n}}}, R.Add{R.V{0n}, R.Mul{R.Mul{R.N{2n}, R.N{0n}}, R.V{1n}}}, {==}),
   R.eq([P.Body.z(b), P.Z.pos(P.Body.vz(b)), P.Z.neg(P.Body.vz(b))],
     R.Add{R.V{0n}, R.Mul{R.Mul{R.N{2n}, R.N{0n}}, R.V{2n}}}, R.Add{R.V{0n}, R.Mul{R.Mul{R.N{2n}, R.N{0n}}, R.V{1n}}}, {==}))

# one tick (kin) and the m after it (ih) are 1 + m ticks of the parabola
def fstep(+g: Nat, +m: Nat, +b: P.Body, +b1: P.Body, +b2: P.Body, kin: Kin(g, b, b1), ih: Par(g, m, b1, b2))
  -> Par(g, 1n+m, b, b2):
  (+ka, kb, +kvx, +kvz, kx, kz) = kin
  (ia, ib, ivx, ivz, ix, iz) = ih
  (vstep(g, m, P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b)), P.Z.pos(P.Body.vy(b1)), P.Z.neg(P.Body.vy(b1)),
     P.Z.pos(P.Body.vy(b2)), P.Z.neg(P.Body.vy(b2)), ka, ia),
   ystep(g, m, P.Body.y(b), P.Body.y(b1), P.Body.y(b2), P.Z.pos(P.Body.vy(b)), P.Z.neg(P.Body.vy(b)),
     P.Z.pos(P.Body.vy(b1)), P.Z.neg(P.Body.vy(b1)), ka, kb, ib),
   Equal.trans(P.Z, P.Body.vx(b2), P.Body.vx(b1), P.Body.vx(b), ivx, kvx),
   Equal.trans(P.Z, P.Body.vz(b2), P.Body.vz(b1), P.Body.vz(b), ivz, kvz),
   hstep(m, P.Body.x(b), P.Body.x(b1), P.Body.x(b2), P.Z.pos(P.Body.vx(b)), P.Z.neg(P.Body.vx(b)), kx,
     hmove(m, P.Body.x(b1), P.Body.x(b2), P.Body.vx(b1), P.Body.vx(b), kvx, ix)),
   hstep(m, P.Body.z(b), P.Body.z(b1), P.Body.z(b2), P.Z.pos(P.Body.vz(b)), P.Z.neg(P.Body.vz(b)), kz,
     hmove(m, P.Body.z(b1), P.Body.z(b2), P.Body.vz(b1), P.Body.vz(b), kvz, iz)))

def fpar(+k: P.K, obss: List<&2, List<&2, P.Body>>, +b: P.Body, +free: {P.Flight.clear(k, obss, b) == True{} : Bool})
  -> Par(P.K.g(k), List.length(&2, List<&2, P.Body>, obss), b, P.Flight.run(k, obss, b)):
  match obss:
    case []:
      par0(P.K.g(k), b)
    case +obs <> +rest:
      +b1 = P.Tick.body(P.Body.tick(k, obs, P.In.idle(), b))
      +c1 = and_l(Bool.and(Bool.not(P.Body.ground(b)), Bool.not(P.Body.hit(b1))), P.Flight.clear(k, rest, b1), free)
      fstep(P.K.g(k), List.length(&2, List<&2, P.Body>, rest), b, b1, P.Flight.run(k, rest, b1),
        Laws.free_flight_kinematics(k, obs, b,
          not_t(P.Body.ground(b), and_l(Bool.not(P.Body.ground(b)), Bool.not(P.Body.hit(b1)), c1)),
          not_t(P.Body.hit(b1), and_r(Bool.not(P.Body.ground(b)), Bool.not(P.Body.hit(b1)), c1))),
        fpar(k, rest, b1, and_r(Bool.and(Bool.not(P.Body.ground(b)), Bool.not(P.Body.hit(b1))), P.Flight.clear(k, rest, b1), free)))

def Laws.flight_is_parabola(k, obss, b, free):
  fpar(k, obss, b, free)

# Jumps
# -----

# in the air the walk never reaches the body: Drive.air drops it
def Laws.no_air_control(k, obs, w, b, air):
  match k b:
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          Empty.absurd({P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit})
              == P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit})
              : P.Body & List<&2, P.Body>}, clash(air))
        case False{}:
          {==}

# on the ground the motor adds acc along the wish to whatever friction left
def MS(+acc: Nat, +ux: P.Z, +uz: P.Z, +b1: P.Body, +b0: P.Body) -> Type:
  {P.Body.vx(b1) == P.Z.add(P.Body.vx(b0), P.Z.q12(acc, ux)) : P.Z}
  & {P.Body.vz(b1) == P.Z.add(P.Body.vz(b0), P.Z.q12(acc, uz)) : P.Z}

def Laws.motor_is_steady(k, b, ux, uz, stand):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          ({==}, {==})
        case False{}:
          Empty.absurd(MS(acc, ux, uz,
            P.Body.drive(P.K{g, mu, j, acc, s}, P.In{Some{P.Wish{ux, uz}}, False{}},
              P.Body{x, y, z, vx, vy, vz, False{}, hit}),
            P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit})),
            clash2(stand))

def Laws.no_air_jump(k, obs, w, b, air):
  match k b:
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          Empty.absurd({P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{w, True{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit})
              == P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit})
              : P.Body & List<&2, P.Body>}, clash(air))
        case False{}:
          {==}

# a takeoff from the ground, untouched: the body after driving is at
# (x, y, z) with velocity (fx, J, fz)
def FJ(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z, +j: Nat) -> Data:
  {P.Body.hit(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx), obs, P.Z.add(vx, fx),
    P.Z.shift(x, P.Z.add(vx, fx)), x, y, z, fx, P.Pos{j}, fz, False{}, False{})))) == False{} : Bool}

def je(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z, +j: Nat,
  +free: FJ(s, g, obs, x, y, z, vx, vz, fx, fz, j))
  -> {P.Body.energy(g, P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx), obs, P.Z.add(vx, fx),
        P.Z.shift(x, P.Z.add(vx, fx)), x, y, z, fx, P.Pos{j}, fz, False{}, False{}))))
      == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx), obs,
             P.Z.add(vx, fx), P.Z.shift(x, P.Z.add(vx, fx)), x, y, z, fx, P.Pos{j}, fz, False{}, False{}))))),
           P.Z.sq(P.Body.vz(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx), obs,
             P.Z.add(vx, fx), P.Z.shift(x, P.Z.add(vx, fx)), x, y, z, fx, P.Pos{j}, fz, False{}, False{})))))),
           Nat.mul(j, j)), Nat.mul(g, y)) : Nat}:
  %x_air_eq(s, Ok1(s, obs, vx, x, y, z, fx), g, obs, vz, P.Z.add(vx, fx), x, y, z, fx, P.Pos{j}, fz, free)
    : {P.Body.energy(g, _) == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(_)), P.Z.sq(P.Body.vz(_))), Nat.mul(j, j)), Nat.mul(g, y)) : Nat}
  Equal.trans(Nat, P.Body.energy(g, Fz(g, P.Z.shift(x, P.Z.add(vx, fx)), y, z, P.Z.add(vz, fz), fx, P.Pos{j}, fz)),
    Nat.add(Nat.add(Nat.add(P.Z.sq(fx), Nat.mul(j, j)), P.Z.sq(fz)), Nat.mul(g, y)),
    Nat.add(Nat.add(Nat.add(P.Z.sq(fx), P.Z.sq(fz)), Nat.mul(j, j)), Nat.mul(g, y)),
    fly_energy(g, y, P.Pos{j}, P.Z.sq(fx), P.Z.sq(fz),
      and_r(P.Z.fits(z, P.Z.add(vz, fz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, P.Pos{j}))),
        and_r(P.Z.fits(x, P.Z.add(vx, fx)), Bool.and(P.Z.fits(z, P.Z.add(vz, fz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, P.Pos{j})))),
          x_air_ok(s, Ok1(s, obs, vx, x, y, z, fx), g, obs, vz, P.Z.add(vx, fx), x, y, z, fx, P.Pos{j}, fz, {==}, free)))),
    R.eq([P.Z.sq(fx), P.Z.sq(fz), j, g, y],
      R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.V{2n}, R.V{2n}}}, R.V{1n}}, R.Mul{R.V{3n}, R.V{4n}}},
      R.Add{R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Mul{R.V{2n}, R.V{2n}}}, R.Mul{R.V{3n}, R.V{4n}}}, {==}))

def Laws.jump_energy(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, +j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          je(s, g, obs, x, y, z, vx, vz, P.Share.fst(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz)),
            P.Share.snd(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz)), j, free)
        case False{}:
          Empty.absurd({P.Body.energy(g, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{None{}, True{}},
              P.Body{x, y, z, vx, vy, vz, False{}, hit})))
            == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{None{}, True{}},
              P.Body{x, y, z, vx, vy, vz, False{}, hit})))), P.Z.sq(P.Body.vz(P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs,
              P.In{None{}, True{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit}))))), Nat.mul(j, j)), Nat.mul(g, y)) : Nat},
            clash2(stand))

# The free path, on the ground
# ----------------------------

def Gz(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +dz: P.Z, +vx: P.Z, +vy: P.Z, +vz: P.Z) -> P.Body:
  P.Body{x, y, P.Z.shift(z, dz), vx, vy, vz, Bool.or(Nat.is_eq(y, 0n), P.Geo.rests(s, x, y, P.Z.shift(z, dz), obs)), False{}}

def z_gnd_eq(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, True{}, False{}))))
    == False{} : Bool})
  -> {Gz(s, obs, x, y, z, dz, vx, vy, vz)
      == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, True{}, False{}))) : P.Body}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Gz(s, obs, x, y, z, dz, vx, vy, vz)
          == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, False{}, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, True{}, False{}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz,
              P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, True{})))),
          hit_ty(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)),
              x, y, z, vx, vy, True{}),
            hit_zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, True{})),
          free))

def x_gnd_eq(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, True{}, False{}))))
    == False{} : Bool})
  -> {Gz(s, obs, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz)
      == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, True{}, False{}))) : P.Body}:
  match ok:
    case True{}:
      z_gnd_eq(s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, free)
    case False{}:
      Empty.absurd({Gz(s, obs, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz)
          == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, False{}, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, True{}, False{}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx,
              P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, True{})))),
          hit_tz(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)),
              x, y, z, vy, vz, True{}),
            hit_xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, True{})),
          free))

def z_gnd_ok(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  eok: {Bool.and(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, True{}, False{}))))
    == False{} : Bool})
  -> {P.Z.fits(z, dz) == True{} : Bool}:
  match ok:
    case True{}:
      and_l(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), obs), eok)
    case False{}:
      Empty.absurd({P.Z.fits(z, dz) == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz,
              P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, True{})))),
          hit_ty(s, g, P.Move.zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)),
              x, y, z, vx, vy, True{}),
            hit_zhit(s, P.Push.z(s, obs, dz, x, y, P.Z.shift(z, dz), vz, P.Geo.head(s, x, y, P.Z.shift(z, dz), obs)), x, y, z, vx, vy, True{})),
          free))

def x_gnd_ok(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  eok: {Bool.and(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, True{}, False{}))))
    == False{} : Bool})
  -> {Bool.and(P.Z.fits(x, dx), P.Z.fits(z, P.Z.add(v0z, vz))) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Bool, P.Z.fits(x, dx), True{}, and_l(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, obs), eok))
        : {Bool.and(_, P.Z.fits(z, P.Z.add(v0z, vz))) == True{} : Bool}
      z_gnd_ok(s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, {==}, free)
    case False{}:
      Empty.absurd({Bool.and(P.Z.fits(x, dx), P.Z.fits(z, P.Z.add(v0z, vz))) == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx,
              P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, True{})))),
          hit_tz(s, g, v0z, P.Move.xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)),
              x, y, z, vy, vz, True{}),
            hit_xhit(s, P.Push.x(s, obs, dx, P.Z.shift(x, dx), y, z, vx, P.Geo.head(s, P.Z.shift(x, dx), y, z, obs)), x, y, z, vy, vz, True{})),
          free))

# Friction
# --------

# x <= p gives x <= 1 + p
def le_succ(+x: Nat, +p: Nat, h: {Nat.is_le(x, p) == True{} : Bool}) -> {Nat.is_le(x, 1n+p) == True{} : Bool}:
  le_of(x, 1n+Nat.sub(p, x), 1n+p,
    %Equal.sym(Nat, Nat.add(x, 1n+Nat.sub(p, x)), 1n+Nat.add(x, Nat.sub(p, x)), R.add_succ(x, Nat.sub(p, x)))
      : {_ == 1n+p : Nat}
    %sub_add(x, p, h) : {1n+Nat.add(x, Nat.sub(p, x)) == 1n+_ : Nat}
    {==})

def sub_le(+a: Nat, +t: Nat) -> {Nat.is_le(Nat.sub(a, t), a) == True{} : Bool}:
  match a t:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      le_refl(p)
    case 1n+p 1n+q:
      le_succ(Nat.sub(p, q), p, sub_le(p, q))

# friction never turns a component around, nor grows it
def nr_pos(+t: Nat, v: P.Z) -> {Nat.is_le(P.Z.pos(P.Z.cut(t, v)), P.Z.pos(v)) == True{} : Bool}:
  match v:
    case P.Pos{+a}:
      sub_le(a, t)
    case P.Neg{+a}:
      {==}

def nr_neg(+t: Nat, v: P.Z) -> {Nat.is_le(P.Z.neg(P.Z.cut(t, v)), P.Z.neg(v)) == True{} : Bool}:
  match v:
    case P.Pos{+a}:
      {==}
    case P.Neg{+a}:
      sub_le(a, t)

# an untouched tick on the ground, with friction f: the body after driving
# is at (x, y, z) with velocity (fx, 0, fz)
def FG(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z) -> Data:
  {P.Body.hit(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx), obs, P.Z.add(vx, fx),
    P.Z.shift(x, P.Z.add(vx, fx)), x, y, z, fx, P.Pos{0n}, fz, True{}, False{})))) == False{} : Bool}

def GB(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z) -> P.Body:
  P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx), obs, P.Z.add(vx, fx),
    P.Z.shift(x, P.Z.add(vx, fx)), x, y, z, fx, P.Pos{0n}, fz, True{}, False{})))

def NR(+vx: P.Z, +vz: P.Z, +b2: P.Body) -> Type:
  {Nat.is_le(P.Z.pos(P.Body.vx(b2)), P.Z.pos(vx)) == True{} : Bool}
  & {Nat.is_le(P.Z.neg(P.Body.vx(b2)), P.Z.neg(vx)) == True{} : Bool}
  & {Nat.is_le(P.Z.pos(P.Body.vz(b2)), P.Z.pos(vz)) == True{} : Bool}
  & {Nat.is_le(P.Z.neg(P.Body.vz(b2)), P.Z.neg(vz)) == True{} : Bool}

def fnr(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +t1: Nat, +t2: Nat,
  free: FG(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz)))
  -> NR(vx, vz, GB(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz))):
  %x_gnd_eq(s, Ok1(s, obs, vx, x, y, z, P.Z.cut(t1, vx)), g, obs, vz, P.Z.add(vx, P.Z.cut(t1, vx)), x, y, z, P.Z.cut(t1, vx), P.Pos{0n},
      P.Z.cut(t2, vz), free)
    : NR(vx, vz, _)
  (nr_pos(t1, vx), nr_neg(t1, vx), nr_pos(t2, vz), nr_neg(t2, vz))

# the friction a tick takes from each component
def T1(+f: Nat, +vx: P.Z, +vz: P.Z) -> Nat:
  P.Fric.take(f, P.Z.mag(vx), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz)))

def T2(+f: Nat, +vx: P.Z, +vz: P.Z) -> Nat:
  P.Fric.take(f, P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz)))

def Laws.friction_never_reverses(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          fnr(s, g, obs, x, y, z, vx, vz, T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), T2(Nat.div(Nat.mul(mu, g), 256n), vx, vz), free)
        case False{}:
          Empty.absurd(NR(vx, vz, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(),
              P.Body{x, y, z, vx, vy, vz, False{}, hit}))), clash2(stand))

def pick_le(ok: Bool, +t: Nat, +a: Nat, -h: Bool, e: {Bool.and(Nat.is_le(t, a), h) == ok : Bool})
  -> {Nat.is_le(P.Pick.n(ok, t, 0n), a) == True{} : Bool}:
  match ok:
    case True{}:
      and_l(Nat.is_le(t, a), h, e)
    case False{}:
      le_add(0n, a)

# friction takes no more than the component has
def take_le(+f: Nat, +a: Nat, +s: Nat) -> {Nat.is_le(P.Fric.take(f, a, s), a) == True{} : Bool}:
  pick_le(Bool.and(Nat.is_le(Nat.min(a, Nat.div(Nat.mul(f, a), s)), a),
      Nat.is_le(Nat.mul(Nat.min(a, Nat.div(Nat.mul(f, a), s)), s), Nat.mul(f, a))),
    Nat.min(a, Nat.div(Nat.mul(f, a), s)), a,
    Nat.is_le(Nat.mul(Nat.min(a, Nat.div(Nat.mul(f, a), s)), s), Nat.mul(f, a)), {==})

# (y + x) - y == x
def sub_back(+y: Nat, +x: Nat) -> {Nat.sub(Nat.add(y, x), y) == x : Nat}:
  match y:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n+q:
      sub_back(q, x)

# t <= a gives a - (a - t) == t
def sub_sub(+a: Nat, +t: Nat, h: {Nat.is_le(t, a) == True{} : Bool}) -> {Nat.sub(a, Nat.sub(a, t)) == t : Nat}:
  %sub_add(t, a, h) : {Nat.sub(_, Nat.sub(a, t)) == t : Nat}
  %R.add_comm(Nat.sub(a, t), t) : {Nat.sub(_, Nat.sub(a, t)) == t : Nat}
  sub_back(Nat.sub(a, t), t)

def mag_cut(+t: Nat, v: P.Z) -> {Nat.sub(P.Z.mag(v), t) == P.Z.mag(P.Z.cut(t, v)) : Nat}:
  match v:
    case P.Pos{+a}:
      {==}
    case P.Neg{+a}:
      {==}

# the work-energy theorem for a tick of friction, taking t from a and u from c
def work_id(+a: Nat, +t: Nat, +c: Nat, +u: Nat, +ht: {Nat.is_le(t, a) == True{} : Bool}, +hu: {Nat.is_le(u, c) == True{} : Bool})
  -> {Nat.add(Nat.mul(a, a), Nat.mul(c, c))
      == Nat.add(Nat.add(Nat.mul(Nat.sub(a, t), Nat.sub(a, t)), Nat.mul(Nat.sub(c, u), Nat.sub(c, u))),
           Nat.add(Nat.mul(Nat.sub(a, Nat.sub(a, t)), Nat.add(a, Nat.sub(a, t))),
                   Nat.mul(Nat.sub(c, Nat.sub(c, u)), Nat.add(c, Nat.sub(c, u))))) : Nat}:
  %Equal.sym(Nat, Nat.sub(a, Nat.sub(a, t)), t, sub_sub(a, t, ht))
    : {Nat.add(Nat.mul(a, a), Nat.mul(c, c))
      == Nat.add(Nat.add(Nat.mul(Nat.sub(a, t), Nat.sub(a, t)), Nat.mul(Nat.sub(c, u), Nat.sub(c, u))),
           Nat.add(Nat.mul(_, Nat.add(a, Nat.sub(a, t))),
                   Nat.mul(Nat.sub(c, Nat.sub(c, u)), Nat.add(c, Nat.sub(c, u))))) : Nat}
  %Equal.sym(Nat, Nat.sub(c, Nat.sub(c, u)), u, sub_sub(c, u, hu))
    : {Nat.add(Nat.mul(a, a), Nat.mul(c, c))
      == Nat.add(Nat.add(Nat.mul(Nat.sub(a, t), Nat.sub(a, t)), Nat.mul(Nat.sub(c, u), Nat.sub(c, u))),
           Nat.add(Nat.mul(t, Nat.add(a, Nat.sub(a, t))), Nat.mul(_, Nat.add(c, Nat.sub(c, u))))) : Nat}
  %sub_add(t, a, ht)
    : {Nat.add(Nat.mul(_, _), Nat.mul(c, c))
      == Nat.add(Nat.add(Nat.mul(Nat.sub(a, t), Nat.sub(a, t)), Nat.mul(Nat.sub(c, u), Nat.sub(c, u))),
           Nat.add(Nat.mul(t, Nat.add(_, Nat.sub(a, t))), Nat.mul(u, Nat.add(c, Nat.sub(c, u))))) : Nat}
  %sub_add(u, c, hu)
    : {Nat.add(Nat.mul(Nat.add(t, Nat.sub(a, t)), Nat.add(t, Nat.sub(a, t))), Nat.mul(_, _))
      == Nat.add(Nat.add(Nat.mul(Nat.sub(a, t), Nat.sub(a, t)), Nat.mul(Nat.sub(c, u), Nat.sub(c, u))),
           Nat.add(Nat.mul(t, Nat.add(Nat.add(t, Nat.sub(a, t)), Nat.sub(a, t))), Nat.mul(u, Nat.add(_, Nat.sub(c, u))))) : Nat}
  R.eq([t, Nat.sub(a, t), u, Nat.sub(c, u)],
    R.Add{R.Mul{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.V{0n}, R.V{1n}}}, R.Mul{R.Add{R.V{2n}, R.V{3n}}, R.Add{R.V{2n}, R.V{3n}}}},
    R.Add{R.Add{R.Mul{R.V{1n}, R.V{1n}}, R.Mul{R.V{3n}, R.V{3n}}},
          R.Add{R.Mul{R.V{0n}, R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{1n}}}, R.Mul{R.V{2n}, R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{3n}}}}},
    {==})

# a sliding component moves by v + v' (same direction)
def kin_cut(+x: Nat, +t: Nat, v: P.Z, fx: {P.Z.fits(x, P.Z.add(v, P.Z.cut(t, v))) == True{} : Bool})
  -> {Nat.add(P.Z.shift(x, P.Z.add(v, P.Z.cut(t, v))), Nat.add(P.Z.neg(v), P.Z.neg(P.Z.cut(t, v))))
      == Nat.add(x, Nat.add(P.Z.pos(v), P.Z.pos(P.Z.cut(t, v)))) : Nat}:
  match v:
    case P.Pos{+a}:
      hkin_pos(x, a, Nat.sub(a, t))
    case P.Neg{+a}:
      hkin_neg(x, a, Nat.sub(a, t), fx)

def FW(+x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +b2: P.Body) -> Type:
  {Nat.add(Nat.mul(P.Z.mag(vx), P.Z.mag(vx)), Nat.mul(P.Z.mag(vz), P.Z.mag(vz)))
    == Nat.add(Nat.add(Nat.mul(P.Z.mag(P.Body.vx(b2)), P.Z.mag(P.Body.vx(b2))), Nat.mul(P.Z.mag(P.Body.vz(b2)), P.Z.mag(P.Body.vz(b2)))),
         Nat.add(Nat.mul(Nat.sub(P.Z.mag(vx), P.Z.mag(P.Body.vx(b2))), Nat.add(P.Z.mag(vx), P.Z.mag(P.Body.vx(b2)))),
                 Nat.mul(Nat.sub(P.Z.mag(vz), P.Z.mag(P.Body.vz(b2))), Nat.add(P.Z.mag(vz), P.Z.mag(P.Body.vz(b2)))))) : Nat}
  & {Nat.add(P.Body.x(b2), Nat.add(P.Z.neg(vx), P.Z.neg(P.Body.vx(b2))))
    == Nat.add(x, Nat.add(P.Z.pos(vx), P.Z.pos(P.Body.vx(b2)))) : Nat}
  & {Nat.add(P.Body.z(b2), Nat.add(P.Z.neg(vz), P.Z.neg(P.Body.vz(b2))))
    == Nat.add(z, Nat.add(P.Z.pos(vz), P.Z.pos(P.Body.vz(b2)))) : Nat}
  & {P.Body.y(b2) == y : Nat}

def fw_ok(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z,
  free: FG(s, g, obs, x, y, z, vx, vz, fx, fz))
  -> {Bool.and(P.Z.fits(x, P.Z.add(vx, fx)), P.Z.fits(z, P.Z.add(vz, fz))) == True{} : Bool}:
  x_gnd_ok(s, Ok1(s, obs, vx, x, y, z, fx), g, obs, vz, P.Z.add(vx, fx), x, y, z, fx, P.Pos{0n}, fz, {==}, free)

def fwork(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +t1: Nat, +t2: Nat,
  h1: {Nat.is_le(t1, P.Z.mag(vx)) == True{} : Bool}, h2: {Nat.is_le(t2, P.Z.mag(vz)) == True{} : Bool},
  +free: FG(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz)))
  -> FW(x, y, z, vx, vz, GB(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz))):
  %x_gnd_eq(s, Ok1(s, obs, vx, x, y, z, P.Z.cut(t1, vx)), g, obs, vz, P.Z.add(vx, P.Z.cut(t1, vx)), x, y, z, P.Z.cut(t1, vx), P.Pos{0n},
      P.Z.cut(t2, vz), free)
    : FW(x, y, z, vx, vz, _)
  %mag_cut(t1, vx)
    : {Nat.add(Nat.mul(P.Z.mag(vx), P.Z.mag(vx)), Nat.mul(P.Z.mag(vz), P.Z.mag(vz)))
      == Nat.add(Nat.add(Nat.mul(_, _), Nat.mul(P.Z.mag(P.Z.cut(t2, vz)), P.Z.mag(P.Z.cut(t2, vz)))),
           Nat.add(Nat.mul(Nat.sub(P.Z.mag(vx), _), Nat.add(P.Z.mag(vx), _)),
                   Nat.mul(Nat.sub(P.Z.mag(vz), P.Z.mag(P.Z.cut(t2, vz))), Nat.add(P.Z.mag(vz), P.Z.mag(P.Z.cut(t2, vz)))))) : Nat}
    & {Nat.add(P.Z.shift(x, P.Z.add(vx, P.Z.cut(t1, vx))), Nat.add(P.Z.neg(vx), P.Z.neg(P.Z.cut(t1, vx))))
      == Nat.add(x, Nat.add(P.Z.pos(vx), P.Z.pos(P.Z.cut(t1, vx)))) : Nat}
    & {Nat.add(P.Z.shift(z, P.Z.add(vz, P.Z.cut(t2, vz))), Nat.add(P.Z.neg(vz), P.Z.neg(P.Z.cut(t2, vz))))
      == Nat.add(z, Nat.add(P.Z.pos(vz), P.Z.pos(P.Z.cut(t2, vz)))) : Nat}
    & {y == y : Nat}
  %mag_cut(t2, vz)
    : {Nat.add(Nat.mul(P.Z.mag(vx), P.Z.mag(vx)), Nat.mul(P.Z.mag(vz), P.Z.mag(vz)))
      == Nat.add(Nat.add(Nat.mul(Nat.sub(P.Z.mag(vx), t1), Nat.sub(P.Z.mag(vx), t1)), Nat.mul(_, _)),
           Nat.add(Nat.mul(Nat.sub(P.Z.mag(vx), Nat.sub(P.Z.mag(vx), t1)), Nat.add(P.Z.mag(vx), Nat.sub(P.Z.mag(vx), t1))),
                   Nat.mul(Nat.sub(P.Z.mag(vz), _), Nat.add(P.Z.mag(vz), _)))) : Nat}
    & {Nat.add(P.Z.shift(x, P.Z.add(vx, P.Z.cut(t1, vx))), Nat.add(P.Z.neg(vx), P.Z.neg(P.Z.cut(t1, vx))))
      == Nat.add(x, Nat.add(P.Z.pos(vx), P.Z.pos(P.Z.cut(t1, vx)))) : Nat}
    & {Nat.add(P.Z.shift(z, P.Z.add(vz, P.Z.cut(t2, vz))), Nat.add(P.Z.neg(vz), P.Z.neg(P.Z.cut(t2, vz))))
      == Nat.add(z, Nat.add(P.Z.pos(vz), P.Z.pos(P.Z.cut(t2, vz)))) : Nat}
    & {y == y : Nat}
  (work_id(P.Z.mag(vx), t1, P.Z.mag(vz), t2, h1, h2),
   kin_cut(x, t1, vx, and_l(P.Z.fits(x, P.Z.add(vx, P.Z.cut(t1, vx))), P.Z.fits(z, P.Z.add(vz, P.Z.cut(t2, vz))),
     fw_ok(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), free))),
   kin_cut(z, t2, vz, and_r(P.Z.fits(x, P.Z.add(vx, P.Z.cut(t1, vx))), P.Z.fits(z, P.Z.add(vz, P.Z.cut(t2, vz))),
     fw_ok(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), free))),
   {==})

def Laws.friction_work(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          fwork(s, g, obs, x, y, z, vx, vz, T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), T2(Nat.div(Nat.mul(mu, g), 256n), vx, vz),
            take_le(Nat.div(Nat.mul(mu, g), 256n), P.Z.mag(vx), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))),
            take_le(Nat.div(Nat.mul(mu, g), 256n), P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))), free)
        case False{}:
          Empty.absurd(FW(x, y, z, vx, vz, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(),
              P.Body{x, y, z, vx, vy, vz, False{}, hit}))), clash2(stand))

# Order
# -----

def le_trans(+x: Nat, +y: Nat, +z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool})
  -> {Nat.is_le(x, z) == True{} : Bool}:
  le_of(x, Nat.add(Nat.sub(y, x), Nat.sub(z, y)), z,
    %sub_add(y, z, h2) : {Nat.add(x, Nat.add(Nat.sub(y, x), Nat.sub(z, y))) == _ : Nat}
    %sub_add(x, y, h1) : {Nat.add(x, Nat.add(Nat.sub(y, x), Nat.sub(z, y))) == Nat.add(_, Nat.sub(z, y)) : Nat}
    Equal.sym(Nat, Nat.add(Nat.add(x, Nat.sub(y, x)), Nat.sub(z, y)), Nat.add(x, Nat.add(Nat.sub(y, x), Nat.sub(z, y))),
      R.add_assoc(x, Nat.sub(y, x), Nat.sub(z, y))))

def le_sq(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.mul(x, x), Nat.mul(y, y)) == True{} : Bool}:
  le_of(Nat.mul(x, x), Nat.add(Nat.add(Nat.mul(x, Nat.sub(y, x)), Nat.mul(x, Nat.sub(y, x))), Nat.mul(Nat.sub(y, x), Nat.sub(y, x))),
    Nat.mul(y, y),
    %sub_add(x, y, h)
      : {Nat.add(Nat.mul(x, x), Nat.add(Nat.add(Nat.mul(x, Nat.sub(y, x)), Nat.mul(x, Nat.sub(y, x))), Nat.mul(Nat.sub(y, x), Nat.sub(y, x))))
         == Nat.mul(_, _) : Nat}
    R.eq([x, Nat.sub(y, x)],
      R.Add{R.Mul{R.V{0n}, R.V{0n}}, R.Add{R.Add{R.Mul{R.V{0n}, R.V{1n}}, R.Mul{R.V{0n}, R.V{1n}}}, R.Mul{R.V{1n}, R.V{1n}}}},
      R.Mul{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.V{0n}, R.V{1n}}}, {==}))

def le_add2(+x: Nat, +y: Nat, +u: Nat, +v: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(u, v) == True{} : Bool})
  -> {Nat.is_le(Nat.add(x, u), Nat.add(y, v)) == True{} : Bool}:
  le_of(Nat.add(x, u), Nat.add(Nat.sub(y, x), Nat.sub(v, u)), Nat.add(y, v),
    %sub_add(x, y, h1) : {Nat.add(Nat.add(x, u), Nat.add(Nat.sub(y, x), Nat.sub(v, u))) == Nat.add(_, v) : Nat}
    %sub_add(u, v, h2) : {Nat.add(Nat.add(x, u), Nat.add(Nat.sub(y, x), Nat.sub(v, u))) == Nat.add(Nat.add(x, Nat.sub(y, x)), _) : Nat}
    R.eq([x, u, Nat.sub(y, x), Nat.sub(v, u)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.V{2n}, R.V{3n}}},
      R.Add{R.Add{R.V{0n}, R.V{2n}}, R.Add{R.V{1n}, R.V{3n}}}, {==}))

def le_mul_l(+c: Nat, +x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(c, x), Nat.mul(c, y)) == True{} : Bool}:
  le_of(Nat.mul(c, x), Nat.mul(c, Nat.sub(y, x)), Nat.mul(c, y),
    %sub_add(x, y, h) : {Nat.add(Nat.mul(c, x), Nat.mul(c, Nat.sub(y, x))) == Nat.mul(c, _) : Nat}
    R.eq([c, x, Nat.sub(y, x)],
      R.Add{R.Mul{R.V{0n}, R.V{1n}}, R.Mul{R.V{0n}, R.V{2n}}}, R.Mul{R.V{0n}, R.Add{R.V{1n}, R.V{2n}}}, {==}))

def le_add_cancel(k: Nat, -u: Nat, -v: Nat, h: {Nat.is_le(Nat.add(k, u), Nat.add(k, v)) == True{} : Bool})
  -> {Nat.is_le(u, v) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+j:
      le_add_cancel(j, u, v, h)

# x (1 + c) <= y (1 + c) gives x <= y
def le_cancel(+x: Nat, +y: Nat, +c: Nat, h: {Nat.is_le(Nat.mul(x, 1n+c), Nat.mul(y, 1n+c)) == True{} : Bool})
  -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n _:
      le_add(0n, y)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, clash2(h))
    case 1n+p 1n+q:
      le_cancel(p, q, c, le_add_cancel(1n+c, Nat.mul(p, 1n+c), Nat.mul(q, 1n+c), h))

def le_zero(+x: Nat, h: {Nat.is_le(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, clash2(h))

# 0 is not 1 + m
def Dz(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+m:
      Empty

def zclash(-m: Nat, e: {0n == 1n+m : Nat}) -> Empty:
  %e : Dz(_)
  Unit{}

def sq_zero(+a: Nat, e: {Nat.mul(a, a) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, zclash(Nat.add(p, Nat.mul(p, 1n+p)),
        Equal.sym(Nat, 1n+Nat.add(p, Nat.mul(p, 1n+p)), 0n, e)))

# friction's share of a component, t s <= f a
def pick_mul(ok: Bool, +t: Nat, +a: Nat, +s: Nat, +f: Nat,
  e: {Bool.and(Nat.is_le(t, a), Nat.is_le(Nat.mul(t, s), Nat.mul(f, a))) == ok : Bool})
  -> {Nat.is_le(Nat.mul(P.Pick.n(ok, t, 0n), s), Nat.mul(f, a)) == True{} : Bool}:
  match ok:
    case True{}:
      and_r(Nat.is_le(t, a), Nat.is_le(Nat.mul(t, s), Nat.mul(f, a)), e)
    case False{}:
      le_add(0n, Nat.mul(f, a))

def take_ok(+f: Nat, +a: Nat, +s: Nat) -> {Nat.is_le(Nat.mul(P.Fric.take(f, a, s), s), Nat.mul(f, a)) == True{} : Bool}:
  pick_mul(Bool.and(Nat.is_le(Nat.min(a, Nat.div(Nat.mul(f, a), s)), a),
      Nat.is_le(Nat.mul(Nat.min(a, Nat.div(Nat.mul(f, a), s)), s), Nat.mul(f, a))),
    Nat.min(a, Nat.div(Nat.mul(f, a), s)), a, s, f, {==})

# the speed is at least |(a, c)|: a^2 + c^2 <= s^2
def speed_pick(ok: Bool, +n: Nat, +r: Nat, +ab: Nat,
  e: {Bool.and(Nat.is_le(n, Nat.mul(r, r)), Nat.is_le(r, ab)) == ok : Bool}, hab: {Nat.is_le(n, Nat.mul(ab, ab)) == True{} : Bool})
  -> {Nat.is_le(n, Nat.mul(P.Pick.n(ok, r, ab), P.Pick.n(ok, r, ab))) == True{} : Bool}:
  match ok:
    case True{}:
      and_l(Nat.is_le(n, Nat.mul(r, r)), Nat.is_le(r, ab), e)
    case False{}:
      hab

def speed_ok(+a: Nat, +c: Nat)
  -> {Nat.is_le(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.mul(P.Fric.speed(a, c), P.Fric.speed(a, c))) == True{} : Bool}:
  speed_pick(Bool.and(Nat.is_le(Nat.add(Nat.mul(a, a), Nat.mul(c, c)),
        Nat.mul(P.Fric.ceil(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), P.Fric.floor(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.add(a, c))),
          P.Fric.ceil(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), P.Fric.floor(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.add(a, c))))),
      Nat.is_le(P.Fric.ceil(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), P.Fric.floor(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.add(a, c))),
        Nat.add(a, c))),
    Nat.add(Nat.mul(a, a), Nat.mul(c, c)),
    P.Fric.ceil(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), P.Fric.floor(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.add(a, c))),
    Nat.add(a, c), {==},
    le_of(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.add(Nat.mul(a, c), Nat.mul(a, c)), Nat.mul(Nat.add(a, c), Nat.add(a, c)),
      R.eq([a, c],
        R.Add{R.Add{R.Mul{R.V{0n}, R.V{0n}}, R.Mul{R.V{1n}, R.V{1n}}}, R.Add{R.Mul{R.V{0n}, R.V{1n}}, R.Mul{R.V{0n}, R.V{1n}}}},
        R.Mul{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.V{0n}, R.V{1n}}}, {==})))

# (t1^2 + t2^2) s^2 <= f^2 s^2
def coulomb_pos(+f: Nat, +a: Nat, +c: Nat, +s: Nat, +t1: Nat, +t2: Nat,
  hk1: {Nat.is_le(Nat.mul(t1, s), Nat.mul(f, a)) == True{} : Bool}, hk2: {Nat.is_le(Nat.mul(t2, s), Nat.mul(f, c)) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.mul(s, s)) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(Nat.add(Nat.mul(t1, t1), Nat.mul(t2, t2)), Nat.mul(s, s)), Nat.mul(Nat.mul(f, f), Nat.mul(s, s))) == True{} : Bool}:
  %R.eq([t1, t2, s],
      R.Add{R.Mul{R.Mul{R.V{0n}, R.V{2n}}, R.Mul{R.V{0n}, R.V{2n}}}, R.Mul{R.Mul{R.V{1n}, R.V{2n}}, R.Mul{R.V{1n}, R.V{2n}}}},
      R.Mul{R.Add{R.Mul{R.V{0n}, R.V{0n}}, R.Mul{R.V{1n}, R.V{1n}}}, R.Mul{R.V{2n}, R.V{2n}}}, {==})
    : {Nat.is_le(_, Nat.mul(Nat.mul(f, f), Nat.mul(s, s))) == True{} : Bool}
  le_trans(Nat.add(Nat.mul(Nat.mul(t1, s), Nat.mul(t1, s)), Nat.mul(Nat.mul(t2, s), Nat.mul(t2, s))),
    Nat.add(Nat.mul(Nat.mul(f, a), Nat.mul(f, a)), Nat.mul(Nat.mul(f, c), Nat.mul(f, c))),
    Nat.mul(Nat.mul(f, f), Nat.mul(s, s)),
    le_add2(Nat.mul(Nat.mul(t1, s), Nat.mul(t1, s)), Nat.mul(Nat.mul(f, a), Nat.mul(f, a)),
      Nat.mul(Nat.mul(t2, s), Nat.mul(t2, s)), Nat.mul(Nat.mul(f, c), Nat.mul(f, c)),
      le_sq(Nat.mul(t1, s), Nat.mul(f, a), hk1), le_sq(Nat.mul(t2, s), Nat.mul(f, c), hk2)),
    %R.eq([f, a, c],
        R.Mul{R.Mul{R.V{0n}, R.V{0n}}, R.Add{R.Mul{R.V{1n}, R.V{1n}}, R.Mul{R.V{2n}, R.V{2n}}}},
        R.Add{R.Mul{R.Mul{R.V{0n}, R.V{1n}}, R.Mul{R.V{0n}, R.V{1n}}}, R.Mul{R.Mul{R.V{0n}, R.V{2n}}, R.Mul{R.V{0n}, R.V{2n}}}}, {==})
      : {Nat.is_le(_, Nat.mul(Nat.mul(f, f), Nat.mul(s, s))) == True{} : Bool}
    le_mul_l(Nat.mul(f, f), Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.mul(s, s), hs))

# nothing slides (speed 0): nothing to take
def coulomb_zero(+f: Nat, +a: Nat, +c: Nat, +t1: Nat, +t2: Nat,
  hl1: {Nat.is_le(t1, a) == True{} : Bool}, hl2: {Nat.is_le(t2, c) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), 0n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(t1, t1), Nat.mul(t2, t2)), Nat.mul(f, f)) == True{} : Bool}:
  %Equal.sym(Nat, t1, 0n, le_zero(t1,
      %sq_zero(a, le_zero(Nat.mul(a, a), le_trans(Nat.mul(a, a), Nat.add(Nat.mul(a, a), Nat.mul(c, c)), 0n,
          le_add(Nat.mul(a, a), Nat.mul(c, c)), hs))) : {Nat.is_le(t1, _) == True{} : Bool}
      hl1))
    : {Nat.is_le(Nat.add(Nat.mul(_, _), Nat.mul(t2, t2)), Nat.mul(f, f)) == True{} : Bool}
  %Equal.sym(Nat, t2, 0n, le_zero(t2,
      %sq_zero(c, le_zero(Nat.mul(c, c), le_trans(Nat.mul(c, c), Nat.add(Nat.mul(a, a), Nat.mul(c, c)), 0n,
          le_of(Nat.mul(c, c), Nat.mul(a, a), Nat.add(Nat.mul(a, a), Nat.mul(c, c)), R.add_comm(Nat.mul(c, c), Nat.mul(a, a))), hs)))
        : {Nat.is_le(t2, _) == True{} : Bool}
      hl2))
    : {Nat.is_le(Nat.add(Nat.mul(0n, 0n), Nat.mul(_, _)), Nat.mul(f, f)) == True{} : Bool}
  le_add(0n, Nat.mul(f, f))

def coulomb_core(+f: Nat, +a: Nat, +c: Nat, +s: Nat, +t1: Nat, +t2: Nat,
  hk1: {Nat.is_le(Nat.mul(t1, s), Nat.mul(f, a)) == True{} : Bool}, hk2: {Nat.is_le(Nat.mul(t2, s), Nat.mul(f, c)) == True{} : Bool},
  hl1: {Nat.is_le(t1, a) == True{} : Bool}, hl2: {Nat.is_le(t2, c) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(Nat.mul(a, a), Nat.mul(c, c)), Nat.mul(s, s)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(t1, t1), Nat.mul(t2, t2)), Nat.mul(f, f)) == True{} : Bool}:
  match s:
    case 0n:
      coulomb_zero(f, a, c, t1, t2, hl1, hl2, hs)
    case 1n+s0:
      le_cancel(Nat.add(Nat.mul(t1, t1), Nat.mul(t2, t2)), Nat.mul(f, f), Nat.add(s0, Nat.mul(s0, 1n+s0)),
        coulomb_pos(f, a, c, 1n+s0, t1, t2, hk1, hk2, hs))

def CF(+vx: P.Z, +vz: P.Z, +f: Nat, +b2: P.Body) -> Type:
  {Nat.is_le(Nat.add(Nat.mul(Nat.sub(P.Z.mag(vx), P.Z.mag(P.Body.vx(b2))), Nat.sub(P.Z.mag(vx), P.Z.mag(P.Body.vx(b2)))),
                     Nat.mul(Nat.sub(P.Z.mag(vz), P.Z.mag(P.Body.vz(b2))), Nat.sub(P.Z.mag(vz), P.Z.mag(P.Body.vz(b2))))),
             Nat.mul(f, f)) == True{} : Bool}

def cfric(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +f: Nat,
  free: FG(s, g, obs, x, y, z, vx, vz, P.Z.cut(T1(f, vx, vz), vx), P.Z.cut(T2(f, vx, vz), vz)))
  -> CF(vx, vz, f, GB(s, g, obs, x, y, z, vx, vz, P.Z.cut(T1(f, vx, vz), vx), P.Z.cut(T2(f, vx, vz), vz))):
  %x_gnd_eq(s, Ok1(s, obs, vx, x, y, z, P.Z.cut(T1(f, vx, vz), vx)), g, obs, vz, P.Z.add(vx, P.Z.cut(T1(f, vx, vz), vx)), x, y, z,
      P.Z.cut(T1(f, vx, vz), vx), P.Pos{0n}, P.Z.cut(T2(f, vx, vz), vz), free)
    : CF(vx, vz, f, _)
  %mag_cut(T1(f, vx, vz), vx)
    : {Nat.is_le(Nat.add(Nat.mul(Nat.sub(P.Z.mag(vx), _), Nat.sub(P.Z.mag(vx), _)),
                     Nat.mul(Nat.sub(P.Z.mag(vz), P.Z.mag(P.Z.cut(T2(f, vx, vz), vz))),
                             Nat.sub(P.Z.mag(vz), P.Z.mag(P.Z.cut(T2(f, vx, vz), vz))))), Nat.mul(f, f)) == True{} : Bool}
  %mag_cut(T2(f, vx, vz), vz)
    : {Nat.is_le(Nat.add(Nat.mul(Nat.sub(P.Z.mag(vx), Nat.sub(P.Z.mag(vx), T1(f, vx, vz))),
                                 Nat.sub(P.Z.mag(vx), Nat.sub(P.Z.mag(vx), T1(f, vx, vz)))),
                     Nat.mul(Nat.sub(P.Z.mag(vz), _), Nat.sub(P.Z.mag(vz), _))), Nat.mul(f, f)) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(P.Z.mag(vx), Nat.sub(P.Z.mag(vx), T1(f, vx, vz))), T1(f, vx, vz),
      sub_sub(P.Z.mag(vx), T1(f, vx, vz), take_le(f, P.Z.mag(vx), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz)))))
    : {Nat.is_le(Nat.add(Nat.mul(_, _),
                     Nat.mul(Nat.sub(P.Z.mag(vz), Nat.sub(P.Z.mag(vz), T2(f, vx, vz))),
                             Nat.sub(P.Z.mag(vz), Nat.sub(P.Z.mag(vz), T2(f, vx, vz))))), Nat.mul(f, f)) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(P.Z.mag(vz), Nat.sub(P.Z.mag(vz), T2(f, vx, vz))), T2(f, vx, vz),
      sub_sub(P.Z.mag(vz), T2(f, vx, vz), take_le(f, P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz)))))
    : {Nat.is_le(Nat.add(Nat.mul(T1(f, vx, vz), T1(f, vx, vz)), Nat.mul(_, _)), Nat.mul(f, f)) == True{} : Bool}
  coulomb_core(f, P.Z.mag(vx), P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz)), T1(f, vx, vz), T2(f, vx, vz),
    take_ok(f, P.Z.mag(vx), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))), take_ok(f, P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))),
    take_le(f, P.Z.mag(vx), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))), take_le(f, P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))),
    speed_ok(P.Z.mag(vx), P.Z.mag(vz)))

def Laws.coulomb_friction(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit}:
      match gr:
        case True{}:
          cfric(s, g, obs, x, y, z, vx, vz, Nat.div(Nat.mul(mu, g), 256n), free)
        case False{}:
          Empty.absurd(CF(vx, vz, Nat.div(Nat.mul(mu, g), 256n), P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs,
              P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit}))), clash2(stand))

# Rest
# ----

def sub_zero_l(+n: Nat) -> {Nat.sub(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def Rest(+x: Nat, +y: Nat, +z: Nat) -> P.Body:
  P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}}

# friction on nothing moving leaves it still
def rs_drive(+f: Nat) -> {(P.Pos{0n}, P.Pos{0n}) == P.Fric.apply(f, P.Pos{0n}, P.Pos{0n}) : P.Z & P.Z}:
  %sub_zero_l(P.Fric.take(f, 0n, P.Fric.speed(0n, 0n)))
    : {(P.Pos{_}, P.Pos{_}) == P.Fric.apply(f, P.Pos{0n}, P.Pos{0n}) : P.Z & P.Z}
  {==}

def rs_y(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  on: {Bool.or(Nat.is_eq(y, 0n), P.Geo.rests(s, x, y, z, obs)) == True{} : Bool})
  -> {P.Tick.y(s, g, (Rest(x, y, z), obs)) == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}:
  %on : {P.Tick.y(s, g, (Rest(x, y, z), obs)) == (P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, _, False{}}, obs) : P.Body & List<&2, P.Body>}
  {==}

def rs_z(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  on: {Bool.or(Nat.is_eq(y, 0n), P.Geo.rests(s, x, y, z, obs)) == True{} : Bool},
  clear: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Tick.y(s, g, P.Move.z(s, obs, P.Pos{0n}, Rest(x, y, z))) == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}:
  %R.add_zero_s(z)
    : {P.Tick.y(s, g, P.Move.zgo(s, P.Geo.free(s, x, y, _, obs), obs, P.Pos{0n}, _, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}))
       == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}
  %Equal.sym(Bool, P.Geo.free(s, x, y, z, obs), True{}, clear)
    : {P.Tick.y(s, g, P.Move.zgo(s, _, obs, P.Pos{0n}, z, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}))
       == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}
  rs_y(s, g, obs, x, y, z, on)

def rs_x(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  on: {Bool.or(Nat.is_eq(y, 0n), P.Geo.rests(s, x, y, z, obs)) == True{} : Bool},
  +clear: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Tick.z(s, g, P.Pos{0n}, P.Move.x(s, obs, P.Pos{0n}, Rest(x, y, z))) == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}:
  %R.add_zero_s(x)
    : {P.Tick.z(s, g, P.Pos{0n}, P.Move.xgo(s, P.Geo.free(s, _, y, z, obs), obs, P.Pos{0n}, _, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}))
       == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}
  %Equal.sym(Bool, P.Geo.free(s, x, y, z, obs), True{}, clear)
    : {P.Tick.z(s, g, P.Pos{0n}, P.Move.xgo(s, _, obs, P.Pos{0n}, x, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}))
       == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}
  rs_z(s, g, obs, x, y, z, on, clear)

def Laws.rest_stays(k, obs, x, y, z, h, on, clear):
  match k:
    case P.K{+g, +mu, +j, +acc, +s}:
      %rs_drive(Nat.div(Nat.mul(mu, g), 256n))
        : {P.Tick.z(s, g, P.Pos{0n}, P.Move.x(s, obs, P.Pos{0n}, P.Drive.ground(P.K{g, mu, j, acc, s}, None{}, False{}, x, y, z, _)))
           == (Rest(x, y, z), obs) : P.Body & List<&2, P.Body>}
      rs_x(s, g, obs, x, y, z, on, clear)

# Energy never grows
# ------------------
# Each stage of a tick, with no input, leaves at most the energy it got:
# driving (friction only takes), each horizontal move (a push shares), the
# vertical move (flight keeps it exact, landings and bumps spend it).

def Pv(r: P.Pushed) -> P.Z:
  P.Pushed{v, obs, at} = r
  v

def Pobs(r: P.Pushed) -> List<&2, P.Body>:
  P.Pushed{v, obs, at} = r
  obs

# x <= y gives x + z <= y + z
def le_sum(+x: Nat, +y: Nat, +z: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, z), Nat.add(y, z)) == True{} : Bool}:
  le_add2(x, y, z, z, h, le_refl(z))

# the same, through equalities: l == x + z, r == y + z
def le_via(+l: Nat, +r: Nat, +x: Nat, +y: Nat, +z: Nat, el: {Nat.add(x, z) == l : Nat}, er: {Nat.add(y, z) == r : Nat},
  h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(l, r) == True{} : Bool}:
  %el : {Nat.is_le(_, r) == True{} : Bool}
  %er : {Nat.is_le(Nat.add(x, z), _) == True{} : Bool}
  le_sum(x, y, z, h)

def le_eq(+x: Nat, -y: Nat, e: {x == y : Nat}) -> {Nat.is_le(x, y) == True{} : Bool}:
  %e : {Nat.is_le(x, _) == True{} : Bool}
  le_refl(x)

# a share, put back into the obstacle it met
def xput_e(+g: Nat, vw: P.Z & P.Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool,
  +oh: Bool, +rest: List<&2, P.Body>, +v: P.Z,
  h: {Nat.is_le(Nat.add(P.Z.sq(P.Share.fst(vw)), P.Z.sq(P.Share.snd(vw))), Nat.add(P.Z.sq(v), P.Z.sq(ovx))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.xput(vw, at, ox, oy, oz, ovy, ovz, og, oh, rest))),
                        P.Body.energies(g, Pobs(P.Push.xput(vw, at, ox, oy, oz, ovy, ovz, og, oh, rest)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh} <> rest))) == True{} : Bool}:
  (+v2, +w2) = vw
  le_via(
    Nat.add(P.Z.sq(v2), Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(w2), P.Z.sq(ovy)), P.Z.sq(ovz)), Nat.mul(g, oy)), P.Body.energies(g, rest))),
    Nat.add(P.Z.sq(v), Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(ovx), P.Z.sq(ovy)), P.Z.sq(ovz)), Nat.mul(g, oy)), P.Body.energies(g, rest))),
    Nat.add(P.Z.sq(v2), P.Z.sq(w2)), Nat.add(P.Z.sq(v), P.Z.sq(ovx)),
    Nat.add(Nat.add(Nat.add(P.Z.sq(ovy), P.Z.sq(ovz)), Nat.mul(g, oy)), P.Body.energies(g, rest)),
    R.eq([P.Z.sq(v2), P.Z.sq(w2), P.Z.sq(ovy), P.Z.sq(ovz), Nat.mul(g, oy), P.Body.energies(g, rest)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}, R.V{5n}}},
      R.Add{R.V{0n}, R.Add{R.Add{R.Add{R.Add{R.V{1n}, R.V{2n}}, R.V{3n}}, R.V{4n}}, R.V{5n}}}, {==}),
    R.eq([P.Z.sq(v), P.Z.sq(ovx), P.Z.sq(ovy), P.Z.sq(ovz), Nat.mul(g, oy), P.Body.energies(g, rest)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}, R.V{5n}}},
      R.Add{R.V{0n}, R.Add{R.Add{R.Add{R.Add{R.V{1n}, R.V{2n}}, R.V{3n}}, R.V{4n}}, R.V{5n}}}, {==}),
    h)

def zput_e(+g: Nat, vw: P.Z & P.Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool,
  +oh: Bool, +rest: List<&2, P.Body>, +v: P.Z,
  h: {Nat.is_le(Nat.add(P.Z.sq(P.Share.fst(vw)), P.Z.sq(P.Share.snd(vw))), Nat.add(P.Z.sq(v), P.Z.sq(ovz))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.zput(vw, at, ox, oy, oz, ovx, ovy, og, oh, rest))),
                        P.Body.energies(g, Pobs(P.Push.zput(vw, at, ox, oy, oz, ovx, ovy, og, oh, rest)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh} <> rest))) == True{} : Bool}:
  (+v2, +w2) = vw
  le_via(
    Nat.add(P.Z.sq(v2), Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(ovx), P.Z.sq(ovy)), P.Z.sq(w2)), Nat.mul(g, oy)), P.Body.energies(g, rest))),
    Nat.add(P.Z.sq(v), Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(ovx), P.Z.sq(ovy)), P.Z.sq(ovz)), Nat.mul(g, oy)), P.Body.energies(g, rest))),
    Nat.add(P.Z.sq(v2), P.Z.sq(w2)), Nat.add(P.Z.sq(v), P.Z.sq(ovz)),
    Nat.add(Nat.add(Nat.add(P.Z.sq(ovx), P.Z.sq(ovy)), Nat.mul(g, oy)), P.Body.energies(g, rest)),
    R.eq([P.Z.sq(v2), P.Z.sq(w2), P.Z.sq(ovx), P.Z.sq(ovy), Nat.mul(g, oy), P.Body.energies(g, rest)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}, R.V{5n}}},
      R.Add{R.V{0n}, R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{1n}}, R.V{4n}}, R.V{5n}}}, {==}),
    R.eq([P.Z.sq(v), P.Z.sq(ovz), P.Z.sq(ovx), P.Z.sq(ovy), Nat.mul(g, oy), P.Body.energies(g, rest)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}, R.V{5n}}},
      R.Add{R.V{0n}, R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{1n}}, R.V{4n}}, R.V{5n}}}, {==}),
    h)

def share_e(close: Bool, +v: P.Z, +w: P.Z)
  -> {Nat.is_le(Nat.add(P.Z.sq(P.Share.fst(P.Push.share(close, v, w))), P.Z.sq(P.Share.snd(P.Push.share(close, v, w)))),
                Nat.add(P.Z.sq(v), P.Z.sq(w))) == True{} : Bool}:
  match close:
    case True{}:
      Laws.push_energy(v, w)
    case False{}:
      le_refl(Nat.add(P.Z.sq(v), P.Z.sq(w)))

def cons_e(+g: Nat, +o: P.Body, r: P.Pushed, +v: P.Z, +rest: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(Pv(r)), P.Body.energies(g, Pobs(r))), Nat.add(P.Z.sq(v), P.Body.energies(g, rest))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.cons(o, r))), P.Body.energies(g, Pobs(P.Push.cons(o, r)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, o <> rest))) == True{} : Bool}:
  P.Pushed{+v2, +obs2, at} = r
  le_via(Nat.add(P.Z.sq(v2), Nat.add(P.Body.energy(g, o), P.Body.energies(g, obs2))),
    Nat.add(P.Z.sq(v), Nat.add(P.Body.energy(g, o), P.Body.energies(g, rest))),
    Nat.add(P.Z.sq(v2), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(v), P.Body.energies(g, rest)), P.Body.energy(g, o),
    R.eq([P.Z.sq(v2), P.Body.energies(g, obs2), P.Body.energy(g, o)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}, R.Add{R.V{0n}, R.Add{R.V{2n}, R.V{1n}}}, {==}),
    R.eq([P.Z.sq(v), P.Body.energies(g, rest), P.Body.energy(g, o)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}, R.Add{R.V{0n}, R.Add{R.V{2n}, R.V{1n}}}, {==}),
    h)

# a push along x: the mover's and the obstacles' energy together never grow
def push_x_e(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +y: Nat, +z: Nat, +v: P.Z, here: Bool)
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.x(s, obs, d, cx, y, z, v, here))), P.Body.energies(g, Pobs(P.Push.x(s, obs, d, cx, y, z, v, here)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, obs))) == True{} : Bool}:
  match obs here:
    case Nil{} _:
      le_refl(Nat.add(P.Z.sq(v), 0n))
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh} <> +rest True{}:
      xput_e(g, P.Push.share(P.Push.closing(d, v, ovx), v, ovx), P.Push.stop(s, d, ox), ox, oy, oz, ovx, ovy, ovz, og, oh, rest, v,
        share_e(P.Push.closing(d, v, ovx), v, ovx))
    case +o <> +rest False{}:
      cons_e(g, o, P.Push.x(s, rest, d, cx, y, z, v, P.Geo.head(s, cx, y, z, rest)), v, rest,
        push_x_e(s, g, rest, d, cx, y, z, v, P.Geo.head(s, cx, y, z, rest)))

def push_z_e(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +d: P.Z, +x: Nat, +y: Nat, +cz: Nat, +v: P.Z, here: Bool)
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.z(s, obs, d, x, y, cz, v, here))), P.Body.energies(g, Pobs(P.Push.z(s, obs, d, x, y, cz, v, here)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, obs))) == True{} : Bool}:
  match obs here:
    case Nil{} _:
      le_refl(Nat.add(P.Z.sq(v), 0n))
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh} <> +rest True{}:
      zput_e(g, P.Push.share(P.Push.closing(d, v, ovz), v, ovz), P.Push.stop(s, d, oz), ox, oy, oz, ovx, ovy, ovz, og, oh, rest, v,
        share_e(P.Push.closing(d, v, ovz), v, ovz))
    case +o <> +rest False{}:
      cons_e(g, o, P.Push.z(s, rest, d, x, y, cz, v, P.Geo.head(s, x, y, cz, rest)), v, rest,
        push_z_e(s, g, rest, d, x, y, cz, v, P.Geo.head(s, x, y, cz, rest)))

# the energy of a body after a horizontal push against before (the pushed
# component: a2 from a, the other two and the height unchanged)
def res_e(+g: Nat, +a: P.Z, +a2: P.Z, +p: Nat, +q: Nat, +y: Nat, +obs: List<&2, P.Body>, +obs2: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(a2), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(a), P.Body.energies(g, obs))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(a2), p), q), Nat.mul(g, y)), P.Body.energies(g, obs2)),
                Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(a), p), q), Nat.mul(g, y)), P.Body.energies(g, obs))) == True{} : Bool}:
  le_via(Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(a2), p), q), Nat.mul(g, y)), P.Body.energies(g, obs2)),
    Nat.add(Nat.add(Nat.add(Nat.add(P.Z.sq(a), p), q), Nat.mul(g, y)), P.Body.energies(g, obs)),
    Nat.add(P.Z.sq(a2), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(a), P.Body.energies(g, obs)), Nat.add(Nat.add(p, q), Nat.mul(g, y)),
    R.eq([P.Z.sq(a2), P.Body.energies(g, obs2), p, q, Nat.mul(g, y)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}},
      R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.V{2n}}, R.V{3n}}, R.V{4n}}, R.V{1n}}, {==}),
    R.eq([P.Z.sq(a), P.Body.energies(g, obs), p, q, Nat.mul(g, y)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}},
      R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.V{2n}}, R.V{3n}}, R.V{4n}}, R.V{1n}}, {==}),
    h)

# the same with the pushed component last (z)
def res_ez(+g: Nat, +a: P.Z, +a2: P.Z, +p: Nat, +q: Nat, +y: Nat, +obs: List<&2, P.Body>, +obs2: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(a2), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(a), P.Body.energies(g, obs))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(Nat.add(p, q), P.Z.sq(a2)), Nat.mul(g, y)), P.Body.energies(g, obs2)),
                Nat.add(Nat.add(Nat.add(Nat.add(p, q), P.Z.sq(a)), Nat.mul(g, y)), P.Body.energies(g, obs))) == True{} : Bool}:
  le_via(Nat.add(Nat.add(Nat.add(Nat.add(p, q), P.Z.sq(a2)), Nat.mul(g, y)), P.Body.energies(g, obs2)),
    Nat.add(Nat.add(Nat.add(Nat.add(p, q), P.Z.sq(a)), Nat.mul(g, y)), P.Body.energies(g, obs)),
    Nat.add(P.Z.sq(a2), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(a), P.Body.energies(g, obs)), Nat.add(Nat.add(p, q), Nat.mul(g, y)),
    R.eq([P.Z.sq(a2), P.Body.energies(g, obs2), p, q, Nat.mul(g, y)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}},
      R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{0n}}, R.V{4n}}, R.V{1n}}, {==}),
    R.eq([P.Z.sq(a), P.Body.energies(g, obs), p, q, Nat.mul(g, y)],
      R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}},
      R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{0n}}, R.V{4n}}, R.V{1n}}, {==}),
    h)


def xput_me(ok: Bool, +g: Nat, +obs2: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +obs: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(v), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(vx), P.Body.energies(g, obs))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xput(ok, obs2, cx, x, y, z, v, vy, vz, gr))), P.Body.energies(g, P.Tick.obs(P.Move.xput(ok, obs2, cx, x, y, z, v, vy, vz, gr)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))))) == True{} : Bool}:
  match ok:
    case True{}:
      res_e(g, vx, v, P.Z.sq(vy), P.Z.sq(vz), y, obs, obs2, h)
    case False{}:
      res_e(g, vx, v, P.Z.sq(vy), P.Z.sq(vz), y, obs, obs2, h)

def xhit_me(+s: Nat, +g: Nat, r: P.Pushed, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool,
  +obs: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(Pv(r)), P.Body.energies(g, Pobs(r))), Nat.add(P.Z.sq(vx), P.Body.energies(g, obs))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xhit(s, r, x, y, z, vy, vz, gr))), P.Body.energies(g, P.Tick.obs(P.Move.xhit(s, r, x, y, z, vy, vz, gr)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))))) == True{} : Bool}:
  P.Pushed{+v, +obs2, at} = r
  match at:
    case None{}:
      res_e(g, vx, v, P.Z.sq(vy), P.Z.sq(vz), y, obs, obs2, h)
    case Some{+cx}:
      xput_me(P.Geo.free(s, cx, y, z, obs2), g, obs2, cx, x, y, z, v, vx, vy, vz, gr, hit, obs, h)

def xgo_me(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xgo(s, ok, obs, d, cx, x, y, z, vx, vy, vz, gr, hit))), P.Body.energies(g, P.Tick.obs(P.Move.xgo(s, ok, obs, d, cx, x, y, z, vx, vy, vz, gr, hit)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs)))))
      == True{} : Bool}:
  match ok:
    case True{}:
      le_refl(Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs)))))
    case False{}:
      xhit_me(s, g, P.Push.x(s, obs, d, cx, y, z, vx, P.Geo.head(s, cx, y, z, obs)), x, y, z, vx, vy, vz, gr, hit, obs,
        push_x_e(s, g, obs, d, cx, y, z, vx, P.Geo.head(s, cx, y, z, obs)))

def mx_e(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.x(s, obs, v0, b))), P.Body.energies(g, P.Tick.obs(P.Move.x(s, obs, v0, b)))), Nat.add(P.Body.energy(g, P.Tick.body((b, obs))), P.Body.energies(g, P.Tick.obs((b, obs))))) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit} = b
  xgo_me(s, Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, obs)), g, obs,
    P.Z.add(v0, vx), P.Z.shift(x, P.Z.add(v0, vx)), x, y, z, vx, vy, vz, gr, hit)

def zput_me(ok: Bool, +g: Nat, +obs2: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +obs: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(v), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(vz), P.Body.energies(g, obs))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.zput(ok, obs2, cz, x, y, z, vx, vy, v, gr))), P.Body.energies(g, P.Tick.obs(P.Move.zput(ok, obs2, cz, x, y, z, vx, vy, v, gr)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))))) == True{} : Bool}:
  match ok:
    case True{}:
      res_ez(g, vz, v, P.Z.sq(vx), P.Z.sq(vy), y, obs, obs2, h)
    case False{}:
      res_ez(g, vz, v, P.Z.sq(vx), P.Z.sq(vy), y, obs, obs2, h)

def zhit_me(+s: Nat, +g: Nat, r: P.Pushed, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool,
  +obs: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(Pv(r)), P.Body.energies(g, Pobs(r))), Nat.add(P.Z.sq(vz), P.Body.energies(g, obs))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.zhit(s, r, x, y, z, vx, vy, gr))), P.Body.energies(g, P.Tick.obs(P.Move.zhit(s, r, x, y, z, vx, vy, gr)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))))) == True{} : Bool}:
  P.Pushed{+v, +obs2, at} = r
  match at:
    case None{}:
      res_ez(g, vz, v, P.Z.sq(vx), P.Z.sq(vy), y, obs, obs2, h)
    case Some{+cz}:
      zput_me(P.Geo.free(s, x, y, cz, obs2), g, obs2, cz, x, y, z, vx, vy, v, vz, gr, hit, obs, h)

def zgo_me(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.zgo(s, ok, obs, d, cz, x, y, z, vx, vy, vz, gr, hit))), P.Body.energies(g, P.Tick.obs(P.Move.zgo(s, ok, obs, d, cz, x, y, z, vx, vy, vz, gr, hit)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs)))))
      == True{} : Bool}:
  match ok:
    case True{}:
      le_refl(Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit}, obs)))))
    case False{}:
      zhit_me(s, g, P.Push.z(s, obs, d, x, y, cz, vz, P.Geo.head(s, x, y, cz, obs)), x, y, z, vx, vy, vz, gr, hit, obs,
        push_z_e(s, g, obs, d, x, y, cz, vz, P.Geo.head(s, x, y, cz, obs)))

def mz_e(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.z(s, obs, v0, b))), P.Body.energies(g, P.Tick.obs(P.Move.z(s, obs, v0, b)))), Nat.add(P.Body.energy(g, P.Tick.body((b, obs))), P.Body.energies(g, P.Tick.obs((b, obs))))) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit} = b
  zgo_me(s, Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), obs)), g, obs,
    P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr, hit)

# a body stopped (vy = 0) at height at most y has at most its energy
def stop_e(+A: Nat, +C: Nat, +S: Nat, +g: Nat, +y: Nat, +fl: Nat, h: {Nat.is_le(fl, y) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(A, 0n), C), Nat.mul(g, fl)), Nat.add(Nat.add(Nat.add(A, S), C), Nat.mul(g, y))) == True{} : Bool}:
  le_of(Nat.add(Nat.add(Nat.add(A, 0n), C), Nat.mul(g, fl)), Nat.add(S, Nat.mul(g, Nat.sub(y, fl))),
    Nat.add(Nat.add(Nat.add(A, S), C), Nat.mul(g, y)),
    %sub_add(fl, y, h) : {Nat.add(Nat.add(Nat.add(Nat.add(A, 0n), C), Nat.mul(g, fl)), Nat.add(S, Nat.mul(g, Nat.sub(y, fl))))
      == Nat.add(Nat.add(Nat.add(A, S), C), Nat.mul(g, _)) : Nat}
    R.eq([A, C, S, g, fl, Nat.sub(y, fl)],
      R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.N{0n}}, R.V{1n}}, R.Mul{R.V{3n}, R.V{4n}}}, R.Add{R.V{2n}, R.Mul{R.V{3n}, R.V{5n}}}},
      R.Add{R.Add{R.Add{R.V{0n}, R.V{2n}}, R.V{1n}}, R.Mul{R.V{3n}, R.Add{R.V{4n}, R.V{5n}}}}, {==}))

def rise_e(ok: Bool, +g: Nat, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z, +vy: P.Z, +hit: Bool,
  he: {Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(v)), P.Z.sq(vz)), Nat.mul(g, Nat.add(y, p)))
       == Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)) : Nat})
  -> {Nat.is_le(P.Body.energy(g, P.Move.rise(ok, x, y, z, p, vx, v, vz, hit)),
                Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  match ok:
    case True{}:
      le_eq(Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(v)), P.Z.sq(vz)), Nat.mul(g, Nat.add(y, p))),
        Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)), he)
    case False{}:
      stop_e(P.Z.sq(vx), P.Z.sq(vz), P.Z.sq(vy), g, y, y, le_refl(y))

def land_e(ok: Bool, +g: Nat, +x: Nat, +y: Nat, +z: Nat, +fl: Nat, +vx: P.Z, +vz: P.Z, +vy: P.Z, -rest: Bool,
  eok: {Bool.and(Nat.is_le(fl, y), rest) == ok : Bool})
  -> {Nat.is_le(P.Body.energy(g, P.Move.land(ok, x, y, z, fl, vx, vz)),
                Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  match ok:
    case True{}:
      stop_e(P.Z.sq(vx), P.Z.sq(vz), P.Z.sq(vy), g, y, fl, and_l(Nat.is_le(fl, y), rest, eok))
    case False{}:
      stop_e(P.Z.sq(vx), P.Z.sq(vz), P.Z.sq(vy), g, y, y, le_refl(y))

def fall_e(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +fl: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +vy: P.Z, +hit: Bool,
  eok: {Bool.and(Nat.is_le(Nat.add(fl, q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)) == ok : Bool},
  hf: {Nat.is_le(q, y) == True{} : Bool}
    -> {Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(v)), P.Z.sq(vz)), Nat.mul(g, Nat.sub(y, q)))
        == Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)) : Nat})
  -> {Nat.is_le(P.Body.energy(g, P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, hit)),
                Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  match ok:
    case True{}:
      le_eq(Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(v)), P.Z.sq(vz)), Nat.mul(g, Nat.sub(y, q))),
        Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)),
        hf(le_addl(fl, q, y, and_l(Nat.is_le(Nat.add(fl, q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs), eok))))
    case False{}:
      land_e(Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), g, x, y, z, fl, vx, vz, vy, P.Geo.free(s, x, fl, z, obs), {==})

def fly_le(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +hit: Bool, +vy: P.Z, st: P.Z & P.Z,
  hf: {P.Z.fits(y, P.Share.snd(st)) == True{} : Bool}
    -> {Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(P.Share.fst(st))), P.Z.sq(vz)), Nat.mul(g, P.Z.shift(y, P.Share.snd(st))))
        == Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)) : Nat})
  -> {Nat.is_le(P.Body.energy(g, P.Move.fly(s, obs, x, y, z, vx, vz, hit, st)),
                Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      rise_e(P.Geo.free(s, x, Nat.add(y, p), z, obs), g, x, y, z, p, vx, v, vz, vy, hit, hf({==}))
    case P.Neg{+q}:
      fall_e(s, Bool.and(Nat.is_le(Nat.add(P.Geo.floor(s, x, y, z, obs, 0n), q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)),
        g, obs, x, y, z, q, P.Geo.floor(s, x, y, z, obs, 0n), vx, v, vz, vy, hit, {==}, hf)

def my_e(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body) -> {Nat.is_le(P.Body.energy(g, P.Move.y(s, g, obs, b)), P.Body.energy(g, b)) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit} = b
  match gr:
    case True{}:
      le_refl(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, True{}, hit}))
    case False{}:
      fly_le(s, g, obs, x, y, z, vx, vz, hit, vy, P.Fly.step(g, vy), h => fly_energy(g, y, vy, P.Z.sq(vx), P.Z.sq(vz), h))

def ty_e(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>) -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Tick.y(s, g, r))), P.Body.energies(g, P.Tick.obs(P.Tick.y(s, g, r)))), Nat.add(P.Body.energy(g, P.Tick.body(r)), P.Body.energies(g, P.Tick.obs(r)))) == True{} : Bool}:
  (+b, +obs) = r
  le_sum(P.Body.energy(g, P.Move.y(s, g, obs, b)), P.Body.energy(g, b), P.Body.energies(g, obs), my_e(s, g, obs, b))

def tz_e(+s: Nat, +g: Nat, +v0: P.Z, r: P.Body & List<&2, P.Body>) -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Tick.z(s, g, v0, r))), P.Body.energies(g, P.Tick.obs(P.Tick.z(s, g, v0, r)))), Nat.add(P.Body.energy(g, P.Tick.body(r)), P.Body.energies(g, P.Tick.obs(r)))) == True{} : Bool}:
  (+b, +obs) = r
  le_trans(Nat.add(P.Body.energy(g, P.Tick.body(P.Tick.y(s, g, P.Move.z(s, obs, v0, b)))), P.Body.energies(g, P.Tick.obs(P.Tick.y(s, g, P.Move.z(s, obs, v0, b))))), Nat.add(P.Body.energy(g, P.Tick.body(P.Move.z(s, obs, v0, b))), P.Body.energies(g, P.Tick.obs(P.Move.z(s, obs, v0, b)))), Nat.add(P.Body.energy(g, P.Tick.body((b, obs))), P.Body.energies(g, P.Tick.obs((b, obs)))),
    ty_e(s, g, P.Move.z(s, obs, v0, b)), mz_e(s, g, obs, v0, b))

def cut_sq(+t: Nat, v: P.Z) -> {Nat.is_le(P.Z.sq(P.Z.cut(t, v)), P.Z.sq(v)) == True{} : Bool}:
  match v:
    case P.Pos{+a}:
      le_sq(Nat.sub(a, t), a, sub_le(a, t))
    case P.Neg{+a}:
      le_sq(Nat.sub(a, t), a, sub_le(a, t))

# driving with no input: friction only takes
def drive_e(+s: Nat, +g: Nat, +mu: Nat, +j: Nat, +acc: Nat, b: P.Body)
  -> {Nat.is_le(P.Body.energy(g, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), b)), P.Body.energy(g, b)) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit} = b
  match gr:
    case True{}:
      le_add2(Nat.add(Nat.add(P.Z.sq(P.Z.cut(T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), vx)), 0n),
          P.Z.sq(P.Z.cut(T2(Nat.div(Nat.mul(mu, g), 256n), vx, vz), vz))),
        Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y), Nat.mul(g, y),
        le_add2(Nat.add(P.Z.sq(P.Z.cut(T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), vx)), 0n), Nat.add(P.Z.sq(vx), P.Z.sq(vy)),
          P.Z.sq(P.Z.cut(T2(Nat.div(Nat.mul(mu, g), 256n), vx, vz), vz)), P.Z.sq(vz),
          le_add2(P.Z.sq(P.Z.cut(T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), vx)), P.Z.sq(vx), 0n, P.Z.sq(vy),
            cut_sq(T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), vx), le_add(0n, P.Z.sq(vy))),
          cut_sq(T2(Nat.div(Nat.mul(mu, g), 256n), vx, vz), vz)),
        le_refl(Nat.mul(g, y)))
    case False{}:
      le_refl(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit}))

def Laws.energy_never_grows(k, obs, b):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit}:
      le_trans(Nat.add(P.Body.energy(g, P.Tick.body(P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(),
            P.Body{x, y, z, vx, vy, vz, gr, hit}))))), P.Body.energies(g, P.Tick.obs(P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(),
            P.Body{x, y, z, vx, vy, vz, gr, hit})))))),
        Nat.add(P.Body.energy(g, P.Tick.body(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit})))), P.Body.energies(g, P.Tick.obs(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit}))))),
        Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit}), P.Body.energies(g, obs)),
        tz_e(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit}))),
        le_trans(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit})))), P.Body.energies(g, P.Tick.obs(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit}))))),
          Nat.add(P.Body.energy(g, P.Tick.body((P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit}), obs))), P.Body.energies(g, P.Tick.obs((P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit}), obs)))),
          Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit}), P.Body.energies(g, obs)),
          mx_e(s, g, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit})),
          le_sum(P.Body.energy(g, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit})),
            P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit}), P.Body.energies(g, obs),
            drive_e(s, g, mu, j, acc, P.Body{x, y, z, vx, vy, vz, gr, hit}))))

# No clipping
# -----------
# Every move goes through a gate that takes it only to a free place, or
# stays where the body was (free by the invariant); a push changes the
# obstacles' velocities, never where they are.

# a tick's result: the body is clear of the obstacles
def NC(+s: Nat, -r: P.Body & List<&2, P.Body>) -> Type:
  {P.Geo.free(s, P.Body.x(P.Tick.body(r)), P.Body.y(P.Tick.body(r)), P.Body.z(P.Tick.body(r)), P.Tick.obs(r)) == True{} : Bool}

def xput_free(+s: Nat, vw: P.Z & P.Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +rest: List<&2, P.Body>, +px: Nat, +py: Nat, +pz: Nat)
  -> {P.Geo.free(s, px, py, pz, Pobs(P.Push.xput(vw, at, ox, oy, oz, ovy, ovz, og, oh, rest)))
      == P.Geo.free(s, px, py, pz, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh} <> rest) : Bool}:
  (v2, w2) = vw
  {==}

def zput_free(+s: Nat, vw: P.Z & P.Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +rest: List<&2, P.Body>, +px: Nat, +py: Nat, +pz: Nat)
  -> {P.Geo.free(s, px, py, pz, Pobs(P.Push.zput(vw, at, ox, oy, oz, ovx, ovy, og, oh, rest)))
      == P.Geo.free(s, px, py, pz, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh} <> rest) : Bool}:
  (v2, w2) = vw
  {==}

def cons_free(+s: Nat, +o: P.Body, r: P.Pushed, +rest: List<&2, P.Body>, +px: Nat, +py: Nat, +pz: Nat,
  h: {P.Geo.free(s, px, py, pz, Pobs(r)) == P.Geo.free(s, px, py, pz, rest) : Bool})
  -> {P.Geo.free(s, px, py, pz, Pobs(P.Push.cons(o, r))) == P.Geo.free(s, px, py, pz, o <> rest) : Bool}:
  P.Pushed{v, +obs2, at} = r
  %Equal.sym(Bool, P.Geo.free(s, px, py, pz, obs2), P.Geo.free(s, px, py, pz, rest), h)
    : {Bool.and(Bool.not(P.Geo.meets(s, px, py, pz, o)), _) == P.Geo.free(s, px, py, pz, o <> rest) : Bool}
  {==}

def push_x_free(+s: Nat, obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +y: Nat, +z: Nat, +v: P.Z, here: Bool, +px: Nat, +py: Nat, +pz: Nat)
  -> {P.Geo.free(s, px, py, pz, Pobs(P.Push.x(s, obs, d, cx, y, z, v, here))) == P.Geo.free(s, px, py, pz, obs) : Bool}:
  match obs here:
    case Nil{} _:
      {==}
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh} <> +rest True{}:
      xput_free(s, P.Push.share(P.Push.closing(d, v, ovx), v, ovx), P.Push.stop(s, d, ox), ox, oy, oz, ovx, ovy, ovz, og, oh, rest,
        px, py, pz)
    case +o <> +rest False{}:
      cons_free(s, o, P.Push.x(s, rest, d, cx, y, z, v, P.Geo.head(s, cx, y, z, rest)), rest, px, py, pz,
        push_x_free(s, rest, d, cx, y, z, v, P.Geo.head(s, cx, y, z, rest), px, py, pz))

def push_z_free(+s: Nat, obs: List<&2, P.Body>, +d: P.Z, +x: Nat, +y: Nat, +cz: Nat, +v: P.Z, here: Bool, +px: Nat, +py: Nat, +pz: Nat)
  -> {P.Geo.free(s, px, py, pz, Pobs(P.Push.z(s, obs, d, x, y, cz, v, here))) == P.Geo.free(s, px, py, pz, obs) : Bool}:
  match obs here:
    case Nil{} _:
      {==}
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh} <> +rest True{}:
      zput_free(s, P.Push.share(P.Push.closing(d, v, ovz), v, ovz), P.Push.stop(s, d, oz), ox, oy, oz, ovx, ovy, ovz, og, oh, rest,
        px, py, pz)
    case +o <> +rest False{}:
      cons_free(s, o, P.Push.z(s, rest, d, x, y, cz, v, P.Geo.head(s, x, y, cz, rest)), rest, px, py, pz,
        push_z_free(s, rest, d, x, y, cz, v, P.Geo.head(s, x, y, cz, rest), px, py, pz))

def xput_nc(+s: Nat, ok: Bool, +obs2: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool,
  eok: {P.Geo.free(s, cx, y, z, obs2) == ok : Bool}, h: {P.Geo.free(s, x, y, z, obs2) == True{} : Bool})
  -> NC(s, P.Move.xput(ok, obs2, cx, x, y, z, v, vy, vz, gr)):
  match ok:
    case True{}:
      eok
    case False{}:
      h

def xhit_nc(+s: Nat, r: P.Pushed, +x: Nat, +y: Nat, +z: Nat, +vy: P.Z, +vz: P.Z, +gr: Bool,
  h: {P.Geo.free(s, x, y, z, Pobs(r)) == True{} : Bool})
  -> NC(s, P.Move.xhit(s, r, x, y, z, vy, vz, gr)):
  P.Pushed{+v, +obs2, at} = r
  match at:
    case None{}:
      h
    case Some{+cx}:
      xput_nc(s, P.Geo.free(s, cx, y, z, obs2), obs2, cx, x, y, z, v, vy, vz, gr, {==}, h)

def xgo_nc(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, eok: {Bool.and(P.Z.fits(x, d), P.Geo.free(s, cx, y, z, obs)) == ok : Bool},
  h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> NC(s, P.Move.xgo(s, ok, obs, d, cx, x, y, z, vx, vy, vz, gr, hit)):
  match ok:
    case True{}:
      and_r(P.Z.fits(x, d), P.Geo.free(s, cx, y, z, obs), eok)
    case False{}:
      xhit_nc(s, P.Push.x(s, obs, d, cx, y, z, vx, P.Geo.head(s, cx, y, z, obs)), x, y, z, vy, vz, gr,
        Equal.trans(Bool, P.Geo.free(s, x, y, z, Pobs(P.Push.x(s, obs, d, cx, y, z, vx, P.Geo.head(s, cx, y, z, obs)))),
          P.Geo.free(s, x, y, z, obs), True{},
          push_x_free(s, obs, d, cx, y, z, vx, P.Geo.head(s, cx, y, z, obs), x, y, z), h))

def mx_nc(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body, h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), obs) == True{} : Bool})
  -> NC(s, P.Move.x(s, obs, v0, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit} = b
  xgo_nc(s, Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, obs)), obs,
    P.Z.add(v0, vx), P.Z.shift(x, P.Z.add(v0, vx)), x, y, z, vx, vy, vz, gr, hit, {==}, h)

def zput_nc(+s: Nat, ok: Bool, +obs2: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z, +gr: Bool,
  eok: {P.Geo.free(s, x, y, cz, obs2) == ok : Bool}, h: {P.Geo.free(s, x, y, z, obs2) == True{} : Bool})
  -> NC(s, P.Move.zput(ok, obs2, cz, x, y, z, vx, vy, v, gr)):
  match ok:
    case True{}:
      eok
    case False{}:
      h

def zhit_nc(+s: Nat, r: P.Pushed, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +gr: Bool,
  h: {P.Geo.free(s, x, y, z, Pobs(r)) == True{} : Bool})
  -> NC(s, P.Move.zhit(s, r, x, y, z, vx, vy, gr)):
  P.Pushed{+v, +obs2, at} = r
  match at:
    case None{}:
      h
    case Some{+cz}:
      zput_nc(s, P.Geo.free(s, x, y, cz, obs2), obs2, cz, x, y, z, vx, vy, v, gr, {==}, h)

def zgo_nc(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, eok: {Bool.and(P.Z.fits(z, d), P.Geo.free(s, x, y, cz, obs)) == ok : Bool},
  h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> NC(s, P.Move.zgo(s, ok, obs, d, cz, x, y, z, vx, vy, vz, gr, hit)):
  match ok:
    case True{}:
      and_r(P.Z.fits(z, d), P.Geo.free(s, x, y, cz, obs), eok)
    case False{}:
      zhit_nc(s, P.Push.z(s, obs, d, x, y, cz, vz, P.Geo.head(s, x, y, cz, obs)), x, y, z, vx, vy, gr,
        Equal.trans(Bool, P.Geo.free(s, x, y, z, Pobs(P.Push.z(s, obs, d, x, y, cz, vz, P.Geo.head(s, x, y, cz, obs)))),
          P.Geo.free(s, x, y, z, obs), True{},
          push_z_free(s, obs, d, x, y, cz, vz, P.Geo.head(s, x, y, cz, obs), x, y, z), h))

def mz_nc(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body, h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), obs) == True{} : Bool})
  -> NC(s, P.Move.z(s, obs, v0, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit} = b
  zgo_nc(s, Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), obs)), obs,
    P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr, hit, {==}, h)

def rise_nc(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z, +hit: Bool,
  eok: {P.Geo.free(s, x, Nat.add(y, p), z, obs) == ok : Bool}, h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.rise(ok, x, y, z, p, vx, v, vz, hit)), P.Body.y(P.Move.rise(ok, x, y, z, p, vx, v, vz, hit)),
        P.Body.z(P.Move.rise(ok, x, y, z, p, vx, v, vz, hit)), obs) == True{} : Bool}:
  match ok:
    case True{}:
      eok
    case False{}:
      h

def land_nc(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +fl: Nat, +vx: P.Z, +vz: P.Z,
  eok: {Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)) == ok : Bool}, h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.land(ok, x, y, z, fl, vx, vz)), P.Body.y(P.Move.land(ok, x, y, z, fl, vx, vz)),
        P.Body.z(P.Move.land(ok, x, y, z, fl, vx, vz)), obs) == True{} : Bool}:
  match ok:
    case True{}:
      and_r(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs), eok)
    case False{}:
      h

def fall_nc(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +fl: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +hit: Bool, eok: {Bool.and(Nat.is_le(Nat.add(fl, q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)) == ok : Bool},
  +h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, hit)), P.Body.y(P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, hit)),
        P.Body.z(P.Move.fall(s, ok, obs, x, y, z, q, fl, vx, v, vz, hit)), obs) == True{} : Bool}:
  match ok:
    case True{}:
      and_r(Nat.is_le(Nat.add(fl, q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs), eok)
    case False{}:
      land_nc(s, Bool.and(Nat.is_le(fl, y), P.Geo.free(s, x, fl, z, obs)), obs, x, y, z, fl, vx, vz, {==}, h)

def fly_nc(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +hit: Bool, st: P.Z & P.Z,
  +h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.fly(s, obs, x, y, z, vx, vz, hit, st)), P.Body.y(P.Move.fly(s, obs, x, y, z, vx, vz, hit, st)),
        P.Body.z(P.Move.fly(s, obs, x, y, z, vx, vz, hit, st)), obs) == True{} : Bool}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      rise_nc(s, P.Geo.free(s, x, Nat.add(y, p), z, obs), obs, x, y, z, p, vx, v, vz, hit, {==}, h)
    case P.Neg{+q}:
      fall_nc(s, Bool.and(Nat.is_le(Nat.add(P.Geo.floor(s, x, y, z, obs, 0n), q), y), P.Geo.free(s, x, Nat.sub(y, q), z, obs)),
        obs, x, y, z, q, P.Geo.floor(s, x, y, z, obs, 0n), vx, v, vz, hit, {==}, h)

def my_nc(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body, h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.y(s, g, obs, b)), P.Body.y(P.Move.y(s, g, obs, b)), P.Body.z(P.Move.y(s, g, obs, b)), obs) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit} = b
  match gr:
    case True{}:
      h
    case False{}:
      fly_nc(s, obs, x, y, z, vx, vz, hit, P.Fly.step(g, vy), h)

def ty_nc(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: NC(s, r)) -> NC(s, P.Tick.y(s, g, r)):
  (+b, +obs) = r
  my_nc(s, g, obs, b, h)

def tz_nc(+s: Nat, +g: Nat, +v0: P.Z, r: P.Body & List<&2, P.Body>, h: NC(s, r)) -> NC(s, P.Tick.z(s, g, v0, r)):
  (+b, +obs) = r
  ty_nc(s, g, P.Move.z(s, obs, v0, b), mz_nc(s, obs, v0, b, h))

# driving moves nothing
def leap_nc(+s: Nat, jump: Bool, +k: P.K, +x: Nat, +y: Nat, +z: Nat, v: P.Z & P.Z, +obs: List<&2, P.Body>,
  h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Drive.leap(jump, k, x, y, z, v)), P.Body.y(P.Drive.leap(jump, k, x, y, z, v)),
        P.Body.z(P.Drive.leap(jump, k, x, y, z, v)), obs) == True{} : Bool}:
  match jump:
    case True{}:
      P.K{g, mu, j, acc, s} = k
      (vx, vz) = v
      h
    case False{}:
      (vx, vz) = v
      h

def air_nc(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +obs: List<&2, P.Body>,
  h: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Drive.air(x, y, z, vx, vy, vz)), P.Body.y(P.Drive.air(x, y, z, vx, vy, vz)),
        P.Body.z(P.Drive.air(x, y, z, vx, vy, vz)), obs) == True{} : Bool}:
  h

def drive_nc(+s: Nat, +g: Nat, +mu: Nat, +j: Nat, +acc: Nat, inp: P.In, b: P.Body, +obs: List<&2, P.Body>,
  h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Body.drive(P.K{g, mu, j, acc, s}, inp, b)), P.Body.y(P.Body.drive(P.K{g, mu, j, acc, s}, inp, b)),
        P.Body.z(P.Body.drive(P.K{g, mu, j, acc, s}, inp, b)), obs) == True{} : Bool}:
  P.In{+walk, jump} = inp
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit} = b
  match gr:
    case True{}:
      leap_nc(s, jump, P.K{g, mu, j, acc, s}, x, y, z,
        P.Motor.go(acc, walk, P.Share.fst(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz)),
          P.Share.snd(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz))), obs, h)
    case False{}:
      air_nc(s, x, y, z, vx, vy, vz, obs, h)

def nclip(+g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +inp: P.In,
  +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, clear: {P.Geo.free(s, x, y, z, obs) == True{} : Bool})
  -> NC(s, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit})))):
  tz_nc(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit})),
    mx_nc(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit}),
      drive_nc(s, g, mu, j, acc, inp, P.Body{x, y, z, vx, vy, vz, gr, hit}, obs, clear)))

def Laws.no_clip(k, obs, inp, b, clear):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit}:
      nclip(g, mu, j, acc, s, obs, inp, x, y, z, vx, vy, vz, gr, hit, clear)
