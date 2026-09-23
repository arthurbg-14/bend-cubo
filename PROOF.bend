# Cubo -- the proofs. Every law of LAWS.bend, filled. Polynomial
# identities go through ring.bend's tactic (R.eq); the rest follows the
# code: every decision it makes is a Bool passed to a helper, and each
# lemma here takes that Bool as a parameter, with how it was computed.

import Base
import ./ring.bend as R
import ./phys.bend as P
import ./LAWS.bend as Laws
import ./rigid.bend as G
import ./world.bend as W

# Kit
# ---

def Once.Body(k: P.Body -> Type, b: P.Body) -> Type:
  match b:
    case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
      k(P.Body{u1, u2, u3, u4, u5, u6, u7, u8, u9})

def Once.Body.down(-k: P.Body -> Type, b: P.Body, h: Once.Body(k, b)) -> k(b):
  match b:
    case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
      h

def Once.Body.up(-k: P.Body -> Type, b: P.Body, h: k(b)) -> Once.Body(k, b):
  match b:
    case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
      h

def Body.of_pair(p: P.Body & Bool) -> P.Body:
  match p:
    case (b, o):
      b

def Tick.shrink.pair_up(-k: P.Body -> Type, c: P.Body, +rt: P.Rot, h: k(c)) -> k(Body.of_pair(P.Tick.shrink.pair(c, rt))):
  match c:
    case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
      h

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

# where a falling body lands: the floor under it, raised by how far a
# cube that has turned reaches below its own y
def flo(+s: Nat, +fl: Nat, +rt: P.Rot) -> Nat:
  Nat.add(fl, P.Geo.sag(s, P.Rot.q(rt)))

def hit_land(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +ny: Nat, +vx: P.Z, +vz: P.Z, +v0: P.Z, +rt: P.Rot)
  -> {P.Body.hit(P.Move.land(ok, x, y, z, ny, vx, vz, v0, rt)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_rise(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z, +rt: P.Rot)
  -> {P.Body.hit(P.Move.rise(ok, x, y, z, p, vx, v, vz, True{}, rt)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# a refused fall is a landing, and a landing is a knock whatever came in
def hit_fall_no(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +v0: P.Z, +hit: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Move.fall(s, False{}, obs, x, y, z, q, vx, v, vz, v0, hit, rt)) == True{} : Bool}:
  hit_land(P.Move.landok(s, obs, x, P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), z, P.Rot.q(rt)), x, y, z,
    P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), vx, vz, v0, rt)

def hit_fall(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +v0: P.Z, +rt: P.Rot)
  -> {P.Body.hit(P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, True{}, rt)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      hit_fall_no(s, obs, x, y, z, q, vx, v, vz, v0, True{}, rt)

def hit_fly(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy0: P.Z, +vz: P.Z, st: P.Z & P.Z, +rt: P.Rot)
  -> {P.Body.hit(P.Move.fly(s, obs, x, y, z, vx, vy0, vz, True{}, st, rt)) == True{} : Bool}:
  (v, d) = st
  match d:
    case P.Pos{+p}:
      hit_rise(P.Geo.free(s, x, Nat.add(y, p), z, P.Rot.q(rt), obs), x, y, z, p, vx, v, vz, rt)
    case P.Neg{+q}:
      hit_fall(s, P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)), obs, x, y, z, q, vx, v, vz, vy0, rt)

# a body that is held up keeps whatever knock it came in with: the press
# of the hold changes how it turns, never that
def hit_stay(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +rt: P.Rot)
  -> {P.Body.hit(P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, True{}, rt)) == True{} : Bool}:
  match rest:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_y(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, gr: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Move.y(s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, True{}, rt})) == True{} : Bool}:
  match gr:
    case True{}:
      hit_stay(P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs), s, g, obs, x, y, z, vx, vy, vz, rt)
    case False{}:
      hit_fly(s, obs, x, y, z, vx, vy, vz, P.Fly.step(g, vy), rt)

def hit_ty(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: {P.Body.hit(P.Tick.body(r)) == True{} : Bool})
  -> {P.Body.hit(P.Tick.body(P.Tick.y(s, g, r))) == True{} : Bool}:
  (b, +obs) = r
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, hit, +rt} = b
  match hit:
    case True{}:
      hit_y(s, g, obs, x, y, z, vx, vy, vz, gr, rt)
    case False{}:
      Empty.absurd({P.Body.hit(P.Tick.body(P.Tick.y(s, g, (P.Body{x, y, z, vx, vy, vz, gr, False{}, rt}, obs)))) == True{} : Bool},
        clash2(h))

def hit_zput(ok: Bool, +obs: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.zput(ok, obs, cz, x, y, z, vx, vy, v, gr, rt))) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_zpushed(r: P.Pushed, +x: Nat, +y: Nat, +cz: Nat, +vx: P.Z, +vy: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt))) == True{} : Bool}:
  P.Pushed{+v, +obs, at} = r
  {==}

def hit_ztouch(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.ztouch(touch, s, obs, d, cz, pr, x, y, z, vx, vy, vz, gr, rt))) == True{} : Bool}:
  match touch:
    case True{}:
      hit_zpushed(P.Push.z(s, obs, d, x, y, pr, vz, P.Rot.q(rt), P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs)), x, y, cz,
        vx, vy, gr, rt)
    case False{}:
      hit_zput(P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), obs, cz, x, y, z, vx, vy, vz, gr, rt)

# a refused move along z, however it ends, is a knock
def hit_zno(+s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.zno(s, obs, d, cz, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))) == True{} : Bool}:
  hit_ztouch(P.Move.ztouches(s, obs, d, x, y, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Rot.q(rt)), s, obs, d,
    P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, rt)

def hit_xput(ok: Bool, +obs: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.xput(ok, obs, cx, x, y, z, v, vy, vz, gr, rt))) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_xpushed(r: P.Pushed, +cx: Nat, +y: Nat, +z: Nat, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt))) == True{} : Bool}:
  P.Pushed{+v, +obs, at} = r
  {==}

def hit_xtouch(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.xtouch(touch, s, obs, d, cx, pr, x, y, z, vx, vy, vz, gr, rt))) == True{} : Bool}:
  match touch:
    case True{}:
      hit_xpushed(P.Push.x(s, obs, d, pr, y, z, vx, P.Rot.q(rt), P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs)), cx, y, z,
        vy, vz, gr, rt)
    case False{}:
      hit_xput(P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), obs, cx, x, y, z, vx, vy, vz, gr, rt)

# a refused move along x, however it ends, is a knock
def hit_xno(+s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {P.Body.hit(P.Tick.body(P.Move.xno(s, obs, d, cx, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))) == True{} : Bool}:
  hit_xtouch(P.Move.xtouches(s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), y, z, P.Rot.q(rt)), s, obs, d,
    P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, rt)

def hit_zgo(+s: Nat, ok: Bool, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +rt: P.Rot) -> {P.Body.hit(P.Tick.body(P.Move.zgo(s, ok, obs, d, cz, P.Body{x,y,z,vx,vy,vz,gr,True{},rt}))) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      hit_zno(s, obs, d, cz, x, y, z, vx, vy, vz, gr, True{}, rt)

def hit_tz(+s: Nat, +g: Nat, +v0: P.Z, r: P.Body & List<&2, P.Body>, h: {P.Body.hit(P.Tick.body(r)) == True{} : Bool})
  -> {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0, r))) == True{} : Bool}:
  (b, +obs) = r
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, hit, +rt} = b
  match hit:
    case True{}:
      hit_ty(s, g, P.Move.z(s, obs, v0, P.Body{x, y, z, vx, vy, vz, gr, True{}, rt}),
        hit_zgo(s, Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), P.Rot.q(rt), obs)),
          obs, P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr, rt))
    case False{}:
      Empty.absurd({P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0, (P.Body{x, y, z, vx, vy, vz, gr, False{}, rt}, obs)))) == True{} : Bool},
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

def Free(+g: Nat, +x: Nat, +y: Nat, +z: Nat, +dx: P.Z, +dz: P.Z, +vx: P.Z, +vy: P.Z, +vz: P.Z, +rt: P.Rot) -> P.Body:
  P.Body{P.Z.shift(x, dx), P.Z.shift(y, P.Share.snd(P.Fly.step(g, vy))), P.Z.shift(z, dz), vx,
    P.Share.fst(P.Fly.step(g, vy)), vz, False{}, False{}, rt}

def y_rise_eq(+rt: P.Rot, ok: Bool, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  free: {P.Body.hit(P.Move.rise(ok, x, y, z, p, vx, v, vz, False{}, rt)) == False{} : Bool})
  -> {P.Body{x, Nat.add(y, p), z, vx, v, vz, False{}, False{}, rt} == P.Move.rise(ok, x, y, z, p, vx, v, vz, False{}, rt) : P.Body}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({P.Body{x, Nat.add(y, p), z, vx, v, vz, False{}, False{}, rt} == P.Body{x, y, z, vx, P.Pos{0n}, vz, False{}, True{}, rt} : P.Body},
        clash(free))

def y_fall_eq(+rt: P.Rot, +s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +v0: P.Z, free: {P.Body.hit(P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, False{}, rt)) == False{} : Bool})
  -> {P.Body{x, Nat.sub(y, q), z, vx, v, vz, False{}, False{}, rt} == P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, False{}, rt) : P.Body}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({P.Body{x, Nat.sub(y, q), z, vx, v, vz, False{}, False{}, rt}
          == P.Move.fall(s, False{}, obs, x, y, z, q, vx, v, vz, v0, False{}, rt) : P.Body},
        unhit(P.Body.hit(P.Move.fall(s, False{}, obs, x, y, z, q, vx, v, vz, v0, False{}, rt)),
          hit_fall_no(s, obs, x, y, z, q, vx, v, vz, v0, False{}, rt), free))

def y_eq(+rt: P.Rot, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy0: P.Z, +vz: P.Z, st: P.Z & P.Z,
  free: {P.Body.hit(P.Move.fly(s, obs, x, y, z, vx, vy0, vz, False{}, st, rt)) == False{} : Bool})
  -> {P.Body{x, P.Z.shift(y, P.Share.snd(st)), z, vx, P.Share.fst(st), vz, False{}, False{}, rt}
      == P.Move.fly(s, obs, x, y, z, vx, vy0, vz, False{}, st, rt) : P.Body}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      y_rise_eq(rt, P.Geo.free(s, x, Nat.add(y, p), z, P.Rot.q(rt), obs), x, y, z, p, vx, v, vz, free)
    case P.Neg{+q}:
      y_fall_eq(rt, s, P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)), obs, x, y, z, q, vx, v, vz, vy0, free)

def y_fall_ok(+rt: P.Rot, +s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +v0: P.Z, eok: {P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)) == ok : Bool},
  free: {P.Body.hit(P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, False{}, rt)) == False{} : Bool})
  -> {Nat.is_le(q, y) == True{} : Bool}:
  match ok:
    case True{}:
      and_l(Nat.is_le(q, y), Bool.and(P.Tick.fits(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt)),
        P.Tick.path(64n, Nat.is_lt(s, q), s, obs, x, y, z, P.Rot.q(rt), q, s)), eok)
    case False{}:
      Empty.absurd({Nat.is_le(q, y) == True{} : Bool},
        unhit(P.Body.hit(P.Move.fall(s, False{}, obs, x, y, z, q, vx, v, vz, v0, False{}, rt)),
          hit_fall_no(s, obs, x, y, z, q, vx, v, vz, v0, False{}, rt), free))

def y_ok(+rt: P.Rot, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy0: P.Z, +vz: P.Z, st: P.Z & P.Z,
  free: {P.Body.hit(P.Move.fly(s, obs, x, y, z, vx, vy0, vz, False{}, st, rt)) == False{} : Bool})
  -> {P.Z.fits(y, P.Share.snd(st)) == True{} : Bool}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      {==}
    case P.Neg{+q}:
      y_fall_ok(rt, s, P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)), obs, x, y, z, q, vx, v, vz, vy0, {==}, free)

# the z move, untouched
def Fz(+g: Nat, +x: Nat, +y: Nat, +z: Nat, +dz: P.Z, +vx: P.Z, +vy: P.Z, +vz: P.Z, +rt: P.Rot) -> P.Body:
  P.Body{x, P.Z.shift(y, P.Share.snd(P.Fly.step(g, vy))), P.Z.shift(z, dz), vx, P.Share.fst(P.Fly.step(g, vy)), vz, False{}, False{}, rt}

def z_air_eq(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))))
    == False{} : Bool})
  -> {Fz(g, x, y, z, dz, vx, vy, vz, rt)
      == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))) : P.Body}:
  match ok:
    case True{}:
      y_eq(rt, s, obs, x, y, P.Z.shift(z, dz), vx, vy, vz, P.Fly.step(g, vy), free)
    case False{}:
      Empty.absurd({Fz(g, x, y, z, dz, vx, vy, vz, rt)
          == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, False{}, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt})))),
          hit_ty(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}),
            hit_zno(s, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, False{}, False{}, rt)),
          free))

# the x move, untouched
def x_air_eq(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))))
    == False{} : Bool})
  -> {Fz(g, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz, rt)
      == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))) : P.Body}:
  match ok:
    case True{}:
      z_air_eq(rt, s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), P.Rot.q(rt), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, free)
    case False{}:
      Empty.absurd({Fz(g, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz, rt)
          == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, False{}, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt})))),
          hit_tz(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}),
            hit_xno(s, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, False{}, False{}, rt)),
          free))

def z_air_ok(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  eok: {Bool.and(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), P.Rot.q(rt), obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))))
    == False{} : Bool})
  -> {Bool.and(P.Z.fits(z, dz), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Bool, P.Z.fits(z, dz), True{}, and_l(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), P.Rot.q(rt), obs), eok))
        : {Bool.and(_, P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))) == True{} : Bool}
      y_ok(rt, s, obs, x, y, P.Z.shift(z, dz), vx, vy, vz, P.Fly.step(g, vy), free)
    case False{}:
      Empty.absurd({Bool.and(P.Z.fits(z, dz), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))) == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt})))),
          hit_ty(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}),
            hit_zno(s, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, False{}, False{}, rt)),
          free))

def x_air_ok(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  eok: {Bool.and(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, P.Rot.q(rt), obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))))
    == False{} : Bool})
  -> {Bool.and(P.Z.fits(x, dx), Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))))) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Bool, P.Z.fits(x, dx), True{}, and_l(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, P.Rot.q(rt), obs), eok))
        : {Bool.and(_, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))))) == True{} : Bool}
      z_air_ok(rt, s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), P.Rot.q(rt), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, {==}, free)
    case False{}:
      Empty.absurd({Bool.and(P.Z.fits(x, dx), Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))))
          == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt})))),
          hit_tz(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}),
            hit_xno(s, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, False{}, False{}, rt)),
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
def Ok1(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +rt: P.Rot) -> Bool:
  Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, P.Rot.q(rt), obs))

# an untouched tick in the air, from the body (x, y, z, vx, vy, vz)
# A tick without a knock did not turn about anything
# ------------------------------------------------
# Turning about a contact sets hit, so a tick that ends without a knock
# either did not turn at all or turned in the air -- and a turn in the
# air leaves the body exactly where it was, going exactly as it was. So
# the body that comes out is the body that went in, turned another way,
# which is what every law about a tick without a knock needs.

def put_hit(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat,
  +nz: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, +r2: P.Rot)
  -> {P.Body.hit(P.Tick.put(ok, s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, True{}, rt, r2)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def place_hit(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, +r2: P.Rot)
  -> {P.Body.hit(P.Tick.place(s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, True{}, rt, r2)) == True{} : Bool}:
  put_hit(P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr), s, g, obs, x, y, z, nx, ny, nz,
    vx, vy, vz, gr, rt, r2)

def pivot_hit(m: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +rt: P.Rot, +r2: P.Rot, +rx: P.Z, +ry: P.Z, +rz: P.Z)
  -> {P.Body.hit(P.Tick.pivot(m, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, rx, ry, rz)) == True{} : Bool}:
  P.Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = P.Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = P.Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = P.Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = P.Tick.drop(s, obs, nx, y, nz, P.Rot.q(r2), Nat.add(Nat.sub(y, P.Pick.low(ny, y)), Nat.div(s, 256n)))
  place_hit(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, rt, r2)

def cand_hit(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z)
  -> {P.Body.hit(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w, rx, ry, rz)) == True{} : Bool}:
  pivot_hit(P.Rot.mat(P.Quat.half(P.Quat.step(w, P.Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, rt,
    P.Rot{P.Rot.turn(P.Rot.q(rt), w), P.Rot.w(rt)}, rx, ry, rz)

def shrink_hit(n: Nat, p: P.Body & Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  hb: {P.Body.hit(Body.of_pair(p)) == True{} : Bool})
  -> {P.Body.hit(P.Tick.shrink(n, p, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w, rx, ry, rz)) == True{} : Bool}:
  match n:
    case 0n:
      match p:
        case (b, ok):
          hb
    case 1n+m:
      match p:
        case (b, ok):
          match ok:
            case True{}:
              hb
            case False{}:
              shrink_hit(m, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, P.Wv.half(w), rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, rt, P.Wv.half(w), rx, ry, rz, Tick.shrink.pair_up((kb: P.Body) => {P.Body.hit(kb) == True{} : Bool}, P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, P.Wv.half(w), rx, ry, rz), rt, cand_hit(s, g, obs, x, y, z, vx, vy, vz, gr, rt, P.Wv.half(w), rx, ry, rz)))

def start_hit(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z)
  -> {P.Body.hit(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w, rx, ry, rz)) == True{} : Bool}:
  shrink_hit(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, rt, w, rx, ry, rz, Tick.shrink.pair_up((kb: P.Body) => {P.Body.hit(kb) == True{} : Bool}, P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w, rx, ry, rz), rt, cand_hit(s, g, obs, x, y, z, vx, vy, vz, gr, rt, w, rx, ry, rz)))

def keepw_hit(+tip: Bool, moved: Bool, +b: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot,
  hb: {P.Body.hit(b) == True{} : Bool})
  -> {P.Body.hit(P.Body.spin(tip, moved, b, rt)) == True{} : Bool}:
  match moved:
    case True{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb
    case False{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb

def pivota0_hit(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv)
  -> {P.Body.hit(P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, w2, a)) == True{} : Bool}:
  P.Wv{+ax, +ay, +az} = a
  keepw_hit(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))), P.Tick.moved(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w2, ax, ay, az), rt), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, rt,
    start_hit(s, g, obs, x, y, z, vx, vy, vz, gr, rt, w2, ax, ay, az))

def pivota_hit(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv)
  -> {P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, a)) == True{} : Bool}:
  match obs:
    case []:
      pivota0_hit(md, s, g, [], x, y, z, vx, vy, vz, gr, rt, r2, P.Tick.pivota0.w2(s, rt, a), a)
    case o <> rest:
      pivota0_hit(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, rt, r2, P.Tick.pivota0.w2(s, rt, a), a)

def put_eq(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  free: {P.Body.hit(P.Tick.put(ok, s, g, obs, x, y, z, x, y, z, vx, vy, vz, False{}, hit, rt, r2)) == False{} : Bool})
  -> {P.Tick.put(ok, s, g, obs, x, y, z, x, y, z, vx, vy, vz, False{}, hit, rt, r2)
      == P.Body.setrot(P.Body{x, y, z, vx, vy, vz, False{}, hit, rt},
           P.Body.rot(P.Tick.put(ok, s, g, obs, x, y, z, x, y, z, vx, vy, vz, False{}, hit, rt, r2))) : P.Body}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({P.Body{x, y, z, vx, vy, vz, False{}, True{}, rt}
          == P.Body.setrot(P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}, rt) : P.Body},
        clash(free))

def turn2_eq(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat,
  free: {P.Body.hit(P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, held, hit, rt, r2, md)) == False{} : Bool})
  -> {P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, held, hit, rt, r2, md)
      == P.Body.setrot(P.Body{x, y, z, vx, vy, vz, held, hit, rt},
           P.Body.rot(P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, held, hit, rt, r2, md))) : P.Body}:
  match held floor:
    case False{} _:
      put_eq(P.Tick.turnok(s, obs, y, x, y, z, P.Rot.q(r2), False{}), s, g, obs, x, y, z, vx, vy, vz, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2, free)
    case True{} False{}:
      Empty.absurd({P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s)) == P.Body.setrot(P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}, P.Body.rot(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s)))) : P.Body},
        clash(Equal.trans(Bool, True{},
          P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))), False{},
          Equal.sym(Bool, P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))), True{},
            pivota_hit(md, s, g, obs, x, y, z, vx, vy, vz, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))),
          free)))
    case True{} True{}:
      Empty.absurd({P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s)) == P.Body.setrot(P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}, P.Body.rot(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s)))) : P.Body},
        clash(Equal.trans(Bool, True{},
          P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))), False{},
          Equal.sym(Bool, P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))), True{},
            pivota_hit(md, s, g, obs, x, y, z, vx, vy, vz, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))),
          free)))

def turn1_eq(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  free: {P.Body.hit(P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == False{} : Bool})
  -> {P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})
      == P.Body.setrot(P.Body{x, y, z, vx, vy, vz, gr, hit, rt},
           P.Body.rot(P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))) : P.Body}:
  match still:
    case True{}:
      {==}
    case False{}:
      turn2_eq(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy,
        vz, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), free)

# the turn left whole is the turn written out, read both ways
def turn_is(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +b: P.Body)
  -> {P.Tick.turn(s, g, obs, b) == P.Tick.turn0(s, g, obs, b) : P.Body}:
  match obs:
    case []:
      {==}
    case o <> rest:
      {==}

def turn_sym(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +b: P.Body)
  -> {P.Tick.turn0(s, g, obs, b) == P.Tick.turn(s, g, obs, b) : P.Body}:
  match obs:
    case []:
      {==}
    case o <> rest:
      {==}

def turn_free(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  h: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Body.hit(P.Tick.turn0(s, g, obs, b)) == False{} : Bool}:
  %turn_is(s, g, obs, b) : {P.Body.hit(_) == False{} : Bool}
  h

def turn_eq0(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn0(s, g, obs, b)) == False{} : Bool})
  -> {P.Tick.turn0(s, g, obs, b) == P.Body.setrot(b, P.Body.rot(P.Tick.turn0(s, g, obs, b))) : P.Body}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  turn1_eq(P.Wv.null(P.Rot.w(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, free)

def turn_eq(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Tick.turn(s, g, obs, b) == P.Body.setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b))) : P.Body}:
  %turn_sym(s, g, obs, b) : {_ == P.Body.setrot(b, P.Body.rot(_)) : P.Body}
  turn_eq0(s, g, obs, b, turn_free(s, g, obs, b, free))

def hit_setrot(+b: P.Body, +r: P.Rot) -> {P.Body.hit(P.Body.setrot(b, r)) == P.Body.hit(b) : Bool}:
  {==}

def energy_setrot(+g: Nat, +b: P.Body, +r: P.Rot)
  -> {P.Body.energy(g, P.Body.setrot(b, r)) == P.Body.energy(g, b) : Nat}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  {==}

def vx_setrot(+b: P.Body, +r: P.Rot) -> {P.Body.vx(P.Body.setrot(b, r)) == P.Body.vx(b) : P.Z}:
  {==}

def vz_setrot(+b: P.Body, +r: P.Rot) -> {P.Body.vz(P.Body.setrot(b, r)) == P.Body.vz(b) : P.Z}:
  {==}

# What a turn leaves the body turned as: the spin taken up. The contact
# branches are not here because they mark the body knocked, which the
# no-knock hypothesis leaves out -- a turn about a contact is a knock.
def put_q(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  free: {P.Body.hit(P.Tick.put(ok, s, g, obs, x, y, z, x, y, z, vx, vy, vz, False{}, hit, rt, r2)) == False{} : Bool})
  -> {P.Rot.q(P.Body.rot(P.Tick.put(ok, s, g, obs, x, y, z, x, y, z, vx, vy, vz, False{}, hit, rt, r2))) == P.Rot.q(r2) : P.Quat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({P.Rot.q(rt) == P.Rot.q(r2) : P.Quat}, clash(free))

def turn2_q(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat,
  free: {P.Body.hit(P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, held, hit, rt, r2, md)) == False{} : Bool})
  -> {P.Rot.q(P.Body.rot(P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, held, hit, rt, r2, md)))
      == P.Rot.q(r2) : P.Quat}:
  match held floor:
    case False{} _:
      put_q(P.Tick.turnok(s, obs, y, x, y, z, P.Rot.q(r2), False{}), s, g, obs, x, y, z, vx, vy, vz, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2, free)
    case True{} False{}:
      Empty.absurd({P.Rot.q(P.Body.rot(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s)))) == P.Rot.q(r2) : P.Quat},
        clash(Equal.trans(Bool, True{},
          P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))), False{},
          Equal.sym(Bool, P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))), True{},
            pivota_hit(md, s, g, obs, x, y, z, vx, vy, vz, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))),
          free)))
    case True{} True{}:
      Empty.absurd({P.Rot.q(P.Body.rot(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s)))) == P.Rot.q(r2) : P.Quat},
        clash(Equal.trans(Bool, True{},
          P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))), False{},
          Equal.sym(Bool, P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))), True{},
            pivota_hit(md, s, g, obs, x, y, z, vx, vy, vz, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))),
          free)))

def turn1_q(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  nn: {still == False{} : Bool},
  free: {P.Body.hit(P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == False{} : Bool})
  -> {P.Rot.q(P.Body.rot(P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))) == P.Rot.q(P.Rot.free(rt)) : P.Quat}:
  match still:
    case True{}:
      Empty.absurd({P.Rot.q(P.Body.rot(P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == P.Rot.q(P.Rot.free(rt)) : P.Quat}, clash(nn))
    case False{}:
      turn2_q(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy,
        vz, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), free)

# the free turn's orientation is the spin taken up
def free_q(rt: P.Rot) -> {P.Rot.q(P.Rot.free(rt)) == P.Rot.turn(P.Rot.q(rt), P.Rot.w(rt)) : P.Quat}:
  P.Rot{+q, +w} = rt
  {==}

def turn_q0(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  spin: {P.Wv.null(P.Rot.w(P.Body.rot(b))) == False{} : Bool},
  free: {P.Body.hit(P.Tick.turn0(s, g, obs, b)) == False{} : Bool})
  -> {P.Rot.q(P.Body.rot(P.Tick.turn0(s, g, obs, b)))
      == P.Rot.turn(P.Rot.q(P.Body.rot(b)), P.Rot.w(P.Body.rot(b))) : P.Quat}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  Equal.trans(P.Quat,
    P.Rot.q(P.Body.rot(P.Tick.turn1(P.Wv.null(P.Rot.w(rt)), s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
    P.Rot.q(P.Rot.free(rt)), P.Rot.turn(P.Rot.q(rt), P.Rot.w(rt)),
    turn1_q(P.Wv.null(P.Rot.w(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, spin, free),
    free_q(rt))

def turn_q(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  spin: {P.Wv.null(P.Rot.w(P.Body.rot(b))) == False{} : Bool},
  free: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Rot.q(P.Body.rot(P.Tick.turn(s, g, obs, b)))
      == P.Rot.turn(P.Rot.q(P.Body.rot(b)), P.Rot.w(P.Body.rot(b))) : P.Quat}:
  %turn_sym(s, g, obs, b)
    : {P.Rot.q(P.Body.rot(_)) == P.Rot.turn(P.Rot.q(P.Body.rot(b)), P.Rot.w(P.Body.rot(b))) : P.Quat}
  turn_q0(s, g, obs, b, spin, turn_free(s, g, obs, b, free))

def spin_q(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  spin: {P.Wv.null(P.Rot.w(P.Body.rot(P.Tick.body(r)))) == False{} : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(s, g, r))))
      == P.Rot.turn(P.Rot.q(P.Body.rot(P.Tick.body(r))), P.Rot.w(P.Body.rot(P.Tick.body(r)))) : P.Quat}:
  (+b, +obs) = r
  turn_q(s, g, obs, b, spin, free)

# What a turn leaves the body spinning as: a turn taken freely carries
# the spin through untouched. A refused turn spends it, but a refused
# turn is a knock, which the no-knock hypothesis leaves out.
def free_w(rt: P.Rot) -> {P.Rot.w(P.Rot.free(rt)) == P.Rot.w(rt) : P.Wv}:
  P.Rot{+q, +w} = rt
  {==}

def put_w(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  free: {P.Body.hit(P.Tick.put(ok, s, g, obs, x, y, z, x, y, z, vx, vy, vz, False{}, hit, rt, r2)) == False{} : Bool})
  -> {P.Rot.w(P.Body.rot(P.Tick.put(ok, s, g, obs, x, y, z, x, y, z, vx, vy, vz, False{}, hit, rt, r2))) == P.Rot.w(r2) : P.Wv}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({P.Rot.w(rt) == P.Rot.w(r2) : P.Wv}, clash(free))

def turn2_w(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat,
  free: {P.Body.hit(P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, held, hit, rt, r2, md)) == False{} : Bool})
  -> {P.Rot.w(P.Body.rot(P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, held, hit, rt, r2, md)))
      == P.Rot.w(r2) : P.Wv}:
  match held floor:
    case False{} _:
      put_w(P.Tick.turnok(s, obs, y, x, y, z, P.Rot.q(r2), False{}), s, g, obs, x, y, z, vx, vy, vz, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2, free)
    case True{} False{}:
      Empty.absurd({P.Rot.w(P.Body.rot(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s)))) == P.Rot.w(r2) : P.Wv},
        clash(Equal.trans(Bool, True{},
          P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))), False{},
          Equal.sym(Bool, P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))), True{},
            pivota_hit(md, s, g, obs, x, y, z, vx, vy, vz, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))),
          free)))
    case True{} True{}:
      Empty.absurd({P.Rot.w(P.Body.rot(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s)))) == P.Rot.w(r2) : P.Wv},
        clash(Equal.trans(Bool, True{},
          P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))), False{},
          Equal.sym(Bool, P.Body.hit(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, True{}, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))), True{},
            pivota_hit(md, s, g, obs, x, y, z, vx, vy, vz, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))),
          free)))

def turn1_w(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  free: {P.Body.hit(P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == False{} : Bool})
  -> {P.Rot.w(P.Body.rot(P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))) == P.Rot.w(rt) : P.Wv}:
  match still:
    case True{}:
      {==}
    case False{}:
      Equal.trans(P.Wv,
        P.Rot.w(P.Body.rot(P.Tick.turn2(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)),
          s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt)))))))),
        P.Rot.w(P.Rot.free(rt)), P.Rot.w(rt),
        turn2_w(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy,
          vz, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), free),
        free_w(rt))

def turn_w0(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn0(s, g, obs, b)) == False{} : Bool})
  -> {P.Rot.w(P.Body.rot(P.Tick.turn0(s, g, obs, b))) == P.Rot.w(P.Body.rot(b)) : P.Wv}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  turn1_w(P.Wv.null(P.Rot.w(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, free)

def turn_w(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Rot.w(P.Body.rot(P.Tick.turn(s, g, obs, b))) == P.Rot.w(P.Body.rot(b)) : P.Wv}:
  %turn_sym(s, g, obs, b) : {P.Rot.w(P.Body.rot(_)) == P.Rot.w(P.Body.rot(b)) : P.Wv}
  turn_w0(s, g, obs, b, turn_free(s, g, obs, b, free))

def spin_w(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(s, g, r))))
      == P.Rot.w(P.Body.rot(P.Tick.body(r))) : P.Wv}:
  (+b, +obs) = r
  turn_w(s, g, obs, b, free)

# What the sideways moves leave alone: the height, the fall's speed and
# whether the body is standing. Every way through them carries those
# three untouched, the pushes included -- which is what lets the fall
# stage have the last word on all three.
def SAME(+vy: P.Z, +gr: Bool, -b2: P.Body) -> Type:
  {P.Body.vy(b2) == vy : P.Z}
  & {P.Body.ground(b2) == gr : Bool}

def xput_same(ok: Bool, +obs: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> SAME(vy, gr, P.Tick.body(P.Move.xput(ok, obs, cx, x, y, z, v, vy, vz, gr, rt))):
  match ok:
    case True{}:
      ({==}, {==})
    case False{}:
      ({==}, {==})

def xpushed_same(r: P.Pushed, +cx: Nat, +y: Nat, +z: Nat, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> SAME(vy, gr, P.Tick.body(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt))):
  P.Pushed{+v, +obs, at} = r
  ({==}, {==})

def xtouch_same(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> SAME(vy, gr, P.Tick.body(P.Move.xtouch(touch, s, obs, d, cx, pr, x, y, z, vx, vy, vz, gr, rt))):
  match touch:
    case True{}:
      xpushed_same(P.Push.x(s, obs, d, pr, y, z, vx, P.Rot.q(rt), P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs)), cx, y, z,
        vy, vz, gr, rt)
    case False{}:
      xput_same(P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), obs, cx, x, y, z, vx, vy, vz, gr, rt)

def zput_same(ok: Bool, +obs: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +v: P.Z, +gr: Bool, +rt: P.Rot)
  -> SAME(vy, gr, P.Tick.body(P.Move.zput(ok, obs, cz, x, y, z, vx, vy, v, gr, rt))):
  match ok:
    case True{}:
      ({==}, {==})
    case False{}:
      ({==}, {==})

def zpushed_same(r: P.Pushed, +x: Nat, +y: Nat, +cz: Nat, +vx: P.Z, +vy: P.Z, +gr: Bool, +rt: P.Rot)
  -> SAME(vy, gr, P.Tick.body(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt))):
  P.Pushed{+v, +obs, at} = r
  ({==}, {==})

def ztouch_same(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> SAME(vy, gr, P.Tick.body(P.Move.ztouch(touch, s, obs, d, cz, pr, x, y, z, vx, vy, vz, gr, rt))):
  match touch:
    case True{}:
      zpushed_same(P.Push.z(s, obs, d, x, y, pr, vz, P.Rot.q(rt), P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs)), x, y, cz,
        vx, vy, gr, rt)
    case False{}:
      zput_same(P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), obs, cz, x, y, z, vx, vy, vz, gr, rt)

def same_v(+vy: P.Z, +gr: Bool, +b2: P.Body, t: SAME(vy, gr, b2))
  -> {P.Body.vy(b2) == vy : P.Z}:
  (+b, +c) = t
  b

def same_g(+vy: P.Z, +gr: Bool, +b2: P.Body, t: SAME(vy, gr, b2))
  -> {P.Body.ground(b2) == gr : Bool}:
  (+b, +c) = t
  c

def xok_same(+obs: List<&2, P.Body>, +cx: Nat, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.xok(obs, cx, b))):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  ({==}, {==})

def xno_same(+s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.xno(s, obs, d, cx, b))):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  xtouch_same(P.Move.xtouches(s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), y, z, P.Rot.q(rt)), s, obs, d,
    P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, rt)

def xgo_same(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.xgo(s, ok, obs, d, cx, b))):
  match ok:
    case True{}:
      xok_same(obs, cx, b)
    case False{}:
      xno_same(s, obs, d, cx, b)

def mx_same(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.x(s, obs, v0, b))):
  xgo_same(Bool.and(P.Z.fits(P.Body.x(b), P.Z.add(v0, P.Body.vx(b))),
      P.Geo.free(s, P.Z.shift(P.Body.x(b), P.Z.add(v0, P.Body.vx(b))), P.Body.y(b), P.Body.z(b),
        P.Rot.q(P.Body.rot(b)), obs)),
    s, obs, P.Z.add(v0, P.Body.vx(b)), P.Z.shift(P.Body.x(b), P.Z.add(v0, P.Body.vx(b))), b)

def zok_same(+obs: List<&2, P.Body>, +cz: Nat, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.zok(obs, cz, b))):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  ({==}, {==})

def zno_same(+s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.zno(s, obs, d, cz, b))):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  ztouch_same(P.Move.ztouches(s, obs, d, x, y, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Rot.q(rt)), s, obs, d,
    P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, rt)

def zgo_same(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.zgo(s, ok, obs, d, cz, b))):
  match ok:
    case True{}:
      zok_same(obs, cz, b)
    case False{}:
      zno_same(s, obs, d, cz, b)

def mz_same(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, +b: P.Body)
  -> SAME(P.Body.vy(b), P.Body.ground(b), P.Tick.body(P.Move.z(s, obs, v0, b))):
  zgo_same(Bool.and(P.Z.fits(P.Body.z(b), P.Z.add(v0, P.Body.vz(b))),
      P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Z.shift(P.Body.z(b), P.Z.add(v0, P.Body.vz(b))),
        P.Rot.q(P.Body.rot(b)), obs)),
    s, obs, P.Z.add(v0, P.Body.vz(b)), P.Z.shift(P.Body.z(b), P.Z.add(v0, P.Body.vz(b))), b)

# Still going down, or standing on something -- never stopped in mid-air
def FS(-b2: P.Body) -> Type:
  {Bool.or(Nat.is_lt(0n, P.Z.neg(P.Body.vy(b2))), P.Body.ground(b2)) == True{} : Bool}

def lt_add(q: Nat, +g: Nat, h: {Nat.is_lt(0n, q) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.add(q, g)) == True{} : Bool}:
  match q:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.add(0n, g)) == True{} : Bool}, clash(Equal.sym(Bool, False{}, True{}, h)))
    case 1n+p:
      {==}

def or_here(+a: Bool, +b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def or_there(a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# A fall that is refused is a landing: either way the body stands
# A refused fall is a landing where the body is held, and nothing at all
# where it is not: it stays, going down as fast as it came in
def land_fs(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +ny: Nat, +vx: P.Z, +vz: P.Z, +vd: Nat, +rt: P.Rot,
  hv: {Nat.is_lt(0n, vd) == True{} : Bool})
  -> FS(P.Move.land(ok, x, y, z, ny, vx, vz, P.Neg{vd}, rt)):
  match ok:
    case True{}:
      or_there(Nat.is_lt(0n, P.Z.neg(P.Pos{0n})), True{}, {==})
    case False{}:
      or_here(Nat.is_lt(0n, vd), False{}, hv)

def fall_fs(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +qd: Nat,
  +vx: P.Z, +vd: Nat, +vz: P.Z, +v0d: Nat, +hit: Bool, +rt: P.Rot,
  hv: {Nat.is_lt(0n, vd) == True{} : Bool}, hv0: {Nat.is_lt(0n, v0d) == True{} : Bool})
  -> FS(P.Move.fall(s, ok, obs, x, y, z, qd, vx, P.Neg{vd}, vz, P.Neg{v0d}, hit, rt)):
  match ok:
    case True{}:
      or_here(Nat.is_lt(0n, vd), False{}, hv)
    case False{}:
      land_fs(P.Move.landok(s, obs, x, P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), qd), z, P.Rot.q(rt)), x, y, z,
        P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), qd), vx, vz, v0d, rt, hv0)

def fly_fs(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +hit: Bool,
  +g: Nat, +q: Nat, +rt: P.Rot, +going: {Nat.is_lt(0n, q) == True{} : Bool})
  -> FS(P.Move.fly(s, obs, x, y, z, vx, P.Neg{q}, vz, hit, P.Fly.step(g, P.Neg{q}), rt)):
  fall_fs(P.Move.fallok(s, obs, x, y, z, Nat.add(Nat.add(q, q), g), P.Rot.q(rt)),
    s, obs, x, y, z, Nat.add(Nat.add(q, q), g), vx, Nat.add(q, g), vz, q, hit, rt, lt_add(q, g, going), going)

# What the turn leaves alone: the fall's speed and whether the body is
# standing. Every way through it carries both untouched, contact turns
# included, so the fall stage has the last word on both.
def VG(+vy: P.Z, +gr: Bool, -b2: P.Body) -> Type:
  {P.Body.vy(b2) == vy : P.Z} & {P.Body.ground(b2) == gr : Bool}

# What the turn does to a falling body. A turn that is refused, or taken
# in the air, leaves its fall alone. One that carries a standing body off
# what held it lets it go -- going down, as fast as its drop pays for,
# and a turn that would lift it off without letting it down at all is
# refused. So, gravity on, a body going down or standing comes out of the
# turn going down or standing.

# a < b gives 0 < b - a
def lt_sub(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(b, a)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, clash2(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.sub(0n, 1n+p)) == True{} : Bool}, clash2(h))
    case 1n+p 1n+q:
      lt_sub(p, q, h)

# the smaller of two numbers above 0 is above 0
def low_pos(le: Bool, +a: Nat, +b: Nat, ha: {Nat.is_lt(0n, a) == True{} : Bool}, hb: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(0n, P.Pick.n(le, a, b)) == True{} : Bool}:
  match le:
    case True{}:
      ha
    case False{}:
      hb

# a or b, and not b: a
def or_left(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, hb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, clash(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, h), hb)))

def putt_fs(gr: Bool, st: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +y: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vy: P.Z, +q: P.Quat,
  est: {P.Tick.stands(gr, s, obs, nx, ny, nz, q) == st : Bool},
  keep: {P.Tick.keeps(gr, s, obs, y, nx, ny, nz, q) == True{} : Bool},
  heavy: {Nat.is_lt(0n, g) == True{} : Bool},
  f: {Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), gr) == True{} : Bool})
  -> {Bool.or(Nat.is_lt(0n, P.Z.neg(P.Tick.letv(gr, st, g, Nat.sub(y, ny), vy))), st) == True{} : Bool}:
  match gr st:
    case True{} True{}:
      or_there(Nat.is_lt(0n, P.Z.neg(vy)), True{}, {==})
    case True{} False{}:
      or_here(Nat.is_lt(0n, P.Pick.low(g, Nat.sub(y, ny))), False{},
        low_pos(Nat.is_le(g, Nat.sub(y, ny)), g, Nat.sub(y, ny), heavy,
          lt_sub(ny, y, or_left(Nat.is_lt(ny, y), Bool.not(P.Tick.sinks(s, obs, nx, ny, nz, q)), keep, est))))
    case False{} True{}:
      Empty.absurd({Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), True{}) == True{} : Bool}, clash2(est))
    case False{} False{}:
      f

def put_fs(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat,
  +nz: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  eok: {P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr) == ok : Bool},
  heavy: {Nat.is_lt(0n, g) == True{} : Bool},
  f: FS(P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FS(P.Tick.put(ok, s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  match ok:
    case True{}:
      putt_fs(gr, P.Tick.stands(gr, s, obs, nx, ny, nz, P.Rot.q(r2)), s, g, obs, y, nx, ny, nz, vy, P.Rot.q(r2), {==},
        and_r(P.Tick.fits(s, obs, nx, ny, nz, P.Rot.q(r2)), P.Tick.keeps(gr, s, obs, y, nx, ny, nz, P.Rot.q(r2)),
          and_r(Nat.is_le(ny, y), Bool.and(P.Tick.fits(s, obs, nx, ny, nz, P.Rot.q(r2)),
            P.Tick.keeps(gr, s, obs, y, nx, ny, nz, P.Rot.q(r2))), eok)),
        heavy, f)
    case False{}:
      f

def place_fs(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FS(P.Tick.place(s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  put_fs(P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr), s, g, obs, x, y, z, nx, ny, nz,
    vx, vy, vz, gr, hit, rt, r2, {==}, heavy, f)

def pivot_fs(m: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FS(P.Tick.pivot(m, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, rx, ry, rz)):
  P.Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = P.Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = P.Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = P.Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = P.Tick.drop(s, obs, nx, y, nz, P.Rot.q(r2), Nat.add(Nat.sub(y, P.Pick.low(ny, y)), Nat.div(s, 256n)))
  place_fs(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, hit, rt, r2, heavy, f)

def cand_fs(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool}, +f: {Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), gr) == True{} : Bool})
  -> FS(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  pivot_fs(P.Rot.mat(P.Quat.half(P.Quat.step(w, P.Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    P.Rot{P.Rot.turn(P.Rot.q(rt), w), P.Rot.w(rt)}, rx, ry, rz, heavy, f)

def shrink_fs(n: Nat, p: P.Body & Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool}, +f: {Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), gr) == True{} : Bool},
  hb: FS(Body.of_pair(p)))
  -> FS(P.Tick.shrink(n, p, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  match n:
    case 0n:
      match p:
        case (b, ok):
          hb
    case 1n+m:
      match p:
        case (b, ok):
          match ok:
            case True{}:
              hb
            case False{}:
              shrink_fs(m, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, heavy, f, Tick.shrink.pair_up((kb: P.Body) => FS(kb), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt, cand_fs(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, heavy, f)))

def start_fs(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool}, +f: {Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), gr) == True{} : Bool})
  -> FS(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  shrink_fs(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, heavy, f, Tick.shrink.pair_up((kb: P.Body) => FS(kb), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt, cand_fs(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, heavy, f)))

def keepw_fs(+tip: Bool, moved: Bool, +b: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool}, +f: {Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), gr) == True{} : Bool},
  hb: Once.Body((kb: P.Body) => FS(kb), b))
  -> Once.Body((kb: P.Body) => FS(kb), P.Body.spin(tip, moved, b, rt)):
  match moved:
    case True{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb
    case False{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb

def pivota0_fs.k1(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv,
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool},
  +f: {Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), gr) == True{} : Bool})
  -> Once.Body((kb: P.Body) => FS(kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  P.Wv{+ax, +ay, +az} = a
  keepw_fs(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))), P.Tick.moved(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, heavy, f, Once.Body.up((kb: P.Body) => FS(kb), (P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az)), start_fs(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az, heavy, f)))

def pivota0_fs(+md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, +a: P.Wv,
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool},
  +f: {Bool.or(Nat.is_lt(0n, P.Z.neg(vy)), gr) == True{} : Bool})
  -> FS(P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  Once.Body.down((kb: P.Body) => FS(kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a),
    pivota0_fs.k1(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a, heavy, f))

def pivota_fs(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FS(P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)):
  match obs:
    case []:
      pivota0_fs(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, heavy, f)
    case o <> rest:
      pivota0_fs(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, heavy, f)

def turn2_fs(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FS(P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)):
  match held floor:
    case False{} _:
      place_fs(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2, heavy, f)
    case True{} False{}:
      pivota_fs(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s), heavy, f)
    case True{} True{}:
      pivota_fs(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s), heavy, f)

def turn1b_fs(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(b))
  -> FS(P.Tick.turn1b(s, g, obs, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  turn2_fs(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Rot.free(rt),
    P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), heavy, f)

def turn1_fs(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(b))
  -> FS(P.Tick.turn1(still, s, g, obs, b)):
  match still:
    case True{}:
      f
    case False{}:
      turn1b_fs(s, g, obs, b, heavy, f)

def turn_fs(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +b: P.Body,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(b))
  -> FS(P.Tick.turn(s, g, obs, b)):
  match obs:
    case []:
      turn1_fs(P.Wv.null(P.Rot.w(P.Body.rot(b))), s, g, [], b, heavy, f)
    case o <> rest:
      turn1_fs(P.Wv.null(P.Rot.w(P.Body.rot(b))), s, g, o <> rest, b, heavy, f)

def spin_fs(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  heavy: {Nat.is_lt(0n, g) == True{} : Bool}, f: FS(P.Tick.body(r)))
  -> FS(P.Tick.body(P.Tick.spin(s, g, r))):
  (+b, +obs) = r
  turn_fs(s, g, obs, b, heavy, f)

def yfly_fs(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +q: Nat,
  hv: {P.Body.vy(b) == P.Neg{q} : P.Z},
  going: {Nat.is_lt(0n, q) == True{} : Bool})
  -> FS(P.Move.yfly(s, g, obs, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  %Equal.sym(P.Z, vy, P.Neg{q}, hv)
    : FS(P.Move.fly(s, obs, x, y, z, vx, _, vz, hit, P.Fly.step(g, _), rt))
  fly_fs(s, obs, x, y, z, vx, vz, hit, g, q, rt, going)

def ygo_fs(gr: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +q: Nat,
  hg: {gr == False{} : Bool},
  hv: {P.Body.vy(b) == P.Neg{q} : P.Z},
  going: {Nat.is_lt(0n, q) == True{} : Bool})
  -> FS(P.Move.ygo(s, gr, g, obs, b)):
  match gr:
    case True{}:
      Empty.absurd(FS(P.Move.ystay(s, g, obs, b)), clash(hg))
    case False{}:
      yfly_fs(s, g, obs, b, q, hv, going)

def my_fs(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +q: Nat,
  hg: {P.Body.ground(b) == False{} : Bool},
  hv: {P.Body.vy(b) == P.Neg{q} : P.Z},
  going: {Nat.is_lt(0n, q) == True{} : Bool})
  -> FS(P.Move.y(s, g, obs, b)):
  ygo_fs(P.Body.ground(b), s, g, obs, b, q, hg, hv, going)

def energy_turn_eq(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Body.energy(g, P.Tick.turn(s, g, obs, b)) == P.Body.energy(g, b) : Nat}:
  %Equal.sym(P.Body, P.Tick.turn(s, g, obs, b), P.Body.setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b))),
    turn_eq(s, g, obs, b, free)) : {P.Body.energy(g, _) == P.Body.energy(g, b) : Nat}
  energy_setrot(g, b, P.Body.rot(P.Tick.turn(s, g, obs, b)))

def vx_turn_eq(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Body.vx(P.Tick.turn(s, g, obs, b)) == P.Body.vx(b) : P.Z}:
  %Equal.sym(P.Body, P.Tick.turn(s, g, obs, b), P.Body.setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b))),
    turn_eq(s, g, obs, b, free)) : {P.Body.vx(_) == P.Body.vx(b) : P.Z}
  vx_setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b)))

def vz_turn_eq(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Body.vz(P.Tick.turn(s, g, obs, b)) == P.Body.vz(b) : P.Z}:
  %Equal.sym(P.Body, P.Tick.turn(s, g, obs, b), P.Body.setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b))),
    turn_eq(s, g, obs, b, free)) : {P.Body.vz(_) == P.Body.vz(b) : P.Z}
  vz_setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b)))

def hit_turn_eq(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body,
  free: {P.Body.hit(P.Tick.turn(s, g, obs, b)) == False{} : Bool})
  -> {P.Body.hit(P.Tick.turn(s, g, obs, b)) == P.Body.hit(b) : Bool}:
  %Equal.sym(P.Body, P.Tick.turn(s, g, obs, b), P.Body.setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b))),
    turn_eq(s, g, obs, b, free)) : {P.Body.hit(_) == P.Body.hit(b) : Bool}
  hit_setrot(b, P.Body.rot(P.Tick.turn(s, g, obs, b)))

def spin_eq(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Tick.body(P.Tick.spin(s, g, r))
      == P.Body.setrot(P.Tick.body(r), P.Body.rot(P.Tick.body(P.Tick.spin(s, g, r)))) : P.Body}:
  (+b, +obs) = r
  turn_eq(s, g, obs, b, free)

# the tick's linear part, as the laws name it
# The tick's linear part is asked for in a shape the checker can carry
# whole (Body.step); every proof below reasons about what is inside it.
# This is the one step between the two, and it costs the checker one
# walk through the tick instead of sixteen.
def step_is(+k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body)
  -> {P.Body.step(k, obs, inp, b) == P.Body.step1(k, obs, inp, b) : P.Body & List<&2, P.Body>}:
  match obs:
    case []:
      {==}
    case o <> rest:
      {==}

# the same knock-free fact, said about the tick's linear part written
# out, which is the shape every proof below reasons in
# the same equality read the other way round
def step_sym(+k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body)
  -> {P.Body.step1(k, obs, inp, b) == P.Body.step(k, obs, inp, b) : P.Body & List<&2, P.Body>}:
  match obs:
    case []:
      {==}
    case o <> rest:
      {==}

def unhit_step(+k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body,
  h: {P.Body.hit(P.Tick.body(P.Body.step(k, obs, inp, b))) == False{} : Bool})
  -> {P.Body.hit(P.Tick.body(P.Body.step1(k, obs, inp, b))) == False{} : Bool}:
  %step_is(k, obs, inp, b) : {P.Body.hit(P.Tick.body(_)) == False{} : Bool}
  h

# the same worth, said about the tick's linear part written out
def energy_step(+g: Nat, +k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body, +c: Nat,
  h: {P.Body.energy(g, P.Tick.body(P.Body.step1(k, obs, inp, b))) == c : Nat})
  -> {P.Body.energy(g, P.Tick.body(P.Body.step(k, obs, inp, b))) == c : Nat}:
  %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(k, obs, inp, b), P.Body.step1(k, obs, inp, b),
    step_is(k, obs, inp, b)) : {P.Body.energy(g, P.Tick.body(_)) == c : Nat}
  h

def STEP(+g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, inp: P.In) -> P.Body & List<&2, P.Body>:
  P.Body.step(P.K{g, mu, j, acc, s}, obs, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})

def spin_sym(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  +free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Body.setrot(P.Tick.body(r), P.Body.rot(P.Tick.body(P.Tick.spin(s, g, r))))
      == P.Tick.body(P.Tick.spin(s, g, r)) : P.Body}:
  Equal.sym(P.Body, P.Tick.body(P.Tick.spin(s, g, r)),
    P.Body.setrot(P.Tick.body(r), P.Body.rot(P.Tick.body(P.Tick.spin(s, g, r)))), spin_eq(s, g, r, free))

def spin_energy(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Body.energy(g, P.Tick.body(P.Tick.spin(s, g, r))) == P.Body.energy(g, P.Tick.body(r)) : Nat}:
  (+b, +obs) = r
  energy_turn_eq(s, g, obs, b, free)

def spin_vx(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Body.vx(P.Tick.body(P.Tick.spin(s, g, r))) == P.Body.vx(P.Tick.body(r)) : P.Z}:
  (+b, +obs) = r
  vx_turn_eq(s, g, obs, b, free)

def spin_vz(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Body.vz(P.Tick.body(P.Tick.spin(s, g, r))) == P.Body.vz(P.Tick.body(r)) : P.Z}:
  (+b, +obs) = r
  vz_turn_eq(s, g, obs, b, free)

def spin_unhit(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>,
  +free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, r))) == False{} : Bool})
  -> {P.Body.hit(P.Tick.body(r)) == False{} : Bool}:
  (+b, +obs) = r
  Equal.trans(Bool, P.Body.hit(b), P.Body.hit(P.Tick.turn(s, g, obs, b)), False{},
    Equal.sym(Bool, P.Body.hit(P.Tick.turn(s, g, obs, b)), P.Body.hit(b), hit_turn_eq(s, g, obs, b, free)), free)

def FF(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +rt: P.Rot) -> Data:
  {P.Body.hit(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, vx, rt), obs, P.Z.add(vx, vx),
    P.Z.shift(x, P.Z.add(vx, vx)), P.Body{x,y,z,vx,vy,vz,False{},False{},rt})))) == False{} : Bool}

# its y move never ran past the floor
def ff_fy(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, free: FF(s, g, obs, x, y, z, vx, vy, vz, rt))
  -> {P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))) == True{} : Bool}:
  and_r(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))),
    and_r(P.Z.fits(x, P.Z.add(vx, vx)), Bool.and(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))),
      x_air_ok(rt, s, Ok1(s, obs, vx, x, y, z, vx, rt), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, {==}, free)))

def ffe(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +hit: Bool,
  +free: FF(s, g, obs, x, y, z, vx, vy, vz, rt))
  -> {P.Body.energy(g, P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, vx, rt), obs, P.Z.add(vx, vx),
        P.Z.shift(x, P.Z.add(vx, vx)), P.Body{x,y,z,vx,vy,vz,False{},False{},rt}))))
      == P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}) : Nat}:
  %x_air_eq(rt, s, Ok1(s, obs, vx, x, y, z, vx, rt), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, free)
    : {P.Body.energy(g, _) == P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}) : Nat}
  fly_energy(g, y, vy, P.Z.sq(vx), P.Z.sq(vz), ff_fy(rt, s, g, obs, x, y, z, vx, vy, vz, free))

def Laws.free_flight_energy(k, obs, b, air, free):
  match k b:
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          Empty.absurd({P.Body.energy(g, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(),
              P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}))) == P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}) : Nat},
            clash(air))
        case False{}:
          %Equal.sym(P.Body, P.Tick.body(P.Tick.spin(s, g, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))),
            P.Body.setrot(P.Tick.body(P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt})),
              P.Body.rot(P.Tick.body(P.Tick.spin(s, g, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))))),
            spin_eq(s, g, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}), free))
            : {P.Body.energy(g, _) == P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}) : Nat}
          Equal.trans(Nat,
            P.Body.energy(g, P.Body.setrot(P.Tick.body(P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt})),
              P.Body.rot(P.Tick.body(P.Tick.spin(s, g, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt})))))),
            P.Body.energy(g, P.Tick.body(P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))),
            P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            energy_setrot(g, P.Tick.body(P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt})),
              P.Body.rot(P.Tick.body(P.Tick.spin(s, g, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))))),
            energy_step(g, P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt},
              P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
              ffe(rt, s, g, obs, x, y, z, vx, vy, vz, hit,
                unhit_step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt},
                  spin_unhit(s, g, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}), free)))))

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

def ff_fx(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, free: FF(s, g, obs, x, y, z, vx, vy, vz, rt))
  -> {P.Z.fits(x, P.Z.add(vx, vx)) == True{} : Bool}:
  and_l(P.Z.fits(x, P.Z.add(vx, vx)), Bool.and(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))),
    x_air_ok(rt, s, Ok1(s, obs, vx, x, y, z, vx, rt), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, {==}, free))

def ff_fz(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, free: FF(s, g, obs, x, y, z, vx, vy, vz, rt))
  -> {P.Z.fits(z, P.Z.add(vz, vz)) == True{} : Bool}:
  and_l(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy))),
    and_r(P.Z.fits(x, P.Z.add(vx, vx)), Bool.and(P.Z.fits(z, P.Z.add(vz, vz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, vy)))),
      x_air_ok(rt, s, Ok1(s, obs, vx, x, y, z, vx, rt), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, {==}, free)))

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

def ffk(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +hit: Bool,
  +free: FF(s, g, obs, x, y, z, vx, vy, vz, rt))
  -> Kin(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}, P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, vx, rt), obs,
       P.Z.add(vx, vx), P.Z.shift(x, P.Z.add(vx, vx)), P.Body{x,y,z,vx,vy,vz,False{},False{},rt})))):
  %x_air_eq(rt, s, Ok1(s, obs, vx, x, y, z, vx, rt), g, obs, vz, P.Z.add(vx, vx), x, y, z, vx, vy, vz, free)
    : Kin(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}, _)
  (fly_kv(g, vy), fly_ky(g, y, vy, ff_fy(rt, s, g, obs, x, y, z, vx, vy, vz, free)), {==}, {==},
    hkin(x, vx, ff_fx(rt, s, g, obs, x, y, z, vx, vy, vz, free)), hkin(z, vz, ff_fz(rt, s, g, obs, x, y, z, vx, vy, vz, free)))

# the same kinematics, said about the tick's linear part written out
def kin_step(+g: Nat, +b0: P.Body, +k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body,
  h: Kin(g, b0, P.Tick.body(P.Body.step1(k, obs, inp, b))))
  -> Kin(g, b0, P.Tick.body(P.Body.step(k, obs, inp, b))):
  %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(k, obs, inp, b), P.Body.step1(k, obs, inp, b),
    step_is(k, obs, inp, b)) : Kin(g, b0, P.Tick.body(_))
  h

def Laws.free_flight_kinematics(k, obs, b, air, free):
  match k b:
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          Empty.absurd(Kin(g, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs,
              P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}))), clash(air))
        case False{}:
          %spin_sym(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, False{}, hit, rt, P.In.idle()), free)
            : Kin(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}, _)
          kin_step(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}, P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt},
            ffk(rt, s, g, obs, x, y, z, vx, vy, vz, hit,
              unhit_step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt},
                spin_unhit(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, False{}, hit, rt, P.In.idle()), free))))

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
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          Empty.absurd({P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt})
              == P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt})
              : P.Body & List<&2, P.Body>}, clash(air))
        case False{}:
          %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            step_is(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))
            : {P.Tick.spin(s, g, _) == P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}) : P.Body & List<&2, P.Body>}
          %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            step_is(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))
            : {P.Tick.spin(s, g, P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))
               == P.Tick.spin(s, g, _) : P.Body & List<&2, P.Body>}
          {==}

# on the ground the motor adds acc along the wish to whatever friction left
def MS(+acc: Nat, +ux: P.Z, +uz: P.Z, +b1: P.Body, +b0: P.Body) -> Type:
  {P.Body.vx(b1) == P.Z.add(P.Body.vx(b0), P.Z.q12(acc, ux)) : P.Z}
  & {P.Body.vz(b1) == P.Z.add(P.Body.vz(b0), P.Z.q12(acc, uz)) : P.Z}

def Laws.motor_is_steady(k, b, ux, uz, stand):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          ({==}, {==})
        case False{}:
          Empty.absurd(MS(acc, ux, uz,
            P.Body.drive(P.K{g, mu, j, acc, s}, P.In{Some{P.Wish{ux, uz}}, False{}},
              P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt})),
            clash2(stand))

def Laws.no_air_jump(k, obs, w, b, air):
  match k b:
    case P.K{+g, mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          Empty.absurd({P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{w, True{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt})
              == P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt})
              : P.Body & List<&2, P.Body>}, clash(air))
        case False{}:
          %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In{w, True{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In{w, True{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            step_is(P.K{g, mu, j, acc, s}, obs, P.In{w, True{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))
            : {P.Tick.spin(s, g, _) == P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}) : P.Body & List<&2, P.Body>}
          %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}),
            step_is(P.K{g, mu, j, acc, s}, obs, P.In{w, False{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))
            : {P.Tick.spin(s, g, P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In{w, True{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))
               == P.Tick.spin(s, g, _) : P.Body & List<&2, P.Body>}
          {==}

# a takeoff from the ground, untouched: the body after driving is at
# (x, y, z) with velocity (fx, J, fz)
def FJ(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z, +j: Nat, +rt: P.Rot) -> Data:
  {P.Body.hit(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx, rt), obs, P.Z.add(vx, fx),
    P.Z.shift(x, P.Z.add(vx, fx)), P.Body{x,y,z,fx,P.Pos{j},fz,False{},False{},rt})))) == False{} : Bool}

# the body a jump's tick leaves, before the turn
def JBody(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z,
  +fz: P.Z, +j: Nat, +rt: P.Rot) -> P.Body:
  P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx, rt), obs, P.Z.add(vx, fx),
    P.Z.shift(x, P.Z.add(vx, fx)), P.Body{x,y,z,fx,P.Pos{j},fz,False{},False{},rt})))

# what a jump is worth: the going it keeps, the jump itself, and the
# height -- said once, so a proof can move it from one body to another
# without writing it out again
def JE(+g: Nat, +j: Nat, +y: Nat, +c: P.Body) -> Data:
  {P.Body.energy(g, c) == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(c)), P.Z.sq(P.Body.vz(c))),
    Nat.mul(j, j)), Nat.mul(g, y)) : Nat}

# the same claim with the body's worth written out, which is what is
# left of it once the turn has been taken out of the way
def JEo(+g: Nat, +j: Nat, +y: Nat, +c: P.Body) -> Data:
  {Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(c)), P.Z.sq(P.Body.vy(c))), P.Z.sq(P.Body.vz(c))),
    Nat.mul(g, P.Body.y(c)))
   == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(c)), P.Z.sq(P.Body.vz(c))), Nat.mul(j, j)), Nat.mul(g, y)) : Nat}

def energy_open(+g: Nat, b: P.Body)
  -> {Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(b)), P.Z.sq(P.Body.vy(b))), P.Z.sq(P.Body.vz(b))),
    Nat.mul(g, P.Body.y(b)))
      == P.Body.energy(g, b) : Nat}:
  P.Body{+x, +y2, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  {==}

def je_open(+g: Nat, +j: Nat, +y: Nat, +b: P.Body, h: JE(g, j, y, b)) -> JEo(g, j, y, b):
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(b)), P.Z.sq(P.Body.vy(b))), P.Z.sq(P.Body.vz(b))),
    Nat.mul(g, P.Body.y(b))),
    P.Body.energy(g, b), energy_open(g, b)) : {_ == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(b)), P.Z.sq(P.Body.vz(b))), Nat.mul(j, j)), Nat.mul(g, y)) : Nat}
  h

def je(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z, +j: Nat,
  +free: FJ(s, g, obs, x, y, z, vx, vz, fx, fz, j, rt))
  -> JE(g, j, y, JBody(s, g, obs, x, y, z, vx, vz, fx, fz, j, rt)):
  %x_air_eq(rt, s, Ok1(s, obs, vx, x, y, z, fx, rt), g, obs, vz, P.Z.add(vx, fx), x, y, z, fx, P.Pos{j}, fz, free)
    : {P.Body.energy(g, _) == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(_)), P.Z.sq(P.Body.vz(_))), Nat.mul(j, j)), Nat.mul(g, y)) : Nat}
  Equal.trans(Nat, P.Body.energy(g, Fz(g, P.Z.shift(x, P.Z.add(vx, fx)), y, z, P.Z.add(vz, fz), fx, P.Pos{j}, fz, rt)),
    Nat.add(Nat.add(Nat.add(P.Z.sq(fx), Nat.mul(j, j)), P.Z.sq(fz)), Nat.mul(g, y)),
    Nat.add(Nat.add(Nat.add(P.Z.sq(fx), P.Z.sq(fz)), Nat.mul(j, j)), Nat.mul(g, y)),
    fly_energy(g, y, P.Pos{j}, P.Z.sq(fx), P.Z.sq(fz),
      and_r(P.Z.fits(z, P.Z.add(vz, fz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, P.Pos{j}))),
        and_r(P.Z.fits(x, P.Z.add(vx, fx)), Bool.and(P.Z.fits(z, P.Z.add(vz, fz)), P.Z.fits(y, P.Share.snd(P.Fly.step(g, P.Pos{j})))),
          x_air_ok(rt, s, Ok1(s, obs, vx, x, y, z, fx, rt), g, obs, vz, P.Z.add(vx, fx), x, y, z, fx, P.Pos{j}, fz, {==}, free)))),
    R.eq([P.Z.sq(fx), P.Z.sq(fz), j, g, y],
      R.Add{R.Add{R.Add{R.V{0n}, R.Mul{R.V{2n}, R.V{2n}}}, R.V{1n}}, R.Mul{R.V{3n}, R.V{4n}}},
      R.Add{R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Mul{R.V{2n}, R.V{2n}}}, R.Mul{R.V{3n}, R.V{4n}}}, {==}))

def je2(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vz: P.Z, +fx: P.Z, +fz: P.Z, +j: Nat, +free: FJ(s, g, obs, x, y, z, vx, vz, fx, fz, j, rt))
  -> JEo(g, j, y, JBody(s, g, obs, x, y, z, vx, vz, fx, fz, j, rt)):
  je_open(g, j, y, JBody(s, g, obs, x, y, z, vx, vz, fx, fz, j, rt), je(rt, s, g, obs, x, y, z, vx, vz, fx, fz, j, free))

# The one law still open: jump_energy.
#
# The law is true. A turn leaves the going and the height alone (the
# lemmas above say so), and turning about a contact marks hit, which
# the law's no-knock hypothesis leaves out. What is missing is a way to
# say it that the checker can carry: the tick's own term is enormous,
# and the checker walks it out whole each time it meets it. Measured:
# it carries TWO meetings and falls over on the third. je2 below is one
# meeting (the linear part, with the body's worth written out); the
# turn needs another, and the two together are one too many.
#
# Tried and not enough: one rewrite at the law; the rewrite plus a
# bridge; the bridge alone; both moves inside a lemma over a name (the
# pair has to be taken apart there, which walks the term out again);
# the opening handed in ready-made. Each piece checks on its own.

# the same jump claim, said about the tick's linear part written out
def jeo_step(+g: Nat, +j: Nat, +y: Nat, +k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body,
  h: JEo(g, j, y, P.Tick.body(P.Body.step1(k, obs, inp, b))))
  -> JEo(g, j, y, P.Tick.body(P.Body.step(k, obs, inp, b))):
  %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(k, obs, inp, b), P.Body.step1(k, obs, inp, b),
    step_is(k, obs, inp, b)) : JEo(g, j, y, P.Tick.body(_))
  h

def Laws.jump_energy(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, +j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          %spin_sym(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In{None{}, True{}}), free) : JE(g, j, y, _)
          jeo_step(g, j, y, P.K{g, mu, j, acc, s}, obs, P.In{None{}, True{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
            je2(rt, s, g, obs, x, y, z, vx, vz, P.Share.fst(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz)), P.Share.snd(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz)), j,
              unhit_step(P.K{g, mu, j, acc, s}, obs, P.In{None{}, True{}}, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
                spin_unhit(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In{None{}, True{}}), free))))
        case False{}:
          Empty.absurd({P.Body.energy(g, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{None{}, True{}},
              P.Body{x, y, z, vx, vy, vz, False{}, hit, rt})))
            == Nat.add(Nat.add(Nat.add(P.Z.sq(P.Body.vx(P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In{None{}, True{}},
              P.Body{x, y, z, vx, vy, vz, False{}, hit, rt})))), P.Z.sq(P.Body.vz(P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs,
              P.In{None{}, True{}}, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))))), Nat.mul(j, j)), Nat.mul(g, y)) : Nat},
            clash2(stand))

# The free path, on the ground
# ----------------------------

# a body held up keeps its place and its going: the press of the hold
# only turns it, so the body that comes out is the body that went in,
# turned another way
def stay_eq(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot)
  -> {P.Body.setrot(P.Body{x, y, z, vx, vy, vz, rest, hit, rt},
        P.Body.rot(P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt)))
      == P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt) : P.Body}:
  match rest:
    case True{}:
      {==}
    case False{}:
      {==}

def Gz(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +dz: P.Z, +vx: P.Z, +vy: P.Z, +vz: P.Z, +rt: P.Rot) -> P.Body:
  P.Body{x, y, P.Z.shift(z, dz), vx, vy, vz,
    P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, P.Z.shift(z, dz), P.Rot.q(rt), obs), False{}, rt}

def z_gnd_eq(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))))
    == False{} : Bool})
  -> {P.Body.setrot(Gz(s, obs, x, y, z, dz, vx, vy, vz, rt),
        P.Body.rot(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))))
      == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))) : P.Body}:
  match ok:
    case True{}:
      stay_eq(P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, P.Z.shift(z, dz), P.Rot.q(rt), obs), s, g, obs,
        x, y, P.Z.shift(z, dz), vx, vy, vz, False{}, rt)
    case False{}:
      Empty.absurd({P.Body.setrot(Gz(s, obs, x, y, z, dz, vx, vy, vz, rt),
            P.Body.rot(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, False{}, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))))
          == P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, False{}, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))),
          hit_ty(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}),
            hit_zno(s, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, True{}, False{}, rt)),
          free))

def x_gnd_eq(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))))
    == False{} : Bool})
  -> {P.Body.setrot(Gz(s, obs, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz, rt),
        P.Body.rot(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))))
      == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))) : P.Body}:
  match ok:
    case True{}:
      z_gnd_eq(rt, s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), P.Rot.q(rt), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, free)
    case False{}:
      Empty.absurd({P.Body.setrot(Gz(s, obs, P.Z.shift(x, dx), y, z, P.Z.add(v0z, vz), vx, vy, vz, rt),
            P.Body.rot(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, False{}, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))))
          == P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, False{}, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))) : P.Body},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))),
          hit_tz(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}),
            hit_xno(s, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, True{}, False{}, rt)),
          free))

def z_gnd_ok(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +dz: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  eok: {Bool.and(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), P.Rot.q(rt), obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zgo(s, ok, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))))
    == False{} : Bool})
  -> {P.Z.fits(z, dz) == True{} : Bool}:
  match ok:
    case True{}:
      and_l(P.Z.fits(z, dz), P.Geo.free(s, x, y, P.Z.shift(z, dz), P.Rot.q(rt), obs), eok)
    case False{}:
      Empty.absurd({P.Z.fits(z, dz) == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.y(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))),
          hit_ty(s, g, P.Move.zno(s, obs, dz, P.Z.shift(z, dz), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}),
            hit_zno(s, obs, dz, P.Z.shift(z, dz), x, y, z, vx, vy, vz, True{}, False{}, rt)),
          free))

def x_gnd_ok(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +v0z: P.Z, +dx: P.Z, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z,
  eok: {Bool.and(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, P.Rot.q(rt), obs)) == ok : Bool},
  free: {P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xgo(s, ok, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}))))
    == False{} : Bool})
  -> {Bool.and(P.Z.fits(x, dx), P.Z.fits(z, P.Z.add(v0z, vz))) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Bool, P.Z.fits(x, dx), True{}, and_l(P.Z.fits(x, dx), P.Geo.free(s, P.Z.shift(x, dx), y, z, P.Rot.q(rt), obs), eok))
        : {Bool.and(_, P.Z.fits(z, P.Z.add(v0z, vz))) == True{} : Bool}
      z_gnd_ok(rt, s, Bool.and(P.Z.fits(z, P.Z.add(v0z, vz)), P.Geo.free(s, P.Z.shift(x, dx), y, P.Z.shift(z, P.Z.add(v0z, vz)), P.Rot.q(rt), obs)),
        g, obs, P.Z.add(v0z, vz), P.Z.shift(x, dx), y, z, vx, vy, vz, {==}, free)
    case False{}:
      Empty.absurd({Bool.and(P.Z.fits(x, dx), P.Z.fits(z, P.Z.add(v0z, vz))) == True{} : Bool},
        unhit(P.Body.hit(P.Tick.body(P.Tick.z(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt})))),
          hit_tz(s, g, v0z, P.Move.xno(s, obs, dx, P.Z.shift(x, dx), P.Body{x,y,z,vx,vy,vz,True{},False{},rt}),
            hit_xno(s, obs, dx, P.Z.shift(x, dx), x, y, z, vx, vy, vz, True{}, False{}, rt)),
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
def FG(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z, +rt: P.Rot) -> Data:
  {P.Body.hit(P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx, rt), obs, P.Z.add(vx, fx),
    P.Z.shift(x, P.Z.add(vx, fx)), P.Body{x,y,z,fx,P.Pos{0n},fz,True{},False{},rt})))) == False{} : Bool}

def GB(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z, +rt: P.Rot) -> P.Body:
  P.Tick.body(P.Tick.z(s, g, vz, P.Move.xgo(s, Ok1(s, obs, vx, x, y, z, fx, rt), obs, P.Z.add(vx, fx),
    P.Z.shift(x, P.Z.add(vx, fx)), P.Body{x,y,z,fx,P.Pos{0n},fz,True{},False{},rt})))

def NR(+vx: P.Z, +vz: P.Z, +b2: P.Body) -> Type:
  {Nat.is_le(P.Z.pos(P.Body.vx(b2)), P.Z.pos(vx)) == True{} : Bool}
  & {Nat.is_le(P.Z.neg(P.Body.vx(b2)), P.Z.neg(vx)) == True{} : Bool}
  & {Nat.is_le(P.Z.pos(P.Body.vz(b2)), P.Z.pos(vz)) == True{} : Bool}
  & {Nat.is_le(P.Z.neg(P.Body.vz(b2)), P.Z.neg(vz)) == True{} : Bool}

def fnr(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +t1: Nat, +t2: Nat,
  free: FG(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), rt))
  -> NR(vx, vz, GB(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), rt)):
  %x_gnd_eq(rt, s, Ok1(s, obs, vx, x, y, z, P.Z.cut(t1, vx), rt), g, obs, vz, P.Z.add(vx, P.Z.cut(t1, vx)), x, y, z, P.Z.cut(t1, vx), P.Pos{0n},
      P.Z.cut(t2, vz), free)
    : NR(vx, vz, _)
  (nr_pos(t1, vx), nr_neg(t1, vx), nr_pos(t2, vz), nr_neg(t2, vz))

# the friction a tick takes from each component
def T1(+f: Nat, +vx: P.Z, +vz: P.Z) -> Nat:
  P.Fric.take(f, P.Z.mag(vx), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz)))

def T2(+f: Nat, +vx: P.Z, +vz: P.Z) -> Nat:
  P.Fric.take(f, P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz)))

# the same claim, said about the tick's linear part written out
def nr_step(+vx: P.Z, +vz: P.Z, +k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body,
  h: NR(vx, vz, P.Tick.body(P.Body.step1(k, obs, inp, b))))
  -> NR(vx, vz, P.Tick.body(P.Body.step(k, obs, inp, b))):
  %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(k, obs, inp, b), P.Body.step1(k, obs, inp, b),
    step_is(k, obs, inp, b)) : NR(vx, vz, P.Tick.body(_))
  h

def Laws.friction_never_reverses(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          %spin_sym(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In.idle()), free)
            : NR(vx, vz, _)
          nr_step(vx, vz, P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
            fnr(rt, s, g, obs, x, y, z, vx, vz, T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), T2(Nat.div(Nat.mul(mu, g), 256n), vx, vz),
              unhit_step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
                spin_unhit(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In.idle()), free))))
        case False{}:
          Empty.absurd(NR(vx, vz, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(),
              P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))), clash2(stand))

def pick_le(ok: Bool, +t: Nat, +a: Nat, -h: Bool, e: {Bool.and(Nat.is_le(t, a), h) == ok : Bool})
  -> {Nat.is_le(P.Pick.n(ok, t, 0n), a) == True{} : Bool}:
  match ok:
    case True{}:
      and_l(Nat.is_le(t, a), h, e)
    case False{}:
      le_add(0n, a)

# friction takes no more than the component has
def take_le(+f: Nat, +a: Nat, +s: Nat) -> {Nat.is_le(P.Fric.take(f, a, s), a) == True{} : Bool}:
  pick_le(Bool.and(Nat.is_le(P.Pick.low(a, Nat.div(Nat.mul(f, a), s)), a),
      Nat.is_le(Nat.mul(P.Pick.low(a, Nat.div(Nat.mul(f, a), s)), s), Nat.mul(f, a))),
    P.Pick.low(a, Nat.div(Nat.mul(f, a), s)), a,
    Nat.is_le(Nat.mul(P.Pick.low(a, Nat.div(Nat.mul(f, a), s)), s), Nat.mul(f, a)), {==})

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

def fw_ok(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +fx: P.Z, +fz: P.Z,
  free: FG(s, g, obs, x, y, z, vx, vz, fx, fz, rt))
  -> {Bool.and(P.Z.fits(x, P.Z.add(vx, fx)), P.Z.fits(z, P.Z.add(vz, fz))) == True{} : Bool}:
  x_gnd_ok(rt, s, Ok1(s, obs, vx, x, y, z, fx, rt), g, obs, vz, P.Z.add(vx, fx), x, y, z, fx, P.Pos{0n}, fz, {==}, free)

def fwork(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +t1: Nat, +t2: Nat,
  h1: {Nat.is_le(t1, P.Z.mag(vx)) == True{} : Bool}, h2: {Nat.is_le(t2, P.Z.mag(vz)) == True{} : Bool},
  +free: FG(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), rt))
  -> FW(x, y, z, vx, vz, GB(s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), rt)):
  %x_gnd_eq(rt, s, Ok1(s, obs, vx, x, y, z, P.Z.cut(t1, vx), rt), g, obs, vz, P.Z.add(vx, P.Z.cut(t1, vx)), x, y, z, P.Z.cut(t1, vx), P.Pos{0n},
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
     fw_ok(rt, s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), free))),
   kin_cut(z, t2, vz, and_r(P.Z.fits(x, P.Z.add(vx, P.Z.cut(t1, vx))), P.Z.fits(z, P.Z.add(vz, P.Z.cut(t2, vz))),
     fw_ok(rt, s, g, obs, x, y, z, vx, vz, P.Z.cut(t1, vx), P.Z.cut(t2, vz), free))),
   {==})

# the same claim, said about the tick's linear part written out
def fw_step(+x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body,
  h: FW(x, y, z, vx, vz, P.Tick.body(P.Body.step1(k, obs, inp, b))))
  -> FW(x, y, z, vx, vz, P.Tick.body(P.Body.step(k, obs, inp, b))):
  %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(k, obs, inp, b), P.Body.step1(k, obs, inp, b),
    step_is(k, obs, inp, b)) : FW(x, y, z, vx, vz, P.Tick.body(_))
  h

def Laws.friction_work(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          %spin_sym(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In.idle()), free)
            : FW(x, y, z, vx, vz, _)
          fw_step(x, y, z, vx, vz, P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
            fwork(rt, s, g, obs, x, y, z, vx, vz, T1(Nat.div(Nat.mul(mu, g), 256n), vx, vz), T2(Nat.div(Nat.mul(mu, g), 256n), vx, vz),
              take_le(Nat.div(Nat.mul(mu, g), 256n), P.Z.mag(vx), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))),
              take_le(Nat.div(Nat.mul(mu, g), 256n), P.Z.mag(vz), P.Fric.speed(P.Z.mag(vx), P.Z.mag(vz))),
              unhit_step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
                spin_unhit(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In.idle()), free))))
        case False{}:
          Empty.absurd(FW(x, y, z, vx, vz, P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs, P.In.idle(),
              P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))), clash2(stand))

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
  pick_mul(Bool.and(Nat.is_le(P.Pick.low(a, Nat.div(Nat.mul(f, a), s)), a),
      Nat.is_le(Nat.mul(P.Pick.low(a, Nat.div(Nat.mul(f, a), s)), s), Nat.mul(f, a))),
    P.Pick.low(a, Nat.div(Nat.mul(f, a), s)), a, s, f, {==})

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

def cfric(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +f: Nat,
  free: FG(s, g, obs, x, y, z, vx, vz, P.Z.cut(T1(f, vx, vz), vx), P.Z.cut(T2(f, vx, vz), vz), rt))
  -> CF(vx, vz, f, GB(s, g, obs, x, y, z, vx, vz, P.Z.cut(T1(f, vx, vz), vx), P.Z.cut(T2(f, vx, vz), vz), rt)):
  %x_gnd_eq(rt, s, Ok1(s, obs, vx, x, y, z, P.Z.cut(T1(f, vx, vz), vx), rt), g, obs, vz, P.Z.add(vx, P.Z.cut(T1(f, vx, vz), vx)), x, y, z,
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

# the same claim, said about the tick's linear part written out
def cf_step(+vx: P.Z, +vz: P.Z, +f: Nat, +k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body,
  h: CF(vx, vz, f, P.Tick.body(P.Body.step1(k, obs, inp, b))))
  -> CF(vx, vz, f, P.Tick.body(P.Body.step(k, obs, inp, b))):
  %Equal.sym(P.Body & List<&2, P.Body>, P.Body.step(k, obs, inp, b), P.Body.step1(k, obs, inp, b),
    step_is(k, obs, inp, b)) : CF(vx, vz, f, P.Tick.body(_))
  h

def Laws.coulomb_friction(k, obs, b, stand, free):
  match k b:
    case P.K{+g, +mu, j, acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt}:
      match gr:
        case True{}:
          %spin_sym(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In.idle()), free)
            : CF(vx, vz, Nat.div(Nat.mul(mu, g), 256n), _)
          cf_step(vx, vz, Nat.div(Nat.mul(mu, g), 256n), P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
            cfric(rt, s, g, obs, x, y, z, vx, vz, Nat.div(Nat.mul(mu, g), 256n),
              unhit_step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, True{}, hit, rt},
                spin_unhit(s, g, STEP(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, True{}, hit, rt, P.In.idle()), free))))
        case False{}:
          Empty.absurd(CF(vx, vz, Nat.div(Nat.mul(mu, g), 256n), P.Tick.body(P.Body.tick(P.K{g, mu, j, acc, s}, obs,
              P.In.idle(), P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))), clash2(stand))

# Rest
# ----

def sub_zero_l(+n: Nat) -> {Nat.sub(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def Rest(+x: Nat, +y: Nat, +z: Nat, +rt: P.Rot) -> P.Body:
  P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt}

# friction on nothing moving leaves it still
def rs_drive(+f: Nat) -> {(P.Pos{0n}, P.Pos{0n}) == P.Fric.apply(f, P.Pos{0n}, P.Pos{0n}) : P.Z & P.Z}:
  %sub_zero_l(P.Fric.take(f, 0n, P.Fric.speed(0n, 0n)))
    : {(P.Pos{_}, P.Pos{_}) == P.Fric.apply(f, P.Pos{0n}, P.Pos{0n}) : P.Z & P.Z}
  {==}

# The hold's press turns the body, so what comes out of the vertical step
# is the body it went in as, turned the way the press left it.
def RestT(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot) -> P.Body:
  P.Body.setrot(Rest(x, y, z, rt), P.Body.rot(P.Tick.body(P.Tick.y(s, g, (Rest(x, y, z, rt), obs)))))

def stay_eq2(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +hit: Bool,
  +rt: P.Rot)
  -> {(P.Move.stay(rest, s, g, obs, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, hit, rt), obs)
      == (P.Body.setrot(P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, rest, hit, rt},
           P.Body.rot(P.Move.stay(rest, s, g, obs, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, hit, rt))), obs)
      : P.Body & List<&2, P.Body>}:
  match rest:
    case True{}:
      {==}
    case False{}:
      {==}

def rs_y(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  on: {P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Tick.y(s, g, (Rest(x, y, z, rt), obs)) == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}:
  %Equal.sym(Bool, P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs), True{}, on)
    : {(P.Move.stay(_, s, g, obs, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, rt), obs)
       == (P.Body.setrot(P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt},
            P.Body.rot(P.Move.stay(_, s, g, obs, x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, rt))), obs)
       : P.Body & List<&2, P.Body>}
  stay_eq2(True{}, s, g, obs, x, y, z, False{}, rt)

def rs_z(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  on: {P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool},
  clear: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Tick.y(s, g, P.Move.z(s, obs, P.Pos{0n}, Rest(x, y, z, rt))) == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}:
  %R.add_zero_s(z)
    : {P.Tick.y(s, g, P.Move.zgo(s, P.Geo.free(s, x, y, _, P.Rot.q(rt), obs), obs, P.Pos{0n}, _, P.Body{x,y,z,P.Pos{0n},P.Pos{0n},P.Pos{0n},True{},False{},rt}))
       == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}
  %Equal.sym(Bool, P.Geo.free(s, x, y, z, P.Rot.q(rt), obs), True{}, clear)
    : {P.Tick.y(s, g, P.Move.zgo(s, _, obs, P.Pos{0n}, z, P.Body{x,y,z,P.Pos{0n},P.Pos{0n},P.Pos{0n},True{},False{},rt}))
       == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}
  rs_y(s, g, obs, x, y, z, rt, on)

def rs_x(+rt: P.Rot, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  on: {P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool},
  +clear: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Tick.z(s, g, P.Pos{0n}, P.Move.x(s, obs, P.Pos{0n}, Rest(x, y, z, rt))) == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}:
  %R.add_zero_s(x)
    : {P.Tick.z(s, g, P.Pos{0n}, P.Move.xgo(s, P.Geo.free(s, _, y, z, P.Rot.q(rt), obs), obs, P.Pos{0n}, _, P.Body{x,y,z,P.Pos{0n},P.Pos{0n},P.Pos{0n},True{},False{},rt}))
       == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}
  %Equal.sym(Bool, P.Geo.free(s, x, y, z, P.Rot.q(rt), obs), True{}, clear)
    : {P.Tick.z(s, g, P.Pos{0n}, P.Move.xgo(s, _, obs, P.Pos{0n}, x, P.Body{x,y,z,P.Pos{0n},P.Pos{0n},P.Pos{0n},True{},False{},rt}))
       == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}
  rs_z(rt, s, g, obs, x, y, z, on, clear)

def pair_eq(+a: P.Body, +c: P.Body, obs: List<&2, P.Body>, e: {a == c : P.Body})
  -> {(a, obs) == (c, obs) : P.Body & List<&2, P.Body>}:
  %Equal.sym(P.Body, a, c, e) : {(_, obs) == (c, obs) : P.Body & List<&2, P.Body>}
  {==}

def tb_eq(a: P.Body & List<&2, P.Body>, c: P.Body & List<&2, P.Body>,
  e: {a == c : P.Body & List<&2, P.Body>}) -> {P.Tick.body(a) == P.Tick.body(c) : P.Body}:
  %Equal.sym(P.Body & List<&2, P.Body>, a, c, e) : {P.Tick.body(_) == P.Tick.body(c) : P.Body}
  {==}

def rs_free(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, a: P.Body & List<&2, P.Body>, +c: P.Body,
  e: {a == (c, obs) : P.Body & List<&2, P.Body>},
  free: {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, a))) == False{} : Bool})
  -> {P.Body.hit(P.Tick.turn(s, g, obs, c)) == False{} : Bool}:
  %e : {P.Body.hit(P.Tick.body(P.Tick.spin(s, g, _))) == False{} : Bool}
  free

# the tick's linear part on a body at rest leaves it where it was, turned
# the way the hold's press left it
def rs_all(+rt: P.Rot, +s: Nat, +g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat,
  +z: Nat, +h: Bool,
  on: {P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool},
  +clear: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})
      == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}:
  %step_sym(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})
    : {_ == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}
  %rs_drive(Nat.div(Nat.mul(mu, g), 256n))
    : {P.Tick.z(s, g, P.Pos{0n}, P.Move.x(s, obs, P.Pos{0n}, P.Drive.ground(P.K{g, mu, j, acc, s}, None{}, False{}, x, y, z, _, rt)))
       == (RestT(s, g, obs, x, y, z, rt), obs) : P.Body & List<&2, P.Body>}
  rs_x(rt, s, g, obs, x, y, z, on, clear)

def Laws.rest_stays(k, obs, x, y, z, h, rt, on, clear, free):
  match k:
    case P.K{+g, +mu, +j, +acc, +s}:
      %Equal.sym(P.Body & List<&2, P.Body>,
         P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}),
         (RestT(s, g, obs, x, y, z, rt), obs),
         rs_all(rt, s, g, mu, j, acc, obs, x, y, z, h, on, clear))
        : {P.Tick.spin(s, g, _)
           == (P.Body.setrot(Rest(x, y, z, rt), P.Body.rot(P.Tick.body(P.Tick.spin(s, g, _)))), obs) : P.Body & List<&2, P.Body>}
      pair_eq(P.Tick.turn(s, g, obs, RestT(s, g, obs, x, y, z, rt)),
        P.Body.setrot(Rest(x, y, z, rt), P.Body.rot(P.Tick.turn(s, g, obs, RestT(s, g, obs, x, y, z, rt)))), obs,
        turn_eq(s, g, obs, RestT(s, g, obs, x, y, z, rt),
          rs_free(s, g, obs,
            P.Body.step(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}),
            RestT(s, g, obs, x, y, z, rt),
            rs_all(rt, s, g, mu, j, acc, obs, x, y, z, h, on, clear), free)))

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
  h: {Nat.is_le(Nat.add(P.Z.sq(P.Share.fst(vw)), P.Z.sq(P.Share.snd(vw))), Nat.add(P.Z.sq(v), P.Z.sq(ovx))) == True{} : Bool}, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.xput(vw, at, ox, oy, oz, ovy, ovz, og, oh, rest, rt))),
                        P.Body.energies(g, Pobs(P.Push.xput(vw, at, ox, oy, oz, ovy, ovz, og, oh, rest, rt)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, rt} <> rest))) == True{} : Bool}:
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
  h: {Nat.is_le(Nat.add(P.Z.sq(P.Share.fst(vw)), P.Z.sq(P.Share.snd(vw))), Nat.add(P.Z.sq(v), P.Z.sq(ovz))) == True{} : Bool}, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.zput(vw, at, ox, oy, oz, ovx, ovy, og, oh, rest, rt))),
                        P.Body.energies(g, Pobs(P.Push.zput(vw, at, ox, oy, oz, ovx, ovy, og, oh, rest, rt)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, rt} <> rest))) == True{} : Bool}:
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
def push_x_e(+qa: P.Quat, +s: Nat, +g: Nat, obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +y: Nat, +z: Nat, +v: P.Z, here: Bool)
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.x(s, obs, d, cx, y, z, v, qa, here))), P.Body.energies(g, Pobs(P.Push.x(s, obs, d, cx, y, z, v, qa, here)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, obs))) == True{} : Bool}:
  match obs here:
    case Nil{} _:
      le_refl(Nat.add(P.Z.sq(v), 0n))
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +rt} <> +rest True{}:
      xput_e(g, P.Push.share(P.Push.closing(d, v, ovx), v, ovx), P.Push.stop(s, d, ox), ox, oy, oz, ovx, ovy, ovz, og, oh, rest, v,
        share_e(P.Push.closing(d, v, ovx), v, ovx), rt)
    case +o <> +rest False{}:
      cons_e(g, o, P.Push.x(s, rest, d, cx, y, z, v, qa, P.Geo.head(s, cx, y, z, qa, rest)), v, rest,
        push_x_e(qa, s, g, rest, d, cx, y, z, v, P.Geo.head(s, cx, y, z, qa, rest)))

def push_z_e(+qa: P.Quat, +s: Nat, +g: Nat, obs: List<&2, P.Body>, +d: P.Z, +x: Nat, +y: Nat, +cz: Nat, +v: P.Z, here: Bool)
  -> {Nat.is_le(Nat.add(P.Z.sq(Pv(P.Push.z(s, obs, d, x, y, cz, v, qa, here))), P.Body.energies(g, Pobs(P.Push.z(s, obs, d, x, y, cz, v, qa, here)))),
                Nat.add(P.Z.sq(v), P.Body.energies(g, obs))) == True{} : Bool}:
  match obs here:
    case Nil{} _:
      le_refl(Nat.add(P.Z.sq(v), 0n))
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +rt} <> +rest True{}:
      zput_e(g, P.Push.share(P.Push.closing(d, v, ovz), v, ovz), P.Push.stop(s, d, oz), ox, oy, oz, ovx, ovy, ovz, og, oh, rest, v,
        share_e(P.Push.closing(d, v, ovz), v, ovz), rt)
    case +o <> +rest False{}:
      cons_e(g, o, P.Push.z(s, rest, d, x, y, cz, v, qa, P.Geo.head(s, x, y, cz, qa, rest)), v, rest,
        push_z_e(qa, s, g, rest, d, x, y, cz, v, P.Geo.head(s, x, y, cz, qa, rest)))

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
  h: {Nat.is_le(Nat.add(P.Z.sq(v), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(vx), P.Body.energies(g, obs))) == True{} : Bool}, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xput(ok, obs2, cx, x, y, z, v, vy, vz, gr, rt))), P.Body.energies(g, P.Tick.obs(P.Move.xput(ok, obs2, cx, x, y, z, v, vy, vz, gr, rt)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  match ok:
    case True{}:
      res_e(g, vx, v, P.Z.sq(vy), P.Z.sq(vz), y, obs, obs2, h)
    case False{}:
      res_e(g, vx, v, P.Z.sq(vy), P.Z.sq(vz), y, obs, obs2, h)

def xpushed_me(+g: Nat, r: P.Pushed, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool,
  +hit: Bool, +obs: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(Pv(r)), P.Body.energies(g, Pobs(r))), Nat.add(P.Z.sq(vx), P.Body.energies(g, obs))) == True{} : Bool}, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt))), P.Body.energies(g, P.Tick.obs(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  P.Pushed{+v, +obs2, at} = r
  res_e(g, vx, v, P.Z.sq(vy), P.Z.sq(vz), y, obs, obs2, h)

def xtouch_me(touch: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +pr: Nat, +x: Nat, +y: Nat,
  +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xtouch(touch, s, obs, d, cx, pr, x, y, z, vx, vy, vz, gr, rt))), P.Body.energies(g, P.Tick.obs(P.Move.xtouch(touch, s, obs, d, cx, pr, x, y, z, vx, vy, vz, gr, rt)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  match touch:
    case True{}:
      xpushed_me(g, P.Push.x(s, obs, d, pr, y, z, vx, P.Rot.q(rt), P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs)), cx, x, y, z,
        vx, vy, vz, gr, hit, obs, push_x_e(P.Rot.q(rt), s, g, obs, d, pr, y, z, vx, P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs)), rt)
    case False{}:
      xput_me(P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), g, obs, cx, x, y, z, vx, vx, vy, vz, gr, hit, obs,
        le_refl(Nat.add(P.Z.sq(vx), P.Body.energies(g, obs))), rt)

def xno_me(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xno(s, obs, d, cx, P.Body{x,y,z,vx,vy,vz,gr,hit,rt}))), P.Body.energies(g, P.Tick.obs(P.Move.xno(s, obs, d, cx, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  xtouch_me(P.Move.xtouches(s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), y, z, P.Rot.q(rt)), s, g, obs, d,
    P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, hit, rt)

def xgo_me(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.xgo(s, ok, obs, d, cx, P.Body{x,y,z,vx,vy,vz,gr,hit,rt}))), P.Body.energies(g, P.Tick.obs(P.Move.xgo(s, ok, obs, d, cx, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs)))))
      == True{} : Bool}:
  match ok:
    case True{}:
      le_refl(Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs)))))
    case False{}:
      xno_me(s, g, obs, d, cx, x, y, z, vx, vy, vz, gr, hit, rt)

def mx_e(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.x(s, obs, v0, b))), P.Body.energies(g, P.Tick.obs(P.Move.x(s, obs, v0, b)))), Nat.add(P.Body.energy(g, P.Tick.body((b, obs))), P.Body.energies(g, P.Tick.obs((b, obs))))) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  xgo_me(s, Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, P.Rot.q(rt), obs)), g, obs,
    P.Z.add(v0, vx), P.Z.shift(x, P.Z.add(v0, vx)), x, y, z, vx, vy, vz, gr, hit, rt)

def zput_me(ok: Bool, +g: Nat, +obs2: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +obs: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(v), P.Body.energies(g, obs2)), Nat.add(P.Z.sq(vz), P.Body.energies(g, obs))) == True{} : Bool}, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.zput(ok, obs2, cz, x, y, z, vx, vy, v, gr, rt))), P.Body.energies(g, P.Tick.obs(P.Move.zput(ok, obs2, cz, x, y, z, vx, vy, v, gr, rt)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  match ok:
    case True{}:
      res_ez(g, vz, v, P.Z.sq(vx), P.Z.sq(vy), y, obs, obs2, h)
    case False{}:
      res_ez(g, vz, v, P.Z.sq(vx), P.Z.sq(vy), y, obs, obs2, h)

def zpushed_me(+g: Nat, r: P.Pushed, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool,
  +hit: Bool, +obs: List<&2, P.Body>,
  h: {Nat.is_le(Nat.add(P.Z.sq(Pv(r)), P.Body.energies(g, Pobs(r))), Nat.add(P.Z.sq(vz), P.Body.energies(g, obs))) == True{} : Bool}, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt))), P.Body.energies(g, P.Tick.obs(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  P.Pushed{+v, +obs2, at} = r
  res_ez(g, vz, v, P.Z.sq(vx), P.Z.sq(vy), y, obs, obs2, h)

def ztouch_me(touch: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +pr: Nat, +x: Nat, +y: Nat,
  +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.ztouch(touch, s, obs, d, cz, pr, x, y, z, vx, vy, vz, gr, rt))), P.Body.energies(g, P.Tick.obs(P.Move.ztouch(touch, s, obs, d, cz, pr, x, y, z, vx, vy, vz, gr, rt)))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  match touch:
    case True{}:
      zpushed_me(g, P.Push.z(s, obs, d, x, y, pr, vz, P.Rot.q(rt), P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs)), cz, x, y, z,
        vx, vy, vz, gr, hit, obs, push_z_e(P.Rot.q(rt), s, g, obs, d, x, y, pr, vz, P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs)), rt)
    case False{}:
      zput_me(P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), g, obs, cz, x, y, z, vx, vy, vz, vz, gr, hit, obs,
        le_refl(Nat.add(P.Z.sq(vz), P.Body.energies(g, obs))), rt)

def zno_me(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.zno(s, obs, d, cz, P.Body{x,y,z,vx,vy,vz,gr,hit,rt}))), P.Body.energies(g, P.Tick.obs(P.Move.zno(s, obs, d, cz, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))))) == True{} : Bool}:
  ztouch_me(P.Move.ztouches(s, obs, d, x, y, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Rot.q(rt)), s, g, obs, d,
    P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, hit, rt)

def zgo_me(+s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.zgo(s, ok, obs, d, cz, P.Body{x,y,z,vx,vy,vz,gr,hit,rt}))), P.Body.energies(g, P.Tick.obs(P.Move.zgo(s, ok, obs, d, cz, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})))), Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs)))))
      == True{} : Bool}:
  match ok:
    case True{}:
      le_refl(Nat.add(P.Body.energy(g, P.Tick.body((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs))), P.Body.energies(g, P.Tick.obs((P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs)))))
    case False{}:
      zno_me(s, g, obs, d, cz, x, y, z, vx, vy, vz, gr, hit, rt)

def mz_e(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.z(s, obs, v0, b))), P.Body.energies(g, P.Tick.obs(P.Move.z(s, obs, v0, b)))), Nat.add(P.Body.energy(g, P.Tick.body((b, obs))), P.Body.energies(g, P.Tick.obs((b, obs))))) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  zgo_me(s, Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), P.Rot.q(rt), obs)), g, obs,
    P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr, hit, rt)

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
       == Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)) : Nat}, +rt: P.Rot)
  -> {Nat.is_le(P.Body.energy(g, P.Move.rise(ok, x, y, z, p, vx, v, vz, hit, rt)),
                Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  match ok:
    case True{}:
      le_eq(Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(v)), P.Z.sq(vz)), Nat.mul(g, Nat.add(y, p))),
        Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)), he)
    case False{}:
      stop_e(P.Z.sq(vx), P.Z.sq(vz), P.Z.sq(vy), g, y, y, le_refl(y))

def land_e(ok: Bool, +g: Nat, +x: Nat, +y: Nat, +z: Nat, +ny: Nat, +vx: P.Z, +vz: P.Z, +vy: P.Z,
  hle: {Nat.is_le(ny, y) == True{} : Bool}, +rt: P.Rot)
  -> {Nat.is_le(P.Body.energy(g, P.Move.land(ok, x, y, z, ny, vx, vz, vy, rt)), Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  match ok:
    case True{}:
      stop_e(P.Z.sq(vx), P.Z.sq(vz), P.Z.sq(vy), g, y, ny, hle)
    case False{}:
      le_refl(Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)))

def fall_e(+rt: P.Rot, +s: Nat, ok: Bool, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +vy: P.Z, +hit: Bool,
  eok: {P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)) == ok : Bool},
  hf: {Nat.is_le(q, y) == True{} : Bool}
    -> {Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(v)), P.Z.sq(vz)), Nat.mul(g, Nat.sub(y, q)))
        == Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)) : Nat})
  -> {Nat.is_le(P.Body.energy(g, P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, vy, hit, rt)), Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  match ok:
    case True{}:
      le_eq(Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(v)), P.Z.sq(vz)), Nat.mul(g, Nat.sub(y, q))), Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)),
        hf(and_l(Nat.is_le(q, y), Bool.and(P.Tick.fits(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt)),
          P.Tick.path(64n, Nat.is_lt(s, q), s, obs, x, y, z, P.Rot.q(rt), q, s)), eok)))
    case False{}:
      land_e(P.Move.landok(s, obs, x, P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), z, P.Rot.q(rt)), g, x, y, z,
        P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), vx, vz, vy, sub_le(y, P.Tick.drop(s, obs, x, y, z, P.Rot.q(rt), q)), rt)

def fly_le(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +hit: Bool, +vy: P.Z, st: P.Z & P.Z,
  hf: {P.Z.fits(y, P.Share.snd(st)) == True{} : Bool}
    -> {Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(P.Share.fst(st))), P.Z.sq(vz)), Nat.mul(g, P.Z.shift(y, P.Share.snd(st))))
        == Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y)) : Nat}, +rt: P.Rot)
  -> {Nat.is_le(P.Body.energy(g, P.Move.fly(s, obs, x, y, z, vx, vy, vz, hit, st, rt)), Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      rise_e(P.Geo.free(s, x, Nat.add(y, p), z, P.Rot.q(rt), obs), g, x, y, z, p, vx, v, vz, vy, hit, hf({==}), rt)
    case P.Neg{+q}:
      fall_e(rt, s, P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)), g, obs, x, y, z, q, vx, v, vz, vy, hit, {==}, hf)

# the press of a hold only turns the body, and what it is worth does not
# depend on how it is turned
def stay_e(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(P.Body.energy(g, P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt})) == True{} : Bool}:
  match rest:
    case True{}:
      le_refl(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}))
    case False{}:
      le_refl(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, True{}, hit, rt}))

def my_e(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body) -> {Nat.is_le(P.Body.energy(g, P.Move.y(s, g, obs, b)), P.Body.energy(g, b)) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  match gr:
    case True{}:
      stay_e(P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs), s, g, obs, x, y, z, vx, vy, vz, hit, rt)
    case False{}:
      fly_le(s, g, obs, x, y, z, vx, vz, hit, vy, P.Fly.step(g, vy), h => fly_energy(g, y, vy, P.Z.sq(vx), P.Z.sq(vz), h), rt)

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
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
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
      le_refl(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, False{}, hit, rt}))

# Turning is worth nothing
# -----------------------
# A turn is taken only where it lets the body down, and it never changes
# how fast the body is going, so the energy it ends with is at most the
# energy it began with. Every way of turning ends in that one choice.

# a <= b false gives b <= a
def le_flip(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, clash(h))
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, clash(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_flip(p, q, h)

# the smaller of g and d, squared, is at most g d
def low_sq(le: Bool, +g: Nat, +d: Nat, e: {Nat.is_le(g, d) == le : Bool})
  -> {Nat.is_le(Nat.mul(P.Pick.n(le, g, d), P.Pick.n(le, g, d)), Nat.mul(g, d)) == True{} : Bool}:
  match le:
    case True{}:
      le_mul_l(g, g, d, e)
    case False{}:
      %R.eq([g, d], R.Mul{R.V{1n}, R.V{0n}}, R.Mul{R.V{0n}, R.V{1n}}, {==}) : {Nat.is_le(Nat.mul(d, d), _) == True{} : Bool}
      le_mul_l(d, d, g, le_flip(g, d, e))

# Letting go makes no energy: a body whose middle went down d = y - ny
# and leaves going down at min(g, d) has at most what it had -- the drop
# gave up g d, and min(g, d) squared is at most that.
def let_e(+A: Nat, +V: Nat, +C: Nat, +g: Nat, +y: Nat, +ny: Nat, hle: {Nat.is_le(ny, y) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(A, Nat.mul(P.Pick.low(g, Nat.sub(y, ny)), P.Pick.low(g, Nat.sub(y, ny)))), C), Nat.mul(g, ny)),
                Nat.add(Nat.add(Nat.add(A, V), C), Nat.mul(g, y))) == True{} : Bool}:
  +L = Nat.mul(P.Pick.low(g, Nat.sub(y, ny)), P.Pick.low(g, Nat.sub(y, ny)))
  +W = Nat.mul(g, Nat.sub(y, ny))
  le_trans(Nat.add(Nat.add(Nat.add(A, L), C), Nat.mul(g, ny)),
    Nat.add(Nat.add(Nat.add(A, Nat.add(W, V)), C), Nat.mul(g, ny)),
    Nat.add(Nat.add(Nat.add(A, V), C), Nat.mul(g, y)),
    le_sum(Nat.add(Nat.add(A, L), C), Nat.add(Nat.add(A, Nat.add(W, V)), C), Nat.mul(g, ny),
      le_sum(Nat.add(A, L), Nat.add(A, Nat.add(W, V)), C,
        le_add2(A, A, L, Nat.add(W, V), le_refl(A),
          le_trans(L, W, Nat.add(W, V), low_sq(Nat.is_le(g, Nat.sub(y, ny)), g, Nat.sub(y, ny), {==}), le_add(W, V))))),
    le_eq(Nat.add(Nat.add(Nat.add(A, Nat.add(W, V)), C), Nat.mul(g, ny)), Nat.add(Nat.add(Nat.add(A, V), C), Nat.mul(g, y)),
      %sub_add(ny, y, hle)
        : {Nat.add(Nat.add(Nat.add(A, Nat.add(W, V)), C), Nat.mul(g, ny)) == Nat.add(Nat.add(Nat.add(A, V), C), Nat.mul(g, _)) : Nat}
      R.eq([A, V, C, g, ny, Nat.sub(y, ny)],
        R.Add{R.Add{R.Add{R.V{0n}, R.Add{R.Mul{R.V{3n}, R.V{5n}}, R.V{1n}}}, R.V{2n}}, R.Mul{R.V{3n}, R.V{4n}}},
        R.Add{R.Add{R.Add{R.V{0n}, R.V{1n}}, R.V{2n}}, R.Mul{R.V{3n}, R.Add{R.V{4n}, R.V{5n}}}}, {==})))

def putt_e(gr: Bool, st: Bool, +g: Nat, +y: Nat, +ny: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  hle: {Nat.is_le(ny, y) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(P.Tick.letv(gr, st, g, Nat.sub(y, ny), vy))), P.Z.sq(vz)), Nat.mul(g, ny)),
       Nat.add(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, y))) == True{} : Bool}:
  match gr st:
    case True{} True{}:
      le_add2(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, ny), Nat.mul(g, y), le_refl(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz))), le_mul_l(g, ny, y, hle))
    case True{} False{}:
      let_e(P.Z.sq(vx), P.Z.sq(vy), P.Z.sq(vz), g, y, ny, hle)
    case False{} True{}:
      le_add2(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, ny), Nat.mul(g, y), le_refl(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz))), le_mul_l(g, ny, y, hle))
    case False{} False{}:
      le_add2(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz)), Nat.mul(g, ny), Nat.mul(g, y), le_refl(Nat.add(Nat.add(P.Z.sq(vx), P.Z.sq(vy)), P.Z.sq(vz))), le_mul_l(g, ny, y, hle))

def put_e2(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat,
  +nz: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  eok: {P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr) == ok : Bool})
  -> {Nat.is_le(P.Body.energy(g, P.Tick.put(ok, s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  match ok:
    case True{}:
      putt_e(gr, P.Tick.stands(gr, s, obs, nx, ny, nz, P.Rot.q(r2)), g, y, ny, vx, vy, vz,
        and_l(Nat.is_le(ny, y), Bool.and(P.Tick.fits(s, obs, nx, ny, nz, P.Rot.q(r2)),
          P.Tick.keeps(gr, s, obs, y, nx, ny, nz, P.Rot.q(r2))), eok))
    case False{}:
      le_refl(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))

def place_e2(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.place(s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  put_e2(P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr), s, g, obs, x, y, z, nx, ny, nz,
    vx, vy, vz, gr, hit, rt, r2, {==})

def pivot_e2(m: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +rx: P.Z, +ry: P.Z, +rz: P.Z)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.pivot(m, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, rx, ry, rz)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  P.Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = P.Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = P.Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = P.Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = P.Tick.drop(s, obs, nx, y, nz, P.Rot.q(r2), Nat.add(Nat.sub(y, P.Pick.low(ny, y)), Nat.div(s, 256n)))
  place_e2(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, hit, rt, r2)

def cand_e2(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  pivot_e2(P.Rot.mat(P.Quat.half(P.Quat.step(w, P.Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    P.Rot{P.Rot.turn(P.Rot.q(rt), w), P.Rot.w(rt)}, rx, ry, rz)

def shrink_e2.t1(+c: P.Body, +g: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, hc1: {Nat.is_le(P.Body.energy(g, c), P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool})
  -> Once.Body(((kb: P.Body) => {Nat.is_le(P.Body.energy((g), kb), P.Body.energy((g), P.Body{(x), (y), (z), (vx), (vy), (vz), (gr), (hit), (rt)})) == True{} : Bool}), Body.of_pair((P.Tick.shrink.pair(c, rt)))):
  Once.Body.up((kb: P.Body) => {Nat.is_le(P.Body.energy((g), kb), P.Body.energy((g), P.Body{(x), (y), (z), (vx), (vy), (vz), (gr), (hit), (rt)})) == True{} : Bool}, Body.of_pair((P.Tick.shrink.pair(c, rt))), Tick.shrink.pair_up((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb), P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, c, rt, hc1))

def shrink_e2(n: Nat, p: P.Body & Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  hb: Once.Body((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, Body.of_pair(p)))
  -> Once.Body((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, P.Tick.shrink(n, p, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  match n:
    case 0n:
      match p:
        case (b, ok):
          hb
    case 1n+m:
      match p:
        case (b, ok):
          match ok:
            case True{}:
              hb
            case False{}:
              shrink_e2(m, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, shrink_e2.t1(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), g, x, y, z, vx, vy, vz, gr, hit, rt, cand_e2(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz)))

def start_e2.t1(+c: P.Body, +g: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, hc1: {Nat.is_le(P.Body.energy(g, c), P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool})
  -> Once.Body(((kb: P.Body) => {Nat.is_le(P.Body.energy((g), kb), P.Body.energy((g), P.Body{(x), (y), (z), (vx), (vy), (vz), (gr), (hit), (rt)})) == True{} : Bool}), Body.of_pair((P.Tick.shrink.pair(c, rt)))):
  Once.Body.up((kb: P.Body) => {Nat.is_le(P.Body.energy((g), kb), P.Body.energy((g), P.Body{(x), (y), (z), (vx), (vy), (vz), (gr), (hit), (rt)})) == True{} : Bool}, Body.of_pair((P.Tick.shrink.pair(c, rt))), Tick.shrink.pair_up((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb), P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, c, rt, hc1))

def start_e2.t2(+c: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z, hc1: {Nat.is_le(P.Body.energy(g, c), P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool})
  -> Once.Body((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb), P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, P.Tick.shrink(7n, P.Tick.shrink.pair(c, rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  shrink_e2(7n, P.Tick.shrink.pair(c, rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, start_e2.t1(c, g, x, y, z, vx, vy, vz, gr, hit, rt, hc1))

def start_e2(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z)
  -> Once.Body((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  start_e2.t2(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, cand_e2(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz))

def keepw_e2(+tip: Bool, moved: Bool, +b: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  hb: Once.Body((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, b))
  -> Once.Body((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, P.Body.spin(tip, moved, b, rt)):
  match moved:
    case True{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb
    case False{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb

def pivota0_e2.k1(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv)
  -> Once.Body((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  P.Wv{+ax, +ay, +az} = a
  keepw_e2(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))), P.Tick.moved(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    start_e2(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az))

def pivota0_e2(+md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, +a: P.Wv)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  Once.Body.down((kb: P.Body) => {Nat.is_le(P.Body.energy(g, kb),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a),
    pivota0_e2.k1(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a))

def pivota_e2(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  match obs:
    case []:
      pivota0_e2(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a)
    case o <> rest:
      pivota0_e2(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a)

def turn2_e2(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  match held floor:
    case False{} _:
      place_e2(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2)
    case True{} False{}:
      pivota_e2(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))
    case True{} True{}:
      pivota_e2(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))

def turn1_e2(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})),
       P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == True{} : Bool}:
  match still:
    case True{}:
      le_refl(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
    case False{}:
      turn2_e2(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx,
        vy, vz, gr, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))))

def turn_e20(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.turn0(s, g, obs, b)), P.Body.energy(g, b)) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  turn1_e2(P.Wv.null(P.Rot.w(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt)

def turn_e2(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.turn(s, g, obs, b)), P.Body.energy(g, b)) == True{} : Bool}:
  %turn_sym(s, g, obs, b) : {Nat.is_le(P.Body.energy(g, _), P.Body.energy(g, b)) == True{} : Bool}
  turn_e20(s, g, obs, b)

def spin_e2(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Tick.spin(s, g, r))), P.Body.energies(g, P.Tick.obs(P.Tick.spin(s, g, r)))),
       Nat.add(P.Body.energy(g, P.Tick.body(r)), P.Body.energies(g, P.Tick.obs(r)))) == True{} : Bool}:
  (+b, +obs) = r
  le_sum(P.Body.energy(g, P.Tick.turn(s, g, obs, b)), P.Body.energy(g, b), P.Body.energies(g, obs),
    turn_e2(s, g, obs, b))

# the tick's linear part never makes energy
def eng_step(+g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
       P.Body.energies(g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))),
       Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs))) == True{} : Bool}:
      le_trans(Nat.add(P.Body.energy(g, P.Tick.body(P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(),
            P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))))), P.Body.energies(g, P.Tick.obs(P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(),
            P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))))),
        Nat.add(P.Body.energy(g, P.Tick.body(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), P.Body.energies(g, P.Tick.obs(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))))),
        Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs)),
        tz_e(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
        le_trans(Nat.add(P.Body.energy(g, P.Tick.body(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), P.Body.energies(g, P.Tick.obs(P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))))),
          Nat.add(P.Body.energy(g, P.Tick.body((P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), obs))), P.Body.energies(g, P.Tick.obs((P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), obs)))),
          Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs)),
          mx_e(s, g, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})),
          le_sum(P.Body.energy(g, P.Body.drive(P.K{g, mu, j, acc, s}, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})),
            P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs),
            drive_e(s, g, mu, j, acc, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))))

# the energy bound, carried from the tick's linear part written out to
# the linear part left whole
def e2_step(+g: Nat, +k: P.K, obs: List<&2, P.Body>, inp: P.In, b: P.Body, +c: Nat,
  h: {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Body.step1(k, obs, inp, b))),
       P.Body.energies(g, P.Tick.obs(P.Body.step1(k, obs, inp, b)))), c) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Body.step(k, obs, inp, b))),
       P.Body.energies(g, P.Tick.obs(P.Body.step(k, obs, inp, b)))), c) == True{} : Bool}:
  %step_sym(k, obs, inp, b)
    : {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(_)), P.Body.energies(g, P.Tick.obs(_))), c) == True{} : Bool}
  h

def eng_step_b(+k: P.K, +obs: List<&2, P.Body>, +b: P.Body)
  -> {Nat.is_le(Nat.add(P.Body.energy(P.K.g(k), P.Tick.body(P.Body.step(k, obs, P.In.idle(), b))),
       P.Body.energies(P.K.g(k), P.Tick.obs(P.Body.step(k, obs, P.In.idle(), b)))),
       Nat.add(P.Body.energy(P.K.g(k), b), P.Body.energies(P.K.g(k), obs))) == True{} : Bool}:
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      eng_step(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, gr, hit, rt)

# the whole tick's energy bound: the turn on top of the tick's linear
# part never raises it either, and the body is still a name here
# two sums compared a piece at a time: one side is bounded, the other is
# the same on both, and the checker never has to hold all four tick-sized
# terms at once
def le_two(+a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat, +c: Nat,
  h1: {Nat.is_le(a1, b1) == True{} : Bool},
  h2: {a2 == b2 : Nat},
  h3: {Nat.is_le(Nat.add(b1, b2), c) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a1, a2), c) == True{} : Bool}:
  %Equal.sym(Nat, a2, b2, h2) : {Nat.is_le(Nat.add(a1, _), c) == True{} : Bool}
  le_trans(Nat.add(a1, b2), Nat.add(b1, b2), c, le_sum(a1, b1, b2, h1), h3)

# what the turn stage does to a pair, taken apart once and for all
def spin_body_r(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>)
  -> {P.Tick.turn(s, g, P.Tick.obs(r), P.Tick.body(r)) == P.Tick.body(P.Tick.spin(s, g, r)) : P.Body}:
  (+b, +obs) = r
  {==}

def spin_obs_r(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>)
  -> {P.Tick.obs(r) == P.Tick.obs(P.Tick.spin(s, g, r)) : List<&2, P.Body>}:
  (+b, +obs) = r
  {==}

# the turn never raises the body's own energy
def spin_body_le(+g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot)
  -> {Nat.is_le(P.Body.energy(g, P.Tick.turn(s, g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})), P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), P.Body.energy(g, P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))) == True{} : Bool}:
  turn_e2(s, g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})), P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))

# the law's own words, taken in: the tick is the step turned, and the
# obstacles it ends with are the ones the step ended with
def ea_in(+g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  h: {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.turn(s, g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})), P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), P.Body.energies(g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs))) == True{} : Bool})
  -> Laws.EnergyAfter(P.K{g, mu, j, acc, s}, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}):
  %spin_body_r(s, g, P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
    : {Nat.is_le(Nat.add(P.Body.energy(g, _), P.Body.energies(g, P.Tick.obs(P.Tick.spin(s, g, P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))))), Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs))) == True{} : Bool}
  %spin_obs_r(s, g, P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
    : {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.turn(s, g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})), P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), P.Body.energies(g, _)), Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs))) == True{} : Bool}
  h

# the two sums put together, still in the step's own names
def spin_sum(+g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  h: {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
       P.Body.energies(g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.turn(s, g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})), P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), P.Body.energies(g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs))) == True{} : Bool}:
  le_two(P.Body.energy(g, P.Tick.turn(s, g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})), P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), P.Body.energies(g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
    P.Body.energy(g, P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))), P.Body.energies(g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
    Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs)), spin_body_le(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, gr, hit, rt), {==}, h)

# the whole tick's energy bound: the turn never raises what the linear
# part left
def spin_eng(+g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  h: {Nat.is_le(Nat.add(P.Body.energy(g, P.Tick.body(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
       P.Body.energies(g, P.Tick.obs(P.Body.step1(P.K{g, mu, j, acc, s}, obs, P.In.idle(), P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), Nat.add(P.Body.energy(g, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}), P.Body.energies(g, obs))) == True{} : Bool})
  -> Laws.EnergyAfter(P.K{g, mu, j, acc, s}, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}):
  ea_in(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, gr, hit, rt, spin_sum(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, gr, hit, rt, h))

def Laws.energy_never_grows(k, obs, b):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      spin_eng(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, gr, hit, rt, eng_step(g, mu, j, acc, s, obs, x, y, z, vx, vy, vz, gr, hit, rt))

# No clipping
# -----------
# Every move goes through a gate that takes it only to a free place, or
# stays where the body was (free by the invariant); a push changes the
# obstacles' velocities, never where they are.

# a tick's result: the body is clear of the obstacles
# no clipping, for one body after one move: where it ends up, turned the
# way it ends up turned, it is clear of everything
def NC(+s: Nat, -r: P.Body & List<&2, P.Body>) -> Type:
  {P.Geo.free(s, P.Body.x(P.Tick.body(r)), P.Body.y(P.Tick.body(r)), P.Body.z(P.Tick.body(r)),
    P.Rot.q(P.Body.rot(P.Tick.body(r))), P.Tick.obs(r)) == True{} : Bool}

def xput_free(+qa: P.Quat, +s: Nat, vw: P.Z & P.Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +rest: List<&2, P.Body>, +px: Nat, +py: Nat, +pz: Nat, +rt: P.Rot)
  -> {P.Geo.free(s, px, py, pz, qa, Pobs(P.Push.xput(vw, at, ox, oy, oz, ovy, ovz, og, oh, rest, rt)))
      == P.Geo.free(s, px, py, pz, qa, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, rt} <> rest) : Bool}:
  (v2, w2) = vw
  {==}

def zput_free(+qa: P.Quat, +s: Nat, vw: P.Z & P.Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +rest: List<&2, P.Body>, +px: Nat, +py: Nat, +pz: Nat, +rt: P.Rot)
  -> {P.Geo.free(s, px, py, pz, qa, Pobs(P.Push.zput(vw, at, ox, oy, oz, ovx, ovy, og, oh, rest, rt)))
      == P.Geo.free(s, px, py, pz, qa, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, rt} <> rest) : Bool}:
  (v2, w2) = vw
  {==}

def cons_free(+qa: P.Quat, +s: Nat, +o: P.Body, r: P.Pushed, +rest: List<&2, P.Body>, +px: Nat, +py: Nat, +pz: Nat,
  h: {P.Geo.free(s, px, py, pz, qa, Pobs(r)) == P.Geo.free(s, px, py, pz, qa, rest) : Bool})
  -> {P.Geo.free(s, px, py, pz, qa, Pobs(P.Push.cons(o, r))) == P.Geo.free(s, px, py, pz, qa, o <> rest) : Bool}:
  P.Pushed{v, +obs2, at} = r
  %Equal.sym(Bool, P.Geo.free(s, px, py, pz, qa, obs2), P.Geo.free(s, px, py, pz, qa, rest), h)
    : {Bool.and(Bool.not(P.Geo.meets(s, px, py, pz, qa, o)), _) == P.Geo.free(s, px, py, pz, qa, o <> rest) : Bool}
  {==}

def push_x_free(+qa: P.Quat, +s: Nat, obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +y: Nat, +z: Nat, +v: P.Z, here: Bool, +px: Nat, +py: Nat, +pz: Nat)
  -> {P.Geo.free(s, px, py, pz, qa, Pobs(P.Push.x(s, obs, d, cx, y, z, v, qa, here))) == P.Geo.free(s, px, py, pz, qa, obs) : Bool}:
  match obs here:
    case Nil{} _:
      {==}
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +rt} <> +rest True{}:
      xput_free(qa, s, P.Push.share(P.Push.closing(d, v, ovx), v, ovx), P.Push.stop(s, d, ox), ox, oy, oz, ovx, ovy, ovz, og, oh, rest,
        px, py, pz, rt)
    case +o <> +rest False{}:
      cons_free(qa, s, o, P.Push.x(s, rest, d, cx, y, z, v, qa, P.Geo.head(s, cx, y, z, qa, rest)), rest, px, py, pz,
        push_x_free(qa, s, rest, d, cx, y, z, v, P.Geo.head(s, cx, y, z, qa, rest), px, py, pz))

def push_z_free(+qa: P.Quat, +s: Nat, obs: List<&2, P.Body>, +d: P.Z, +x: Nat, +y: Nat, +cz: Nat, +v: P.Z, here: Bool, +px: Nat, +py: Nat, +pz: Nat)
  -> {P.Geo.free(s, px, py, pz, qa, Pobs(P.Push.z(s, obs, d, x, y, cz, v, qa, here))) == P.Geo.free(s, px, py, pz, qa, obs) : Bool}:
  match obs here:
    case Nil{} _:
      {==}
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +rt} <> +rest True{}:
      zput_free(qa, s, P.Push.share(P.Push.closing(d, v, ovz), v, ovz), P.Push.stop(s, d, oz), ox, oy, oz, ovx, ovy, ovz, og, oh, rest,
        px, py, pz, rt)
    case +o <> +rest False{}:
      cons_free(qa, s, o, P.Push.z(s, rest, d, x, y, cz, v, qa, P.Geo.head(s, x, y, cz, qa, rest)), rest, px, py, pz,
        push_z_free(qa, s, rest, d, x, y, cz, v, P.Geo.head(s, x, y, cz, qa, rest), px, py, pz))

def xput_nc(+rt: P.Rot, +s: Nat, ok: Bool, +obs2: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool,
  +step: Bool, eok: {Bool.and(step, P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs2)) == ok : Bool},
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs2) == True{} : Bool})
  -> NC(s, P.Move.xput(ok, obs2, cx, x, y, z, v, vy, vz, gr, rt)):
  match ok:
    case True{}:
      and_r(step, P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs2), eok)
    case False{}:
      h

def xpushed_nc(+rt: P.Rot, +s: Nat, r: P.Pushed, +cx: Nat, +y: Nat, +z: Nat, +vy: P.Z, +vz: P.Z, +gr: Bool,
  h: {P.Geo.free(s, cx, y, z, P.Rot.q(rt), Pobs(r)) == True{} : Bool})
  -> NC(s, P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt)):
  P.Pushed{+v, +obs2, at} = r
  h

# a refused move stops where the body is clear: what it reached was
# tested before anything was pushed, and a push moves nothing, it only
# hands out velocity
def xtouch_nc(touch: Bool, +rt: P.Rot, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +pr: Nat, +x: Nat, +y: Nat,
  +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool,
  et: {P.Move.xtouches(s, obs, d, cx, y, z, P.Rot.q(rt)) == touch : Bool},
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> NC(s, P.Move.xtouch(touch, s, obs, d, cx, pr, x, y, z, vx, vy, vz, gr, rt)):
  match touch:
    case True{}:
      xpushed_nc(rt, s, P.Push.x(s, obs, d, pr, y, z, vx, P.Rot.q(rt), P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs)), cx, y, z, vy, vz, gr,
        Equal.trans(Bool, P.Geo.free(s, cx, y, z, P.Rot.q(rt), Pobs(P.Push.x(s, obs, d, pr, y, z, vx, P.Rot.q(rt), P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs)))),
          P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), True{},
          push_x_free(P.Rot.q(rt), s, obs, d, pr, y, z, vx, P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs), cx, y, z),
          and_l(P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), Bool.not(P.Geo.free(s, P.Z.shift(cx, P.Z.like(d, 1n)), y, z, P.Rot.q(rt), obs)), et)))
    case False{}:
      xput_nc(rt, s, P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), obs, cx, x, y, z, vx, vy, vz, gr, True{}, {==}, h)

def xno_nc(+rt: P.Rot, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> NC(s, P.Move.xno(s, obs, d, cx, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})):
  xtouch_nc(P.Move.xtouches(s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), y, z, P.Rot.q(rt)), rt, s, obs, d,
    P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, {==}, h)

def xgo_nc(+rt: P.Rot, +s: Nat, ok: Bool, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, eok: {Bool.and(P.Z.fits(x, d), P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs)) == ok : Bool},
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> NC(s, P.Move.xgo(s, ok, obs, d, cx, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})):
  match ok:
    case True{}:
      and_r(P.Z.fits(x, d), P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), eok)
    case False{}:
      xno_nc(rt, s, obs, d, cx, x, y, z, vx, vy, vz, gr, hit, h)

def mx_nc(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body, h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs) == True{} : Bool})
  -> NC(s, P.Move.x(s, obs, v0, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  xgo_nc(rt, s, Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, P.Rot.q(rt), obs)), obs,
    P.Z.add(v0, vx), P.Z.shift(x, P.Z.add(v0, vx)), x, y, z, vx, vy, vz, gr, hit, {==}, h)

def zput_nc(+rt: P.Rot, +s: Nat, ok: Bool, +obs2: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z, +gr: Bool,
  +step: Bool, eok: {Bool.and(step, P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs2)) == ok : Bool},
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs2) == True{} : Bool})
  -> NC(s, P.Move.zput(ok, obs2, cz, x, y, z, vx, vy, v, gr, rt)):
  match ok:
    case True{}:
      and_r(step, P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs2), eok)
    case False{}:
      h

def zpushed_nc(+rt: P.Rot, +s: Nat, r: P.Pushed, +x: Nat, +y: Nat, +cz: Nat, +vx: P.Z, +vy: P.Z, +gr: Bool,
  h: {P.Geo.free(s, x, y, cz, P.Rot.q(rt), Pobs(r)) == True{} : Bool})
  -> NC(s, P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt)):
  P.Pushed{+v, +obs2, at} = r
  h

def ztouch_nc(touch: Bool, +rt: P.Rot, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +pr: Nat, +x: Nat, +y: Nat,
  +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool,
  et: {P.Move.ztouches(s, obs, d, x, y, cz, P.Rot.q(rt)) == touch : Bool},
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> NC(s, P.Move.ztouch(touch, s, obs, d, cz, pr, x, y, z, vx, vy, vz, gr, rt)):
  match touch:
    case True{}:
      zpushed_nc(rt, s, P.Push.z(s, obs, d, x, y, pr, vz, P.Rot.q(rt), P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs)), x, y, cz, vx, vy, gr,
        Equal.trans(Bool, P.Geo.free(s, x, y, cz, P.Rot.q(rt), Pobs(P.Push.z(s, obs, d, x, y, pr, vz, P.Rot.q(rt), P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs)))),
          P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), True{},
          push_z_free(P.Rot.q(rt), s, obs, d, x, y, pr, vz, P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs), x, y, cz),
          and_l(P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), Bool.not(P.Geo.free(s, x, y, P.Z.shift(cz, P.Z.like(d, 1n)), P.Rot.q(rt), obs)), et)))
    case False{}:
      zput_nc(rt, s, P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), obs, cz, x, y, z, vx, vy, vz, gr, True{}, {==}, h)

def zno_nc(+rt: P.Rot, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> NC(s, P.Move.zno(s, obs, d, cz, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})):
  ztouch_nc(P.Move.ztouches(s, obs, d, x, y, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Rot.q(rt)), rt, s, obs, d,
    P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
    x, y, z, vx, vy, vz, gr, {==}, h)

def zgo_nc(+rt: P.Rot, +s: Nat, ok: Bool, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, eok: {Bool.and(P.Z.fits(z, d), P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs)) == ok : Bool},
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> NC(s, P.Move.zgo(s, ok, obs, d, cz, P.Body{x,y,z,vx,vy,vz,gr,hit,rt})):
  match ok:
    case True{}:
      and_r(P.Z.fits(z, d), P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), eok)
    case False{}:
      zno_nc(rt, s, obs, d, cz, x, y, z, vx, vy, vz, gr, hit, h)

def mz_nc(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body, h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs) == True{} : Bool})
  -> NC(s, P.Move.z(s, obs, v0, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  zgo_nc(rt, s, Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), P.Rot.q(rt), obs)), obs,
    P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr, hit, {==}, h)

def rise_nc(+rt: P.Rot, +s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z, +hit: Bool,
  eok: {P.Geo.free(s, x, Nat.add(y, p), z, P.Rot.q(rt), obs) == ok : Bool}, h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.rise(ok, x, y, z, p, vx, v, vz, hit, rt)), P.Body.y(P.Move.rise(ok, x, y, z, p, vx, v, vz, hit, rt)),
        P.Body.z(P.Move.rise(ok, x, y, z, p, vx, v, vz, hit, rt)), P.Rot.q(P.Body.rot(P.Move.rise(ok, x, y, z, p, vx, v, vz, hit, rt))), obs) == True{} : Bool}:
  match ok:
    case True{}:
      eok
    case False{}:
      h

# landing: whatever else the tick asked before it (that the floor is
# below and within the step), what it asked last is that the body be
# clear where it lands -- and that is the half the law needs
def fits2_free(free: Bool, +s: Nat, +y: Nat, +q: P.Quat,
  e: {P.Tick.fits2(free, s, y, q) == True{} : Bool}) -> {free == True{} : Bool}:
  match free:
    case True{}:
      {==}
    case False{}:
      e

# where Tick.fits says yes, the body is clear of every cube
def fits_free(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat,
  e: {P.Tick.fits(s, obs, x, y, z, q) == True{} : Bool}) -> {P.Geo.free(s, x, y, z, q, obs) == True{} : Bool}:
  fits2_free(P.Geo.free(s, x, y, z, q, obs), s, y, q, e)

# a landing is taken only where the body fits, and a refused one leaves
# it where it was
def land_nc(+rt: P.Rot, +s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +ny: Nat, +vx: P.Z, +vz: P.Z,
  +v0: P.Z, eok: {P.Move.landok(s, obs, x, ny, z, P.Rot.q(rt)) == ok : Bool}, h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.land(ok, x, y, z, ny, vx, vz, v0, rt)), P.Body.y(P.Move.land(ok, x, y, z, ny, vx, vz, v0, rt)), P.Body.z(P.Move.land(ok, x, y, z, ny, vx, vz, v0, rt)), P.Rot.q(P.Body.rot(P.Move.land(ok, x, y, z, ny, vx, vz, v0, rt))), obs) == True{} : Bool}:
  match ok:
    case True{}:
      fits_free(s, obs, x, ny, z, P.Rot.q(rt), and_l(P.Tick.fits(s, obs, x, ny, z, P.Rot.q(rt)), Bool.not(P.Tick.sinks(s, obs, x, ny, z, P.Rot.q(rt))), eok))
    case False{}:
      h

def fall_nc(+rt: P.Rot, +s: Nat, ok: Bool, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +v0: P.Z, +hit: Bool, eok: {P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)) == ok : Bool},
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, hit, rt)), P.Body.y(P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, hit, rt)), P.Body.z(P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, hit, rt)), P.Rot.q(P.Body.rot(P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, hit, rt))), obs) == True{} : Bool}:
  match ok:
    case True{}:
      fits_free(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt),
        and_l(P.Tick.fits(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt)), P.Tick.path(64n, Nat.is_lt(s, q), s, obs, x, y, z, P.Rot.q(rt), q, s),
          and_r(Nat.is_le(q, y), Bool.and(P.Tick.fits(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt)),
            P.Tick.path(64n, Nat.is_lt(s, q), s, obs, x, y, z, P.Rot.q(rt), q, s)), eok)))
    case False{}:
      land_nc(rt, s, P.Move.landok(s, obs, x, P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), z, P.Rot.q(rt)), obs, x, y, z,
        P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), vx, vz, v0, {==}, h)

def fly_nc(+rt: P.Rot, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy0: P.Z, +vz: P.Z, +hit: Bool, st: P.Z & P.Z,
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.fly(s, obs, x, y, z, vx, vy0, vz, hit, st, rt)), P.Body.y(P.Move.fly(s, obs, x, y, z, vx, vy0, vz, hit, st, rt)), P.Body.z(P.Move.fly(s, obs, x, y, z, vx, vy0, vz, hit, st, rt)), P.Rot.q(P.Body.rot(P.Move.fly(s, obs, x, y, z, vx, vy0, vz, hit, st, rt))), obs) == True{} : Bool}:
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      rise_nc(rt, s, P.Geo.free(s, x, Nat.add(y, p), z, P.Rot.q(rt), obs), obs, x, y, z, p, vx, v, vz, hit, {==}, h)
    case P.Neg{+q}:
      fall_nc(rt, s, P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)), obs, x, y, z, q, vx, v, vz, vy0, hit, {==}, h)

# a hold from below only presses: it leaves the body where it is and
# turned as it was, and only the spin it carries changes
# a hold from below only presses: it leaves the body where it is and
# turned as it was, and only the spin it carries changes
def q_held(floor: Bool, +rt: P.Rot, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +j: Nat, obs: List<&2, P.Body>)
  -> {P.Rot.q(rt) == P.Rot.q(P.Rot.held(floor, rt, s, x, y, z, j, obs)) : P.Quat}:
  match floor:
    case True{}:
      {==}
    case False{}:
      {==}

def stay_nc(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot,
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt)),
       P.Body.y(P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt)),
       P.Body.z(P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt)),
       P.Rot.q(P.Body.rot(P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt))), obs) == True{} : Bool}:
  match rest:
    case True{}:
      %q_held(P.Geo.onfloor(s, y, P.Rot.q(rt)), rt, s, x, y, z, g, obs)
        : {P.Geo.free(s, x, y, z, _, obs) == True{} : Bool}
      h
    case False{}:
      h

def my_nc(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body, h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Move.y(s, g, obs, b)), P.Body.y(P.Move.y(s, g, obs, b)), P.Body.z(P.Move.y(s, g, obs, b)),
      P.Rot.q(P.Body.rot(P.Move.y(s, g, obs, b))), obs) == True{} : Bool}:
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  match gr:
    case True{}:
      stay_nc(P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs), s, g, obs, x, y, z, vx, vy, vz, hit, rt, h)
    case False{}:
      fly_nc(rt, s, obs, x, y, z, vx, vy, vz, hit, P.Fly.step(g, vy), h)

def ty_nc(+rt: P.Rot, +s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: NC(s, r)) -> NC(s, P.Tick.y(s, g, r)):
  (+b, +obs) = r
  my_nc(s, g, obs, b, h)

def tz_nc(+rt: P.Rot, +s: Nat, +g: Nat, +v0: P.Z, r: P.Body & List<&2, P.Body>, h: NC(s, r)) -> NC(s, P.Tick.z(s, g, v0, r)):
  (+b, +obs) = r
  ty_nc(rt, s, g, P.Move.z(s, obs, v0, b), mz_nc(s, obs, v0, b, h))

# driving moves nothing
def leap_nc(+rt: P.Rot, +s: Nat, jump: Bool, +k: P.K, +x: Nat, +y: Nat, +z: Nat, v: P.Z & P.Z, +obs: List<&2, P.Body>,
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Drive.leap(jump, k, x, y, z, v, rt)), P.Body.y(P.Drive.leap(jump, k, x, y, z, v, rt)),
        P.Body.z(P.Drive.leap(jump, k, x, y, z, v, rt)), P.Rot.q(P.Body.rot(P.Drive.leap(jump, k, x, y, z, v, rt))), obs) == True{} : Bool}:
  match jump:
    case True{}:
      P.K{g, mu, j, acc, s} = k
      (vx, vz) = v
      h
    case False{}:
      (vx, vz) = v
      h

def air_nc(+rt: P.Rot, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +obs: List<&2, P.Body>,
  h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Drive.air(x, y, z, vx, vy, vz, rt)), P.Body.y(P.Drive.air(x, y, z, vx, vy, vz, rt)),
        P.Body.z(P.Drive.air(x, y, z, vx, vy, vz, rt)), P.Rot.q(P.Body.rot(P.Drive.air(x, y, z, vx, vy, vz, rt))), obs) == True{} : Bool}:
  h

def drive_nc(+s: Nat, +g: Nat, +mu: Nat, +j: Nat, +acc: Nat, inp: P.In, b: P.Body, +obs: List<&2, P.Body>,
  h: {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Body.x(P.Body.drive(P.K{g, mu, j, acc, s}, inp, b)), P.Body.y(P.Body.drive(P.K{g, mu, j, acc, s}, inp, b)),
        P.Body.z(P.Body.drive(P.K{g, mu, j, acc, s}, inp, b)),
        P.Rot.q(P.Body.rot(P.Body.drive(P.K{g, mu, j, acc, s}, inp, b))), obs) == True{} : Bool}:
  P.In{+walk, jump} = inp
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  match gr:
    case True{}:
      leap_nc(rt, s, jump, P.K{g, mu, j, acc, s}, x, y, z,
        P.Motor.go(acc, walk, P.Share.fst(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz)),
          P.Share.snd(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz))), obs, h)
    case False{}:
      air_nc(rt, s, x, y, z, vx, vy, vz, obs, h)

def nclip(+rt: P.Rot, +g: Nat, +mu: Nat, +j: Nat, +acc: Nat, +s: Nat, +obs: List<&2, P.Body>, +inp: P.In,
  +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, clear: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> NC(s, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))):
  tz_nc(rt, s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})),
    mx_nc(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}),
      drive_nc(s, g, mu, j, acc, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, obs, clear)))

# Turning keeps the body clear
# ---------------------------
# However a cube turns -- free in the air, about the hold under it, or
# about the corner it stands on -- it ends in the same choice: the turn
# is taken only where the body fits turned the way it ends up (and only
# where it does not lift it), and refused otherwise, and a refused turn
# leaves the body exactly where it was. So one proof carries every way of
# turning: it is asked of Tick.put, and every other step hands it on.

def FREE(+s: Nat, +obs: List<&2, P.Body>, -b: P.Body) -> Type:
  {P.Geo.free(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs) == True{} : Bool}

# the clearing, back out of the answer Tick.fits gave
def put_nc(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  eok: {P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr) == ok : Bool},
  h: FREE(s, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FREE(s, obs, P.Tick.put(ok, s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  match ok:
    case True{}:
      fits_free(s, obs, nx, ny, nz, P.Rot.q(r2),
        and_l(P.Tick.fits(s, obs, nx, ny, nz, P.Rot.q(r2)), P.Tick.keeps(gr, s, obs, y, nx, ny, nz, P.Rot.q(r2)),
          and_r(Nat.is_le(ny, y), Bool.and(P.Tick.fits(s, obs, nx, ny, nz, P.Rot.q(r2)),
            P.Tick.keeps(gr, s, obs, y, nx, ny, nz, P.Rot.q(r2))), eok)))
    case False{}:
      h

def place_nc(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  h: FREE(s, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FREE(s, obs, P.Tick.place(s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  put_nc(P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr), s, g, obs, x, y, z, nx, ny, nz,
    vx, vy, vz, gr, hit, rt, r2, {==}, h)

def pivot_nc(m: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  h: FREE(s, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FREE(s, obs, P.Tick.pivot(m, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, rx, ry, rz)):
  P.Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = P.Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = P.Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = P.Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = P.Tick.drop(s, obs, nx, y, nz, P.Rot.q(r2), Nat.add(Nat.sub(y, P.Pick.low(ny, y)), Nat.div(s, 256n)))
  place_nc(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, hit, rt, r2, h)

def cand_nc(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> FREE(s, obs, P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  pivot_nc(P.Rot.mat(P.Quat.half(P.Quat.step(w, P.Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    P.Rot{P.Rot.turn(P.Rot.q(rt), w), P.Rot.w(rt)}, rx, ry, rz, h)

def shrink_nc.t1(+c: P.Body, +s: Nat, +obs: List<&2, P.Body>, +rt: P.Rot, hc1: FREE(s, obs, c))
  -> Once.Body(((kb: P.Body) => FREE((s), (obs), kb)), Body.of_pair((P.Tick.shrink.pair(c, rt)))):
  Once.Body.up((kb: P.Body) => FREE((s), (obs), kb), Body.of_pair((P.Tick.shrink.pair(c, rt))), Tick.shrink.pair_up((kb: P.Body) => FREE(s, obs, kb), c, rt, hc1))

def shrink_nc(n: Nat, p: P.Body & Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool},
  hb: Once.Body((kb: P.Body) => FREE(s, obs, kb), Body.of_pair(p)))
  -> Once.Body((kb: P.Body) => FREE(s, obs, kb), P.Tick.shrink(n, p, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  match n:
    case 0n:
      match p:
        case (b, ok):
          hb
    case 1n+m:
      match p:
        case (b, ok):
          match ok:
            case True{}:
              hb
            case False{}:
              shrink_nc(m, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, h, shrink_nc.t1(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), s, obs, rt, cand_nc(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, h)))

def start_nc(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> Once.Body((kb: P.Body) => FREE(s, obs, kb), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  shrink_nc(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, h, Once.Body.up((kb: P.Body) => FREE((s), (obs), kb), Body.of_pair((P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt))), Tick.shrink.pair_up((kb: P.Body) => FREE(s, obs, kb), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt, cand_nc(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, h))))

def keepw_nc(+tip: Bool, moved: Bool, +b: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool},
  hb: Once.Body((kb: P.Body) => FREE(s, obs, kb), b))
  -> Once.Body((kb: P.Body) => FREE(s, obs, kb), P.Body.spin(tip, moved, b, rt)):
  match moved:
    case True{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb
    case False{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb

def pivota0_nc.k1(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv,
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> Once.Body((kb: P.Body) => FREE(s, obs, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  P.Wv{+ax, +ay, +az} = a
  keepw_nc(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))), P.Tick.moved(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, h,
    start_nc(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az, h))

def pivota0_nc(+md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, +a: P.Wv,
  +h: {P.Geo.free(s, x, y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> FREE(s, obs, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  Once.Body.down((kb: P.Body) => FREE(s, obs, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a),
    pivota0_nc.k1(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a, h))

def pivota_nc(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv,
  h: FREE(s, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FREE(s, obs, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)):
  match obs:
    case []:
      pivota0_nc(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, h)
    case o <> rest:
      pivota0_nc(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, h)

def turn2_nc(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat,
  h: FREE(s, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FREE(s, obs, P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)):
  match held floor:
    case False{} _:
      place_nc(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2, h)
    case True{} False{}:
      pivota_nc(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s), h)
    case True{} True{}:
      pivota_nc(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s), h)

def turn1_nc(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  h: FREE(s, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))
  -> FREE(s, obs, P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})):
  match still:
    case True{}:
      h
    case False{}:
      turn2_nc(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy,
        vz, gr, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), h)

def turn_nc0(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, h: FREE(s, obs, b))
  -> FREE(s, obs, P.Tick.turn0(s, g, obs, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  turn1_nc(P.Wv.null(P.Rot.w(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, h)

def turn_nc(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, h: FREE(s, obs, b))
  -> FREE(s, obs, P.Tick.turn(s, g, obs, b)):
  %turn_sym(s, g, obs, b) : FREE(s, obs, _)
  turn_nc0(s, g, obs, b, h)

def spin_nc(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: NC(s, r)) -> NC(s, P.Tick.spin(s, g, r)):
  (+b, +obs) = r
  turn_nc(s, g, obs, b, h)

def Laws.spin_turns_the_body(k, obs, inp, b, spin, free):
  spin_q(P.K.size(k), P.K.g(k), P.Body.step(k, obs, inp, b), spin, free)

# the last two stages of the tick's linear part, opened once
def ticky_is(+s: Nat, +g: Nat, r2: P.Body & List<&2, P.Body>)
  -> {P.Tick.body(P.Tick.y(s, g, r2)) == P.Move.y(s, g, P.Tick.obs(r2), P.Tick.body(r2)) : P.Body}:
  (+b, +obs) = r2
  {==}

def tickz_is(+s: Nat, +g: Nat, +vz0: P.Z, r: P.Body & List<&2, P.Body>)
  -> {P.Tick.body(P.Tick.z(s, g, vz0, r))
      == P.Move.y(s, g, P.Tick.obs(P.Move.z(s, P.Tick.obs(r), vz0, P.Tick.body(r))),
           P.Tick.body(P.Move.z(s, P.Tick.obs(r), vz0, P.Tick.body(r)))) : P.Body}:
  (+b, +obs) = r
  ticky_is(s, g, P.Move.z(s, obs, vz0, b))

# the tick's linear part ends in the fall stage
def stepy_is(+k: P.K, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +q: Nat, +vz: P.Z,
  +hh: Bool, +rt: P.Rot)
  -> {P.Tick.body(P.Body.step(k, obs, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})) == P.Move.y(P.K.size(k), P.K.g(k), P.Tick.obs(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))), P.Tick.body(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))))) : P.Body}:
  tickz_is(P.K.size(k), P.K.g(k), vz,
    P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))

def step_fs(+k: P.K, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +q: Nat, +vz: P.Z,
  +hh: Bool, +rt: P.Rot, going: {Nat.is_lt(0n, q) == True{} : Bool})
  -> FS(P.Tick.body(P.Body.step(k, obs, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))):
  %Equal.sym(P.Body, P.Tick.body(P.Body.step(k, obs, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})), P.Move.y(P.K.size(k), P.K.g(k), P.Tick.obs(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))), P.Tick.body(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))))), stepy_is(k, obs, x, y, z, vx, q, vz, hh, rt)) : FS(_)
  my_fs(P.K.size(k), P.K.g(k), P.Tick.obs(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))), P.Tick.body(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))), q,
    Equal.trans(Bool, P.Body.ground(P.Tick.body(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))))), P.Body.ground(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), False{},
      same_g(P.Body.vy(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), P.Body.ground(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), P.Tick.body(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))),
        mz_same(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))),
      Equal.trans(Bool, P.Body.ground(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), P.Body.ground(P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})), False{},
        same_g(P.Body.vy(P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})), P.Body.ground(P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})), P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))),
          mx_same(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), {==})),
    Equal.trans(P.Z, P.Body.vy(P.Tick.body(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))))), P.Body.vy(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), P.Neg{q},
      same_v(P.Body.vy(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), P.Body.ground(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), P.Tick.body(P.Move.z(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))),
        mz_same(P.K.size(k), P.Tick.obs(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), vz, P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))))),
      Equal.trans(P.Z, P.Body.vy(P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})))), P.Body.vy(P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})), P.Neg{q},
        same_v(P.Body.vy(P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})), P.Body.ground(P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt})), P.Tick.body(P.Move.x(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))),
          mx_same(P.K.size(k), obs, vx, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, hh, rt}))), {==})),
    going)

def Laws.it_falls_or_it_stands(k, heavy, obs, x, y, z, vx, vz, q, going, h, rt):
  spin_fs(P.K.size(k), P.K.g(k), P.Body.step(k, obs, P.In.idle(), P.Body{x, y, z, vx, P.Neg{q}, vz, False{}, h, rt}),
    heavy, step_fs(k, obs, x, y, z, vx, q, vz, h, rt, going))

def Laws.no_clip(k, obs, inp, b, clear):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      spin_nc(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx,
          P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
        nclip(rt, g, mu, j, acc, s, obs, inp, x, y, z, vx, vy, vz, gr, hit, clear))

# Turning
# -------
# Rot.free hands back the same three rates and the angle plus the rate,
# which is the law word for word.

def Laws.free_spin_keeps_the_turning(r):
  match r:
    case P.Rot{+q, +w}:
      match w:
        case P.Wv{+x, +y, +z}:
          ({==}, {==}, {==})

# A hit adds the crossing to the turning, part by part: it is what
# Rot.hit is written to do, so each of the three comes out by itself.

def Laws.a_hit_adds_the_whole_turning(r, rx, ry, rz, jx, jy, jz):
  match r:
    case P.Rot{+q, +w}:
      match w:
        case P.Wv{+x, +y, +z}:
          ({==}, {==}, {==})

# An arm of zero: every product in the crossing is zero times something,
# and Nat.mul counts down its first number, so those fall out at once.

def Laws.no_spin_from_the_middle(jx, jy, jz):
  match jx jy jz:
    case P.Pos{+a} P.Pos{+b} P.Pos{+c}:
      ({==}, {==}, {==})
    case P.Pos{+a} P.Pos{+b} P.Neg{+c}:
      ({==}, {==}, {==})
    case P.Pos{+a} P.Neg{+b} P.Pos{+c}:
      ({==}, {==}, {==})
    case P.Pos{+a} P.Neg{+b} P.Neg{+c}:
      ({==}, {==}, {==})
    case P.Neg{+a} P.Pos{+b} P.Pos{+c}:
      ({==}, {==}, {==})
    case P.Neg{+a} P.Pos{+b} P.Neg{+c}:
      ({==}, {==}, {==})
    case P.Neg{+a} P.Neg{+b} P.Pos{+c}:
      ({==}, {==}, {==})
    case P.Neg{+a} P.Neg{+b} P.Neg{+c}:
      ({==}, {==}, {==})

# An arm and a push both along one axis. One of the two products in each
# crossing has the nothing on the left, where Nat.mul counts down and it
# falls out at once; the other has it on the right, and that one takes the
# induction below: anything times nothing is nothing.
def mul_zero(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def across_pp(+a: Nat, +b: Nat)
  -> {P.Z.mag(P.Rot.cry(P.Pos{0n}, P.Pos{a}, P.Pos{0n}, P.Pos{b})) == 0n : Nat}:
  %Equal.sym(Nat, Nat.mul(a, 0n), 0n, mul_zero(a))
    : {P.Z.mag(P.Z.add(P.Pos{Nat.mul(0n, b)}, P.Z.opp(P.Pos{_}))) == 0n : Nat}
  {==}

def across_pn(+a: Nat, +b: Nat)
  -> {P.Z.mag(P.Rot.cry(P.Pos{0n}, P.Pos{a}, P.Pos{0n}, P.Neg{b})) == 0n : Nat}:
  %Equal.sym(Nat, Nat.mul(a, 0n), 0n, mul_zero(a))
    : {P.Z.mag(P.Z.add(P.Neg{Nat.mul(0n, b)}, P.Z.opp(P.Pos{_}))) == 0n : Nat}
  {==}

def across_np(+a: Nat, +b: Nat)
  -> {P.Z.mag(P.Rot.cry(P.Pos{0n}, P.Neg{a}, P.Pos{0n}, P.Pos{b})) == 0n : Nat}:
  %Equal.sym(Nat, Nat.mul(a, 0n), 0n, mul_zero(a))
    : {P.Z.mag(P.Z.add(P.Pos{Nat.mul(0n, b)}, P.Z.opp(P.Neg{_}))) == 0n : Nat}
  {==}

def across_nn(+a: Nat, +b: Nat)
  -> {P.Z.mag(P.Rot.cry(P.Pos{0n}, P.Neg{a}, P.Pos{0n}, P.Neg{b})) == 0n : Nat}:
  %Equal.sym(Nat, Nat.mul(a, 0n), 0n, mul_zero(a))
    : {P.Z.mag(P.Z.add(P.Neg{Nat.mul(0n, b)}, P.Z.opp(P.Neg{_}))) == 0n : Nat}
  {==}

def Laws.spin_is_across_the_push(rx, jx):
  match rx jx:
    case P.Pos{+a} P.Pos{+b}:
      ({==}, across_pp(a, b))
    case P.Pos{+a} P.Neg{+b}:
      ({==}, across_pn(a, b))
    case P.Neg{+a} P.Pos{+b}:
      ({==}, across_np(a, b))
    case P.Neg{+a} P.Neg{+b}:
      ({==}, across_nn(a, b))

# Nothing goes into the floor
# ---------------------------
# A body's lowest point is y - sag. Every move that changes where a body
# is, or how it is turned, is gated by Tick.fits, and Tick.fits asks for
# exactly sag <= y; a move that is not gated by it changes neither y nor
# the turn, or only raises y. So a body that starts above the floor ends
# every stage of the tick above it.

def FL(+s: Nat, -b: P.Body) -> Type:
  {Nat.is_le(P.Geo.sag(s, P.Rot.q(P.Body.rot(b))), P.Body.y(b)) == True{} : Bool}

def fits2_sag(free: Bool, +s: Nat, +y: Nat, +q: P.Quat, e: {P.Tick.fits2(free, s, y, q) == True{} : Bool})
  -> {Nat.is_le(P.Geo.sag(s, q), y) == True{} : Bool}:
  match free:
    case True{}:
      e
    case False{}:
      Empty.absurd({Nat.is_le(P.Geo.sag(s, q), y) == True{} : Bool}, clash2(e))

# where Tick.fits says yes, the body's lowest point is above the floor
def fits_sag(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat,
  e: {P.Tick.fits(s, obs, x, y, z, q) == True{} : Bool}) -> {Nat.is_le(P.Geo.sag(s, q), y) == True{} : Bool}:
  fits2_sag(P.Geo.free(s, x, y, z, q, obs), s, y, q, e)

def leap_fl(+rt: P.Rot, +s: Nat, jump: Bool, +k: P.K, +x: Nat, +y: Nat, +z: Nat, v: P.Z & P.Z, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Drive.leap(jump, k, x, y, z, v, rt)):
  match jump:
    case True{}:
      P.K{g, mu, j, acc, sz} = k
      (vx, vz) = v
      h
    case False{}:
      (vx, vz) = v
      h

def drive_fl(+s: Nat, +g: Nat, +mu: Nat, +j: Nat, +acc: Nat, inp: P.In, b: P.Body, h: FL(s, b))
  -> FL(s, P.Body.drive(P.K{g, mu, j, acc, s}, inp, b)):
  P.In{+walk, jump} = inp
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  match gr:
    case True{}:
      leap_fl(rt, s, jump, P.K{g, mu, j, acc, s}, x, y, z,
        P.Motor.go(acc, walk, P.Share.fst(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz)),
          P.Share.snd(P.Fric.apply(Nat.div(Nat.mul(mu, g), 256n), vx, vz))), h)
    case False{}:
      h

def xput_fl(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool}) -> FL(s, P.Tick.body(P.Move.xput(ok, obs, cx, x, y, z, v, vy, vz, gr, rt))):
  match ok:
    case True{}:
      h
    case False{}:
      h

def xpushed_fl(r: P.Pushed, +s: Nat, +cx: Nat, +y: Nat, +z: Nat, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.body(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt))):
  P.Pushed{+v, +obs, at} = r
  h

def xtouch_fl(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.body(P.Move.xtouch(touch, s, obs, d, cx, pr, x, y, z, vx, vy, vz, gr, rt))):
  match touch:
    case True{}:
      xpushed_fl(P.Push.x(s, obs, d, pr, y, z, vx, P.Rot.q(rt), P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs)), s, cx, y, z, vy, vz, gr, rt, h)
    case False{}:
      xput_fl(P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), s, obs, cx, x, y, z, vx, vy, vz, gr, rt, h)

def xgo_fl(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.body(P.Move.xgo(s, ok, obs, d, cx, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))):
  match ok:
    case True{}:
      h
    case False{}:
      xtouch_fl(P.Move.xtouches(s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), y, z, P.Rot.q(rt)), s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
        x, y, z, vx, vy, vz, gr, rt, h)

def mx_fl(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body, h: FL(s, b)) -> FL(s, P.Tick.body(P.Move.x(s, obs, v0, b))):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  xgo_fl(Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, P.Rot.q(rt), obs)), s, obs,
    P.Z.add(v0, vx), P.Z.shift(x, P.Z.add(v0, vx)), x, y, z, vx, vy, vz, gr, hit, rt, h)

def zput_fl(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z,
  +gr: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool}) -> FL(s, P.Tick.body(P.Move.zput(ok, obs, cz, x, y, z, vx, vy, v, gr, rt))):
  match ok:
    case True{}:
      h
    case False{}:
      h

def zpushed_fl(r: P.Pushed, +s: Nat, +x: Nat, +y: Nat, +cz: Nat, +vx: P.Z, +vy: P.Z, +gr: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.body(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt))):
  P.Pushed{+v, +obs, at} = r
  h

def ztouch_fl(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.body(P.Move.ztouch(touch, s, obs, d, cz, pr, x, y, z, vx, vy, vz, gr, rt))):
  match touch:
    case True{}:
      zpushed_fl(P.Push.z(s, obs, d, x, y, pr, vz, P.Rot.q(rt), P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs)), s, x, y, cz, vx, vy, gr, rt, h)
    case False{}:
      zput_fl(P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), s, obs, cz, x, y, z, vx, vy, vz, gr, rt, h)

def zgo_fl(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.body(P.Move.zgo(s, ok, obs, d, cz, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))):
  match ok:
    case True{}:
      h
    case False{}:
      ztouch_fl(P.Move.ztouches(s, obs, d, x, y, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Rot.q(rt)), s, obs, d, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.shift(P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Z.like(d, 1n)),
        x, y, z, vx, vy, vz, gr, rt, h)

def mz_fl(+s: Nat, +obs: List<&2, P.Body>, +v0: P.Z, b: P.Body, h: FL(s, b)) -> FL(s, P.Tick.body(P.Move.z(s, obs, v0, b))):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  zgo_fl(Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), P.Rot.q(rt), obs)), s, obs,
    P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr, hit, rt, h)

def rise_fl(ok: Bool, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z, +hit: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Move.rise(ok, x, y, z, p, vx, v, vz, hit, rt)):
  match ok:
    case True{}:
      le_trans(P.Geo.sag(s, P.Rot.q(rt)), y, Nat.add(y, p), h, le_add(y, p))
    case False{}:
      h

def land_fl(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +ny: Nat, +vx: P.Z, +vz: P.Z, +v0: P.Z,
  +rt: P.Rot, eok: {P.Move.landok(s, obs, x, ny, z, P.Rot.q(rt)) == ok : Bool}, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Move.land(ok, x, y, z, ny, vx, vz, v0, rt)):
  match ok:
    case True{}:
      fits_sag(s, obs, x, ny, z, P.Rot.q(rt), and_l(P.Tick.fits(s, obs, x, ny, z, P.Rot.q(rt)), Bool.not(P.Tick.sinks(s, obs, x, ny, z, P.Rot.q(rt))), eok))
    case False{}:
      h

def fall_fl(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +v0: P.Z, +hit: Bool, +rt: P.Rot, eok: {P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)) == ok : Bool}, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, hit, rt)):
  match ok:
    case True{}:
      fits_sag(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt),
        and_l(P.Tick.fits(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt)), P.Tick.path(64n, Nat.is_lt(s, q), s, obs, x, y, z, P.Rot.q(rt), q, s),
          and_r(Nat.is_le(q, y), Bool.and(P.Tick.fits(s, obs, x, Nat.sub(y, q), z, P.Rot.q(rt)),
            P.Tick.path(64n, Nat.is_lt(s, q), s, obs, x, y, z, P.Rot.q(rt), q, s)), eok)))
    case False{}:
      land_fl(P.Move.landok(s, obs, x, P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), z, P.Rot.q(rt)), s, obs, x, y, z,
        P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), vx, vz, v0, rt, {==}, h)

def fly_fl(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy0: P.Z, +vz: P.Z, +hit: Bool,
  st: P.Z & P.Z, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool}) -> FL(s, P.Move.fly(s, obs, x, y, z, vx, vy0, vz, hit, st, rt)):
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      rise_fl(P.Geo.free(s, x, Nat.add(y, p), z, P.Rot.q(rt), obs), s, x, y, z, p, vx, v, vz, hit, rt, h)
    case P.Neg{+q}:
      fall_fl(P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)), s, obs, x, y, z, q, vx, v, vz, vy0, hit, rt, {==}, h)

def stay_fl(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool}) -> FL(s, P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt)):
  match rest:
    case True{}:
      %q_held(P.Geo.onfloor(s, y, P.Rot.q(rt)), rt, s, x, y, z, g, obs) : {Nat.is_le(P.Geo.sag(s, _), y) == True{} : Bool}
      h
    case False{}:
      h

def my_fl(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body, h: FL(s, b)) -> FL(s, P.Move.y(s, g, obs, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  match gr:
    case True{}:
      stay_fl(P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs), s, g, obs, x, y, z, vx, vy, vz, hit, rt, h)
    case False{}:
      fly_fl(s, obs, x, y, z, vx, vy, vz, hit, P.Fly.step(g, vy), rt, h)

def ty_fl(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: FL(s, P.Tick.body(r))) -> FL(s, P.Tick.body(P.Tick.y(s, g, r))):
  (+b, +obs) = r
  my_fl(s, g, obs, b, h)

def tz_fl(+s: Nat, +g: Nat, +v0: P.Z, r: P.Body & List<&2, P.Body>, h: FL(s, P.Tick.body(r)))
  -> FL(s, P.Tick.body(P.Tick.z(s, g, v0, r))):
  (+b, +obs) = r
  ty_fl(s, g, P.Move.z(s, obs, v0, b), mz_fl(s, obs, v0, b, h))

def put_fl(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot,
  eok: {P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr) == ok : Bool}, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.put(ok, s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  match ok:
    case True{}:
      fits_sag(s, obs, nx, ny, nz, P.Rot.q(r2),
        and_l(P.Tick.fits(s, obs, nx, ny, nz, P.Rot.q(r2)), P.Tick.keeps(gr, s, obs, y, nx, ny, nz, P.Rot.q(r2)),
          and_r(Nat.is_le(ny, y), Bool.and(P.Tick.fits(s, obs, nx, ny, nz, P.Rot.q(r2)),
            P.Tick.keeps(gr, s, obs, y, nx, ny, nz, P.Rot.q(r2))), eok)))
    case False{}:
      h

def place_fl(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.place(s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  put_fl(P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr), s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2,
    {==}, h)

def pivot_fl(m: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +rx: P.Z, +ry: P.Z, +rz: P.Z, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.pivot(m, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, rx, ry, rz)):
  P.Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = P.Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = P.Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = P.Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = P.Tick.drop(s, obs, nx, y, nz, P.Rot.q(r2), Nat.add(Nat.sub(y, P.Pick.low(ny, y)), Nat.div(s, 256n)))
  place_fl(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, hit, rt, r2, h)

def cand_fl(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  pivot_fl(P.Rot.mat(P.Quat.half(P.Quat.step(w, P.Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    P.Rot{P.Rot.turn(P.Rot.q(rt), w), P.Rot.w(rt)}, rx, ry, rz, h)

def shrink_fl(n: Nat, p: P.Body & Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool},
  hb: FL(s, Body.of_pair(p)))
  -> FL(s, P.Tick.shrink(n, p, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  match n:
    case 0n:
      match p:
        case (b, ok):
          hb
    case 1n+m:
      match p:
        case (b, ok):
          match ok:
            case True{}:
              hb
            case False{}:
              shrink_fl(m, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, h, Tick.shrink.pair_up((kb: P.Body) => FL(s, kb), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt, cand_fl(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, h)))

def start_fl(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  shrink_fl(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, h, Tick.shrink.pair_up((kb: P.Body) => FL(s, kb), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt, cand_fl(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, h)))

def keepw_fl(+tip: Bool, moved: Bool, +b: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  +h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool},
  hb: Once.Body((kb: P.Body) => FL(s, kb), b))
  -> Once.Body((kb: P.Body) => FL(s, kb), P.Body.spin(tip, moved, b, rt)):
  match moved:
    case True{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb
    case False{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb

def pivota0_fl.k1(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv, +h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> Once.Body((kb: P.Body) => FL(s, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  P.Wv{+ax, +ay, +az} = a
  keepw_fl(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))), P.Tick.moved(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, h, Once.Body.up((kb: P.Body) => FL((s), kb), (P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az)), start_fl(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az, h)))

def pivota0_fl(+md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, +a: P.Wv, +h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  Once.Body.down((kb: P.Body) => FL(s, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a),
    pivota0_fl.k1(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a, h))

def pivota_fl(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)):
  match obs:
    case []:
      pivota0_fl(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, h)
    case o <> rest:
      pivota0_fl(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, h)

def turn2_fl(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)):
  match held floor:
    case False{} _:
      place_fl(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2, h)
    case True{} False{}:
      pivota_fl(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s), h)
    case True{} True{}:
      pivota_fl(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s), h)

def turn1_fl(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, h: {Nat.is_le(P.Geo.sag(s, P.Rot.q(rt)), y) == True{} : Bool})
  -> FL(s, P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})):
  match still:
    case True{}:
      h
    case False{}:
      turn2_fl(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), h)

def turn_fl0(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, h: FL(s, b)) -> FL(s, P.Tick.turn0(s, g, obs, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  turn1_fl(P.Wv.null(P.Rot.w(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, h)

def turn_fl(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, h: FL(s, b)) -> FL(s, P.Tick.turn(s, g, obs, b)):
  %turn_sym(s, g, obs, b) : FL(s, _)
  turn_fl0(s, g, obs, b, h)

def spin_fl(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: FL(s, P.Tick.body(r)))
  -> FL(s, P.Tick.body(P.Tick.spin(s, g, r))):
  (+b, +obs) = r
  turn_fl(s, g, obs, b, h)

def Laws.never_under_the_floor(k, obs, inp, b, above):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      spin_fl(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp,
          P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
        tz_fl(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})),
          mx_fl(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}),
            drive_fl(s, g, mu, j, acc, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}, above))))

# Nothing floats
# --------------
# A body ends a tick standing only where it is held: the vertical move
# stands it only after asking Tick.sinks, a landing only after asking it
# where it lands, and a turn that moves a standing body asks it again
# where the body ends up -- the very question the law asks. Nothing else
# ever stands a body up.

def SH(+s: Nat, +obs: List<&2, P.Body>, -b: P.Body) -> Type:
  {Bool.and(P.Body.ground(b), P.Tick.sinks(s, obs, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)))) == False{} : Bool}

def and_not_self(b: Bool) -> {Bool.and(Bool.not(b), b) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def stay_sh(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +hit: Bool, +rt: P.Rot, e: {Bool.not(P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == rest : Bool})
  -> SH(s, obs, P.Move.stay(rest, s, g, obs, x, y, z, vx, vy, vz, hit, rt)):
  match rest:
    case True{}:
      %q_held(P.Geo.onfloor(s, y, P.Rot.q(rt)), rt, s, x, y, z, g, obs)
        : {Bool.and(True{}, P.Tick.sinks(s, obs, x, y, z, _)) == False{} : Bool}
      not_t(P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt)), e)
    case False{}:
      {==}

def land_sh(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +ny: Nat, +vx: P.Z, +vz: P.Z, +v0: P.Z,
  +rt: P.Rot, eok: {P.Move.landok(s, obs, x, ny, z, P.Rot.q(rt)) == ok : Bool})
  -> SH(s, obs, P.Move.land(ok, x, y, z, ny, vx, vz, v0, rt)):
  match ok:
    case True{}:
      not_t(P.Tick.sinks(s, obs, x, ny, z, P.Rot.q(rt)), and_r(P.Tick.fits(s, obs, x, ny, z, P.Rot.q(rt)), Bool.not(P.Tick.sinks(s, obs, x, ny, z, P.Rot.q(rt))), eok))
    case False{}:
      {==}

def fall_sh(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +v0: P.Z, +hit: Bool, +rt: P.Rot) -> SH(s, obs, P.Move.fall(s, ok, obs, x, y, z, q, vx, v, vz, v0, hit, rt)):
  match ok:
    case True{}:
      {==}
    case False{}:
      land_sh(P.Move.landok(s, obs, x, P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), z, P.Rot.q(rt)), s, obs, x, y, z,
        P.Move.landy(s, obs, x, y, z, P.Rot.q(rt), q), vx, vz, v0, rt, {==})

def rise_sh(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: P.Z, +v: P.Z, +vz: P.Z,
  +hit: Bool, +rt: P.Rot) -> SH(s, obs, P.Move.rise(ok, x, y, z, p, vx, v, vz, hit, rt)):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def fly_sh(+s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy0: P.Z, +vz: P.Z, +hit: Bool,
  st: P.Z & P.Z, +rt: P.Rot) -> SH(s, obs, P.Move.fly(s, obs, x, y, z, vx, vy0, vz, hit, st, rt)):
  (+v, d) = st
  match d:
    case P.Pos{+p}:
      rise_sh(P.Geo.free(s, x, Nat.add(y, p), z, P.Rot.q(rt), obs), s, obs, x, y, z, p, vx, v, vz, hit, rt)
    case P.Neg{+q}:
      fall_sh(P.Move.fallok(s, obs, x, y, z, q, P.Rot.q(rt)), s, obs, x, y, z, q, vx, v, vz, vy0, hit, rt)

def my_sh(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body) -> SH(s, obs, P.Move.y(s, g, obs, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  match gr:
    case True{}:
      stay_sh(P.Geo.held(P.Quat.flat(P.Rot.q(rt)), s, x, y, z, P.Rot.q(rt), obs), s, g, obs, x, y, z, vx, vy, vz, hit, rt, {==})
    case False{}:
      fly_sh(s, obs, x, y, z, vx, vy, vz, hit, P.Fly.step(g, vy), rt)

def ty_sh(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>)
  -> SH(s, P.Tick.obs(P.Tick.y(s, g, r)), P.Tick.body(P.Tick.y(s, g, r))):
  (+b, +obs) = r
  my_sh(s, g, obs, b)

def tz_sh(+s: Nat, +g: Nat, +v0: P.Z, r: P.Body & List<&2, P.Body>)
  -> SH(s, P.Tick.obs(P.Tick.z(s, g, v0, r)), P.Tick.body(P.Tick.z(s, g, v0, r))):
  (+b, +obs) = r
  ty_sh(s, g, P.Move.z(s, obs, v0, b))

def stands_sh(gr: Bool, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat)
  -> {Bool.and(P.Tick.stands(gr, s, obs, x, y, z, q), P.Tick.sinks(s, obs, x, y, z, q)) == False{} : Bool}:
  match gr:
    case True{}:
      and_not_self(P.Tick.sinks(s, obs, x, y, z, q))
    case False{}:
      {==}

def put_sh(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.put(ok, s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  match ok:
    case True{}:
      stands_sh(gr, s, obs, nx, ny, nz, P.Rot.q(r2))
    case False{}:
      h

def place_sh(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.place(s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  put_sh(P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr), s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2, h)

def pivot_sh(m: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +rx: P.Z, +ry: P.Z, +rz: P.Z, h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.pivot(m, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, rx, ry, rz)):
  P.Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = P.Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = P.Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = P.Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = P.Tick.drop(s, obs, nx, y, nz, P.Rot.q(r2), Nat.add(Nat.sub(y, P.Pick.low(ny, y)), Nat.div(s, 256n)))
  place_sh(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, hit, rt, r2, h)

def cand_sh(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  pivot_sh(P.Rot.mat(P.Quat.half(P.Quat.step(w, P.Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    P.Rot{P.Rot.turn(P.Rot.q(rt), w), P.Rot.w(rt)}, rx, ry, rz, h)

def shrink_sh.t1(+c: P.Body, +s: Nat, +obs: List<&2, P.Body>, +rt: P.Rot, hc1: SH(s, obs, c))
  -> Once.Body(((kb: P.Body) => SH((s), (obs), kb)), Body.of_pair((P.Tick.shrink.pair(c, rt)))):
  Once.Body.up((kb: P.Body) => SH((s), (obs), kb), Body.of_pair((P.Tick.shrink.pair(c, rt))), Tick.shrink.pair_up((kb: P.Body) => SH(s, obs, kb), c, rt, hc1))

def shrink_sh(n: Nat, p: P.Body & Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool},
  hb: Once.Body((kb: P.Body) => SH(s, obs, kb), Body.of_pair(p)))
  -> Once.Body((kb: P.Body) => SH(s, obs, kb), P.Tick.shrink(n, p, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  match n:
    case 0n:
      match p:
        case (b, ok):
          hb
    case 1n+m:
      match p:
        case (b, ok):
          match ok:
            case True{}:
              hb
            case False{}:
              shrink_sh(m, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, h, shrink_sh.t1(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), s, obs, rt, cand_sh(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, h)))

def start_sh.t1(+c: P.Body, +s: Nat, +obs: List<&2, P.Body>, +rt: P.Rot, hc1: SH(s, obs, c))
  -> Once.Body(((kb: P.Body) => SH((s), (obs), kb)), Body.of_pair((P.Tick.shrink.pair(c, rt)))):
  Once.Body.up((kb: P.Body) => SH((s), (obs), kb), Body.of_pair((P.Tick.shrink.pair(c, rt))), Tick.shrink.pair_up((kb: P.Body) => SH(s, obs, kb), c, rt, hc1))

def start_sh.t2(+c: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z, +h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool}, hc1: SH(s, obs, c))
  -> Once.Body((kb: P.Body) => SH(s, obs, kb), P.Tick.shrink(7n, P.Tick.shrink.pair(c, rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  shrink_sh(7n, P.Tick.shrink.pair(c, rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, h, start_sh.t1(c, s, obs, rt, hc1))

def start_sh(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z,
  +h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> Once.Body((kb: P.Body) => SH(s, obs, kb), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  start_sh.t2(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, h, cand_sh(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, h))

def keepw_sh(+tip: Bool, moved: Bool, +b: P.Body, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  +h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool},
  hb: Once.Body((kb: P.Body) => SH(s, obs, kb), b))
  -> Once.Body((kb: P.Body) => SH(s, obs, kb), P.Body.spin(tip, moved, b, rt)):
  match moved:
    case True{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb
    case False{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          hb

def pivota0_sh.k1(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv, +h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> Once.Body((kb: P.Body) => SH(s, obs, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  P.Wv{+ax, +ay, +az} = a
  keepw_sh(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))), P.Tick.moved(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, h,
    start_sh(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az, h))

def pivota0_sh(+md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, +a: P.Wv, +h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  Once.Body.down((kb: P.Body) => SH(s, obs, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a),
    pivota0_sh.k1(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a, h))

def pivota_sh(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv, h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)):
  match obs:
    case []:
      pivota0_sh(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, h)
    case o <> rest:
      pivota0_sh(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, h)

def turn2_sh(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat, h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)):
  match held floor:
    case False{} _:
      place_sh(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2, h)
    case True{} False{}:
      pivota_sh(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s), h)
    case True{} True{}:
      pivota_sh(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s), h)

def turn1_sh(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, h: {Bool.and(gr, P.Tick.sinks(s, obs, x, y, z, P.Rot.q(rt))) == False{} : Bool})
  -> SH(s, obs, P.Tick.turn1(still, s, g, obs, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})):
  match still:
    case True{}:
      h
    case False{}:
      turn2_sh(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Rot.free(rt),
        P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), h)

def turn_sh0(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, h: SH(s, obs, b)) -> SH(s, obs, P.Tick.turn0(s, g, obs, b)):
  P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  turn1_sh(P.Wv.null(P.Rot.w(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, h)

def turn_sh(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, h: SH(s, obs, b)) -> SH(s, obs, P.Tick.turn(s, g, obs, b)):
  %turn_sym(s, g, obs, b) : SH(s, obs, _)
  turn_sh0(s, g, obs, b, h)

def spin_sh(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, h: SH(s, P.Tick.obs(r), P.Tick.body(r)))
  -> SH(s, P.Tick.obs(P.Tick.spin(s, g, r)), P.Tick.body(P.Tick.spin(s, g, r))):
  (+b, +obs) = r
  turn_sh(s, g, obs, b, h)

# standing, and not both standing and able to sink: not able to sink
def sh_use(gg: Bool, -sk: Bool, h: {Bool.and(gg, sk) == False{} : Bool}, st: {gg == True{} : Bool}) -> {sk == False{} : Bool}:
  match gg:
    case True{}:
      h
    case False{}:
      Empty.absurd({sk == False{} : Bool}, clash2(st))

def Laws.standing_is_held(k, obs, inp, b, stands):
  match k b:
    case P.K{+g, +mu, +j, +acc, +s} P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      sh_use(P.Body.ground(P.Tick.body(P.Tick.spin(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))))),
        P.Tick.sinks(s, P.Tick.obs(P.Tick.spin(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))))), P.Body.x(P.Tick.body(P.Tick.spin(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))))), P.Body.y(P.Tick.body(P.Tick.spin(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))))), P.Body.z(P.Tick.body(P.Tick.spin(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))))),
          P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))))))),
        spin_sh(s, g, P.Tick.z(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))), tz_sh(s, g, vz, P.Move.x(s, obs, vx, P.Body.drive(P.K{g, mu, j, acc, s}, inp, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})))), stands)

# A push is a touch
# -----------------
# A refused move pushes only down the branch that asked, where the body
# stopped, whether it is touching something one unit on. The law hands
# in that it is not: that branch is then impossible, and every other
# branch hands the obstacles back as they came.

def xput_obs(ok: Bool, +obs: List<&2, P.Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool,
  +rt: P.Rot) -> {P.Tick.obs(P.Move.xput(ok, obs, cx, x, y, z, v, vy, vz, gr, rt)) == obs : List<&2, P.Body>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def xpushed_x(r: P.Pushed, +cx: Nat, +y: Nat, +z: Nat, +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.x(P.Tick.body(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt))) == cx : Nat}:
  P.Pushed{+v, +obs, at} = r
  {==}

def free_at(-X: Nat, +cx: Nat, +l: P.Z, +s: Nat, +y: Nat, +z: Nat, +q: P.Quat, +obs: List<&2, P.Body>,
  e: {X == cx : Nat}, h: {P.Geo.free(s, P.Z.shift(X, l), y, z, q, obs) == True{} : Bool})
  -> {P.Geo.free(s, P.Z.shift(cx, l), y, z, q, obs) == True{} : Bool}:
  %e : {P.Geo.free(s, P.Z.shift(_, l), y, z, q, obs) == True{} : Bool}
  h

def xtouch_obs(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot,
  et: {P.Move.xtouches(s, obs, d, cx, y, z, P.Rot.q(rt)) == touch : Bool},
  room: {P.Geo.free(s, P.Z.shift(P.Body.x(P.Tick.body(P.Move.xtouch(touch, s, obs, d, cx, P.Z.shift(cx, P.Z.like(d, 1n)), x, y, z,
    vx, vy, vz, gr, rt))), P.Z.like(d, 1n)), y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Tick.obs(P.Move.xtouch(touch, s, obs, d, cx, P.Z.shift(cx, P.Z.like(d, 1n)), x, y, z, vx, vy, vz, gr, rt))
      == obs : List<&2, P.Body>}:
  match touch:
    case True{}:
      +pr = P.Z.shift(cx, P.Z.like(d, 1n))
      +r = P.Push.x(s, obs, d, pr, y, z, vx, P.Rot.q(rt), P.Geo.head(s, pr, y, z, P.Rot.q(rt), obs))
      Empty.absurd({P.Tick.obs(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt)) == obs : List<&2, P.Body>},
        clash(Equal.trans(Bool, True{}, P.Geo.free(s, pr, y, z, P.Rot.q(rt), obs), False{},
          Equal.sym(Bool, P.Geo.free(s, pr, y, z, P.Rot.q(rt), obs), True{},
            free_at(P.Body.x(P.Tick.body(P.Move.xpushed(r, cx, y, z, vy, vz, gr, rt))), cx, P.Z.like(d, 1n), s, y, z, P.Rot.q(rt), obs,
              xpushed_x(r, cx, y, z, vy, vz, gr, rt), room)),
          not_t(P.Geo.free(s, pr, y, z, P.Rot.q(rt), obs),
            and_r(P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), Bool.not(P.Geo.free(s, pr, y, z, P.Rot.q(rt), obs)), et)))))
    case False{}:
      xput_obs(P.Geo.free(s, cx, y, z, P.Rot.q(rt), obs), obs, cx, x, y, z, vx, vy, vz, gr, rt)

def xgo_obs(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  room: {P.Geo.free(s, P.Z.shift(P.Body.x(P.Tick.body(P.Move.xgo(s, ok, obs, d, cx, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
    P.Z.like(d, 1n)), y, z, P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Tick.obs(P.Move.xgo(s, ok, obs, d, cx, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == obs : List<&2, P.Body>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      xtouch_obs(P.Move.xtouches(s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), y, z, P.Rot.q(rt)), s, obs, d, P.Move.xto(s, obs, d, x, y, z, P.Rot.q(rt)), x, y, z, vx, vy, vz, gr, rt, {==}, room)

def Laws.a_push_is_a_touch_x(s, obs, v0, b, room):
  match b:
    case P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      xgo_obs(Bool.and(P.Z.fits(x, P.Z.add(v0, vx)), P.Geo.free(s, P.Z.shift(x, P.Z.add(v0, vx)), y, z, P.Rot.q(rt), obs)), s, obs,
        P.Z.add(v0, vx), P.Z.shift(x, P.Z.add(v0, vx)), x, y, z, vx, vy, vz, gr, hit, rt, room)

def zput_obs(ok: Bool, +obs: List<&2, P.Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +v: P.Z, +gr: Bool,
  +rt: P.Rot) -> {P.Tick.obs(P.Move.zput(ok, obs, cz, x, y, z, vx, vy, v, gr, rt)) == obs : List<&2, P.Body>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def zpushed_z(r: P.Pushed, +x: Nat, +y: Nat, +cz: Nat, +vx: P.Z, +vy: P.Z, +gr: Bool, +rt: P.Rot)
  -> {P.Body.z(P.Tick.body(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt))) == cz : Nat}:
  P.Pushed{+v, +obs, at} = r
  {==}

def free_atz(-Zz: Nat, +cz: Nat, +l: P.Z, +s: Nat, +x: Nat, +y: Nat, +q: P.Quat, +obs: List<&2, P.Body>,
  e: {Zz == cz : Nat}, h: {P.Geo.free(s, x, y, P.Z.shift(Zz, l), q, obs) == True{} : Bool})
  -> {P.Geo.free(s, x, y, P.Z.shift(cz, l), q, obs) == True{} : Bool}:
  %e : {P.Geo.free(s, x, y, P.Z.shift(_, l), q, obs) == True{} : Bool}
  h

def ztouch_obs(touch: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z,
  +vy: P.Z, +vz: P.Z, +gr: Bool, +rt: P.Rot,
  et: {P.Move.ztouches(s, obs, d, x, y, cz, P.Rot.q(rt)) == touch : Bool},
  room: {P.Geo.free(s, x, y, P.Z.shift(P.Body.z(P.Tick.body(P.Move.ztouch(touch, s, obs, d, cz, P.Z.shift(cz, P.Z.like(d, 1n)), x, y, z,
    vx, vy, vz, gr, rt))), P.Z.like(d, 1n)), P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Tick.obs(P.Move.ztouch(touch, s, obs, d, cz, P.Z.shift(cz, P.Z.like(d, 1n)), x, y, z, vx, vy, vz, gr, rt))
      == obs : List<&2, P.Body>}:
  match touch:
    case True{}:
      +pr = P.Z.shift(cz, P.Z.like(d, 1n))
      +r = P.Push.z(s, obs, d, x, y, pr, vz, P.Rot.q(rt), P.Geo.head(s, x, y, pr, P.Rot.q(rt), obs))
      Empty.absurd({P.Tick.obs(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt)) == obs : List<&2, P.Body>},
        clash(Equal.trans(Bool, True{}, P.Geo.free(s, x, y, pr, P.Rot.q(rt), obs), False{},
          Equal.sym(Bool, P.Geo.free(s, x, y, pr, P.Rot.q(rt), obs), True{},
            free_atz(P.Body.z(P.Tick.body(P.Move.zpushed(r, x, y, cz, vx, vy, gr, rt))), cz, P.Z.like(d, 1n), s, x, y, P.Rot.q(rt), obs,
              zpushed_z(r, x, y, cz, vx, vy, gr, rt), room)),
          not_t(P.Geo.free(s, x, y, pr, P.Rot.q(rt), obs),
            and_r(P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), Bool.not(P.Geo.free(s, x, y, pr, P.Rot.q(rt), obs)), et)))))
    case False{}:
      zput_obs(P.Geo.free(s, x, y, cz, P.Rot.q(rt), obs), obs, cz, x, y, z, vx, vy, vz, gr, rt)

def zgo_obs(ok: Bool, +s: Nat, +obs: List<&2, P.Body>, +d: P.Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot,
  room: {P.Geo.free(s, x, y, P.Z.shift(P.Body.z(P.Tick.body(P.Move.zgo(s, ok, obs, d, cz, P.Body{x, y, z, vx, vy, vz, gr, hit, rt}))),
    P.Z.like(d, 1n)), P.Rot.q(rt), obs) == True{} : Bool})
  -> {P.Tick.obs(P.Move.zgo(s, ok, obs, d, cz, P.Body{x, y, z, vx, vy, vz, gr, hit, rt})) == obs : List<&2, P.Body>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      ztouch_obs(P.Move.ztouches(s, obs, d, x, y, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), P.Rot.q(rt)), s, obs, d, P.Move.zto(s, obs, d, x, y, z, P.Rot.q(rt)), x, y, z, vx, vy, vz, gr, rt, {==}, room)

def Laws.a_push_is_a_touch_z(s, obs, v0, b, room):
  match b:
    case P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      zgo_obs(Bool.and(P.Z.fits(z, P.Z.add(v0, vz)), P.Geo.free(s, x, y, P.Z.shift(z, P.Z.add(v0, vz)), P.Rot.q(rt), obs)), s, obs,
        P.Z.add(v0, vz), P.Z.shift(z, P.Z.add(v0, vz)), x, y, z, vx, vy, vz, gr, hit, rt, room)

# On a corner, it tips: the sign of the torque
# ==============================================
# The mathematical core of Laws.on_a_corner_it_tips_{x,z} and, by the same
# chain with Hold.arm(Geo.foot(...)) in place of Hold.low, of the
# past_the_edge_it_tips_* and tipping_is_never_thrown_away_* families
# (PROMPT-TOMBAR.md has the physics derivation and the pitfalls below).

def lt_zero_r(+x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def mul_pos(+a: Nat, +ha: {Nat.is_lt(0n, a) == True{} : Bool}, +g: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(a, g)) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(0n, g)) == True{} : Bool}, clash2(ha))
    case 1n+p:
      match g:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, Nat.mul(1n+p, 0n)) == True{} : Bool}, clash2(hg))
        case 1n+q:
          {==}

def le_zero_l(+x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# is_le(a, b) -> is_le(a, 1n+b): weaken the upper bound by one
def le_weaken_r(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 1n+0n) == True{} : Bool}, clash2(h))
        case 1n+bp:
          le_weaken_r(ap, bp, h)

# is_le(1n+d, x) -> is_le(d, x)
def le_weaken_s(+d: Nat, +x: Nat, +h: {Nat.is_le(1n+d, x) == True{} : Bool}) -> {Nat.is_le(d, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(d, 0n) == True{} : Bool}, clash2(h))
    case 1n+xp:
      le_weaken_r(d, xp, h)

# is_le(d, x) -> is_lt(d, 1n+x)
def le_to_lt_s(+d: Nat, +x: Nat, +h: {Nat.is_le(d, x) == True{} : Bool}) -> {Nat.is_lt(d, 1n+x) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+dp:
      match x:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+dp, 1n+0n) == True{} : Bool}, clash2(h))
        case 1n+xp:
          le_to_lt_s(dp, xp, h)

# is_le(1n+d, x) -> is_lt(d, x)
def le_s_to_lt(+d: Nat, +x: Nat, +h: {Nat.is_le(1n+d, x) == True{} : Bool}) -> {Nat.is_lt(d, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(d, 0n) == True{} : Bool}, clash2(h))
    case 1n+xp:
      le_to_lt_s(d, xp, h)

# the div-mod accumulator only grows
def go_mono(+n: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(d, Nat.div.fin(Nat.divmod.go(n, m, d, r))) == True{} : Bool}:
  match n:
    case 0n:
      le_refl(d)
    case 1n+np:
      match m:
        case 0n:
          le_weaken_s(d, Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), go_mono(np, r, 1n+d, 0n))
        case 1n+mp:
          go_mono(np, mp, d, 1n+r)

# enough fuel (n > m) makes the div-mod accumulator strictly grow
def go_pos(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +h: {Nat.is_le(1n+m, n) == True{} : Bool})
  -> {Nat.is_lt(d, Nat.div.fin(Nat.divmod.go(n, m, d, r))) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_lt(d, Nat.div.fin(Nat.divmod.go(0n, m, d, r))) == True{} : Bool}, clash2(h))
    case 1n+np:
      match m:
        case 0n:
          le_s_to_lt(d, Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), go_mono(np, r, 1n+d, 0n))
        case 1n+mp:
          go_pos(np, mp, d, 1n+r, h)

def div_pos(+a: Nat, +b: Nat, +hb: {Nat.is_lt(0n, b) == True{} : Bool}, +h: {Nat.is_le(b, a) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.div(a, b)) == True{} : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.div(a, 0n)) == True{} : Bool}, clash2(hb))
    case 1n+bp:
      go_pos(a, bp, 0n, 0n, h)

def pick_n_pos(c: Bool, +x: Nat, +hx: {Nat.is_lt(0n, x) == True{} : Bool}, +y: Nat,
  +hy: {Nat.is_lt(0n, y) == True{} : Bool}) -> {Nat.is_lt(0n, P.Pick.n(c, x, y)) == True{} : Bool}:
  match c:
    case True{}:
      hx
    case False{}:
      hy

def pick_high_1_pos(+d: Nat) -> {Nat.is_lt(0n, P.Pick.high(d, 1n)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+dp:
      pick_n_pos(Nat.is_le(1n+dp, 1n), 1n, {==}, 1n+dp, {==})

def sub_zero_r(+x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_add_l(+x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(y, x)) == True{} : Bool}:
  match y:
    case 0n:
      le_refl(x)
    case 1n+yp:
      le_weaken_r(x, Nat.add(yp, x), le_add_l(x, yp))

def divc_numerator_ge(+n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +e: Nat)
  -> {Nat.is_le(e, Nat.add(n, Nat.sub(e, 1n))) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(e, Nat.add(0n, Nat.sub(e, 1n))) == True{} : Bool}, clash2(hn))
    case 1n+np:
      match e:
        case 0n:
          le_zero_l(Nat.add(1n+np, 0n))
        case 1n+ep:
          %Equal.sym(Nat, Nat.sub(ep, 0n), ep, sub_zero_r(ep)) : {Nat.is_le(1n+ep, Nat.add(1n+np, _)) == True{} : Bool}
          le_add_l(ep, np)

def divc_mag_pos(+n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +d: Nat)
  -> {Nat.is_lt(0n, Nat.div(Nat.add(n, Nat.sub(P.Pick.high(d, 1n), 1n)), P.Pick.high(d, 1n))) == True{} : Bool}:
  div_pos(Nat.add(n, Nat.sub(P.Pick.high(d, 1n), 1n)), P.Pick.high(d, 1n), pick_high_1_pos(d),
    divc_numerator_ge(n, hn, P.Pick.high(d, 1n)))

# Z zero-absorption kit (Pos{0n} and Neg{0n} are different terms as written:
# Z.add(v, Pos{0n}) == v is FALSE for v == Neg{0n}. Only proved for v of
# known-nonzero magnitude, except Z.add(v, Neg{0n}) == v, which is
# unconditional.)
# ---------------------------------------------------------------------------

def Z_add_r_pos0(+v: P.Z, +hv: {Nat.is_lt(0n, P.Z.mag(v)) == True{} : Bool}) -> {P.Z.add(v, P.Pos{0n}) == v : P.Z}:
  match v:
    case P.Pos{n}:
      %R.add_zero(n) : {P.Pos{Nat.add(n, 0n)} == P.Pos{_} : P.Z}
      {==}
    case P.Neg{n}:
      %Equal.sym(Bool, Nat.is_lt(0n, n), True{}, hv) : {P.Z.diff(_, 0n, n) == P.Neg{n} : P.Z}
      %sub_zero_r(n) : {P.Neg{Nat.sub(n, 0n)} == P.Neg{_} : P.Z}
      {==}

def Z_add_r_neg0(+v: P.Z) -> {P.Z.add(v, P.Neg{0n}) == v : P.Z}:
  match v:
    case P.Pos{n}:
      %Equal.sym(Bool, Nat.is_lt(n, 0n), False{}, lt_zero_r(n)) : {P.Z.diff(_, n, 0n) == P.Pos{n} : P.Z}
      %sub_zero_r(n) : {P.Pos{Nat.sub(n, 0n)} == P.Pos{_} : P.Z}
      {==}
    case P.Neg{n}:
      %R.add_zero(n) : {P.Neg{Nat.add(n, 0n)} == P.Neg{_} : P.Z}
      {==}

def Z_add_l_pos0(+v: P.Z, +hv: {Nat.is_lt(0n, P.Z.mag(v)) == True{} : Bool}) -> {P.Z.add(P.Pos{0n}, v) == v : P.Z}:
  match v:
    case P.Pos{n}:
      {==}
    case P.Neg{n}:
      %Equal.sym(Bool, Nat.is_lt(0n, n), True{}, hv) : {P.Z.diff(_, 0n, n) == P.Neg{n} : P.Z}
      %sub_zero_r(n) : {P.Neg{Nat.sub(n, 0n)} == P.Neg{_} : P.Z}
      {==}

# Rot.crz(ax, ay, 0, g) is exactly ax * g (the ay*0 term always cancels)
# -------------------------------------------------------------------------

def Z_mul_pos_mag(+ax: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(ax)) == True{} : Bool}, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}) -> {Nat.is_lt(0n, P.Z.mag(P.Z.mul(ax, P.Pos{g}))) == True{} : Bool}:
  match ax:
    case P.Pos{a}:
      mul_pos(a, ha, g, hg)
    case P.Neg{a}:
      mul_pos(a, ha, g, hg)

def crz_eq(+ax: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(ax)) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}) -> {P.Rot.crz(ax, ay, P.Pos{0n}, P.Pos{g}) == P.Z.mul(ax, P.Pos{g}) : P.Z}:
  match ay:
    case P.Pos{a}:
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, R.mul_zero(a))
        : {P.Z.sub(P.Z.mul(ax, P.Pos{g}), P.Pos{_}) == P.Z.mul(ax, P.Pos{g}) : P.Z}
      Z_add_r_neg0(P.Z.mul(ax, P.Pos{g}))
    case P.Neg{a}:
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, R.mul_zero(a))
        : {P.Z.sub(P.Z.mul(ax, P.Pos{g}), P.Neg{_}) == P.Z.mul(ax, P.Pos{g}) : P.Z}
      Z_add_r_pos0(P.Z.mul(ax, P.Pos{g}), Z_mul_pos_mag(ax, ha, g, hg))

# The sign of the torque about z: ax * w.z > 0 whenever ax != 0, g > 0.
# This is the mathematical core of the on_a_corner_it_tips_x and (by the
# same chain, past_the_edge_it_tips_*) family: Body.step sets the new spin
# w' via Rot.kickd(Rot.about(s,ax,ay,az), ax,ay,az, Pos{0},Pos{g},Pos{0}),
# so w'.z == Z.divc(Rot.crz(ax,ay,Pos{0},Pos{g}), Rot.about(s,ax,ay,az)),
# and Rot.about always has the form Nat.add(8n, Y) for some Y -- opaque,
# never expand it, just its positivity (D below stands for it).
# ---------------------------------------------------------------------------

def kickzsign(+ax: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(ax)) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat, +hD: {Nat.is_lt(0n, D) == True{} : Bool})
  -> {P.Z.above(P.Z.mul(ax, P.Z.divc(P.Rot.crz(ax, ay, P.Pos{0n}, P.Pos{g}), D)), P.Pos{0n}) == True{} : Bool}:
  match ax:
    case P.Pos{a}:
      %Equal.sym(P.Z, P.Rot.crz(P.Pos{a}, ay, P.Pos{0n}, P.Pos{g}), P.Z.mul(P.Pos{a}, P.Pos{g}),
        crz_eq(P.Pos{a}, ha, ay, g, hg)) : {P.Z.above(P.Z.mul(P.Pos{a}, P.Z.divc(_, D)), P.Pos{0n}) == True{} : Bool}
      mul_pos(a, ha, Nat.div(Nat.add(Nat.mul(a, g), Nat.sub(P.Pick.high(D, 1n), 1n)), P.Pick.high(D, 1n)),
        divc_mag_pos(Nat.mul(a, g), mul_pos(a, ha, g, hg), D))
    case P.Neg{a}:
      %Equal.sym(P.Z, P.Rot.crz(P.Neg{a}, ay, P.Pos{0n}, P.Pos{g}), P.Z.mul(P.Neg{a}, P.Pos{g}),
        crz_eq(P.Neg{a}, ha, ay, g, hg)) : {P.Z.above(P.Z.mul(P.Neg{a}, P.Z.divc(_, D)), P.Pos{0n}) == True{} : Bool}
      mul_pos(a, ha, Nat.div(Nat.add(Nat.mul(a, g), Nat.sub(P.Pick.high(D, 1n), 1n)), P.Pick.high(D, 1n)),
        divc_mag_pos(Nat.mul(a, g), mul_pos(a, ha, g, hg), D))

def about_pos(+s: Nat, +rx: P.Z, +ry: P.Z, +rz: P.Z) -> {Nat.is_lt(0n, P.Rot.about(s, rx, ry, rz)) == True{} : Bool}:
  {==}

# both Pick.n branches equal: the value does not depend on the condition
def pick_same(c: Bool, +v: Nat) -> {P.Pick.n(c, v, v) == v : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# Body.step1 on a body at rest (v=0), idle input, no obstacles: a no-op on
# x, y, z, vx, vy, vz -- only the spin (Rot.w) moves, via Rot.held. Proved
# in three pieces (drive, then the x/z moves) because unfolding Body.step1
# whole balloons combinatorially in the checker.

def drive_idle0(+k: P.K, +x: Nat, +y: Nat, +z: Nat, +h: Bool, +rt: P.Rot)
  -> {P.Body.drive(k, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})
      == P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt} : P.Body}:
  match k:
    case P.K{g, mu, jump, acc, size}:
      %Equal.sym(Nat,
        P.Pick.n(Cmp.is_le(Nat.cmp(0n, Nat.mul(Nat.div.fin(Nat.divmod.go(Nat.mul(mu, g), 255n, 0n, 0n)), 0n))), 0n, 0n),
        0n,
        pick_same(Cmp.is_le(Nat.cmp(0n, Nat.mul(Nat.div.fin(Nat.divmod.go(Nat.mul(mu, g), 255n, 0n, 0n)), 0n))), 0n))
        : {P.Body{x, y, z, P.Pos{Nat.sub(0n, _)}, P.Pos{0n}, P.Pos{Nat.sub(0n, _)}, True{}, False{}, rt}
            == P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt} : P.Body}
      {==}

def movex_idle0(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +h: Bool, +rt: P.Rot)
  -> {P.Move.x(s, [], P.Pos{0n}, P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})
      == (P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}, []) : P.Body & List<&2, P.Body>}:
  %R.add_zero(x) : {(P.Body{Nat.add(x, 0n), y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}, [])
    == (P.Body{_, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}, []) : P.Body & List<&2, P.Body>}
  {==}

def movez_idle0(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +h: Bool, +rt: P.Rot)
  -> {P.Move.z(s, [], P.Pos{0n}, P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})
      == (P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}, []) : P.Body & List<&2, P.Body>}:
  %R.add_zero(z) : {(P.Body{x, y, Nat.add(z, 0n), P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}, [])
    == (P.Body{x, y, _, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}, []) : P.Body & List<&2, P.Body>}
  {==}

# Composing Body.step for an idle, resting, obstacle-free body: the drive,
# the two horizontal moves and the vertical hold, chained through
# Equal.cong/Equal.trans instead of rewriting the checker's own
# eagerly-unfolded (and, for an opaque k, unreadable) normal form directly.
# See PROMPT-TOMBAR.md for why this shape was needed.
# ---------------------------------------------------------------------------

def wz_after_pressw(+rt: P.Rot, +s: Nat, +a: P.Wv, +g: Nat)
  -> {P.Wv.z(P.Rot.w(P.Rot.pressw(rt, s, a, g)))
      == P.Z.add(P.Wv.z(P.Rot.w(rt)), P.Z.divc(P.Rot.crz(P.Wv.x(a), P.Wv.y(a), P.Pos{0n}, P.Pos{g}),
          P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a)))) : P.Z}:
  {==}

def movey_stay0(+s: Nat, +g: Nat, +x: Nat, +y: Nat, +z: Nat, +h: Bool, +q: P.Quat,
  +held: {P.Tick.sinks(s, [], x, y, z, q) == False{} : Bool},
  +floor: {P.Geo.onfloor(s, y, q) == True{} : Bool})
  -> {P.Move.y(s, g, [], P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}})
      == P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h,
          P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, P.Hold.low(P.Rot.mat(q), s), g)} : P.Body}:
  %Equal.sym(Bool, P.Tick.sinks(s, [], x, y, z, q), False{}, held)
    : {P.Move.stay(Bool.not(_), s, g, [], x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, h, P.Rot{q, P.Wv.zero()})
        == P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h,
            P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, P.Hold.low(P.Rot.mat(q), s), g)} : P.Body}
  %Equal.sym(Bool, P.Geo.onfloor(s, y, q), True{}, floor)
    : {P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot.held(_, P.Rot{q, P.Wv.zero()}, s, x, y, z, g, [])}
        == P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h,
            P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, P.Hold.low(P.Rot.mat(q), s), g)} : P.Body}
  {==}

def step_pair(+k: P.K, +x: Nat, +y: Nat, +z: Nat, +h: Bool, +q: P.Quat,
  +held: {P.Tick.sinks(P.K.size(k), [], x, y, z, q) == False{} : Bool},
  +floor: {P.Geo.onfloor(P.K.size(k), y, q) == True{} : Bool})
  -> {P.Body.step(k, [], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}})
      == (P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{},
          P.Rot.pressw(P.Rot{q, P.Wv.zero()}, P.K.size(k), P.Hold.low(P.Rot.mat(q), P.K.size(k)), P.K.g(k))}, []) : P.Body & List<&2, P.Body>}:
  +s = P.K.size(k)
  +g2 = P.K.g(k)
  +rt = {P.Rot{q, P.Wv.zero()} : P.Rot}
  +bd = {P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt} : P.Body}
  +e_drive = drive_idle0(k, x, y, z, h, rt)
  +e_x = Equal.trans(P.Body & List<&2, P.Body>,
    P.Move.x(s, [], P.Pos{0n}, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})),
    P.Move.x(s, [], P.Pos{0n}, bd), (bd, []),
    Equal.cong(P.Body, P.Body & List<&2, P.Body>, (b: P.Body) => P.Move.x(s, [], P.Pos{0n}, b),
      P.Body.drive(k, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}), bd, e_drive),
    movex_idle0(s, x, y, z, False{}, rt))
  +e_movez_cong = Equal.cong(P.Body & List<&2, P.Body>, P.Body & List<&2, P.Body>, (r: P.Body & List<&2, P.Body>) => P.Tick.y(s, g2, r),
    P.Move.z(s, [], P.Pos{0n}, bd), (bd, []), movez_idle0(s, x, y, z, False{}, rt))
  +e_movez_final = Equal.trans(P.Body & List<&2, P.Body>,
    P.Tick.y(s, g2, P.Move.z(s, [], P.Pos{0n}, bd)), P.Tick.y(s, g2, (bd, [])), (P.Move.y(s, g2, [], bd), []),
    e_movez_cong, {==})
  +e_z = Equal.trans(P.Body & List<&2, P.Body>,
    P.Tick.z(s, g2, P.Pos{0n}, P.Move.x(s, [], P.Pos{0n}, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}))),
    P.Tick.z(s, g2, P.Pos{0n}, (bd, [])), (P.Move.y(s, g2, [], bd), []),
    Equal.cong(P.Body & List<&2, P.Body>, P.Body & List<&2, P.Body>, (r: P.Body & List<&2, P.Body>) => P.Tick.z(s, g2, P.Pos{0n}, r),
      P.Move.x(s, [], P.Pos{0n}, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})), (bd, []), e_x),
    e_movez_final)
  Equal.trans(P.Body & List<&2, P.Body>,
    P.Body.step(k, [], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}),
    (P.Move.y(s, g2, [], bd), []),
    (P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, P.Rot.pressw(rt, s, P.Hold.low(P.Rot.mat(q), s), g2)}, []),
    e_z,
    Equal.cong(P.Body, P.Body & List<&2, P.Body>, (b: P.Body) => (b, []),
      P.Move.y(s, g2, [], bd), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, P.Rot.pressw(rt, s, P.Hold.low(P.Rot.mat(q), s), g2)},
      movey_stay0(s, g2, x, y, z, False{}, q, held, floor)))

def wz_after_pressw0(+q: P.Quat, +s: Nat, +a: P.Wv, +g: Nat)
  -> {P.Wv.z(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, a, g)))
      == P.Z.add(P.Pos{0n}, P.Z.divc(P.Rot.crz(P.Wv.x(a), P.Wv.y(a), P.Pos{0n}, P.Pos{g}),
          P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a)))) : P.Z}:
  wz_after_pressw(P.Rot{q, P.Wv.zero()}, s, a, g)

def kickzsign_mag(+ax: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(ax)) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat)
  -> {Nat.is_lt(0n, P.Z.mag(P.Z.divc(P.Rot.crz(ax, ay, P.Pos{0n}, P.Pos{g}), D))) == True{} : Bool}:
  match ax:
    case P.Pos{a}:
      %Equal.sym(P.Z, P.Rot.crz(P.Pos{a}, ay, P.Pos{0n}, P.Pos{g}), P.Z.mul(P.Pos{a}, P.Pos{g}),
        crz_eq(P.Pos{a}, ha, ay, g, hg)) : {Nat.is_lt(0n, P.Z.mag(P.Z.divc(_, D))) == True{} : Bool}
      divc_mag_pos(Nat.mul(a, g), mul_pos(a, ha, g, hg), D)
    case P.Neg{a}:
      %Equal.sym(P.Z, P.Rot.crz(P.Neg{a}, ay, P.Pos{0n}, P.Pos{g}), P.Z.mul(P.Neg{a}, P.Pos{g}),
        crz_eq(P.Neg{a}, ha, ay, g, hg)) : {Nat.is_lt(0n, P.Z.mag(P.Z.divc(_, D))) == True{} : Bool}
      divc_mag_pos(Nat.mul(a, g), mul_pos(a, ha, g, hg), D)

# Half a turning, rounded up
# ==========================
# A refused turn keeps Wv.halfc of its turning (Body.spin): each part
# ceil(n / 2), n its size, with its sign. Two facts carry the laws through
# it: the half of a part that is there is still there, with its sign (a
# cube that was turning the way it tips still is), and twice the half is
# at most one more than the whole (a_stopped_turn_does_not_wind_up).
# Nat.div counts its dividend down one step at a time (Nat.divmod.go), so
# both come out of that count.
# ---------------------------------------------------------------------------

# a + (1 + b) is 1 + (a + b)
def add_succ_r(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, (v: Nat) => 1n+v, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ_r(p, b))

# the count by 2 that Nat.div makes, from the phase with one step to go
# before it counts one more (m = 1, r = 0) or one step in (m = 0, r = 1):
# twice what it ends with is at most twice what it had, plus what is left
def HalfGo(+n: Nat, ph: Bool, +d: Nat) -> Type:
  match ph:
    case True{}:
      {Nat.is_le(Nat.add(Nat.div.fin(Nat.divmod.go(n, 1n, d, 0n)), Nat.div.fin(Nat.divmod.go(n, 1n, d, 0n))),
        Nat.add(Nat.add(d, d), n)) == True{} : Bool}
    case False{}:
      {Nat.is_le(Nat.add(Nat.div.fin(Nat.divmod.go(n, 0n, d, 1n)), Nat.div.fin(Nat.divmod.go(n, 0n, d, 1n))),
        Nat.add(Nat.add(d, d), 1n+n)) == True{} : Bool}

# (1 + d) + (1 + d), and n on, is d + d and 2 + n on
def half_go.e(+d: Nat, +n: Nat) -> {Nat.add(Nat.add(1n+d, 1n+d), n) == Nat.add(Nat.add(d, d), 1n+(1n+n)) : Nat}:
  +l = Equal.cong(Nat, Nat, (v: Nat) => 1n+Nat.add(v, n), Nat.add(d, 1n+d), 1n+Nat.add(d, d), add_succ_r(d, d))
  +r = Equal.trans(Nat, Nat.add(Nat.add(d, d), 1n+(1n+n)), 1n+Nat.add(Nat.add(d, d), 1n+n), 1n+(1n+Nat.add(Nat.add(d, d), n)),
    add_succ_r(Nat.add(d, d), 1n+n),
    Equal.cong(Nat, Nat, (v: Nat) => 1n+v, Nat.add(Nat.add(d, d), 1n+n), 1n+Nat.add(Nat.add(d, d), n), add_succ_r(Nat.add(d, d), n)))
  Equal.trans(Nat, Nat.add(Nat.add(1n+d, 1n+d), n), 1n+(1n+Nat.add(Nat.add(d, d), n)), Nat.add(Nat.add(d, d), 1n+(1n+n)),
    l, Equal.sym(Nat, Nat.add(Nat.add(d, d), 1n+(1n+n)), 1n+(1n+Nat.add(Nat.add(d, d), n)), r))

def half_go(n: Nat, ph: Bool, +d: Nat) -> HalfGo(n, ph, d):
  match n:
    case 0n:
      match ph:
        case True{}:
          le_add(Nat.add(d, d), 0n)
        case False{}:
          le_add(Nat.add(d, d), 1n)
    case 1n++np:
      match ph:
        case True{}:
          half_go(np, False{}, d)
        case False{}:
          %half_go.e(d, np) : {Nat.is_le(Nat.add(Nat.div.fin(Nat.divmod.go(np, 1n, 1n+d, 0n)), Nat.div.fin(Nat.divmod.go(np, 1n, 1n+d, 0n))), _) == True{} : Bool};
          half_go(np, True{}, 1n+d)

# twice ceil(n / 2) is at most 1 + n
def zhalf(+n: Nat) -> {Nat.is_le(Nat.add(Nat.div(Nat.add(1n, n), 2n), Nat.div(Nat.add(1n, n), 2n)), Nat.add(1n, n)) == True{} : Bool}:
  half_go(1n+n, True{}, 0n)

def zhalf_z(v: P.Z) -> {Nat.is_le(Nat.add(P.Z.mag(P.Z.halfc(v)), P.Z.mag(P.Z.halfc(v))), Nat.add(1n, P.Z.mag(v))) == True{} : Bool}:
  match v:
    case P.Pos{+n}:
      zhalf(n)
    case P.Neg{+n}:
      zhalf(n)

# the half of 1 + m is at least 1
def halfc_one(+m: Nat) -> {Nat.is_lt(0n, Nat.div(Nat.add(1n, 1n+m), 2n)) == True{} : Bool}:
  le_s_to_lt(0n, Nat.div.fin(Nat.divmod.go(m, 1n, 1n, 0n)), go_mono(m, 1n, 1n, 0n))

# a part below 0 has its half below 0, one above has it above
def halfc_neg(v: P.Z, h: {P.Z.above(P.Pos{0n}, v) == True{} : Bool}) -> {P.Z.above(P.Pos{0n}, P.Z.halfc(v)) == True{} : Bool}:
  match v:
    case P.Pos{+y}:
      Empty.absurd({P.Z.above(P.Pos{0n}, P.Z.halfc(P.Pos{y})) == True{} : Bool},
        clash2(Equal.trans(Bool, False{}, Nat.is_lt(y, 0n), True{}, Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, lt_zero_r(y)), h)))
    case P.Neg{y}:
      match y:
        case 0n:
          Empty.absurd({P.Z.above(P.Pos{0n}, P.Z.halfc(P.Neg{0n})) == True{} : Bool}, clash2(h))
        case 1n+m:
          halfc_one(m)

def halfc_pos(v: P.Z, h: {P.Z.above(v, P.Pos{0n}) == True{} : Bool}) -> {P.Z.above(P.Z.halfc(v), P.Pos{0n}) == True{} : Bool}:
  match v:
    case P.Pos{y}:
      match y:
        case 0n:
          Empty.absurd({P.Z.above(P.Z.halfc(P.Pos{0n}), P.Pos{0n}) == True{} : Bool}, clash2(h))
        case 1n+m:
          halfc_one(m)
    case P.Neg{y}:
      Empty.absurd({P.Z.above(P.Z.halfc(P.Neg{y}), P.Pos{0n}) == True{} : Bool}, clash2(h))

# p y above 0 gives p ceil(y / 2) above 0
def prod_half(p: Nat, +y: Nat, h: {Nat.is_lt(0n, Nat.mul(p, y)) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(p, Nat.div(Nat.add(1n, y), 2n))) == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(0n, Nat.div(Nat.add(1n, y), 2n))) == True{} : Bool}, clash2(h))
    case 1n++pp:
      match y:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, Nat.mul(1n+pp, Nat.div(Nat.add(1n, 0n), 2n))) == True{} : Bool},
            clash2(%mul_zero(pp) : {Nat.is_lt(0n, _) == True{} : Bool}; h))
        case 1n+m:
          lt_add(Nat.div(Nat.add(1n, 1n+m), 2n), Nat.mul(pp, Nat.div(Nat.add(1n, 1n+m), 2n)), halfc_one(m))

# a product above 0 stays above 0 with its second factor halved, and one
# below 0 stays below 0
def mulhalf_pos(a: P.Z, v: P.Z, h: {P.Z.above(P.Z.mul(a, v), P.Pos{0n}) == True{} : Bool})
  -> {P.Z.above(P.Z.mul(a, P.Z.halfc(v)), P.Pos{0n}) == True{} : Bool}:
  match a v:
    case P.Pos{+p} P.Pos{+y}:
      prod_half(p, y, h)
    case P.Neg{+p} P.Neg{+y}:
      prod_half(p, y, h)
    case P.Pos{+p} P.Neg{+y}:
      Empty.absurd({P.Z.above(P.Z.mul(P.Pos{p}, P.Z.halfc(P.Neg{y})), P.Pos{0n}) == True{} : Bool}, clash2(h))
    case P.Neg{+p} P.Pos{+y}:
      Empty.absurd({P.Z.above(P.Z.mul(P.Neg{p}, P.Z.halfc(P.Pos{y})), P.Pos{0n}) == True{} : Bool}, clash2(h))

def mulhalf_neg(a: P.Z, v: P.Z, h: {P.Z.above(P.Pos{0n}, P.Z.mul(a, v)) == True{} : Bool})
  -> {P.Z.above(P.Pos{0n}, P.Z.mul(a, P.Z.halfc(v))) == True{} : Bool}:
  match a v:
    case P.Pos{+p} P.Neg{+y}:
      prod_half(p, y, h)
    case P.Neg{+p} P.Pos{+y}:
      prod_half(p, y, h)
    case P.Pos{+p} P.Pos{+y}:
      Empty.absurd({P.Z.above(P.Pos{0n}, P.Z.mul(P.Pos{p}, P.Z.halfc(P.Pos{y}))) == True{} : Bool},
        clash2(Equal.trans(Bool, False{}, Nat.is_lt(Nat.mul(p, y), 0n), True{},
          Equal.sym(Bool, Nat.is_lt(Nat.mul(p, y), 0n), False{}, lt_zero_r(Nat.mul(p, y))), h)))
    case P.Neg{+p} P.Neg{+y}:
      Empty.absurd({P.Z.above(P.Pos{0n}, P.Z.mul(P.Neg{p}, P.Z.halfc(P.Neg{y}))) == True{} : Bool},
        clash2(Equal.trans(Bool, False{}, Nat.is_lt(Nat.mul(p, y), 0n), True{},
          Equal.sym(Bool, Nat.is_lt(Nat.mul(p, y), 0n), False{}, lt_zero_r(Nat.mul(p, y))), h)))


# The turning through the turn about a contact
# ============================================
# The search the turn makes (Tick.shrink, Tick.cand, Tick.pivot, down to
# Tick.put) never touches the turning: every candidate is built as
# Rot{Rot.turn(q, w), Rot.w(rt)}, and Tick.put hands back either it or the
# rt it started from. So Rot.w comes out of the whole turn as it went in
# (ROTW), and proving that needs nothing of the quaternion.
#
# Two ways NOT to do this, both measured: {==} (and Equal.cong/Equal.trans,
# which are {==} underneath) against a term that drags in Tick.turn1b,
# Tick.turn2, Tick.pivota0 or Tick.shrink never finishes -- {==} normalizes
# the whole 7-level search, a 64-step Tick.drop inside each level; and a
# predicate that projects Rot.q out of the body the search returns blows up
# the same way (the quaternion is built from Quat.step/Rot.turn at every
# level). Match on the same parameter the return type mentions instead, as
# the _fs family does, and only ever look at the turning.
# ---------------------------------------------------------------------------

def ROTW(+w0: P.Wv, -b: P.Body) -> Type:
  {P.Rot.w(P.Body.rot(b)) == w0 : P.Wv}

# a fact about the turning of b: what the turn about a contact keeps is
# the turning the step left (w0), or, refused, half of it (Body.spin), so
# a fact that holds of both holds of what comes out
def WP(Pw: P.Wv -> Type, b: P.Body) -> Type:
  Pw(P.Rot.w(P.Body.rot(b)))

def put_rotw(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat,
  +nz: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w0: P.Wv,
  hrt: {P.Rot.w(rt) == w0 : P.Wv}, hr2: {P.Rot.w(r2) == w0 : P.Wv})
  -> ROTW(w0, P.Tick.put(ok, s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  match ok:
    case True{}:
      hr2
    case False{}:
      hrt

def place_rotw(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w0: P.Wv,
  hrt: {P.Rot.w(rt) == w0 : P.Wv}, hr2: {P.Rot.w(r2) == w0 : P.Wv})
  -> ROTW(w0, P.Tick.place(s, g, obs, x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)):
  put_rotw(P.Tick.turnok(s, obs, y, nx, ny, nz, P.Rot.q(r2), gr), s, g, obs, x, y, z, nx, ny, nz,
    vx, vy, vz, gr, hit, rt, r2, w0, hrt, hr2)

def pivot_rotw(m: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +rx: P.Z, +ry: P.Z, +rz: P.Z, +w0: P.Wv,
  hrt: {P.Rot.w(rt) == w0 : P.Wv}, hr2: {P.Rot.w(r2) == w0 : P.Wv})
  -> ROTW(w0, P.Tick.pivot(m, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, rx, ry, rz)):
  P.Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = P.Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = P.Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = P.Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = P.Tick.drop(s, obs, nx, y, nz, P.Rot.q(r2), Nat.add(Nat.sub(y, P.Pick.low(ny, y)), Nat.div(s, 256n)))
  place_rotw(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, hit, rt, r2, w0, hrt, hr2)

def cand_rotw(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z, +w0: P.Wv,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv})
  -> ROTW(w0, P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  pivot_rotw(P.Rot.mat(P.Quat.half(P.Quat.step(w, P.Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    P.Rot{P.Rot.turn(P.Rot.q(rt), w), P.Rot.w(rt)}, rx, ry, rz, w0, hrt, hrt)

def shrink_rotw(n: Nat, p: P.Body & Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z, +w0: P.Wv,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv}, hb: ROTW(w0, Body.of_pair(p)))
  -> ROTW(w0, P.Tick.shrink(n, p, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  match n:
    case 0n:
      match p:
        case (b, ok):
          hb
    case 1n+m:
      match p:
        case (b, ok):
          match ok:
            case True{}:
              hb
            case False{}:
              shrink_rotw(m, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt),
                s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, w0, hrt, Tick.shrink.pair_up((kb: P.Body) => ROTW(w0, kb), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz), rt, cand_rotw(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, P.Wv.half(w), rx, ry, rz, w0, hrt)))

def start_rotw(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z,
  +gr: Bool, +hit: Bool, +rt: P.Rot, +w: P.Wv, +rx: P.Z, +ry: P.Z, +rz: P.Z, +w0: P.Wv,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv})
  -> ROTW(w0, P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt),
      s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz)):
  shrink_rotw(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt),
    s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, w0, hrt, Tick.shrink.pair_up((kb: P.Body) => ROTW(w0, kb), P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz), rt, cand_rotw(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w, rx, ry, rz, w0, hrt)))

def spin_wp(tip: Bool, moved: Bool, +b: P.Body, +rt: P.Rot, +w0: P.Wv, -Pw: P.Wv -> Type,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv}, hb: Once.Body((kb: P.Body) => ROTW(w0, kb), b), +htip: {tip == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> Once.Body((kb: P.Body) => WP(Pw, kb), P.Body.spin(tip, moved, b, rt)):
  match moved:
    case True{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          %Equal.sym(P.Wv, P.Rot.w(u9), w0, hb) : Pw(_);
          h0
    case False{}:
      match b:
        case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
          %Equal.sym(Bool, tip, True{}, htip) : Pw(P.Pick.w(_, P.Wv.halfc(P.Rot.w(rt)), P.Wv.zero()));
          %Equal.sym(P.Wv, P.Rot.w(rt), w0, hrt) : Pw(P.Wv.halfc(_));
          h1

def pivota0_wp.k1(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv, +w0: P.Wv, -Pw: P.Wv -> Type,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(a)), P.Z.mag(P.Wv.z(a)))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> Once.Body((kb: P.Body) => WP(Pw, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  P.Wv{+ax, +ay, +az} = a
  spin_wp(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))),
    P.Tick.moved(P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt),
    P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az),
    rt, w0, Pw, hrt, Once.Body.up((kb: P.Body) => ROTW((w0), kb), (P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az)), start_rotw(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az, w0, hrt)),
    htip, h0, h1)

def pivota0_wp(+md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, +a: P.Wv, +w0: P.Wv, -Pw: P.Wv -> Type,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(a)), P.Z.mag(P.Wv.z(a)))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  Once.Body.down((kb: P.Body) => WP(Pw, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a),
    pivota0_wp.k1(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a, w0, Pw, hrt, htip, h0, h1))

def pivota_wp(md: P.Mat, +s: Nat, +g: Nat, obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv, +w0: P.Wv, -Pw: P.Wv -> Type,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(a)), P.Z.mag(P.Wv.z(a)))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)):
  match obs:
    case []:
      pivota0_wp(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, w0, Pw, hrt, htip, h0, h1)
    case o <> rest:
      pivota0_wp(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a, w0, Pw, hrt, htip, h0, h1)

def turn2_wp(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat, +w0: P.Wv, -Pw: P.Wv -> Type,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv},
  +hheld: {held == True{} : Bool}, +hfloor: {floor == True{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))),
    P.Z.mag(P.Wv.z(P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)):
  match held floor:
    case False{} _:
      Empty.absurd(WP(Pw, P.Tick.place(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2)), clash2(hheld))
    case True{} False{}:
      Empty.absurd(WP(Pw, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2,
        P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))), clash2(hfloor))
    case True{} True{}:
      pivota_wp(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2,
        P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s), w0, Pw, hrt, htip, h0, h1)

def turn1b_wp(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == True{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn1b(s, g, obs, b)):
  match b:
    case P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      turn2_wp(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
        P.Rot.free(rt), P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), w0, Pw,
        hb, hgr, hfloor, htip, h0, h1)

def turn1_wp(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == True{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn1(still, s, g, obs, b)):
  match still:
    case True{}:
      %Equal.sym(P.Wv, P.Rot.w(P.Body.rot(b)), w0, hb) : Pw(_);
      h0
    case False{}:
      turn1b_wp(s, g, obs, b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)

def turn0_wp(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == True{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn0(s, g, obs, b)):
  turn1_wp(P.Wv.null(P.Rot.w(P.Body.rot(b))), s, g, obs, b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)

def turn_wp(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == True{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.low(P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn(s, g, obs, b)):
  match obs:
    case []:
      turn0_wp(s, g, [], b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)
    case o <> rest:
      turn0_wp(s, g, o <> rest, b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)

# The same torque about x: the floor pressing up at +z of the middle turns
# the cube about -x (Rot.crx carries -az*g), so the arm along z and the
# turning about x have opposite signs.
# ---------------------------------------------------------------------------

def Z_add_l_neg0(+v: P.Z) -> {P.Z.add(P.Neg{0n}, v) == v : P.Z}:
  match v:
    case P.Pos{n}:
      %Equal.sym(Bool, Nat.is_lt(n, 0n), False{}, lt_zero_r(n)) : {P.Z.diff(_, n, 0n) == P.Pos{n} : P.Z}
      %sub_zero_r(n) : {P.Pos{Nat.sub(n, 0n)} == P.Pos{_} : P.Z}
      {==}
    case P.Neg{n}:
      {==}

def Z_opp_mul_pos_mag(+az: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(az)) == True{} : Bool}, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}) -> {Nat.is_lt(0n, P.Z.mag(P.Z.opp(P.Z.mul(az, P.Pos{g})))) == True{} : Bool}:
  match az:
    case P.Pos{a}:
      mul_pos(a, ha, g, hg)
    case P.Neg{a}:
      mul_pos(a, ha, g, hg)

def crx_eq(+ay: P.Z, +az: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(az)) == True{} : Bool}, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}) -> {P.Rot.crx(ay, az, P.Pos{g}, P.Pos{0n}) == P.Z.opp(P.Z.mul(az, P.Pos{g})) : P.Z}:
  match ay:
    case P.Pos{a}:
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, R.mul_zero(a))
        : {P.Z.sub(P.Pos{_}, P.Z.mul(az, P.Pos{g})) == P.Z.opp(P.Z.mul(az, P.Pos{g})) : P.Z}
      Z_add_l_pos0(P.Z.opp(P.Z.mul(az, P.Pos{g})), Z_opp_mul_pos_mag(az, ha, g, hg))
    case P.Neg{a}:
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, R.mul_zero(a))
        : {P.Z.sub(P.Neg{_}, P.Z.mul(az, P.Pos{g})) == P.Z.opp(P.Z.mul(az, P.Pos{g})) : P.Z}
      Z_add_l_neg0(P.Z.opp(P.Z.mul(az, P.Pos{g})))

def kickxsign(+az: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(az)) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat)
  -> {P.Z.above(P.Pos{0n}, P.Z.mul(az, P.Z.divc(P.Rot.crx(ay, az, P.Pos{g}, P.Pos{0n}), D))) == True{} : Bool}:
  match az:
    case P.Pos{c}:
      %Equal.sym(P.Z, P.Rot.crx(ay, P.Pos{c}, P.Pos{g}, P.Pos{0n}), P.Z.opp(P.Z.mul(P.Pos{c}, P.Pos{g})),
        crx_eq(ay, P.Pos{c}, ha, g, hg)) : {P.Z.above(P.Pos{0n}, P.Z.mul(P.Pos{c}, P.Z.divc(_, D))) == True{} : Bool}
      mul_pos(c, ha, Nat.div(Nat.add(Nat.mul(c, g), Nat.sub(P.Pick.high(D, 1n), 1n)), P.Pick.high(D, 1n)),
        divc_mag_pos(Nat.mul(c, g), mul_pos(c, ha, g, hg), D))
    case P.Neg{c}:
      %Equal.sym(P.Z, P.Rot.crx(ay, P.Neg{c}, P.Pos{g}, P.Pos{0n}), P.Z.opp(P.Z.mul(P.Neg{c}, P.Pos{g})),
        crx_eq(ay, P.Neg{c}, ha, g, hg)) : {P.Z.above(P.Pos{0n}, P.Z.mul(P.Neg{c}, P.Z.divc(_, D))) == True{} : Bool}
      mul_pos(c, ha, Nat.div(Nat.add(Nat.mul(c, g), Nat.sub(P.Pick.high(D, 1n), 1n)), P.Pick.high(D, 1n)),
        divc_mag_pos(Nat.mul(c, g), mul_pos(c, ha, g, hg), D))

def kickxsign_mag(+az: P.Z, +ha: {Nat.is_lt(0n, P.Z.mag(az)) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat)
  -> {Nat.is_lt(0n, P.Z.mag(P.Z.divc(P.Rot.crx(ay, az, P.Pos{g}, P.Pos{0n}), D))) == True{} : Bool}:
  match az:
    case P.Pos{c}:
      %Equal.sym(P.Z, P.Rot.crx(ay, P.Pos{c}, P.Pos{g}, P.Pos{0n}), P.Z.opp(P.Z.mul(P.Pos{c}, P.Pos{g})),
        crx_eq(ay, P.Pos{c}, ha, g, hg)) : {Nat.is_lt(0n, P.Z.mag(P.Z.divc(_, D))) == True{} : Bool}
      divc_mag_pos(Nat.mul(c, g), mul_pos(c, ha, g, hg), D)
    case P.Neg{c}:
      %Equal.sym(P.Z, P.Rot.crx(ay, P.Neg{c}, P.Pos{g}, P.Pos{0n}), P.Z.opp(P.Z.mul(P.Neg{c}, P.Pos{g})),
        crx_eq(ay, P.Neg{c}, ha, g, hg)) : {Nat.is_lt(0n, P.Z.mag(P.Z.divc(_, D))) == True{} : Bool}
      divc_mag_pos(Nat.mul(c, g), mul_pos(c, ha, g, hg), D)

def wx_after_pressw0(+q: P.Quat, +s: Nat, +a: P.Wv, +g: Nat)
  -> {P.Wv.x(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, a, g)))
      == P.Z.add(P.Pos{0n}, P.Z.divc(P.Rot.crx(P.Wv.y(a), P.Wv.z(a), P.Pos{g}, P.Pos{0n}),
          P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a)))) : P.Z}:
  {==}

# 0 < b gives 0 < a + b
def lt_add_r(+a: Nat, q: Nat, h: {Nat.is_lt(0n, q) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(a, q)) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+p:
      {==}

# The sign of the kick each law asks for, from the press alone -- nothing
# of the turn about the contact.
def corner_sign_x(+s: Nat, +g: Nat, +q: P.Quat, +a: P.Wv,
  +off: {Nat.is_lt(0n, P.Z.mag(P.Wv.x(a))) == True{} : Bool},
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool})
  -> {P.Z.above(P.Z.mul(P.Wv.x(a), P.Wv.z(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, a, g)))), P.Pos{0n}) == True{} : Bool}:
  +d = {P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a)) : Nat}
  +divc = {P.Z.divc(P.Rot.crz(P.Wv.x(a), P.Wv.y(a), P.Pos{0n}, P.Pos{g}), d) : P.Z}
  +wz = {P.Wv.z(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, a, g))) : P.Z}
  +ew = Equal.trans(P.Z, wz, P.Z.add(P.Pos{0n}, divc), divc,
    wz_after_pressw0(q, s, a, g), Z_add_l_pos0(divc, kickzsign_mag(P.Wv.x(a), off, P.Wv.y(a), g, heavy, d)))
  Equal.trans(Bool, P.Z.above(P.Z.mul(P.Wv.x(a), wz), P.Pos{0n}), P.Z.above(P.Z.mul(P.Wv.x(a), divc), P.Pos{0n}), True{},
    Equal.cong(P.Z, Bool, (v: P.Z) => P.Z.above(P.Z.mul(P.Wv.x(a), v), P.Pos{0n}), wz, divc, ew),
    kickzsign(P.Wv.x(a), off, P.Wv.y(a), g, heavy, d, about_pos(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a))))

def corner_sign_z(+s: Nat, +g: Nat, +q: P.Quat, +a: P.Wv,
  +off: {Nat.is_lt(0n, P.Z.mag(P.Wv.z(a))) == True{} : Bool},
  +heavy: {Nat.is_lt(0n, g) == True{} : Bool})
  -> {P.Z.above(P.Pos{0n}, P.Z.mul(P.Wv.z(a), P.Wv.x(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, a, g))))) == True{} : Bool}:
  +d = {P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a)) : Nat}
  +divc = {P.Z.divc(P.Rot.crx(P.Wv.y(a), P.Wv.z(a), P.Pos{g}, P.Pos{0n}), d) : P.Z}
  +wx = {P.Wv.x(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, a, g))) : P.Z}
  +ew = Equal.trans(P.Z, wx, P.Z.add(P.Pos{0n}, divc), divc,
    wx_after_pressw0(q, s, a, g), Z_add_l_pos0(divc, kickxsign_mag(P.Wv.z(a), off, P.Wv.y(a), g, heavy, d)))
  Equal.trans(Bool, P.Z.above(P.Pos{0n}, P.Z.mul(P.Wv.z(a), wx)), P.Z.above(P.Pos{0n}, P.Z.mul(P.Wv.z(a), divc)), True{},
    Equal.cong(P.Z, Bool, (v: P.Z) => P.Z.above(P.Pos{0n}, P.Z.mul(P.Wv.z(a), v)), wx, divc, ew),
    kickxsign(P.Wv.z(a), off, P.Wv.y(a), g, heavy, d))

# The turning a cube at rest on its lowest point comes out of a whole tick
# with: exactly the press of the floor (Rot.pressw) -- Body.step sets it,
# and the turn about the contact never changes it (ROTW).
# The turning a cube at rest on its lowest point comes out of a whole tick
# with: the press of the floor (Rot.pressw) -- Body.step sets it -- or,
# where the turn about the contact is refused, half of it (Body.spin); so
# a fact about both is a fact about the turning the tick ends with (WP).
def corner_spin(+k: P.K, +x: Nat, +y: Nat, +z: Nat, +h: Bool, +q: P.Quat,
  +floor: {P.Geo.onfloor(P.K.size(k), y, q) == True{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.low(P.Rot.mat(q), P.K.size(k)))),
    P.Z.mag(P.Wv.z(P.Hold.low(P.Rot.mat(q), P.K.size(k)))))) == True{} : Bool},
  hstep: {P.Body.step(k, [], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}})
      == (P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{},
          P.Rot.pressw(P.Rot{q, P.Wv.zero()}, P.K.size(k), P.Hold.low(P.Rot.mat(q), P.K.size(k)), P.K.g(k))}, []) : P.Body & List<&2, P.Body>},
  -Pw: P.Wv -> Type,
  h0: Pw(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, P.K.size(k), P.Hold.low(P.Rot.mat(q), P.K.size(k)), P.K.g(k)))),
  h1: Pw(P.Wv.halfc(P.Rot.w(P.Rot.pressw(P.Rot{q, P.Wv.zero()}, P.K.size(k), P.Hold.low(P.Rot.mat(q), P.K.size(k)), P.K.g(k))))))
  -> Pw(P.Rot.w(P.Body.rot(P.Tick.body(P.Body.tick(k, [], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}}))))):
  +s = P.K.size(k)
  +g2 = P.K.g(k)
  +rt2 = {P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, P.Hold.low(P.Rot.mat(q), s), g2) : P.Rot}
  +body2 = {P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt2} : P.Body}
  e_turn = turn_wp(s, g2, [], body2, P.Rot.w(rt2), Pw, {==}, {==}, floor, htip, h0, h1)
  e_tick = Equal.cong(P.Body & List<&2, P.Body>, P.Wv,
    (r: P.Body & List<&2, P.Body>) => P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(s, g2, r)))),
    P.Body.step(k, [], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}}),
    (body2, []), hstep)
  %Equal.sym(P.Wv,
    P.Rot.w(P.Body.rot(P.Tick.body(P.Body.tick(k, [], P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}})))),
    P.Rot.w(P.Body.rot(P.Tick.turn(s, g2, [], body2))), e_tick) : Pw(_);
  e_turn

def Laws.on_a_corner_it_tips_x(k, heavy, x, y, z, h, q, floor, held, off):
  +s = P.K.size(k)
  +g2 = P.K.g(k)
  +arm = {P.Hold.low(P.Rot.mat(q), s) : P.Wv}
  +rt2 = {P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, arm, g2) : P.Rot}
  +b0 = {P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}} : P.Body}
  espin = corner_spin(k, x, y, z, h, q, floor,
    lt_add(P.Z.mag(P.Wv.x(arm)), P.Z.mag(P.Wv.z(arm)), off),
    step_pair(k, x, y, z, h, q, held, floor),
    (w: P.Wv) => {P.Z.above(P.Z.mul(P.Wv.x(arm), P.Wv.z(w)), P.Pos{0n}) == True{} : Bool},
    corner_sign_x(s, g2, q, arm, off, heavy),
    mulhalf_pos(P.Wv.x(arm), P.Wv.z(P.Rot.w(rt2)), corner_sign_x(s, g2, q, arm, off, heavy)))
  or_there(
    Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Body.tick(k, [], P.In.idle(), b0)))), q)),
    P.Z.above(P.Z.mul(P.Wv.x(arm), P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(P.Body.tick(k, [], P.In.idle(), b0)))))), P.Pos{0n}),
    espin)

def Laws.on_a_corner_it_tips_z(k, heavy, x, y, z, h, q, floor, held, off):
  +s = P.K.size(k)
  +g2 = P.K.g(k)
  +arm = {P.Hold.low(P.Rot.mat(q), s) : P.Wv}
  +rt2 = {P.Rot.pressw(P.Rot{q, P.Wv.zero()}, s, arm, g2) : P.Rot}
  +b0 = {P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, P.Rot{q, P.Wv.zero()}} : P.Body}
  espin = corner_spin(k, x, y, z, h, q, floor,
    lt_add_r(P.Z.mag(P.Wv.x(arm)), P.Z.mag(P.Wv.z(arm)), off),
    step_pair(k, x, y, z, h, q, held, floor),
    (w: P.Wv) => {P.Z.above(P.Pos{0n}, P.Z.mul(P.Wv.z(arm), P.Wv.x(w))) == True{} : Bool},
    corner_sign_z(s, g2, q, arm, off, heavy),
    mulhalf_neg(P.Wv.z(arm), P.Wv.x(P.Rot.w(rt2)), corner_sign_z(s, g2, q, arm, off, heavy)))
  or_there(
    Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Body.tick(k, [], P.In.idle(), b0)))), q)),
    P.Z.above(P.Pos{0n}, P.Z.mul(P.Wv.z(arm), P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(P.Body.tick(k, [], P.In.idle(), b0))))))),
    espin)

# The step at rest over one cube
# ------------------------------
# A body at rest, idle, on the ground flag, with one cube around it: the
# drive, the moves along x and z and the fall leave it where it is and
# press it by its hold against that cube. The moves have nowhere to go
# (the displacement is zero), but whether they find the cube in the way,
# and push it, depends on things this does not know; every way they can
# go ends at the same place, the cube keeping its place and turn (a push
# only changes its velocity).

# a search over nothing ends at nothing, whatever the probe says
def step_bis0(fit: Bool, +axis: Nat, +dir: P.Z, +s: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat)
  -> {P.Tick.bis(0n, fit, axis, dir, s, obs, x, y, z, q, 0n, 0n, 0n) == 0n : Nat}:
  match fit:
    case True{}:
      {==}
    case False{}:
      {==}

def step_slide0(+axis: Nat, +s: Nat, +o: P.Body, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat)
  -> {P.Tick.slide(axis, s, [o], x, y, z, q, P.Pos{0n}) == 0n : Nat}:
  step_bis0(P.Probe.at(axis, s, [o], x, y, z, q, P.Z.like(P.Pos{0n}, P.Tick.half(0n, 0n))), axis, P.Pos{0n}, s, [o], x, y, z, q)

def step_xto(+s: Nat, +o: P.Body, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat)
  -> {P.Move.xto(s, [o], P.Pos{0n}, x, y, z, q) == x : Nat}:
  %Equal.sym(Nat, P.Tick.slide(0n, s, [o], x, y, z, q, P.Pos{0n}), 0n, step_slide0(0n, s, o, x, y, z, q))
    : {Nat.add(x, _) == x : Nat}
  R.add_zero(x)

def step_zto(+s: Nat, +o: P.Body, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat)
  -> {P.Move.zto(s, [o], P.Pos{0n}, x, y, z, q) == z : Nat}:
  %Equal.sym(Nat, P.Tick.slide(2n, s, [o], x, y, z, q, P.Pos{0n}), 0n, step_slide0(2n, s, o, x, y, z, q))
    : {Nat.add(z, _) == z : Nat}
  R.add_zero(z)

# whether a body sinks onto a cube does not ask how the cube moves
def step_sinks_v(+s: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +a1: P.Z, +b1: P.Z, +c1: P.Z, +a2: P.Z, +b2: P.Z, +c2: P.Z,
  +og: Bool, +oh: Bool, +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat)
  -> {P.Tick.sinks(s, [P.Body{ox, oy, oz, a1, b1, c1, og, oh, ort}], x, y, z, q)
      == P.Tick.sinks(s, [P.Body{ox, oy, oz, a2, b2, c2, og, oh, ort}], x, y, z, q) : Bool}:
  {==}

# what the step leaves, for any velocities it gives the body and the cube
def step_H(+s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +og: Bool, +oh: Bool, +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat,
  +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type) -> Type:
  @vx2:P.Z -> @vy2:P.Z -> @vz2:P.Z -> @h2:Bool -> @w1:P.Z -> @w2:P.Z -> @w3:P.Z ->
    R((P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, P.Rot.held(False{}, rt, s, x, y, z, g, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])},
      [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))

# the fall: held (it does not sink onto the cube) and off the floor, the body keeps its place and the hold presses it
def step_y(+s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +ovy: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vz: P.Z, +h2: Bool, +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type,
  held2: {P.Tick.sinks(s, [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: R((P.Body{x, y, z, vx, P.Pos{0n}, vz, True{}, h2,
      P.Rot.held(False{}, rt, s, x, y, z, g, [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}])},
    [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}])))
  -> R(P.Tick.y(s, g, (P.Body{x, y, z, vx, P.Pos{0n}, vz, True{}, h2, rt}, [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}]))):
  %Equal.sym(Bool, P.Tick.sinks(s, [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}], x, y, z, P.Rot.q(rt)), False{}, held2)
    : R((P.Move.stay(Bool.not(_), s, g, [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}], x, y, z, vx, P.Pos{0n}, vz, h2, rt),
      [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}]))
  %Equal.sym(Bool, P.Geo.onfloor(s, y, P.Rot.q(rt)), False{}, off)
    : R((P.Body{x, y, z, vx, P.Pos{0n}, vz, True{}, h2,
        P.Rot.held(_, rt, s, x, y, z, g, [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}])},
      [P.Body{ox, oy, oz, w1, ovy, w3, og, oh, ort}]))
  hp

# held over the cube as it was is held over the cube with other velocities
def step_held(+s: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +a: P.Z, +c: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, q) == False{} : Bool})
  -> {P.Tick.sinks(s, [P.Body{ox, oy, oz, a, ovy, c, og, oh, ort}], x, y, z, q) == False{} : Bool}:
  Equal.trans(Bool, P.Tick.sinks(s, [P.Body{ox, oy, oz, a, ovy, c, og, oh, ort}], x, y, z, q),
    P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, q), False{},
    step_sinks_v(s, ox, oy, oz, a, ovy, c, ovx, ovy, ovz, og, oh, ort, x, y, z, q), held)

# the move along z that found the way blocked and did not touch: in place, whether it could put the body there or not
def step_zput(ok: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, +w1: P.Z, +vx: P.Z, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.y(s, g, P.Move.zput(ok, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}], z, x, y, z, vx, P.Pos{0n}, P.Pos{0n}, True{}, rt))):
  match ok:
    case True{}:
      step_y(s, g, ox, oy, oz, w1, ovy, ovz, og, oh, ort, x, y, z, vx, P.Pos{0n}, True{}, rt, R,
        step_held(s, ox, oy, oz, ovx, ovy, ovz, w1, ovz, og, oh, ort, x, y, z, P.Rot.q(rt), held), off,
        hp(vx, P.Pos{0n}, P.Pos{0n}, True{}, w1, ovy, ovz))
    case False{}:
      step_y(s, g, ox, oy, oz, w1, ovy, ovz, og, oh, ort, x, y, z, vx, P.Pos{0n}, True{}, rt, R,
        step_held(s, ox, oy, oz, ovx, ovy, ovz, w1, ovz, og, oh, ort, x, y, z, P.Rot.q(rt), held), off,
        hp(vx, P.Pos{0n}, P.Pos{0n}, True{}, w1, ovy, ovz))

# the push along z of the cube: it gets w2, the body v2, both stay where they are
def step_zp(vw: P.Z & P.Z, +at: Nat, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool,
  +oh: Bool, +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, +w1: P.Z, +vx: P.Z, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.y(s, g, P.Move.zpushed(P.Push.zput(vw, at, ox, oy, oz, w1, ovy, og, oh, [], ort), x, y, z, vx, P.Pos{0n}, True{}, rt))):
  match vw:
    case (+v2, +w2):
      step_y(s, g, ox, oy, oz, w1, ovy, w2, og, oh, ort, x, y, z, vx, v2, True{}, rt, R,
        step_held(s, ox, oy, oz, ovx, ovy, ovz, w1, w2, og, oh, ort, x, y, z, P.Rot.q(rt), held), off,
        hp(vx, P.Pos{0n}, v2, True{}, w1, ovy, w2))

def step_zh(here: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, +w1: P.Z, +vx: P.Z, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.y(s, g, P.Move.zpushed(P.Push.z(s, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}], P.Pos{0n}, x, y, Nat.add(z, 1n),
      P.Pos{0n}, P.Rot.q(rt), here), x, y, z, vx, P.Pos{0n}, True{}, rt))):
  match here:
    case True{}:
      step_zp(P.Push.share(P.Push.closing(P.Pos{0n}, P.Pos{0n}, ovz), P.Pos{0n}, ovz), P.Push.stop(s, P.Pos{0n}, oz),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, w1, vx, R, held, off, hp)
    case False{}:
      step_y(s, g, ox, oy, oz, w1, ovy, ovz, og, oh, ort, x, y, z, vx, P.Pos{0n}, True{}, rt, R,
        step_held(s, ox, oy, oz, ovx, ovy, ovz, w1, ovz, og, oh, ort, x, y, z, P.Rot.q(rt), held), off,
        hp(vx, P.Pos{0n}, P.Pos{0n}, True{}, w1, ovy, ovz))

def step_zt(touch: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, +w1: P.Z, +vx: P.Z, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.y(s, g, P.Move.ztouch(touch, s, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}], P.Pos{0n}, z, Nat.add(z, 1n),
      x, y, z, vx, P.Pos{0n}, P.Pos{0n}, True{}, rt))):
  match touch:
    case True{}:
      step_zh(P.Geo.head(s, x, y, Nat.add(z, 1n), P.Rot.q(rt), [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}]),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, w1, vx, R, held, off, hp)
    case False{}:
      step_zput(P.Geo.free(s, x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}]),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, w1, vx, R, held, off, hp)

def step_zgo(fr: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, +w1: P.Z, +vx: P.Z, +h1: Bool, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.y(s, g, P.Move.zgo(s, fr, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}], P.Pos{0n}, Nat.add(z, 0n),
      P.Body{x, y, z, vx, P.Pos{0n}, P.Pos{0n}, True{}, h1, rt}))):
  match fr:
    case True{}:
      %Equal.sym(Nat, Nat.add(z, 0n), z, R.add_zero(z))
        : R(P.Tick.y(s, g, (P.Body{x, y, _, vx, P.Pos{0n}, P.Pos{0n}, True{}, h1, rt}, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}])))
      step_y(s, g, ox, oy, oz, w1, ovy, ovz, og, oh, ort, x, y, z, vx, P.Pos{0n}, h1, rt, R,
        step_held(s, ox, oy, oz, ovx, ovy, ovz, w1, ovz, og, oh, ort, x, y, z, P.Rot.q(rt), held), off,
        hp(vx, P.Pos{0n}, P.Pos{0n}, h1, w1, ovy, ovz))
    case False{}:
      %Equal.sym(Nat, P.Move.zto(s, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}], P.Pos{0n}, x, y, z, P.Rot.q(rt)), z,
          step_zto(s, P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}, x, y, z, P.Rot.q(rt)))
        : R(P.Tick.y(s, g, P.Move.zreach(s, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}], P.Pos{0n}, _, x, y, z, vx, P.Pos{0n},
            P.Pos{0n}, True{}, rt)))
      step_zt(P.Move.ztouches(s, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}], P.Pos{0n}, x, y, z, P.Rot.q(rt)),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, w1, vx, R, held, off, hp)

# the move along z and the fall, after the move along x left the body in place
def step_z(+s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, +w1: P.Z, +vx: P.Z, +h1: Bool, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.z(s, g, P.Pos{0n}, (P.Body{x, y, z, vx, P.Pos{0n}, P.Pos{0n}, True{}, h1, rt}, [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}]))):
  step_zgo(P.Geo.free(s, x, y, Nat.add(z, 0n), P.Rot.q(rt), [P.Body{ox, oy, oz, w1, ovy, ovz, og, oh, ort}]),
    s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, w1, vx, h1, R, held, off, hp)

# the move along x that found the way blocked and did not touch: in place
def step_xput(ok: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.z(s, g, P.Pos{0n}, P.Move.xput(ok, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, x, y, z, P.Pos{0n}, P.Pos{0n},
      P.Pos{0n}, True{}, rt))):
  match ok:
    case True{}:
      step_z(s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, ovx, P.Pos{0n}, True{}, R, held, off, hp)
    case False{}:
      step_z(s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, ovx, P.Pos{0n}, True{}, R, held, off, hp)

# the push along x of the cube: it gets w2, the body v2, both stay where they are
def step_xp(vw: P.Z & P.Z, +at: Nat, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool,
  +oh: Bool, +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.z(s, g, P.Pos{0n}, P.Move.xpushed(P.Push.xput(vw, at, ox, oy, oz, ovy, ovz, og, oh, [], ort), x, y, z, P.Pos{0n},
      P.Pos{0n}, True{}, rt))):
  match vw:
    case (+v2, +w2):
      step_z(s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, w2, v2, True{}, R, held, off, hp)

def step_xh(here: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.z(s, g, P.Pos{0n}, P.Move.xpushed(P.Push.x(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.Pos{0n}, Nat.add(x, 1n),
      y, z, P.Pos{0n}, P.Rot.q(rt), here), x, y, z, P.Pos{0n}, P.Pos{0n}, True{}, rt))):
  match here:
    case True{}:
      step_xp(P.Push.share(P.Push.closing(P.Pos{0n}, P.Pos{0n}, ovx), P.Pos{0n}, ovx), P.Push.stop(s, P.Pos{0n}, ox),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, R, held, off, hp)
    case False{}:
      step_z(s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, ovx, P.Pos{0n}, True{}, R, held, off, hp)

def step_xt(touch: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.z(s, g, P.Pos{0n}, P.Move.xtouch(touch, s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.Pos{0n}, x, Nat.add(x, 1n),
      x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, rt))):
  match touch:
    case True{}:
      step_xh(P.Geo.head(s, Nat.add(x, 1n), y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}]),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, R, held, off, hp)
    case False{}:
      step_xput(P.Geo.free(s, x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}]),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, R, held, off, hp)

def step_x(fr: Bool, +s: Nat, +g: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool,
  +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(s, y, P.Rot.q(rt)) == False{} : Bool},
  hp: step_H(s, g, ox, oy, oz, og, oh, ort, x, y, z, rt, R))
  -> R(P.Tick.z(s, g, P.Pos{0n}, P.Move.xgo(s, fr, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.Pos{0n}, Nat.add(x, 0n),
      P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt}))):
  match fr:
    case True{}:
      %Equal.sym(Nat, Nat.add(x, 0n), x, R.add_zero(x))
        : R(P.Tick.z(s, g, P.Pos{0n}, (P.Body{_, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt},
            [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}])))
      step_z(s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, ovx, P.Pos{0n}, False{}, R, held, off, hp)
    case False{}:
      %Equal.sym(Nat, P.Move.xto(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.Pos{0n}, x, y, z, P.Rot.q(rt)), x,
          step_xto(s, P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}, x, y, z, P.Rot.q(rt)))
        : R(P.Tick.z(s, g, P.Pos{0n}, P.Move.xreach(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.Pos{0n}, _, x, y, z,
            P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, rt)))
      step_xt(P.Move.xtouches(s, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.Pos{0n}, x, y, z, P.Rot.q(rt)),
        s, g, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, R, held, off, hp)

# The step at rest over one cube, for any claim R about what it leaves:
# enough that R holds of the body in place, pressed by its hold, and the
# cube in place, whatever velocities the moves gave them.
def step_o(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +h: Bool, +rt: P.Rot, -R: (P.Body & List<&2, P.Body>) -> Type,
  held: {P.Tick.sinks(P.K.size(k), [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt)) == False{} : Bool},
  hp: @vx2:P.Z -> @vy2:P.Z -> @vz2:P.Z -> @h2:Bool -> @w1:P.Z -> @w2:P.Z -> @w3:P.Z ->
    R((P.Body{x, y, z, vx2, vy2, vz2, True{}, h2,
        P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])},
       [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))
  -> R(P.Body.step(k, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.In.idle(),
       P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})):
  %Equal.sym(P.Body, P.Body.drive(k, P.In.idle(), P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt}),
      P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}, rt}, drive_idle0(k, x, y, z, h, rt))
    : R(P.Tick.z(P.K.size(k), P.K.g(k), P.Pos{0n}, P.Move.x(P.K.size(k), [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.Pos{0n}, _)))
  step_x(P.Geo.free(P.K.size(k), Nat.add(x, 0n), y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}]),
    P.K.size(k), P.K.g(k), ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, rt, R, held, off, hp)


# The spin the step made survives the turn off the floor too: standing on
# a cube (held, but not on the floor), the turn pivots about the arm the
# hold gives (Hold.arm on the foot), and the search under it never touches
# the spin -- the same ROTW argument as on the floor.
# ---------------------------------------------------------------------------

def spo_turn2(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat, +w0: P.Wv, -Pw: P.Wv -> Type,
  +hrt: {P.Rot.w(rt) == w0 : P.Wv},
  +hheld: {held == True{} : Bool}, +hfloor: {floor == False{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(
    P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))),
    P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)):
  match held floor:
    case False{} _:
      Empty.absurd(WP(Pw, P.Tick.place(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2)), clash2(hheld))
    case True{} False{}:
      pivota_wp(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2,
        P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s), w0, Pw, hrt, htip, h0, h1)
    case True{} True{}:
      Empty.absurd(WP(Pw, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2,
        P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))), clash(hfloor))

def spo_turn1b(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == False{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(
    P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn1b(s, g, obs, b)):
  match b:
    case P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      spo_turn2(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
        P.Rot.free(rt), P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), w0, Pw,
        hb, hgr, hfloor, htip, h0, h1)

def spo_turn1(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == False{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(
    P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn1(still, s, g, obs, b)):
  match still:
    case True{}:
      %Equal.sym(P.Wv, P.Rot.w(P.Body.rot(b)), w0, hb) : Pw(_);
      h0
    case False{}:
      spo_turn1b(s, g, obs, b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)

def spo_turn0(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == False{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(
    P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn0(s, g, obs, b)):
  spo_turn1(P.Wv.null(P.Rot.w(P.Body.rot(b))), s, g, obs, b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)

def spo_turn(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +b: P.Body, +w0: P.Wv, -Pw: P.Wv -> Type,
  hb: ROTW(w0, b),
  +hgr: {P.Body.ground(b) == True{} : Bool},
  +hfloor: {P.Geo.onfloor(s, P.Body.y(b), P.Rot.q(P.Body.rot(b))) == False{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(
    P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))),
    P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(s, P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Rot.q(P.Body.rot(b)), obs, P.Foot.none()),
      P.Rot.mat(P.Rot.q(P.Body.rot(b))), s))))) == True{} : Bool},
  h0: Pw(w0), h1: Pw(P.Wv.halfc(w0)))
  -> WP(Pw, P.Tick.turn(s, g, obs, b)):
  match obs:
    case []:
      spo_turn0(s, g, [], b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)
    case o <> rest:
      spo_turn0(s, g, o <> rest, b, w0, Pw, hb, hgr, hfloor, htip, h0, h1)

# The whole turn of a tick, one cube in the way, off the floor: what holds
# of the spin the step left and of its half holds of the spin the tick
# ends with.
def spin_o(+s: Nat, +g: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z, +vz: P.Z, +h: Bool, +rt2: P.Rot, +o: P.Body,
  -Pw: P.Wv -> Type,
  +off: {P.Geo.onfloor(s, y, P.Rot.q(rt2)) == False{} : Bool},
  +htip: {Nat.is_lt(0n, Nat.add(
      P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt2), [o], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), s))),
      P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt2), [o], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), s))))) == True{} : Bool},
  h0: Pw(P.Rot.w(rt2)), h1: Pw(P.Wv.halfc(P.Rot.w(rt2))))
  -> Pw(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(s, g, (P.Body{x, y, z, vx, vy, vz, True{}, h, rt2}, [o])))))):
  spo_turn(s, g, [o], P.Body{x, y, z, vx, vy, vz, True{}, h, rt2}, P.Rot.w(rt2), Pw, {==}, {==}, off, htip, h0, h1)


# Past the edge: the sign of the arm along x, and so of the turning about z
# ==========================================================================
# A cube standing on one cube, off the floor, is pressed at its lowest point
# held inside the foot (Hold.arm, Geo.leanf). Past the +x edge of the cube
# under it (ox + s < x + s/2) both ends of the foot along x sit behind its
# middle, so the arm points -x: the press turns it about -z. Past the -x
# edge (x + s/2 < ox) the foot's low end already lies ahead of the middle,
# so the arm points +x and it turns about +z. Only the foot's bounds along
# x decide it, never the quaternion. Used by past_the_edge_it_tips_px/_nx
# and tipping_is_never_thrown_away_px/_nx.
# ---------------------------------------------------------------------------

def sgx_lt_irrefl(+x: Nat) -> {Nat.is_lt(x, x) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      sgx_lt_irrefl(p)

def sgx_lt_asym(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n _:
      lt_zero_r(b)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+ap) == False{} : Bool}, clash2(h))
    case 1n+ap 1n+bp:
      sgx_lt_asym(ap, bp, h)

def sgx_le_lt.go(+y: Nat, +z: Nat, +x: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool})
  -> {Nat.is_lt(x, z) == True{} : Bool}:
  match y:
    case 0n:
      match x:
        case 0n:
          h2
        case 1n+xp:
          Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, clash2(h1))
    case 1n+yp:
      match z:
        case 0n:
          Empty.absurd({Nat.is_lt(x, 0n) == True{} : Bool}, clash2(h2))
        case 1n+zp:
          match x:
            case 0n:
              {==}
            case 1n+xp:
              sgx_le_lt.go(yp, zp, xp, h1, h2)

# x <= y < z gives x < z
def sgx_le_lt(+x: Nat, +y: Nat, +z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool})
  -> {Nat.is_lt(x, z) == True{} : Bool}:
  sgx_le_lt.go(y, z, x, h1, h2)

def sgx_lt_le.go(+y: Nat, +z: Nat, +x: Nat, h1: {Nat.is_lt(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool})
  -> {Nat.is_lt(x, z) == True{} : Bool}:
  match y:
    case 0n:
      Empty.absurd({Nat.is_lt(x, z) == True{} : Bool},
        clash2(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, lt_zero_r(x)), h1)))
    case 1n+yp:
      match z:
        case 0n:
          Empty.absurd({Nat.is_lt(x, 0n) == True{} : Bool}, clash2(h2))
        case 1n+zp:
          match x:
            case 0n:
              {==}
            case 1n+xp:
              sgx_lt_le.go(yp, zp, xp, h1, h2)

# x < y <= z gives x < z
def sgx_lt_le(+x: Nat, +y: Nat, +z: Nat, h1: {Nat.is_lt(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool})
  -> {Nat.is_lt(x, z) == True{} : Bool}:
  sgx_lt_le.go(y, z, x, h1, h2)

def sgx_lt_trans(+x: Nat, +y: Nat, +z: Nat, h1: {Nat.is_lt(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool})
  -> {Nat.is_lt(x, z) == True{} : Bool}:
  sgx_lt_le(x, y, z, h1, lt_true_le(y, z, h2))

# 0 < h gives x < x + h
def sgx_lt_add_self(+x: Nat, +h: Nat, hh: {Nat.is_lt(0n, h) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(x, h)) == True{} : Bool}:
  match x:
    case 0n:
      hh
    case 1n+p:
      sgx_lt_add_self(p, h, hh)

# x < x + h gives 0 < h
def sgx_pos_of_lt_add(+x: Nat, +h: Nat, e: {Nat.is_lt(x, Nat.add(x, h)) == True{} : Bool}) -> {Nat.is_lt(0n, h) == True{} : Bool}:
  match x:
    case 0n:
      e
    case 1n+p:
      sgx_pos_of_lt_add(p, h, e)

def sgx_sub_lt.go(+x: Nat, +u: Nat, +h: Nat, hu: {Nat.is_lt(u, Nat.add(x, h)) == True{} : Bool},
  hh: {Nat.is_lt(0n, h) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(u, x), h) == True{} : Bool}:
  match x:
    case 0n:
      match u:
        case 0n:
          hu
        case 1n+up:
          hu
    case 1n+xp:
      match u:
        case 0n:
          hh
        case 1n+up:
          sgx_sub_lt.go(xp, up, h, hu, hh)

# u < x + h and 0 < h give u - x < h
def sgx_sub_lt(+u: Nat, +x: Nat, +h: Nat, hu: {Nat.is_lt(u, Nat.add(x, h)) == True{} : Bool},
  hh: {Nat.is_lt(0n, h) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(u, x), h) == True{} : Bool}:
  sgx_sub_lt.go(x, u, h, hu, hh)

def sgx_sub_gt.go(+x: Nat, +u: Nat, +h: Nat, hu: {Nat.is_lt(Nat.add(x, h), u) == True{} : Bool})
  -> {Nat.is_lt(h, Nat.sub(u, x)) == True{} : Bool}:
  match x:
    case 0n:
      match u:
        case 0n:
          hu
        case 1n+up:
          hu
    case 1n+xp:
      match u:
        case 0n:
          Empty.absurd({Nat.is_lt(h, Nat.sub(0n, 1n+xp)) == True{} : Bool}, clash2(hu))
        case 1n+up:
          sgx_sub_gt.go(xp, up, h, hu)

# x + h < u gives h < u - x
def sgx_sub_gt(+u: Nat, +x: Nat, +h: Nat, hu: {Nat.is_lt(Nat.add(x, h), u) == True{} : Bool})
  -> {Nat.is_lt(h, Nat.sub(u, x)) == True{} : Bool}:
  sgx_sub_gt.go(x, u, h, hu)

# 0 < a - b gives b < a
def sgx_lt_of_sub(+a: Nat, +b: Nat, h: {Nat.is_lt(0n, Nat.sub(a, b)) == True{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, clash2(h))
        case 1n+bp:
          Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, clash2(h))
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          sgx_lt_of_sub(ap, bp, h)

# a - d <= a
def sgx_sub_le(+a: Nat, +d: Nat) -> {Nat.is_le(Nat.sub(a, d), a) == True{} : Bool}:
  match a:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+dp:
          {==}
    case 1n+ap:
      match d:
        case 0n:
          le_refl(1n+ap)
        case 1n+dp:
          le_succ(Nat.sub(ap, dp), ap, sgx_sub_le(ap, dp))

def sgx_sub_lt_self.go(+n: Nat, +m: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, hle: {Nat.is_le(n, m) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(m, n), m) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(m, 0n), m) == True{} : Bool}, clash2(hn))
    case 1n+np:
      match m:
        case 0n:
          Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+np), 0n) == True{} : Bool}, clash2(hle))
        case 1n+mp:
          le_to_lt_s(Nat.sub(mp, np), mp, sgx_sub_le(mp, np))

# 0 < n <= m gives m - n < m
def sgx_sub_lt_self(+m: Nat, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, hle: {Nat.is_le(n, m) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(m, n), m) == True{} : Bool}:
  sgx_sub_lt_self.go(n, m, hn, hle)

# Pick.low and Pick.high, bounded
# -------------------------------

def sgx_low_le_r.go(c: Bool, +a: Nat, +b: Nat, hc: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(P.Pick.n(c, a, b), b) == True{} : Bool}:
  match c:
    case True{}:
      hc
    case False{}:
      le_refl(b)

def sgx_low_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(P.Pick.low(a, b), b) == True{} : Bool}:
  sgx_low_le_r.go(Nat.is_le(a, b), a, b, {==})

def sgx_low_le_l.go(c: Bool, +a: Nat, +b: Nat, hc: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(P.Pick.n(c, a, b), a) == True{} : Bool}:
  match c:
    case True{}:
      le_refl(a)
    case False{}:
      le_flip(a, b, hc)

def sgx_low_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(P.Pick.low(a, b), a) == True{} : Bool}:
  sgx_low_le_l.go(Nat.is_le(a, b), a, b, {==})

def sgx_high_ge_l.go(c: Bool, +a: Nat, +b: Nat, hc: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(a, P.Pick.n(c, b, a)) == True{} : Bool}:
  match c:
    case True{}:
      hc
    case False{}:
      le_refl(a)

def sgx_high_ge_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, P.Pick.high(a, b)) == True{} : Bool}:
  sgx_high_ge_l.go(Nat.is_le(a, b), a, b, {==})

def sgx_high_ge_r.go(c: Bool, +a: Nat, +b: Nat, hc: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(b, P.Pick.n(c, b, a)) == True{} : Bool}:
  match c:
    case True{}:
      le_refl(b)
    case False{}:
      le_flip(a, b, hc)

def sgx_high_ge_r(+a: Nat, +b: Nat) -> {Nat.is_le(b, P.Pick.high(a, b)) == True{} : Bool}:
  sgx_high_ge_r.go(Nat.is_le(a, b), a, b, {==})

def sgx_high_lt.go(c: Bool, +u: Nat, +w: Nat, +t: Nat, hu: {Nat.is_lt(u, t) == True{} : Bool},
  hw: {Nat.is_lt(w, t) == True{} : Bool}) -> {Nat.is_lt(P.Pick.n(c, w, u), t) == True{} : Bool}:
  match c:
    case True{}:
      hw
    case False{}:
      hu

# both under t: so is the higher
def sgx_high_lt(+u: Nat, +w: Nat, +t: Nat, hu: {Nat.is_lt(u, t) == True{} : Bool}, hw: {Nat.is_lt(w, t) == True{} : Bool})
  -> {Nat.is_lt(P.Pick.high(u, w), t) == True{} : Bool}:
  sgx_high_lt.go(Nat.is_le(u, w), u, w, t, hu, hw)

def sgx_high_le.go(c: Bool, +u: Nat, +w: Nat, +t: Nat, hu: {Nat.is_le(u, t) == True{} : Bool},
  hw: {Nat.is_le(w, t) == True{} : Bool}) -> {Nat.is_le(P.Pick.n(c, w, u), t) == True{} : Bool}:
  match c:
    case True{}:
      hw
    case False{}:
      hu

def sgx_high_le(+u: Nat, +w: Nat, +t: Nat, hu: {Nat.is_le(u, t) == True{} : Bool}, hw: {Nat.is_le(w, t) == True{} : Bool})
  -> {Nat.is_le(P.Pick.high(u, w), t) == True{} : Bool}:
  sgx_high_le.go(Nat.is_le(u, w), u, w, t, hu, hw)

def sgx_low_ge.go(c: Bool, +u: Nat, +w: Nat, +t: Nat, hu: {Nat.is_le(t, u) == True{} : Bool},
  hw: {Nat.is_le(t, w) == True{} : Bool}) -> {Nat.is_le(t, P.Pick.n(c, u, w)) == True{} : Bool}:
  match c:
    case True{}:
      hu
    case False{}:
      hw

# t under both: so it is under the lower
def sgx_low_ge(+u: Nat, +w: Nat, +t: Nat, hu: {Nat.is_le(t, u) == True{} : Bool}, hw: {Nat.is_le(t, w) == True{} : Bool})
  -> {Nat.is_le(t, P.Pick.low(u, w)) == True{} : Bool}:
  sgx_low_ge.go(Nat.is_le(u, w), u, w, t, hu, hw)

def sgx_lt_high_inv.go(c: Bool, +hi: Nat, +lo: Nat, h: {Nat.is_lt(lo, P.Pick.n(c, lo, hi)) == True{} : Bool})
  -> {Nat.is_lt(lo, hi) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Nat.is_lt(lo, hi) == True{} : Bool},
        clash2(Equal.trans(Bool, False{}, Nat.is_lt(lo, lo), True{}, Equal.sym(Bool, Nat.is_lt(lo, lo), False{}, sgx_lt_irrefl(lo)), h)))
    case False{}:
      h

# lo < high(hi, lo) gives lo < hi
def sgx_lt_high_inv(+hi: Nat, +lo: Nat, h: {Nat.is_lt(lo, P.Pick.high(hi, lo)) == True{} : Bool}) -> {Nat.is_lt(lo, hi) == True{} : Bool}:
  sgx_lt_high_inv.go(Nat.is_le(hi, lo), hi, lo, h)

# lo < hi gives a gap: 0 < high(hi, lo) - lo
def sgx_gap_pos(+lo: Nat, +hi: Nat, h: {Nat.is_lt(lo, hi) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.sub(P.Pick.high(hi, lo), lo)) == True{} : Bool}:
  lt_sub(lo, P.Pick.high(hi, lo), sgx_lt_le(lo, hi, P.Pick.high(hi, lo), h, sgx_high_ge_l(hi, lo)))

# Overlaps
# --------

# a positive overlap: the higher start is below the lower end
def sgx_lap_ends(+s: Nat, +a: Nat, +b: Nat, h: {Nat.is_lt(0n, P.Geo.lap(s, a, b)) == True{} : Bool})
  -> {Nat.is_lt(P.Pick.high(a, b), P.Pick.low(Nat.add(a, s), Nat.add(b, s))) == True{} : Bool}:
  sgx_lt_high_inv(P.Pick.low(Nat.add(a, s), Nat.add(b, s)), P.Pick.high(a, b),
    sgx_lt_of_sub(P.Pick.high(P.Pick.low(Nat.add(a, s), Nat.add(b, s)), P.Pick.high(a, b)), P.Pick.high(a, b), h))

# the widened overlap is no smaller: 0 < lap gives 0 < lapd, whatever the widening d
def sgx_lapd_pos(+s: Nat, +d: Nat, +a: Nat, +b: Nat, h: {Nat.is_lt(0n, P.Geo.lap(s, a, b)) == True{} : Bool})
  -> {Nat.is_lt(0n, P.Geo.lapd(s, d, a, b)) == True{} : Bool}:
  +lo0 = P.Pick.high(a, b)
  +hi0 = P.Pick.low(Nat.add(a, s), Nat.add(b, s))
  +lo1 = P.Pick.high(Nat.sub(a, d), b)
  +hi1 = P.Pick.low(Nat.add(Nat.add(a, s), d), Nat.add(b, s))
  sgx_gap_pos(lo1, hi1,
    sgx_le_lt(lo1, lo0, hi1,
      sgx_high_le(Nat.sub(a, d), b, lo0, le_trans(Nat.sub(a, d), a, lo0, sgx_sub_le(a, d), sgx_high_ge_l(a, b)), sgx_high_ge_r(a, b)),
      sgx_lt_le(lo0, hi0, hi1, sgx_lap_ends(s, a, b, h),
        sgx_low_ge(Nat.add(Nat.add(a, s), d), Nat.add(b, s), hi0,
          le_trans(hi0, Nat.add(a, s), Nat.add(Nat.add(a, s), d), sgx_low_le_l(Nat.add(a, s), Nat.add(b, s)), le_add(Nat.add(a, s), d)),
          sgx_low_le_r(Nat.add(a, s), Nat.add(b, s))))))

# The arm
# -------

# the point held in [lo, hi], as an arm from c: behind c when both ends are
def sgx_leanf_neg(+c: Nat, +a: Nat, +lo: Nat, +hi: Nat, hlo: {Nat.is_lt(lo, c) == True{} : Bool},
  hhi: {Nat.is_lt(hi, c) == True{} : Bool}) -> {P.Z.above(P.Pos{0n}, P.Geo.leanf(c, a, lo, hi)) == True{} : Bool}:
  +p = P.Pick.high(P.Pick.low(a, hi), lo)
  +hp = sgx_high_lt(P.Pick.low(a, hi), lo, c, sgx_le_lt(P.Pick.low(a, hi), hi, c, sgx_low_le_r(a, hi), hhi), hlo)
  %Equal.sym(Bool, Nat.is_lt(p, c), True{}, hp) : {P.Z.above(P.Pos{0n}, P.Z.diff(_, p, c)) == True{} : Bool}
  lt_sub(p, c, hp)

# ... ahead of c when the low end is
def sgx_leanf_pos(+c: Nat, +a: Nat, +lo: Nat, +hi: Nat, hlo: {Nat.is_lt(c, lo) == True{} : Bool})
  -> {P.Z.above(P.Geo.leanf(c, a, lo, hi), P.Pos{0n}) == True{} : Bool}:
  +p = P.Pick.high(P.Pick.low(a, hi), lo)
  +hp = sgx_lt_le(c, lo, p, hlo, sgx_high_ge_r(P.Pick.low(a, hi), lo))
  %Equal.sym(Bool, Nat.is_lt(p, c), False{}, sgx_lt_asym(c, p, hp)) : {P.Z.above(P.Z.diff(_, p, c), P.Pos{0n}) == True{} : Bool}
  lt_sub(c, p, hp)

def sgx_armx_neg(+n: Nat, +lx: Nat, +hx: Nat, +lz: Nat, +hz: Nat, +ty: Nat, +m: P.Mat, +s: Nat,
  hlx: {Nat.is_lt(lx, Nat.div(s, 2n)) == True{} : Bool}, hhx: {Nat.is_lt(hx, Nat.div(s, 2n)) == True{} : Bool})
  -> {P.Z.above(P.Pos{0n}, P.Wv.x(P.Hold.arm(P.Foot{n, lx, hx, lz, hz, ty}, m, s))) == True{} : Bool}:
  sgx_leanf_neg(Nat.div(s, 2n), P.Z.slide(Nat.div(s, 2n), P.Wv.x(P.Hold.low(m, s))), lx, hx, hlx, hhx)

def sgx_armx_pos(+n: Nat, +lx: Nat, +hx: Nat, +lz: Nat, +hz: Nat, +ty: Nat, +m: P.Mat, +s: Nat,
  hlx: {Nat.is_lt(Nat.div(s, 2n), lx) == True{} : Bool})
  -> {P.Z.above(P.Wv.x(P.Hold.arm(P.Foot{n, lx, hx, lz, hz, ty}, m, s)), P.Pos{0n}) == True{} : Bool}:
  sgx_leanf_pos(Nat.div(s, 2n), P.Z.slide(Nat.div(s, 2n), P.Wv.x(P.Hold.low(m, s))), lx, hx, hlx)

# Geo.foot's last step either way it goes, on the cube or on nothing
def sgx_foot2_xneg(on: Bool, +s: Nat, +dx: Nat, +dz: Nat, +x: Nat, +z: Nat, +ox: Nat, +oz: Nat, +top: Nat, +m: P.Mat,
  hlo: {Nat.is_lt(P.Geo.laplw(s, dx, x, ox), Nat.div(s, 2n)) == True{} : Bool},
  hhi: {Nat.is_lt(P.Geo.laphw(s, dx, x, ox), Nat.div(s, 2n)) == True{} : Bool},
  +hh: {Nat.is_lt(0n, Nat.div(s, 2n)) == True{} : Bool})
  -> {P.Z.above(P.Pos{0n}, P.Wv.x(P.Hold.arm(P.Geo.foot2(on, True{}, s, dx, dz, x, z, ox, oz, top, P.Foot.none()), m, s))) == True{} : Bool}:
  match on:
    case True{}:
      sgx_armx_neg(1n, P.Geo.laplw(s, dx, x, ox), P.Geo.laphw(s, dx, x, ox), P.Geo.laplw(s, dz, z, oz), P.Geo.laphw(s, dz, z, oz),
        top, m, s, hlo, hhi)
    case False{}:
      sgx_armx_neg(0n, 0n, 0n, 0n, 0n, 0n, m, s, hh, hh)

def sgx_foot2_xpos(on: Bool, hon: {on == True{} : Bool}, +s: Nat, +dx: Nat, +dz: Nat, +x: Nat, +z: Nat, +ox: Nat, +oz: Nat,
  +top: Nat, +m: P.Mat, hlo: {Nat.is_lt(Nat.div(s, 2n), P.Geo.laplw(s, dx, x, ox)) == True{} : Bool})
  -> {P.Z.above(P.Wv.x(P.Hold.arm(P.Geo.foot2(on, True{}, s, dx, dz, x, z, ox, oz, top, P.Foot.none()), m, s)), P.Pos{0n}) == True{} : Bool}:
  match on:
    case True{}:
      sgx_armx_pos(1n, P.Geo.laplw(s, dx, x, ox), P.Geo.laphw(s, dx, x, ox), P.Geo.laplw(s, dz, z, oz), P.Geo.laphw(s, dz, z, oz),
        top, m, s, hlo)
    case False{}:
      Empty.absurd({P.Z.above(P.Wv.x(P.Hold.arm(P.Geo.foot2(False{}, True{}, s, dx, dz, x, z, ox, oz, top, P.Foot.none()), m, s)), P.Pos{0n})
        == True{} : Bool}, clash2(hon))

def sgx_and_true(a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, clash2(ha))

# the cube under it is the foot: it is low enough, and overlaps the widened
# body along x and z
def sgx_on(+s: Nat, +dx: Nat, +dz: Nat, +x: Nat, +y: Nat, +z: Nat, +ox: Nat, +oz: Nat, +top: Nat,
  under: {Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))) == True{} : Bool},
  across: {Nat.is_lt(0n, P.Geo.lap(s, x, ox)) == True{} : Bool},
  along: {Nat.is_lt(0n, P.Geo.lap(s, z, oz)) == True{} : Bool})
  -> {Bool.and(Bool.and(Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))),
        Bool.and(Nat.is_lt(0n, P.Geo.lapd(s, dx, x, ox)), Nat.is_lt(0n, P.Geo.lapd(s, dz, z, oz)))),
      Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top))) == True{} : Bool}:
  sgx_and_true(Bool.and(Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))),
      Bool.and(Nat.is_lt(0n, P.Geo.lapd(s, dx, x, ox)), Nat.is_lt(0n, P.Geo.lapd(s, dz, z, oz)))),
    Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top)),
    sgx_and_true(Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))),
      Bool.and(Nat.is_lt(0n, P.Geo.lapd(s, dx, x, ox)), Nat.is_lt(0n, P.Geo.lapd(s, dz, z, oz))), under,
      sgx_and_true(Nat.is_lt(0n, P.Geo.lapd(s, dx, x, ox)), Nat.is_lt(0n, P.Geo.lapd(s, dz, z, oz)),
        sgx_lapd_pos(s, dx, x, ox, across), sgx_lapd_pos(s, dz, z, oz, along))),
    {==})

# past the +x edge: the arm along x points -x
def sgx_arm_px(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(ox, P.K.size(k)), Nat.add(x, Nat.div(P.K.size(k), 2n))) == True{} : Bool})
  -> {P.Z.above(P.Pos{0n}, P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt),
      [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))) == True{} : Bool}:
  +s = P.K.size(k)
  +h = Nat.div(s, 2n)
  +m = P.Rot.mat(P.Rot.q(rt))
  +dx = P.Geo.widex(s, m)
  +dz = P.Geo.widez(s, m)
  +top = P.Geo.top(s, oy, ort)
  +xo = sgx_le_lt(x, P.Pick.high(x, ox), Nat.add(ox, s), sgx_high_ge_l(x, ox),
    sgx_lt_le(P.Pick.high(x, ox), P.Pick.low(Nat.add(x, s), Nat.add(ox, s)), Nat.add(ox, s), sgx_lap_ends(s, x, ox, across),
      sgx_low_le_r(Nat.add(x, s), Nat.add(ox, s))))
  +xh = sgx_lt_trans(x, Nat.add(ox, s), Nat.add(x, h), xo, past)
  +hh = sgx_pos_of_lt_add(x, h, xh)
  +hhi = sgx_sub_lt(P.Pick.high(P.Pick.low(Nat.add(Nat.add(x, s), dx), Nat.add(ox, s)), x), x, h,
    sgx_high_lt(P.Pick.low(Nat.add(Nat.add(x, s), dx), Nat.add(ox, s)), x, Nat.add(x, h),
      sgx_le_lt(P.Pick.low(Nat.add(Nat.add(x, s), dx), Nat.add(ox, s)), Nat.add(ox, s), Nat.add(x, h),
        sgx_low_le_r(Nat.add(Nat.add(x, s), dx), Nat.add(ox, s)), past), xh), hh)
  +hlo = sgx_sub_lt(P.Pick.high(Nat.sub(x, dx), ox), x, h,
    sgx_high_lt(Nat.sub(x, dx), ox, Nat.add(x, h), sgx_le_lt(Nat.sub(x, dx), x, Nat.add(x, h), sgx_sub_le(x, dx), xh),
      sgx_le_lt(ox, Nat.add(ox, s), Nat.add(x, h), le_add(ox, s), past)), hh)
  sgx_foot2_xneg(Bool.and(Bool.and(Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))),
      Bool.and(Nat.is_lt(0n, P.Geo.lapd(s, dx, x, ox)), Nat.is_lt(0n, P.Geo.lapd(s, dz, z, oz)))),
      Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top))),
    s, dx, dz, x, z, ox, oz, top, m, hlo, hhi, hh)

# past the -x edge: the arm along x points +x
def sgx_arm_nx(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(x, Nat.div(P.K.size(k), 2n)), ox) == True{} : Bool})
  -> {P.Z.above(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt),
      [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k))), P.Pos{0n}) == True{} : Bool}:
  +s = P.K.size(k)
  +h = Nat.div(s, 2n)
  +m = P.Rot.mat(P.Rot.q(rt))
  +dx = P.Geo.widex(s, m)
  +dz = P.Geo.widez(s, m)
  +top = P.Geo.top(s, oy, ort)
  +hlx = sgx_sub_gt(P.Pick.high(Nat.sub(x, dx), ox), x, h,
    sgx_lt_le(Nat.add(x, h), ox, P.Pick.high(Nat.sub(x, dx), ox), past, sgx_high_ge_r(Nat.sub(x, dx), ox)))
  sgx_foot2_xpos(Bool.and(Bool.and(Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))),
      Bool.and(Nat.is_lt(0n, P.Geo.lapd(s, dx, x, ox)), Nat.is_lt(0n, P.Geo.lapd(s, dz, z, oz)))),
      Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top))),
    sgx_on(s, dx, dz, x, y, z, ox, oz, top, under, across, along),
    s, dx, dz, x, z, ox, oz, top, m, hlx)

# The turning about z the press gives
# -----------------------------------

def sgx_sub_lt_or(lt: Bool, +m: Nat, +n: Nat, hlt: {Nat.is_lt(m, n) == lt : Bool}, hn: {Nat.is_lt(0n, n) == True{} : Bool})
  -> {P.Z.above(P.Pos{m}, P.Z.diff(lt, m, n)) == True{} : Bool}:
  match lt:
    case True{}:
      or_there(Nat.is_lt(0n, m), Nat.is_lt(0n, Nat.sub(n, m)), lt_sub(m, n, hlt))
    case False{}:
      sgx_sub_lt_self(m, n, hn, lt_false_le(m, n, hlt))

# v - n is below v, for n > 0
def sgx_above_add_neg(+v: P.Z, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool})
  -> {P.Z.above(v, P.Z.add(v, P.Neg{n})) == True{} : Bool}:
  match v:
    case P.Pos{m}:
      sgx_sub_lt_or(Nat.is_lt(m, n), m, n, {==}, hn)
    case P.Neg{m}:
      sgx_lt_add_self(m, n, hn)

def sgx_or_sub(+m: Nat, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool})
  -> {Bool.or(Nat.is_lt(0n, Nat.sub(n, m)), Nat.is_lt(0n, m)) == True{} : Bool}:
  match m:
    case 0n:
      match n:
        case 0n:
          Empty.absurd({Bool.or(Nat.is_lt(0n, Nat.sub(0n, 0n)), Nat.is_lt(0n, 0n)) == True{} : Bool}, clash2(hn))
        case 1n+np:
          {==}
    case 1n+mp:
      or_there(Nat.is_lt(0n, Nat.sub(n, 1n+mp)), Nat.is_lt(0n, 1n+mp), {==})

def sgx_add_lt_or(lt: Bool, +m: Nat, +n: Nat, hlt: {Nat.is_lt(n, m) == lt : Bool}, hn: {Nat.is_lt(0n, n) == True{} : Bool})
  -> {P.Z.above(P.Z.diff(lt, n, m), P.Neg{m}) == True{} : Bool}:
  match lt:
    case True{}:
      sgx_sub_lt_self(m, n, hn, lt_true_le(n, m, hlt))
    case False{}:
      sgx_or_sub(m, n, hn)

# v + n is above v, for n > 0
def sgx_above_add_pos(+v: P.Z, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool})
  -> {P.Z.above(P.Z.add(v, P.Pos{n}), v) == True{} : Bool}:
  match v:
    case P.Pos{m}:
      sgx_lt_add_self(m, n, hn)
    case P.Neg{m}:
      sgx_add_lt_or(Nat.is_lt(n, m), m, n, {==}, hn)

# an arm pointing -x makes the turning about z go down
def sgx_wz_dec(+wz: P.Z, +ax: P.Z, +hax: {P.Z.above(P.Pos{0n}, ax) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat)
  -> {P.Z.above(wz, P.Z.add(wz, P.Z.divc(P.Rot.crz(ax, ay, P.Pos{0n}, P.Pos{g}), D))) == True{} : Bool}:
  match ax:
    case P.Pos{a}:
      Empty.absurd({P.Z.above(wz, P.Z.add(wz, P.Z.divc(P.Rot.crz(P.Pos{a}, ay, P.Pos{0n}, P.Pos{g}), D))) == True{} : Bool},
        clash2(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, lt_zero_r(a)), hax)))
    case P.Neg{a}:
      %Equal.sym(P.Z, P.Rot.crz(P.Neg{a}, ay, P.Pos{0n}, P.Pos{g}), P.Z.mul(P.Neg{a}, P.Pos{g}), crz_eq(P.Neg{a}, hax, ay, g, hg))
        : {P.Z.above(wz, P.Z.add(wz, P.Z.divc(_, D))) == True{} : Bool}
      sgx_above_add_neg(wz, Nat.div(Nat.add(Nat.mul(a, g), Nat.sub(P.Pick.high(D, 1n), 1n)), P.Pick.high(D, 1n)),
        divc_mag_pos(Nat.mul(a, g), mul_pos(a, hax, g, hg), D))

# an arm pointing +x makes it go up
def sgx_wz_inc(+wz: P.Z, +ax: P.Z, +hax: {P.Z.above(ax, P.Pos{0n}) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat)
  -> {P.Z.above(P.Z.add(wz, P.Z.divc(P.Rot.crz(ax, ay, P.Pos{0n}, P.Pos{g}), D)), wz) == True{} : Bool}:
  match ax:
    case P.Pos{a}:
      %Equal.sym(P.Z, P.Rot.crz(P.Pos{a}, ay, P.Pos{0n}, P.Pos{g}), P.Z.mul(P.Pos{a}, P.Pos{g}), crz_eq(P.Pos{a}, hax, ay, g, hg))
        : {P.Z.above(P.Z.add(wz, P.Z.divc(_, D)), wz) == True{} : Bool}
      sgx_above_add_pos(wz, Nat.div(Nat.add(Nat.mul(a, g), Nat.sub(P.Pick.high(D, 1n), 1n)), P.Pick.high(D, 1n)),
        divc_mag_pos(Nat.mul(a, g), mul_pos(a, hax, g, hg), D))
    case P.Neg{a}:
      Empty.absurd({P.Z.above(P.Z.add(wz, P.Z.divc(P.Rot.crz(P.Neg{a}, ay, P.Pos{0n}, P.Pos{g}), D)), wz) == True{} : Bool}, clash2(hax))

def sgx_mag_neg(+ax: P.Z, hax: {P.Z.above(P.Pos{0n}, ax) == True{} : Bool}) -> {Nat.is_lt(0n, P.Z.mag(ax)) == True{} : Bool}:
  match ax:
    case P.Pos{a}:
      Empty.absurd({Nat.is_lt(0n, a) == True{} : Bool},
        clash2(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, lt_zero_r(a)), hax)))
    case P.Neg{a}:
      hax

def sgx_mag_pos(+ax: P.Z, hax: {P.Z.above(ax, P.Pos{0n}) == True{} : Bool}) -> {Nat.is_lt(0n, P.Z.mag(ax)) == True{} : Bool}:
  match ax:
    case P.Pos{a}:
      hax
    case P.Neg{a}:
      Empty.absurd({Nat.is_lt(0n, a) == True{} : Bool}, clash2(hax))

# The four the laws use
# ---------------------

def sign_px(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(ox, P.K.size(k)), Nat.add(x, Nat.div(P.K.size(k), 2n))) == True{} : Bool})
  -> {P.Z.above(P.Wv.z(P.Rot.w(rt)), P.Wv.z(P.Rot.w(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k),
      [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))) == True{} : Bool}:
  +arm = {P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()),
    P.Rot.mat(P.Rot.q(rt)), P.K.size(k)) : P.Wv}
  sgx_wz_dec(P.Wv.z(P.Rot.w(rt)), P.Wv.x(arm), sgx_arm_px(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, across, past),
    P.Wv.y(arm), P.K.g(k), heavy, P.Rot.about(P.K.size(k), P.Wv.x(arm), P.Wv.y(arm), P.Wv.z(arm)))

def sign_nx(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(x, Nat.div(P.K.size(k), 2n)), ox) == True{} : Bool})
  -> {P.Z.above(P.Wv.z(P.Rot.w(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k),
      [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))), P.Wv.z(P.Rot.w(rt))) == True{} : Bool}:
  +arm = {P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()),
    P.Rot.mat(P.Rot.q(rt)), P.K.size(k)) : P.Wv}
  sgx_wz_inc(P.Wv.z(P.Rot.w(rt)), P.Wv.x(arm),
    sgx_arm_nx(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past),
    P.Wv.y(arm), P.K.g(k), heavy, P.Rot.about(P.K.size(k), P.Wv.x(arm), P.Wv.y(arm), P.Wv.z(arm)))

def tip_px(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(ox, P.K.size(k)), Nat.add(x, Nat.div(P.K.size(k), 2n))) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt),
        [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))),
      P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt),
        [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))))) == True{} : Bool}:
  +arm = {P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()),
    P.Rot.mat(P.Rot.q(rt)), P.K.size(k)) : P.Wv}
  lt_add(P.Z.mag(P.Wv.x(arm)), P.Z.mag(P.Wv.z(arm)),
    sgx_mag_neg(P.Wv.x(arm), sgx_arm_px(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, across, past)))

def tip_nx(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(x, Nat.div(P.K.size(k), 2n)), ox) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt),
        [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))),
      P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt),
        [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))))) == True{} : Bool}:
  +arm = {P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()),
    P.Rot.mat(P.Rot.q(rt)), P.K.size(k)) : P.Wv}
  lt_add(P.Z.mag(P.Wv.x(arm)), P.Z.mag(P.Wv.z(arm)),
    sgx_mag_pos(P.Wv.x(arm), sgx_arm_nx(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past)))


# Past the edge along z: the sign of the arm, and of the turning it gives
# =========================================================================
# A cube standing on one cube o, off the floor, its middle past o's edge
# along z: the foot o gives is Foot{1, laplw, laphw, ...} (o counts as a
# support: its widened overlap lapd is at least the plain one lap the law
# asks for), and the arm's z is the middle held inside [laplw, laphw] along
# z, which the past hypothesis puts wholly on one side of the middle. The
# press at that arm turns the cube about x: Rot.crx(ay, az, g, 0) = -az*g.

# ---- order kit ----

def sgz_le_lt(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, clash(Equal.trans(Bool, True{}, Nat.is_lt(b, 0n), False{},
        Equal.sym(Bool, Nat.is_lt(b, 0n), True{}, h2), lt_zero_r(b))))
    case 0n _ 1n+cp:
      {==}
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool}, clash2(h1))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, clash2(h2))
    case 1n+ap 1n+bp 1n+cp:
      sgz_le_lt(ap, bp, cp, h1, h2)

def sgz_lt_le(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(a, c) == True{} : Bool}, clash(Equal.trans(Bool, True{}, Nat.is_lt(a, 0n), False{},
        Equal.sym(Bool, Nat.is_lt(a, 0n), True{}, h1), lt_zero_r(a))))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, clash2(h2))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, clash2(h2))
    case 1n+ap 1n+bp 1n+cp:
      sgz_lt_le(ap, bp, cp, h1, h2)

def sgz_lt_asym(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == False{} : Bool}, clash2(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, clash2(h))
    case 1n+p 1n+q:
      sgz_lt_asym(p, q, h)

def sgz_le_false_lt(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, clash(e))
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, clash(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sgz_le_false_lt(p, q, e)

def sgz_lt_le_false(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, clash2(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, clash2(h))
    case 1n+p 1n+q:
      sgz_lt_le_false(p, q, h)

# a < b + c and 0 < c give a - b < c
def sgz_sub_lt(+a: Nat, +b: Nat, +c: Nat, h: {Nat.is_lt(a, Nat.add(b, c)) == True{} : Bool}, hc: {Nat.is_lt(0n, c) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(a, b), c) == True{} : Bool}:
  match a b:
    case 0n 0n:
      hc
    case 0n 1n+q:
      hc
    case 1n+p 0n:
      h
    case 1n+p 1n+q:
      sgz_sub_lt(p, q, c, h, hc)

def sgz_lt_add_self(+z: Nat, +h: Nat, hh: {Nat.is_lt(0n, h) == True{} : Bool}) -> {Nat.is_lt(z, Nat.add(z, h)) == True{} : Bool}:
  match z:
    case 0n:
      hh
    case 1n+p:
      sgz_lt_add_self(p, h, hh)

def sgz_lt_self_add(+z: Nat, +h: Nat, H: {Nat.is_lt(z, Nat.add(z, h)) == True{} : Bool}) -> {Nat.is_lt(0n, h) == True{} : Bool}:
  match z:
    case 0n:
      H
    case 1n+p:
      sgz_lt_self_add(p, h, H)

def sgz_sub_mono(+u: Nat, +v: Nat, +z: Nat, h: {Nat.is_le(u, v) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(u, z), Nat.sub(v, z)) == True{} : Bool}:
  match u v z:
    case 0n _ 0n:
      le_zero_l(Nat.sub(v, 0n))
    case 0n _ 1n+zp:
      le_zero_l(Nat.sub(v, 1n+zp))
    case 1n+up 0n _:
      Empty.absurd({Nat.is_le(Nat.sub(1n+up, z), Nat.sub(0n, z)) == True{} : Bool}, clash2(h))
    case 1n+up 1n+vp 0n:
      h
    case 1n+up 1n+vp 1n+zp:
      sgz_sub_mono(up, vp, zp, h)

# z + h < oz gives h < oz - z
def sgz_lt_sub_gt(+z: Nat, +h: Nat, +oz: Nat, H: {Nat.is_lt(Nat.add(z, h), oz) == True{} : Bool})
  -> {Nat.is_lt(h, Nat.sub(oz, z)) == True{} : Bool}:
  match z oz:
    case 0n 0n:
      H
    case 0n 1n+q:
      H
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(h, Nat.sub(0n, 1n+p)) == True{} : Bool}, clash(Equal.trans(Bool, True{}, Nat.is_lt(1n+Nat.add(p, h), 0n), False{},
        Equal.sym(Bool, Nat.is_lt(1n+Nat.add(p, h), 0n), True{}, H), lt_zero_r(1n+Nat.add(p, h)))))
    case 1n+p 1n+q:
      sgz_lt_sub_gt(p, h, q, H)

# 0 < n <= m gives m - n < m
def sgz_sub_lt_self(+m: Nat, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, hle: {Nat.is_le(n, m) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(m, n), m) == True{} : Bool}:
  match m n:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(m, 0n), m) == True{} : Bool}, clash2(hn))
    case 0n 1n+np:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+np), 0n) == True{} : Bool}, clash2(hle))
    case 1n+mp 1n+np:
      le_to_lt_s(Nat.sub(mp, np), mp, sub_le(mp, np))

# ---- Pick kit ----

def sgz_low_le_r.go(c: Bool, +a: Nat, +b: Nat, e: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(P.Pick.n(c, a, b), b) == True{} : Bool}:
  match c:
    case True{}:
      e
    case False{}:
      le_refl(b)

def sgz_low_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(P.Pick.low(a, b), b) == True{} : Bool}:
  sgz_low_le_r.go(Nat.is_le(a, b), a, b, {==})

def sgz_high_ge_r.go(c: Bool, +a: Nat, +b: Nat, e: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(b, P.Pick.n(c, b, a)) == True{} : Bool}:
  match c:
    case True{}:
      le_refl(b)
    case False{}:
      le_flip(a, b, e)

def sgz_high_ge_r(+a: Nat, +b: Nat) -> {Nat.is_le(b, P.Pick.high(a, b)) == True{} : Bool}:
  sgz_high_ge_r.go(Nat.is_le(a, b), a, b, {==})

def sgz_high_ge_l.go(c: Bool, +a: Nat, +b: Nat, e: {Nat.is_le(a, b) == c : Bool}) -> {Nat.is_le(a, P.Pick.n(c, b, a)) == True{} : Bool}:
  match c:
    case True{}:
      e
    case False{}:
      le_refl(a)

def sgz_high_ge_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, P.Pick.high(a, b)) == True{} : Bool}:
  sgz_high_ge_l.go(Nat.is_le(a, b), a, b, {==})

def sgz_high_mono.go(c1: Bool, c2: Bool, +u: Nat, +v: Nat, +b: Nat, h: {Nat.is_le(u, v) == True{} : Bool},
  e1: {Nat.is_le(u, b) == c1 : Bool}, e2: {Nat.is_le(v, b) == c2 : Bool})
  -> {Nat.is_le(P.Pick.n(c1, b, u), P.Pick.n(c2, b, v)) == True{} : Bool}:
  match c1 c2:
    case True{} True{}:
      le_refl(b)
    case True{} False{}:
      le_flip(v, b, e2)
    case False{} True{}:
      le_trans(u, v, b, h, e2)
    case False{} False{}:
      h

def sgz_high_mono(+u: Nat, +v: Nat, +b: Nat, h: {Nat.is_le(u, v) == True{} : Bool})
  -> {Nat.is_le(P.Pick.high(u, b), P.Pick.high(v, b)) == True{} : Bool}:
  sgz_high_mono.go(Nat.is_le(u, b), Nat.is_le(v, b), u, v, b, h, {==}, {==})

def sgz_low_mono.go(c1: Bool, c2: Bool, +u: Nat, +v: Nat, +b: Nat, h: {Nat.is_le(u, v) == True{} : Bool},
  e1: {Nat.is_le(u, b) == c1 : Bool}, e2: {Nat.is_le(v, b) == c2 : Bool})
  -> {Nat.is_le(P.Pick.n(c1, u, b), P.Pick.n(c2, v, b)) == True{} : Bool}:
  match c1 c2:
    case True{} True{}:
      h
    case True{} False{}:
      e1
    case False{} True{}:
      Empty.absurd({Nat.is_le(b, v) == True{} : Bool}, clash(Equal.trans(Bool, True{}, Nat.is_le(u, b), False{},
        Equal.sym(Bool, Nat.is_le(u, b), True{}, le_trans(u, v, b, h, e2)), e1)))
    case False{} False{}:
      le_refl(b)

def sgz_low_mono(+u: Nat, +v: Nat, +b: Nat, h: {Nat.is_le(u, v) == True{} : Bool})
  -> {Nat.is_le(P.Pick.low(u, b), P.Pick.low(v, b)) == True{} : Bool}:
  sgz_low_mono.go(Nat.is_le(u, b), Nat.is_le(v, b), u, v, b, h, {==}, {==})

# ---- overlaps ----

# lo - lo is never above 0
def sgz_sub_self_lt(+lo: Nat, h: {Nat.is_lt(0n, Nat.sub(lo, lo)) == True{} : Bool}) -> Empty:
  match lo:
    case 0n:
      clash2(h)
    case 1n+p:
      sgz_sub_self_lt(p, h)

def sgz_lt_of_lap.go(c: Bool, +lo: Nat, +hi: Nat, e: {Nat.is_le(hi, lo) == c : Bool},
  h: {Nat.is_lt(0n, Nat.sub(P.Pick.n(c, lo, hi), lo)) == True{} : Bool}) -> {Nat.is_lt(lo, hi) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Nat.is_lt(lo, hi) == True{} : Bool}, sgz_sub_self_lt(lo, h))
    case False{}:
      sgz_le_false_lt(hi, lo, e)

# an overlap that is there: lo < hi
def sgz_lt_of_lap(+lo: Nat, +hi: Nat, h: {Nat.is_lt(0n, Nat.sub(P.Pick.high(hi, lo), lo)) == True{} : Bool})
  -> {Nat.is_lt(lo, hi) == True{} : Bool}:
  sgz_lt_of_lap.go(Nat.is_le(hi, lo), lo, hi, {==}, h)

def sgz_lap_of_lt(+lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.sub(P.Pick.high(hi, lo), lo)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(hi, lo), False{}, sgz_lt_le_false(lo, hi, h))
    : {Nat.is_lt(0n, Nat.sub(P.Pick.n(_, lo, hi), lo)) == True{} : Bool}
  lt_sub(lo, hi, h)

# the widened overlap is at least the plain one
def sgz_lapd_pos(+s: Nat, +d: Nat, +a: Nat, +b: Nat, h: {Nat.is_lt(0n, P.Geo.lap(s, a, b)) == True{} : Bool})
  -> {Nat.is_lt(0n, P.Geo.lapd(s, d, a, b)) == True{} : Bool}:
  +lo = P.Pick.high(a, b)
  +hi = P.Pick.low(Nat.add(a, s), Nat.add(b, s))
  +lod = P.Pick.high(Nat.sub(a, d), b)
  +hid = P.Pick.low(Nat.add(Nat.add(a, s), d), Nat.add(b, s))
  sgz_lap_of_lt(lod, hid,
    sgz_le_lt(lod, lo, hid, sgz_high_mono(Nat.sub(a, d), a, b, sub_le(a, d)),
      sgz_lt_le(lo, hi, hid, sgz_lt_of_lap(lo, hi, h), sgz_low_mono(Nat.add(a, s), Nat.add(Nat.add(a, s), d), Nat.add(b, s), le_add(Nat.add(a, s), d)))))

# 0 < lap(s, z, oz) gives z < oz + s
def sgz_lap_lt(+s: Nat, +z: Nat, +oz: Nat, h: {Nat.is_lt(0n, P.Geo.lap(s, z, oz)) == True{} : Bool})
  -> {Nat.is_lt(z, Nat.add(oz, s)) == True{} : Bool}:
  +lo = P.Pick.high(z, oz)
  +hi = P.Pick.low(Nat.add(z, s), Nat.add(oz, s))
  sgz_le_lt(z, lo, Nat.add(oz, s), sgz_high_ge_l(z, oz),
    sgz_lt_le(lo, hi, Nat.add(oz, s), sgz_lt_of_lap(lo, hi, h), sgz_low_le_r(Nat.add(z, s), Nat.add(oz, s))))

# ---- the arm held inside [lo, hi], on one side of the middle c ----

def sgz_pick_lt(c: Bool, +u: Nat, +v: Nat, +k: Nat, hu: {Nat.is_lt(u, k) == True{} : Bool}, hv: {Nat.is_lt(v, k) == True{} : Bool})
  -> {Nat.is_lt(P.Pick.n(c, u, v), k) == True{} : Bool}:
  match c:
    case True{}:
      hu
    case False{}:
      hv

def sgz_low_lt(c: Bool, +a: Nat, +hi: Nat, +k: Nat, e: {Nat.is_le(a, hi) == c : Bool}, hhi: {Nat.is_lt(hi, k) == True{} : Bool})
  -> {Nat.is_lt(P.Pick.n(c, a, hi), k) == True{} : Bool}:
  match c:
    case True{}:
      sgz_le_lt(a, hi, k, e, hhi)
    case False{}:
      hhi

def sgz_gt_high(c: Bool, +u: Nat, +lo: Nat, +k: Nat, e: {Nat.is_le(u, lo) == c : Bool}, hlo: {Nat.is_lt(k, lo) == True{} : Bool})
  -> {Nat.is_lt(k, P.Pick.n(c, lo, u)) == True{} : Bool}:
  match c:
    case True{}:
      hlo
    case False{}:
      sgz_lt_le(k, lo, u, hlo, le_flip(u, lo, e))

# lo and hi below c: the arm points back, Neg
def sgz_leanf_neg(+c: Nat, +a: Nat, +lo: Nat, +hi: Nat, hlo: {Nat.is_lt(lo, c) == True{} : Bool}, hhi: {Nat.is_lt(hi, c) == True{} : Bool})
  -> {P.Z.above(P.Pos{0n}, P.Geo.leanf(c, a, lo, hi)) == True{} : Bool}:
  +p = P.Pick.high(P.Pick.low(a, hi), lo)
  +hp = sgz_pick_lt(Nat.is_le(P.Pick.low(a, hi), lo), lo, P.Pick.low(a, hi), c, hlo, sgz_low_lt(Nat.is_le(a, hi), a, hi, c, {==}, hhi))
  %Equal.sym(Bool, Nat.is_lt(p, c), True{}, hp) : {P.Z.above(P.Pos{0n}, P.Z.diff(_, p, c)) == True{} : Bool}
  lt_sub(p, c, hp)

# lo above c: the arm points on, Pos
def sgz_leanf_pos(+c: Nat, +a: Nat, +lo: Nat, +hi: Nat, hlo: {Nat.is_lt(c, lo) == True{} : Bool})
  -> {P.Z.above(P.Geo.leanf(c, a, lo, hi), P.Pos{0n}) == True{} : Bool}:
  +p = P.Pick.high(P.Pick.low(a, hi), lo)
  +hp = sgz_gt_high(Nat.is_le(P.Pick.low(a, hi), lo), P.Pick.low(a, hi), lo, c, {==}, hlo)
  %Equal.sym(Bool, Nat.is_lt(p, c), False{}, sgz_lt_asym(c, p, hp)) : {P.Z.above(P.Z.diff(_, p, c), P.Pos{0n}) == True{} : Bool}
  lt_sub(c, p, hp)

# ---- signs of Z ----

def sgz_above_neg_mag(+v: P.Z, h: {P.Z.above(P.Pos{0n}, v) == True{} : Bool}) -> {Nat.is_lt(0n, P.Z.mag(v)) == True{} : Bool}:
  match v:
    case P.Pos{n}:
      Empty.absurd({Nat.is_lt(0n, n) == True{} : Bool}, clash(Equal.trans(Bool, True{}, Nat.is_lt(n, 0n), False{},
        Equal.sym(Bool, Nat.is_lt(n, 0n), True{}, h), lt_zero_r(n))))
    case P.Neg{n}:
      h

def sgz_above_pos_mag(+v: P.Z, h: {P.Z.above(v, P.Pos{0n}) == True{} : Bool}) -> {Nat.is_lt(0n, P.Z.mag(v)) == True{} : Bool}:
  match v:
    case P.Pos{n}:
      h
    case P.Neg{n}:
      Empty.absurd({Nat.is_lt(0n, n) == True{} : Bool}, clash2(h))

# an arm back along z (Neg) kicks the turning about x up
def sgz_kick_pos(+az: P.Z, +haz: {P.Z.above(P.Pos{0n}, az) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat)
  -> {P.Z.above(P.Z.divc(P.Rot.crx(ay, az, P.Pos{g}, P.Pos{0n}), D), P.Pos{0n}) == True{} : Bool}:
  match az:
    case P.Pos{c}:
      Empty.absurd({P.Z.above(P.Z.divc(P.Rot.crx(ay, P.Pos{c}, P.Pos{g}, P.Pos{0n}), D), P.Pos{0n}) == True{} : Bool},
        clash(Equal.trans(Bool, True{}, Nat.is_lt(c, 0n), False{}, Equal.sym(Bool, Nat.is_lt(c, 0n), True{}, haz), lt_zero_r(c))))
    case P.Neg{c}:
      %Equal.sym(P.Z, P.Rot.crx(ay, P.Neg{c}, P.Pos{g}, P.Pos{0n}), P.Z.opp(P.Z.mul(P.Neg{c}, P.Pos{g})),
        crx_eq(ay, P.Neg{c}, haz, g, hg)) : {P.Z.above(P.Z.divc(_, D), P.Pos{0n}) == True{} : Bool}
      divc_mag_pos(Nat.mul(c, g), mul_pos(c, haz, g, hg), D)

# an arm on along z (Pos) kicks it down
def sgz_kick_neg(+az: P.Z, +haz: {P.Z.above(az, P.Pos{0n}) == True{} : Bool}, +ay: P.Z, +g: Nat,
  +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +D: Nat)
  -> {P.Z.above(P.Pos{0n}, P.Z.divc(P.Rot.crx(ay, az, P.Pos{g}, P.Pos{0n}), D)) == True{} : Bool}:
  match az:
    case P.Pos{c}:
      %Equal.sym(P.Z, P.Rot.crx(ay, P.Pos{c}, P.Pos{g}, P.Pos{0n}), P.Z.opp(P.Z.mul(P.Pos{c}, P.Pos{g})),
        crx_eq(ay, P.Pos{c}, haz, g, hg)) : {P.Z.above(P.Pos{0n}, P.Z.divc(_, D)) == True{} : Bool}
      divc_mag_pos(Nat.mul(c, g), mul_pos(c, haz, g, hg), D)
    case P.Neg{c}:
      Empty.absurd({P.Z.above(P.Pos{0n}, P.Z.divc(P.Rot.crx(ay, P.Neg{c}, P.Pos{g}, P.Pos{0n}), D)) == True{} : Bool}, clash2(haz))

def sgz_add_pos.neg(c: Bool, +m: Nat, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, e: {Nat.is_lt(n, m) == c : Bool})
  -> {P.Z.above(P.Z.diff(c, n, m), P.Neg{m}) == True{} : Bool}:
  match c:
    case True{}:
      sgz_sub_lt_self(m, n, hn, lt_true_le(n, m, e))
    case False{}:
      match m:
        case 0n:
          or_here(Nat.is_lt(0n, Nat.sub(n, 0n)), Nat.is_lt(0n, 0n),
            (%Equal.sym(Nat, Nat.sub(n, 0n), n, sub_zero_r(n)) : {Nat.is_lt(0n, _) == True{} : Bool}; hn))
        case 1n+mp:
          or_there(Nat.is_lt(0n, Nat.sub(n, 1n+mp)), Nat.is_lt(0n, 1n+mp), {==})

# v plus something above 0 is above v, whatever the sign of v
def sgz_add_pos(+v: P.Z, +u: P.Z, +hu: {P.Z.above(u, P.Pos{0n}) == True{} : Bool})
  -> {P.Z.above(P.Z.add(v, u), v) == True{} : Bool}:
  match v u:
    case P.Pos{m} P.Pos{n}:
      sgz_lt_add_self(m, n, hu)
    case P.Pos{m} P.Neg{n}:
      Empty.absurd({P.Z.above(P.Z.add(P.Pos{m}, P.Neg{n}), P.Pos{m}) == True{} : Bool}, clash2(hu))
    case P.Neg{m} P.Pos{n}:
      sgz_add_pos.neg(Nat.is_lt(n, m), m, n, hu, {==})
    case P.Neg{m} P.Neg{n}:
      Empty.absurd({P.Z.above(P.Z.add(P.Neg{m}, P.Neg{n}), P.Neg{m}) == True{} : Bool}, clash2(hu))

def sgz_add_neg.pos(c: Bool, +m: Nat, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, e: {Nat.is_lt(m, n) == c : Bool})
  -> {P.Z.above(P.Pos{m}, P.Z.diff(c, m, n)) == True{} : Bool}:
  match c:
    case True{}:
      or_there(Nat.is_lt(0n, m), Nat.is_lt(0n, Nat.sub(n, m)), lt_sub(m, n, e))
    case False{}:
      sgz_sub_lt_self(m, n, hn, lt_false_le(m, n, e))

# v plus something below 0 is below v, whatever the sign of v
def sgz_add_neg(+v: P.Z, +u: P.Z, +hu: {P.Z.above(P.Pos{0n}, u) == True{} : Bool})
  -> {P.Z.above(v, P.Z.add(v, u)) == True{} : Bool}:
  match v u:
    case P.Pos{m} P.Pos{n}:
      Empty.absurd({P.Z.above(P.Pos{m}, P.Z.add(P.Pos{m}, P.Pos{n})) == True{} : Bool},
        clash(Equal.trans(Bool, True{}, Nat.is_lt(n, 0n), False{}, Equal.sym(Bool, Nat.is_lt(n, 0n), True{}, hu), lt_zero_r(n))))
    case P.Pos{m} P.Neg{n}:
      sgz_add_neg.pos(Nat.is_lt(m, n), m, n, hu, {==})
    case P.Neg{m} P.Pos{n}:
      Empty.absurd({P.Z.above(P.Neg{m}, P.Z.add(P.Neg{m}, P.Pos{n})) == True{} : Bool},
        clash(Equal.trans(Bool, True{}, Nat.is_lt(n, 0n), False{}, Equal.sym(Bool, Nat.is_lt(n, 0n), True{}, hu), lt_zero_r(n))))
    case P.Neg{m} P.Neg{n}:
      sgz_lt_add_self(m, n, hu)

# ---- the press at an arm a, about x ----

def sgz_press_pz(+rt: P.Rot, +s: Nat, +a: P.Wv, +g: Nat, +heavy: {Nat.is_lt(0n, g) == True{} : Bool},
  +hz: {P.Z.above(P.Pos{0n}, P.Wv.z(a)) == True{} : Bool})
  -> {P.Z.above(P.Wv.x(P.Rot.w(P.Rot.pressw(rt, s, a, g))), P.Wv.x(P.Rot.w(rt))) == True{} : Bool}:
  sgz_add_pos(P.Wv.x(P.Rot.w(rt)), P.Z.divc(P.Rot.crx(P.Wv.y(a), P.Wv.z(a), P.Pos{g}, P.Pos{0n}), P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a))),
    sgz_kick_pos(P.Wv.z(a), hz, P.Wv.y(a), g, heavy, P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a))))

def sgz_press_nz(+rt: P.Rot, +s: Nat, +a: P.Wv, +g: Nat, +heavy: {Nat.is_lt(0n, g) == True{} : Bool},
  +hz: {P.Z.above(P.Wv.z(a), P.Pos{0n}) == True{} : Bool})
  -> {P.Z.above(P.Wv.x(P.Rot.w(rt)), P.Wv.x(P.Rot.w(P.Rot.pressw(rt, s, a, g)))) == True{} : Bool}:
  sgz_add_neg(P.Wv.x(P.Rot.w(rt)), P.Z.divc(P.Rot.crx(P.Wv.y(a), P.Wv.z(a), P.Pos{g}, P.Pos{0n}), P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a))),
    sgz_kick_neg(P.Wv.z(a), hz, P.Wv.y(a), g, heavy, P.Rot.about(s, P.Wv.x(a), P.Wv.y(a), P.Wv.z(a))))

# ---- the foot one cube gives: o counts ----

def sgz_foot2(a: Bool, b: Bool, c: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}, ec: {c == True{} : Bool},
  +s: Nat, +dx: Nat, +dz: Nat, +x: Nat, +z: Nat, +ox: Nat, +oz: Nat, +top: Nat)
  -> {P.Geo.foot2(Bool.and(Bool.and(a, Bool.and(b, c)), Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top))),
      Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_lt(P.Foot.ty(P.Foot.none()), top)), s, dx, dz, x, z, ox, oz, top, P.Foot.none()) == P.Foot{1n, P.Geo.laplw(s, dx, x, ox), P.Geo.laphw(s, dx, x, ox), P.Geo.laplw(s, dz, z, oz), P.Geo.laphw(s, dz, z, oz), top} : P.Foot}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case False{} _ _:
      Empty.absurd({P.Geo.foot2(Bool.and(Bool.and(False{}, Bool.and(b, c)), Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top))),
      Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_lt(P.Foot.ty(P.Foot.none()), top)), s, dx, dz, x, z, ox, oz, top, P.Foot.none()) == P.Foot{1n, P.Geo.laplw(s, dx, x, ox), P.Geo.laphw(s, dx, x, ox), P.Geo.laplw(s, dz, z, oz), P.Geo.laphw(s, dz, z, oz), top} : P.Foot}, clash2(ea))
    case True{} False{} _:
      Empty.absurd({P.Geo.foot2(Bool.and(Bool.and(True{}, Bool.and(False{}, c)), Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top))),
      Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_lt(P.Foot.ty(P.Foot.none()), top)), s, dx, dz, x, z, ox, oz, top, P.Foot.none()) == P.Foot{1n, P.Geo.laplw(s, dx, x, ox), P.Geo.laphw(s, dx, x, ox), P.Geo.laplw(s, dz, z, oz), P.Geo.laphw(s, dz, z, oz), top} : P.Foot}, clash2(eb))
    case True{} True{} False{}:
      Empty.absurd({P.Geo.foot2(Bool.and(Bool.and(True{}, Bool.and(True{}, False{})), Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_le(P.Foot.ty(P.Foot.none()), top))),
      Bool.or(Nat.is_eq(P.Foot.n(P.Foot.none()), 0n), Nat.is_lt(P.Foot.ty(P.Foot.none()), top)), s, dx, dz, x, z, ox, oz, top, P.Foot.none()) == P.Foot{1n, P.Geo.laplw(s, dx, x, ox), P.Geo.laphw(s, dx, x, ox), P.Geo.laplw(s, dz, z, oz), P.Geo.laphw(s, dz, z, oz), top} : P.Foot}, clash2(ec))

def sgz_foot_eq(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +q: P.Quat, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z,
  +og: Bool, +oh: Bool, +ort: P.Rot,
  +under: {Nat.is_le(P.Geo.top(s, oy, ort), Nat.add(y, Nat.div(s, 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(s, x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(s, z, oz)) == True{} : Bool})
  -> {P.Geo.foot(s, x, y, z, q, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none())
    == P.Foot{1n, P.Geo.laplw(s, P.Geo.widex(s, P.Rot.mat(q)), x, ox), P.Geo.laphw(s, P.Geo.widex(s, P.Rot.mat(q)), x, ox),
      P.Geo.laplw(s, P.Geo.widez(s, P.Rot.mat(q)), z, oz), P.Geo.laphw(s, P.Geo.widez(s, P.Rot.mat(q)), z, oz), P.Geo.top(s, oy, ort)} : P.Foot}:
  sgz_foot2(Nat.is_le(P.Geo.top(s, oy, ort), Nat.add(y, Nat.div(s, 2n))),
    Nat.is_lt(0n, P.Geo.lapd(s, P.Geo.widex(s, P.Rot.mat(q)), x, ox)), Nat.is_lt(0n, P.Geo.lapd(s, P.Geo.widez(s, P.Rot.mat(q)), z, oz)),
    under, sgz_lapd_pos(s, P.Geo.widex(s, P.Rot.mat(q)), x, ox, across), sgz_lapd_pos(s, P.Geo.widez(s, P.Rot.mat(q)), z, oz, along),
    s, P.Geo.widex(s, P.Rot.mat(q)), P.Geo.widez(s, P.Rot.mat(q)), x, z, ox, oz, P.Geo.top(s, oy, ort))

# ---- where the foot's z reaches, against the middle h ----

def sgz_lo_lt.go(c: Bool, +u: Nat, +oz: Nat, +z: Nat, +h: Nat, e: {Nat.is_le(u, oz) == c : Bool}, hu: {Nat.is_le(u, z) == True{} : Bool},
  hoz: {Nat.is_lt(oz, Nat.add(z, h)) == True{} : Bool}, +hh: {Nat.is_lt(0n, h) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(P.Pick.n(c, oz, u), z), h) == True{} : Bool}:
  match c:
    case True{}:
      sgz_sub_lt(oz, z, h, hoz, hh)
    case False{}:
      sgz_sub_lt(u, z, h, sgz_le_lt(u, z, Nat.add(z, h), hu, sgz_lt_add_self(z, h, hh)), hh)

def sgz_lo_lt(+s: Nat, +d: Nat, +z: Nat, +oz: Nat, +h: Nat, hoz: {Nat.is_lt(oz, Nat.add(z, h)) == True{} : Bool},
  hh: {Nat.is_lt(0n, h) == True{} : Bool}) -> {Nat.is_lt(P.Geo.laplw(s, d, z, oz), h) == True{} : Bool}:
  sgz_lo_lt.go(Nat.is_le(Nat.sub(z, d), oz), Nat.sub(z, d), oz, z, h, {==}, sub_le(z, d), hoz, hh)

def sgz_hi_lt.go(c: Bool, +u: Nat, +z: Nat, +B: Nat, +h: Nat, e: {Nat.is_le(u, z) == c : Bool}, hu: {Nat.is_le(u, B) == True{} : Bool},
  hB: {Nat.is_lt(B, Nat.add(z, h)) == True{} : Bool}, +hh: {Nat.is_lt(0n, h) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(P.Pick.n(c, z, u), z), h) == True{} : Bool}:
  match c:
    case True{}:
      sgz_sub_lt(z, z, h, sgz_lt_add_self(z, h, hh), hh)
    case False{}:
      sgz_sub_lt(u, z, h, sgz_le_lt(u, B, Nat.add(z, h), hu, hB), hh)

def sgz_hi_lt(+s: Nat, +d: Nat, +z: Nat, +oz: Nat, +h: Nat, hpast: {Nat.is_lt(Nat.add(oz, s), Nat.add(z, h)) == True{} : Bool},
  hh: {Nat.is_lt(0n, h) == True{} : Bool}) -> {Nat.is_lt(P.Geo.laphw(s, d, z, oz), h) == True{} : Bool}:
  sgz_hi_lt.go(Nat.is_le(P.Pick.low(Nat.add(Nat.add(z, s), d), Nat.add(oz, s)), z), P.Pick.low(Nat.add(Nat.add(z, s), d), Nat.add(oz, s)),
    z, Nat.add(oz, s), h, {==}, sgz_low_le_r(Nat.add(Nat.add(z, s), d), Nat.add(oz, s)), hpast, hh)

def sgz_lo_gt(+s: Nat, +d: Nat, +z: Nat, +oz: Nat, +h: Nat, hpast: {Nat.is_lt(Nat.add(z, h), oz) == True{} : Bool})
  -> {Nat.is_lt(h, P.Geo.laplw(s, d, z, oz)) == True{} : Bool}:
  sgz_lt_le(h, Nat.sub(oz, z), P.Geo.laplw(s, d, z, oz), sgz_lt_sub_gt(z, h, oz, hpast),
    sgz_sub_mono(oz, P.Pick.high(Nat.sub(z, d), oz), z, sgz_high_ge_r(Nat.sub(z, d), oz)))

# ---- the arm's z ----

def sgz_armz_pz(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(oz, P.K.size(k)), Nat.add(z, Nat.div(P.K.size(k), 2n))) == True{} : Bool})
  -> {P.Z.above(P.Pos{0n}, P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))) == True{} : Bool}:
  +hh = sgz_lt_self_add(z, Nat.div(P.K.size(k), 2n), sgz_le_lt(z, Nat.add(oz, P.K.size(k)), Nat.add(z, Nat.div(P.K.size(k), 2n)), lt_true_le(z, Nat.add(oz, P.K.size(k)), sgz_lap_lt(P.K.size(k), z, oz, along)), past))
  %Equal.sym(P.Foot, P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Foot{1n, P.Geo.laplw(P.K.size(k), P.Geo.widex(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), x, ox), P.Geo.laphw(P.K.size(k), P.Geo.widex(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), x, ox), P.Geo.laplw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz), P.Geo.laphw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz), P.Geo.top(P.K.size(k), oy, ort)}, sgz_foot_eq(P.K.size(k), x, y, z, P.Rot.q(rt), ox, oy, oz, w1, w2, w3, og, oh, ort, under, across, along))
    : {P.Z.above(P.Pos{0n}, P.Wv.z(P.Hold.arm(_, P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))) == True{} : Bool}
  sgz_leanf_neg(Nat.div(P.K.size(k), 2n), P.Z.slide(Nat.div(P.K.size(k), 2n), P.Wv.z(P.Hold.low(P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), P.Geo.laplw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz), P.Geo.laphw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz),
    sgz_lo_lt(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz, Nat.div(P.K.size(k), 2n), sgz_le_lt(oz, Nat.add(oz, P.K.size(k)), Nat.add(z, Nat.div(P.K.size(k), 2n)), le_add(oz, P.K.size(k)), past), hh),
    sgz_hi_lt(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz, Nat.div(P.K.size(k), 2n), past, hh))

def sgz_armz_nz(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(z, Nat.div(P.K.size(k), 2n)), oz) == True{} : Bool})
  -> {P.Z.above(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k))), P.Pos{0n}) == True{} : Bool}:
  %Equal.sym(P.Foot, P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Foot{1n, P.Geo.laplw(P.K.size(k), P.Geo.widex(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), x, ox), P.Geo.laphw(P.K.size(k), P.Geo.widex(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), x, ox), P.Geo.laplw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz), P.Geo.laphw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz), P.Geo.top(P.K.size(k), oy, ort)}, sgz_foot_eq(P.K.size(k), x, y, z, P.Rot.q(rt), ox, oy, oz, w1, w2, w3, og, oh, ort, under, across, along))
    : {P.Z.above(P.Wv.z(P.Hold.arm(_, P.Rot.mat(P.Rot.q(rt)), P.K.size(k))), P.Pos{0n}) == True{} : Bool}
  sgz_leanf_pos(Nat.div(P.K.size(k), 2n), P.Z.slide(Nat.div(P.K.size(k), 2n), P.Wv.z(P.Hold.low(P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), P.Geo.laplw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz), P.Geo.laphw(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz),
    sgz_lo_gt(P.K.size(k), P.Geo.widez(P.K.size(k), P.Rot.mat(P.Rot.q(rt))), z, oz, Nat.div(P.K.size(k), 2n), past))

# ---- the four lemmas ----

# past the +z edge: the press turns the cube about +x (its turning about x grows)
def sign_pz(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(oz, P.K.size(k)), Nat.add(z, Nat.div(P.K.size(k), 2n))) == True{} : Bool})
  -> {P.Z.above(P.Wv.x(P.Rot.w(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))), P.Wv.x(P.Rot.w(rt))) == True{} : Bool}:
  sgz_press_pz(rt, P.K.size(k), P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)), P.K.g(k), heavy, sgz_armz_pz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past))

# past the -z edge: about -x
def sign_nz(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(z, Nat.div(P.K.size(k), 2n)), oz) == True{} : Bool})
  -> {P.Z.above(P.Wv.x(P.Rot.w(rt)), P.Wv.x(P.Rot.w(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))) == True{} : Bool}:
  sgz_press_nz(rt, P.K.size(k), P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)), P.K.g(k), heavy, sgz_armz_nz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past))

# the arm is off the middle (Body.spin keeps the turning)
def tip_pz(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(oz, P.K.size(k)), Nat.add(z, Nat.div(P.K.size(k), 2n))) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))))) == True{} : Bool}:
  lt_add_r(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), sgz_above_neg_mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k))), sgz_armz_pz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past)))

def tip_nz(+k: P.K, +heavy: {Nat.is_lt(0n, P.K.g(k)) == True{} : Bool},
  +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  +under: {Nat.is_le(P.Geo.top(P.K.size(k), oy, ort), Nat.add(y, Nat.div(P.K.size(k), 2n))) == True{} : Bool},
  +across: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), x, ox)) == True{} : Bool},
  +along: {Nat.is_lt(0n, P.Geo.lap(P.K.size(k), z, oz)) == True{} : Bool},
  +past: {Nat.is_lt(Nat.add(z, Nat.div(P.K.size(k), 2n)), oz) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))))) == True{} : Bool}:
  lt_add_r(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k)))), sgz_above_pos_mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), P.K.size(k))), sgz_armz_nz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past)))

# step_o, with the spin after the step handed on as a parameter rt2 and
# three facts about it proven once for the spin the step makes: a law that
# then turns the body never has to work that spin out again
def step_o3.go(+vx2: P.Z, +vy2: P.Z, +vz2: P.Z, +hh2: Bool, +w1: P.Z, +w2: P.Z, +w3: P.Z,
  +k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +og: Bool, +oh: Bool, +ort: P.Rot, +x: Nat, +y: Nat, +z: Nat, +rt: P.Rot,
  -R: (P.Body & List<&2, P.Body>) -> Type, -Q1: P.Rot -> List<&2, P.Body> -> Type, -Q2: P.Rot -> List<&2, P.Body> -> Type, -Q3: P.Rot -> List<&2, P.Body> -> Type,
  hq1: @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> Q1(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), hq2: @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> Q2(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), hq3: @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> Q3(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]),
  hp: @vx2:P.Z -> @vy2:P.Z -> @vz2:P.Z -> @hh2:Bool -> @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> @rt2:P.Rot -> @q1:Q1(rt2, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]) -> @q2:Q2(rt2, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]) -> @q3:Q3(rt2, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]) -> R((P.Body{x, y, z, vx2, vy2, vz2, True{}, hh2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))
  -> R((P.Body{x, y, z, vx2, vy2, vz2, True{}, hh2, P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])):
  hp(vx2, vy2, vz2, hh2, w1, w2, w3, P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), hq1(w1, w2, w3), hq2(w1, w2, w3), hq3(w1, w2, w3))

def step_o3(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: P.Z, +ovy: P.Z, +ovz: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +h: Bool, +rt: P.Rot,
  -R: (P.Body & List<&2, P.Body>) -> Type, -Q1: P.Rot -> List<&2, P.Body> -> Type, -Q2: P.Rot -> List<&2, P.Body> -> Type, -Q3: P.Rot -> List<&2, P.Body> -> Type,
  held: {P.Tick.sinks(P.K.size(k), [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], x, y, z, P.Rot.q(rt)) == False{} : Bool},
  off: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt)) == False{} : Bool},
  hq1: @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> Q1(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), hq2: @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> Q2(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), hq3: @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> Q3(P.Rot.held(False{}, rt, P.K.size(k), x, y, z, P.K.g(k), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]),
  hp: @vx2:P.Z -> @vy2:P.Z -> @vz2:P.Z -> @hh2:Bool -> @w1:P.Z -> @w2:P.Z -> @w3:P.Z -> @rt2:P.Rot -> @q1:Q1(rt2, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]) -> @q2:Q2(rt2, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]) -> @q3:Q3(rt2, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]) -> R((P.Body{x, y, z, vx2, vy2, vz2, True{}, hh2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))
  -> R(P.Body.step(k, [P.Body{ox, oy, oz, ovx, ovy, ovz, og, oh, ort}], P.In.idle(),
       P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, h, rt})):
  step_o(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, rt, R, held, off,
    (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (hh2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) =>
      step_o3.go(vx2, vy2, vz2, hh2, w1, w2, w3, k, ox, oy, oz, og, oh, ort, x, y, z, rt, R, Q1, Q2, Q3, hq1, hq2, hq3, hp))

def Laws.past_the_edge_it_tips_px(k, heavy, o, x, y, z, h, rt, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, rt,
        (r: P.Body & List<&2, P.Body>) => {P.Z.above(P.Wv.z(P.Rot.w(rt)), P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(r))))) == True{} : Bool},
        held, off,
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) =>
          sign_px(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past))

def Laws.past_the_edge_it_tips_nx(k, heavy, o, x, y, z, h, rt, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, rt,
        (r: P.Body & List<&2, P.Body>) => {P.Z.above(P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(r)))), P.Wv.z(P.Rot.w(rt))) == True{} : Bool},
        held, off,
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) =>
          sign_nx(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past))

def Laws.past_the_edge_it_tips_pz(k, heavy, o, x, y, z, h, rt, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, rt,
        (r: P.Body & List<&2, P.Body>) => {P.Z.above(P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(r)))), P.Wv.x(P.Rot.w(rt))) == True{} : Bool},
        held, off,
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) =>
          sign_pz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past))

def Laws.past_the_edge_it_tips_nz(k, heavy, o, x, y, z, h, rt, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, rt,
        (r: P.Body & List<&2, P.Body>) => {P.Z.above(P.Wv.x(P.Rot.w(rt)), P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(r))))) == True{} : Bool},
        held, off,
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) =>
          sign_nz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, rt, under, across, along, past))

def tip_asm_px(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +q: P.Quat, +vx2: P.Z, +vy2: P.Z, +vz2: P.Z, +h2: Bool, +rt2: P.Rot,
  +q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}, +q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}, +q3: {P.Z.above(P.Pos{0n}, P.Wv.z(P.Rot.w(rt2))) == True{} : Bool})
  -> {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Pos{0n}, P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))))))) == True{} : Bool}:
  or_there(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Pos{0n}, P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))))),
    spin_o(P.K.size(k), P.K.g(k), x, y, z, vx2, vy2, vz2, h2, rt2, P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort},
      (w: P.Wv) => {P.Z.above(P.Pos{0n}, P.Wv.z(w)) == True{} : Bool}, q1, q2, q3, halfc_neg(P.Wv.z(P.Rot.w(rt2)), q3)))

def Laws.tipping_is_never_thrown_away_px(k, heavy, o, x, y, z, h, q, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o3(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, P.Rot{q, P.Wv.zero()},
        (r: P.Body & List<&2, P.Body>) => {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r)))), q)), P.Z.above(P.Pos{0n}, P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r))))))) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(r)) == False{} : Bool}, (r: P.Rot) => (os: List<&2, P.Body>) => {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))))) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Z.above(P.Pos{0n}, P.Wv.z(P.Rot.w(r))) == True{} : Bool},
        held, off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => tip_px(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => sign_px(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => (rt2: P.Rot) => (q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}) => (q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}) => (q3: {P.Z.above(P.Pos{0n}, P.Wv.z(P.Rot.w(rt2))) == True{} : Bool}) =>
          tip_asm_px(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, q, vx2, vy2, vz2, h2, rt2, q1, q2, q3))

def tip_asm_nx(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +q: P.Quat, +vx2: P.Z, +vy2: P.Z, +vz2: P.Z, +h2: Bool, +rt2: P.Rot,
  +q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}, +q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}, +q3: {P.Z.above(P.Wv.z(P.Rot.w(rt2)), P.Pos{0n}) == True{} : Bool})
  -> {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))))), P.Pos{0n})) == True{} : Bool}:
  or_there(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))))), P.Pos{0n}),
    spin_o(P.K.size(k), P.K.g(k), x, y, z, vx2, vy2, vz2, h2, rt2, P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort},
      (w: P.Wv) => {P.Z.above(P.Wv.z(w), P.Pos{0n}) == True{} : Bool}, q1, q2, q3, halfc_pos(P.Wv.z(P.Rot.w(rt2)), q3)))

def Laws.tipping_is_never_thrown_away_nx(k, heavy, o, x, y, z, h, q, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o3(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, P.Rot{q, P.Wv.zero()},
        (r: P.Body & List<&2, P.Body>) => {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r)))), q)), P.Z.above(P.Wv.z(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r))))), P.Pos{0n})) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(r)) == False{} : Bool}, (r: P.Rot) => (os: List<&2, P.Body>) => {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))))) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Z.above(P.Wv.z(P.Rot.w(r)), P.Pos{0n}) == True{} : Bool},
        held, off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => tip_nx(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => sign_nx(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => (rt2: P.Rot) => (q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}) => (q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}) => (q3: {P.Z.above(P.Wv.z(P.Rot.w(rt2)), P.Pos{0n}) == True{} : Bool}) =>
          tip_asm_nx(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, q, vx2, vy2, vz2, h2, rt2, q1, q2, q3))

def tip_asm_pz(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +q: P.Quat, +vx2: P.Z, +vy2: P.Z, +vz2: P.Z, +h2: Bool, +rt2: P.Rot,
  +q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}, +q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}, +q3: {P.Z.above(P.Wv.x(P.Rot.w(rt2)), P.Pos{0n}) == True{} : Bool})
  -> {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))))), P.Pos{0n})) == True{} : Bool}:
  or_there(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))))), P.Pos{0n}),
    spin_o(P.K.size(k), P.K.g(k), x, y, z, vx2, vy2, vz2, h2, rt2, P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort},
      (w: P.Wv) => {P.Z.above(P.Wv.x(w), P.Pos{0n}) == True{} : Bool}, q1, q2, q3, halfc_pos(P.Wv.x(P.Rot.w(rt2)), q3)))

def Laws.tipping_is_never_thrown_away_pz(k, heavy, o, x, y, z, h, q, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o3(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, P.Rot{q, P.Wv.zero()},
        (r: P.Body & List<&2, P.Body>) => {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r)))), q)), P.Z.above(P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r))))), P.Pos{0n})) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(r)) == False{} : Bool}, (r: P.Rot) => (os: List<&2, P.Body>) => {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))))) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Z.above(P.Wv.x(P.Rot.w(r)), P.Pos{0n}) == True{} : Bool},
        held, off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => tip_pz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => sign_pz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => (rt2: P.Rot) => (q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}) => (q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}) => (q3: {P.Z.above(P.Wv.x(P.Rot.w(rt2)), P.Pos{0n}) == True{} : Bool}) =>
          tip_asm_pz(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, q, vx2, vy2, vz2, h2, rt2, q1, q2, q3))

def tip_asm_nz(+k: P.K, +ox: Nat, +oy: Nat, +oz: Nat, +w1: P.Z, +w2: P.Z, +w3: P.Z, +og: Bool, +oh: Bool, +ort: P.Rot,
  +x: Nat, +y: Nat, +z: Nat, +q: P.Quat, +vx2: P.Z, +vy2: P.Z, +vz2: P.Z, +h2: Bool, +rt2: P.Rot,
  +q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}, +q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}, +q3: {P.Z.above(P.Pos{0n}, P.Wv.x(P.Rot.w(rt2))) == True{} : Bool})
  -> {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Pos{0n}, P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}])))))))) == True{} : Bool}:
  or_there(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))), q)), P.Z.above(P.Pos{0n}, P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), (P.Body{x, y, z, vx2, vy2, vz2, True{}, h2, rt2}, [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}]))))))),
    spin_o(P.K.size(k), P.K.g(k), x, y, z, vx2, vy2, vz2, h2, rt2, P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort},
      (w: P.Wv) => {P.Z.above(P.Pos{0n}, P.Wv.x(w)) == True{} : Bool}, q1, q2, q3, halfc_neg(P.Wv.x(P.Rot.w(rt2)), q3)))

def Laws.tipping_is_never_thrown_away_nz(k, heavy, o, x, y, z, h, q, held, off, under, across, along, past):
  match o:
    case P.Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +ort}:
      step_o3(k, ox, oy, oz, ovx, ovy, ovz, og, oh, ort, x, y, z, h, P.Rot{q, P.Wv.zero()},
        (r: P.Body & List<&2, P.Body>) => {Bool.or(Bool.not(P.Quat.same(P.Rot.q(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r)))), q)), P.Z.above(P.Pos{0n}, P.Wv.x(P.Rot.w(P.Body.rot(P.Tick.body(P.Tick.spin(P.K.size(k), P.K.g(k), r))))))) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(r)) == False{} : Bool}, (r: P.Rot) => (os: List<&2, P.Body>) => {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(r), os, P.Foot.none()), P.Rot.mat(P.Rot.q(r)), P.K.size(k)))))) == True{} : Bool},
        (r: P.Rot) => (os: List<&2, P.Body>) => {P.Z.above(P.Pos{0n}, P.Wv.x(P.Rot.w(r))) == True{} : Bool},
        held, off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => off,
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => tip_nz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => sign_nz(k, heavy, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, P.Rot{q, P.Wv.zero()}, under, across, along, past),
        (vx2: P.Z) => (vy2: P.Z) => (vz2: P.Z) => (h2: Bool) => (w1: P.Z) => (w2: P.Z) => (w3: P.Z) => (rt2: P.Rot) => (q1: {P.Geo.onfloor(P.K.size(k), y, P.Rot.q(rt2)) == False{} : Bool}) => (q2: {Nat.is_lt(0n, Nat.add(P.Z.mag(P.Wv.x(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))), P.Z.mag(P.Wv.z(P.Hold.arm(P.Geo.foot(P.K.size(k), x, y, z, P.Rot.q(rt2), [P.Body{ox, oy, oz, w1, w2, w3, og, oh, ort}], P.Foot.none()), P.Rot.mat(P.Rot.q(rt2)), P.K.size(k)))))) == True{} : Bool}) => (q3: {P.Z.above(P.Pos{0n}, P.Wv.x(P.Rot.w(rt2))) == True{} : Bool}) =>
          tip_asm_nz(k, ox, oy, oz, w1, w2, w3, og, oh, ort, x, y, z, q, vx2, vy2, vz2, h2, rt2, q1, q2, q3))


# A stopped turn does not wind up
# ===============================
# A body standing after its step, whose turn the tick refuses, ends the
# tick turning half as fast as the step left it, part by part and rounded
# up (Wv.halfc), or not at all. The turn is followed down as the turning
# laws follow it, from Tick.turn to Body.spin, with the claim written as
# what follows from the refusal (STOP): where the search moved the
# orientation there is nothing to show, and it has only to be told apart
# from a refusal by the answer Tick.moved gave -- never by working the
# search out.
# ---------------------------------------------------------------------------

# twice each part of w is at most one more than that part of w0
def HALFB(+w0: P.Wv, +w: P.Wv) -> Type:
  {Nat.is_le(Nat.add(P.Z.mag(P.Wv.x(w)), P.Z.mag(P.Wv.x(w))), Nat.add(1n, P.Z.mag(P.Wv.x(w0)))) == True{} : Bool}
  & {Nat.is_le(Nat.add(P.Z.mag(P.Wv.y(w)), P.Z.mag(P.Wv.y(w))), Nat.add(1n, P.Z.mag(P.Wv.y(w0)))) == True{} : Bool}
  & {Nat.is_le(Nat.add(P.Z.mag(P.Wv.z(w)), P.Z.mag(P.Wv.z(w))), Nat.add(1n, P.Z.mag(P.Wv.z(w0)))) == True{} : Bool}

def halfb_half(+w: P.Wv) -> HALFB(w, P.Wv.halfc(w)):
  (zhalf_z(P.Wv.x(w)), zhalf_z(P.Wv.y(w)), zhalf_z(P.Wv.z(w)))

def halfb_zero(+w: P.Wv) -> HALFB(w, P.Wv.zero()):
  ({==}, {==}, {==})

# a part of size 0 is at most half of one more than itself
def zero_comp(x: P.Z, h: {Nat.is_eq(P.Z.mag(x), 0n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P.Z.mag(x), P.Z.mag(x)), Nat.add(1n, P.Z.mag(x))) == True{} : Bool}:
  match x:
    case P.Pos{n}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          Empty.absurd({Nat.is_le(Nat.add(1n+m, 1n+m), Nat.add(1n, 1n+m)) == True{} : Bool}, clash2(h))
    case P.Neg{n}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          Empty.absurd({Nat.is_le(Nat.add(1n+m, 1n+m), Nat.add(1n, 1n+m)) == True{} : Bool}, clash2(h))

# a body not turning at all: the tick leaves it as it is, and nothing is
# more than half of one
def halfb_null(w: P.Wv, +hn: {P.Wv.null(w) == True{} : Bool}) -> HALFB(w, w):
  match w:
    case P.Wv{+x, +y, +z}:
      (zero_comp(x, and_l(Nat.is_eq(P.Z.mag(x), 0n), Bool.and(Nat.is_eq(P.Z.mag(y), 0n), Nat.is_eq(P.Z.mag(z), 0n)), hn)),
       zero_comp(y, and_l(Nat.is_eq(P.Z.mag(y), 0n), Nat.is_eq(P.Z.mag(z), 0n),
         and_r(Nat.is_eq(P.Z.mag(x), 0n), Bool.and(Nat.is_eq(P.Z.mag(y), 0n), Nat.is_eq(P.Z.mag(z), 0n)), hn))),
       zero_comp(z, and_r(Nat.is_eq(P.Z.mag(y), 0n), Nat.is_eq(P.Z.mag(z), 0n),
         and_r(Nat.is_eq(P.Z.mag(x), 0n), Bool.and(Nat.is_eq(P.Z.mag(y), 0n), Nat.is_eq(P.Z.mag(z), 0n)), hn))))

# the law for b, what the turn of a body turned by rt left: if b is
# turned as rt was, it turns at most half as fast
def STOP(+rt: P.Rot, -b: P.Body) -> Type:
  {P.Quat.same(P.Rot.q(P.Body.rot(b)), P.Rot.q(rt)) == True{} : Bool} -> HALFB(P.Rot.w(rt), P.Rot.w(P.Body.rot(b)))

# Body.spin, told by `same` whether the search left the orientation as it
# was: then half the turning or none; else it moved, and a body that moved
# is not turned as it was
def spin_stop2(same: Bool, tip: Bool, +u1: Nat, +u2: Nat, +u3: Nat, +u4: P.Z, +u5: P.Z, +u6: P.Z, +u7: Bool, +u8: Bool,
  +u9: P.Rot, +rt: P.Rot, +hs: {P.Quat.same(P.Rot.q(u9), P.Rot.q(rt)) == same : Bool})
  -> STOP(rt, P.Body{u1, u2, u3, u4, u5, u6, u7, u8,
       P.Body.spin.rot(tip, Bool.not(same), P.Body{u1, u2, u3, u4, u5, u6, u7, u8, u9}, rt)}):
  match same:
    case True{}:
      match tip:
        case True{}:
          (st: {P.Quat.same(P.Rot.q(u9), P.Rot.q(rt)) == True{} : Bool}) => halfb_half(P.Rot.w(rt))
        case False{}:
          (st: {P.Quat.same(P.Rot.q(u9), P.Rot.q(rt)) == True{} : Bool}) => halfb_zero(P.Rot.w(rt))
    case False{}:
      (st: {P.Quat.same(P.Rot.q(u9), P.Rot.q(rt)) == True{} : Bool}) =>
        Empty.absurd(HALFB(P.Rot.w(rt), P.Rot.w(u9)),
          clash(Equal.trans(Bool, True{}, P.Quat.same(P.Rot.q(u9), P.Rot.q(rt)), False{},
            Equal.sym(Bool, P.Quat.same(P.Rot.q(u9), P.Rot.q(rt)), True{}, st), hs)))

def spin_stop(tip: Bool, b: P.Body, +rt: P.Rot)
  -> Once.Body((kb: P.Body) => STOP(rt, kb), P.Body.spin(tip, P.Tick.moved(b, rt), b, rt)):
  match b:
    case P.Body{+u1, +u2, +u3, +u4, +u5, +u6, +u7, +u8, +u9}:
      spin_stop2(P.Quat.same(P.Rot.q(u9), P.Rot.q(rt)), tip, u1, u2, u3, u4, u5, u6, u7, u8, u9, rt, {==})

def pivota0_stop.k1(md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, a: P.Wv)
  -> Once.Body((kb: P.Body) => STOP(rt, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  P.Wv{+ax, +ay, +az} = a
  spin_stop(Nat.is_lt(0n, Nat.add(P.Z.mag(ax), P.Z.mag(az))),
    P.Tick.shrink(7n, P.Tick.shrink.pair(P.Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az), rt), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az),
    rt)

def pivota0_stop(+md: P.Mat, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +w2: P.Wv, +a: P.Wv)
  -> STOP(rt, P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a)):
  Once.Body.down((kb: P.Body) => STOP(rt, kb), P.Tick.pivota0(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a),
    pivota0_stop.k1(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, w2, a))

def pivota_stop(md: P.Mat, +s: Nat, +g: Nat, obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, +vx: P.Z, +vy: P.Z,
  +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +a: P.Wv)
  -> STOP(rt, P.Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)):
  match obs:
    case []:
      pivota0_stop(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a)
    case o <> rest:
      pivota0_stop(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, P.Tick.pivota0.w2(s, rt, a), a)

def turn2_stop(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: P.Z, +vy: P.Z, +vz: P.Z, +gr: Bool, +hit: Bool, +rt: P.Rot, +r2: P.Rot, +md: P.Mat,
  +hheld: {held == True{} : Bool})
  -> STOP(rt, P.Tick.turn2(held, floor, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)):
  match held floor:
    case False{} _:
      Empty.absurd(STOP(rt, P.Tick.place(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, P.Rot{P.Rot.q(rt), P.Wv.zero()}, r2)), clash2(hheld))
    case True{} False{}:
      pivota_stop(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2,
        P.Hold.arm(P.Geo.foot(s, x, y, z, P.Rot.q(rt), obs, P.Foot.none()), P.Rot.mat(P.Rot.q(rt)), s))
    case True{} True{}:
      pivota_stop(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, P.Hold.low(P.Rot.mat(P.Rot.q(rt)), s))

def turn1b_stop(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, b: P.Body, +hgr: {P.Body.ground(b) == True{} : Bool})
  -> STOP(P.Body.rot(b), P.Tick.turn1b(s, g, obs, b)):
  match b:
    case P.Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt}:
      turn2_stop(gr, P.Geo.onfloor(s, y, P.Rot.q(rt)), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
        P.Rot.free(rt), P.Rot.mat(P.Quat.half(P.Quat.step(P.Rot.w(rt), P.Wv.mag(P.Rot.w(rt))))), hgr)

def turn1_stop(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +hgr: {P.Body.ground(b) == True{} : Bool},
  +hst: {P.Wv.null(P.Rot.w(P.Body.rot(b))) == still : Bool})
  -> STOP(P.Body.rot(b), P.Tick.turn1(still, s, g, obs, b)):
  match still:
    case True{}:
      (st: {P.Quat.same(P.Rot.q(P.Body.rot(b)), P.Rot.q(P.Body.rot(b))) == True{} : Bool}) => halfb_null(P.Rot.w(P.Body.rot(b)), hst)
    case False{}:
      turn1b_stop(s, g, obs, b, hgr)

def turn0_stop(+s: Nat, +g: Nat, +obs: List<&2, P.Body>, +b: P.Body, +hgr: {P.Body.ground(b) == True{} : Bool})
  -> STOP(P.Body.rot(b), P.Tick.turn0(s, g, obs, b)):
  turn1_stop(P.Wv.null(P.Rot.w(P.Body.rot(b))), s, g, obs, b, hgr, {==})

def turn_stop(+s: Nat, +g: Nat, obs: List<&2, P.Body>, +b: P.Body, +hgr: {P.Body.ground(b) == True{} : Bool})
  -> STOP(P.Body.rot(b), P.Tick.turn(s, g, obs, b)):
  match obs:
    case []:
      turn0_stop(s, g, [], b, hgr)
    case o <> rest:
      turn0_stop(s, g, o <> rest, b, hgr)

# the turn of a tick, on the pair the step hands it
def stop_pair(+s: Nat, +g: Nat, r: P.Body & List<&2, P.Body>, +hgr: {P.Body.ground(P.Tick.body(r)) == True{} : Bool})
  -> STOP(P.Body.rot(P.Tick.body(r)), P.Tick.body(P.Tick.spin(s, g, r))):
  match r:
    case (b, obs):
      turn_stop(s, g, obs, b, hgr)

def Laws.a_stopped_turn_does_not_wind_up(k, obs, inp, b, held, stopped):
  stop_pair(P.K.size(k), P.K.g(k), P.Body.step(k, obs, inp, b), held)(stopped)

# The rigid bodies
# ----------------

def rg_and(x: Bool, -y: Bool, hx: {x == True{} : Bool}, hy: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  match x:
    case True{}:
      hy
    case False{}:
      Empty.absurd({Bool.and(False{}, y) == True{} : Bool}, clash2(hx))

# the contact Ct.safe hands on is within Coulomb, whatever it was handed
def rg_safe_pick(ok: Bool, +k: P.K, c: G.Ct, e: {G.Ct.coul(k, c) == ok : Bool})
  -> {G.Ct.coul(k, G.Ct.safe2(ok, c)) == True{} : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      match c:
        case G.Ct{a, b, fl, ra, rb, n, gap, +jn, jt}:
          le_zero_l(Nat.mul(G.Imp.lim(k, jn), G.Imp.lim(k, jn)))

def rg_safe(+k: P.K, +c: G.Ct) -> {G.Ct.coul(k, G.Ct.safe(k, c)) == True{} : Bool}:
  rg_safe_pick(G.Ct.coul(k, c), k, c, {==})

# a step of the solver puts in front the contact Ct.safe hands on, and
# gives back the rest as it was
def rg_one(+k: P.K, +c: G.Ct, +st: G.St, h: {G.Ct.coulomb(k, G.Rb.done(st)) == True{} : Bool})
  -> {G.Ct.coulomb(k, G.Rb.done(G.Imp.one(k, c, st))) == True{} : Bool}:
  match st:
    case G.St{done, +bs}:
      +raw = G.Imp.raw(k, c, G.Bs.at(bs, G.Ct.a(c)), G.Bs.at(bs, G.Ct.b(c)))
      rg_and(G.Ct.coul(k, G.Ct.safe(k, G.R2.c(raw))), G.Ct.coulomb(k, done), rg_safe(k, G.R2.c(raw)), h)

def rg_pass(+k: P.K, cs: List<&2, G.Ct>, +st: G.St, h: {G.Ct.coulomb(k, G.Rb.done(st)) == True{} : Bool})
  -> {G.Ct.coulomb(k, G.Rb.done(G.Imp.pass(k, cs, st))) == True{} : Bool}:
  match cs:
    case []:
      h
    case +c <> rest:
      rg_pass(k, rest, G.Imp.one(k, c, st), rg_one(k, c, st, h))

# a pass starts from no contacts, so whatever it is handed, all it hands
# back went through a step
def rg_again(+k: P.K, +st: G.St) -> {G.Ct.coulomb(k, G.Rb.done(G.Imp.again(k, st))) == True{} : Bool}:
  match st:
    case G.St{done, +bs}:
      rg_pass(k, done, G.St{[], bs}, {==})

def rg_iter(n: Nat, +k: P.K, +st: G.St, h: {G.Ct.coulomb(k, G.Rb.done(st)) == True{} : Bool})
  -> {G.Ct.coulomb(k, G.Rb.done(G.Imp.iter(n, k, st))) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+m:
      rg_iter(m, k, G.Imp.again(k, st), rg_again(k, st))

def Laws.rigid_coulomb(k, bs, ss):
  rg_iter(15n, k, G.Imp.again(k, G.St{G.Ct.all(bs, k, 0n, ss, []), G.Rb.fall(k, bs)}),
    rg_again(k, G.St{G.Ct.all(bs, k, 0n, ss, []), G.Rb.fall(k, bs)}))

def rg_not(a: Bool, -b: Bool, e: {a == b : Bool}) -> {Bool.not(a) == Bool.not(b) : Bool}:
  %e : {Bool.not(a) == Bool.not(_) : Bool}
  {==}

def rg_and2(x: Bool, -x2: Bool, y: Bool, -y2: Bool, ex: {x == x2 : Bool}, ey: {y == y2 : Bool})
  -> {Bool.and(x, y) == Bool.and(x2, y2) : Bool}:
  %ex : {Bool.and(x, y) == Bool.and(_, y2) : Bool}
  %ey : {Bool.and(x, y) == Bool.and(x, _) : Bool}
  {==}

def rg_trans(a: Bool, -b: Bool, -c: Bool, e1: {a == b : Bool}, e2: {b == c : Bool}) -> {a == c : Bool}:
  %e2 : {a == _ : Bool}
  e1

def rg_absurd(x: Bool, e: {x == False{} : Bool}, h: {x == True{} : Bool}) -> {False{} == True{} : Bool}:
  %e : {_ == True{} : Bool}
  h

# stopping a body changes nothing the gate looks at: it sees a body bare
# (R.bare), where it is and how it is turned
def rg_h4o(near: Bool, +s: Nat, +p: P.Body, +o: P.Body)
  -> {G.R.hits4(near, s, p, G.B.set(o, G.V.zero(), G.V.zero())) == G.R.hits4(near, s, p, o) : Bool}:
  match near:
    case False{}:
      {==}
    case True{}:
      {==}

def rg_hits_o(+s: Nat, +p: P.Body, +o: P.Body)
  -> {G.R.hits(s, p, G.B.set(o, G.V.zero(), G.V.zero())) == G.R.hits(s, p, o) : Bool}:
  rg_h4o(G.Ct.near(s, 0n, G.B.d(p, o)), s, p, o)

def rg_h4p(near: Bool, +s: Nat, +b: P.Body, +o: P.Body)
  -> {G.R.hits4(near, s, G.B.set(b, G.V.zero(), G.V.zero()), o) == G.R.hits4(near, s, b, o) : Bool}:
  match near:
    case False{}:
      {==}
    case True{}:
      {==}

def rg_hits_p(+s: Nat, +b: P.Body, +o: P.Body)
  -> {G.R.hits(s, G.B.set(b, G.V.zero(), G.V.zero()), o) == G.R.hits(s, b, o) : Bool}:
  rg_h4p(G.Ct.near(s, 0n, G.B.d(b, o)), s, b, o)

def rg_floor(+s: Nat, +b: P.Body) -> {G.Mv.floor(s, G.B.set(b, G.V.zero(), G.V.zero())) == G.Mv.floor(s, b) : Bool}:
  {==}

def rg_clear_p(+s: Nat, +b: P.Body, obs: List<&2, P.Body>)
  -> {G.Mv.clear(s, G.B.set(b, G.V.zero(), G.V.zero()), obs) == G.Mv.clear(s, b, obs) : Bool}:
  match obs:
    case []:
      {==}
    case +o <> +rest:
      rg_and2(Bool.not(G.R.hits(s, G.B.set(b, G.V.zero(), G.V.zero()), o)), Bool.not(G.R.hits(s, b, o)),
        G.Mv.clear(s, G.B.set(b, G.V.zero(), G.V.zero()), rest), G.Mv.clear(s, b, rest),
        rg_not(G.R.hits(s, G.B.set(b, G.V.zero(), G.V.zero()), o), G.R.hits(s, b, o), rg_hits_p(s, b, o)),
        rg_clear_p(s, b, rest))

def rg_clear_still(+s: Nat, +p: P.Body, rest: List<&2, P.Body>, +ss: List<&2, P.Body>)
  -> {G.Mv.clear(s, p, List.append(&2, P.Body, G.En.still(rest), ss)) == G.Mv.clear(s, p, List.append(&2, P.Body, rest, ss)) : Bool}:
  match rest:
    case []:
      {==}
    case +o <> +r:
      rg_and2(Bool.not(G.R.hits(s, p, G.B.set(o, G.V.zero(), G.V.zero()))), Bool.not(G.R.hits(s, p, o)),
        G.Mv.clear(s, p, List.append(&2, P.Body, G.En.still(r), ss)), G.Mv.clear(s, p, List.append(&2, P.Body, r, ss)),
        rg_not(G.R.hits(s, p, G.B.set(o, G.V.zero(), G.V.zero())), G.R.hits(s, p, o), rg_hits_o(s, p, o)),
        rg_clear_still(s, p, r, ss))

# the bodies stopped where they are are apart exactly when they were
def rg_apart_still(+s: Nat, bs: List<&2, P.Body>, +ss: List<&2, P.Body>)
  -> {G.Rb.apart(s, G.En.still(bs), ss) == G.Rb.apart(s, bs, ss) : Bool}:
  match bs:
    case []:
      {==}
    case +b <> +rest:
      +b0 = G.B.set(b, G.V.zero(), G.V.zero())
      +obs0 = List.append(&2, P.Body, G.En.still(rest), ss)
      +obs = List.append(&2, P.Body, rest, ss)
      rg_and2(G.Mv.fits(s, b0, obs0), G.Mv.fits(s, b, obs), G.Rb.apart(s, G.En.still(rest), ss), G.Rb.apart(s, rest, ss),
        rg_and2(G.Mv.floor(s, b0), G.Mv.floor(s, b), G.Mv.clear(s, b0, obs0), G.Mv.clear(s, b, obs),
          rg_floor(s, b),
          rg_trans(G.Mv.clear(s, b0, obs0), G.Mv.clear(s, b, obs0), G.Mv.clear(s, b, obs),
            rg_clear_p(s, b, obs0), rg_clear_still(s, b, rest, ss))),
        rg_apart_still(s, rest, ss))

def rg_kept3(was: Bool, +bs: List<&2, P.Body>, +out: List<&2, P.Body>, +s: Nat, +ss: List<&2, P.Body>,
  e: {G.Rb.apart(s, bs, ss) == was : Bool}, start: {G.Rb.apart(s, bs, ss) == True{} : Bool})
  -> {G.Rb.apart(s, G.Rb.kept3(was, bs, out), ss) == True{} : Bool}:
  match was:
    case True{}:
      %Equal.sym(Bool, G.Rb.apart(s, G.En.still(bs), ss), G.Rb.apart(s, bs, ss), rg_apart_still(s, bs, ss)) : {_ == True{} : Bool}
      start
    case False{}:
      Empty.absurd({G.Rb.apart(s, out, ss) == True{} : Bool}, clash2(rg_absurd(G.Rb.apart(s, bs, ss), e, start)))

def rg_kept2(ok: Bool, +s: Nat, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>, +out: List<&2, P.Body>,
  e: {G.Rb.apart(s, out, ss) == ok : Bool}, start: {G.Rb.apart(s, bs, ss) == True{} : Bool})
  -> {G.Rb.apart(s, G.Rb.kept2(ok, s, bs, ss, out), ss) == True{} : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      rg_kept3(G.Rb.apart(s, bs, ss), bs, out, s, ss, {==}, start)

def Laws.rigid_apart(k, bs, ss, start):
  +out = G.Rb.out(k, bs, ss, G.Imp.iter(16n, k, G.St{G.Ct.all(bs, k, 0n, ss, []), G.Rb.fall(k, bs)}))
  rg_kept2(G.Rb.apart(P.K.size(k), out, ss), P.K.size(k), bs, ss, out, {==}, start)

def rg_or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a body stopped where it is has no more energy than it had: the same
# height, and no moving or turning
def rg_div0(+d: Nat) -> {Nat.div(0n, d) == 0n : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rg_e_one(+k: P.K, +y0: Nat, +b: P.Body)
  -> {Nat.is_le(G.En.one(k, y0, G.B.set(b, G.V.zero(), G.V.zero())), G.En.one(k, y0, b)) == True{} : Bool}:
  +d = P.Pick.high(Nat.div(Nat.mul(P.K.size(k), P.K.size(k)), 65536n), 1n)
  +gy = Nat.mul(P.K.g(k), Nat.sub(P.Body.y(b), y0))
  +top = G.En.one(k, y0, b)
  %Equal.sym(Nat, Nat.div(0n, d), 0n, rg_div0(d)) : {Nat.is_le(Nat.add(_, gy), top) == True{} : Bool}
  le_add_l(gy, Nat.add(G.V.sq(G.B.v(b)), G.En.rot(P.K.size(k), G.B.L(b))))

def rg_e_still(+k: P.K, bs: List<&2, P.Body>)
  -> {Nat.is_le(G.En.all(k, bs, G.En.still(bs)), G.En.all(k, bs, bs)) == True{} : Bool}:
  match bs:
    case []:
      {==}
    case +b <> +rest:
      +y0 = Nat.sub(P.Body.y(b), P.K.size(k))
      le_add2(G.En.one(k, y0, G.B.set(b, G.V.zero(), G.V.zero())), G.En.one(k, y0, b),
        G.En.all(k, rest, G.En.still(rest)), G.En.all(k, rest, rest), rg_e_one(k, y0, b), rg_e_still(k, rest))

# the energy gate: whatever it hands back has no more energy than the
# bodies began with
def rg_cut4(ok: Bool, +k: P.K, +b0s: List<&2, P.Body>, +e0: Nat, +bs: List<&2, P.Body>,
  e: {Nat.is_le(G.En.all(k, b0s, bs), e0) == ok : Bool}, hst: {Nat.is_le(G.En.all(k, b0s, G.En.still(b0s)), e0) == True{} : Bool})
  -> {Nat.is_le(G.En.all(k, b0s, G.En.cut4(ok, b0s, bs)), e0) == True{} : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      hst

def rg_cut2(ok: Bool, +k: P.K, +b0s: List<&2, P.Body>, +e0: Nat, +bs: List<&2, P.Body>, +kin: Nat, +over: Nat,
  hst: {Nat.is_le(G.En.all(k, b0s, G.En.still(b0s)), e0) == True{} : Bool})
  -> {Nat.is_le(G.En.all(k, b0s, G.En.cut2(ok, k, b0s, e0, bs, kin, over)), e0) == True{} : Bool}:
  match ok:
    case False{}:
      hst
    case True{}:
      +sc = G.En.scale(bs, P.Fric.floor(Nat.mul(Nat.div(Nat.mul(Nat.sub(kin, over), 65536n), P.Pick.high(kin, 1n)), 65536n), 65536n))
      rg_cut4(Nat.is_le(G.En.all(k, b0s, sc), e0), k, b0s, e0, sc, {==}, hst)

def rg_gate(over: Bool, +k: P.K, +b0s: List<&2, P.Body>, +bs: List<&2, P.Body>,
  e: {Nat.is_lt(G.En.all(k, b0s, b0s), G.En.all(k, b0s, bs)) == over : Bool},
  hst: {Nat.is_le(G.En.all(k, b0s, G.En.still(b0s)), G.En.all(k, b0s, b0s)) == True{} : Bool})
  -> {Nat.is_le(G.En.all(k, b0s, G.En.gate(over, k, b0s, G.En.all(k, b0s, b0s), G.En.all(k, b0s, bs), bs)), G.En.all(k, b0s, b0s)) == True{} : Bool}:
  match over:
    case False{}:
      lt_false_le(G.En.all(k, b0s, b0s), G.En.all(k, b0s, bs), e)
    case True{}:
      +e0 = G.En.all(k, b0s, b0s)
      +e1 = G.En.all(k, b0s, bs)
      rg_cut2(Nat.is_lt(Nat.sub(e1, e0), G.En.kin(k, bs)), k, b0s, e0, bs, G.En.kin(k, bs), Nat.sub(e1, e0), hst)

def rg_egate(deep: Bool, +k: P.K, +bs: List<&2, P.Body>, +moved: List<&2, P.Body>)
  -> {Bool.or(deep, Nat.is_le(G.En.all(k, bs, G.Rb.egate(k, bs, deep, moved)), G.En.all(k, bs, bs))) == True{} : Bool}:
  match deep:
    case True{}:
      {==}
    case False{}:
      rg_gate(Nat.is_lt(G.En.all(k, bs, bs), G.En.all(k, bs, moved)), k, bs, moved, {==}, rg_e_still(k, bs))

# and the island's end check hands back the gate's bodies, or the bodies
# stopped where they began
def rg_e_k3(was: Bool, +k: P.K, +bs: List<&2, P.Body>, +deep: Bool, +out: List<&2, P.Body>,
  e_out: {Bool.or(deep, Nat.is_le(G.En.all(k, bs, out), G.En.all(k, bs, bs))) == True{} : Bool})
  -> {Bool.or(deep, Nat.is_le(G.En.all(k, bs, G.Rb.kept3(was, bs, out)), G.En.all(k, bs, bs))) == True{} : Bool}:
  match was:
    case True{}:
      rg_or_r(deep, Nat.is_le(G.En.all(k, bs, G.En.still(bs)), G.En.all(k, bs, bs)), rg_e_still(k, bs))
    case False{}:
      e_out

def rg_e_k2(ok: Bool, +k: P.K, +s: Nat, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>, +deep: Bool, +out: List<&2, P.Body>,
  e_out: {Bool.or(deep, Nat.is_le(G.En.all(k, bs, out), G.En.all(k, bs, bs))) == True{} : Bool})
  -> {Bool.or(deep, Nat.is_le(G.En.all(k, bs, G.Rb.kept2(ok, s, bs, ss, out)), G.En.all(k, bs, bs))) == True{} : Bool}:
  match ok:
    case True{}:
      e_out
    case False{}:
      rg_e_k3(G.Rb.apart(s, bs, ss), k, bs, deep, out, e_out)

def Laws.rigid_energy(k, bs, ss):
  +st = G.Imp.iter(16n, k, G.St{G.Ct.all(bs, k, 0n, ss, []), G.Rb.fall(k, bs)})
  +deep = G.Rb.deepof(P.K.size(k), st)
  +moved = G.Rb.moved(k, bs, ss, st)
  +out = G.Rb.egate(k, bs, deep, moved)
  rg_e_k2(G.Rb.apart(P.K.size(k), out, ss), k, P.K.size(k), bs, ss, deep, out, rg_egate(deep, k, bs, moved))

def Laws.rigid_no_push_off_air(k, inp, p, air):
  %Equal.sym(Bool, P.Body.ground(p), False{}, air) : {W.W.drive2(_, k, inp, p) == p : P.Body}
  {==}

# Action and reaction
# -------------------

# Signed numbers add as integers: a + b, the minus parts moved across
def rg_zint_pn(lt: Bool, +x: Nat, +y: Nat, e: {Nat.is_lt(x, y) == lt : Bool})
  -> {Nat.add(Nat.add(P.Z.pos(P.Z.diff(lt, x, y)), 0n), y) == Nat.add(Nat.add(x, 0n), P.Z.neg(P.Z.diff(lt, x, y))) : Nat}:
  match lt:
    case True{}:
      %sub_add(x, y, lt_true_le(x, y, e)) : {_ == Nat.add(Nat.add(x, 0n), Nat.sub(y, x)) : Nat}
      R.eq([x, Nat.sub(y, x)], R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.V{0n}, R.N{0n}}, R.V{1n}}, {==})
    case False{}:
      %sub_add(y, x, lt_false_le(x, y, e)) : {Nat.add(Nat.add(Nat.sub(x, y), 0n), y) == Nat.add(Nat.add(_, 0n), 0n) : Nat}
      R.eq([y, Nat.sub(x, y)], R.Add{R.Add{R.V{1n}, R.N{0n}}, R.V{0n}}, R.Add{R.Add{R.Add{R.V{0n}, R.V{1n}}, R.N{0n}}, R.N{0n}}, {==})

def rg_zint_np(lt: Bool, +x: Nat, +y: Nat, e: {Nat.is_lt(y, x) == lt : Bool})
  -> {Nat.add(Nat.add(P.Z.pos(P.Z.diff(lt, y, x)), x), 0n) == Nat.add(Nat.add(0n, y), P.Z.neg(P.Z.diff(lt, y, x))) : Nat}:
  match lt:
    case True{}:
      %sub_add(y, x, lt_true_le(y, x, e)) : {Nat.add(Nat.add(0n, _), 0n) == Nat.add(Nat.add(0n, y), Nat.sub(x, y)) : Nat}
      R.eq([y, Nat.sub(x, y)], R.Add{R.Add{R.N{0n}, R.Add{R.V{0n}, R.V{1n}}}, R.N{0n}}, R.Add{R.Add{R.N{0n}, R.V{0n}}, R.V{1n}}, {==})
    case False{}:
      %sub_add(x, y, lt_false_le(y, x, e)) : {Nat.add(Nat.add(Nat.sub(y, x), x), 0n) == Nat.add(Nat.add(0n, _), 0n) : Nat}
      R.eq([x, Nat.sub(y, x)], R.Add{R.Add{R.V{1n}, R.V{0n}}, R.N{0n}}, R.Add{R.Add{R.N{0n}, R.Add{R.V{0n}, R.V{1n}}}, R.N{0n}}, {==})

def rg_zint(a: P.Z, b: P.Z)
  -> {Nat.add(Nat.add(P.Z.pos(P.Z.add(a, b)), P.Z.neg(a)), P.Z.neg(b)) == Nat.add(Nat.add(P.Z.pos(a), P.Z.pos(b)), P.Z.neg(P.Z.add(a, b))) : Nat}:
  match a b:
    case P.Pos{+x} P.Pos{+y}:
      R.eq([x, y], R.Add{R.Add{R.Add{R.V{0n}, R.V{1n}}, R.N{0n}}, R.N{0n}}, R.Add{R.Add{R.V{0n}, R.V{1n}}, R.N{0n}}, {==})
    case P.Neg{+x} P.Neg{+y}:
      R.eq([x, y], R.Add{R.Add{R.N{0n}, R.V{0n}}, R.V{1n}}, R.Add{R.Add{R.N{0n}, R.N{0n}}, R.Add{R.V{0n}, R.V{1n}}}, {==})
    case P.Pos{+x} P.Neg{+y}:
      rg_zint_pn(Nat.is_lt(x, y), x, y, {==})
    case P.Neg{+x} P.Pos{+y}:
      rg_zint_np(Nat.is_lt(y, x), x, y, {==})

# and a - b likewise
def rg_zsub(+a: P.Z, b: P.Z)
  -> {Nat.add(Nat.add(P.Z.pos(P.Z.add(a, P.Z.opp(b))), P.Z.neg(a)), P.Z.pos(b)) == Nat.add(Nat.add(P.Z.pos(a), P.Z.neg(b)), P.Z.neg(P.Z.add(a, P.Z.opp(b)))) : Nat}:
  match b:
    case P.Pos{+m}:
      rg_zint(a, P.Neg{m})
    case P.Neg{+m}:
      rg_zint(a, P.Pos{m})


def rg_add_eq(a: Nat, -b: Nat, c: Nat, -d: Nat, e1: {a == b : Nat}, e2: {c == d : Nat}) -> {Nat.add(a, c) == Nat.add(b, d) : Nat}:
  %e2 : {Nat.add(a, c) == Nat.add(b, _) : Nat}
  %e1 : {Nat.add(a, c) == Nat.add(_, c) : Nat}
  {==}

# the algebra of one step: a0 + j + d at one body, b0 - j - d at the other,
# and the list's momentum before (S), after the first write (L1), after
# the second (L2)
def rg_mo_core(+pS: Nat, +nS: Nat, +pL1: Nat, +nL1: Nat, +pL2: Nat, +nL2: Nat, +a0: P.Z, +j: P.Z, +d: P.Z, +b0: P.Z,
  e1: {Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))) == Nat.add(Nat.add(Nat.add(pS, P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), nL1), P.Z.neg(a0)) : Nat},
  e2: {Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))) == Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), nL2), P.Z.neg(b0)) : Nat})
  -> {Nat.add(pL2, nS) == Nat.add(pS, nL2) : Nat}:
  +sum = rg_add_eq(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.neg(a0)), P.Z.neg(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(a0, j))), P.Z.neg(d))), Nat.add(Nat.add(P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(b0)), P.Z.pos(j))), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pS, P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), nL1), P.Z.neg(a0)), Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), nL2), P.Z.neg(b0))), Nat.add(Nat.add(P.Z.pos(a0), P.Z.pos(j)), P.Z.neg(P.Z.add(a0, j)))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.pos(d)), P.Z.neg(P.Z.add(P.Z.add(a0, j), d)))), Nat.add(Nat.add(P.Z.pos(b0), P.Z.neg(j)), P.Z.neg(P.Z.add(b0, P.Z.opp(j))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(d)), Nat.add(Nat.add(P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(d)), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), rg_add_eq(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.neg(a0)), P.Z.neg(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(a0, j))), P.Z.neg(d))), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pS, P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), nL1), P.Z.neg(a0)), Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), nL2), P.Z.neg(b0))), Nat.add(Nat.add(P.Z.pos(a0), P.Z.pos(j)), P.Z.neg(P.Z.add(a0, j)))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.pos(d)), P.Z.neg(P.Z.add(P.Z.add(a0, j), d)))), Nat.add(Nat.add(P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(b0)), P.Z.pos(j)), Nat.add(Nat.add(P.Z.pos(b0), P.Z.neg(j)), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), rg_add_eq(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.neg(a0)), P.Z.neg(j))), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pS, P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), nL1), P.Z.neg(a0)), Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), nL2), P.Z.neg(b0))), Nat.add(Nat.add(P.Z.pos(a0), P.Z.pos(j)), P.Z.neg(P.Z.add(a0, j)))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(a0, j))), P.Z.neg(d)), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.pos(d)), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), rg_add_eq(Nat.add(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(Nat.add(Nat.add(pS, P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), nL1), P.Z.neg(a0)), Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), nL2), P.Z.neg(b0))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.neg(a0)), P.Z.neg(j)), Nat.add(Nat.add(P.Z.pos(a0), P.Z.pos(j)), P.Z.neg(P.Z.add(a0, j))), rg_add_eq(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pS, P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), nL1), P.Z.neg(a0)), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), nL2), P.Z.neg(b0)), e1, e2), rg_zint(a0, j)), rg_zint(P.Z.add(a0, j), d)), rg_zsub(b0, j)), rg_zsub(P.Z.add(b0, P.Z.opp(j)), d))
  +r1 = R.eq([pS, nS, pL1, nL1, pL2, nL2, P.Z.pos(a0), P.Z.neg(a0), P.Z.pos(j), P.Z.neg(j), P.Z.pos(d), P.Z.neg(d), P.Z.pos(b0), P.Z.neg(b0), P.Z.pos(P.Z.add(a0, j)), P.Z.neg(P.Z.add(a0, j)), P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(P.Z.add(a0, j), d)), P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(P.Z.add(b0, P.Z.opp(j))), P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))], R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{6n}}, R.V{1n}}, R.V{17n}}, R.Add{R.Add{R.Add{R.V{4n}, R.V{12n}}, R.V{3n}}, R.V{21n}}}, R.Add{R.Add{R.V{14n}, R.V{7n}}, R.V{9n}}}, R.Add{R.Add{R.V{16n}, R.V{15n}}, R.V{11n}}}, R.Add{R.Add{R.V{18n}, R.V{13n}}, R.V{8n}}}, R.Add{R.Add{R.V{20n}, R.V{19n}}, R.V{10n}}}, R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{6n}}, R.V{7n}}, R.V{12n}}, R.V{13n}}, R.V{16n}}, R.V{17n}}, R.V{20n}}, R.V{21n}}, R.V{14n}}, R.V{15n}}, R.V{18n}}, R.V{19n}}, R.V{8n}}, R.V{9n}}, R.V{10n}}, R.V{11n}}, R.Add{R.V{4n}, R.V{1n}}}, {==})
  +r2 = R.eq([pS, nS, pL1, nL1, pL2, nL2, P.Z.pos(a0), P.Z.neg(a0), P.Z.pos(j), P.Z.neg(j), P.Z.pos(d), P.Z.neg(d), P.Z.pos(b0), P.Z.neg(b0), P.Z.pos(P.Z.add(a0, j)), P.Z.neg(P.Z.add(a0, j)), P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(P.Z.add(a0, j), d)), P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(P.Z.add(b0, P.Z.opp(j))), P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))], R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.V{16n}}, R.V{3n}}, R.V{7n}}, R.Add{R.Add{R.Add{R.V{2n}, R.V{20n}}, R.V{5n}}, R.V{13n}}}, R.Add{R.Add{R.V{6n}, R.V{8n}}, R.V{15n}}}, R.Add{R.Add{R.V{14n}, R.V{10n}}, R.V{17n}}}, R.Add{R.Add{R.V{12n}, R.V{9n}}, R.V{19n}}}, R.Add{R.Add{R.V{18n}, R.V{11n}}, R.V{21n}}}, R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{6n}}, R.V{7n}}, R.V{12n}}, R.V{13n}}, R.V{16n}}, R.V{17n}}, R.V{20n}}, R.V{21n}}, R.V{14n}}, R.V{15n}}, R.V{18n}}, R.V{19n}}, R.V{8n}}, R.V{9n}}, R.V{10n}}, R.V{11n}}, R.Add{R.V{0n}, R.V{5n}}}, {==})
  add_cancel(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, nL1), P.Z.pos(a0)), P.Z.neg(a0)), P.Z.pos(b0)), P.Z.neg(b0)), P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.pos(P.Z.add(a0, j))), P.Z.neg(P.Z.add(a0, j))), P.Z.pos(P.Z.add(b0, P.Z.opp(j)))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(j)), P.Z.neg(j)), P.Z.pos(d)), P.Z.neg(d)), Nat.add(pL2, nS), Nat.add(pS, nL2),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, nL1), P.Z.pos(a0)), P.Z.neg(a0)), P.Z.pos(b0)), P.Z.neg(b0)), P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.pos(P.Z.add(a0, j))), P.Z.neg(P.Z.add(a0, j))), P.Z.pos(P.Z.add(b0, P.Z.opp(j)))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(j)), P.Z.neg(j)), P.Z.pos(d)), P.Z.neg(d)), Nat.add(pL2, nS)), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.neg(a0)), P.Z.neg(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(a0, j))), P.Z.neg(d))), Nat.add(Nat.add(P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(b0)), P.Z.pos(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(d))), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, nL1), P.Z.pos(a0)), P.Z.neg(a0)), P.Z.pos(b0)), P.Z.neg(b0)), P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.pos(P.Z.add(a0, j))), P.Z.neg(P.Z.add(a0, j))), P.Z.pos(P.Z.add(b0, P.Z.opp(j)))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(j)), P.Z.neg(j)), P.Z.pos(d)), P.Z.neg(d)), Nat.add(pS, nL2)),
      Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.neg(a0)), P.Z.neg(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(a0, j))), P.Z.neg(d))), Nat.add(Nat.add(P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(b0)), P.Z.pos(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(d))), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, nL1), P.Z.pos(a0)), P.Z.neg(a0)), P.Z.pos(b0)), P.Z.neg(b0)), P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.pos(P.Z.add(a0, j))), P.Z.neg(P.Z.add(a0, j))), P.Z.pos(P.Z.add(b0, P.Z.opp(j)))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(j)), P.Z.neg(j)), P.Z.pos(d)), P.Z.neg(d)), Nat.add(pL2, nS)), r1),
      Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(a0)), nS), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), Nat.add(Nat.add(Nat.add(pL2, P.Z.pos(b0)), nL1), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.neg(a0)), P.Z.neg(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(a0, j), d)), P.Z.neg(P.Z.add(a0, j))), P.Z.neg(d))), Nat.add(Nat.add(P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(b0)), P.Z.pos(j))), Nat.add(Nat.add(P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(d))), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pS, P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), nL1), P.Z.neg(a0)), Nat.add(Nat.add(Nat.add(pL1, P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), nL2), P.Z.neg(b0))), Nat.add(Nat.add(P.Z.pos(a0), P.Z.pos(j)), P.Z.neg(P.Z.add(a0, j)))), Nat.add(Nat.add(P.Z.pos(P.Z.add(a0, j)), P.Z.pos(d)), P.Z.neg(P.Z.add(P.Z.add(a0, j), d)))), Nat.add(Nat.add(P.Z.pos(b0), P.Z.neg(j)), P.Z.neg(P.Z.add(b0, P.Z.opp(j))))), Nat.add(Nat.add(P.Z.pos(P.Z.add(b0, P.Z.opp(j))), P.Z.neg(d)), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d))))), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(pL1, nL1), P.Z.pos(a0)), P.Z.neg(a0)), P.Z.pos(b0)), P.Z.neg(b0)), P.Z.pos(P.Z.add(P.Z.add(a0, j), d))), P.Z.neg(P.Z.add(P.Z.add(a0, j), d))), P.Z.pos(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.neg(P.Z.add(P.Z.add(b0, P.Z.opp(j)), P.Z.opp(d)))), P.Z.pos(P.Z.add(a0, j))), P.Z.neg(P.Z.add(a0, j))), P.Z.pos(P.Z.add(b0, P.Z.opp(j)))), P.Z.neg(P.Z.add(b0, P.Z.opp(j)))), P.Z.pos(j)), P.Z.neg(j)), P.Z.pos(d)), P.Z.neg(d)), Nat.add(pS, nL2)), sum, r2)))


def rg_pz(+ax: Nat, +q: P.Body) -> Nat:
  P.Z.pos(G.V.at(ax, G.B.v(q)))

def rg_nz(+ax: Nat, +q: P.Body) -> Nat:
  P.Z.neg(G.V.at(ax, G.B.v(q)))

# writing x at i of xs changes the momentum by x less what was there
def rg_put_sum(+ax: Nat, xs: List<&2, P.Body>, i: Nat, +x: P.Body, h: {Nat.is_lt(i, List.length(&2, P.Body, xs)) == True{} : Bool})
  -> {Nat.add(Nat.add(Nat.add(G.Mo.p(ax, G.Bs.put(xs, i, x)), rg_pz(ax, G.Bs.at(xs, i))), G.Mo.n(ax, xs)), rg_nz(ax, x))
      == Nat.add(Nat.add(Nat.add(G.Mo.p(ax, xs), rg_pz(ax, x)), G.Mo.n(ax, G.Bs.put(xs, i, x))), rg_nz(ax, G.Bs.at(xs, i))) : Nat}:
  match xs i:
    case Nil{} 0n:
      Empty.absurd({Nat.add(Nat.add(Nat.add(0n, rg_pz(ax, G.Bs.at([], 0n))), 0n), rg_nz(ax, x))
        == Nat.add(Nat.add(Nat.add(0n, rg_pz(ax, x)), 0n), rg_nz(ax, G.Bs.at([], 0n))) : Nat}, clash2(h))
    case Nil{} 1n++j:
      Empty.absurd({Nat.add(Nat.add(Nat.add(0n, rg_pz(ax, G.Bs.at([], 1n+j))), 0n), rg_nz(ax, x))
        == Nat.add(Nat.add(Nat.add(0n, rg_pz(ax, x)), 0n), rg_nz(ax, G.Bs.at([], 1n+j))) : Nat}, clash2(h))
    case +y <> +rest 0n:
      R.eq([rg_pz(ax, x), rg_pz(ax, y), rg_nz(ax, x), rg_nz(ax, y), G.Mo.p(ax, rest), G.Mo.n(ax, rest)],
        R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.V{4n}}, R.V{1n}}, R.Add{R.V{3n}, R.V{5n}}}, R.V{2n}},
        R.Add{R.Add{R.Add{R.Add{R.V{1n}, R.V{4n}}, R.V{0n}}, R.Add{R.V{2n}, R.V{5n}}}, R.V{3n}}, {==})
    case +y <> +rest 1n++j:
      +py = rg_pz(ax, y)
      +ny = rg_nz(ax, y)
      +p1 = G.Mo.p(ax, G.Bs.put(rest, j, x))
      +q = rg_pz(ax, G.Bs.at(rest, j))
      +n0 = G.Mo.n(ax, rest)
      +xn = rg_nz(ax, x)
      +p0 = G.Mo.p(ax, rest)
      +px = rg_pz(ax, x)
      +n1 = G.Mo.n(ax, G.Bs.put(rest, j, x))
      +nq = rg_nz(ax, G.Bs.at(rest, j))
      +ihl = Nat.add(Nat.add(Nat.add(p1, q), n0), xn)
      +ihr = Nat.add(Nat.add(Nat.add(p0, px), n1), nq)
      Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(py, p1), q), Nat.add(ny, n0)), xn), Nat.add(Nat.add(py, ny), ihl),
        Nat.add(Nat.add(Nat.add(Nat.add(py, p0), px), Nat.add(ny, n1)), nq),
        R.eq([py, ny, p1, q, n0, xn, p0, px, n1, nq], R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.V{2n}}, R.V{3n}}, R.Add{R.V{1n}, R.V{4n}}}, R.V{5n}},
          R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.Add{R.V{2n}, R.V{3n}}, R.V{4n}}, R.V{5n}}}, {==}),
        Equal.trans(Nat, Nat.add(Nat.add(py, ny), ihl), Nat.add(Nat.add(py, ny), ihr),
          Nat.add(Nat.add(Nat.add(Nat.add(py, p0), px), Nat.add(ny, n1)), nq),
          Equal.cong(Nat, Nat, t => Nat.add(Nat.add(py, ny), t), ihl, ihr, rg_put_sum(ax, rest, j, x, h)),
          R.eq([py, ny, p1, q, n0, xn, p0, px, n1, nq], R.Add{R.Add{R.V{0n}, R.V{1n}}, R.Add{R.Add{R.Add{R.V{6n}, R.V{7n}}, R.V{8n}}, R.V{9n}}},
            R.Add{R.Add{R.Add{R.Add{R.V{0n}, R.V{6n}}, R.V{7n}}, R.Add{R.V{1n}, R.V{8n}}}, R.V{9n}}, {==})))

# writing at j leaves every other place as it was
def rg_at_put_ne(xs: List<&2, P.Body>, i: Nat, j: Nat, +x: P.Body, h: {Nat.is_eq(i, j) == False{} : Bool})
  -> {G.Bs.at(G.Bs.put(xs, j, x), i) == G.Bs.at(xs, i) : P.Body}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case +y <> +rest 0n 0n:
      Empty.absurd({G.Bs.at(G.Bs.put(y <> rest, 0n, x), 0n) == G.Bs.at(y <> rest, 0n) : P.Body}, clash(h))
    case +y <> +rest 0n 1n++q:
      {==}
    case +y <> +rest 1n++p 0n:
      {==}
    case +y <> +rest 1n++p 1n++q:
      rg_at_put_ne(rest, p, q, x, h)

def rg_len_put(xs: List<&2, P.Body>, i: Nat, +x: P.Body) -> {List.length(&2, P.Body, G.Bs.put(xs, i, x)) == List.length(&2, P.Body, xs) : Nat}:
  match xs i:
    case Nil{} _:
      {==}
    case +y <> +rest 0n:
      {==}
    case +y <> +rest 1n++j:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, P.Body, G.Bs.put(rest, j, x)), List.length(&2, P.Body, rest), rg_len_put(rest, j, x))

def rg_in_put(+xs: List<&2, P.Body>, +a: Nat, +b: Nat, +x: P.Body, hb: {Nat.is_lt(b, List.length(&2, P.Body, xs)) == True{} : Bool})
  -> {Nat.is_lt(b, List.length(&2, P.Body, G.Bs.put(xs, a, x))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, P.Body, G.Bs.put(xs, a, x)), List.length(&2, P.Body, xs), rg_len_put(xs, a, x))
    : {Nat.is_lt(b, _) == True{} : Bool}
  hb

# the second write, with what the first left at b being what was there
def rg_e2_of(+ax: Nat, +bs: List<&2, P.Body>, +a: Nat, +b: Nat, +xa: P.Body, +xb: P.Body,
  hab: {Nat.is_eq(b, a) == False{} : Bool}, hb: {Nat.is_lt(b, List.length(&2, P.Body, bs)) == True{} : Bool})
  -> {Nat.add(Nat.add(Nat.add(G.Mo.p(ax, G.Bs.put(G.Bs.put(bs, a, xa), b, xb)), rg_pz(ax, G.Bs.at(bs, b))), G.Mo.n(ax, G.Bs.put(bs, a, xa))), rg_nz(ax, xb))
      == Nat.add(Nat.add(Nat.add(G.Mo.p(ax, G.Bs.put(bs, a, xa)), rg_pz(ax, xb)), G.Mo.n(ax, G.Bs.put(G.Bs.put(bs, a, xa), b, xb))), rg_nz(ax, G.Bs.at(bs, b))) : Nat}:
  +l1 = G.Bs.put(bs, a, xa)
  +l2 = G.Bs.put(l1, b, xb)
  %rg_at_put_ne(bs, b, a, xa, hab)
    : {Nat.add(Nat.add(Nat.add(G.Mo.p(ax, l2), rg_pz(ax, _)), G.Mo.n(ax, l1)), rg_nz(ax, xb))
      == Nat.add(Nat.add(Nat.add(G.Mo.p(ax, l1), rg_pz(ax, xb)), G.Mo.n(ax, l2)), rg_nz(ax, _)) : Nat}
  rg_put_sum(ax, l1, b, xb, rg_in_put(bs, a, b, xa, hb))

# an impulse given equal and opposite: +j + dt at a, -j - dt at b (along
# each axis in turn, so that the velocity's part reduces)
def rg_give_ax(ax: Nat, +bs: List<&2, P.Body>, +a: Nat, +b: Nat, +ra: P.Wv, +rb: P.Wv, +j: P.Wv, +dt: P.Wv,
  hab: {Nat.is_eq(b, a) == False{} : Bool}, ha: {Nat.is_lt(a, List.length(&2, P.Body, bs)) == True{} : Bool},
  hb: {Nat.is_lt(b, List.length(&2, P.Body, bs)) == True{} : Bool})
  -> {Nat.add(G.Mo.p(ax, G.Bs.put(G.Bs.put(bs, a, G.B.push(G.B.push(G.Bs.at(bs, a), j, ra), dt, ra)), b, G.B.pull(G.B.pull(G.Bs.at(bs, b), j, rb), dt, rb))), G.Mo.n(ax, bs))
      == Nat.add(G.Mo.p(ax, bs), G.Mo.n(ax, G.Bs.put(G.Bs.put(bs, a, G.B.push(G.B.push(G.Bs.at(bs, a), j, ra), dt, ra)), b, G.B.pull(G.B.pull(G.Bs.at(bs, b), j, rb), dt, rb)))) : Nat}:
  match ax:
    case 0n:
      +xa = G.B.push(G.B.push(G.Bs.at(bs, a), j, ra), dt, ra)
      +xb = G.B.pull(G.B.pull(G.Bs.at(bs, b), j, rb), dt, rb)
      +l1 = G.Bs.put(bs, a, xa)
      +l2 = G.Bs.put(l1, b, xb)
      rg_mo_core(G.Mo.p(0n, bs), G.Mo.n(0n, bs), G.Mo.p(0n, l1), G.Mo.n(0n, l1), G.Mo.p(0n, l2), G.Mo.n(0n, l2),
        G.V.at(0n, G.B.v(G.Bs.at(bs, a))), G.V.at(0n, j), G.V.at(0n, dt), G.V.at(0n, G.B.v(G.Bs.at(bs, b))),
        rg_put_sum(0n, bs, a, xa, ha), rg_e2_of(0n, bs, a, b, xa, xb, hab, hb))
    case 1n+m:
      match m:
        case 0n:
          +xa = G.B.push(G.B.push(G.Bs.at(bs, a), j, ra), dt, ra)
          +xb = G.B.pull(G.B.pull(G.Bs.at(bs, b), j, rb), dt, rb)
          +l1 = G.Bs.put(bs, a, xa)
          +l2 = G.Bs.put(l1, b, xb)
          rg_mo_core(G.Mo.p(1n, bs), G.Mo.n(1n, bs), G.Mo.p(1n, l1), G.Mo.n(1n, l1), G.Mo.p(1n, l2), G.Mo.n(1n, l2),
            G.V.at(1n, G.B.v(G.Bs.at(bs, a))), G.V.at(1n, j), G.V.at(1n, dt), G.V.at(1n, G.B.v(G.Bs.at(bs, b))),
            rg_put_sum(1n, bs, a, xa, ha), rg_e2_of(1n, bs, a, b, xa, xb, hab, hb))
        case 1n++o:
          +xa = G.B.push(G.B.push(G.Bs.at(bs, a), j, ra), dt, ra)
          +xb = G.B.pull(G.B.pull(G.Bs.at(bs, b), j, rb), dt, rb)
          +l1 = G.Bs.put(bs, a, xa)
          +l2 = G.Bs.put(l1, b, xb)
          rg_mo_core(G.Mo.p(1n+1n+o, bs), G.Mo.n(1n+1n+o, bs), G.Mo.p(1n+1n+o, l1), G.Mo.n(1n+1n+o, l1), G.Mo.p(1n+1n+o, l2), G.Mo.n(1n+1n+o, l2),
            G.V.at(1n+1n+o, G.B.v(G.Bs.at(bs, a))), G.V.at(1n+1n+o, j), G.V.at(1n+1n+o, dt), G.V.at(1n+1n+o, G.B.v(G.Bs.at(bs, b))),
            rg_put_sum(1n+1n+o, bs, a, xa, ha), rg_e2_of(1n+1n+o, bs, a, b, xa, xb, hab, hb))

def Laws.rigid_action_reaction(k, c, done, bs, ax, two, ab, ina, inb):
  +ba = G.Bs.at(bs, G.Ct.a(c))
  +bb = G.Bs.at(bs, G.Ct.b(c))
  +raw = G.Imp.raw(k, c, ba, bb)
  +j = G.R2.j(raw)
  +dt = G.V.sub(G.Ct.jt(G.Ct.safe(k, G.R2.c(raw))), G.Ct.jt(c))
  +pl = G.B.pull(G.B.pull(bb, j, G.Ct.rb(c)), dt, G.Ct.rb(c))
  +pu = G.Bs.put(bs, G.Ct.a(c), G.B.push(G.B.push(ba, j, G.Ct.ra(c)), dt, G.Ct.ra(c)))
  %Equal.sym(Bool, G.Ct.fl(c), False{}, two)
    : {Nat.add(G.Mo.p(ax, G.Imp.side(_, G.Ct.b(c), pl, pu)), G.Mo.n(ax, bs))
      == Nat.add(G.Mo.p(ax, bs), G.Mo.n(ax, G.Imp.side(_, G.Ct.b(c), pl, pu))) : Nat}
  rg_give_ax(ax, bs, G.Ct.a(c), G.Ct.b(c), G.Ct.ra(c), G.Ct.rb(c), j, dt, ab, ina, inb)
