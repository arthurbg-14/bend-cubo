# Cubo -- the physics: bodies, gravity, friction, pushes, collisions.
#
# Everything is an integer. A tick is 1/128 s. Positions are in units of
# 2^-18 m (a cube is 2^18 units wide); velocities in units of 1/1024 m/s,
# which, with the tick, makes a velocity v move a body by v units in half
# a tick: a tick moves it by v + v', the start and end velocities added
# (their average over the whole tick). With that rule, constant
# acceleration is integrated exactly -- so, under gravity g (velocity lost
# per tick), v^2 + g y does not change at all from tick to tick: that is
# the body's mechanical energy (kinetic plus potential), in these units,
# and the laws (LAWS.bend) hold it exact.
#
# Every body is a unit cube. The player is a body (the blue cube) and so
# is every green cube; a tick moves one body among the others (its
# obstacles): the ground's friction or the air, the player's motor and
# jump, gravity, and then the moves, x, z and y, each through a gate: a
# move is taken only where the box is free. A body that runs into another
# shares its velocity along that axis with it, momentum kept (the push).

import Base

def Pick.n(c: Bool, +a: Nat, +b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

# the smaller and the larger of two, chosen and not counted: Nat.min and
# Nat.max walk down in ones, and these are world numbers.
def Pick.low(+a: Nat, +b: Nat) -> Nat:
  Pick.n(Nat.is_le(a, b), a, b)

def Pick.high(+a: Nat, +b: Nat) -> Nat:
  Pick.n(Nat.is_le(a, b), b, a)

# Numbers
# -------

# a signed number: +n or -n (Neg{0n} is 0 too)
type Z is Data:
  Pos{n: Nat}
  Neg{n: Nat}

def Z.mag(v: Z) -> Nat:
  match v:
    case Pos{n}:
      n
    case Neg{n}:
      n

def Z.sq(v: Z) -> Nat:
  match v:
    case Pos{+n}:
      Nat.mul(n, n)
    case Neg{+n}:
      Nat.mul(n, n)

# the positive and the negative part: v = pos - neg
def Z.pos(v: Z) -> Nat:
  match v:
    case Pos{n}:
      n
    case Neg{n}:
      0n

def Z.neg(v: Z) -> Nat:
  match v:
    case Pos{n}:
      0n
    case Neg{n}:
      n

# x - y, told whether x < y
def Z.diff(lt: Bool, +x: Nat, +y: Nat) -> Z:
  match lt:
    case True{}:
      Neg{Nat.sub(y, x)}
    case False{}:
      Pos{Nat.sub(x, y)}

def Z.add(a: Z, b: Z) -> Z:
  match a b:
    case Pos{x} Pos{y}:
      Pos{Nat.add(x, y)}
    case Neg{x} Neg{y}:
      Neg{Nat.add(x, y)}
    case Pos{+x} Neg{+y}:
      Z.diff(Nat.is_lt(x, y), x, y)
    case Neg{+x} Pos{+y}:
      Z.diff(Nat.is_lt(y, x), y, x)

# x moved by d (the world starts far from 0: it never goes below)
def Z.shift(+x: Nat, d: Z) -> Nat:
  match d:
    case Pos{p}:
      Nat.add(x, p)
    case Neg{q}:
      Nat.sub(x, q)

# does x moved by d stay at or above 0? (0 is the world's far wall)
def Z.fits(+x: Nat, d: Z) -> Bool:
  match d:
    case Pos{p}:
      True{}
    case Neg{q}:
      Nat.is_le(q, x)

# v with its size cut by f
def Z.cut(+f: Nat, v: Z) -> Z:
  match v:
    case Pos{n}:
      Pos{Nat.sub(n, f)}
    case Neg{n}:
      Neg{Nat.sub(n, f)}

# a v / 4096, with v's sign (a direction of size 4096 scaled by a)
def Z.q12(+a: Nat, v: Z) -> Z:
  match v:
    case Pos{n}:
      Pos{Nat.div(Nat.mul(a, n), 4096n)}
    case Neg{n}:
      Neg{Nat.div(Nat.mul(a, n), 4096n)}

# u v / 4096
def Z.mulq(u: Z, v: Z) -> Z:
  match u v:
    case Pos{a} Pos{b}:
      Pos{Nat.div(Nat.mul(a, b), 4096n)}
    case Neg{a} Neg{b}:
      Pos{Nat.div(Nat.mul(a, b), 4096n)}
    case Pos{a} Neg{b}:
      Neg{Nat.div(Nat.mul(a, b), 4096n)}
    case Neg{a} Pos{b}:
      Neg{Nat.div(Nat.mul(a, b), 4096n)}

# v < m
def Z.below(v: Z, +m: Nat) -> Bool:
  match v:
    case Pos{n}:
      Nat.is_lt(n, m)
    case Neg{n}:
      True{}

# a > b
def Z.above(a: Z, b: Z) -> Bool:
  match a b:
    case Pos{x} Pos{y}:
      Nat.is_lt(y, x)
    case Neg{x} Neg{y}:
      Nat.is_lt(x, y)
    case Pos{x} Neg{y}:
      Bool.or(Nat.is_lt(0n, x), Nat.is_lt(0n, y))
    case Neg{x} Pos{y}:
      False{}

# The constants
# -------------
# All of them can be changed while playing (main.bend), so every law holds
# for any value of each. g: gravity, the velocity it takes each tick; mu:
# the ground's friction coefficient, in 256ths; jump: the takeoff speed;
# acc: the motor's push each tick, on the ground (in the air the motor does
# nothing: a body in flight only falls).

type K is Data:
  K{g: Nat, mu: Nat, jump: Nat, acc: Nat, size: Nat}

def K.g(k: K) -> Nat:
  K{g, mu, jump, acc, size} = k
  g

def K.size(k: K) -> Nat:
  K{g, mu, jump, acc, size} = k
  size

def K.jump(k: K) -> Nat:
  K{g, mu, jump, acc, size} = k
  jump

def K.acc(k: K) -> Nat:
  K{g, mu, jump, acc, size} = k
  acc

# Coulomb's friction: the ground takes mu N from the speed, N = m g
def K.fric(k: K) -> Nat:
  K{+g, +mu, jump, acc, size} = k
  Nat.div(Nat.mul(mu, g), 256n)

# Square roots
# ------------
# Newton's, on whole numbers: from any x0 at or above the root it comes
# down to it. Friction uses it for the speed, the turning for the size of
# the turning.

def Fric.next(+n: Nat, +x: Nat) -> Nat:
  Nat.div(Nat.add(x, Nat.div(n, x)), 2n)

def Fric.newton(fuel: Nat, +n: Nat, +x: Nat, more: Bool) -> Nat:
  match fuel more:
    case 0n _:
      x
    case 1n+f True{}:
      Fric.newton(f, n, Fric.next(n, x), Nat.is_lt(Fric.next(n, Fric.next(n, x)), Fric.next(n, x)))
    case 1n+f False{}:
      x

# the square root of n rounded down, from x0 >= it
def Fric.floor(+n: Nat, +x0: Nat) -> Nat:
  Fric.newton(64n, n, x0, Nat.is_lt(Fric.next(n, x0), x0))

def Fric.ceil(+n: Nat, +r: Nat) -> Nat:
  Pick.n(Nat.is_lt(Nat.mul(r, r), n), Nat.add(r, 1n), r)


# Turning: the sine and the cosine
# --------------------------------
# An angle is a whole word: the whole of it is a whole turn, so an angle
# never rounds and never runs off the end. Its sine and cosine come out in
# 2^-16, each from its own series, worked out in 2^-20 with every division
# rounded. They are dead on at the quarter turns -- a cube that has not
# turned is exactly square, and the old boxes are untouched -- and 2^-16
# out of true at worst in between (a hundredth of a millimetre on a cube of
# a metre). The GPU is handed these same two numbers, so the shape that is
# drawn is the shape that collides, to the unit.

def Trig.dv(+a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.add(a, Nat.div(b, 2n)), b)

# an angle inside a quarter turn, in radians in 2^-20 (2 pi is 6588397 of
# those; the angle is cut by 2^8 first, to keep the product small)
def Trig.th(+u: U32) -> Nat:
  Trig.dv(Nat.mul(U32.to_nat((u >> 8n : U32)), 6588397n), 16777216n)

# what is left of the pluses after the minuses, in 2^-16: the two sides
# nearly cancel at the quarter turn, so the floor at zero matters -- both
# the sine and the cosine of a quarter of a turn are zero or above
def Trig.cut(+p: Nat, +q: Nat) -> Nat:
  Trig.dv(Nat.mul(Nat.sub(Pick.high(p, q), q), 65536n), 1048576n)

# t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880, the pluses gathered apart
# from the minuses
def Trig.sq(+u: U32) -> Nat:
  +t = Trig.th(u)
  +t2 = Trig.dv(Nat.mul(t, t), 1048576n)
  +t3 = Trig.dv(Nat.mul(t2, t), 1048576n)
  +t5 = Trig.dv(Nat.mul(t3, t2), 1048576n)
  +t7 = Trig.dv(Nat.mul(t5, t2), 1048576n)
  +t9 = Trig.dv(Nat.mul(t7, t2), 1048576n)
  Trig.cut(Nat.add(Nat.add(t, Trig.dv(t5, 120n)), Trig.dv(t9, 362880n)),
    Nat.add(Trig.dv(t3, 6n), Trig.dv(t7, 5040n)))

# 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800
def Trig.cq(+u: U32) -> Nat:
  +t = Trig.th(u)
  +t2 = Trig.dv(Nat.mul(t, t), 1048576n)
  +t4 = Trig.dv(Nat.mul(t2, t2), 1048576n)
  +t6 = Trig.dv(Nat.mul(t4, t2), 1048576n)
  +t8 = Trig.dv(Nat.mul(t6, t2), 1048576n)
  +t10 = Trig.dv(Nat.mul(t8, t2), 1048576n)
  Trig.cut(Nat.add(Nat.add(1048576n, Trig.dv(t4, 24n)), Trig.dv(t8, 40320n)),
    Nat.add(Nat.add(Trig.dv(t2, 2n), Trig.dv(t6, 720n)), Trig.dv(t10, 3628800n)))

# which quarter the angle is in tells which of the two to take, and its sign
def Trig.pick(q: Nat, +s: Nat, +c: Nat) -> Z:
  match q:
    case 0n:
      Pos{s}
    case 1n:
      Pos{c}
    case 2n:
      Neg{s}
    case _:
      Neg{c}

def Trig.sin(+a: U32) -> Z:
  Trig.pick(U32.to_nat((a >> 30n : U32)), Trig.sq((a .&. 1073741823 : U32)), Trig.cq((a .&. 1073741823 : U32)))

# the cosine is the sine a quarter turn on
def Trig.cos(+a: U32) -> Z:
  Trig.sin((a + 1073741824 : U32))

# Rotation
# --------
# A cube resists turning the same about every axis: its inertia is
# I = m s^2 / 6 times the identity. Two things follow, and the whole model
# here rests on them.
#
# One: a cube in flight does not wobble. The term that makes a brick
# tumble oddly, w x I w, is zero when I is a multiple of the identity, so
# the angular velocity of a cube in flight never changes and the angle it
# has turned grows by exactly the same amount every tick. That is exact in
# integers, the way the parabola of a fall already is.
#
# Two: a hit out of the middle turns the body by the arm crossed with the
# impulse, over that same I -- no tensor to carry around.
#
# What is kept is the turning as a vector -- exact: a hit adds to it, and
# nothing else ever touches it -- and the orientation as a quaternion in
# 2^-15. The turning counts shares of a whole turn a tick, a whole turn
# being a whole word. The quaternion is the one thing here that is not
# exact: a tick of turning multiplies it by the turn of that tick and
# brings its size back to 2^15, which is right to 2^-15 of itself; the
# turning it carries, and every law about it, stay exact.

type Wv is Data:
  Wv{x: Z, y: Z, z: Z}

type Quat is Data:
  Quat{a: Z, b: Z, c: Z, d: Z}

type Rot is Data:
  Rot{q: Quat, w: Wv}

def Quat.one() -> Quat:
  Quat{Pos{32768n}, Pos{0n}, Pos{0n}, Pos{0n}}

def Wv.zero() -> Wv:
  Wv{Pos{0n}, Pos{0n}, Pos{0n}}

def Rot.rest() -> Rot:
  Rot{Quat.one(), Wv.zero()}

def Pick.q(c: Bool, a: Quat, b: Quat) -> Quat:
  match c:
    case True{}:
      a
    case False{}:
      b

def Rot.q(r: Rot) -> Quat:
  Rot{q, w} = r
  q

def Rot.w(r: Rot) -> Wv:
  Rot{q, w} = r
  w

def Wv.x(v: Wv) -> Z:
  Wv{x, y, z} = v
  x

def Wv.y(v: Wv) -> Z:
  Wv{x, y, z} = v
  y

def Wv.z(v: Wv) -> Z:
  Wv{x, y, z} = v
  z

def Quat.a(q: Quat) -> Z:
  Quat{a, b, c, d} = q
  a

def Quat.b(q: Quat) -> Z:
  Quat{a, b, c, d} = q
  b

def Quat.c(q: Quat) -> Z:
  Quat{a, b, c, d} = q
  c

def Quat.d(q: Quat) -> Z:
  Quat{a, b, c, d} = q
  d

# Four zeros are no quaternion at all. An array of bodies starts zeroed,
# and a cube that has never turned has never had its four written, so
# that is what comes back from it -- and four zeros would swallow every
# turn that came after, because a product with them is them. Read as the
# turn of nothing, which is the one that changes nothing.
def Quat.ok(+q: Quat) -> Quat:
  Pick.q(Nat.is_eq(Nat.add(Nat.add(Z.mag(Quat.a(q)), Z.mag(Quat.b(q))),
    Nat.add(Z.mag(Quat.c(q)), Z.mag(Quat.d(q)))), 0n), Quat.one(), q)

def Rot.ok(+r: Rot) -> Rot:
  Rot{Quat.ok(Rot.q(r)), Rot.w(r)}

# are two numbers the same number? (Neg{0} is 0 too)
def Z.same(+a: Z, +b: Z) -> Bool:
  Nat.is_eq(Nat.add(Z.pos(a), Z.neg(b)), Nat.add(Z.pos(b), Z.neg(a)))

# are two orientations the same one, part by part?
def Quat.same(+p: Quat, +q: Quat) -> Bool:
  Bool.and(Bool.and(Z.same(Quat.a(p), Quat.a(q)), Z.same(Quat.b(p), Quat.b(q))),
    Bool.and(Z.same(Quat.c(p), Quat.c(q)), Z.same(Quat.d(p), Quat.d(q))))

# nothing turning, nothing turned: a cube like this is square to the world
# and every box around it is the old one, to the unit
def Wv.null(v: Wv) -> Bool:
  Wv{+x, +y, +z} = v
  Bool.and(Nat.is_eq(Z.mag(x), 0n), Bool.and(Nat.is_eq(Z.mag(y), 0n), Nat.is_eq(Z.mag(z), 0n)))

def Quat.flat(q: Quat) -> Bool:
  Quat{a, +b, +c, +d} = q
  Bool.and(Nat.is_eq(Z.mag(b), 0n), Bool.and(Nat.is_eq(Z.mag(c), 0n), Nat.is_eq(Z.mag(d), 0n)))

def Rot.still(r: Rot) -> Bool:
  Rot{+q, +w} = r
  Bool.and(Quat.flat(q), Wv.null(w))


def Z.divn(v: Z, +d: Nat) -> Z:
  match v:
    case Pos{+n}:
      Pos{Nat.div(n, d)}
    case Neg{+n}:
      Neg{Nat.div(n, d)}

def Z.shr16(v: Z) -> Z:
  match v:
    case Pos{+n}:
      Pos{Nat.div(n, 65536n)}
    case Neg{+n}:
      Neg{Nat.div(n, 65536n)}


def Z.opp(v: Z) -> Z:
  match v:
    case Pos{n}:
      Neg{n}
    case Neg{n}:
      Pos{n}

def Z.sub(a: Z, b: Z) -> Z:
  Z.add(a, Z.opp(b))

# u v, the sign kept
def Z.mul(u: Z, v: Z) -> Z:
  match u v:
    case Pos{+a} Pos{+b}:
      Pos{Nat.mul(a, b)}
    case Neg{+a} Neg{+b}:
      Pos{Nat.mul(a, b)}
    case Pos{+a} Neg{+b}:
      Neg{Nat.mul(a, b)}
    case Neg{+a} Pos{+b}:
      Neg{Nat.mul(a, b)}

# n with the sign of v
def Z.like(v: Z, +n: Nat) -> Z:
  match v:
    case Pos{p}:
      Pos{n}
    case Neg{p}:
      Neg{n}

# how fast the body turns, in the same shares of a turn a tick: the parts
# are cut by 2^8 before squaring, so the sum stays well inside a word
def Wv.mag(v: Wv) -> Nat:
  Wv{+x, +y, +z} = v
  +a = Nat.div(Z.mag(x), 256n)
  +b = Nat.div(Z.mag(y), 256n)
  +c = Nat.div(Z.mag(z), 256n)
  +n = Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(b, b)), Nat.mul(c, c))
  Nat.mul(256n, Fric.floor(n, Pick.high(Nat.add(Nat.add(a, b), c), 1n)))

# one part of the turn of a tick: sin(half the angle) along the axis the
# body turns on, in 2^-16
def Quat.part(+s: Z, +v: Z, +m: Nat) -> Z:
  Z.like(v, Nat.div(Nat.mul(Z.mag(s), Z.mag(v)), Pick.high(m, 1n)))

# the turn of one tick as a quaternion in 2^-16: half the angle, about the
# axis of the turning itself
# A body that is not turning steps by nothing at all. Asking that first
# is not only quicker: it is what lets a proof about a tick get past
# this step, because a turn of a rate the checker cannot work out stops
# right here instead of running into the series in U32.
def Quat.step2(+h: U32, +w: Wv, +m: Nat) -> Quat:
  Quat{Trig.cos(h), Quat.part(Trig.sin(h), Wv.x(w), m), Quat.part(Trig.sin(h), Wv.y(w), m),
    Quat.part(Trig.sin(h), Wv.z(w), m)}

def Quat.step1(still: Bool, +w: Wv, +m: Nat) -> Quat:
  match still:
    case True{}:
      Quat.one()
    case False{}:
      Quat.step2(U32.from_nat(Nat.div(m, 2n)), w, m)

def Quat.step(+w: Wv, +m: Nat) -> Quat:
  Quat.step1(Wv.null(w), w, m)

# one quaternion after the other, the first in 2^-15 and the second in
# 2^-16, out in 2^-15
def Quat.mul(+p: Quat, +r: Quat) -> Quat:
  Quat{Z.shr16(Z.sub(Z.mul(Quat.a(p), Quat.a(r)), Z.add(Z.add(Z.mul(Quat.b(p), Quat.b(r)),
         Z.mul(Quat.c(p), Quat.c(r))), Z.mul(Quat.d(p), Quat.d(r))))),
    Z.shr16(Z.sub(Z.add(Z.add(Z.mul(Quat.a(p), Quat.b(r)), Z.mul(Quat.b(p), Quat.a(r))),
         Z.mul(Quat.c(p), Quat.d(r))), Z.mul(Quat.d(p), Quat.c(r)))),
    Z.shr16(Z.sub(Z.add(Z.add(Z.mul(Quat.a(p), Quat.c(r)), Z.mul(Quat.c(p), Quat.a(r))),
         Z.mul(Quat.d(p), Quat.b(r))), Z.mul(Quat.b(p), Quat.d(r)))),
    Z.shr16(Z.sub(Z.add(Z.add(Z.mul(Quat.a(p), Quat.d(r)), Z.mul(Quat.d(p), Quat.a(r))),
         Z.mul(Quat.b(p), Quat.c(r))), Z.mul(Quat.c(p), Quat.b(r))))}
# the same turn written in 2^-15 instead of 2^-16
def Quat.half(+q: Quat) -> Quat:
  Quat{Z.divn(Quat.a(q), 2n), Z.divn(Quat.b(q), 2n), Z.divn(Quat.c(q), 2n), Z.divn(Quat.d(q), 2n)}

# the size of a quaternion in 2^-15
def Quat.mag(+q: Quat) -> Nat:
  +n = Nat.add(Nat.add(Nat.mul(Z.mag(Quat.a(q)), Z.mag(Quat.a(q))), Nat.mul(Z.mag(Quat.b(q)), Z.mag(Quat.b(q)))),
    Nat.add(Nat.mul(Z.mag(Quat.c(q)), Z.mag(Quat.c(q))), Nat.mul(Z.mag(Quat.d(q)), Z.mag(Quat.d(q)))))
  Fric.floor(n, Pick.high(Nat.add(Nat.add(Z.mag(Quat.a(q)), Z.mag(Quat.b(q))),
    Nat.add(Z.mag(Quat.c(q)), Z.mag(Quat.d(q)))), 1n))

def Quat.scale(+v: Z, +m: Nat) -> Z:
  Z.like(v, Nat.div(Nat.mul(Z.mag(v), 32768n), Pick.high(m, 1n)))

# its size brought back to 2^15, so the turning never grows or shrinks the
# cube: this is where the 2^-15 of slack comes from
def Quat.unit(+q: Quat) -> Quat:
  Quat{Quat.scale(Quat.a(q), Quat.mag(q)), Quat.scale(Quat.b(q), Quat.mag(q)),
    Quat.scale(Quat.c(q), Quat.mag(q)), Quat.scale(Quat.d(q), Quat.mag(q))}

# the rotation with one of its seven numbers put in: how a walk that
# reads an array one word at a time builds it back up
def Rot.put(k: Nat, +r: Rot, +v: Z) -> Rot:
  match k:
    case 0n:
      Rot{Quat{v, Quat.b(Rot.q(r)), Quat.c(Rot.q(r)), Quat.d(Rot.q(r))}, Rot.w(r)}
    case 1n:
      Rot{Quat{Quat.a(Rot.q(r)), v, Quat.c(Rot.q(r)), Quat.d(Rot.q(r))}, Rot.w(r)}
    case 2n:
      Rot{Quat{Quat.a(Rot.q(r)), Quat.b(Rot.q(r)), v, Quat.d(Rot.q(r))}, Rot.w(r)}
    case 3n:
      Rot{Quat{Quat.a(Rot.q(r)), Quat.b(Rot.q(r)), Quat.c(Rot.q(r)), v}, Rot.w(r)}
    case 4n:
      Rot{Rot.q(r), Wv{v, Wv.y(Rot.w(r)), Wv.z(Rot.w(r))}}
    case 5n:
      Rot{Rot.q(r), Wv{Wv.x(Rot.w(r)), v, Wv.z(Rot.w(r))}}
    case _:
      Rot{Rot.q(r), Wv{Wv.x(Rot.w(r)), Wv.y(Rot.w(r)), v}}

# a tick of a body that touches nothing: the same turning, and the
# orientation carried on by exactly that turning
def Rot.turn(+q: Quat, +w: Wv) -> Quat:
  Quat.unit(Quat.mul(q, Quat.step(w, Wv.mag(w))))

def Rot.free(r: Rot) -> Rot:
  Rot{+q, +w} = r
  Rot{Rot.turn(q, w), w}
# v / 8: what is left, in the units kept here, of dividing by a cube's
# resistance to turning. The arm is in 2^-18 m and the impulse in 2^-10
# m/s; their product over I = m s^2 / 6, turned into a share of a whole
# turn a tick (a turn being a whole word), comes to a division by eight.
# Landing on a corner at 5 m/s comes off turning two and a half times a
# second, which is what a cube of a metre really does.
def Z.shr3(v: Z) -> Z:
  match v:
    case Pos{+n}:
      Pos{Nat.div(n, 8n)}
    case Neg{+n}:
      Neg{Nat.div(n, 8n)}

# the arm crossed with the impulse, one part for each axis. Nothing comes
# of an arm of zero (hit dead centre), and nothing about an axis from a
# push along it.
def Rot.crx(+ry: Z, +rz: Z, +jy: Z, +jz: Z) -> Z:
  Z.sub(Z.mul(ry, jz), Z.mul(rz, jy))

def Rot.cry(+rz: Z, +rx: Z, +jz: Z, +jx: Z) -> Z:
  Z.sub(Z.mul(rz, jx), Z.mul(rx, jz))

def Rot.crz(+rx: Z, +ry: Z, +jx: Z, +jy: Z) -> Z:
  Z.sub(Z.mul(rx, jy), Z.mul(ry, jx))

# the body after a hit of impulse j at the point the arm r points to: the
# whole of the arm crossed with the impulse goes into the turning, not
# just the part that lies along some axis
def Wv.add(+v: Wv, +u: Wv) -> Wv:
  Wv{Z.add(Wv.x(v), Wv.x(u)), Z.add(Wv.y(v), Wv.y(u)), Z.add(Wv.z(v), Wv.z(u))}

def Rot.kick(+rx: Z, +ry: Z, +rz: Z, +jx: Z, +jy: Z, +jz: Z) -> Wv:
  Wv{Z.shr3(Rot.crx(ry, rz, jy, jz)), Z.shr3(Rot.cry(rz, rx, jz, jx)), Z.shr3(Rot.crz(rx, ry, jx, jy))}

def Rot.hit(r: Rot, +rx: Z, +ry: Z, +rz: Z, +jx: Z, +jy: Z, +jz: Z) -> Rot:
  Rot{+q, +w} = r
  Rot{q, Wv.add(w, Rot.kick(rx, ry, rz, jx, jy, jz))}

# Bodies
# ------
# A body: where its lowest corner is, its velocity, whether it stands on
# something (ground), whether its last tick touched anything (hit).

type Body is Data:
  Body{x: Nat, y: Nat, z: Nat, vx: Z, vy: Z, vz: Z, ground: Bool, hit: Bool, rot: Rot}

def Body.rot(b: Body) -> Rot:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  rt

def Body.hit(b: Body) -> Bool:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  hit

def Body.ground(b: Body) -> Bool:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  ground

def Body.x(b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  x

def Body.y(b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  y

def Body.z(b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  z

def Body.vx(b: Body) -> Z:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  vx

def Body.vy(b: Body) -> Z:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  vy

def Body.vz(b: Body) -> Z:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  vz

# Boxes
# -----
# A body's box is [x, x + S) by [y, y + S) by [z, z + S).

# is c between where the body was and where its own step would take it?
# A stop is worked out from the boxes, and with a turned cube in the way a
# box can point somewhere the body could never reach in one tick -- that
# is no stop at all, and the body stays where it is.
def Geo.step(+a: Nat, +t: Nat, +c: Nat) -> Bool:
  Bool.and(Nat.is_le(Pick.low(a, t), c), Nat.is_le(c, Pick.high(a, t)))

# do [a, a + S) and [b, b + S) overlap?
def Geo.ovl(+s: Nat, +a: Nat, +b: Nat) -> Bool:
  Bool.and(Nat.is_lt(a, Nat.add(b, s)), Nat.is_lt(b, Nat.add(a, s)))

# Turned boxes
# ------------
# A cube that has turned is not a box along the world's axes any more, so
# telling two of them apart takes a direction that separates them: if the
# shadows both cast on some direction do not overlap, they are apart. For
# two boxes fifteen directions are enough -- the three faces of each and
# the nine crossings of their edges -- and if none of the fifteen has them
# apart, they touch. It is all whole numbers: the orientation comes in as
# a matrix in 2^-12 and both sides of every test are multiplied out, so
# nothing is ever divided away.
#
# A cube that has not turned gives back the plain box test, to the unit:
# its matrix is exactly 4096, 0, 0 / 0, 4096, 0 / 0, 0, 4096.

type Mat is Data:
  Mat{xx: Z, xy: Z, xz: Z, yx: Z, yy: Z, yz: Z, zx: Z, zy: Z, zz: Z}

# 1 - 2(p + q), in 2^-16, out of squares in 2^-30. Sixteen bits and not
# twelve because the whole test hangs on these: at 2^-12 a cube's shadow
# came out a tenth of a millimetre short, which is the size of the gaps
# the fifteen axes have to judge.
# Every number here is cut down in two steps of 2^7 instead of one of
# 2^14, and the diagonal is written as a difference of squares instead of
# a count down from 2^30. Same numbers: what changes is that a proof can
# look at them. The checker counts a Nat out one by one, so a literal of
# 2^30 sitting against a value it cannot work out is the end of its
# stack, and every law that mentions a turned cube runs into it.
def Mat.rnd(v: Z) -> Z:
  match v:
    case Pos{+n}:
      Pos{Nat.div(Nat.div(Nat.add(n, 8192n), 128n), 128n)}
    case Neg{+n}:
      Neg{Nat.div(Nat.div(Nat.add(n, 8192n), 128n), 128n)}

# 1 - 2(p + q), with the whole being a^2 + b^2 + c^2 + d^2: the two the
# row keeps, less the two it does not
def Mat.diag(+p: Nat, +q: Nat, +r: Nat, +t: Nat) -> Z:
  Mat.rnd(Z.diff(Nat.is_lt(Nat.add(r, t), Nat.add(p, q)), Nat.add(r, t), Nat.add(p, q)))

# 2(u v - p q), the same way
def Mat.off(+u: Z, +v: Z, +p: Z, +q: Z) -> Z:
  Mat.rnd(Z.mul(Pos{2n}, Z.sub(Z.mul(u, v), Z.mul(p, q))))

# the cube's own three axes, as they lie in the world, one to a row
def Rot.mat(+q: Quat) -> Mat:
  Mat{Mat.diag(Z.sq(Quat.c(q)), Z.sq(Quat.d(q)), Z.sq(Quat.a(q)), Z.sq(Quat.b(q))),
    Mat.off(Quat.b(q), Quat.c(q), Z.opp(Quat.a(q)), Quat.d(q)),
    Mat.off(Quat.b(q), Quat.d(q), Quat.a(q), Quat.c(q)),
    Mat.off(Quat.b(q), Quat.c(q), Quat.a(q), Quat.d(q)),
    Mat.diag(Z.sq(Quat.b(q)), Z.sq(Quat.d(q)), Z.sq(Quat.a(q)), Z.sq(Quat.c(q))),
    Mat.off(Quat.c(q), Quat.d(q), Z.opp(Quat.a(q)), Quat.b(q)),
    Mat.off(Quat.b(q), Quat.d(q), Z.opp(Quat.a(q)), Quat.c(q)),
    Mat.off(Quat.c(q), Quat.d(q), Quat.a(q), Quat.b(q)),
    Mat.diag(Z.sq(Quat.b(q)), Z.sq(Quat.c(q)), Z.sq(Quat.a(q)), Z.sq(Quat.d(q)))}

def V3.dot(+ax: Z, +ay: Z, +az: Z, +bx: Z, +by: Z, +bz: Z) -> Z:
  Z.add(Z.add(Z.mul(ax, bx), Z.mul(ay, by)), Z.mul(az, bz))

# apart along one of the first cube's own axes?
def Sat.a(+t: Z, +ha: Nat, +hb: Nat, +r0: Z, +r1: Z, +r2: Z) -> Bool:
  Nat.is_le(Nat.add(Nat.mul(ha, 65536n), Nat.mul(hb, Nat.add(Nat.add(Z.mag(r0), Z.mag(r1)), Z.mag(r2)))),
    Nat.mul(Z.mag(t), 65536n))

# apart along one of the second cube's?
def Sat.b(+t0: Z, +t1: Z, +t2: Z, +r0: Z, +r1: Z, +r2: Z, +ha: Nat, +hb: Nat) -> Bool:
  Nat.is_le(Nat.add(Nat.mul(hb, 65536n), Nat.mul(ha, Nat.add(Nat.add(Z.mag(r0), Z.mag(r1)), Z.mag(r2)))),
    Z.mag(V3.dot(t0, t1, t2, r0, r1, r2)))

# apart along the crossing of an edge of each. When the two edges are
# parallel the crossing is nothing at all -- a direction of nothing would
# say "apart" about every pair of cubes -- so that crossing is skipped:
# what it would have decided, the faces already decide. The crossing of
# A's edge i with B's edge j is nothing exactly when they point the same
# way, which is when their dot product R is a whole 4096.
def Sat.deg(+r: Z) -> Bool:
  Nat.is_lt(Nat.sub(4294967295n, Pick.low(Z.sq(r), 4294967295n)), 4194304n)

def Sat.x2(deg: Bool, +t1: Z, +t2: Z, +a1: Z, +a2: Z, +b1: Z, +b2: Z, +ha: Nat, +hb: Nat) -> Bool:
  match deg:
    case True{}:
      False{}
    case False{}:
      Nat.is_le(Nat.add(Nat.mul(ha, Nat.add(Z.mag(a1), Z.mag(a2))), Nat.mul(hb, Nat.add(Z.mag(b1), Z.mag(b2)))),
        Z.mag(Z.sub(Z.mul(t2, a1), Z.mul(t1, a2))))

def Sat.x(+rij: Z, +t1: Z, +t2: Z, +a1: Z, +a2: Z, +b1: Z, +b2: Z, +ha: Nat, +hb: Nat) -> Bool:
  Sat.x2(Sat.deg(rij), t1, t2, a1, a2, b1, b2, ha, hb)

def Sat.some(+p: Bool, +q: Bool, +r: Bool) -> Bool:
  Bool.or(p, Bool.or(q, r))

# the fifteen tests, with the two cubes' axes already worked out. The
# shadows are compared multiplied out, and apart counts from the moment
# they merely touch -- so two cubes side by side, edge against edge, are
# as free as they have always been.
def Geo.sat2(+ha: Nat, +hb: Nat, +tx: Z, +ty: Z, +tz: Z, ma: Mat, mb: Mat) -> Bool:
  Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = ma
  Mat{+bxx, +bxy, +bxz, +byx, +byy, +byz, +bzx, +bzy, +bzz} = mb
  +t0 = Z.divn(V3.dot(tx, ty, tz, axx, axy, axz), 65536n)
  +t1 = Z.divn(V3.dot(tx, ty, tz, ayx, ayy, ayz), 65536n)
  +t2 = Z.divn(V3.dot(tx, ty, tz, azx, azy, azz), 65536n)
  +r00 = Z.divn(V3.dot(axx, axy, axz, bxx, bxy, bxz), 65536n)
  +r01 = Z.divn(V3.dot(axx, axy, axz, byx, byy, byz), 65536n)
  +r02 = Z.divn(V3.dot(axx, axy, axz, bzx, bzy, bzz), 65536n)
  +r10 = Z.divn(V3.dot(ayx, ayy, ayz, bxx, bxy, bxz), 65536n)
  +r11 = Z.divn(V3.dot(ayx, ayy, ayz, byx, byy, byz), 65536n)
  +r12 = Z.divn(V3.dot(ayx, ayy, ayz, bzx, bzy, bzz), 65536n)
  +r20 = Z.divn(V3.dot(azx, azy, azz, bxx, bxy, bxz), 65536n)
  +r21 = Z.divn(V3.dot(azx, azy, azz, byx, byy, byz), 65536n)
  +r22 = Z.divn(V3.dot(azx, azy, azz, bzx, bzy, bzz), 65536n)
  Bool.not(Bool.or(Bool.or(
    Sat.some(Sat.a(t0, ha, hb, r00, r01, r02), Sat.a(t1, ha, hb, r10, r11, r12),
      Sat.a(t2, ha, hb, r20, r21, r22)),
    Sat.some(Sat.b(t0, t1, t2, r00, r10, r20, ha, hb), Sat.b(t0, t1, t2, r01, r11, r21, ha, hb),
      Sat.b(t0, t1, t2, r02, r12, r22, ha, hb))),
    Bool.or(Bool.or(
      Sat.some(Sat.x(r00, t1, t2, r10, r20, r02, r01, ha, hb), Sat.x(r01, t1, t2, r11, r21, r02, r00, ha, hb),
        Sat.x(r02, t1, t2, r12, r22, r01, r00, ha, hb)),
      Sat.some(Sat.x(r10, t2, t0, r20, r00, r12, r11, ha, hb), Sat.x(r11, t2, t0, r21, r01, r12, r10, ha, hb),
        Sat.x(r12, t2, t0, r22, r02, r11, r10, ha, hb))),
      Sat.some(Sat.x(r20, t0, t1, r00, r10, r22, r21, ha, hb), Sat.x(r21, t0, t1, r01, r11, r22, r20, ha, hb),
        Sat.x(r22, t0, t1, r02, r12, r21, r20, ha, hb)))))

# do the cube at (ax, ay, az) turned by qa and the one at (bx, by, bz)
# turned by qb touch?
# the same, with the room each cube's own turn takes this tick added to
# its side: a body that is turning claims where its turn is going, so a
# neighbour that moves at the same time -- and sees only the world as it
# was -- cannot walk into it.
def Geo.satw(+s: Nat, +ax: Nat, +ay: Nat, +az: Nat, +qa: Quat, +ea: Nat, +bx: Nat, +by: Nat, +bz: Nat,
  +qb: Quat, +eb: Nat) -> Bool:
  Geo.sat2(Nat.add(Nat.div(s, 2n), ea), Nat.add(Nat.div(s, 2n), eb),
    Z.diff(Nat.is_lt(bx, ax), bx, ax), Z.diff(Nat.is_lt(by, ay), by, ay),
    Z.diff(Nat.is_lt(bz, az), bz, az), Rot.mat(qa), Rot.mat(qb))


def Geo.sat(+s: Nat, +ax: Nat, +ay: Nat, +az: Nat, +qa: Quat, +bx: Nat, +by: Nat, +bz: Nat,
  +qb: Quat) -> Bool:
  Geo.satw(s, ax, ay, az, qa, 0n, bx, by, bz, qb, 0n)

# the arc a corner sweeps in one tick: half a side times the angle
def Geo.sweep1(zero: Bool, +s: Nat, +w: Wv) -> Nat:
  match zero:
    case True{}:
      0n
    case False{}:
      Nat.div(Nat.mul(Nat.div(Wv.mag(w), 256n), Nat.div(s, 2n)), 667544n)

# Asked once for the size being nothing and once for it being something,
# for the checker and not for the machine (a size of nothing sweeps
# nothing, so the answer is the same). The checker counts a number that
# big out one by one whenever it works out a term that holds it, and the
# arc is in every gate a move goes through (Geo.meets): unfolded, each
# lemma about a gate cost it a minute; folded until the size is known,
# five seconds for the whole of them.
def Geo.sweep(+s: Nat, +w: Wv) -> Nat:
  Geo.sweep1(Nat.is_eq(s, 0n), s, w)

# the mechanical energy, kinetic plus potential: vx^2 + vy^2 + vz^2 + g y
# said with projections, not by taking the body apart: a body the
# checker cannot work out is copied once per field when it is opened,
# and only four of the nine fields are worth anything here.
def Body.energy(+g: Nat, +b: Body) -> Nat:
  Nat.add(Nat.add(Nat.add(Z.sq(Body.vx(b)), Z.sq(Body.vy(b))), Z.sq(Body.vz(b))), Nat.mul(g, Body.y(b)))

def Body.energies(+g: Nat, bs: List<&2, Body>) -> Nat:
  match bs:
    case []:
      0n
    case b <> rest:
      Nat.add(Body.energy(g, b), Body.energies(g, rest))

# do the box at (x, y, z), turned by qa, and o's box overlap? While
# neither has turned this is the plain box test, to the unit; the moment
# one of them has, the fifteen directions decide.
def Geo.pair(flat: Bool, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +qa: Quat, +ox: Nat, +oy: Nat, +oz: Nat,
  +qb: Quat, +eb: Nat) -> Bool:
  match flat:
    case True{}:
      Bool.and(Geo.ovl(s, x, ox), Bool.and(Geo.ovl(s, z, oz), Geo.ovl(s, y, oy)))
    case False{}:
      Geo.satw(s, x, y, z, qa, 0n, ox, oy, oz, qb, eb)

# The gate a move has to pass also asks for a hair of room -- a quarter
# of a millimetre on a cube of a metre. The fifteen axes work out the
# shadows from a matrix in 2^-16, which is right to a few units, and the
# hair is what keeps those few units from ever becoming a real overlap.

# do two cubes really share space, with no room claimed for turns? This
# is what a check asks after the fact; the gate a move has to pass asks
# for more (Geo.meets), because a body that is turning claims where its
# turn is going.
def Geo.hits(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +qa: Quat, o: Body) -> Bool:
  Body{+ox, +oy, +oz, vx, vy, vz, ground, hit, +rt} = o
  Geo.pair(Bool.and(Quat.flat(qa), Quat.flat(Rot.q(rt))), s, x, y, z, qa, ox, oy, oz, Rot.q(rt), 0n)

# How much room an obstacle is handed beyond its own box: the arc it
# sweeps if it is turning, and a hair of skin on top of that, so that two
# cubes ticking against the same picture of the world cannot both walk
# into the same place, and so that the rounding of the fifteen directions
# (a matrix in 2^-16 over a cube of 2^18) is covered.
#
# The hair is a thirty-second of a millimetre, not half of one: a cube
# that rests on another has to be able to turn about their touching
# faces, and a turn is never allowed to lift a cube, so the skin it has
# to climb out of each tick must be smaller than the drop the turn
# itself buys. Eight units of skin cover the rounding (three units at
# the worst corner) and still leave the turn room to happen.
def Geo.skin(+s: Nat, +w: Wv) -> Nat:
  Nat.add(Geo.sweep(s, w), Nat.div(s, 16384n))

def Geo.meets(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +qa: Quat, o: Body) -> Bool:
  Body{+ox, +oy, +oz, vx, vy, vz, ground, hit, +rt} = o
  Geo.pair(Bool.and(Quat.flat(qa), Bool.and(Quat.flat(Rot.q(rt)), Wv.null(Rot.w(rt)))), s, x, y, z, qa, ox, oy,
    oz, Rot.q(rt), Geo.skin(s, Rot.w(rt)))

# is the box at (x, y, z) clear of every obstacle?
def Geo.free(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +qa: Quat, obs: List<&2, Body>) -> Bool:
  match obs:
    case []:
      True{}
    case o <> rest:
      Bool.and(Bool.not(Geo.meets(s, x, y, z, qa, o)), Geo.free(s, x, y, z, qa, rest))

# does the box at (x, y, z) meet the first obstacle of obs?
def Geo.head(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +qa: Quat, obs: List<&2, Body>) -> Bool:
  match obs:
    case []:
      False{}
    case o <> rest:
      Geo.meets(s, x, y, z, qa, o)

# how far below its box corner a turned cube hangs: its shadow on the
# world's up is taller than a cube, and it is the bottom that lands
def Geo.sag2(+s: Nat, m: Mat) -> Nat:
  Mat{axx, +axy, axz, ayx, +ayy, ayz, azx, +azy, azz} = m
  +h = Nat.div(s, 2n)
  +t = Nat.div(Nat.div(Nat.mul(h, Nat.add(Nat.add(Z.mag(axy), Z.mag(ayy)), Z.mag(azy))), 256n), 256n)
  Nat.sub(Pick.high(t, h), h)

def Geo.sag1(zero: Bool, +s: Nat, +q: Quat) -> Nat:
  match zero:
    case True{}:
      0n
    case False{}:
      Geo.sag2(s, Rot.mat(q))

# Folded like Geo.sweep, for the checker: a size of nothing hangs nothing,
# and until the size is known the sag stays a name. Every statement about
# the floor carries the sag of the turn a body ends in, which is a
# quaternion the checker would otherwise work out to the last unit.
def Geo.sag(+s: Nat, +q: Quat) -> Nat:
  Geo.sag1(Nat.is_eq(s, 0n), s, q)

def Geo.sagq(flat: Bool, +s: Nat, +q: Quat) -> Nat:
  match flat:
    case True{}:
      0n
    case False{}:
      Geo.sag(s, q)

# where the top of a body really is: a turned cube sticks out above its
# box corner by as much as it hangs below it, so whatever lands on it has
# to stop that much higher
def Geo.top(+s: Nat, +oy: Nat, +rt: Rot) -> Nat:
  Nat.add(Nat.add(oy, s), Geo.sagq(Quat.flat(Rot.q(rt)), s, Rot.q(rt)))

# the top of o, if it is under the column (x, z) at most at height y
def Geo.floor1(+s: Nat, +x: Nat, +y: Nat, +z: Nat, o: Body, +best: Nat) -> Nat:
  Body{+ox, +oy, +oz, vx, vy, vz, ground, hit, +rt} = o
  +top = Geo.top(s, oy, rt)
  Pick.n(Bool.and(Bool.and(Geo.ovl(s, x, ox), Geo.ovl(s, z, oz)), Bool.and(Nat.is_le(top, y), Nat.is_lt(best, top))), top, best)

# the highest top under the column (x, z), at most y: where a fall lands
# (the ground, 0, if nothing)
def Geo.floor(+s: Nat, +x: Nat, +y: Nat, +z: Nat, obs: List<&2, Body>, +best: Nat) -> Nat:
  match obs:
    case []:
      best
    case o <> rest:
      Geo.floor(s, x, y, z, rest, Geo.floor1(s, x, y, z, o, best))

# is there a top exactly at y under the column (x, z)?
def Geo.rests(+s: Nat, +x: Nat, +y: Nat, +z: Nat, obs: List<&2, Body>) -> Bool:
  match obs:
    case []:
      False{}
    case o <> rest:
      Body{+ox, +oy, +oz, vx, vy, vz, ground, hit, +rt} = o
      Bool.or(Bool.and(Bool.and(Geo.ovl(s, x, ox), Geo.ovl(s, z, oz)), Nat.is_eq(Nat.add(oy, s), y)),
        Geo.rests(s, x, y, z, rest))

# does the body stand clear at (x, y, z), turned by q? Clear of the
# obstacles, and clear of the world's floor -- a turned cube reaches
# below its own y by Geo.sag.
#
# The two are asked one inside the other, not side by side, so that a
# proof can take the clearing back out of the answer without ever
# working out the sag: the sag is a matrix in 2^-16 and the checker
# counts a number that big out one by one.
def Tick.fits2(free: Bool, +s: Nat, +y: Nat, +q: Quat) -> Bool:
  match free:
    case True{}:
      Nat.is_le(Geo.sag(s, q), y)
    case False{}:
      False{}

def Tick.fits(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat) -> Bool:
  Tick.fits2(Geo.free(s, x, y, z, q, obs), s, y, q)

# The room a turned cube keeps under it where it rests. A cube square
# with the world rests exactly on what holds it: its box test is exact.
# A turned one is judged by the fifteen axes, whose matrix is rounded,
# and the smallest turn moves that rounding by a few units either way;
# resting a hair above the contact -- an eighth of a millimetre -- is
# what lets it turn at all without every turn looking like a push into
# what holds it.
def Geo.gap(+q: Quat) -> Nat:
  Pick.n(Quat.flat(q), 0n, 32n)

# Could the body go down -- one unit past the gap it keeps -- without
# going into the floor or into a cube? A body that could is held by
# nothing; one that could not is held, by the floor or by a cube. This
# is what "standing" has to mean (LAWS.standing_is_held).
def Tick.sinks(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat) -> Bool:
  Bool.and(Nat.is_le(Nat.add(Geo.gap(q), 1n), y),
    Tick.fits(s, obs, x, Nat.sub(y, Nat.add(Geo.gap(q), 1n)), z, q))

# does the body stand on the world's floor -- its lowest point within
# two millimetres of it?
def Geo.onfloor(+s: Nat, +y: Nat, +q: Quat) -> Bool:
  Nat.is_le(y, Nat.add(Geo.sag(s, q), Nat.div(s, 512n)))


# Searching for a contact
# -----------------------
# Where a move is refused, the body still goes as far as it can: it comes
# to rest against what stopped it -- not a whole tick's step short of it,
# hanging in the air, and not a hair into it. Where that is, is found by
# halving, with the same test that gates every move. Nothing a search
# hands back is trusted: every place it finds is tested again, by the
# gate, where it is used; the search only decides where to look.

# x moved by d, never below 0 (a Nat taken below 0 is no number at all)
def Z.slide(+x: Nat, d: Z) -> Nat:
  match d:
    case Pos{p}:
      Nat.add(x, p)
    case Neg{+q}:
      Nat.sub(Pick.high(x, q), q)

# does the body fit with its corner moved by d along one axis (0 x, 1 y,
# 2 z)? Sideways the test is the obstacles' own (Geo.free): a slide does
# not change how high the body is. Up and down it is Tick.fits, which
# also asks for the floor.
def Probe.at(axis: Nat, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat, +d: Z) -> Bool:
  match axis:
    case 0n:
      Geo.free(s, Z.slide(x, d), y, z, q, obs)
    case 1n:
      Tick.fits(s, obs, x, Z.slide(y, d), z, q)
    case _:
      Geo.free(s, x, y, Z.slide(z, d), q, obs)

# half way from a to b
def Tick.half(+a: Nat, +b: Nat) -> Nat:
  Nat.add(a, Nat.div(Nat.sub(Pick.high(b, a), a), 2n))

# how many halvings bring a run of v units down to one
def Tick.nbits(n: Nat, zero: Bool, +v: Nat) -> Nat:
  match n zero:
    case 0n _:
      0n
    case _ True{}:
      0n
    case 1n+m False{}:
      Nat.add(1n, Tick.nbits(m, Nat.is_eq(Nat.div(v, 2n), 0n), Nat.div(v, 2n)))

def Tick.bits(+v: Nat) -> Nat:
  Tick.nbits(64n, Nat.is_eq(v, 0n), v)

# the furthest whole step in [lo, hi) along dir at which the body fits:
# lo is a step at which it does, hi one at which it does not, mid the
# step being looked at and fit what the test said of it
def Tick.bis(n: Nat, fit: Bool, +axis: Nat, +dir: Z, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat,
  +z: Nat, +q: Quat, +lo: Nat, +hi: Nat, +mid: Nat) -> Nat:
  match n fit:
    case 0n True{}:
      mid
    case 0n False{}:
      lo
    case 1n+m True{}:
      Tick.bis(m, Probe.at(axis, s, obs, x, y, z, q, Z.like(dir, Tick.half(mid, hi))), axis, dir, s, obs, x, y,
        z, q, mid, hi, Tick.half(mid, hi))
    case 1n+m False{}:
      Tick.bis(m, Probe.at(axis, s, obs, x, y, z, q, Z.like(dir, Tick.half(lo, mid))), axis, dir, s, obs, x, y,
        z, q, lo, mid, Tick.half(lo, mid))

def Tick.reach0(+axis: Nat, +dir: Z, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat,
  +lo: Nat, +hi: Nat) -> Nat:
  Tick.bis(Tick.bits(Nat.sub(Pick.high(hi, lo), lo)),
    Probe.at(axis, s, obs, x, y, z, q, Z.like(dir, Tick.half(lo, hi))), axis, dir, s, obs, x, y, z, q, lo, hi,
    Tick.half(lo, hi))

# Written out once for each shape the obstacles can have, like Tick.drop:
# for the checker, so the search stays folded until they are known.
def Tick.reach(+axis: Nat, +dir: Z, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat,
  +lo: Nat, +hi: Nat) -> Nat:
  match obs:
    case []:
      Tick.reach0(axis, dir, s, [], x, y, z, q, lo, hi)
    case o <> rest:
      Tick.reach0(axis, dir, s, o <> rest, x, y, z, q, lo, hi)

# Going down a cube at a time, and last by the whole drop q: the last drop
# at which the body still fits (0 when not even the first does). A fall
# of more than a cube in one tick could otherwise step over a cube.
def Tick.block(n: Nat, fit: Bool, last: Bool, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat,
  +qr: Quat, +q: Nat, +lo: Nat, +d: Nat) -> Nat:
  match n fit last:
    case _ False{} _:
      lo
    case _ True{} True{}:
      d
    case 0n True{} False{}:
      d
    case 1n+m True{} False{}:
      Tick.block(m, Tick.fits(s, obs, x, Nat.sub(y, Pick.low(Nat.add(d, s), q)), z, qr),
        Nat.is_eq(Pick.low(Nat.add(d, s), q), q), s, obs, x, y, z, qr, q, d, Pick.low(Nat.add(d, s), q))

# the whole drop fits, a cube at a time?
def Tick.path(n: Nat, more: Bool, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +qr: Quat,
  +q: Nat, +d: Nat) -> Bool:
  match n more:
    case 0n _:
      False{}
    case _ False{}:
      True{}
    case 1n+m True{}:
      Bool.and(Tick.fits(s, obs, x, Nat.sub(y, d), z, qr),
        Tick.path(m, Nat.is_lt(Nat.add(d, s), q), s, obs, x, y, z, qr, q, Nat.add(d, s)))

# How far the body can go down, at most q: down to where it touches, then
# back up by the gap it keeps (Geo.gap). The answer is only a place to
# look; the caller tests it.
def Tick.drop0(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +qr: Quat, +q: Nat) -> Nat:
  +qq = Pick.low(q, y)
  +f = Pick.low(s, qq)
  +lo = Tick.block(64n, Tick.fits(s, obs, x, Nat.sub(y, f), z, qr), Nat.is_eq(f, qq), s, obs, x, y, z, qr, qq,
    0n, f)
  +d0 = Tick.reach(1n, Neg{0n}, s, obs, x, y, z, qr, lo, Pick.low(Nat.add(lo, s), qq))
  Nat.sub(Pick.high(d0, Geo.gap(qr)), Geo.gap(qr))

# The drop asked for once for each shape the obstacles can have, like the
# turn (Tick.turn): for the checker and not for the machine. Asked this
# way the search cannot be unfolded until the obstacles are known, so it
# stays folded in every proof that carries a drop around. Unfolded, the
# checker works out its sixty-four steps in each proof that mentions the
# turn about a contact: the same lemma took over two minutes instead of
# five seconds.
def Tick.drop(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +qr: Quat, +q: Nat) -> Nat:
  match obs:
    case []:
      Tick.drop0(s, [], x, y, z, qr, q)
    case o <> rest:
      Tick.drop0(s, o <> rest, x, y, z, qr, q)

# The same sideways: how far along d the body gets before it touches,
# less than the whole of d (the whole of d is what was refused).
def Tick.slide(+axis: Nat, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat, +d: Z) -> Nat:
  Tick.reach(axis, d, s, obs, x, y, z, q, 0n, Z.mag(d))

# is anything holding the body up right now? It is held when it cannot
# go down (Tick.sinks): by the floor or by a cube, square with the world
# or turned. (flat is not asked any more; it stays for the laws that
# name this.)
def Geo.held(flat: Bool, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +q: Quat, obs: List<&2, Body>) -> Bool:
  Bool.not(Tick.sinks(s, obs, x, y, z, q))

# Contacts: the press and the turn it gives
# ----------------------------------------
# A contact presses a body along one direction, and where it presses
# counts as much as how hard. The press goes into the velocity, as it
# always did; the arm -- from the middle of the body to where it presses
# -- crossed with the press goes into the turning. Toppling is no rule of
# its own: a cube held up off its middle is turned by the very hold that
# keeps it from falling.
#
# A body held at a contact turns about that contact, not about its own
# middle, and that is harder to get going: I + m r^2 instead of I. A body
# that touches nothing turns about its middle, which is the plain I.

type Foot is Data:
  Foot{n: Nat, lx: Nat, hx: Nat, lz: Nat, hz: Nat, ty: Nat}

def Foot.none() -> Foot:
  Foot{0n, 0n, 0n, 0n, 0n, 0n}

def Foot.n(f: Foot) -> Nat:
  Foot{n, lx, hx, lz, hz, ty} = f
  n

def Foot.lx(f: Foot) -> Nat:
  Foot{n, lx, hx, lz, hz, ty} = f
  lx

def Foot.hx(f: Foot) -> Nat:
  Foot{n, lx, hx, lz, hz, ty} = f
  hx

def Foot.lz(f: Foot) -> Nat:
  Foot{n, lx, hx, lz, hz, ty} = f
  lz

def Foot.hz(f: Foot) -> Nat:
  Foot{n, lx, hx, lz, hz, ty} = f
  hz

def Foot.ty(f: Foot) -> Nat:
  Foot{n, lx, hx, lz, hz, ty} = f
  ty

def Z.scale(+n: Nat, v: Z) -> Z:
  match v:
    case Pos{+p}:
      Pos{Nat.mul(n, p)}
    case Neg{+q}:
      Neg{Nat.mul(n, q)}

# how much two runs of s, one from a and one from b, share
def Geo.lap(+s: Nat, +a: Nat, +b: Nat) -> Nat:
  +lo = Pick.high(a, b)
  +hi = Pick.low(Nat.add(a, s), Nat.add(b, s))
  Nat.sub(Pick.high(hi, lo), lo)

# where a run of s from b starts and ends inside a run of s from a, in
# steps from a's own start. The world lies far from zero -- a place is
# nearly a whole word -- so nothing here ever adds two places together.
def Geo.lapl(+s: Nat, +a: Nat, +b: Nat) -> Nat:
  Nat.sub(Pick.high(a, b), a)

def Geo.laph(+s: Nat, +a: Nat, +b: Nat) -> Nat:
  Nat.sub(Pick.high(Pick.low(Nat.add(a, s), Nat.add(b, s)), a), a)

# What holds the body up: the highest top under its middle, and how far
# that top reaches sideways. The press of the hold lands on that top,
# right under the middle while the middle is over it -- nothing to turn
# the body -- and at the edge of it the moment the middle goes past,
# which is what tips a cube over a ledge.
# The body that stands is not its box: a turned cube stands on what its
# shadow on the ground covers, and that reaches past the box -- a cube
# swung out over an edge still rests on it long after its box corner has
# gone beyond. Asked of the box alone, the foot came out empty the tick the
# corner passed the edge, the hold pressed at a corner of the box, and a
# cube that was tipping straight began to wobble sideways for nothing.
# The shadow is the box made d wider on each side (d is nothing for a cube
# square with the world, and then everything below is the box's own).
def Geo.lapd(+s: Nat, +d: Nat, +a: Nat, +b: Nat) -> Nat:
  +lo = Pick.high(Nat.sub(a, d), b)
  +hi = Pick.low(Nat.add(Nat.add(a, s), d), Nat.add(b, s))
  Nat.sub(Pick.high(hi, lo), lo)

def Geo.laplw(+s: Nat, +d: Nat, +a: Nat, +b: Nat) -> Nat:
  Nat.sub(Pick.high(Nat.sub(a, d), b), a)

def Geo.laphw(+s: Nat, +d: Nat, +a: Nat, +b: Nat) -> Nat:
  Nat.sub(Pick.high(Pick.low(Nat.add(Nat.add(a, s), d), Nat.add(b, s)), a), a)

# how much wider than its box a turned cube's shadow is, along x (or z),
# on each side: half a side times what its three axes lean into that
# direction (in 2^-16), less half a side
def Geo.widex(+s: Nat, m: Mat) -> Nat:
  Mat{+axx, axy, axz, +ayx, ayy, ayz, +azx, azy, azz} = m
  Nat.sub(Nat.div(Nat.div(Nat.mul(Nat.div(s, 2n), Nat.add(Nat.add(Z.mag(axx), Z.mag(ayx)), Z.mag(azx))), 256n), 256n),
    Nat.div(s, 2n))

def Geo.widez(+s: Nat, m: Mat) -> Nat:
  Mat{axx, axy, +axz, ayx, ayy, +ayz, azx, azy, +azz} = m
  Nat.sub(Nat.div(Nat.div(Nat.mul(Nat.div(s, 2n), Nat.add(Nat.add(Z.mag(axz), Z.mag(ayz)), Z.mag(azz))), 256n), 256n),
    Nat.div(s, 2n))

def Geo.foot2(on: Bool, up: Bool, +s: Nat, +dx: Nat, +dz: Nat, +x: Nat, +z: Nat, +ox: Nat, +oz: Nat, +top: Nat,
  +f: Foot) -> Foot:
  match on up:
    case False{} _:
      f
    case True{} True{}:
      Foot{1n, Geo.laplw(s, dx, x, ox), Geo.laphw(s, dx, x, ox), Geo.laplw(s, dz, z, oz), Geo.laphw(s, dz, z, oz), top}
    case True{} False{}:
      Foot{Nat.add(Foot.n(f), 1n), Pick.low(Foot.lx(f), Geo.laplw(s, dx, x, ox)),
        Pick.high(Foot.hx(f), Geo.laphw(s, dx, x, ox)), Pick.low(Foot.lz(f), Geo.laplw(s, dz, z, oz)),
        Pick.high(Foot.hz(f), Geo.laphw(s, dz, z, oz)), Foot.ty(f)}

def Geo.foot1(+s: Nat, +dx: Nat, +dz: Nat, +x: Nat, +y: Nat, +z: Nat, o: Body, +f: Foot) -> Foot:
  Body{+ox, +oy, +oz, vx, vy, vz, ground, hit, +rt} = o
  +top = Geo.top(s, oy, rt)
  +under = Bool.and(Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))),
    Bool.and(Nat.is_lt(0n, Geo.lapd(s, dx, x, ox)), Nat.is_lt(0n, Geo.lapd(s, dz, z, oz))))
  Geo.foot2(Bool.and(under, Bool.or(Nat.is_eq(Foot.n(f), 0n), Nat.is_le(Foot.ty(f), top))),
    Bool.or(Nat.is_eq(Foot.n(f), 0n), Nat.is_lt(Foot.ty(f), top)), s, dx, dz, x, z, ox, oz, top, f)

def Geo.footw(+s: Nat, +dx: Nat, +dz: Nat, +x: Nat, +y: Nat, +z: Nat, obs: List<&2, Body>, f: Foot) -> Foot:
  match obs:
    case []:
      f
    case o <> rest:
      Geo.footw(s, dx, dz, x, y, z, rest, Geo.foot1(s, dx, dz, x, y, z, o, f))

# the foot of the body at (x, y, z) turned by q, on the obstacles obs
def Geo.foot(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +q: Quat, obs: List<&2, Body>, f: Foot) -> Foot:
  match obs:
    case []:
      f
    case o <> rest:
      Geo.footw(s, Geo.widex(s, Rot.mat(q)), Geo.widez(s, Rot.mat(q)), x, y, z, o <> rest, f)

# the middle held down to the hold's reach, as an arm from the middle
def Geo.lean(+c: Nat, +lo: Nat, +hi: Nat) -> Z:
  +p = Pick.high(Pick.low(c, hi), lo)
  Z.diff(Nat.is_lt(p, c), p, c)

# how much harder a cube is to turn about a point an arm away than about
# its middle: (I + m r^2) / I = 1 + 6 r^2 / s^2, counted in eighths so it
# lands on the same division the middle takes
def Rot.about(+s: Nat, +rx: Z, +ry: Z, +rz: Z) -> Nat:
  Nat.add(8n, Nat.div(Nat.mul(48n, Nat.add(Nat.add(Z.sq(rx), Z.sq(ry)), Z.sq(rz))), Nat.mul(s, s)))

# v / d rounded away from 0: a torque that is there never rounds away
def Z.divc(v: Z, +d: Nat) -> Z:
  match v:
    case Pos{+n}:
      Pos{Nat.div(Nat.add(n, Nat.sub(Pick.high(d, 1n), 1n)), Pick.high(d, 1n))}
    case Neg{+n}:
      Neg{Nat.div(Nat.add(n, Nat.sub(Pick.high(d, 1n), 1n)), Pick.high(d, 1n))}

def Rot.kickd(+d: Nat, +rx: Z, +ry: Z, +rz: Z, +jx: Z, +jy: Z, +jz: Z) -> Wv:
  Wv{Z.divc(Rot.crx(ry, rz, jy, jz), d), Z.divc(Rot.cry(rz, rx, jz, jx), d),
    Z.divc(Rot.crz(rx, ry, jx, jy), d)}

# the body after a press of j at the arm r, turning about that contact
def Rot.press(+rt: Rot, +s: Nat, +rx: Z, +ry: Z, +rz: Z, +jx: Z, +jy: Z, +jz: Z) -> Rot:
  Rot{Rot.q(rt), Wv.add(Rot.w(rt), Rot.kickd(Rot.about(s, rx, ry, rz), rx, ry, rz, jx, jy, jz))}

def Pick.z(c: Bool, a: Z, b: Z) -> Z:
  match c:
    case True{}:
      a
    case False{}:
      b

# -1, 0 or 1: the sign of v, turned about
def Z.sgnop(v: Z) -> Z:
  match v:
    case Pos{+n}:
      Pick.z(Nat.is_eq(n, 0n), Pos{0n}, Neg{1n})
    case Neg{+n}:
      Pick.z(Nat.is_eq(n, 0n), Pos{0n}, Pos{1n})

# -1, 0 or 1: the sign of v turned about, with a dead zone. Along an axis
# of the cube that lies within a twentieth of a degree of level (the
# rounding a turned cube carries), both of its ends are as low as each
# other, and the body stands on both: the middle of them. That is how a
# cube lying on a face stands on the middle of the face, and one on an
# edge on the middle of the edge. The zone is that narrow because a wider
# one has the body pressed at the middle of a face that is tilted -- off
# its middle by the tilt, on the side that turns it further from level --
# and a cube that lands a little off square then never lies flat.
def Z.dead(v: Z) -> Z:
  match v:
    case Pos{+n}:
      Pick.z(Nat.is_lt(n, 64n), Pos{0n}, Neg{1n})
    case Neg{+n}:
      Pick.z(Nat.is_lt(n, 64n), Pos{0n}, Pos{1n})

# one coordinate of the arm from the middle to the body's lowest point:
# half a side along each axis of the cube, the way that axis leans down
def Tip.arm(+h: Nat, +sx: Z, +sy: Z, +sz: Z, +ax: Z, +ay: Z, +az: Z) -> Z:
  Z.divn(Z.divn(Z.scale(h, Z.add(Z.add(Z.mul(sx, ax), Z.mul(sy, ay)), Z.mul(sz, az))), 256n), 256n)

# the arm from the middle to the lowest point of the body: its lowest
# corner, or the middle of its lowest edge or face
#
# A cube on a face -- one axis of it pointing down, the other two level --
# stands on the whole face, and the floor's press can land anywhere on it:
# nothing turns it. Its lowest point is taken to be the middle of the face
# straight under its middle, whatever the tilt inside the dead zone puts
# the face's own middle sideways. Left to that, a cube lying a hair off
# square was pressed off its middle on the side that turns it further off.
def Hold.face(face: Bool, a: Z) -> Z:
  match face:
    case True{}:
      Pos{0n}
    case False{}:
      a

def Hold.low2(+face: Bool, +h: Nat, +sx: Z, +sy: Z, +sz: Z, +axx: Z, +axy: Z, +axz: Z, +ayx: Z, +ayy: Z, +ayz: Z,
  +azx: Z, +azy: Z, +azz: Z) -> Wv:
  Wv{Hold.face(face, Tip.arm(h, sx, sy, sz, axx, ayx, azx)), Tip.arm(h, sx, sy, sz, axy, ayy, azy),
    Hold.face(face, Tip.arm(h, sx, sy, sz, axz, ayz, azz))}

def Hold.low(m: Mat, +s: Nat) -> Wv:
  Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +sx = Z.dead(axy)
  +sy = Z.dead(ayy)
  +sz = Z.dead(azy)
  Hold.low2(Nat.is_eq(Nat.add(Nat.add(Z.mag(sx), Z.mag(sy)), Z.mag(sz)), 1n), Nat.div(s, 2n), sx, sy, sz,
    axx, axy, axz, ayx, ayy, ayz, azx, azy, azz)

# a point a held inside [lo, hi], as an arm from the middle c
def Geo.leanf(+c: Nat, +a: Nat, +lo: Nat, +hi: Nat) -> Z:
  +p = Pick.high(Pick.low(a, hi), lo)
  Z.diff(Nat.is_lt(p, c), p, c)

# Where a cube holds a body up: at the body's lowest point, held inside
# what holds it. The foot is how far the tops under the body reach, as
# steps from the body's corner; the lowest point, pushed inside the foot
# sideways, is where the press lands. While the lowest point is over the
# foot the press lands right on it; the moment it is past the foot's
# edge the press lands on that edge -- off to one side of the middle,
# which is what tips a cube over a ledge, square with the world or on a
# corner. A cube square with the world has its lowest point in the middle
# of its base, so this is the middle held inside the foot, as it was.
def Hold.arm(f: Foot, m: Mat, +s: Nat) -> Wv:
  Foot{+n, +lx, +hx, +lz, +hz, +ty} = f
  +h = Nat.div(s, 2n)
  +lw = Hold.low(m, s)
  Wv{Geo.leanf(h, Z.slide(h, Wv.x(lw)), lx, hx), Wv.y(lw), Geo.leanf(h, Z.slide(h, Wv.z(lw)), lz, hz)}

# the body after a press j straight up at the arm a
def Rot.pressw(+rt: Rot, +s: Nat, +a: Wv, +j: Nat) -> Rot:
  Rot.press(rt, s, Wv.x(a), Wv.y(a), Wv.z(a), Pos{0n}, Pos{j}, Pos{0n})

# the hold of a tick: the floor presses at the body's lowest point, which
# is as wide as the floor; a cube presses at that point held inside it
def Rot.held(floor: Bool, +rt: Rot, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +j: Nat,
  obs: List<&2, Body>) -> Rot:
  match floor:
    case True{}:
      Rot.pressw(rt, s, Hold.low(Rot.mat(Rot.q(rt)), s), j)
    case False{}:
      Rot.pressw(rt, s, Hold.arm(Geo.foot(s, x, y, z, Rot.q(rt), obs, Foot.none()), Rot.mat(Rot.q(rt)), s), j)

# Friction
# --------
# On the ground, friction takes up to mu g of speed each tick, against the
# velocity: each component loses its share, F a / s (a its size, s the
# speed), never more than it has. s is the speed rounded up, from Newton's
# square root, checked (s^2 >= a^2 + b^2, s <= a + b; else a + b, which
# always is).

# the speed of (a, b), rounded up
def Fric.speed(+a: Nat, +b: Nat) -> Nat:
  +n = Nat.add(Nat.mul(a, a), Nat.mul(b, b))
  +ab = Nat.add(a, b)
  +r = Fric.ceil(n, Fric.floor(n, ab))
  Pick.n(Bool.and(Nat.is_le(n, Nat.mul(r, r)), Nat.is_le(r, ab)), r, ab)

# what friction F takes from a component of size a, the speed being s
def Fric.take(+f: Nat, +a: Nat, +s: Nat) -> Nat:
  +t = Pick.low(a, Nat.div(Nat.mul(f, a), s))
  Pick.n(Bool.and(Nat.is_le(t, a), Nat.is_le(Nat.mul(t, s), Nat.mul(f, a))), t, 0n)

def Fric.apply(+f: Nat, +vx: Z, +vz: Z) -> Z & Z:
  +a = Z.mag(vx)
  +b = Z.mag(vz)
  +s = Fric.speed(a, b)
  (Z.cut(Fric.take(f, a, s), vx), Z.cut(Fric.take(f, b, s), vz))

# The motor
# ---------
# The player walks toward a direction (a vector of size 4096): the motor
# adds acc along it, the same acc whatever the speed already is -- there is
# no top speed, and no push at all while off the ground.

type Wish is Data:
  Wish{ux: Z, uz: Z}

type In is Data:
  In{walk: Maybe<&2, Wish>, jump: Bool}

def In.idle() -> In:
  In{None{}, False{}}

def Motor.go(+acc: Nat, walk: Maybe<&2, Wish>, +vx: Z, +vz: Z) -> Z & Z:
  match walk:
    case None{}:
      (vx, vz)
    case Some{Wish{ux, uz}}:
      (Z.add(vx, Z.q12(acc, ux)), Z.add(vz, Z.q12(acc, uz)))

# Driving
# -------
# The forces of a tick on the velocity: on the ground, friction, the motor
# and the jump (a takeoff at the jump speed); in the air, nothing at all --
# no motor, no friction (gravity comes with the vertical move, Move.y). The
# tick starts untouched (hit off).

def Drive.leap(jump: Bool, +k: K, +x: Nat, +y: Nat, +z: Nat, v: Z & Z, +rt: Rot) -> Body:
  match jump:
    case True{}:
      K{g, mu, j, acc, size} = k
      (vx, vz) = v
      Body{x, y, z, vx, Pos{j}, vz, False{}, False{}, rt}
    case False{}:
      (vx, vz) = v
      Body{x, y, z, vx, Pos{0n}, vz, True{}, False{}, rt}

def Drive.ground(+k: K, walk: Maybe<&2, Wish>, jump: Bool, +x: Nat, +y: Nat, +z: Nat, v: Z & Z, +rt: Rot) -> Body:
  K{g, mu, j, +acc, size} = k
  (vx, vz) = v
  Drive.leap(jump, k, x, y, z, Motor.go(acc, walk, vx, vz), rt)

def Drive.air(+x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z, +rt: Rot) -> Body:
  Body{x, y, z, vx, vy, vz, False{}, False{}, rt}

def Drive.go(gr: Bool, +k: K, walk: Maybe<&2, Wish>, jump: Bool, +x: Nat, +y: Nat, +z: Nat,
  +vx: Z, +vy: Z, +vz: Z, +rt: Rot) -> Body:
  match gr:
    case True{}:
      Drive.ground(k, walk, jump, x, y, z, Fric.apply(K.fric(k), vx, vz), rt)
    case False{}:
      Drive.air(x, y, z, vx, vy, vz, rt)

def Body.drive(+k: K, inp: In, b: Body) -> Body:
  In{walk, jump} = inp
  Body{x, y, z, vx, vy, vz, gr, hit, +rt} = b
  Drive.go(gr, k, walk, jump, x, y, z, vx, vy, vz, rt)

# Sharing
# -------
# Two bodies meeting along an axis, one closing in on the other, leave
# with the same velocity -- a perfectly inelastic collision of equal
# masses: the momentum (the sum) is kept exactly, the odd unit going to
# the one pushed, and kinetic energy is lost, never made. What is shared,
# d, splits as d = e + e + j (checked, with lo + d = hi; else nothing
# changes).

def Share.chk(ok: Bool, +p: Nat, +q: Nat, +h: Nat, +r: Nat) -> Nat & Nat:
  match ok:
    case True{}:
      (h, r)
    case False{}:
      (p, q)

def Share.sign(pos: Bool, m: Nat & Nat) -> Z & Z:
  match pos:
    case True{}:
      (h, r) = m
      (Pos{h}, Pos{r})
    case False{}:
      (h, r) = m
      (Neg{h}, Neg{r})

def Share.back(pos: Bool, +p: Nat, +q: Nat) -> Z & Z:
  match pos:
    case True{}:
      (Pos{p}, Neg{q})
    case False{}:
      (Neg{p}, Pos{q})

def Share.flip(ok: Bool, up: Bool, pos: Bool, +p: Nat, +q: Nat, +h: Nat, +r: Nat) -> Z & Z:
  match ok:
    case True{}:
      Share.sign(up, (h, r))
    case False{}:
      Share.back(pos, p, q)

# same direction, sizes p (the pusher's) and q, sign pos; lo, hi the
# smaller and the bigger size
def Share.same3(pos: Bool, +p: Nat, +q: Nat, +lo: Nat, +hi: Nat, +d: Nat, +e: Nat) -> Z & Z:
  Share.sign(pos, Share.chk(Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)),
    p, q, Nat.add(lo, e), Nat.add(Nat.add(lo, e), Nat.sub(d, Nat.add(e, e)))))

def Share.same2(pos: Bool, +p: Nat, +q: Nat, +lo: Nat, +hi: Nat) -> Z & Z:
  +d = Nat.sub(hi, lo)
  Share.same3(pos, p, q, lo, hi, d, Nat.div(d, 2n))

def Share.same(+le: Bool, pos: Bool, +p: Nat, +q: Nat) -> Z & Z:
  Share.same2(pos, p, q, Pick.n(le, p, q), Pick.n(le, q, p))

# opposite directions: +p against -q (pos) or -p against +q; what is
# left, d = |p - q|, goes the bigger one's way (up: the result is Pos)
def Share.opp3(up: Bool, pos: Bool, +p: Nat, +q: Nat, +lo: Nat, +hi: Nat, +d: Nat, +e: Nat) -> Z & Z:
  Share.flip(Bool.and(Nat.is_le(Nat.add(e, e), d), Nat.is_eq(Nat.add(lo, d), hi)), up, pos, p, q, e,
    Nat.add(e, Nat.sub(d, Nat.add(e, e))))

def Share.opp2(up: Bool, pos: Bool, +p: Nat, +q: Nat, +lo: Nat, +hi: Nat) -> Z & Z:
  +d = Nat.sub(hi, lo)
  Share.opp3(up, pos, p, q, lo, hi, d, Nat.div(d, 2n))

def Share.opp(+le: Bool, +pos: Bool, +p: Nat, +q: Nat) -> Z & Z:
  Share.opp2(Bool.xor(le, pos), pos, p, q, Pick.n(le, p, q), Pick.n(le, q, p))

# a's and b's velocities after they meet
def Share.go(a: Z, b: Z) -> Z & Z:
  match a b:
    case Pos{+p} Pos{+q}:
      Share.same(Nat.is_le(p, q), True{}, p, q)
    case Neg{+p} Neg{+q}:
      Share.same(Nat.is_le(p, q), False{}, p, q)
    case Pos{+p} Neg{+q}:
      Share.opp(Nat.is_le(p, q), True{}, p, q)
    case Neg{+p} Pos{+q}:
      Share.opp(Nat.is_le(p, q), False{}, p, q)

# Pushes
# ------
# A move along x (or z) that runs into obstacles: the first one met shares
# its velocity along the axis with the mover, if the mover closes in on
# it, and the mover's box stops against it.

type Pushed is Data:
  Pushed{v: Z, obs: List<&2, Body>, at: Maybe<&2, Nat>}

# does a mover at v, going along d, close in on a body at w?
def Push.closing(d: Z, +v: Z, +w: Z) -> Bool:
  match d:
    case Pos{p}:
      Z.above(v, w)
    case Neg{q}:
      Z.above(w, v)

def Push.share(close: Bool, +v: Z, +w: Z) -> Z & Z:
  match close:
    case True{}:
      Share.go(v, w)
    case False{}:
      (v, w)

# where the mover's box stops against a box at o, going along d
def Push.stop(+s: Nat, d: Z, +o: Nat) -> Nat:
  match d:
    case Pos{p}:
      Nat.sub(o, s)
    case Neg{q}:
      Nat.add(o, s)

def Push.cons(+o: Body, r: Pushed) -> Pushed:
  Pushed{v, obs, at} = r
  Pushed{v, o <> obs, at}

def Push.xput(vw: Z & Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovy: Z, +ovz: Z, +og: Bool, +oh: Bool,
  rest: List<&2, Body>, +rt: Rot) -> Pushed:
  (v2, w2) = vw
  Pushed{v2, Body{ox, oy, oz, w2, ovy, ovz, og, oh, rt} <> rest, Some{at}}

def Push.xone(+s: Nat, +d: Z, +v: Z, o: Body, rest: List<&2, Body>) -> Pushed:
  Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +rt} = o
  Push.xput(Push.share(Push.closing(d, v, ovx), v, ovx), Push.stop(s, d, ox), ox, oy, oz, ovy, ovz, og, oh, rest, rt)

def Push.x(+s: Nat, obs: List<&2, Body>, +d: Z, +cx: Nat, +y: Nat, +z: Nat, +v: Z, +qa: Quat, here: Bool) -> Pushed:
  match obs here:
    case Nil{} _:
      Pushed{v, [], None{}}
    case o <> rest True{}:
      Push.xone(s, d, v, o, rest)
    case +o <> +rest False{}:
      Push.cons(o, Push.x(s, rest, d, cx, y, z, v, qa, Geo.head(s, cx, y, z, qa, rest)))

def Push.zput(vw: Z & Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: Z, +ovy: Z, +og: Bool, +oh: Bool,
  rest: List<&2, Body>, +rt: Rot) -> Pushed:
  (v2, w2) = vw
  Pushed{v2, Body{ox, oy, oz, ovx, ovy, w2, og, oh, rt} <> rest, Some{at}}

def Push.zone(+s: Nat, +d: Z, +v: Z, o: Body, rest: List<&2, Body>) -> Pushed:
  Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh, +rt} = o
  Push.zput(Push.share(Push.closing(d, v, ovz), v, ovz), Push.stop(s, d, oz), ox, oy, oz, ovx, ovy, og, oh, rest, rt)

def Push.z(+s: Nat, obs: List<&2, Body>, +d: Z, +x: Nat, +y: Nat, +cz: Nat, +v: Z, +qa: Quat, here: Bool) -> Pushed:
  match obs here:
    case Nil{} _:
      Pushed{v, [], None{}}
    case o <> rest True{}:
      Push.zone(s, d, v, o, rest)
    case +o <> +rest False{}:
      Push.cons(o, Push.z(s, rest, d, x, y, cz, v, qa, Geo.head(s, x, y, cz, qa, rest)))

# Moves
# -----
# Each move is gated: the box goes to its new place only if it is free
# there; blocked, it stops against what it met (if free there) or stays.

def Move.xput(ok: Bool, +obs: List<&2, Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: Z, +vy: Z, +vz: Z, +gr: Bool, +rt: Rot)
  -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{cx, y, z, v, vy, vz, gr, True{}, rt}, obs)
    case False{}:
      (Body{x, y, z, v, vy, vz, gr, True{}, rt}, obs)

def Move.xok(+obs: List<&2, Body>, +cx: Nat, b: Body) -> Body & List<&2, Body>:
  Body{x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  (Body{cx, y, z, vx, vy, vz, gr, hit, rt}, obs)

# after a push: the pusher stops where it reached, with the velocity the
# push left it
def Move.xpushed(r: Pushed, +cx: Nat, +y: Nat, +z: Nat, +vy: Z, +vz: Z, +gr: Bool, +rt: Rot)
  -> Body & List<&2, Body>:
  Pushed{v, obs, at} = r
  (Body{cx, y, z, v, vy, vz, gr, True{}, rt}, obs)

# A move along x that does not fit goes as far as it can (Tick.slide),
# to cx, and stops there. It pushes only if it got somewhere clear and,
# one unit further on (pr), would be in something: then it is touching
# that, and the first body in the way takes its share of the velocity.
# Anything else pushes nothing -- a body is never shoved by one that has
# not reached it (LAWS.a_push_is_a_touch_x).
def Move.xtouch(touch: Bool, +s: Nat, +obs: List<&2, Body>, +d: Z, +cx: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: Z, +vy: Z, +vz: Z, +gr: Bool, +rt: Rot) -> Body & List<&2, Body>:
  match touch:
    case True{}:
      Move.xpushed(Push.x(s, obs, d, pr, y, z, vx, Rot.q(rt), Geo.head(s, pr, y, z, Rot.q(rt), obs)), cx, y, z,
        vy, vz, gr, rt)
    case False{}:
      Move.xput(Geo.free(s, cx, y, z, Rot.q(rt), obs), obs, cx, x, y, z, vx, vy, vz, gr, rt)

# how far along x a refused move gets: as far as the body fits
def Move.xto(+s: Nat, +obs: List<&2, Body>, +d: Z, +x: Nat, +y: Nat, +z: Nat, +q: Quat) -> Nat:
  Z.slide(x, Z.like(d, Tick.slide(0n, s, obs, x, y, z, q, d)))

# does the body at cx touch something one unit on, along d?
def Move.xtouches(+s: Nat, +obs: List<&2, Body>, +d: Z, +cx: Nat, +y: Nat, +z: Nat, +q: Quat) -> Bool:
  Bool.and(Geo.free(s, cx, y, z, q, obs), Bool.not(Geo.free(s, Z.shift(cx, Z.like(d, 1n)), y, z, q, obs)))

def Move.xreach(+s: Nat, +obs: List<&2, Body>, +d: Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z,
  +vz: Z, +gr: Bool, +rt: Rot) -> Body & List<&2, Body>:
  Move.xtouch(Move.xtouches(s, obs, d, cx, y, z, Rot.q(rt)), s, obs, d, cx, Z.shift(cx, Z.like(d, 1n)), x, y, z,
    vx, vy, vz, gr, rt)

def Move.xno(+s: Nat, +obs: List<&2, Body>, +d: Z, +cx: Nat, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, hit, +rt} = b
  Move.xreach(s, obs, d, Move.xto(s, obs, d, x, y, z, Rot.q(rt)), x, y, z, vx, vy, vz, gr, rt)

def Move.xgo(+s: Nat, ok: Bool, +obs: List<&2, Body>, +d: Z, +cx: Nat, b: Body) -> Body & List<&2, Body>:
  match ok:
    case True{}:
      Move.xok(obs, cx, b)
    case False{}:
      Move.xno(s, obs, d, cx, b)

# the move along x, by the start and end velocities added
def Move.x(+s: Nat, +obs: List<&2, Body>, +v0: Z, +b: Body) -> Body & List<&2, Body>:
  +d = Z.add(v0, Body.vx(b))
  +cx = Z.shift(Body.x(b), d)
  Move.xgo(s, Bool.and(Z.fits(Body.x(b), d), Geo.free(s, cx, Body.y(b), Body.z(b), Rot.q(Body.rot(b)), obs)), obs, d, cx, b)

def Move.zput(ok: Bool, +obs: List<&2, Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +v: Z, +gr: Bool, +rt: Rot)
  -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{x, y, cz, vx, vy, v, gr, True{}, rt}, obs)
    case False{}:
      (Body{x, y, z, vx, vy, v, gr, True{}, rt}, obs)

def Move.zok(+obs: List<&2, Body>, +cz: Nat, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  (Body{x, y, cz, vx, vy, vz, gr, hit, rt}, obs)

def Move.zpushed(r: Pushed, +x: Nat, +y: Nat, +cz: Nat, +vx: Z, +vy: Z, +gr: Bool, +rt: Rot)
  -> Body & List<&2, Body>:
  Pushed{v, obs, at} = r
  (Body{x, y, cz, vx, vy, v, gr, True{}, rt}, obs)

# the same along z (LAWS.a_push_is_a_touch_z)
def Move.ztouch(touch: Bool, +s: Nat, +obs: List<&2, Body>, +d: Z, +cz: Nat, +pr: Nat, +x: Nat, +y: Nat, +z: Nat,
  +vx: Z, +vy: Z, +vz: Z, +gr: Bool, +rt: Rot) -> Body & List<&2, Body>:
  match touch:
    case True{}:
      Move.zpushed(Push.z(s, obs, d, x, y, pr, vz, Rot.q(rt), Geo.head(s, x, y, pr, Rot.q(rt), obs)), x, y, cz,
        vx, vy, gr, rt)
    case False{}:
      Move.zput(Geo.free(s, x, y, cz, Rot.q(rt), obs), obs, cz, x, y, z, vx, vy, vz, gr, rt)

def Move.zto(+s: Nat, +obs: List<&2, Body>, +d: Z, +x: Nat, +y: Nat, +z: Nat, +q: Quat) -> Nat:
  Z.slide(z, Z.like(d, Tick.slide(2n, s, obs, x, y, z, q, d)))

def Move.ztouches(+s: Nat, +obs: List<&2, Body>, +d: Z, +x: Nat, +y: Nat, +cz: Nat, +q: Quat) -> Bool:
  Bool.and(Geo.free(s, x, y, cz, q, obs), Bool.not(Geo.free(s, x, y, Z.shift(cz, Z.like(d, 1n)), q, obs)))

def Move.zreach(+s: Nat, +obs: List<&2, Body>, +d: Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z,
  +vz: Z, +gr: Bool, +rt: Rot) -> Body & List<&2, Body>:
  Move.ztouch(Move.ztouches(s, obs, d, x, y, cz, Rot.q(rt)), s, obs, d, cz, Z.shift(cz, Z.like(d, 1n)), x, y, z,
    vx, vy, vz, gr, rt)

def Move.zno(+s: Nat, +obs: List<&2, Body>, +d: Z, +cz: Nat, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, hit, +rt} = b
  Move.zreach(s, obs, d, Move.zto(s, obs, d, x, y, z, Rot.q(rt)), x, y, z, vx, vy, vz, gr, rt)

def Move.zgo(+s: Nat, ok: Bool, +obs: List<&2, Body>, +d: Z, +cz: Nat, b: Body) -> Body & List<&2, Body>:
  match ok:
    case True{}:
      Move.zok(obs, cz, b)
    case False{}:
      Move.zno(s, obs, d, cz, b)

def Move.z(+s: Nat, +obs: List<&2, Body>, +v0: Z, +b: Body) -> Body & List<&2, Body>:
  +d = Z.add(v0, Body.vz(b))
  +cz = Z.shift(Body.z(b), d)
  Move.zgo(s, Bool.and(Z.fits(Body.z(b), d), Geo.free(s, Body.x(b), Body.y(b), cz, Rot.q(Body.rot(b)), obs)), obs, d, cz, b)

# Gravity: a tick takes g from the vertical velocity; the move is the
# start and end velocities added, (v', v + v'). Rising at s < g, the body
# turns over within the tick.
def Fly.up(lt: Bool, +g: Nat, +s: Nat) -> Z & Z:
  match lt:
    case False{}:
      (Pos{Nat.sub(s, g)}, Pos{Nat.add(s, Nat.sub(s, g))})
    case True{}:
      (Neg{Nat.sub(g, s)}, Z.diff(Nat.is_lt(s, Nat.sub(g, s)), s, Nat.sub(g, s)))

def Fly.step(+g: Nat, v: Z) -> Z & Z:
  match v:
    case Pos{+s}:
      Fly.up(Nat.is_lt(s, g), g, s)
    case Neg{+s}:
      (Neg{Nat.add(s, g)}, Neg{Nat.add(Nat.add(s, s), g)})

def Move.rise(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: Z, +v: Z, +vz: Z, +hit: Bool, +rt: Rot) -> Body:
  match ok:
    case True{}:
      Body{x, Nat.add(y, p), z, vx, v, vz, False{}, hit, rt}
    case False{}:
      Body{x, y, z, vx, Pos{0n}, vz, False{}, True{}, rt}

# A fall that is refused is a landing: the body goes down as far as it
# can (Tick.drop) and stops there, standing -- but only if it really is
# held there, which is asked again here, with the very test the laws use.
# Where it is not (a search that found nothing to stand on), it is not
# stood anywhere: it stays where it was, still falling as fast as it was
# at the start of the tick, and falls again the next. Nothing is ever
# left standing in mid-air, and nothing is ever let down into the floor.
def Move.land(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +ny: Nat, +vx: Z, +vz: Z, +v0: Z, +rt: Rot) -> Body:
  match ok:
    case True{}:
      Body{x, ny, z, vx, Pos{0n}, vz, True{}, True{}, rt}
    case False{}:
      Body{x, y, z, vx, v0, vz, False{}, True{}, rt}

# the whole drop q is free: above the floor, clear of every cube, and
# clear at every whole cube on the way
def Move.fallok(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +qr: Quat) -> Bool:
  Bool.and(Nat.is_le(q, y), Bool.and(Tick.fits(s, obs, x, Nat.sub(y, q), z, qr),
    Tick.path(64n, Nat.is_lt(s, q), s, obs, x, y, z, qr, q, s)))

# where a refused fall looks to land
def Move.landy(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +qr: Quat, +q: Nat) -> Nat:
  Nat.sub(y, Tick.drop(s, obs, x, y, z, qr, q))

# and whether it may: it fits there, and there it is held
def Move.landok(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +qr: Quat) -> Bool:
  Bool.and(Tick.fits(s, obs, x, y, z, qr), Bool.not(Tick.sinks(s, obs, x, y, z, qr)))

def Move.fall(+s: Nat, ok: Bool, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +vx: Z, +v: Z, +vz: Z,
  +v0: Z, +hit: Bool, +rt: Rot) -> Body:
  match ok:
    case True{}:
      Body{x, Nat.sub(y, q), z, vx, v, vz, False{}, hit, rt}
    case False{}:
      +ny = Move.landy(s, obs, x, y, z, Rot.q(rt), q)
      Move.land(Move.landok(s, obs, x, ny, z, Rot.q(rt)), x, y, z, ny, vx, vz, v0, rt)

# the vertical move of a body in the air: up if the way up is clear; down
# the whole drop if the body fits there -- above the floor, clear of every
# cube, and clear at every whole cube on the way -- else a landing
def Move.fly(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy0: Z, +vz: Z, +hit: Bool,
  st: Z & Z, +rt: Rot) -> Body:
  (v, d) = st
  match d:
    case Pos{+p}:
      Move.rise(Geo.free(s, x, Nat.add(y, p), z, Rot.q(rt), obs), x, y, z, p, vx, v, vz, hit, rt)
    case Neg{+q}:
      Move.fall(s, Move.fallok(s, obs, x, y, z, q, Rot.q(rt)), obs, x, y, z, q, vx, v, vz, vy0, hit, rt)

# a body that is held up is pressed up by what holds it, every tick, by
# just what gravity would have taken: that press is what keeps it there,
# and where the press lands is what turns it
def Move.stay(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z,
  +vz: Z, +hit: Bool, +rt: Rot) -> Body:
  match rest:
    case True{}:
      Body{x, y, z, vx, vy, vz, True{}, hit, Rot.held(Geo.onfloor(s, y, Rot.q(rt)), rt, s, x, y, z, g, obs)}
    case False{}:
      Body{x, y, z, vx, vy, vz, False{}, hit, rt}

def Move.ystay(+s: Nat, +g: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  Move.stay(Geo.held(Quat.flat(Rot.q(rt)), s, x, y, z, Rot.q(rt), obs), s, g, obs, x, y, z, vx, vy, vz, hit, rt)

def Move.yfly(+s: Nat, +g: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  Move.fly(s, obs, x, y, z, vx, vy, vz, hit, Fly.step(g, vy), rt)

# the fall, with the body kept whole until the ground is known
def Move.ygo(+s: Nat, gr: Bool, +g: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  match gr:
    case True{}:
      Move.ystay(s, g, obs, b)
    case False{}:
      Move.yfly(s, g, obs, b)

# the vertical move: standing, whether still held; else a tick of
# gravity, a free fall or rise, or a landing or a bump
def Move.y(+s: Nat, +g: Nat, +obs: List<&2, Body>, +b: Body) -> Body:
  Move.ygo(s, Body.ground(b), g, obs, b)

# The tick
# --------
# The forces on the velocity, then the moves along x, z and y. Returns the
# body and its obstacles (the ones it pushed now move).

def Tick.y(+s: Nat, +g: Nat, r: Body & List<&2, Body>) -> Body & List<&2, Body>:
  (b, +obs) = r
  (Move.y(s, g, obs, b), obs)

def Tick.z(+s: Nat, +g: Nat, +vz0: Z, r: Body & List<&2, Body>) -> Body & List<&2, Body>:
  (b, obs) = r
  Tick.y(s, g, Move.z(s, obs, vz0, b))


# The turn of a tick
# ------------------
# A body that touches nothing turns about its own middle. A body that is
# held turns about where it is held: its middle swings round that point,
# which is how a cube goes over an edge. Either way the turn is taken
# only where it leaves the body clear of everything and of the floor, and
# never where it would lift the body -- nothing lifts itself.
#
# A refused turn is a knock: the body stays where it was, and what stopped
# the turn stops the turning -- all of it, as a contact that gives nothing
# back does. Keeping it instead left cubes lying still with a turning
# they could never take, and a body that is turning claims the room its
# turn sweeps: its neighbours hung in the air beside it or were shoved
# from across the room. The one turn that is never spent is a hold that
# leans (Wv.keep): it hands the turning back every tick anyway, and
# spending it is what kept a perched cube from ever tipping.
#
# A body that stood, and that the turn carried off what held it, stands
# no more: standing is asked again wherever the body ends up.
def Tick.stands(gr: Bool, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat) -> Bool:
  match gr:
    case True{}:
      Bool.not(Tick.sinks(s, obs, x, y, z, q))
    case False{}:
      False{}

# A body that stood, and that the turn carried off what held it, is let
# go: its middle went down d this tick, and it goes on down as fast as
# that drop pays for -- min(g, d) squared is at most g d, the energy the
# drop gave up, so letting go makes none.
def Tick.letv(gr: Bool, held: Bool, +g: Nat, +d: Nat, +vy: Z) -> Z:
  match gr held:
    case True{} True{}:
      vy
    case True{} False{}:
      Neg{Pick.low(g, d)}
    case False{} _:
      vy

# a turn may carry a standing body off what held it only by letting it
# down: one that would come off it without going down at all is not
# turning about anything that holds it, and is refused
def Tick.keeps(gr: Bool, +s: Nat, +obs: List<&2, Body>, +y: Nat, +nx: Nat, +ny: Nat, +nz: Nat, +q: Quat) -> Bool:
  match gr:
    case True{}:
      Bool.or(Nat.is_lt(ny, y), Bool.not(Tick.sinks(s, obs, nx, ny, nz, q)))
    case False{}:
      True{}

def Tick.put(ok: Bool, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat,
  +nz: Nat, +vx: Z, +vy: Z, +vz: Z, +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot) -> Body:
  match ok:
    case True{}:
      +st = Tick.stands(gr, s, obs, nx, ny, nz, Rot.q(r2))
      Body{nx, ny, nz, vx, Tick.letv(gr, st, g, Nat.sub(y, ny), vy), vz, st, hit, r2}
    case False{}:
      Body{x, y, z, vx, vy, vz, gr, True{}, rt}

# the gate of a turn: no higher than the body was, clear of everything
# and of the floor, and not carried off its hold without going down
def Tick.turnok(+s: Nat, +obs: List<&2, Body>, +y: Nat, +nx: Nat, +ny: Nat, +nz: Nat, +q: Quat, +gr: Bool) -> Bool:
  Bool.and(Nat.is_le(ny, y), Bool.and(Tick.fits(s, obs, nx, ny, nz, q), Tick.keeps(gr, s, obs, y, nx, ny, nz, q)))

def Tick.place(+s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat,
  +nz: Nat, +vx: Z, +vy: Z, +vz: Z, +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot) -> Body:
  Tick.put(Tick.turnok(s, obs, y, nx, ny, nz, Rot.q(r2), gr), s, g, obs,
    x, y, z, nx, ny, nz, vx, vy, vz, gr, hit, rt, r2)

# The turning a refused turn leaves the body with (Tick.put hands back the
# body it is given): none, as a knock stops the turning -- unless the hold
# is leaning, its arm off the middle, and then all of it. The hold gives
# that turning back every tick it leans, so spending it on a turn the
# rounding refused kept a perched cube from ever starting to tip.
# where one coordinate of the middle lands when the body turns about an
# arm: the arm turns with it, so the middle moves by r - M r
def Pivot.c(+c: Nat, +r: Z, +ax: Z, +ay: Z, +az: Z, +rx: Z, +ry: Z, +rz: Z) -> Nat:
  Z.shift(c, Z.sub(r, Z.divn(Z.divn(V3.dot(ax, ay, az, rx, ry, rz), 256n), 256n)))

# The turn about a contact: the middle swings round the arm to it, which
# is where it goes sideways. How high it ends up is not worked out from
# the arm -- a turned cube's numbers are rounded, and a unit of rounding
# into what holds it would refuse every small turn, so a cube could never
# begin to tip. It is let down onto what holds it instead, from no higher
# than it was, and comes to rest the gap above it (Geo.gap), as a landing
# does.
def Tick.pivot(m: Mat, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, +rx: Z, +ry: Z, +rz: Z) -> Body:
  Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = Pivot.c(x, rx, axx, ayx, azx, rx, ry, rz)
  +ny = Pivot.c(y, ry, axy, ayy, azy, rx, ry, rz)
  +nz = Pivot.c(z, rz, axz, ayz, azz, rx, ry, rz)
  +d = Tick.drop(s, obs, nx, y, nz, Rot.q(r2), Nat.add(Nat.sub(y, Pick.low(ny, y)), Nat.div(s, 256n)))
  Tick.place(s, g, obs, x, y, z, nx, Nat.sub(y, d), nz, vx, vy, vz, gr, hit, rt, r2)

# The least turn a held body takes in a tick, when what holds it is well
# off its middle: a fiftieth of a radian. A cube resting square on
# another touches it exactly, and a turned cube is judged by the fifteen
# axes with a hair of room around it; a turn too small to lift the body
# off that hair is refused, the turning it had is spent, and the next
# tick's is as small again -- so a cube hanging off an edge never began
# to tip. Held off its middle by more than three centimetres, it takes its
# turn at least this big, which clears the hair at once.
def Tick.least() -> Nat:
  13671000n

def Z.stretch(v: Z, +m: Nat, +t: Nat) -> Z:
  match v:
    case Pos{+n}:
      Pos{Nat.div(Nat.mul(n, t), Pick.high(m, 1n))}
    case Neg{+n}:
      Neg{Nat.div(Nat.mul(n, t), Pick.high(m, 1n))}

def Wv.stretch(w: Wv, +m: Nat, +t: Nat) -> Wv:
  Wv{+a, +b, +c} = w
  Wv{Z.stretch(a, m, t), Z.stretch(b, m, t), Z.stretch(c, m, t)}

# half of v, toward 0
def Z.half(v: Z) -> Z:
  match v:
    case Pos{+n}:
      Pos{Nat.div(n, 2n)}
    case Neg{+n}:
      Neg{Nat.div(n, 2n)}

def Wv.half(w: Wv) -> Wv:
  Wv{+a, +b, +c} = w
  Wv{Z.half(a), Z.half(b), Z.half(c)}

def Tick.boost2(small: Bool, +w: Wv, +m: Nat) -> Wv:
  match small:
    case True{}:
      Wv.stretch(w, m, Tick.least())
    case False{}:
      w

def Tick.boost(big: Bool, +w: Wv) -> Wv:
  match big:
    case True{}:
      Tick.boost2(Nat.is_lt(Wv.mag(w), Tick.least()), w, Wv.mag(w))
    case False{}:
      w

# the turn about the point (rx, ry, rz) by the turning w, the body it
# leaves: the one Tick.place lets through, or the one it keeps
def Tick.cand(+s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +w: Wv, +rx: Z, +ry: Z, +rz: Z) -> Body:
  Tick.pivot(Rot.mat(Quat.half(Quat.step(w, Wv.mag(w)))), s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt,
    Rot{Rot.turn(Rot.q(rt), w), Rot.w(rt)}, rx, ry, rz)

# did the turn go through? Then the body is turned another way
def Tick.moved(b: Body, rt: Rot) -> Bool:
  Bool.not(Quat.same(Rot.q(Body.rot(b)), Rot.q(rt)))

# The biggest turn that fits: the turn asked for, and if the gate refuses
# it, half of it, and half of that, down to a hundred and twenty-eighth. A
# cube that lands a little off square, or stands on a corner with the
# rest of it a little above the floor, can only turn as far as the next
# edge it meets; refusing the whole turn left it standing on the corner
# for good. Every candidate goes through the same gate (Tick.place), so
# nothing a candidate does is trusted: b is the body the last one left,
# ok whether it went through.
def Tick.shrink(n: Nat, ok: Bool, +b: Body, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat,
  +vx: Z, +vy: Z, +vz: Z, +gr: Bool, +hit: Bool, +rt: Rot, +w: Wv, +rx: Z, +ry: Z, +rz: Z) -> Body:
  match n ok:
    case _ True{}:
      b
    case 0n False{}:
      b
    case 1n+m False{}:
      +nb = Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, Wv.half(w), rx, ry, rz)
      Tick.shrink(m, Tick.moved(nb, rt), nb, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, Wv.half(w), rx, ry, rz)

# the turn about the point a: the turning the body carries, taken at
# least at the size above when a is far off its middle
def Body.setrot(+b: Body, r: Rot) -> Body:
  Body{Body.x(b), Body.y(b), Body.z(b), Body.vx(b), Body.vy(b), Body.vz(b), Body.ground(b), Body.hit(b), r}

def Pick.w(c: Bool, a: Wv, b: Wv) -> Wv:
  match c:
    case True{}:
      a
    case False{}:
      b

# The turning a refused turn leaves the body with, given whole: unlike
# Tick.put (which only ever zeroes it, one candidate at a time), this asks
# once, after the search over candidates is done, whether the ORIENTATION
# moved at all. A search that moved keeps exactly what Tick.put already
# gave it (the candidate's own turning, r2's, carried through untouched);
# one that never moved -- every candidate refused -- gets its turning
# back only where the hold leans (tip); square, it is spent, as it always
# was. Asking this once outside the search, instead of inside every
# candidate Tick.pivot tries, is what a proof about the search can afford:
# Body.setrot never opens what it does not touch, so this costs nothing to
# carry through a fact about hit, energy or the floor -- only a fact about
# the turning itself has to look inside.
def Body.spin(tip: Bool, moved: Bool, +b: Body, +rt: Rot) -> Body:
  match moved:
    case True{}:
      b
    case False{}:
      Body.setrot(b, Rot{Rot.q(Body.rot(b)), Pick.w(tip, Rot.w(rt), Wv.zero())})

def Tick.pivota0(md: Mat, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, a: Wv) -> Body:
  Wv{+ax, +ay, +az} = a
  +w2 = Tick.boost(Nat.is_le(Nat.div(s, 32n), Nat.add(Z.mag(ax), Z.mag(az))), Rot.w(rt))
  +b0 = Tick.cand(s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az)
  +bf = Tick.shrink(7n, Tick.moved(b0, rt), b0, s, g, obs, x, y, z, vx, vy, vz, gr, hit, rt, w2, ax, ay, az)
  Body.spin(Nat.is_lt(0n, Nat.add(Z.mag(ax), Z.mag(az))), Tick.moved(bf, rt), bf, rt)

# The same turn, written out once for each shape the obstacles can have,
# like Tick.turn and Tick.drop: for the checker and not for the machine.
# The arm a is often a value the checker can open (Hold.low builds its
# arm out of the matrix without asking anything of it), and opened, the
# whole turn -- the boost, the matrix, the search for the contact -- lands
# in every proof that only carries the turn around. Asked this way it
# stays folded until the obstacles are known.
def Tick.pivota(md: Mat, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, a: Wv) -> Body:
  match obs:
    case []:
      Tick.pivota0(md, s, g, [], x, y, z, vx, vy, vz, gr, hit, rt, r2, a)
    case o <> rest:
      Tick.pivota0(md, s, g, o <> rest, x, y, z, vx, vy, vz, gr, hit, rt, r2, a)

# Turning about a contact is a knock: the cube is leaning on something,
# and that is what hit says. Marking it is not bookkeeping -- it is what
# lets every law that speaks of a tick without a knock go on speaking of
# a body that neither walked nor was turned about anything. The point it
# turns about is the very point the hold pressed on (Rot.held).
def Tick.turn2(held: Bool, floor: Bool, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z,
  +vz: Z, +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, +md: Mat) -> Body:
  match held floor:
    case False{} _:
      Tick.place(s, g, obs, x, y, z, x, y, z, vx, vy, vz, gr, hit, Rot{Rot.q(rt), Wv.zero()}, r2)
    case True{} False{}:
      Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2,
        Hold.arm(Geo.foot(s, x, y, z, Rot.q(rt), obs, Foot.none()), Rot.mat(Rot.q(rt)), s))
    case True{} True{}:
      Tick.pivota(md, s, g, obs, x, y, z, vx, vy, vz, gr, True{}, rt, r2, Hold.low(Rot.mat(Rot.q(rt)), s))

# The turn takes the body whole and only opens it once it knows there is
# a turn to take. A body the checker cannot work out is copied once per
# field when it is opened, and the turn sits on top of a whole tick.
def Tick.turn1b(+s: Nat, +g: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  Tick.turn2(gr, Geo.onfloor(s, y, Rot.q(rt)), s, g, obs, x, y, z, vx, vy,
    vz, gr, hit, rt, Rot.free(rt),
    Rot.mat(Quat.half(Quat.step(Rot.w(rt), Wv.mag(Rot.w(rt))))))

def Tick.turn1(still: Bool, +s: Nat, +g: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  match still:
    case True{}:
      b
    case False{}:
      Tick.turn1b(s, g, obs, b)

def Tick.turn0(+s: Nat, +g: Nat, +obs: List<&2, Body>, +b: Body) -> Body:
  Tick.turn1(Wv.null(Rot.w(Body.rot(b))), s, g, obs, b)

# The same turn, written out once for each shape the obstacles can have.
# That is for the checker and not for the machine: asked this way the turn
# cannot be unfolded until the obstacles are known, and the whole geometry
# behind it -- the fit, the sag, the matrices -- stays folded up with it.
def Tick.turn(+s: Nat, +g: Nat, +obs: List<&2, Body>, +b: Body) -> Body:
  match obs:
    case []:
      Tick.turn0(s, g, [], b)
    case o <> rest:
      Tick.turn0(s, g, o <> rest, b)

def Tick.body(r: Body & List<&2, Body>) -> Body:
  (b, obs) = r
  b

def Tick.obs(r: Body & List<&2, Body>) -> List<&2, Body>:
  (b, obs) = r
  obs

def Tick.spin(+s: Nat, +g: Nat, r: Body & List<&2, Body>) -> Body & List<&2, Body>:
  (b, +obs) = r
  (Tick.turn(s, g, obs, b), obs)

# the tick without the turning: the drive, the push along x, the push
# along z and the fall. A tick is this and then the turn.
def Body.step1(+k: K, obs: List<&2, Body>, inp: In, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  Tick.z(K.size(k), K.g(k), vz, Move.x(K.size(k), obs, vx, Body.drive(k, inp, Body{x, y, z, vx, vy, vz, gr, hit, rt})))

# The same, written out once for each shape the obstacles can have. That
# is for the checker and not for the machine: a tick is four steps, each
# handing the next a pair it cannot work out, and taking such a pair
# apart copies what is inside it. Four steps deep that is sixteen copies
# of the whole tick, and a law that names the tick twice never finishes.
# Asked this way the step cannot be unfolded until the obstacles are
# known, so the checker carries it whole instead of walking it out.
def Body.step(+k: K, obs: List<&2, Body>, inp: In, b: Body) -> Body & List<&2, Body>:
  Body.step1(k, obs, inp, b)

def Body.tick(+k: K, +obs: List<&2, Body>, inp: In, b: Body) -> Body & List<&2, Body>:
  Tick.spin(K.size(k), K.g(k), Body.step(k, obs, inp, b))

# the same body, turned another way: what a tick without a knock does to
# a cube, and nothing else
def Share.fst(r: Z & Z) -> Z:
  (a, b) = r
  a

def Share.snd(r: Z & Z) -> Z:
  (a, b) = r
  b

# Flights
# -------
# A flight: ticks of a body left alone, one per set of obstacles around it
# (the world changes between ticks), and whether every one of them starts
# in the air and touches nothing. LAWS.flight_is_parabola is about them.

def Flight.run(+k: K, obss: List<&2, List<&2, Body>>, b: Body) -> Body:
  match obss:
    case []:
      b
    case obs <> rest:
      Flight.run(k, rest, Tick.body(Body.tick(k, obs, In.idle(), b)))

def Flight.clear(+k: K, obss: List<&2, List<&2, Body>>, +b: Body) -> Bool:
  match obss:
    case []:
      True{}
    case obs <> rest:
      +b2 = Tick.body(Body.tick(k, obs, In.idle(), b))
      Bool.and(Bool.and(Bool.not(Body.ground(b)), Bool.not(Body.hit(b2))), Flight.clear(k, rest, b2))

