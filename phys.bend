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
  Trig.dv(Nat.mul(Nat.sub(Nat.max(p, q), q), 65536n), 1048576n)

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
  Nat.mul(256n, Fric.floor(n, Nat.max(Nat.add(Nat.add(a, b), c), 1n)))

# one part of the turn of a tick: sin(half the angle) along the axis the
# body turns on, in 2^-16
def Quat.part(+s: Z, +v: Z, +m: Nat) -> Z:
  Z.like(v, Nat.div(Nat.mul(Z.mag(s), Z.mag(v)), Nat.max(m, 1n)))

# the turn of one tick as a quaternion in 2^-16: half the angle, about the
# axis of the turning itself
def Quat.step(+w: Wv, +m: Nat) -> Quat:
  +h = U32.from_nat(Nat.div(m, 2n))
  Quat{Trig.cos(h), Quat.part(Trig.sin(h), Wv.x(w), m), Quat.part(Trig.sin(h), Wv.y(w), m),
    Quat.part(Trig.sin(h), Wv.z(w), m)}

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
  Fric.floor(n, Nat.max(Nat.add(Nat.add(Z.mag(Quat.a(q)), Z.mag(Quat.b(q))),
    Nat.add(Z.mag(Quat.c(q)), Z.mag(Quat.d(q)))), 1n))

def Quat.scale(+v: Z, +m: Nat) -> Z:
  Z.like(v, Nat.div(Nat.mul(Z.mag(v), 32768n), Nat.max(m, 1n)))

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

# the mechanical energy, kinetic plus potential: vx^2 + vy^2 + vz^2 + g y
def Body.energy(+g: Nat, b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit, +rt} = b
  Nat.add(Nat.add(Nat.add(Z.sq(vx), Z.sq(vy)), Z.sq(vz)), Nat.mul(g, y))

def Body.energies(+g: Nat, bs: List<&2, Body>) -> Nat:
  match bs:
    case []:
      0n
    case b <> rest:
      Nat.add(Body.energy(g, b), Body.energies(g, rest))

# Boxes
# -----
# A body's box is [x, x + S) by [y, y + S) by [z, z + S).

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

# 1 - 2(p + q), in 2^-12, out of squares in 2^-30
def Mat.diag(+p: Nat, +q: Nat) -> Z:
  +t = Nat.mul(2n, Nat.add(p, q))
  Z.divn(Z.diff(Nat.is_lt(1073741824n, t), 1073741824n, t), 262144n)

# 2(u v - p q), the same way
def Mat.off(+u: Z, +v: Z, +p: Z, +q: Z) -> Z:
  Z.divn(Z.mul(Pos{2n}, Z.sub(Z.mul(u, v), Z.mul(p, q))), 262144n)

# the cube's own three axes, as they lie in the world, one to a row
def Rot.mat(+q: Quat) -> Mat:
  Mat{Mat.diag(Z.sq(Quat.c(q)), Z.sq(Quat.d(q))),
    Mat.off(Quat.b(q), Quat.c(q), Z.opp(Quat.a(q)), Quat.d(q)),
    Mat.off(Quat.b(q), Quat.d(q), Quat.a(q), Quat.c(q)),
    Mat.off(Quat.b(q), Quat.c(q), Quat.a(q), Quat.d(q)),
    Mat.diag(Z.sq(Quat.b(q)), Z.sq(Quat.d(q))),
    Mat.off(Quat.c(q), Quat.d(q), Z.opp(Quat.a(q)), Quat.b(q)),
    Mat.off(Quat.b(q), Quat.d(q), Z.opp(Quat.a(q)), Quat.c(q)),
    Mat.off(Quat.c(q), Quat.d(q), Quat.a(q), Quat.b(q)),
    Mat.diag(Z.sq(Quat.b(q)), Z.sq(Quat.c(q)))}

def V3.dot(+ax: Z, +ay: Z, +az: Z, +bx: Z, +by: Z, +bz: Z) -> Z:
  Z.add(Z.add(Z.mul(ax, bx), Z.mul(ay, by)), Z.mul(az, bz))

# apart along one of the first cube's own axes?
def Sat.a(+t: Z, +h: Nat, +r0: Z, +r1: Z, +r2: Z) -> Bool:
  Nat.is_le(Nat.mul(h, Nat.add(4096n, Nat.add(Nat.add(Z.mag(r0), Z.mag(r1)), Z.mag(r2)))),
    Nat.mul(Z.mag(t), 4096n))

# apart along one of the second cube's?
def Sat.b(+t0: Z, +t1: Z, +t2: Z, +r0: Z, +r1: Z, +r2: Z, +h: Nat) -> Bool:
  Nat.is_le(Nat.mul(h, Nat.add(4096n, Nat.add(Nat.add(Z.mag(r0), Z.mag(r1)), Z.mag(r2)))),
    Z.mag(V3.dot(t0, t1, t2, r0, r1, r2)))

# apart along the crossing of an edge of each. When the two edges are
# parallel the crossing is nothing at all, and a direction of nothing
# would say "apart" about every pair of cubes: the one added to each side
# below keeps that from happening, and costs a twentieth of a millimetre
# of room on the crossings that do mean something.
def Sat.x(+t1: Z, +t2: Z, +a1: Z, +a2: Z, +b1: Z, +b2: Z, +h: Nat) -> Bool:
  Nat.is_le(Nat.mul(h, Nat.add(Nat.add(Nat.add(Z.mag(a1), 1n), Nat.add(Z.mag(a2), 1n)),
      Nat.add(Nat.add(Z.mag(b1), 1n), Nat.add(Z.mag(b2), 1n)))),
    Z.mag(Z.sub(Z.mul(t2, a1), Z.mul(t1, a2))))

def Sat.some(+p: Bool, +q: Bool, +r: Bool) -> Bool:
  Bool.or(p, Bool.or(q, r))

# the fifteen tests, with the two cubes' axes already worked out. The
# shadows are compared multiplied out, and apart counts from the moment
# they merely touch -- so two cubes side by side, edge against edge, are
# as free as they have always been.
def Geo.sat2(+h: Nat, +tx: Z, +ty: Z, +tz: Z, ma: Mat, mb: Mat) -> Bool:
  Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = ma
  Mat{+bxx, +bxy, +bxz, +byx, +byy, +byz, +bzx, +bzy, +bzz} = mb
  +t0 = Z.divn(V3.dot(tx, ty, tz, axx, axy, axz), 4096n)
  +t1 = Z.divn(V3.dot(tx, ty, tz, ayx, ayy, ayz), 4096n)
  +t2 = Z.divn(V3.dot(tx, ty, tz, azx, azy, azz), 4096n)
  +r00 = Z.divn(V3.dot(axx, axy, axz, bxx, bxy, bxz), 4096n)
  +r01 = Z.divn(V3.dot(axx, axy, axz, byx, byy, byz), 4096n)
  +r02 = Z.divn(V3.dot(axx, axy, axz, bzx, bzy, bzz), 4096n)
  +r10 = Z.divn(V3.dot(ayx, ayy, ayz, bxx, bxy, bxz), 4096n)
  +r11 = Z.divn(V3.dot(ayx, ayy, ayz, byx, byy, byz), 4096n)
  +r12 = Z.divn(V3.dot(ayx, ayy, ayz, bzx, bzy, bzz), 4096n)
  +r20 = Z.divn(V3.dot(azx, azy, azz, bxx, bxy, bxz), 4096n)
  +r21 = Z.divn(V3.dot(azx, azy, azz, byx, byy, byz), 4096n)
  +r22 = Z.divn(V3.dot(azx, azy, azz, bzx, bzy, bzz), 4096n)
  Bool.not(Bool.or(Bool.or(
    Sat.some(Sat.a(t0, h, r00, r01, r02), Sat.a(t1, h, r10, r11, r12), Sat.a(t2, h, r20, r21, r22)),
    Sat.some(Sat.b(t0, t1, t2, r00, r10, r20, h), Sat.b(t0, t1, t2, r01, r11, r21, h),
      Sat.b(t0, t1, t2, r02, r12, r22, h))),
    Bool.or(Bool.or(
      Sat.some(Sat.x(t1, t2, r10, r20, r02, r01, h), Sat.x(t1, t2, r11, r21, r02, r00, h),
        Sat.x(t1, t2, r12, r22, r01, r00, h)),
      Sat.some(Sat.x(t2, t0, r20, r00, r12, r11, h), Sat.x(t2, t0, r21, r01, r12, r10, h),
        Sat.x(t2, t0, r22, r02, r11, r10, h))),
      Sat.some(Sat.x(t0, t1, r00, r10, r22, r21, h), Sat.x(t0, t1, r01, r11, r22, r20, h),
        Sat.x(t0, t1, r02, r12, r21, r20, h)))))

# do the cube at (ax, ay, az) turned by qa and the one at (bx, by, bz)
# turned by qb touch?
def Geo.sat(+s: Nat, +ax: Nat, +ay: Nat, +az: Nat, +qa: Quat, +bx: Nat, +by: Nat, +bz: Nat,
  +qb: Quat) -> Bool:
  Geo.sat2(Nat.div(s, 2n), Z.diff(Nat.is_lt(bx, ax), bx, ax), Z.diff(Nat.is_lt(by, ay), by, ay),
    Z.diff(Nat.is_lt(bz, az), bz, az), Rot.mat(qa), Rot.mat(qb))

# do the box at (x, y, z), turned by qa, and o's box overlap? While
# neither has turned this is the plain box test, to the unit; the moment
# one of them has, the fifteen directions decide.
def Geo.pair(flat: Bool, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +qa: Quat, +ox: Nat, +oy: Nat, +oz: Nat,
  +qb: Quat) -> Bool:
  match flat:
    case True{}:
      Bool.and(Geo.ovl(s, x, ox), Bool.and(Geo.ovl(s, z, oz), Geo.ovl(s, y, oy)))
    case False{}:
      Geo.sat(s, x, y, z, qa, ox, oy, oz, qb)

def Geo.meets(+s: Nat, +x: Nat, +y: Nat, +z: Nat, +qa: Quat, o: Body) -> Bool:
  Body{+ox, +oy, +oz, vx, vy, vz, ground, hit, +rt} = o
  Geo.pair(Bool.and(Quat.flat(qa), Quat.flat(Rot.q(rt))), s, x, y, z, qa, ox, oy, oz, Rot.q(rt))

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
  +t = Nat.div(Nat.mul(h, Nat.add(Nat.add(Z.mag(axy), Z.mag(ayy)), Z.mag(azy))), 4096n)
  Nat.sub(Nat.max(t, h), h)

def Geo.sag(+s: Nat, +q: Quat) -> Nat:
  Geo.sag2(s, Rot.mat(q))

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
  +lo = Nat.max(a, b)
  +hi = Nat.min(Nat.add(a, s), Nat.add(b, s))
  Nat.sub(Nat.max(hi, lo), lo)

# where a run of s from b starts and ends inside a run of s from a, in
# steps from a's own start. The world lies far from zero -- a place is
# nearly a whole word -- so nothing here ever adds two places together.
def Geo.lapl(+s: Nat, +a: Nat, +b: Nat) -> Nat:
  Nat.sub(Nat.max(a, b), a)

def Geo.laph(+s: Nat, +a: Nat, +b: Nat) -> Nat:
  Nat.sub(Nat.max(Nat.min(Nat.add(a, s), Nat.add(b, s)), a), a)

# What holds the body up: the highest top under its middle, and how far
# that top reaches sideways. The press of the hold lands on that top,
# right under the middle while the middle is over it -- nothing to turn
# the body -- and at the edge of it the moment the middle goes past,
# which is what tips a cube over a ledge.
def Geo.foot2(on: Bool, up: Bool, +s: Nat, +x: Nat, +z: Nat, +ox: Nat, +oz: Nat, +top: Nat,
  +f: Foot) -> Foot:
  match on up:
    case False{} _:
      f
    case True{} True{}:
      Foot{1n, Geo.lapl(s, x, ox), Geo.laph(s, x, ox), Geo.lapl(s, z, oz), Geo.laph(s, z, oz), top}
    case True{} False{}:
      Foot{Nat.add(Foot.n(f), 1n), Nat.min(Foot.lx(f), Geo.lapl(s, x, ox)),
        Nat.max(Foot.hx(f), Geo.laph(s, x, ox)), Nat.min(Foot.lz(f), Geo.lapl(s, z, oz)),
        Nat.max(Foot.hz(f), Geo.laph(s, z, oz)), Foot.ty(f)}

def Geo.foot1(+s: Nat, +x: Nat, +y: Nat, +z: Nat, o: Body, +f: Foot) -> Foot:
  Body{+ox, +oy, +oz, vx, vy, vz, ground, hit, +rt} = o
  +top = Geo.top(s, oy, rt)
  +under = Bool.and(Nat.is_le(top, Nat.add(y, Nat.div(s, 2n))),
    Bool.and(Nat.is_lt(0n, Geo.lap(s, x, ox)), Nat.is_lt(0n, Geo.lap(s, z, oz))))
  Geo.foot2(Bool.and(under, Bool.or(Nat.is_eq(Foot.n(f), 0n), Nat.is_le(Foot.ty(f), top))),
    Bool.or(Nat.is_eq(Foot.n(f), 0n), Nat.is_lt(Foot.ty(f), top)), s, x, z, ox, oz, top, f)

def Geo.foot(+s: Nat, +x: Nat, +y: Nat, +z: Nat, obs: List<&2, Body>, f: Foot) -> Foot:
  match obs:
    case []:
      f
    case o <> rest:
      Geo.foot(s, x, y, z, rest, Geo.foot1(s, x, y, z, o, f))

# is anything holding the body up right now? A cube square with the world
# rests when a top meets its base exactly; a turned cube rests when it
# cannot go down by two millimetres -- the same thing, and it still says
# it while a cube is going over an edge, when its base is no longer level
# with anything. The two millimetres are the room the turn itself takes:
# a turn about a contact lands on whole numbers, and the body is walked
# back out of what it would otherwise be a unit or two inside.
def Geo.held(flat: Bool, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +q: Quat, obs: List<&2, Body>) -> Bool:
  match flat:
    case True{}:
      Bool.or(Nat.is_eq(y, 0n), Geo.rests(s, x, y, z, obs))
    case False{}:
      Bool.or(Nat.is_le(y, Nat.add(Geo.sag(s, q), Nat.div(s, 512n))),
        Bool.not(Geo.free(s, x, Nat.sub(y, Nat.div(s, 512n)), z, q, obs)))

# the middle held down to the hold's reach, as an arm from the middle
def Geo.lean(+c: Nat, +lo: Nat, +hi: Nat) -> Z:
  +p = Nat.max(Nat.min(c, hi), lo)
  Z.diff(Nat.is_lt(p, c), p, c)

# how much harder a cube is to turn about a point an arm away than about
# its middle: (I + m r^2) / I = 1 + 6 r^2 / s^2, counted in eighths so it
# lands on the same division the middle takes
def Rot.about(+s: Nat, +rx: Z, +ry: Z, +rz: Z) -> Nat:
  Nat.add(8n, Nat.div(Nat.mul(48n, Nat.add(Nat.add(Z.sq(rx), Z.sq(ry)), Z.sq(rz))), Nat.mul(s, s)))

def Rot.kickd(+d: Nat, +rx: Z, +ry: Z, +rz: Z, +jx: Z, +jy: Z, +jz: Z) -> Wv:
  Wv{Z.divn(Rot.crx(ry, rz, jy, jz), d), Z.divn(Rot.cry(rz, rx, jz, jx), d),
    Z.divn(Rot.crz(rx, ry, jx, jy), d)}

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

# a hold from below on a cube that has not turned: the press comes up at
# the height of its base, under the middle or at the hold's edge
def Rot.stand(f: Foot, +rt: Rot, +s: Nat, +y: Nat, +j: Nat) -> Rot:
  Foot{+n, +lx, +hx, +lz, +hz, +ty} = f
  Rot.press(rt, s, Geo.lean(Nat.div(s, 2n), lx, hx),
    Z.diff(Nat.is_lt(ty, Nat.add(y, Nat.div(s, 2n))), ty, Nat.add(y, Nat.div(s, 2n))),
    Geo.lean(Nat.div(s, 2n), lz, hz), Pos{0n}, Pos{j}, Pos{0n})

# a hold from below on a cube that has turned: it stands on the one
# corner that lies lowest, and the press comes up through that corner
def Rot.tip(m: Mat, +rt: Rot, +s: Nat, +j: Nat) -> Rot:
  Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +h = Nat.div(s, 2n)
  +sx = Z.sgnop(axy)
  +sy = Z.sgnop(ayy)
  +sz = Z.sgnop(azy)
  Rot.press(rt, s,
    Z.divn(Z.scale(h, Z.add(Z.add(Z.mul(sx, axx), Z.mul(sy, ayx)), Z.mul(sz, azx))), 4096n),
    Z.divn(Z.scale(h, Z.add(Z.add(Z.mul(sx, axy), Z.mul(sy, ayy)), Z.mul(sz, azy))), 4096n),
    Z.divn(Z.scale(h, Z.add(Z.add(Z.mul(sx, axz), Z.mul(sy, ayz)), Z.mul(sz, azz))), 4096n),
    Pos{0n}, Pos{j}, Pos{0n})

# the hold of a tick, whichever kind it is
# the floor holds a turned cube on the one corner that lies lowest; a
# cube holds it where its top reaches, which is what tips a body over a
# ledge -- the press moves out to the ledge as the middle goes past it
def Rot.held(floor: Bool, +rt: Rot, +s: Nat, +x: Nat, +y: Nat, +z: Nat, +j: Nat,
  obs: List<&2, Body>) -> Rot:
  match floor:
    case True{}:
      Rot.tip(Rot.mat(Rot.q(rt)), rt, s, j)
    case False{}:
      Rot.stand(Geo.foot(s, x, y, z, obs, Foot.none()), rt, s, y, j)

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
  +t = Nat.min(a, Nat.div(Nat.mul(f, a), s))
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

def Move.xat(+s: Nat, at: Maybe<&2, Nat>, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +v: Z, +vy: Z, +vz: Z, +gr: Bool, +rt: Rot)
  -> Body & List<&2, Body>:
  match at:
    case None{}:
      (Body{x, y, z, v, vy, vz, gr, True{}, rt}, obs)
    case Some{+cx}:
      Move.xput(Geo.free(s, cx, y, z, Rot.q(rt), obs), obs, cx, x, y, z, v, vy, vz, gr, rt)

def Move.xhit(+s: Nat, r: Pushed, +x: Nat, +y: Nat, +z: Nat, +vy: Z, +vz: Z, +gr: Bool, +rt: Rot) -> Body & List<&2, Body>:
  Pushed{v, obs, at} = r
  Move.xat(s, at, obs, x, y, z, v, vy, vz, gr, rt)

def Move.xgo(+s: Nat, ok: Bool, +obs: List<&2, Body>, +d: Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot) -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{cx, y, z, vx, vy, vz, gr, hit, rt}, obs)
    case False{}:
      Move.xhit(s, Push.x(s, obs, d, cx, y, z, vx, Rot.q(rt), Geo.head(s, cx, y, z, Rot.q(rt), obs)), x, y, z, vy, vz, gr, rt)

# the move along x, by the start and end velocities added
def Move.x(+s: Nat, +obs: List<&2, Body>, +v0: Z, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  +d = Z.add(v0, vx)
  +cx = Z.shift(x, d)
  Move.xgo(s, Bool.and(Z.fits(x, d), Geo.free(s, cx, y, z, Rot.q(rt), obs)), obs, d, cx, x, y, z, vx, vy, vz, gr, hit, rt)

def Move.zput(ok: Bool, +obs: List<&2, Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +v: Z, +gr: Bool, +rt: Rot)
  -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{x, y, cz, vx, vy, v, gr, True{}, rt}, obs)
    case False{}:
      (Body{x, y, z, vx, vy, v, gr, True{}, rt}, obs)

def Move.zat(+s: Nat, at: Maybe<&2, Nat>, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +v: Z, +gr: Bool, +rt: Rot)
  -> Body & List<&2, Body>:
  match at:
    case None{}:
      (Body{x, y, z, vx, vy, v, gr, True{}, rt}, obs)
    case Some{+cz}:
      Move.zput(Geo.free(s, x, y, cz, Rot.q(rt), obs), obs, cz, x, y, z, vx, vy, v, gr, rt)

def Move.zhit(+s: Nat, r: Pushed, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +gr: Bool, +rt: Rot) -> Body & List<&2, Body>:
  Pushed{v, obs, at} = r
  Move.zat(s, at, obs, x, y, z, vx, vy, v, gr, rt)

def Move.zgo(+s: Nat, ok: Bool, +obs: List<&2, Body>, +d: Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot) -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{x, y, cz, vx, vy, vz, gr, hit, rt}, obs)
    case False{}:
      Move.zhit(s, Push.z(s, obs, d, x, y, cz, vz, Rot.q(rt), Geo.head(s, x, y, cz, Rot.q(rt), obs)), x, y, z, vx, vy, gr, rt)

def Move.z(+s: Nat, +obs: List<&2, Body>, +v0: Z, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  +d = Z.add(v0, vz)
  +cz = Z.shift(z, d)
  Move.zgo(s, Bool.and(Z.fits(z, d), Geo.free(s, x, y, cz, Rot.q(rt), obs)), obs, d, cz, x, y, z, vx, vy, vz, gr, hit, rt)

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

def Move.land(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +fl: Nat, +vx: Z, +vz: Z, +rt: Rot) -> Body:
  match ok:
    case True{}:
      Body{x, fl, z, vx, Pos{0n}, vz, True{}, True{}, rt}
    case False{}:
      Body{x, y, z, vx, Pos{0n}, vz, False{}, True{}, rt}

def Move.fall(+s: Nat, ok: Bool, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +fl: Nat, +vx: Z, +v: Z, +vz: Z,
  +hit: Bool, +rt: Rot) -> Body:
  match ok:
    case True{}:
      Body{x, Nat.sub(y, q), z, vx, v, vz, False{}, hit, rt}
    case False{}:
      Move.land(Bool.and(Nat.is_le(Nat.add(fl, Geo.sag(s, Rot.q(rt))), y),
        Geo.free(s, x, Nat.add(fl, Geo.sag(s, Rot.q(rt))), z, Rot.q(rt), obs)), x, y, z,
        Nat.add(fl, Geo.sag(s, Rot.q(rt))), vx, vz, rt)

def Move.fly(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vz: Z, +hit: Bool, st: Z & Z, +rt: Rot) -> Body:
  (v, d) = st
  match d:
    case Pos{+p}:
      Move.rise(Geo.free(s, x, Nat.add(y, p), z, Rot.q(rt), obs), x, y, z, p, vx, v, vz, hit, rt)
    case Neg{+q}:
      +fl = Geo.floor(s, x, y, z, obs, 0n)
      Move.fall(s, Bool.and(Nat.is_le(Nat.add(fl, q), y), Geo.free(s, x, Nat.sub(y, q), z, Rot.q(rt), obs)), obs, x, y, z, q, fl,
        vx, v, vz, hit, rt)

# a body that is held up is pressed up by what holds it, every tick, by
# just what gravity would have taken: that press is what keeps it there,
# and where the press lands is what turns it
def Move.stay(rest: Bool, +s: Nat, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z,
  +vz: Z, +hit: Bool, +rt: Rot) -> Body:
  match rest:
    case True{}:
      Body{x, y, z, vx, vy, vz, True{}, hit,
        Rot.held(Nat.is_le(y, Nat.add(Geo.sag(s, Rot.q(rt)), Nat.div(s, 512n))), rt, s, x, y, z, g, obs)}
    case False{}:
      Body{x, y, z, vx, vy, vz, False{}, hit, rt}

def Move.ygo(+s: Nat, gr: Bool, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +hit: Bool, +rt: Rot) -> Body:
  match gr:
    case True{}:
      Move.stay(Geo.held(Quat.flat(Rot.q(rt)), s, x, y, z, Rot.q(rt), obs), s, g, obs, x, y, z, vx, vy, vz, hit, rt)
    case False{}:
      Move.fly(s, obs, x, y, z, vx, vz, hit, Fly.step(g, vy), rt)

# the vertical move: standing, whether still on something; else a tick of
# gravity, a free fall or rise, or a landing (on the highest top under the
# body, the ground at 0) or a bump
def Move.y(+s: Nat, +g: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit, +rt} = b
  Move.ygo(s, gr, g, obs, x, y, z, vx, vy, vz, hit, rt)

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
# held turns about what holds it: its middle swings round the contact,
# which is how a cube goes over an edge -- the middle rises as the cube
# tips, exactly as it does when a real cube goes over. Either way the
# turn is taken only where it leaves the body clear of everything: a cube
# can no more turn into a neighbour than walk into one. A turn that does
# not fit is a turn the contact stopped, and the turning stops with it.

def Tick.put(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +nx: Nat, +ny: Nat, +nz: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot) -> Body:
  match ok:
    case True{}:
      Body{nx, ny, nz, vx, vy, vz, gr, hit, r2}
    case False{}:
      Body{x, y, z, vx, vy, vz, gr, hit, Rot{Rot.q(rt), Wv.zero()}}

# A turn about a contact keeps the contact still, but the numbers are
# whole: the body can end up a unit or two into what holds it. This
# walks it back out, a little at a time and never more than a millimetre,
# and every step is tested like any other move.
def Tick.up(n: Nat, ok: Bool, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Quat,
  +d: Nat) -> Nat:
  match n ok:
    case 0n _:
      d
    case _ True{}:
      d
    case 1n+m False{}:
      Tick.up(m, Geo.free(s, x, Nat.add(y, Nat.add(Nat.mul(d, 4n), 1n)), z, q, obs), s, obs, x, y, z, q,
        Nat.add(Nat.mul(d, 4n), 1n))

# where the middle goes when the body turns about a contact an arm away:
# the arm turns with it, so the middle moves by r - M r
def Tick.pivot(m: Mat, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, +rx: Z, +ry: Z, +rz: Z) -> Body:
  Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +nx = Z.shift(x, Z.sub(rx, Z.divn(V3.dot(axx, ayx, azx, rx, ry, rz), 4096n)))
  +ny = Z.shift(y, Z.sub(ry, Z.divn(V3.dot(axy, ayy, azy, rx, ry, rz), 4096n)))
  +nz = Z.shift(z, Z.sub(rz, Z.divn(V3.dot(axz, ayz, azz, rx, ry, rz), 4096n)))
  +uy = Nat.add(ny, Tick.up(6n, Geo.free(s, nx, ny, nz, Rot.q(r2), obs), s, obs, nx, ny, nz, Rot.q(r2), 0n))
  Tick.put(Geo.free(s, x, y, z, Rot.q(r2), obs), x, y, z, x, y, z, vx, vy, vz, gr, hit, rt, r2)

# the arm from the middle of a turned cube to the corner it stands on
def Tick.tipv(m: Mat, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, md: Mat) -> Body:
  Mat{+axx, +axy, +axz, +ayx, +ayy, +ayz, +azx, +azy, +azz} = m
  +h = Nat.div(s, 2n)
  +sx = Z.sgnop(axy)
  +sy = Z.sgnop(ayy)
  +sz = Z.sgnop(azy)
  Tick.pivot(md, s, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2,
    Z.divn(Z.scale(h, Z.add(Z.add(Z.mul(sx, axx), Z.mul(sy, ayx)), Z.mul(sz, azx))), 4096n),
    Z.divn(Z.scale(h, Z.add(Z.add(Z.mul(sx, axy), Z.mul(sy, ayy)), Z.mul(sz, azy))), 4096n),
    Z.divn(Z.scale(h, Z.add(Z.add(Z.mul(sx, axz), Z.mul(sy, ayz)), Z.mul(sz, azz))), 4096n))

# the arm from the middle of a cube that has not turned to the middle of
# what holds it up
def Tick.footv(f: Foot, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, md: Mat) -> Body:
  Foot{+n, +lx, +hx, +lz, +hz, +ty} = f
  Tick.pivot(md, s, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, Geo.lean(Nat.div(s, 2n), lx, hx),
    Z.diff(Nat.is_lt(ty, Nat.add(y, Nat.div(s, 2n))), ty, Nat.add(y, Nat.div(s, 2n))),
    Geo.lean(Nat.div(s, 2n), lz, hz))

def Tick.turn2(held: Bool, floor: Bool, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z,
  +vz: Z, +gr: Bool, +hit: Bool, +rt: Rot, +r2: Rot, +md: Mat) -> Body:
  match held floor:
    case False{} _:
      Tick.put(Geo.free(s, x, y, z, Rot.q(r2), obs), x, y, z, x, y, z, vx, vy, vz, gr, hit, rt, r2)
    case True{} False{}:
      Tick.footv(Geo.foot(s, x, y, z, obs, Foot.none()), s, obs, x, y, z, vx, vy, vz,
        gr, hit, rt, r2, md)
    case True{} True{}:
      Tick.tipv(Rot.mat(Rot.q(rt)), s, obs, x, y, z, vx, vy, vz, gr, hit, rt, r2, md)

def Tick.turn1(still: Bool, +s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool, +rt: Rot) -> Body:
  match still:
    case True{}:
      Body{x, y, z, vx, vy, vz, gr, hit, rt}
    case False{}:
      Tick.turn2(gr, Nat.is_le(y, Nat.add(Geo.sag(s, Rot.q(rt)), Nat.div(s, 512n))), s, obs, x, y, z, vx, vy,
        vz, gr, hit, rt, Rot.free(rt),
        Rot.mat(Quat.half(Quat.step(Rot.w(rt), Wv.mag(Rot.w(rt))))))

def Tick.turn(+s: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  Tick.turn1(Wv.null(Rot.w(rt)), s, obs, x, y, z, vx, vy, vz, gr, hit, rt)

def Tick.spin(+s: Nat, r: Body & List<&2, Body>) -> Body & List<&2, Body>:
  (b, +obs) = r
  (Tick.turn(s, obs, b), obs)

def Body.tick(+k: K, +obs: List<&2, Body>, inp: In, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit, +rt} = b
  Tick.spin(K.size(k),
    Tick.z(K.size(k), K.g(k), vz, Move.x(K.size(k), obs, vx, Body.drive(k, inp, Body{x, y, z, vx, vy, vz, gr, hit, rt}))))

def Tick.body(r: Body & List<&2, Body>) -> Body:
  (b, obs) = r
  b

def Tick.obs(r: Body & List<&2, Body>) -> List<&2, Body>:
  (b, obs) = r
  obs

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

