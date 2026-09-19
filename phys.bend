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
# acc, air: the motor's push each tick, on the ground and in the air;
# vmax: the fastest the motor walks.

type K is Data:
  K{g: Nat, mu: Nat, jump: Nat, acc: Nat, air: Nat, vmax: Nat, size: Nat}

def K.g(k: K) -> Nat:
  K{g, mu, jump, acc, air, vmax, size} = k
  g

def K.size(k: K) -> Nat:
  K{g, mu, jump, acc, air, vmax, size} = k
  size

def K.jump(k: K) -> Nat:
  K{g, mu, jump, acc, air, vmax, size} = k
  jump

# Coulomb's friction: the ground takes mu N from the speed, N = m g
def K.fric(k: K) -> Nat:
  K{+g, +mu, jump, acc, air, vmax, size} = k
  Nat.div(Nat.mul(mu, g), 256n)

# Bodies
# ------
# A body: where its lowest corner is, its velocity, whether it stands on
# something (ground), whether its last tick touched anything (hit).

type Body is Data:
  Body{x: Nat, y: Nat, z: Nat, vx: Z, vy: Z, vz: Z, ground: Bool, hit: Bool}

def Body.hit(b: Body) -> Bool:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  hit

def Body.ground(b: Body) -> Bool:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  ground

def Body.x(b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  x

def Body.y(b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  y

def Body.z(b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  z

def Body.vx(b: Body) -> Z:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  vx

def Body.vy(b: Body) -> Z:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  vy

def Body.vz(b: Body) -> Z:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
  vz

# the mechanical energy, kinetic plus potential: vx^2 + vy^2 + vz^2 + g y
def Body.energy(+g: Nat, b: Body) -> Nat:
  Body{x, y, z, vx, vy, vz, ground, hit} = b
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

# does the box at (x, y, z) overlap o's?
def Geo.meets(+s: Nat, +x: Nat, +y: Nat, +z: Nat, o: Body) -> Bool:
  Body{ox, oy, oz, vx, vy, vz, ground, hit} = o
  Bool.and(Geo.ovl(s, x, ox), Bool.and(Geo.ovl(s, z, oz), Geo.ovl(s, y, oy)))

# is the box at (x, y, z) clear of every obstacle?
def Geo.free(+s: Nat, +x: Nat, +y: Nat, +z: Nat, obs: List<&2, Body>) -> Bool:
  match obs:
    case []:
      True{}
    case o <> rest:
      Bool.and(Bool.not(Geo.meets(s, x, y, z, o)), Geo.free(s, x, y, z, rest))

# does the box at (x, y, z) meet the first obstacle of obs?
def Geo.head(+s: Nat, +x: Nat, +y: Nat, +z: Nat, obs: List<&2, Body>) -> Bool:
  match obs:
    case []:
      False{}
    case o <> rest:
      Geo.meets(s, x, y, z, o)

# the top of o, if it is under the column (x, z) at most at height y
def Geo.floor1(+s: Nat, +x: Nat, +y: Nat, +z: Nat, o: Body, +best: Nat) -> Nat:
  Body{+ox, +oy, +oz, vx, vy, vz, ground, hit} = o
  +top = Nat.add(oy, s)
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
      Body{+ox, +oy, +oz, vx, vy, vz, ground, hit} = o
      Bool.or(Bool.and(Bool.and(Geo.ovl(s, x, ox), Geo.ovl(s, z, oz)), Nat.is_eq(Nat.add(oy, s), y)),
        Geo.rests(s, x, y, z, rest))

# Friction
# --------
# On the ground, friction takes up to mu g of speed each tick, against the
# velocity: each component loses its share, F a / s (a its size, s the
# speed), never more than it has. s is the speed rounded up, from Newton's
# square root, checked (s^2 >= a^2 + b^2, s <= a + b; else a + b, which
# always is).

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
# The player walks toward a direction (a vector of size 4096): while its
# speed that way is under vmax, the motor adds acc along it.

type Wish is Data:
  Wish{ux: Z, uz: Z}

type In is Data:
  In{walk: Maybe<&2, Wish>, jump: Bool}

def In.idle() -> In:
  In{None{}, False{}}

def Motor.push(go: Bool, +acc: Nat, ux: Z, uz: Z, vx: Z, vz: Z) -> Z & Z:
  match go:
    case True{}:
      (Z.add(vx, Z.q12(acc, ux)), Z.add(vz, Z.q12(acc, uz)))
    case False{}:
      (vx, vz)

def Motor.go(+acc: Nat, +vmax: Nat, walk: Maybe<&2, Wish>, +vx: Z, +vz: Z) -> Z & Z:
  match walk:
    case None{}:
      (vx, vz)
    case Some{Wish{+ux, +uz}}:
      Motor.push(Z.below(Z.add(Z.mulq(vx, ux), Z.mulq(vz, uz)), vmax), acc, ux, uz, vx, vz)

# Driving
# -------
# The forces of a tick on the velocity: on the ground, friction, the motor
# and the jump (a takeoff at the jump speed); in the air, only the motor,
# weaker (gravity comes with the vertical move, Move.y). The tick starts
# untouched (hit off).

def Drive.leap(jump: Bool, +k: K, +x: Nat, +y: Nat, +z: Nat, v: Z & Z) -> Body:
  match jump:
    case True{}:
      K{g, mu, j, acc, air, vmax, size} = k
      (vx, vz) = v
      Body{x, y, z, vx, Pos{j}, vz, False{}, False{}}
    case False{}:
      (vx, vz) = v
      Body{x, y, z, vx, Pos{0n}, vz, True{}, False{}}

def Drive.ground(+k: K, walk: Maybe<&2, Wish>, jump: Bool, +x: Nat, +y: Nat, +z: Nat, v: Z & Z) -> Body:
  K{g, mu, j, +acc, air, +vmax, size} = k
  (vx, vz) = v
  Drive.leap(jump, k, x, y, z, Motor.go(acc, vmax, walk, vx, vz))

def Drive.air(+x: Nat, +y: Nat, +z: Nat, +vy: Z, v: Z & Z) -> Body:
  (vx, vz) = v
  Body{x, y, z, vx, vy, vz, False{}, False{}}

def Drive.go(gr: Bool, +k: K, walk: Maybe<&2, Wish>, jump: Bool, +x: Nat, +y: Nat, +z: Nat,
  +vx: Z, +vy: Z, +vz: Z) -> Body:
  match gr:
    case True{}:
      Drive.ground(k, walk, jump, x, y, z, Fric.apply(K.fric(k), vx, vz))
    case False{}:
      K{g, mu, j, acc, +air, +vmax, size} = k
      Drive.air(x, y, z, vy, Motor.go(air, vmax, walk, vx, vz))

def Body.drive(+k: K, inp: In, b: Body) -> Body:
  In{walk, jump} = inp
  Body{x, y, z, vx, vy, vz, gr, hit} = b
  Drive.go(gr, k, walk, jump, x, y, z, vx, vy, vz)

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
  rest: List<&2, Body>) -> Pushed:
  (v2, w2) = vw
  Pushed{v2, Body{ox, oy, oz, w2, ovy, ovz, og, oh} <> rest, Some{at}}

def Push.xone(+s: Nat, +d: Z, +v: Z, o: Body, rest: List<&2, Body>) -> Pushed:
  Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh} = o
  Push.xput(Push.share(Push.closing(d, v, ovx), v, ovx), Push.stop(s, d, ox), ox, oy, oz, ovy, ovz, og, oh, rest)

def Push.x(+s: Nat, obs: List<&2, Body>, +d: Z, +cx: Nat, +y: Nat, +z: Nat, +v: Z, here: Bool) -> Pushed:
  match obs here:
    case Nil{} _:
      Pushed{v, [], None{}}
    case o <> rest True{}:
      Push.xone(s, d, v, o, rest)
    case +o <> +rest False{}:
      Push.cons(o, Push.x(s, rest, d, cx, y, z, v, Geo.head(s, cx, y, z, rest)))

def Push.zput(vw: Z & Z, +at: Nat, +ox: Nat, +oy: Nat, +oz: Nat, +ovx: Z, +ovy: Z, +og: Bool, +oh: Bool,
  rest: List<&2, Body>) -> Pushed:
  (v2, w2) = vw
  Pushed{v2, Body{ox, oy, oz, ovx, ovy, w2, og, oh} <> rest, Some{at}}

def Push.zone(+s: Nat, +d: Z, +v: Z, o: Body, rest: List<&2, Body>) -> Pushed:
  Body{+ox, +oy, +oz, +ovx, +ovy, +ovz, +og, +oh} = o
  Push.zput(Push.share(Push.closing(d, v, ovz), v, ovz), Push.stop(s, d, oz), ox, oy, oz, ovx, ovy, og, oh, rest)

def Push.z(+s: Nat, obs: List<&2, Body>, +d: Z, +x: Nat, +y: Nat, +cz: Nat, +v: Z, here: Bool) -> Pushed:
  match obs here:
    case Nil{} _:
      Pushed{v, [], None{}}
    case o <> rest True{}:
      Push.zone(s, d, v, o, rest)
    case +o <> +rest False{}:
      Push.cons(o, Push.z(s, rest, d, x, y, cz, v, Geo.head(s, x, y, cz, rest)))

# Moves
# -----
# Each move is gated: the box goes to its new place only if it is free
# there; blocked, it stops against what it met (if free there) or stays.

def Move.xput(ok: Bool, +obs: List<&2, Body>, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +v: Z, +vy: Z, +vz: Z, +gr: Bool)
  -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{cx, y, z, v, vy, vz, gr, True{}}, obs)
    case False{}:
      (Body{x, y, z, v, vy, vz, gr, True{}}, obs)

def Move.xat(+s: Nat, at: Maybe<&2, Nat>, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +v: Z, +vy: Z, +vz: Z, +gr: Bool)
  -> Body & List<&2, Body>:
  match at:
    case None{}:
      (Body{x, y, z, v, vy, vz, gr, True{}}, obs)
    case Some{+cx}:
      Move.xput(Geo.free(s, cx, y, z, obs), obs, cx, x, y, z, v, vy, vz, gr)

def Move.xhit(+s: Nat, r: Pushed, +x: Nat, +y: Nat, +z: Nat, +vy: Z, +vz: Z, +gr: Bool) -> Body & List<&2, Body>:
  Pushed{v, obs, at} = r
  Move.xat(s, at, obs, x, y, z, v, vy, vz, gr)

def Move.xgo(+s: Nat, ok: Bool, +obs: List<&2, Body>, +d: Z, +cx: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool) -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{cx, y, z, vx, vy, vz, gr, hit}, obs)
    case False{}:
      Move.xhit(s, Push.x(s, obs, d, cx, y, z, vx, Geo.head(s, cx, y, z, obs)), x, y, z, vy, vz, gr)

# the move along x, by the start and end velocities added
def Move.x(+s: Nat, +obs: List<&2, Body>, +v0: Z, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit} = b
  +d = Z.add(v0, vx)
  +cx = Z.shift(x, d)
  Move.xgo(s, Bool.and(Z.fits(x, d), Geo.free(s, cx, y, z, obs)), obs, d, cx, x, y, z, vx, vy, vz, gr, hit)

def Move.zput(ok: Bool, +obs: List<&2, Body>, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +v: Z, +gr: Bool)
  -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{x, y, cz, vx, vy, v, gr, True{}}, obs)
    case False{}:
      (Body{x, y, z, vx, vy, v, gr, True{}}, obs)

def Move.zat(+s: Nat, at: Maybe<&2, Nat>, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +v: Z, +gr: Bool)
  -> Body & List<&2, Body>:
  match at:
    case None{}:
      (Body{x, y, z, vx, vy, v, gr, True{}}, obs)
    case Some{+cz}:
      Move.zput(Geo.free(s, x, y, cz, obs), obs, cz, x, y, z, vx, vy, v, gr)

def Move.zhit(+s: Nat, r: Pushed, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +gr: Bool) -> Body & List<&2, Body>:
  Pushed{v, obs, at} = r
  Move.zat(s, at, obs, x, y, z, vx, vy, v, gr)

def Move.zgo(+s: Nat, ok: Bool, +obs: List<&2, Body>, +d: Z, +cz: Nat, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +gr: Bool, +hit: Bool) -> Body & List<&2, Body>:
  match ok:
    case True{}:
      (Body{x, y, cz, vx, vy, vz, gr, hit}, obs)
    case False{}:
      Move.zhit(s, Push.z(s, obs, d, x, y, cz, vz, Geo.head(s, x, y, cz, obs)), x, y, z, vx, vy, gr)

def Move.z(+s: Nat, +obs: List<&2, Body>, +v0: Z, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit} = b
  +d = Z.add(v0, vz)
  +cz = Z.shift(z, d)
  Move.zgo(s, Bool.and(Z.fits(z, d), Geo.free(s, x, y, cz, obs)), obs, d, cz, x, y, z, vx, vy, vz, gr, hit)

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

def Move.rise(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +p: Nat, +vx: Z, +v: Z, +vz: Z, +hit: Bool) -> Body:
  match ok:
    case True{}:
      Body{x, Nat.add(y, p), z, vx, v, vz, False{}, hit}
    case False{}:
      Body{x, y, z, vx, Pos{0n}, vz, False{}, True{}}

def Move.land(ok: Bool, +x: Nat, +y: Nat, +z: Nat, +fl: Nat, +vx: Z, +vz: Z) -> Body:
  match ok:
    case True{}:
      Body{x, fl, z, vx, Pos{0n}, vz, True{}, True{}}
    case False{}:
      Body{x, y, z, vx, Pos{0n}, vz, False{}, True{}}

def Move.fall(+s: Nat, ok: Bool, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +q: Nat, +fl: Nat, +vx: Z, +v: Z, +vz: Z,
  +hit: Bool) -> Body:
  match ok:
    case True{}:
      Body{x, Nat.sub(y, q), z, vx, v, vz, False{}, hit}
    case False{}:
      Move.land(Bool.and(Nat.is_le(fl, y), Geo.free(s, x, fl, z, obs)), x, y, z, fl, vx, vz)

def Move.fly(+s: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vz: Z, +hit: Bool, st: Z & Z) -> Body:
  (v, d) = st
  match d:
    case Pos{+p}:
      Move.rise(Geo.free(s, x, Nat.add(y, p), z, obs), x, y, z, p, vx, v, vz, hit)
    case Neg{+q}:
      +fl = Geo.floor(s, x, y, z, obs, 0n)
      Move.fall(s, Bool.and(Nat.is_le(Nat.add(fl, q), y), Geo.free(s, x, Nat.sub(y, q), z, obs)), obs, x, y, z, q, fl,
        vx, v, vz, hit)

def Move.ygo(+s: Nat, gr: Bool, +g: Nat, +obs: List<&2, Body>, +x: Nat, +y: Nat, +z: Nat, +vx: Z, +vy: Z, +vz: Z,
  +hit: Bool) -> Body:
  match gr:
    case True{}:
      Body{x, y, z, vx, vy, vz, Bool.or(Nat.is_eq(y, 0n), Geo.rests(s, x, y, z, obs)), hit}
    case False{}:
      Move.fly(s, obs, x, y, z, vx, vz, hit, Fly.step(g, vy))

# the vertical move: standing, whether still on something; else a tick of
# gravity, a free fall or rise, or a landing (on the highest top under the
# body, the ground at 0) or a bump
def Move.y(+s: Nat, +g: Nat, +obs: List<&2, Body>, b: Body) -> Body:
  Body{+x, +y, +z, +vx, +vy, +vz, gr, +hit} = b
  Move.ygo(s, gr, g, obs, x, y, z, vx, vy, vz, hit)

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

def Body.tick(+k: K, +obs: List<&2, Body>, inp: In, b: Body) -> Body & List<&2, Body>:
  Body{+x, +y, +z, +vx, +vy, +vz, +gr, +hit} = b
  Tick.z(K.size(k), K.g(k), vz, Move.x(K.size(k), obs, vx, Body.drive(k, inp, Body{x, y, z, vx, vy, vz, gr, hit})))

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
