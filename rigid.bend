# Cubo -- rigid bodies: contacts, impulses and the tick of an island.
#
# A body is a cube of mass 1 and side s: where its box corner is (as in
# phys.bend; its middle is the corner plus s/2), how it is turned (a
# quaternion in 2^-15), its velocity v (a tick moves a free body by the
# start and end velocities added) and its angular momentum L (per unit
# of mass, in units of place times velocity -- an impulse J at an arm r
# adds exactly r x J). A cube turns the same about every axis: its
# inertia is s^2/6, so it turns at w = 6 L / s^2.
#
# The tick of an island (every body that can touch another this tick):
# gravity on every velocity; the contacts, corner against face and corner
# against the floor; impulses at the contacts until they agree; then each
# body moves, and only ever to a place clear of everything. Tipping over
# an edge, spinning off a hit, sliding, falling off a wall: none of it is
# a rule of its own. It is what impulses at the points of contact do.

import Base
import ./phys.bend as P

# Picking
# -------

def R.pz(c: Bool, +a: P.Z, +b: P.Z) -> P.Z:
  match c:
    case True{}:
      a
    case False{}:
      b

def R.pv(c: Bool, +a: P.Wv, +b: P.Wv) -> P.Wv:
  match c:
    case True{}:
      a
    case False{}:
      b

def R.pb(c: Bool, +a: P.Body, +b: P.Body) -> P.Body:
  match c:
    case True{}:
      a
    case False{}:
      b

# a - b
def R.zd(+a: Nat, +b: Nat) -> P.Z:
  P.Z.diff(Nat.is_lt(a, b), a, b)

# the friction coefficient, in 256ths
def R.mu(k: P.K) -> Nat:
  P.K{g, mu, jump, acc, size} = k
  mu

def R.keep(c: Bool, +x: P.Body, xs: List<&2, P.Body>) -> List<&2, P.Body>:
  match c:
    case True{}:
      x <> xs
    case False{}:
      xs

def R.z0() -> P.Z:
  P.Pos{0n}

# is v at or below m?
def R.zle(v: P.Z, +m: Nat) -> Bool:
  match v:
    case P.Pos{n}:
      Nat.is_le(n, m)
    case P.Neg{n}:
      True{}

# Vectors
# -------
# P.Wv is the vector: three signed numbers.

def V.zero() -> P.Wv:
  P.Wv{P.Pos{0n}, P.Pos{0n}, P.Pos{0n}}

def V.add(+a: P.Wv, +b: P.Wv) -> P.Wv:
  P.Wv{P.Z.add(P.Wv.x(a), P.Wv.x(b)), P.Z.add(P.Wv.y(a), P.Wv.y(b)), P.Z.add(P.Wv.z(a), P.Wv.z(b))}

def V.sub(+a: P.Wv, +b: P.Wv) -> P.Wv:
  P.Wv{P.Z.sub(P.Wv.x(a), P.Wv.x(b)), P.Z.sub(P.Wv.y(a), P.Wv.y(b)), P.Z.sub(P.Wv.z(a), P.Wv.z(b))}

def V.opp(+a: P.Wv) -> P.Wv:
  P.Wv{P.Z.opp(P.Wv.x(a)), P.Z.opp(P.Wv.y(a)), P.Z.opp(P.Wv.z(a))}

def V.dot(+a: P.Wv, +b: P.Wv) -> P.Z:
  P.Z.add(P.Z.add(P.Z.mul(P.Wv.x(a), P.Wv.x(b)), P.Z.mul(P.Wv.y(a), P.Wv.y(b))), P.Z.mul(P.Wv.z(a), P.Wv.z(b)))

def V.cross(+a: P.Wv, +b: P.Wv) -> P.Wv:
  P.Wv{P.Z.sub(P.Z.mul(P.Wv.y(a), P.Wv.z(b)), P.Z.mul(P.Wv.z(a), P.Wv.y(b))),
    P.Z.sub(P.Z.mul(P.Wv.z(a), P.Wv.x(b)), P.Z.mul(P.Wv.x(a), P.Wv.z(b))),
    P.Z.sub(P.Z.mul(P.Wv.x(a), P.Wv.y(b)), P.Z.mul(P.Wv.y(a), P.Wv.x(b)))}

# a / d, part by part, toward 0
def V.divn(+a: P.Wv, +d: Nat) -> P.Wv:
  P.Wv{P.Z.divn(P.Wv.x(a), d), P.Z.divn(P.Wv.y(a), d), P.Z.divn(P.Wv.z(a), d)}

# a k, part by part
def V.mulz(+a: P.Wv, +k: P.Z) -> P.Wv:
  P.Wv{P.Z.mul(P.Wv.x(a), k), P.Z.mul(P.Wv.y(a), k), P.Z.mul(P.Wv.z(a), k)}

# a k / 2^16: a direction in 2^-16 scaled by k
def V.fx(+a: P.Wv, +k: P.Z) -> P.Wv:
  V.divn(V.mulz(a, k), 65536n)

def V.l1(+a: P.Wv) -> Nat:
  Nat.add(Nat.add(P.Z.mag(P.Wv.x(a)), P.Z.mag(P.Wv.y(a))), P.Z.mag(P.Wv.z(a)))

def V.sq(+a: P.Wv) -> Nat:
  Nat.add(Nat.add(P.Z.sq(P.Wv.x(a)), P.Z.sq(P.Wv.y(a))), P.Z.sq(P.Wv.z(a)))

# the three axes of a turned cube, one to a row, in 2^-16
def M.r0(+m: P.Mat) -> P.Wv:
  P.Mat{+xx, +xy, +xz, yx, yy, yz, zx, zy, zz} = m
  P.Wv{xx, xy, xz}

def M.r1(+m: P.Mat) -> P.Wv:
  P.Mat{xx, xy, xz, +yx, +yy, +yz, zx, zy, zz} = m
  P.Wv{yx, yy, yz}

def M.r2(+m: P.Mat) -> P.Wv:
  P.Mat{xx, xy, xz, yx, yy, yz, +zx, +zy, +zz} = m
  P.Wv{zx, zy, zz}

# Bodies
# ------

def B.v(+b: P.Body) -> P.Wv:
  P.Wv{P.Body.vx(b), P.Body.vy(b), P.Body.vz(b)}

def B.L(+b: P.Body) -> P.Wv:
  P.Rot.w(P.Body.rot(b))

def B.q(+b: P.Body) -> P.Quat:
  P.Rot.q(P.Body.rot(b))

# from the middle of b to the middle of a
def B.d(+a: P.Body, +b: P.Body) -> P.Wv:
  P.Wv{R.zd(P.Body.x(a), P.Body.x(b)), R.zd(P.Body.y(a), P.Body.y(b)), R.zd(P.Body.z(a), P.Body.z(b))}

# b with velocity v and angular momentum L, flags kept
def B.set(+b: P.Body, +v: P.Wv, +l: P.Wv) -> P.Body:
  P.Body{P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Wv.x(v), P.Wv.y(v), P.Wv.z(v), P.Body.ground(b), P.Body.hit(b),
    P.Rot{B.q(b), l}}

# an impulse J at the arm r: v + J, L + r x J
def B.push(+b: P.Body, +j: P.Wv, +r: P.Wv) -> P.Body:
  B.set(b, V.add(B.v(b), j), V.add(B.L(b), V.cross(r, j)))

# and the same impulse taken away: the other side of the contact
def B.pull(+b: P.Body, +j: P.Wv, +r: P.Wv) -> P.Body:
  B.set(b, V.sub(B.v(b), j), V.sub(B.L(b), V.cross(r, j)))

# how fast the point at the arm r of b moves: v + w x r, w = 6 L / s^2
# (worked out on L and r cut by 2^8 each, which is plenty for the push
# a contact asks for; the impulse itself is exact)
def B.at(+k: P.K, +b: P.Body, +r: P.Wv) -> P.Wv:
  V.add(B.v(b), V.divn(V.mulz(V.cross(V.divn(B.L(b), 256n), V.divn(r, 256n)), P.Pos{6n}),
    P.Pick.high(Nat.div(Nat.mul(P.K.size(k), P.K.size(k)), 65536n), 1n)))

# Lists of bodies by place
# ------------------------

def Bs.at(xs: List<&2, P.Body>, i: Nat) -> P.Body:
  match xs i:
    case [] _:
      P.Body{0n, 0n, 0n, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}, P.Rot.rest()}
    case b <> rest 0n:
      b
    case b <> rest 1n+j:
      Bs.at(rest, j)

def Bs.put(xs: List<&2, P.Body>, i: Nat, +b: P.Body) -> List<&2, P.Body>:
  match xs i:
    case [] _:
      []
    case x <> rest 0n:
      b <> rest
    case x <> rest 1n+j:
      x <> Bs.put(rest, j, b)

# every body but the one at i
def Bs.drop(xs: List<&2, P.Body>, i: Nat) -> List<&2, P.Body>:
  match xs i:
    case [] _:
      []
    case x <> rest 0n:
      rest
    case x <> rest 1n+j:
      x <> Bs.drop(rest, j)

# Contacts
# --------
# A contact between a and b (or a and the floor): the arms from each
# middle to the point, the normal (from b to a, a direction in 2^-16), how
# far apart they are there (gap; below 0 is inside), and what has been
# pushed so far: jn along the normal, never below 0, and jt across it.

type Ct is Data:
  Ct{a: Nat, b: Nat, fl: Bool, ra: P.Wv, rb: P.Wv, n: P.Wv, gap: P.Z, jn: Nat, jt: P.Wv}

# the three half edges of a cube turned by q: h times each of its axes
type E3 is Data:
  E3{e0: P.Wv, e1: P.Wv, e2: P.Wv}

def Ct.half(+h: Nat, +m: P.Mat) -> E3:
  E3{V.fx(M.r0(m), P.Pos{h}), V.fx(M.r1(m), P.Pos{h}), V.fx(M.r2(m), P.Pos{h})}

def Ct.row(i: Nat, +m: P.Mat) -> P.Wv:
  match i:
    case 0n:
      M.r0(m)
    case 1n:
      M.r1(m)
    case _:
      M.r2(m)

def Ct.sgn(s: Bool, +v: P.Wv) -> P.Wv:
  R.pv(s, v, V.opp(v))

# a corner: the arm from the middle, for the signs sx sy sz
def Ct.corner(sx: Bool, sy: Bool, sz: Bool, +e0: P.Wv, +e1: P.Wv, +e2: P.Wv) -> P.Wv:
  V.add(V.add(Ct.sgn(sx, e0), Ct.sgn(sy, e1)), Ct.sgn(sz, e2))

# where p (from the middle of a cube whose axes are m0 m1 m2) lies along
# each axis, in units
def Ct.loc(+p: P.Wv, +m: P.Wv) -> P.Z:
  P.Z.divn(V.dot(p, m), 65536n)

def Ct.in(+l: P.Z, +lim: Nat) -> Bool:
  Nat.is_le(P.Z.mag(l), lim)

def Ct.add_if(c: Bool, +x: Ct, xs: List<&2, Ct>) -> List<&2, Ct>:
  match c:
    case True{}:
      x <> xs
    case False{}:
      xs

# how far a cube with half edges e reaches along the direction n (2^-16)
def Ct.reach(+e: E3, +n: P.Wv) -> Nat:
  E3{+e0, +e1, +e2} = e
  Nat.div(Nat.add(Nat.add(P.Z.mag(V.dot(e0, n)), P.Z.mag(V.dot(e1, n))), P.Z.mag(V.dot(e2, n))), 65536n)

# The face contact. Of the six axes of the two cubes, the one along
# which they are furthest apart (or least into each other) names the
# reference face: that cube's face across that axis, turned toward the
# other. The other cube's face that looks most against it is the
# incident face; its outline, cut to the sides of the reference face
# (Sutherland-Hodgman), is where the two touch, and every point of it no
# further from the reference face than the margin is a contact, all with
# the reference face's normal. A cube lying across another's edge -- its
# bottom edge over the other's top, no corner of either inside the other
# -- is held where that edge crosses; asked corner by corner it was held
# by nothing, and hung in the air.

# a face axis: how far apart along it, the normal (from b to a), whether
# b is the reference (rb), and which of its axes
type Fx is Data:
  Fx{sep: P.Z, n: P.Wv, rb: Bool, ax: Nat}

def Ct.fsep(+d: P.Wv, +ea: E3, +eb: E3, +m: P.Wv, +rb: Bool, +ax: Nat) -> Fx:
  +t = P.Z.divn(V.dot(d, m), 65536n)
  Fx{R.zd(P.Z.mag(t), Nat.add(Ct.reach(ea, m), Ct.reach(eb, m))), R.pv(P.Z.above(P.Pos{0n}, t), V.opp(m), m), rb, ax}

def Fx.sep(+f: Fx) -> P.Z:
  Fx{sep, n, rb, ax} = f
  sep

def Ct.fbest2(c: Bool, +a: Fx, +b: Fx) -> Fx:
  match c:
    case True{}:
      b
    case False{}:
      a

def Ct.fbest(+a: Fx, +b: Fx) -> Fx:
  Ct.fbest2(P.Z.above(Fx.sep(b), Fx.sep(a)), a, b)

def Ct.faces(+d: P.Wv, +ea: E3, +eb: E3, +ma: P.Mat, +mb: P.Mat) -> Fx:
  Ct.fbest(Ct.fbest(Ct.fbest(Ct.fsep(d, ea, eb, M.r1(mb), True{}, 1n), Ct.fsep(d, ea, eb, M.r0(mb), True{}, 0n)),
      Ct.fbest(Ct.fsep(d, ea, eb, M.r2(mb), True{}, 2n), Ct.fsep(d, ea, eb, M.r1(ma), False{}, 1n))),
    Ct.fbest(Ct.fsep(d, ea, eb, M.r0(ma), False{}, 0n), Ct.fsep(d, ea, eb, M.r2(ma), False{}, 2n)))

# v / den for a signed den, part by part, toward 0
def V.divz(+v: P.Wv, den: P.Z) -> P.Wv:
  match den:
    case P.Pos{d}:
      V.divn(v, P.Pick.high(d, 1n))
    case P.Neg{d}:
      V.divn(V.opp(v), P.Pick.high(d, 1n))

def R.zle2(+a: P.Z, +b: P.Z) -> Bool:
  Bool.not(P.Z.above(a, b))

# where the edge from s to e crosses the plane p.m = c (ds, de: s.m, e.m)
def Clip.x(+s: P.Wv, +e: P.Wv, +ds: P.Z, +de: P.Z, +c: P.Z) -> P.Wv:
  V.add(s, V.divz(V.mulz(V.sub(e, s), P.Z.sub(c, ds)), P.Z.sub(de, ds)))

def Clip.edge2(sin: Bool, ein: Bool, +s: P.Wv, +e: P.Wv, +ds: P.Z, +de: P.Z, +c: P.Z, acc: List<&2, P.Wv>)
  -> List<&2, P.Wv>:
  match sin ein:
    case True{} True{}:
      e <> acc
    case False{} True{}:
      e <> (Clip.x(s, e, ds, de, c) <> acc)
    case True{} False{}:
      Clip.x(s, e, ds, de, c) <> acc
    case False{} False{}:
      acc

def Clip.edge(+s: P.Wv, +e: P.Wv, +m: P.Wv, +c: P.Z, acc: List<&2, P.Wv>) -> List<&2, P.Wv>:
  +ds = P.Z.divn(V.dot(s, m), 65536n)
  +de = P.Z.divn(V.dot(e, m), 65536n)
  Clip.edge2(R.zle2(ds, c), R.zle2(de, c), s, e, ds, de, c, acc)

def Clip.poly(pts: List<&2, P.Wv>, +first: P.Wv, +prev: P.Wv, +m: P.Wv, +c: P.Z, acc: List<&2, P.Wv>) -> List<&2, P.Wv>:
  match pts:
    case []:
      Clip.edge(prev, first, m, c, acc)
    case +e <> rest:
      Clip.poly(rest, first, e, m, c, Clip.edge(prev, e, m, c, acc))

# the polygon pts cut to the side p.m <= c of a plane
def Clip.run(pts: List<&2, P.Wv>, +m: P.Wv, +c: P.Z) -> List<&2, P.Wv>:
  match pts:
    case []:
      []
    case +p0 <> rest:
      Clip.poly(rest, p0, p0, m, c, [])

# cut to the four sides of a face whose other two axes are u and v
def Clip.four(pts: List<&2, P.Wv>, +u: P.Wv, +v: P.Wv, +h: Nat) -> List<&2, P.Wv>:
  Clip.run(Clip.run(Clip.run(Clip.run(pts, u, P.Pos{h}), V.opp(u), P.Pos{h}), v, P.Pos{h}), V.opp(v), P.Pos{h})

# the incident face: of a cube with half edges e0 e1 e2 and its middle at
# c, the face whose outward normal points most against nref, as its four
# corners in order
def Inc.corners(+f: P.Wv, +g: P.Wv, +k: P.Wv) -> List<&2, P.Wv>:
  [V.add(V.add(f, g), k), V.sub(V.add(f, g), k), V.sub(V.sub(f, g), k), V.add(V.sub(f, g), k)]

def Inc.pick(i: Nat, +c: P.Wv, +e0: P.Wv, +e1: P.Wv, +e2: P.Wv, +nref: P.Wv) -> List<&2, P.Wv>:
  match i:
    case 0n:
      Inc.corners(V.add(c, Ct.sgn(P.Z.above(P.Pos{0n}, V.dot(e0, nref)), e0)), e1, e2)
    case 1n:
      Inc.corners(V.add(c, Ct.sgn(P.Z.above(P.Pos{0n}, V.dot(e1, nref)), e1)), e2, e0)
    case _:
      Inc.corners(V.add(c, Ct.sgn(P.Z.above(P.Pos{0n}, V.dot(e2, nref)), e2)), e0, e1)

def Inc.face(+c: P.Wv, +e: E3, +nref: P.Wv) -> List<&2, P.Wv>:
  E3{+e0, +e1, +e2} = e
  +d0 = P.Z.mag(V.dot(e0, nref))
  +d1 = P.Z.mag(V.dot(e1, nref))
  +d2 = P.Z.mag(V.dot(e2, nref))
  Inc.pick(P.Pick.n(Bool.and(Nat.is_le(d1, d0), Nat.is_le(d2, d0)), 0n, P.Pick.n(Nat.is_le(d2, d1), 1n, 2n)), c, e0, e1, e2, nref)

# The edge against edge contact. Of the nine directions across an edge
# of each cube (a_i x b_j, made a direction), the one along which the two
# are furthest apart; if that beats every face's by more than a hair, the
# cubes meet edge on edge -- a turned cube leaning its edge on another's,
# where no corner of either is inside the other and the corners found
# nothing -- and the contact is where the two edges come closest.
type Ex is Data:
  Ex{sep: P.Z, n: P.Wv, ia: Nat, jb: Nat, ok: Bool}

def Ct.hrow(i: Nat, e: E3) -> P.Wv:
  match i e:
    case 0n E3{e0, e1, e2}:
      e0
    case 1n E3{e0, e1, e2}:
      e1
    case _ E3{e0, e1, e2}:
      e2

# a x b for two directions in 2^-16, made a direction again (0 when the
# two all but lie along each other: then there is no edge against edge)
def Ct.xdir2(+c: P.Wv, +len: Nat) -> P.Wv:
  V.divn(V.mulz(c, P.Pos{65536n}), P.Pick.high(len, 1n))

def Ct.xdir(+a: P.Wv, +b: P.Wv) -> P.Wv:
  +c = V.cross(V.divn(a, 64n), V.divn(b, 64n))
  Ct.xdir2(c, P.Fric.floor(V.sq(c), P.Pick.high(V.l1(c), 1n)))

def Ct.ex1(+d: P.Wv, +ea: E3, +eb: E3, +l: P.Wv, +i: Nat, +j: Nat) -> Ex:
  +t = P.Z.divn(V.dot(d, l), 65536n)
  Ex{R.zd(P.Z.mag(t), Nat.add(Ct.reach(ea, l), Ct.reach(eb, l))), R.pv(P.Z.above(P.Pos{0n}, t), V.opp(l), l), i, j,
    Nat.is_lt(52429n, V.l1(l))}

def Ct.exbest2(c: Bool, +a: Ex, +b: Ex) -> Ex:
  match c:
    case True{}:
      b
    case False{}:
      a

def Ex.sep(+e: Ex) -> P.Z:
  Ex{sep, n, ia, jb, ok} = e
  sep

def Ex.ok(+e: Ex) -> Bool:
  Ex{sep, n, ia, jb, ok} = e
  ok

def Ct.exbest(+a: Ex, +b: Ex) -> Ex:
  Ct.exbest2(Bool.and(Ex.ok(b), Bool.or(Bool.not(Ex.ok(a)), P.Z.above(Ex.sep(b), Ex.sep(a)))), a, b)

def Ct.ex(+d: P.Wv, +ea: E3, +eb: E3, +ma: P.Mat, +mb: P.Mat, +i: Nat, +j: Nat) -> Ex:
  Ct.ex1(d, ea, eb, Ct.xdir(Ct.row(i, ma), Ct.row(j, mb)), i, j)

def Ct.edges(+d: P.Wv, +ea: E3, +eb: E3, +ma: P.Mat, +mb: P.Mat) -> Ex:
  Ct.exbest(Ct.exbest(Ct.exbest(Ct.ex(d, ea, eb, ma, mb, 0n, 0n), Ct.ex(d, ea, eb, ma, mb, 0n, 1n)),
      Ct.exbest(Ct.ex(d, ea, eb, ma, mb, 0n, 2n), Ct.ex(d, ea, eb, ma, mb, 1n, 0n))),
    Ct.exbest(Ct.exbest(Ct.ex(d, ea, eb, ma, mb, 1n, 1n), Ct.ex(d, ea, eb, ma, mb, 1n, 2n)),
      Ct.exbest(Ct.ex(d, ea, eb, ma, mb, 2n, 0n), Ct.ex(d, ea, eb, ma, mb, 2n, 1n))))

def Ct.edges9(+d: P.Wv, +ea: E3, +eb: E3, +ma: P.Mat, +mb: P.Mat) -> Ex:
  Ct.exbest(Ct.edges(d, ea, eb, ma, mb), Ct.ex(d, ea, eb, ma, mb, 2n, 2n))

# the offset, from a cube's middle, of its edge along axis i that reaches
# furthest the way n points (sg true) or the other way: the other two half
# edges, each turned toward n
def Ct.toward(+sg: Bool, +e: P.Wv, +n: P.Wv) -> P.Wv:
  +pos = Bool.not(P.Z.above(P.Pos{0n}, V.dot(e, n)))
  R.pv(Bool.or(Bool.and(sg, pos), Bool.and(Bool.not(sg), Bool.not(pos))), e, V.opp(e))

def Ct.edge_off(+i: Nat, +sg: Bool, +e: E3, +n: P.Wv) -> P.Wv:
  E3{+e0, +e1, +e2} = e
  V.add(V.add(R.pv(Nat.is_eq(i, 0n), V.zero(), Ct.toward(sg, e0, n)), R.pv(Nat.is_eq(i, 1n), V.zero(), Ct.toward(sg, e1, n))),
    R.pv(Nat.is_eq(i, 2n), V.zero(), Ct.toward(sg, e2, n)))

# s and t held to the edges (the half side h either way of their middles)
def Ct.clampz(+x: P.Z, +h: Nat) -> P.Z:
  R.pz(Nat.is_lt(P.Z.mag(x), h), x, R.pz(P.Z.above(x, P.Pos{0n}), P.Pos{h}, P.Neg{h}))

# the closest points of the edges pa + s u and pb + t v (u, v directions
# in 2^-16, s and t in [-h, h]), from the middle of b: their midpoint, if
# both fall inside their edges -- where the edges really cross. Where one
# falls at an end, the two meet corner to face or corner to edge, and the
# face contacts already hold that; two cubes square with each other have
# every edge direction along a face, and the ends of such edges gave a
# point under the middle that held a cube past an edge up by nothing.
type Ep is Data:
  Ep{inside: Bool, p: P.Wv}

def Ct.close2(+pa: P.Wv, +u: P.Wv, +pb: P.Wv, +v: P.Wv, +h: Nat, +bb: P.Z, +s: P.Z, +best: Bool) -> Ep:
  +w = V.sub(pa, pb)
  +t = P.Z.add(P.Z.divn(V.dot(v, w), 65536n), P.Z.divn(P.Z.mul(bb, s), 65536n))
  Ep{Bool.or(best, Bool.and(Nat.is_lt(P.Z.mag(s), h), Nat.is_lt(P.Z.mag(t), h))),
    V.divn(V.add(V.add(pa, V.fx(u, Ct.clampz(s, h))), V.add(pb, V.fx(v, Ct.clampz(t, h)))), 2n)}

# The nearest points of two edges, and whether they lie on both. Where
# the edges tell the pair apart strictly better than any face (best), the
# contact is made even if the nearest points of the two lines fall a hair
# past an end (held to the edges): the pair is deepest there, and a
# contact the impulses never saw let a body fall into what the gate then
# refused every tick -- it hung in the air. Square cubes never get here:
# their edge directions are face directions.
def Ct.close(+pa: P.Wv, +u: P.Wv, +pb: P.Wv, +v: P.Wv, +h: Nat, +best: Bool) -> Ep:
  +w = V.sub(pa, pb)
  +bb = P.Z.divn(V.dot(u, v), 65536n)
  +dd = P.Z.divn(V.dot(u, w), 65536n)
  +ee = P.Z.divn(V.dot(v, w), 65536n)
  +den = Nat.sub(65536n, Nat.div(P.Z.sq(bb), 65536n))
  Ct.close2(pa, u, pb, v, h, bb, P.Z.divn(P.Z.sub(P.Z.mul(bb, ee), P.Z.mul(dd, P.Pos{65536n})), P.Pick.high(den, 1n)), best)

def Ct.edge2(+i: Nat, +j: Nat, +d: P.Wv, +sep: P.Z, +n: P.Wv, ep: Ep, cs: List<&2, Ct>) -> List<&2, Ct>:
  Ep{+inside, +p} = ep
  Ct.add_if(inside, Ct{i, j, False{}, V.sub(p, d), p, n, sep, 0n, V.zero()}, cs)

def Ct.edge1(+best: Bool, +i: Nat, +j: Nat, +d: P.Wv, +ea: E3, +eb: E3, +ma: P.Mat, +mb: P.Mat, +h: Nat, e: Ex, cs: List<&2, Ct>)
  -> List<&2, Ct>:
  Ex{+sep, +n, +ia, +jb, ok} = e
  Ct.edge2(i, j, d, sep, n,
    Ct.close(V.add(d, Ct.edge_off(ia, False{}, ea, n)), Ct.row(ia, ma), Ct.edge_off(jb, True{}, eb, n), Ct.row(jb, mb), h, best), cs)

# the margin a pair is looked at within: a sixty-fourth of a side, and
# twice what the two can close in a tick
def Ct.margin(+k: P.K, +va: P.Wv, +vb: P.Wv) -> Nat:
  Nat.add(Nat.div(P.K.size(k), 64n), Nat.mul(2n, Nat.add(Nat.add(V.l1(va), V.l1(vb)), P.K.g(k))))

# are two middles near enough to touch within the margin?
def Ct.near(+s: Nat, +mg: Nat, +d: P.Wv) -> Bool:
  +r = Nat.add(Nat.mul(2n, s), mg)
  Bool.and(Nat.is_lt(P.Z.mag(P.Wv.x(d)), r), Bool.and(Nat.is_lt(P.Z.mag(P.Wv.y(d)), r), Nat.is_lt(P.Z.mag(P.Wv.z(d)), r)))

# the corners of a on the floor: the floor pushes straight up
def Ct.flvert(+i: Nat, +cy: Nat, +r: P.Wv, +mg: Nat, cs: List<&2, Ct>) -> List<&2, Ct>:
  +gy = P.Z.add(P.Pos{cy}, P.Wv.y(r))
  Ct.add_if(R.zle(gy, mg), Ct{i, 0n, True{}, r, V.zero(), P.Wv{P.Pos{0n}, P.Pos{65536n}, P.Pos{0n}}, gy, 0n, V.zero()}, cs)

def Ct.flcorners(n: Nat, +i: Nat, +cy: Nat, +e0: P.Wv, +e1: P.Wv, +e2: P.Wv, +mg: Nat, cs: List<&2, Ct>) -> List<&2, Ct>:
  match n:
    case 0n:
      cs
    case 1n++c:
      Ct.flcorners(c, i, cy, e0, e1, e2, mg,
        Ct.flvert(i, cy, Ct.corner(Nat.is_eq(Nat.mod(c, 2n), 1n), Nat.is_eq(Nat.mod(Nat.div(c, 2n), 2n), 1n),
          Nat.is_eq(Nat.mod(Nat.div(c, 4n), 2n), 1n), e0, e1, e2), mg, cs))

def Ct.floor2(ea: E3, +i: Nat, +cy: Nat, +mg: Nat, cs: List<&2, Ct>) -> List<&2, Ct>:
  E3{+a0, +a1, +a2} = ea
  Ct.flcorners(8n, i, cy, a0, a1, a2, mg, cs)

def Ct.floor(+k: P.K, +i: Nat, +a: P.Body, cs: List<&2, Ct>) -> List<&2, Ct>:
  +h = Nat.div(P.K.size(k), 2n)
  Ct.floor2(Ct.half(h, P.Rot.mat(B.q(a))), i, Nat.add(P.Body.y(a), h),
    Nat.add(Nat.div(P.K.size(k), 64n), Nat.mul(2n, Nat.add(V.l1(B.v(a)), P.K.g(k)))), cs)

# A fixed body -- one that sleeps, held by what is under it -- is to the
# ones that move what the floor is: it pushes back and is not moved. Its
# contacts carry fl, and b is its place among the fixed ones plus one (0
# is the floor).
def Ct.fix(cs: List<&2, Ct>, +j: Nat) -> List<&2, Ct>:
  match cs:
    case []:
      []
    case Ct{a, b, fl, ra, rb, n, gap, jn, jt} <> rest:
      Ct{a, Nat.add(j, 1n), True{}, ra, rb, n, gap, jn, jt} <> Ct.fix(rest, j)

type St is Data:
  St{done: List<&2, Ct>, bs: List<&2, P.Body>}

def Imp.keff2(fl: Bool, +ta: Nat, +tb: Nat) -> Nat:
  match fl:
    case True{}:
      Nat.add(1024n, ta)
    case False{}:
      Nat.add(2048n, Nat.add(ta, tb))

# how much harder the contact is to push than a free mass: 1 for each
# body, and 6 (r x n)^2 / s^2 for the turning of each, in 1024ths
def Imp.keff(+k: P.K, fl: Bool, +ra: P.Wv, +rb: P.Wv, +n: P.Wv) -> Nat:
  +s2 = P.Pick.high(Nat.div(Nat.mul(P.K.size(k), P.K.size(k)), 256n), 1n)
  Imp.keff2(fl, Nat.div(Nat.mul(6144n, V.sq(V.divn(V.cross(ra, n), 1048576n))), s2),
    Nat.div(Nat.mul(6144n, V.sq(V.divn(V.cross(rb, n), 1048576n))), s2))

# the velocity of a's point against b's (b nothing for the floor)
def Imp.rel(+k: P.K, fl: Bool, +a: P.Body, +b: P.Body, +ra: P.Wv, +rb: P.Wv) -> P.Wv:
  R.pv(fl, B.at(k, a, ra), V.sub(B.at(k, a, ra), B.at(k, b, rb)))

# what has been pushed, plus lam, never below 0
def Imp.accn(+jn: Nat, lam: P.Z) -> Nat:
  match lam:
    case P.Pos{p}:
      Nat.add(jn, p)
    case P.Neg{q}:
      Nat.sub(jn, q)

# the friction pushed so far, held to mu jn/256 in size: scaled down by
# lim / |t| when bigger, and the scaled one checked -- a square root a unit
# short would leave it a hair over, and then there is none (Coulomb holds
# whatever the root: Imp.clamp_ok)
def Imp.clamp3(ok: Bool, +r: P.Wv) -> P.Wv:
  match ok:
    case True{}:
      r
    case False{}:
      V.zero()

def Imp.clamp2(big: Bool, +t: P.Wv, +lim: Nat, +mag: Nat) -> P.Wv:
  match big:
    case False{}:
      t
    case True{}:
      +r = V.divn(V.mulz(t, P.Pos{lim}), P.Pick.high(mag, 1n))
      Imp.clamp3(Nat.is_le(V.sq(r), Nat.mul(lim, lim)), r)

def Imp.clamp(+t: P.Wv, +lim: Nat) -> P.Wv:
  +sq = V.sq(t)
  +mag = P.Fric.ceil(sq, P.Fric.floor(sq, P.Pick.high(V.l1(t), 1n)))
  Imp.clamp2(Nat.is_lt(Nat.mul(lim, lim), sq), t, lim, mag)

def Imp.side(fl: Bool, +i: Nat, +b: P.Body, +bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match fl:
    case True{}:
      bs
    case False{}:
      Bs.put(bs, i, b)

# the friction, once the push along the normal is in
# the most friction a contact pushing jn can give: mu jn (mu in 1/256)
def Imp.lim(+k: P.K, +jn: Nat) -> Nat:
  Nat.div(Nat.mul(R.mu(k), jn), 256n)

# the friction that would stop the sliding at the contact outright, added
# to what it pushed so far
def Imp.tfric(+k: P.K, +fl: Bool, +ba: P.Body, +bb: P.Body, +ra: P.Wv, +rb: P.Wv, +n: P.Wv, +jt: P.Wv, +kf: Nat) -> P.Wv:
  +u = Imp.rel(k, fl, ba, bb, ra, rb)
  +ut = V.sub(u, V.fx(n, P.Z.divn(V.dot(u, n), 65536n)))
  V.sub(jt, V.divn(V.mulz(ut, P.Pos{1024n}), kf))

# a contact once its push is in, with the friction it asks for (not yet
# given), and the bodies as the push left them
type R2 is Data:
  R2{c: Ct, j: P.Wv}

def R2.c(+r: R2) -> Ct:
  R2{c, j} = r
  c

def R2.j(+r: R2) -> P.Wv:
  R2{c, j} = r
  j

def Imp.fric(+k: P.K, +a: Nat, +b: Nat, +fl: Bool, +ra: P.Wv, +rb: P.Wv, +n: P.Wv, +gap: P.Z, +jn: Nat, +jt: P.Wv,
  +kf: Nat, +j: P.Wv, +ba: P.Body, +bb: P.Body) -> R2:
  R2{Ct{a, b, fl, ra, rb, n, gap, jn, Imp.clamp(Imp.tfric(k, fl, ba, bb, ra, rb, n, jt, kf), Imp.lim(k, jn))}, j}

# Coulomb, for one contact: its friction is at most mu times its push
def Ct.coul(+k: P.K, c: Ct) -> Bool:
  Ct{a, b, fl, ra, rb, n, gap, +jn, +jt} = c
  Nat.is_le(V.sq(jt), Nat.mul(Imp.lim(k, jn), Imp.lim(k, jn)))

# the contact as it goes into the list, and as its friction is given: as
# asked if within Coulomb (the clamp makes it so), else none
def Ct.safe2(ok: Bool, c: Ct) -> Ct:
  match ok:
    case True{}:
      c
    case False{}:
      Ct{a, b, fl, ra, rb, n, gap, jn, jt} = c
      Ct{a, b, fl, ra, rb, n, gap, jn, V.zero()}

def Ct.safe(+k: P.K, +c: Ct) -> Ct:
  Ct.safe2(Ct.coul(k, c), c)

def Ct.jt(+c: Ct) -> P.Wv:
  Ct{a, b, fl, ra, rb, n, gap, jn, jt} = c
  jt

def Ct.a(+c: Ct) -> Nat:
  Ct{a, b, fl, ra, rb, n, gap, jn, jt} = c
  a

def Ct.b(+c: Ct) -> Nat:
  Ct{a, b, fl, ra, rb, n, gap, jn, jt} = c
  b

def Ct.fl(+c: Ct) -> Bool:
  Ct{a, b, fl, ra, rb, n, gap, jn, jt} = c
  fl

def Ct.ra(+c: Ct) -> P.Wv:
  Ct{a, b, fl, ra, rb, n, gap, jn, jt} = c
  ra

def Ct.rb(+c: Ct) -> P.Wv:
  Ct{a, b, fl, ra, rb, n, gap, jn, jt} = c
  rb

# What a solved contact gives its two bodies (ba, bb as they were): the
# push j along the normal and the friction dt, both at once, equal and
# opposite, at the same point (each body's arm to it). A fixed body is
# left as it is. This is the only way the solver changes a velocity.
def Imp.give(+c: Ct, +j: P.Wv, +dt: P.Wv, bs: List<&2, P.Body>, +ba: P.Body, +bb: P.Body) -> List<&2, P.Body>:
  Imp.side(Ct.fl(c), Ct.b(c), B.pull(B.pull(bb, j, Ct.rb(c)), dt, Ct.rb(c)),
    Bs.put(bs, Ct.a(c), B.push(B.push(ba, j, Ct.ra(c)), dt, Ct.ra(c))))

type Sup is Data:
  Sup{touched: Bool, nn: P.Wv, n: Nat, lx: P.Z, hx: P.Z, lz: P.Z, hz: P.Z, dg: P.Z, dn: P.Wv, pj: Nat, pr: P.Wv}

def Sup.none() -> Sup:
  Sup{False{}, V.zero(), 0n, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, P.Pos{1073741824n}, V.zero(), 0n, V.zero()}

def Sup.lo(+a: P.Z, +b: P.Z) -> P.Z:
  R.pz(P.Z.above(a, b), b, a)

def Sup.hi(+a: P.Z, +b: P.Z) -> P.Z:
  R.pz(P.Z.above(a, b), a, b)

# the points of the cut outline no further from the reference face (its
# outward normal nf, h from its middle) than the margin, as contacts:
# with b the reference the points are from b's middle, else from a's
def Ct.clipped(pts: List<&2, P.Wv>, +i: Nat, +j: Nat, +rb: Bool, +n: P.Wv, +nf: P.Wv, +d: P.Wv, +h: Nat, +mg: Nat,
  +lo: P.Z, cs: List<&2, Ct>) -> List<&2, Ct>:
  match pts:
    case []:
      cs
    case +p <> rest:
      +gap = Sup.hi(lo, P.Z.sub(P.Z.divn(V.dot(p, nf), 65536n), P.Pos{h}))
      Ct.clipped(rest, i, j, rb, n, nf, d, h, mg, lo,
        Ct.add_if(R.zle(gap, mg), Ct{i, j, False{}, R.pv(rb, V.sub(p, d), p), R.pv(rb, p, V.add(p, d)), n, gap, 0n, V.zero()}, cs))

def Ct.facepair(rb: Bool, +ea: E3, +eb: E3, +i: Nat, +j: Nat, +d: P.Wv, +ma: P.Mat, +mb: P.Mat, +h: Nat, +mg: Nat,
  +n: P.Wv, +ax: Nat, +lo: P.Z, cs: List<&2, Ct>) -> List<&2, Ct>:
  match rb:
    case True{}:
      Ct.clipped(Clip.four(Inc.face(d, ea, n), Ct.row(Nat.mod(Nat.add(ax, 1n), 3n), mb), Ct.row(Nat.mod(Nat.add(ax, 2n), 3n), mb), h),
        i, j, True{}, n, n, d, h, mg, lo, cs)
    case False{}:
      Ct.clipped(Clip.four(Inc.face(V.opp(d), eb, V.opp(n)), Ct.row(Nat.mod(Nat.add(ax, 1n), 3n), ma),
        Ct.row(Nat.mod(Nat.add(ax, 2n), 3n), ma), h), i, j, False{}, n, V.opp(n), d, h, mg, lo, cs)

# lo: the most the pair is apart along any of the fifteen directions; no
# point of it is further into the other than that (a face's own depths
# can say more, when the pair is best told apart edge by edge, and pushed
# apart what the gate had found clear)
def Ct.pairf(+ea: E3, +eb: E3, +i: Nat, +j: Nat, +d: P.Wv, +ma: P.Mat, +mb: P.Mat, +h: Nat, +mg: Nat, f: Fx,
  +lo: P.Z, cs: List<&2, Ct>) -> List<&2, Ct>:
  Fx{sep, +n, +rb, +ax} = f
  Ct.facepair(rb, ea, eb, i, j, d, ma, mb, h, mg, n, ax, lo, cs)

# a contact that pushed the body: its normal f facing it, at arm r. Its
# point widens the reach of the contacts around the middle; one pushing
# up from below (within 45 degrees of up) counts as a support.
def Sup.add3(up: Bool, +f: P.Wv, +r: P.Wv, s: Sup) -> Sup:
  Sup{t, +nn, +n, +lx, +hx, +lz, +hz, dg, dn, pj, pr} = s
  +x = P.Wv.x(r)
  +z = P.Wv.z(r)
  +first = Bool.not(t)
  Sup{True{}, V.add(nn, f), P.Pick.n(up, Nat.add(n, 1n), n), R.pz(first, x, Sup.lo(lx, x)), R.pz(first, x, Sup.hi(hx, x)),
    R.pz(first, z, Sup.lo(lz, z)), R.pz(first, z, Sup.hi(hz, z)), dg, dn, pj, pr}

def Sup.add2(pushed: Bool, +f: P.Wv, +r: P.Wv, s: Sup) -> Sup:
  match pushed:
    case False{}:
      Sup{t, +nn, n, lx, hx, lz, hz, dg, dn, pj, pr} = s
      Sup{t, V.add(nn, f), n, lx, hx, lz, hz, dg, dn, pj, pr}
    case True{}:
      Sup.add3(P.Z.above(P.Wv.y(f), P.Pos{46341n}), f, r, s)

# the contact the body is deepest into (or nearest): the way out of it
def Sup.deep(+gap: P.Z, +f: P.Wv, s: Sup) -> Sup:
  Sup{t, nn, n, lx, hx, lz, hz, +dg, +dn, pj, pr} = s
  Sup{t, nn, n, lx, hx, lz, hz, R.pz(P.Z.above(dg, gap), gap, dg), R.pv(P.Z.above(dg, gap), f, dn), pj, pr}

# the contact that carries the most is what the body turns about
def Sup.piv(+jn: Nat, +r: P.Wv, s: Sup) -> Sup:
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, +pj, +pr} = s
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, P.Pick.n(Nat.is_lt(pj, jn), jn, pj), R.pv(Nat.is_lt(pj, jn), r, pr)}

def Sup.add0(mine: Bool, +pushed: Bool, +f: P.Wv, +r: P.Wv, +gap: P.Z, +jn: Nat, s: Sup) -> Sup:
  match mine:
    case False{}:
      s
    case True{}:
      Sup.piv(jn, r, Sup.deep(gap, f, Sup.add2(pushed, f, r, s)))

def Sup.pr(s: Sup) -> P.Wv:
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, pj, pr} = s
  pr

def Sup.pivots(s: Sup) -> Bool:
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, pj, pr} = s
  Nat.is_lt(0n, pj)

def Sup.dn(s: Sup) -> P.Wv:
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, pj, pr} = s
  dn

# nn counts every contact of the body, pushed or not: a body touching a
# wall only within the rounding of the fifteen axes, with nothing pushing,
# had no way to be lifted off it, and every move along the wall was
# refused
# what holds the body up is what touches it (see Mv.cut)
def Sup.add1(+sk: P.Z, +i: Nat, c: Ct, s: Sup) -> Sup:
  Ct{+a, +b, +fl, +ra, +rb, +n, +gap, +jn, +jt} = c
  +pushed = Bool.and(Bool.or(Nat.is_lt(0n, jn), Nat.is_lt(0n, V.l1(jt))), R.zle2(gap, sk))
  +asa = Nat.is_eq(a, i)
  +asb = Bool.and(Bool.not(fl), Nat.is_eq(b, i))
  Sup.add0(Bool.or(asa, asb), pushed, R.pv(asa, n, V.opp(n)), R.pv(asa, ra, rb), gap, jn, s)

def Sup.of(+sk: P.Z, +i: Nat, cs: List<&2, Ct>, s: Sup) -> Sup:
  match cs:
    case []:
      s
    case +c <> rest:
      Sup.of(sk, i, rest, Sup.add1(sk, i, c, s))

# is the middle over the support: 0 inside [lx, hx] and [lz, hz]?
def Sup.balanced(s: Sup) -> Bool:
  Sup{t, nn, +n, lx, hx, lz, hz, dg, dn, pj, pr} = s
  Bool.and(Nat.is_lt(0n, n), Bool.and(Bool.and(R.zle(lx, 0n), Bool.not(P.Z.above(P.Pos{0n}, hx))),
    Bool.and(R.zle(lz, 0n), Bool.not(P.Z.above(P.Pos{0n}, hz)))))

def Sup.touched(s: Sup) -> Bool:
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, pj, pr} = s
  t

def Sup.held(s: Sup) -> Bool:
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, pj, pr} = s
  Nat.is_lt(0n, n)

def Sup.nn(s: Sup) -> P.Wv:
  Sup{t, nn, n, lx, hx, lz, hz, dg, dn, pj, pr} = s
  nn

# Moving
# ------
# A body nothing pushed flies: it moves by its start and end velocities
# added -- the exact parabola -- and turns as its angular momentum says.
# A body in contact moves by twice its end velocity. Either way it only
# goes where it is clear of everything and of the floor. A turn is taken
# about the middle, and over a whole tick the corners go round an arc,
# not the straight line the impulses planned: a cube tipping over an edge
# dips the corner it pivots on into what holds it by h t^2 / 2 (t the
# angle), and the move was refused, and the cube stayed balanced on the
# edge. So a refused move is tried again lifted by that much, the way
# what it touches pushes it; then the biggest part of it that is clear
# (halving, six times, each lifted too); and if none is, it stays, and
# the knock takes its velocity and its turning.

# the turning of a tick, in shares of a whole turn a tick, from L:
# w = 6 L / s^2 radians a half tick, twice that a tick, times 2^32 / 2 pi:
# 12 L 2^32 / (2 pi s^2) = 125163 L / (s^2 / 2^16), worked out on L / 16
# so that the product stays under 2^48 (a whole word of turning)
def Mv.w(+k: P.K, +l: P.Wv) -> P.Wv:
  +s2 = P.Pick.high(Nat.div(Nat.mul(P.K.size(k), P.K.size(k)), 1048576n), 1n)
  V.divn(V.mulz(V.divn(l, 16n), P.Pos{125163n}), s2)

# the way to lift a body: its contacts' normals, as a direction in 2^-16
def Mv.away(+nn: P.Wv) -> P.Wv:
  V.divn(V.mulz(nn, P.Pos{65536n}), P.Pick.high(P.Fric.floor(V.sq(nn), P.Pick.high(V.l1(nn), 1n)), 1n))

# The slop: how far two turned cubes may be into each other and still
# count as touching -- a 4096th of a side, a quarter of a millimetre. The
# fifteen directions come from matrices in 2^-16, and two ways of asking
# where a turned cube is (its contact points, its separation) disagree
# by a few units; with nothing to take that up, a body resting on
# another's edge was held by the one and dropped by the other, and hung.
# The gate lets a body that far in, and the impulses push out only what
# is further in than that.
def R.slop(+s: Nat) -> Nat:
  Nat.div(s, 4096n)

# how far into each other the impulses let two cubes stay before they
# push them apart: a quarter of the gate's slop, so that a pair the
# impulses hold keeps most of the slop in hand. With a slop four times as
# wide the pairs drifted deep into it, and a body wedged between two was
# refused every way out.
def R.skin(+s: Nat) -> Nat:
  Nat.div(s, 16384n)

# what the velocity along the normal has to reach: apart by gap, it may
# close in by half of it a half tick (a body in contact moves by twice its
# end velocity); into each other, it must not close in, and pushes out
# what is past the skin, half of it a half tick -- so a resting pair keeps
# most of the slop in hand before the gate would refuse a move
def Imp.target(+s: Nat, gap: P.Z) -> P.Z:
  match gap:
    case P.Pos{g}:
      P.Neg{Nat.div(g, 2n)}
    case P.Neg{g}:
      P.Pos{Nat.div(Nat.sub(g, R.skin(s)), 2n)}

# the push along the normal so far, and the change that makes the contact
# close in no faster than it may -- never below nothing (Imp.accn)
def Imp.jn2(+k: P.K, +fl: Bool, +ra: P.Wv, +rb: P.Wv, +n: P.Wv, +gap: P.Z, +jn: Nat, +kf: Nat, +ba: P.Body, +bb: P.Body) -> Nat:
  +vn = P.Z.divn(V.dot(Imp.rel(k, fl, ba, bb, ra, rb), n), 65536n)
  Imp.accn(jn, P.Z.divc(P.Z.mul(P.Z.sub(Imp.target(P.K.size(k), gap), vn), P.Pos{1024n}), kf))

def Imp.norm(+k: P.K, +a: Nat, +b: Nat, +fl: Bool, +ra: P.Wv, +rb: P.Wv, +n: P.Wv, +gap: P.Z, +jn: Nat, +jt: P.Wv,
  +ba: P.Body, +bb: P.Body) -> R2:
  +kf = Imp.keff(k, fl, ra, rb, n)
  +jn2 = Imp.jn2(k, fl, ra, rb, n, gap, jn, kf, ba, bb)
  +j = V.fx(n, R.zd(jn2, jn))
  Imp.fric(k, a, b, fl, ra, rb, n, gap, jn2, jt, kf, j, B.push(ba, j, ra), R.pb(fl, bb, B.pull(bb, j, rb)))

# the contact solved (its push in, its friction asked for) and the push,
# from the contact and its two bodies
def Imp.raw(+k: P.K, c: Ct, +ba: P.Body, +bb: P.Body) -> R2:
  Ct{+a, +b, +fl, +ra, +rb, +n, +gap, +jn, +jt} = c
  Imp.norm(k, a, b, fl, ra, rb, n, gap, jn, jt, ba, bb)

# one contact solved: its push, then its friction as Ct.safe hands it on,
# both given to the bodies at once (Imp.give)
def Imp.one2(+k: P.K, +c0: Ct, +r: R2, done: List<&2, Ct>, bs: List<&2, P.Body>, +ba: P.Body, +bb: P.Body) -> St:
  +c = Ct.safe(k, R2.c(r))
  St{c <> done, Imp.give(c0, R2.j(r), V.sub(Ct.jt(c), Ct.jt(c0)), bs, ba, bb)}

def Imp.one(+k: P.K, +c: Ct, st: St) -> St:
  St{done, +bs} = st
  +ba = Bs.at(bs, Ct.a(c))
  +bb = Bs.at(bs, Ct.b(c))
  Imp.one2(k, c, Imp.raw(k, c, ba, bb), done, bs, ba, bb)

# one pass over the contacts
def Imp.pass(+k: P.K, cs: List<&2, Ct>, st: St) -> St:
  match cs:
    case []:
      st
    case c <> rest:
      Imp.pass(k, rest, Imp.one(k, c, st))

def Imp.again(+k: P.K, st: St) -> St:
  St{done, bs} = st
  Imp.pass(k, done, St{[], bs})

def Imp.iter(n: Nat, +k: P.K, st: St) -> St:
  match n:
    case 0n:
      st
    case 1n+m:
      Imp.iter(m, k, Imp.again(k, st))

# What the contacts did to one body
# ---------------------------------
# touched: some contact pushed it; nn: the normals of those contacts,
# turned to face it, added up (the way what it touches pushes it); n: how
# many of them push it up from below (their normal within 45 degrees of
# up); and the reach of all their points around its middle, along x and
# along z -- a cube wedged between what it stands on and the side of a
# neighbour is held by both.

def R.exsep(+e: Ex) -> P.Z:
  R.pz(Ex.ok(e), Ex.sep(e), P.Neg{1073741824n})

# the face contacts, and the edge contact too when the edges come within
# the margin: two turned cubes can touch edge to edge a hair nearer than
# any face says, and a contact the impulses never saw let a body fall
# into what the gate then would not let it enter
def Ct.pair4(edge: Bool, +ea: E3, +eb: E3, +i: Nat, +j: Nat, +d: P.Wv, +ma: P.Mat, +mb: P.Mat, +h: Nat, +mg: Nat,
  +f: Fx, +e: Ex, cs: List<&2, Ct>) -> List<&2, Ct>:
  match edge:
    case True{}:
      Ct.edge1(P.Z.above(Ex.sep(e), Fx.sep(f)), i, j, d, ea, eb, ma, mb, h, e, Ct.pairf(ea, eb, i, j, d, ma, mb, h, mg, f, Sup.hi(Fx.sep(f), Ex.sep(e)), cs))
    case False{}:
      Ct.pairf(ea, eb, i, j, d, ma, mb, h, mg, f, Sup.hi(Fx.sep(f), R.exsep(e)), cs)

def Ct.pair2b(+ea: E3, +eb: E3, +i: Nat, +j: Nat, +d: P.Wv, +ma: P.Mat, +mb: P.Mat, +h: Nat, +mg: Nat, +f: Fx, +e: Ex,
  cs: List<&2, Ct>) -> List<&2, Ct>:
  Ct.pair4(Bool.and(Ex.ok(e), R.zle(Ex.sep(e), mg)),
    ea, eb, i, j, d, ma, mb, h, mg, f, e, cs)

def Ct.pair2(+ea: E3, +eb: E3, +i: Nat, +j: Nat, +d: P.Wv, +ma: P.Mat, +mb: P.Mat, +h: Nat, +mg: Nat,
  cs: List<&2, Ct>) -> List<&2, Ct>:
  Ct.pair2b(ea, eb, i, j, d, ma, mb, h, mg, Ct.faces(d, ea, eb, ma, mb), Ct.edges9(d, ea, eb, ma, mb), cs)

def Ct.pair1(near: Bool, +k: P.K, +i: Nat, +j: Nat, +a: P.Body, +b: P.Body, +d: P.Wv, +mg: Nat, cs: List<&2, Ct>)
  -> List<&2, Ct>:
  match near:
    case False{}:
      cs
    case True{}:
      +h = Nat.div(P.K.size(k), 2n)
      +ma = P.Rot.mat(B.q(a))
      +mb = P.Rot.mat(B.q(b))
      Ct.pair2(Ct.half(h, ma), Ct.half(h, mb), i, j, d, ma, mb, h, mg, cs)

def Ct.pair(+k: P.K, +i: Nat, +j: Nat, +a: P.Body, +b: P.Body, cs: List<&2, Ct>) -> List<&2, Ct>:
  +d = B.d(a, b)
  +mg = Ct.margin(k, B.v(a), B.v(b))
  Ct.pair1(Ct.near(P.K.size(k), mg, d), k, i, j, a, b, d, mg, cs)

# every contact of the body at i with the ones after it, and the floor's
def Ct.with(rest: List<&2, P.Body>, +k: P.K, +i: Nat, +j: Nat, +a: P.Body, cs: List<&2, Ct>) -> List<&2, Ct>:
  match rest:
    case []:
      cs
    case +b <> more:
      Ct.with(more, k, i, Nat.add(j, 1n), a, Ct.pair(k, i, j, a, b, cs))

def Ct.withfix(ss: List<&2, P.Body>, +k: P.K, +i: Nat, +j: Nat, +a: P.Body, cs: List<&2, Ct>) -> List<&2, Ct>:
  match ss:
    case []:
      cs
    case +b <> more:
      Ct.withfix(more, k, i, Nat.add(j, 1n), a, List.append(&2, Ct, Ct.fix(Ct.pair(k, i, j, a, b, []), j), cs))

def Ct.all(bs: List<&2, P.Body>, +k: P.K, +i: Nat, +ss: List<&2, P.Body>, cs: List<&2, Ct>) -> List<&2, Ct>:
  match bs:
    case []:
      cs
    case +a <> +rest:
      Ct.all(rest, k, Nat.add(i, 1n), ss,
        Ct.with(rest, k, i, Nat.add(i, 1n), a, Ct.withfix(ss, k, i, 0n, a, Ct.floor(k, i, a, cs))))

# Impulses
# --------
# At a contact, the push along the normal that keeps the two from
# closing in more than the gap over the tick (a body in contact moves by
# twice its end velocity), added to what was pushed before and never
# below 0: a contact only ever pushes. Then the friction, against the
# sliding at that point, never more than mu times the push (Coulomb).
# Every impulse goes to both sides, the same and opposite, at the same
# point.

# How far apart two cubes are, the one way both the contacts and the gate
# ask it: the most they are apart along any of the fifteen directions
# (the six axes and the nine edge by edge ones). Below 0 is overlapping;
# touching (0) is not. The gate once asked phys.bend's test while the
# contacts asked this one; the two round differently by a few units, and
# a body the impulses let slide along a wall was refused by the gate, and
# hung there.
def R.gap(+s: Nat, +a: P.Body, +b: P.Body) -> P.Z:
  +h = Nat.div(s, 2n)
  +d = B.d(a, b)
  +ma = P.Rot.mat(B.q(a))
  +mb = P.Rot.mat(B.q(b))
  +ea = Ct.half(h, ma)
  +eb = Ct.half(h, mb)
  Sup.hi(Fx.sep(Ct.faces(d, ea, eb, ma, mb)), R.exsep(Ct.edges9(d, ea, eb, ma, mb)))

def R.hits2(flat: Bool, +s: Nat, +p: P.Body, +o: P.Body) -> Bool:
  match flat:
    case True{}:
      P.Geo.hits(s, P.Body.x(p), P.Body.y(p), P.Body.z(p), B.q(p), o)
    case False{}:
      P.Z.above(P.Neg{R.slop(s)}, R.gap(s, p, o))

# a body as the gate sees it: where it is and how it is turned, nothing
# else -- so that nothing else can change what it sees (rg_hits_*)
def R.bare(+b: P.Body) -> P.Body:
  P.Body{P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}, P.Rot{B.q(b), V.zero()}}

# a body at p against one other: overlapping? Two cubes square with the
# world are two boxes, and that is asked exactly. Two cubes whose middles
# are 2 s apart along some axis cannot overlap (a cube reaches
# s sqrt(3) / 2 from its middle): the fifteen directions are only worked
# out for the ones nearer than that.
def R.hits4(near: Bool, +s: Nat, +p: P.Body, +o: P.Body) -> Bool:
  match near:
    case False{}:
      False{}
    case True{}:
      R.hits2(Bool.and(P.Quat.flat(B.q(p)), P.Quat.flat(B.q(o))), s, R.bare(p), R.bare(o))

def R.hits(+s: Nat, +p: P.Body, +o: P.Body) -> Bool:
  R.hits4(Ct.near(s, 0n, B.d(p, o)), s, p, o)

def Mv.clear(+s: Nat, +p: P.Body, obs: List<&2, P.Body>) -> Bool:
  match obs:
    case []:
      True{}
    case +o <> rest:
      Bool.and(Bool.not(R.hits(s, p, o)), Mv.clear(s, p, rest))

# above the floor, the way the floor's contacts measure it: the lowest
# corner (the middle less the half edges' heights) no lower than the slop
# under 0. Asked with phys.bend's sag instead, a turned body the floor's
# contacts had 16 units up was already under the floor for the gate, and
# every move it made was refused.
def Mv.floor2(e: E3, +s: Nat, +y: Nat) -> Bool:
  E3{+e0, +e1, +e2} = e
  Nat.is_le(Nat.add(Nat.add(P.Z.mag(P.Wv.y(e0)), P.Z.mag(P.Wv.y(e1))), P.Z.mag(P.Wv.y(e2))),
    Nat.add(Nat.add(y, Nat.div(s, 2n)), R.slop(s)))

def Mv.floor(+s: Nat, +p: P.Body) -> Bool:
  Mv.floor2(Ct.half(Nat.div(s, 2n), P.Rot.mat(B.q(p))), s, P.Body.y(p))

def Mv.fits(+s: Nat, +p: P.Body, obs: List<&2, P.Body>) -> Bool:
  Bool.and(Mv.floor(s, p), Mv.clear(s, p, obs))

# the move d with what goes into the contacts taken out: less its part
# along u (the way what it touches pushes it) where that part is negative
def Mv.slide(+d: P.Wv, +u: P.Wv) -> P.Wv:
  +t = P.Z.divn(V.dot(d, u), 65536n)
  R.pv(P.Z.above(P.Pos{0n}, t), V.sub(d, V.fx(u, t)), d)

# How a body is turned: the turning w is in the world's axes (the angular
# momentum is r x J, arms and impulses as they lie in the world), so the
# turn of a tick goes on the left of the orientation: step(w) q, not
# q step(w). Composed on the right it turned a tilted cube about its own
# axes instead, the impulses planned one motion and the body made another,
# and the gate kept refusing what they asked. No turn leaves the body
# exactly as it is turned: the product set back to unit length moved a
# component of some orientations by one part in 2^15, which swings a corner
# a dozen units, and a cube that was not turning at all was turned into its
# neighbour -- every fall refused, and it hung in the air.
def R.turn2(still: Bool, +q: P.Quat, +w: P.Wv) -> P.Quat:
  match still:
    case True{}:
      q
    case False{}:
      P.Quat.unit(P.Quat.mul(P.Quat.step(w, P.Wv.mag(w)), q))

def R.turn(+q: P.Quat, +w: P.Wv) -> P.Quat:
  R.turn2(P.Wv.null(w), q, w)

# What goes with a body's move: u, the way to slide it off what it
# touches; du, the way out of the contact it is deepest in; pr, the arm
# of the contact it turns about (the one that carries the most), if piv.
type Mc is Data:
  Mc{u: P.Wv, du: P.Wv, pr: P.Wv, piv: Bool}

def Mc.u(+m: Mc) -> P.Wv:
  Mc{u, du, pr, piv} = m
  u

def Mc.du(+m: Mc) -> P.Wv:
  Mc{u, du, pr, piv} = m
  du

# A body held somewhere turns about that point, not about its middle.
# Moving the middle by twice its velocity and turning about the middle is
# right to first order; over the tick the pivot goes round an arc and
# drifts off by the arc's sag, and a pivot that sinks into what holds it
# is refused by the gate, one that rises makes energy. So the pivot is
# moved by exactly what the impulses made its velocity -- twice the
# turning's part of it here, the middle's part being in the move -- and
# the middle put where the turned body's arm r1 reaches it from there:
# r0 + 2 (w x r) - r1. The arm is taken into the body and back out by
# both orientations the same way (r0 by the first, r1 by the second), so
# that no turn is exactly no correction: set against r itself, the
# rounding of that round trip (some 15 units on an arm of a side) pushed a
# cube leaning on a wall into it every tick, every pose was refused, and
# it hung on the wall.
def Mv.arm(+m0: P.Mat, +m: P.Mat, +r: P.Wv) -> P.Wv:
  V.add(V.add(V.fx(M.r0(m), Ct.loc(r, M.r0(m0))), V.fx(M.r1(m), Ct.loc(r, M.r1(m0)))), V.fx(M.r2(m), Ct.loc(r, M.r2(m0))))

def Mv.corr(+k: P.K, +r: P.Wv, +l: P.Wv, +q0: P.Quat, +q1: P.Quat) -> P.Wv:
  +m0 = P.Rot.mat(q0)
  +wr = V.sub(B.at(k, P.Body{0n, 0n, 0n, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}, P.Rot{q0, l}}, r), V.zero())
  V.sub(V.add(Mv.arm(m0, m0, r), V.add(wr, wr)), Mv.arm(m0, P.Rot.mat(q1), r))

# the pose after moving d and turning by w, each cut by 2^c, about the
# pivot if there is one
def Mv.pose(+k: P.K, +b: P.Body, +d: P.Wv, +w: P.Wv, +c: Nat, +mc: Mc) -> P.Body:
  Mc{u, du, +pr, +piv} = mc
  +f = Nat.pow(2n, c)
  +wc = V.divn(w, f)
  +q1 = R.turn(B.q(b), wc)
  +dc = V.add(V.divn(d, f), R.pv(piv, Mv.corr(k, pr, V.divn(B.L(b), f), B.q(b), q1), V.zero()))
  P.Body{P.Z.shift(P.Body.x(b), P.Wv.x(dc)), P.Z.shift(P.Body.y(b), P.Wv.y(dc)),
    P.Z.shift(P.Body.z(b), P.Wv.z(dc)), P.Body.vx(b), P.Body.vy(b), P.Body.vz(b), P.Body.ground(b),
    P.Body.hit(b), P.Rot{q1, B.L(b)}}

# the i-th pose tried: the whole move; slid off the contacts; then that
# cut by 2, 4, ...
def Mv.cand(+i: Nat, +k: P.K, +b: P.Body, +d: P.Wv, +w: P.Wv, +mc: Mc) -> P.Body:
  Mv.pose(k, b, R.pv(Nat.is_eq(i, 0n), d, Mv.slide(d, Mc.u(mc))), w, Nat.sub(i, 1n), mc)

def Mv.stay(+b: P.Body) -> P.Body:
  P.Body{P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, P.Body.ground(b), True{},
    P.Rot{B.q(b), V.zero()}}

def Mv.ok(+k: P.K, +p: P.Body, +obs: List<&2, P.Body>) -> Bool:
  Mv.fits(P.K.size(k), p, obs)

# Every pose refused: the body is caught against what it touches within
# the rounding of the fifteen axes, the impulses asking it to go where the
# test will not let it. It steps away from what it touches -- 16 units,
# then 64, then 256 -- and only if none of those is clear does it stay,
# knocked still. Staying was a body hanging in the air for good.
def Mv.off(+b: P.Body, +u: P.Wv, +a: Nat) -> P.Body:
  +dc = V.fx(u, P.Pos{a})
  P.Body{P.Z.shift(P.Body.x(b), P.Wv.x(dc)), P.Z.shift(P.Body.y(b), P.Wv.y(dc)), P.Z.shift(P.Body.z(b), P.Wv.z(dc)),
    P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, P.Body.ground(b), True{}, P.Rot{B.q(b), V.zero()}}

def Mv.flee(n: Nat, ok: Bool, +k: P.K, +b: P.Body, +u: P.Wv, +a: Nat, +obs: List<&2, P.Body>) -> P.Body:
  match n ok:
    case _ True{}:
      Mv.off(b, u, a)
    case 0n False{}:
      Mv.stay(b)
    case 1n+m False{}:
      Mv.flee(m, Mv.ok(k, Mv.off(b, u, Nat.mul(a, 4n)), obs), k, b, u, Nat.mul(a, 4n), obs)

# p is the i-th pose, ok whether it is clear; n more to try
# the velocity and turning a body keeps after its i-th pose was the one
# that went through: all of it for the whole move; slid off its
# contacts, without what went into them; cut by 2^c, that much less. A
# move the world only let through in part is a knock, and a body kept a
# velocity its place would not let it use -- stuck against what stopped
# it and gathering speed it could never spend. One that only an eighth of
# its move or less fits (i from 4) ran into what stops it, and stops: a
# cube wedged at a slant kept a sliver of its velocity every tick, never
# at rest, and the heap it was in never slept.
def Mv.keep(+i: Nat, +p: P.Body, +u: P.Wv) -> P.Body:
  +f = Nat.pow(2n, Nat.sub(i, 1n))
  +stop = Nat.is_le(4n, i)
  +v = R.pv(Nat.is_eq(i, 0n), B.v(p), R.pv(stop, V.zero(), V.divn(Mv.slide(B.v(p), u), f)))
  B.set(p, v, R.pv(stop, V.zero(), R.pv(Nat.is_lt(i, 2n), B.L(p), V.divn(B.L(p), f))))

def Mv.try(n: Nat, ok: Bool, +i: Nat, +k: P.K, +b: P.Body, +d: P.Wv, +w: P.Wv, +mc: Mc, +obs: List<&2, P.Body>,
  +p: P.Body) -> P.Body:
  match n ok:
    case _ True{}:
      Mv.keep(i, p, Mc.u(mc))
    case 0n False{}:
      Mv.flee(3n, Mv.ok(k, Mv.off(b, Mc.du(mc), 16n), obs), k, b, Mc.du(mc), 16n, obs)
    case 1n+m False{}:
      Mv.try(m, Mv.ok(k, Mv.cand(Nat.add(i, 1n), k, b, d, w, mc), obs), Nat.add(i, 1n), k, b, d, w, mc, obs,
        Mv.cand(Nat.add(i, 1n), k, b, d, w, mc))

# Rest: a body held from below with its middle over what holds it, and
# only a little velocity and turning left from the impulses, is at rest:
# exactly still, and does not move this tick. A body whose middle hangs
# past its support gets nothing of the kind, and goes on tipping.
# small: what the impulses leave of gravity on a body that rests -- up to
# two ticks of gravity, and the turning that moves a corner that much (a
# corner goes at w s sqrt(3)/2 = 3 sqrt(3) L / s: L up to g s / 3 moves it
# 1.7 g). A
# body is at rest only if it was that still when the tick began too: the
# motor's push on a player standing still is under it once friction has
# had its share, and took the player for a body at rest.
def Mv.small(+k: P.K, +b: P.Body) -> Bool:
  Bool.and(Nat.is_le(V.l1(B.v(b)), Nat.mul(2n, P.K.g(k))),
    Nat.is_le(V.l1(B.L(b)), Nat.div(Nat.mul(P.K.g(k), P.K.size(k)), 3n)))

def Mv.flags(+b: P.Body, +gr: Bool, +hit: Bool) -> P.Body:
  P.Body{P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Body.vx(b), P.Body.vy(b), P.Body.vz(b), gr, hit, P.Body.rot(b)}

# The poses, in turn: the whole move; the move less what goes into the
# contacts; that, without the turn; then the move with its turn halved,
# again and again. A turn swings the corners, and a body leaning on a wall
# can have every turning pose refused while the straight move is clear:
# with the turn in every try, it only got the last sliver of a move each
# tick, and hung on the wall. A pose without the turn has its turning
# stopped (the turn is what was refused), and no pivot to turn about.
def Mv.flat3(ok: Bool, +k: P.K, +b1: P.Body, +d: P.Wv, +w: P.Wv, +mc: Mc, +obs: List<&2, P.Body>, +p: P.Body) -> P.Body:
  match ok:
    case True{}:
      B.set(p, Mv.slide(B.v(p), Mc.u(mc)), V.zero())
    case False{}:
      Mv.try(6n, Mv.ok(k, Mv.cand(2n, k, b1, d, w, mc), obs), 2n, k, b1, d, w, mc, obs, Mv.cand(2n, k, b1, d, w, mc))

def Mv.flat2(+k: P.K, +b1: P.Body, +d: P.Wv, +w: P.Wv, +mc: Mc, +obs: List<&2, P.Body>, +p: P.Body) -> P.Body:
  Mv.flat3(Mv.ok(k, p, obs), k, b1, d, w, mc, obs, p)

def Mv.flat(+k: P.K, +b1: P.Body, +d: P.Wv, +w: P.Wv, +mc: Mc, +obs: List<&2, P.Body>) -> P.Body:
  Mc{+u, du, pr, piv} = mc
  Mv.flat2(k, b1, d, w, Mc{u, du, pr, piv}, obs, Mv.pose(k, b1, Mv.slide(d, u), V.zero(), 0n, Mc{u, du, pr, False{}}))

def Mv.go3(n: Nat, ok: Bool, +k: P.K, +b1: P.Body, +d: P.Wv, +w: P.Wv, +mc: Mc, +obs: List<&2, P.Body>, +i: Nat, +p: P.Body)
  -> P.Body:
  match n ok:
    case _ True{}:
      Mv.keep(i, p, Mc.u(mc))
    case 0n False{}:
      Mv.flat(k, b1, d, w, mc, obs)
    case 1n+m False{}:
      Mv.go3(m, Mv.ok(k, Mv.cand(Nat.add(i, 1n), k, b1, d, w, mc), obs), k, b1, d, w, mc, obs, Nat.add(i, 1n),
        Mv.cand(Nat.add(i, 1n), k, b1, d, w, mc))

def Mv.go2(+k: P.K, +b1: P.Body, +d: P.Wv, +w: P.Wv, +mc: Mc, +obs: List<&2, P.Body>) -> P.Body:
  Mv.go3(1n, Mv.ok(k, Mv.cand(0n, k, b1, d, w, mc), obs), k, b1, d, w, mc, obs, 0n, Mv.cand(0n, k, b1, d, w, mc))

# A cube is the same cube turned by any of the 24 turns that map it onto
# itself. At rest, one that lies within a hair of such a turn (each of its
# axes within 8 parts in 2^16 of an axis of the world) is set square with
# the world, where that is clear: a cube that tipped over onto a face is
# square again, and can sleep.
def Mv.axis(+r: P.Wv) -> Bool:
  Bool.or(Nat.is_le(65528n, P.Z.mag(P.Wv.x(r))), Bool.or(Nat.is_le(65528n, P.Z.mag(P.Wv.y(r))),
    Nat.is_le(65528n, P.Z.mag(P.Wv.z(r)))))

def Mv.square(+q: P.Quat) -> Bool:
  +m = P.Rot.mat(q)
  Bool.and(Mv.axis(M.r0(m)), Bool.and(Mv.axis(M.r1(m)), Mv.axis(M.r2(m))))

def Mv.canon2(ok: Bool, +b: P.Body) -> P.Body:
  match ok:
    case True{}:
      P.Body{P.Body.x(b), P.Body.y(b), P.Body.z(b), P.Body.vx(b), P.Body.vy(b), P.Body.vz(b), P.Body.ground(b),
        P.Body.hit(b), P.Rot{P.Quat.one(), B.L(b)}}
    case False{}:
      b

def Mv.canon(+k: P.K, +b: P.Body, +obs: List<&2, P.Body>) -> P.Body:
  Mv.canon2(Bool.and(Mv.square(B.q(b)), Mv.fits(P.K.size(k), Mv.canon2(True{}, b), obs)), b)

def Mv.go(still: Bool, +k: P.K, +b0: P.Body, +b1: P.Body, +obs: List<&2, P.Body>, free: Bool, +mc: Mc) -> P.Body:
  match still:
    case True{}:
      Mv.canon(k, B.set(b1, V.zero(), V.zero()), obs)
    case False{}:
      Mv.go2(k, b1, R.pv(free, V.add(B.v(b0), B.v(b1)), V.add(B.v(b1), B.v(b1))), Mv.w(k, B.L(b1)), mc, obs)

# the body at i: b0 as it started the tick, b1 with the velocities the
# impulses left it, obs everything else as it is now
# What a body is already inside when the tick starts does not stop its
# move: the impulses push the two apart (a contact with a gap below 0
# asks for them to open up), and a gate that refused every pose still
# inside froze them there for good. A move is only ever stopped by what
# it runs into; a body that starts clear of everything is gated against
# everything, exactly as before.
def Mv.apart(+s: Nat, +b: P.Body, obs: List<&2, P.Body>) -> List<&2, P.Body>:
  match obs:
    case []:
      []
    case +o <> rest:
      R.keep(Bool.not(R.hits(s, b, o)), o, Mv.apart(s, b, rest))

# Held: something the body touches, with a face that looks up, pushed it
# this tick -- the floor, a cube under it, the edge it leans on, the side
# of the notch it is wedged in. A wall does not hold: its face looks
# sideways. The player walks and jumps only off what holds it. Touched:
# some contact pushed, even one still a gap away that only kept the body
# from closing in too fast.
type Hd is Data:
  Hd{pn: Bool, t: Bool}

def Hd.add2(+f: P.Wv, +jn: Nat, +touching: Bool, +pushed: Bool, h: Hd) -> Hd:
  Hd{pn, t} = h
  Hd{Bool.or(pn, Bool.and(touching, Bool.and(P.Z.above(P.Wv.y(f), P.Pos{0n}), Nat.is_lt(0n, jn)))), Bool.or(t, pushed)}

def Hd.add1(mine: Bool, +asa: Bool, +n: P.Wv, +gap: P.Z, +jn: Nat, +jt: P.Wv, +sk: P.Z, h: Hd) -> Hd:
  match mine:
    case False{}:
      h
    case True{}:
      Hd.add2(R.pv(asa, n, V.opp(n)), jn, R.zle2(gap, sk), Bool.or(Nat.is_lt(0n, jn), Nat.is_lt(0n, V.l1(jt))), h)

def Hd.of(+sk: P.Z, +i: Nat, cs: List<&2, Ct>, h: Hd) -> Hd:
  match cs:
    case []:
      h
    case Ct{+a, +b, +fl, ra, rb, +n, +gap, +jn, +jt} <> rest:
      +asa = Nat.is_eq(a, i)
      Hd.of(sk, i, rest, Hd.add1(Bool.or(asa, Bool.and(Bool.not(fl), Nat.is_eq(b, i))), asa, n, gap, jn, jt, sk, h))

def Hd.t(h: Hd) -> Bool:
  Hd{pn, t} = h
  t

def Hd.held(h: Hd) -> Bool:
  Hd{pn, t} = h
  pn

# the body at rest if it is (balanced, and only a little velocity and
# turning left before and after the impulses), else moved; with its
# flags: held, touched
def Mv.one(+k: P.K, +b0: P.Body, +b1: P.Body, +obs: List<&2, P.Body>, +su: Sup, +hd: Hd) -> P.Body:
  Mv.flags(Mv.go(Bool.and(Sup.balanced(su), Bool.and(Mv.small(k, b0), Mv.small(k, b1))), k, b0, b1, Mv.apart(P.K.size(k), b1, obs),
    Bool.not(Hd.t(hd)), Mc{Mv.away(Sup.nn(su)), Sup.dn(su), Sup.pr(su), Sup.pivots(su)}), Hd.held(hd), Hd.t(hd))

# What touches a body. The contact of it that pushed and is least apart
# must touch (apart by no more than the slop), else the body is not held
# at all: a contact still a gap away, pushing only so that the body does
# not close in too fast, is no support -- a body at rest on it would stay
# that far up for good. The contacts that pushed within twice the slop of
# that one all touch: a cube lying on its face a hair off square (the
# rounding of its turns) has two corners down and two a few dozen units
# up, and all four hold it. cut: the most apart a touching contact is.
def Mv.low(+i: Nat, cs: List<&2, Ct>, +m: P.Z) -> P.Z:
  match cs:
    case []:
      m
    case Ct{+a, +b, +fl, ra, rb, n, +gap, +jn, +jt} <> rest:
      +mine = Bool.or(Nat.is_eq(a, i), Bool.and(Bool.not(fl), Nat.is_eq(b, i)))
      +pushed = Bool.or(Nat.is_lt(0n, jn), Nat.is_lt(0n, V.l1(jt)))
      Mv.low(i, rest, R.pz(Bool.and(Bool.and(mine, pushed), P.Z.above(m, gap)), gap, m))

def Mv.cut2(+s: Nat, +lo: P.Z) -> P.Z:
  R.pz(R.zle2(lo, P.Pos{R.slop(s)}), P.Z.add(lo, P.Pos{Nat.mul(2n, R.slop(s))}), P.Neg{1073741824n})

def Mv.cut(+s: Nat, +i: Nat, cs: List<&2, Ct>) -> P.Z:
  Mv.cut2(s, Mv.low(i, cs, P.Pos{1073741824n}))

def Mv.put(+i: Nat, +b: P.Body, cur: List<&2, P.Body>) -> List<&2, P.Body>:
  Bs.put(cur, i, b)

def Mv.all(n: Nat, +k: P.K, +i: Nat, +b0s: List<&2, P.Body>, +cur: List<&2, P.Body>, +ss: List<&2, P.Body>,
  +cs: List<&2, Ct>) -> List<&2, P.Body>:
  match n:
    case 0n:
      cur
    case 1n+m:
      Mv.all(m, k, Nat.add(i, 1n), b0s,
        Mv.put(i, Mv.one(k, Bs.at(b0s, i), Bs.at(cur, i), List.append(&2, P.Body, Bs.drop(cur, i), ss),
          Sup.of(Mv.cut(P.K.size(k), i, cs), i, cs, Sup.none()), Hd.of(Mv.cut(P.K.size(k), i, cs), i, cs, Hd{False{}, False{}})), cur), ss, cs)

# The tick of an island
# ---------------------

def Rb.fall(+k: P.K, bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match bs:
    case []:
      []
    case +b <> rest:
      B.set(b, V.sub(B.v(b), P.Wv{P.Pos{0n}, P.Pos{P.K.g(k)}, P.Pos{0n}}), B.L(b)) <> Rb.fall(k, rest)

def Rb.done(st: St) -> List<&2, Ct>:
  St{done, bs} = st
  done

def Rb.bodies(st: St) -> List<&2, P.Body>:
  St{done, bs} = st
  bs

# Waking: a fixed body some contact pushed sideways, or hit hard (more
# than eight times a body's weight in a tick), wakes -- it is no longer
# held where it is. What only rests its weight on it does not wake it.
def Rb.woke1(+j: Nat, +g: Nat, c: Ct) -> Bool:
  Ct{a, b, +fl, ra, rb, +n, gap, +jn, +jt} = c
  +jh = V.add(V.fx(n, P.Pos{jn}), jt)
  Bool.and(Bool.and(fl, Nat.is_eq(b, Nat.add(j, 1n))),
    Bool.or(Nat.is_lt(Nat.div(g, 2n), Nat.add(P.Z.mag(P.Wv.x(jh)), P.Z.mag(P.Wv.z(jh)))), Nat.is_lt(Nat.mul(8n, g), jn)))

def Rb.woke(+j: Nat, +g: Nat, cs: List<&2, Ct>) -> Bool:
  match cs:
    case []:
      False{}
    case +c <> rest:
      Bool.or(Rb.woke1(j, g, c), Rb.woke(j, g, rest))

def Rb.wakes(ss: List<&2, P.Body>, +j: Nat, +g: Nat, +cs: List<&2, Ct>) -> List<&2, P.Body>:
  match ss:
    case []:
      []
    case +b <> rest:
      R.keep(Rb.woke(j, g, cs), b, Rb.wakes(rest, Nat.add(j, 1n), g, cs))

# what a tick of an island hands back: the bodies that move, where they
# went, and the fixed ones it woke
type Rs is Data:
  Rs{bs: List<&2, P.Body>, woke: List<&2, P.Body>}

# The energy of a body, for the gate: v^2 + 6 L^2 / s^2 + g y -- what a
# free flight keeps exactly (the kinetic energy of its moving and of its
# turning, and its height), counted from a height y0 so that the numbers
# stay small; the turning is worked out on L / 256.
def En.rot(+s: Nat, +l: P.Wv) -> Nat:
  Nat.div(Nat.mul(6n, V.sq(V.divn(l, 256n))), P.Pick.high(Nat.div(Nat.mul(s, s), 65536n), 1n))

def En.one(+k: P.K, +y0: Nat, +b: P.Body) -> Nat:
  Nat.add(Nat.add(V.sq(B.v(b)), En.rot(P.K.size(k), B.L(b))), Nat.mul(P.K.g(k), Nat.sub(P.Body.y(b), y0)))

# the energy of bs, each counted from where it started (b0s); the lowest
# a body can go in a tick is under its start, so the heights are taken
# from the start less a whole side
def En.all(+k: P.K, b0s: List<&2, P.Body>, bs: List<&2, P.Body>) -> Nat:
  match b0s bs:
    case Nil{} _:
      0n
    case +a <> ra Nil{}:
      0n
    case +a <> ra +b <> rb:
      Nat.add(En.one(k, Nat.sub(P.Body.y(a), P.K.size(k)), b), En.all(k, ra, rb))

# the kinetic energy of bs (v^2 + 6 L^2 / s^2), and the height energy
# of bs over b0s (g y, each from its start less a side)
def En.kin(+k: P.K, bs: List<&2, P.Body>) -> Nat:
  match bs:
    case []:
      0n
    case +b <> rest:
      Nat.add(Nat.add(V.sq(B.v(b)), En.rot(P.K.size(k), B.L(b))), En.kin(k, rest))

# every body's velocity and turning times r / 2^16
def En.scale(bs: List<&2, P.Body>, +r: Nat) -> List<&2, P.Body>:
  match bs:
    case []:
      []
    case +b <> rest:
      B.set(b, V.divn(V.mulz(B.v(b), P.Pos{r}), 65536n), V.divn(V.mulz(B.L(b), P.Pos{r}), 65536n)) <> En.scale(rest, r)

def En.still(bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match bs:
    case []:
      []
    case +b <> rest:
      B.set(b, V.zero(), V.zero()) <> En.still(rest)

def En.cut4(ok: Bool, +b0s: List<&2, P.Body>, +bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match ok:
    case True{}:
      bs
    case False{}:
      En.still(b0s)

def En.cut3(+k: P.K, +b0s: List<&2, P.Body>, +e0: Nat, +bs: List<&2, P.Body>) -> List<&2, P.Body>:
  En.cut4(Nat.is_le(En.all(k, b0s, bs), e0), b0s, bs)

# The energy gate. A tick of an island, with no one driving it, never
# ends with more energy than it began with. Whatever the impulses, the
# lifts off the edges and the rounding of the turns gave, the excess is
# taken out of the moving, and only that: every velocity and turning is
# cut by sqrt((K - excess) / K), rounded down, K the kinetic energy --
# a friction that spends exactly what was made. (Halving everything the
# moment a few units were made stopped a cube tipping over an edge dead,
# and the player with it.) If the height gained is more than all the
# moving there is, the bodies stay where they began, still.
def En.cut2(ok: Bool, +k: P.K, +b0s: List<&2, P.Body>, +e0: Nat, +bs: List<&2, P.Body>, +kin: Nat, +over: Nat)
  -> List<&2, P.Body>:
  match ok:
    case False{}:
      En.still(b0s)
    case True{}:
      En.cut3(k, b0s, e0, En.scale(bs, P.Fric.floor(Nat.mul(Nat.div(Nat.mul(Nat.sub(kin, over), 65536n), P.Pick.high(kin, 1n)), 65536n),
        65536n)))

def En.gate(over: Bool, +k: P.K, +b0s: List<&2, P.Body>, +e0: Nat, +e1: Nat, +bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match over:
    case False{}:
      bs
    case True{}:
      En.cut2(Nat.is_lt(Nat.sub(e1, e0), En.kin(k, bs)), k, b0s, e0, bs, En.kin(k, bs), Nat.sub(e1, e0))

# is some contact further in than the skin? Then the tick is pushing two
# bodies out of each other -- a correction, not a motion, and what it
# costs in energy is not the gate's to refuse: refusing it left the two
# inside each other for good
def Rb.deep(+s: Nat, cs: List<&2, Ct>) -> Bool:
  match cs:
    case []:
      False{}
    case Ct{a, b, fl, ra, rb, n, +gap, jn, jt} <> rest:
      Bool.or(P.Z.above(P.Neg{R.skin(s)}, gap), Rb.deep(s, rest))

# the bodies moved and gated, energy and all
def Rb.moved(+k: P.K, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>, st: St) -> List<&2, P.Body>:
  St{+done, +bs1} = st
  Mv.all(List.length(&2, P.Body, bs), k, 0n, bs, bs1, ss, done)

# was some contact of the tick deeper than the skin?
def Rb.deepof(+s: Nat, st: St) -> Bool:
  St{done, bs1} = st
  Rb.deep(s, done)

# the energy gate on the moved bodies (see En.gate): none when a contact
# was deeper than the skin, where pushing the pair apart is what the
# energy went into
def Rb.egate(+k: P.K, +bs: List<&2, P.Body>, deep: Bool, +moved: List<&2, P.Body>) -> List<&2, P.Body>:
  +e0 = En.all(k, bs, bs)
  +e1 = En.all(k, bs, moved)
  En.gate(Bool.and(Bool.not(deep), Nat.is_lt(e0, e1)), k, bs, e0, e1, moved)

def Rb.out(+k: P.K, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>, +st: St) -> List<&2, P.Body>:
  Rb.egate(k, bs, Rb.deepof(P.K.size(k), st), Rb.moved(k, bs, ss, st))

def Rb.wokeof(+k: P.K, +ss: List<&2, P.Body>, st: St) -> List<&2, P.Body>:
  St{done, bs1} = st
  Rb.wakes(ss, 0n, P.K.g(k), done)

# Apart: no two of bs overlap, none overlaps one of the fixed ss, none is
# under the floor -- by the gate's own tests (the fifteen directions, the
# floor's corners)
def Rb.apart(+s: Nat, bs: List<&2, P.Body>, +ss: List<&2, P.Body>) -> Bool:
  match bs:
    case []:
      True{}
    case +b <> +rest:
      Bool.and(Mv.fits(s, b, List.append(&2, P.Body, rest, ss)), Rb.apart(s, rest, ss))

# The island's end, checked. Every pose went through the gate, so bodies
# that began apart end apart; were they not, the tick would leave them
# where they began, still -- the law (rigid_apart) rests on this check, and
# no run has ever reached its other side. An island that began with an
# overlap is handed on as the tick left it.
def Rb.kept3(was: Bool, +bs: List<&2, P.Body>, +out: List<&2, P.Body>) -> List<&2, P.Body>:
  match was:
    case True{}:
      En.still(bs)
    case False{}:
      out

def Rb.kept2(ok: Bool, +s: Nat, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>, +out: List<&2, P.Body>) -> List<&2, P.Body>:
  match ok:
    case True{}:
      out
    case False{}:
      Rb.kept3(Rb.apart(s, bs, ss), bs, out)

def Rb.checked(+s: Nat, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>, +out: List<&2, P.Body>) -> List<&2, P.Body>:
  Rb.kept2(Rb.apart(s, out, ss), s, bs, ss, out)

def Rb.step2(+k: P.K, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>, +st: St) -> Rs:
  Rs{Rb.checked(P.K.size(k), bs, ss, Rb.out(k, bs, ss, st)), Rb.wokeof(k, ss, st)}

def Rs.bs(r: Rs) -> List<&2, P.Body>:
  Rs{bs, woke} = r
  bs

def Rs.woke(r: Rs) -> List<&2, P.Body>:
  Rs{bs, woke} = r
  woke

# the tick of bodies with nothing fixed around them
# the tick of the bodies bs among the fixed ones ss
def Rb.tick(+k: P.K, +bs: List<&2, P.Body>, +ss: List<&2, P.Body>) -> Rs:
  Rb.step2(k, bs, ss, Imp.iter(16n, k, St{Ct.all(bs, k, 0n, ss, []), Rb.fall(k, bs)}))

def Rb.step(+k: P.K, +bs: List<&2, P.Body>) -> List<&2, P.Body>:
  Rs.bs(Rb.tick(k, bs, []))

# Islands
# -------
# Bodies that cannot touch in a tick cannot push each other either, so the
# island is cut into the groups that can: two bodies go together if their
# boxes come within the margin of each other (the fifteen directions say
# how far apart they are), and so does everything touching either. Each
# group is then its own tick, and a crowd falling apart is a thousand ticks
# of one body, not one tick of a thousand -- every impulse looks its two
# bodies up in a list, and a list of a thousand made each look a thousand
# steps.

# a pair of places
type Pr is Data:
  Pr{i: Nat, j: Nat}

# a body with its x and its place, for the sweep along x
type Xe is Data:
  Xe{x: Nat, i: Nat, b: P.Body}

def Xe.x(e: Xe) -> Nat:
  Xe{x, i, b} = e
  x

def Xe.i(+e: Xe) -> Nat:
  Xe{x, i, b} = e
  i

def Xe.b(+e: Xe) -> P.Body:
  Xe{x, i, b} = e
  b

def Is.le(a: Xe, b: Xe) -> Bool:
  Nat.is_le(Xe.x(a), Xe.x(b))

def Is.ents(bs: List<&2, P.Body>, +i: Nat) -> List<&2, Xe>:
  match bs:
    case []:
      []
    case +b <> rest:
      Xe{P.Body.x(b), i, b} <> Is.ents(rest, Nat.add(i, 1n))

# the x of the first entry, or past everything
def Is.hx(es: List<&2, Xe>) -> Nat:
  match es:
    case []:
      Nat.mul(4294967295n, 65536n)
    case +e <> rest:
      Xe.x(e)

# can a and b touch this tick? Near by their middles, and apart along
# the fifteen directions by no more than the pair's margin
def Is.cheb(+s: Nat, +d: P.Wv) -> P.Z:
  P.Z.sub(P.Pos{P.Pick.high(P.Z.mag(P.Wv.x(d)), P.Pick.high(P.Z.mag(P.Wv.y(d)), P.Z.mag(P.Wv.z(d))))}, P.Pos{s})

# two square cubes are apart by how far their middles are past a side;
# turned ones, by the fifteen directions
def Is.sep(flat: Bool, +s: Nat, +a: P.Body, +b: P.Body) -> P.Z:
  match flat:
    case True{}:
      Is.cheb(s, B.d(a, b))
    case False{}:
      R.gap(s, a, b)

def Is.near2(box: Bool, +k: P.K, +mg: Nat, +a: P.Body, +b: P.Body) -> Bool:
  match box:
    case False{}:
      False{}
    case True{}:
      R.zle2(Is.sep(Bool.and(P.Quat.flat(B.q(a)), P.Quat.flat(B.q(b))), P.K.size(k), a, b), P.Pos{mg})

def Is.near(+k: P.K, +a: P.Body, +b: P.Body) -> Bool:
  +mg = Ct.margin(k, B.v(a), B.v(b))
  Is.near2(Ct.near(P.K.size(k), mg, B.d(a, b)), k, mg, a, b)

def Is.pair_if(c: Bool, +i: Nat, +j: Nat, acc: List<&2, Pr>) -> List<&2, Pr>:
  match c:
    case True{}:
      Pr{i, j} <> acc
    case False{}:
      acc

# e against the entries after it, while they are within reach along x
# (stop says the next one is not)
def Is.ahead(rest: List<&2, Xe>, stop: Bool, +k: P.K, +reach: Nat, +e: Xe, acc: List<&2, Pr>)
  -> List<&2, Pr>:
  match rest stop:
    case _ True{}:
      acc
    case Nil{} False{}:
      acc
    case +f <> +more False{}:
      Is.ahead(more, Nat.is_le(Nat.add(Xe.x(e), reach), Is.hx(more)), k, reach, e,
        Is.pair_if(Is.near(k, Xe.b(e), Xe.b(f)), Xe.i(e), Xe.i(f), acc))

def Is.sweep(es: List<&2, Xe>, +k: P.K, +reach: Nat, acc: List<&2, Pr>) -> List<&2, Pr>:
  match es:
    case []:
      acc
    case +e <> +rest:
      Is.sweep(rest, k, reach, Is.ahead(rest, Nat.is_le(Nat.add(Xe.x(e), reach), Is.hx(rest)), k, reach, e, acc))

# the fastest any body goes (the margin of any pair is under what two of
# them can close)
def Is.vmax(bs: List<&2, P.Body>, +m: Nat) -> Nat:
  match bs:
    case []:
      m
    case +b <> rest:
      Is.vmax(rest, P.Pick.high(m, V.l1(B.v(b))))

# Labels: every body starts as its own; a pass over the pairs gives both
# of a pair the lesser of their two; passes go on while one changes
# something, and the bodies of an island end with one label.
type Lb is Type:
  Lb{a: Array<Nat>, ch: Bool}

def Lb.get(a: Array<Nat>, +i: Nat) -> Array<Nat> & Nat:
  Array.get(Nat, a, U32.from_nat(i))

def Lb.set2(r: Array<Nat> & Nat, +i: Nat, +j: Nat, +li: Nat, ch: Bool) -> Lb:
  (a, +lj) = r
  +m = P.Pick.low(li, lj)
  Lb{Array.set(Nat, Array.set(Nat, a, U32.from_nat(i), m), U32.from_nat(j), m), Bool.or(ch, Bool.not(Nat.is_eq(li, lj)))}

def Lb.set1(r: Array<Nat> & Nat, +i: Nat, +j: Nat, ch: Bool) -> Lb:
  (a, +li) = r
  Lb.set2(Lb.get(a, j), i, j, li, ch)

def Lb.step(p: Pr, st: Lb) -> Lb:
  Pr{+i, +j} = p
  Lb{a, ch} = st
  Lb.set1(Lb.get(a, i), i, j, ch)

def Lb.pass(ps: List<&2, Pr>, st: Lb) -> Lb:
  match ps:
    case []:
      st
    case +p <> rest:
      Lb.pass(rest, Lb.step(p, st))

def Lb.again2(ch: Bool, a: Array<Nat>, +ps: List<&2, Pr>) -> Lb:
  match ch:
    case True{}:
      Lb.pass(ps, Lb{a, False{}})
    case False{}:
      Lb{a, False{}}

def Lb.again(st: Lb, +ps: List<&2, Pr>) -> Lb:
  Lb{a, ch} = st
  Lb.again2(ch, a, ps)

def Lb.passes(n: Nat, st: Lb, +ps: List<&2, Pr>) -> Lb:
  match n:
    case 0n:
      st
    case 1n+m:
      Lb.passes(m, Lb.again(st, ps), ps)

def Lb.init(n: Nat, +i: Nat, a: Array<Nat>) -> Array<Nat>:
  match n:
    case 0n:
      a
    case 1n+m:
      Lb.init(m, Nat.add(i, 1n), Array.set(Nat, a, U32.from_nat(i), i))

# the depth of an array with room for n
def Lb.depth(fuel: Nat, +n: Nat, +k: Nat) -> Nat:
  match fuel:
    case 0n:
      k
    case 1n+f:
      P.Pick.n(Nat.is_le(n, Nat.pow(2n, k)), k, Lb.depth(f, n, Nat.add(k, 1n)))

# each body with its island's label
type Lab is Data:
  Lab{l: Nat, i: Nat, b: P.Body}

# by label and place, from the last: the runs come out reversed, so the
# first island is the one of place 0 (the player's) and each island keeps
# the order of the list
def Lab.le(a: Lab, b: Lab) -> Bool:
  Lab{+la, +ia, ba} = a
  Lab{+lb, +ib, bb} = b
  Bool.or(Nat.is_lt(lb, la), Bool.and(Nat.is_eq(la, lb), Nat.is_le(ib, ia)))

type LabSt is Type:
  LabSt{a: Array<Nat>, acc: List<&2, Lab>}

def Lab.step2(r: Array<Nat> & Nat, +i: Nat, +b: P.Body, acc: List<&2, Lab>) -> LabSt:
  (a, +l) = r
  LabSt{a, Lab{l, i, b} <> acc}

def Lab.step(+b: P.Body, st: LabSt, +i: Nat) -> LabSt:
  LabSt{a, acc} = st
  Lab.step2(Lb.get(a, i), i, b, acc)

def Lab.of(bs: List<&2, P.Body>, st: LabSt, +i: Nat) -> LabSt:
  match bs:
    case []:
      st
    case +b <> rest:
      Lab.of(rest, Lab.step(b, st, i), Nat.add(i, 1n))

def LabSt.acc(st: LabSt) -> List<&2, Lab>:
  LabSt{a, acc} = st
  acc

def Lb.a(st: Lb) -> Array<Nat>:
  Lb{a, ch} = st
  a

def Is.close(grp: List<&2, P.Body>, acc: List<&2, List<&2, P.Body>>) -> List<&2, List<&2, P.Body>>:
  match grp:
    case []:
      acc
    case +g <> gs:
      (g <> gs) <> acc

def Is.grp(same: Bool, +b: P.Body, grp: List<&2, P.Body>) -> List<&2, P.Body>:
  match same:
    case True{}:
      b <> grp
    case False{}:
      [b]

def Is.acc2(same: Bool, grp: List<&2, P.Body>, acc: List<&2, List<&2, P.Body>>) -> List<&2, List<&2, P.Body>>:
  match same:
    case True{}:
      acc
    case False{}:
      Is.close(grp, acc)

# the labelled bodies, sorted by label, cut into runs of one label
def Is.runs(ls: List<&2, Lab>, +cur: Nat, +grp: List<&2, P.Body>, acc: List<&2, List<&2, P.Body>>)
  -> List<&2, List<&2, P.Body>>:
  match ls:
    case []:
      Is.close(grp, acc)
    case Lab{+l, i, +b} <> rest:
      Is.runs(rest, l, Is.grp(Nat.is_eq(l, cur), b, grp), Is.acc2(Nat.is_eq(l, cur), grp, acc))

# the islands of bs: the groups of bodies that can touch one another
def Rb.islands(+k: P.K, +bs: List<&2, P.Body>) -> List<&2, List<&2, P.Body>>:
  +n = List.length(&2, P.Body, bs)
  +reach = Nat.add(Nat.add(Nat.mul(2n, P.K.size(k)), Nat.div(P.K.size(k), 64n)),
    Nat.add(Nat.mul(4n, Is.vmax(bs, 0n)), Nat.mul(2n, P.K.g(k))))
  +pairs = Is.sweep(List.sort(Xe, Is.le, Is.ents(bs, 0n)), k, reach, [])
  lab = Lb.passes(64n, Lb{Lb.init(n, 0n, Array.new(Nat, Lb.depth(20n, P.Pick.high(n, 1n), 0n), 0n)), True{}}, pairs)
  Is.runs(List.sort(Lab, Lab.le, LabSt.acc(Lab.of(bs, LabSt{Lb.a(lab), []}, 0n))), 4294967295n, [], [])

# the bodies of every island, each tagged with its island's number
def Is.tag(bs: List<&2, P.Body>, +n: Nat, acc: List<&2, Xe>) -> List<&2, Xe>:
  match bs:
    case []:
      acc
    case +b <> rest:
      Is.tag(rest, n, Xe{P.Body.x(b), n, b} <> acc)

def Is.tags(isl: List<&2, List<&2, P.Body>>, +n: Nat, acc: List<&2, Xe>) -> List<&2, Xe>:
  match isl:
    case []:
      acc
    case +i <> rest:
      Is.tags(rest, Nat.add(n, 1n), Is.tag(i, n, acc))

def Is.hit2(near: Bool, +s: Nat, +a: P.Body, +b: P.Body) -> Bool:
  match near:
    case False{}:
      False{}
    case True{}:
      R.hits(s, a, b)

# does e overlap an entry after it, of another island? (two cubes that
# overlap have middles closer than 2 s, and so corners too)
def Is.cross(rest: List<&2, Xe>, stop: Bool, +s: Nat, +e: Xe) -> Bool:
  match rest stop:
    case _ True{}:
      False{}
    case Nil{} False{}:
      False{}
    case +f <> +more False{}:
      Bool.or(Is.hit2(Bool.and(Bool.not(Nat.is_eq(Xe.i(e), Xe.i(f))), Ct.near(s, 0n, B.d(Xe.b(e), Xe.b(f)))), s, Xe.b(e), Xe.b(f)),
        Is.cross(more, Nat.is_le(Nat.add(Xe.x(e), Nat.mul(2n, s)), Is.hx(more)), s, e))

def Is.clash(es: List<&2, Xe>, +s: Nat) -> Bool:
  match es:
    case []:
      False{}
    case +e <> +rest:
      Bool.or(Is.cross(rest, Nat.is_le(Nat.add(Xe.x(e), Nat.mul(2n, s)), Is.hx(rest)), s, e), Is.clash(rest, s))

# do two bodies of different islands overlap? Each island's tick keeps
# its own bodies apart; this looks at the pairs no tick saw
def Rb.clash(+s: Nat, isl: List<&2, List<&2, P.Body>>) -> Bool:
  Is.clash(List.sort(Xe, Is.le, Is.tags(isl, 0n, [])), s)

def Ct.coulomb(+k: P.K, cs: List<&2, Ct>) -> Bool:
  match cs:
    case []:
      True{}
    case c <> rest:
      Bool.and(Ct.coul(k, c), Ct.coulomb(k, rest))

# Momentum
# --------
# along axis ax (0 x, 1 y, 2 z) of a list of bodies of mass 1: what goes
# one way (Mo.p) and what goes the other (Mo.n); the momentum is
# Mo.p - Mo.n, and a law about it moves the minus to the other side
def V.at(+ax: Nat, +v: P.Wv) -> P.Z:
  match ax:
    case 0n:
      P.Wv.x(v)
    case 1n+m:
      match m:
        case 0n:
          P.Wv.y(v)
        case 1n+o:
          P.Wv.z(v)

def Mo.p(+ax: Nat, bs: List<&2, P.Body>) -> Nat:
  match bs:
    case []:
      0n
    case +b <> rest:
      Nat.add(P.Z.pos(V.at(ax, B.v(b))), Mo.p(ax, rest))

def Mo.n(+ax: Nat, bs: List<&2, P.Body>) -> Nat:
  match bs:
    case []:
      0n
    case +b <> rest:
      Nat.add(P.Z.neg(V.at(ax, B.v(b))), Mo.n(ax, rest))
