# Cubo -- the world: an endless floor of 1 m cells, green cubes on it.
#
# Where the cubes are is a function of a random seed: every cell hashes to
# whether a stack of 1, 2 or 3 cubes stands on it (denser in some regions
# than in others, none around the start). The GPU computes the same
# function (effs/scene.comp) to draw them, so the untouched world costs
# nothing to keep or to send. A trie keeps only the cells that changed
# (a cube pushed away, or come to rest there); every other cell reads the
# generator. Cubes at rest sleep in their cells; a cube pushed, or left
# without support, wakes up and is simulated (phys.bend) until it rests
# again.

import Base
import ./phys.bend as P

def Pick.u(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Pick.n(c: Bool, +a: Nat, +b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

# a cube's side, 2^18 units (1 m)
def W.size() -> Nat:
  262144n

# the start's cell, 2^29 on both axes: the world reaches 2^29 cells (537
# thousand km) to every side of it
def W.origin() -> U32:
  536870912

def W.cell_of(+x: Nat) -> U32:
  U32.from_nat(Nat.div(x, W.size()))

def W.base(+c: U32) -> Nat:
  Nat.mul(U32.to_nat(c), W.size())

# Hashes (the same in effs/scene.comp)
# ------------------------------------

def Hash.mix(+h: U32) -> U32:
  +a = ((h .^. (h >> 16n)) * 2146121005 : U32)
  +b = ((a .^. (a >> 15n)) * 2221713035 : U32)
  (b .^. (b >> 16n) : U32)

def Hash.cell(+seed: U32, +cx: U32, +cz: U32) -> U32:
  Hash.mix((seed .^. Hash.mix((cx .^. Hash.mix((cz + 2654435769 : U32)) : U32)) : U32))

# The generator
# -------------

# how many cubes stand on cell (cx, cz): 0 to 3
def Gen.count(+seed: U32, +cx: U32, +cz: U32) -> U32:
  +rd = (Hash.cell(seed, (cx >> 4n : U32), (cz >> 4n : U32)) .&. 255 : U32)
  +dens = (6 + rd * 40 / 256 : U32)
  +h = Hash.cell((seed + 1 : U32), cx, cz)
  +hh = ((h >> 8n) .&. 255 : U32)
  +near = Bool.and(((cx - W.origin() + 3 : U32) < 6 : U32), ((cz - W.origin() + 3 : U32) < 6 : U32))
  Pick.u(Bool.or(near, ((h .&. 255 : U32) >= dens : U32)), 0, Pick.u((hh < 150 : U32), 1, Pick.u((hh < 225 : U32), 2, 3)))

# a cube at rest at (x, y, z)
def W.cube(+x: Nat, +y: Nat, +z: Nat) -> P.Body:
  P.Body{x, y, z, P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, True{}, False{}}

def Gen.stack(+n: Nat, +x: Nat, +z: Nat) -> List<&2, P.Body>:
  match n:
    case 0n:
      []
    case 1n+k:
      W.cube(x, Nat.mul(k, W.size()), z) <> Gen.stack(k, x, z)

# the cubes a cell was generated with
def Gen.cubes(+seed: U32, +cx: U32, +cz: U32) -> List<&2, P.Body>:
  Gen.stack(U32.to_nat(Gen.count(seed, cx, cz)), W.base(cx), W.base(cz))

# The cells
# ---------
# A trie over the 30 bits of a cell's x and z: a node splits on one bit of
# each. A leaf is a changed cell (its sleeping cubes); CGen, a region as
# generated.

type Cells is Data:
  CGen{}
  CLeaf{cubes: List<&2, P.Body>}
  CNode{a: Cells, b: Cells, c: Cells, d: Cells}

def W.bit(+c: U32, l: Nat) -> Bool:
  match l:
    case 0n:
      False{}
    case 1n+k:
      U32.is_eq(((c >> k) .&. 1 : U32), 1)

# the sleeping cubes of cell (cx, cz); l levels left, (bx, bz) the bits
# that choose among the node's children
def Cells.get(+l: Nat, t: Cells, +seed: U32, +cx: U32, +cz: U32, bx: Bool, bz: Bool) -> List<&2, P.Body>:
  match l t bx bz:
    case _ CGen{} _ _:
      Gen.cubes(seed, cx, cz)
    case _ CLeaf{cubes} _ _:
      cubes
    case 0n CNode{a, b, c, d} _ _:
      []
    case 1n+k CNode{a, b, c, d} False{} False{}:
      Cells.get(k, a, seed, cx, cz, W.bit(cx, k), W.bit(cz, k))
    case 1n+k CNode{a, b, c, d} True{} False{}:
      Cells.get(k, b, seed, cx, cz, W.bit(cx, k), W.bit(cz, k))
    case 1n+k CNode{a, b, c, d} False{} True{}:
      Cells.get(k, c, seed, cx, cz, W.bit(cx, k), W.bit(cz, k))
    case 1n+k CNode{a, b, c, d} True{} True{}:
      Cells.get(k, d, seed, cx, cz, W.bit(cx, k), W.bit(cz, k))

def Cells.levels() -> Nat:
  30n

def Cells.at(+t: Cells, +seed: U32, +cx: U32, +cz: U32) -> List<&2, P.Body>:
  Cells.get(Cells.levels(), t, seed, cx, cz, W.bit(cx, Cells.levels()), W.bit(cz, Cells.levels()))

# cell (cx, cz) set to cubes
def Cells.put(+l: Nat, t: Cells, +cx: U32, +cz: U32, cubes: List<&2, P.Body>, bx: Bool, bz: Bool) -> Cells:
  match l t bx bz:
    case 0n _ _ _:
      CLeaf{cubes}
    case 1n+k CNode{a, b, c, d} False{} False{}:
      CNode{Cells.put(k, a, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k)), b, c, d}
    case 1n+k CNode{a, b, c, d} True{} False{}:
      CNode{a, Cells.put(k, b, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k)), c, d}
    case 1n+k CNode{a, b, c, d} False{} True{}:
      CNode{a, b, Cells.put(k, c, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k)), d}
    case 1n+k CNode{a, b, c, d} True{} True{}:
      CNode{a, b, c, Cells.put(k, d, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k))}
    case 1n+k _ False{} False{}:
      CNode{Cells.put(k, CGen{}, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k)), CGen{}, CGen{}, CGen{}}
    case 1n+k _ True{} False{}:
      CNode{CGen{}, Cells.put(k, CGen{}, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k)), CGen{}, CGen{}}
    case 1n+k _ False{} True{}:
      CNode{CGen{}, CGen{}, Cells.put(k, CGen{}, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k)), CGen{}}
    case 1n+k _ True{} True{}:
      CNode{CGen{}, CGen{}, CGen{}, Cells.put(k, CGen{}, cx, cz, cubes, W.bit(cx, k), W.bit(cz, k))}

def Cells.set(t: Cells, +cx: U32, +cz: U32, cubes: List<&2, P.Body>) -> Cells:
  Cells.put(Cells.levels(), t, cx, cz, cubes, W.bit(cx, Cells.levels()), W.bit(cz, Cells.levels()))

# Around a body
# -------------

# How far a body can reach in a tick (in units): twice its speed on each
# axis (a tick moves it by v + v'), what the motor and gravity add, and a
# quarter of a metre to spare.
def W.reach(+k: P.K, b: P.Body) -> Nat:
  P.K{+g, mu, jump, +acc, +air, vmax, size} = k
  P.Body{x, y, z, vx, vy, vz, gr, h} = b
  Nat.add(Nat.mul(2n, Nat.add(Nat.add(P.Z.mag(vx), P.Z.mag(vy)), P.Z.mag(vz))),
    Nat.add(Nat.mul(2n, Nat.add(Nat.add(acc, air), g)), 65536n))

# the sleeping cubes of the cells in (x0 .. x0 + nx - 1, z0 .. z0 + nz - 1),
# i counting them down
def W.rect(+i: Nat, +t: Cells, +seed: U32, +x0: U32, +z0: U32, +nx: Nat) -> List<&2, P.Body>:
  match i:
    case 0n:
      []
    case 1n+k:
      List.append(&2, P.Body, Cells.at(t, seed, (x0 + U32.from_nat(Nat.mod(k, nx)) : U32), (z0 + U32.from_nat(Nat.div(k, nx)) : U32)),
        W.rect(k, t, seed, x0, z0, nx))

# the cells whose cubes a body at x (m its reach) can touch: a cube homed
# in cell h spans [h, h + 2) cubes, the body [x - m, x + S + m): h from
# cell(x - m) - 1 to cell(x + S + m - 1)
def W.lo(+x: Nat, +m: Nat) -> U32:
  (W.cell_of(Nat.sub(x, m)) - 1 : U32)

def W.span(+x: Nat, +m: Nat) -> Nat:
  Nat.add(U32.to_nat((W.cell_of(Nat.sub(Nat.add(Nat.add(x, W.size()), m), 1n)) - W.lo(x, m) : U32)), 1n)

# the sleeping cubes a body can touch in a tick
def W.around(+k: P.K, +t: Cells, +seed: U32, +b: P.Body) -> List<&2, P.Body>:
  +m = W.reach(k, b)
  +x = P.Body.x(b)
  +z = P.Body.z(b)
  +nx = W.span(x, m)
  W.rect(Nat.mul(nx, W.span(z, m)), t, seed, W.lo(x, m), W.lo(z, m), nx)

# is o within a tick's reach of b (m the reach)?
def W.dist(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.sub(a, b), Nat.sub(b, a))

def W.close(+m: Nat, +b: P.Body, +o: P.Body) -> Bool:
  +r = Nat.add(Nat.mul(2n, W.size()), m)
  Bool.and(Nat.is_lt(W.dist(P.Body.x(b), P.Body.x(o)), r),
    Bool.and(Nat.is_lt(W.dist(P.Body.z(b), P.Body.z(o)), r), Nat.is_lt(W.dist(P.Body.y(b), P.Body.y(o)), r)))

def W.moving(b: P.Body) -> Bool:
  P.Body{x, y, z, vx, vy, vz, g, h} = b
  Bool.or(Nat.is_lt(0n, P.Z.mag(vx)), Bool.or(Nat.is_lt(0n, P.Z.mag(vy)), Nat.is_lt(0n, P.Z.mag(vz))))

def W.same(+a: P.Body, +b: P.Body) -> Bool:
  Bool.and(Nat.is_eq(P.Body.x(a), P.Body.x(b)), Bool.and(Nat.is_eq(P.Body.y(a), P.Body.y(b)), Nat.is_eq(P.Body.z(a), P.Body.z(b))))

def W.keep_if(drop: Bool, +b: P.Body, rest: List<&2, P.Body>) -> List<&2, P.Body>:
  match drop:
    case True{}:
      rest
    case False{}:
      b <> rest

# xs without the cube at c's place
def W.without(+c: P.Body, xs: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +b <> rest:
      W.keep_if(W.same(c, b), b, W.without(c, rest))

def W.take_if(take: Bool, +b: P.Body, rest: List<&2, P.Body>) -> List<&2, P.Body>:
  match take:
    case True{}:
      b <> rest
    case False{}:
      rest

# the moving ones
def W.woken(xs: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +b <> rest:
      W.take_if(W.moving(b), b, W.woken(rest))

type Two is Data:
  Two{a: List<&2, P.Body>, b: List<&2, P.Body>}

def W.two_cons(+x: P.Body, r: Two) -> Two:
  Two{a, b} = r
  Two{x <> a, b}

# the first n of xs, and the rest
def W.split(n: Nat, xs: List<&2, P.Body>) -> Two:
  match n xs:
    case 0n _:
      Two{[], xs}
    case 1n+m Nil{}:
      Two{[], []}
    case 1n+m +x <> rest:
      W.two_cons(x, W.split(m, rest))

def W.part1(up: Bool, +b: P.Body, r: Two) -> Two:
  match up:
    case True{}:
      Two{keep, ups} = r
      Two{keep, b <> ups}
    case False{}:
      Two{keep, ups} = r
      Two{b <> keep, ups}

# the cubes above height y (b), and the others (a)
def W.parts(+y: Nat, xs: List<&2, P.Body>) -> Two:
  match xs:
    case []:
      Two{[], []}
    case +b <> rest:
      W.part1(Nat.is_lt(y, P.Body.y(b)), b, W.parts(y, rest))

def W.near1(n: Bool, +o: P.Body, r: Two) -> Two:
  match n:
    case True{}:
      Two{a, b} = r
      Two{o <> a, b}
    case False{}:
      Two{a, b} = r
      Two{a, o <> b}

# the bodies within a tick's reach of b (a), and the others (b)
def W.part_near(+m: Nat, +b: P.Body, xs: List<&2, P.Body>) -> Two:
  match xs:
    case []:
      Two{[], []}
    case +o <> rest:
      W.near1(W.close(m, b, o), o, W.part_near(m, b, rest))

# Waking
# ------
# A cube that wakes leaves its cell, and so do the cubes above it in the 9
# cells around (what may have stood on it), which wake in turn. The
# changed cells are noted for the GPU.

type Cell is Data:
  Cell{cx: U32, cz: U32}

type St is Data:
  St{t: Cells, dirty: List<&2, Cell>, fresh: List<&2, P.Body>, work: List<&2, P.Body>}

def W.lift_put(r: Two, +cx: U32, +cz: U32, t: Cells, dirty: List<&2, Cell>, fresh: List<&2, P.Body>, work: List<&2, P.Body>) -> St:
  Two{keep, up} = r
  match up:
    case []:
      St{t, dirty, fresh, work}
    case +u <> +us:
      St{Cells.set(t, cx, cz, keep), Cell{cx, cz} <> dirty, fresh, List.append(&2, P.Body, u <> us, work)}

def W.lift_cell(+seed: U32, +y: Nat, +cx: U32, +cz: U32, st: St) -> St:
  St{+t, dirty, fresh, work} = st
  W.lift_put(W.parts(y, Cells.at(t, seed, cx, cz)), cx, cz, t, dirty, fresh, work)

def W.lift9(+n: Nat, +seed: U32, +y: Nat, +cx: U32, +cz: U32, st: St) -> St:
  match n:
    case 0n:
      st
    case 1n+k:
      +i = U32.from_nat(k)
      W.lift9(k, seed, y, cx, cz, W.lift_cell(seed, y, (cx - 1 + i % 3 : U32), (cz - 1 + i / 3 : U32), st))

# cube c out of its cell, into the fresh ones, and what stood on it to work
def W.lift(+seed: U32, +c: P.Body, st: St) -> St:
  St{+t, dirty, fresh, work} = st
  +cx = W.cell_of(P.Body.x(c))
  +cz = W.cell_of(P.Body.z(c))
  W.lift9(9n, seed, P.Body.y(c), cx, cz,
    St{Cells.set(t, cx, cz, W.without(c, Cells.at(t, seed, cx, cz))), Cell{cx, cz} <> dirty, c <> fresh, work})

def W.wake(fuel: Nat, +seed: U32, st: St) -> St:
  match fuel:
    case 0n:
      st
    case 1n+f:
      St{t, dirty, fresh, work} = st
      match work:
        case []:
          St{t, dirty, fresh, []}
        case +c <> rest:
          W.wake(f, seed, W.lift(seed, c, St{t, dirty, fresh, rest}))

# The world's tick
# ----------------
# The player first (with the input), then every awake cube (no input),
# each among the sleepers around it and every other awake body; what they
# pushed wakes. Then the awake cubes that came to rest on the ground or on
# sleeping cubes go to sleep in their cells.

type World is Data:
  World{seed: U32, t: Cells, awake: List<&2, P.Body>, dirty: List<&2, Cell>, player: P.Body}

def W.first(xs: List<&2, P.Body>) -> P.Body:
  match xs:
    case []:
      W.cube(0n, 0n, 0n)
    case b <> rest:
      b

def W.p3(+seed: U32, p: P.Body, awake: List<&2, P.Body>, st: St) -> World:
  St{t, dirty, fresh, work} = st
  World{seed, t, List.append(&2, P.Body, fresh, awake), dirty, p}

def W.p2(+seed: U32, p: P.Body, sp: Two, t: Cells, dirty: List<&2, Cell>, far: List<&2, P.Body>) -> World:
  Two{near, sl} = sp
  W.p3(seed, p, List.append(&2, P.Body, near, far), W.wake(256n, seed, St{t, dirty, [], W.woken(sl)}))

def W.p1(+seed: U32, +n: Nat, r: P.Body & List<&2, P.Body>, t: Cells, dirty: List<&2, Cell>, far: List<&2, P.Body>) -> World:
  (p, obs) = r
  W.p2(seed, p, W.split(n, obs), t, dirty, far)

def W.p0(+k: P.K, inp: P.In, +seed: U32, pa: Two, +t: Cells, dirty: List<&2, Cell>, +p: P.Body) -> World:
  Two{+near, far} = pa
  W.p1(seed, List.length(&2, P.Body, near),
    P.Body.tick(k, List.append(&2, P.Body, near, W.around(k, t, seed, p)), inp, p), t, dirty, far)

# the player's tick among the awake cubes within reach and the sleepers
# around
def W.player_step(+k: P.K, inp: P.In, w: World) -> World:
  World{+seed, +t, awake, dirty, +p} = w
  W.p0(k, inp, seed, W.part_near(W.reach(k, p), p, awake), t, dirty, p)

# A few awake bodies
# ------------------
# Each cube among all the others, split by distance: n^2, cheap for few.

type Zip is Data:
  Zip{done: List<&2, P.Body>, todo: List<&2, P.Body>, ps: List<&2, P.Body>, t: Cells, dirty: List<&2, Cell>}

type Far is Data:
  Far{ps: List<&2, P.Body>, done: List<&2, P.Body>, rest: List<&2, P.Body>}

def W.ce(c: P.Body, ps: List<&2, P.Body>, done: List<&2, P.Body>, todo: List<&2, P.Body>, far: Far, st: St) -> Zip:
  Far{pf, df, rf} = far
  St{t, dirty, fresh, work} = st
  Zip{c <> List.append(&2, P.Body, fresh, List.append(&2, P.Body, done, df)), List.append(&2, P.Body, todo, rf),
    List.append(&2, P.Body, ps, pf), t, dirty}

def W.cd(+seed: U32, c: P.Body, ps: List<&2, P.Body>, done: List<&2, P.Body>, sp: Two, t: Cells, dirty: List<&2, Cell>,
  far: Far) -> Zip:
  Two{todo, sl} = sp
  W.ce(c, ps, done, todo, far, W.wake(256n, seed, St{t, dirty, [], W.woken(sl)}))

def W.cc(+seed: U32, +nr: Nat, c: P.Body, ps: List<&2, P.Body>, sp: Two, t: Cells, dirty: List<&2, Cell>, far: Far) -> Zip:
  Two{done, rest} = sp
  W.cd(seed, c, ps, done, W.split(nr, rest), t, dirty, far)

def W.cb(+seed: U32, +nd: Nat, +nr: Nat, c: P.Body, sp: Two, t: Cells, dirty: List<&2, Cell>, far: Far) -> Zip:
  Two{ps, rest} = sp
  W.cc(seed, nr, c, ps, W.split(nd, rest), t, dirty, far)

def W.ca(+seed: U32, +np: Nat, +nd: Nat, +nr: Nat, r: P.Body & List<&2, P.Body>, t: Cells, dirty: List<&2, Cell>, far: Far) -> Zip:
  (c, obs) = r
  W.cb(seed, nd, nr, c, W.split(np, obs), t, dirty, far)

def W.cg0(+k: P.K, +seed: U32, +c: P.Body, pp: Two, dd: Two, rr: Two, +t: Cells, dirty: List<&2, Cell>) -> Zip:
  Two{+pn, pf} = pp
  Two{+dn, df} = dd
  Two{+rn, rf} = rr
  W.ca(seed, List.length(&2, P.Body, pn), List.length(&2, P.Body, dn), List.length(&2, P.Body, rn),
    P.Body.tick(k, List.append(&2, P.Body, pn, List.append(&2, P.Body, dn, List.append(&2, P.Body, rn,
      W.around(k, t, seed, c)))), P.In.idle(), c), t, dirty, Far{pf, df, rf})

# the next awake cube's tick, among the bodies within reach (the player,
# the ones done, the ones to do) and the sleepers around
def W.cube_go(+k: P.K, +seed: U32, done: List<&2, P.Body>, todo: List<&2, P.Body>, ps: List<&2, P.Body>, +t: Cells,
  dirty: List<&2, Cell>) -> Zip:
  match todo:
    case []:
      Zip{done, [], ps, t, dirty}
    case +c <> rest:
      +m = W.reach(k, c)
      W.cg0(k, seed, c, W.part_near(m, c, ps), W.part_near(m, c, done), W.part_near(m, c, rest), t, dirty)

def W.cube_step(+k: P.K, +seed: U32, z: Zip) -> Zip:
  Zip{done, todo, ps, t, dirty} = z
  W.cube_go(k, seed, done, todo, ps, t, dirty)

def W.cubes(n: Nat, +k: P.K, +seed: U32, z: Zip) -> Zip:
  match n:
    case 0n:
      z
    case 1n+m:
      W.cubes(m, k, seed, W.cube_step(k, seed, z))

def W.unzip(+seed: U32, z: Zip) -> World:
  Zip{done, todo, ps, t, dirty} = z
  World{seed, t, List.append(&2, P.Body, todo, done), dirty, W.first(ps)}

def W.cubes_list(+k: P.K, w: World) -> World:
  World{+seed, t, +awake, dirty, p} = w
  W.unzip(seed, W.cubes(List.length(&2, P.Body, awake), k, seed, Zip{[], awake, [p], t, dirty}))

# The awake bodies, by block
# --------------------------
# A cube's tick meets only what is within its reach, so during the cubes'
# ticks the awake bodies wait in buckets by block of 4 x 4 cells (the low 6
# bits of the block on each axis: a 64 x 64 map; far blocks sharing a
# bucket are told apart by distance). A cube looks at the buckets it can reach, not at
# every awake body: a tick of n awake cubes costs n, not n^2. Pushes change
# velocities, never places, so a body stays in its bucket until its own
# tick moves it.

type Bk is Data:
  BE{}
  BL{xs: List<&2, P.Body>}
  BN{a: Bk, b: Bk, c: Bk, d: Bk}

def Bk.levels() -> Nat:
  6n

def Bk.na(r: List<&2, P.Body> & Bk, b: Bk, c: Bk, d: Bk) -> List<&2, P.Body> & Bk:
  (xs, a) = r
  (xs, BN{a, b, c, d})

def Bk.nb(a: Bk, r: List<&2, P.Body> & Bk, c: Bk, d: Bk) -> List<&2, P.Body> & Bk:
  (xs, b) = r
  (xs, BN{a, b, c, d})

def Bk.nc(a: Bk, b: Bk, r: List<&2, P.Body> & Bk, d: Bk) -> List<&2, P.Body> & Bk:
  (xs, c) = r
  (xs, BN{a, b, c, d})

def Bk.nd(a: Bk, b: Bk, c: Bk, r: List<&2, P.Body> & Bk) -> List<&2, P.Body> & Bk:
  (xs, d) = r
  (xs, BN{a, b, c, d})

# the bodies of bucket (cx, cz), and the map without them
def Bk.take(+l: Nat, t: Bk, +cx: U32, +cz: U32, bx: Bool, bz: Bool) -> List<&2, P.Body> & Bk:
  match l t bx bz:
    case _ BE{} _ _:
      ([], BE{})
    case _ BL{xs} _ _:
      (xs, BE{})
    case 0n BN{a, b, c, d} _ _:
      ([], BN{a, b, c, d})
    case 1n+k BN{a, b, c, d} False{} False{}:
      Bk.na(Bk.take(k, a, cx, cz, W.bit(cx, k), W.bit(cz, k)), b, c, d)
    case 1n+k BN{a, b, c, d} True{} False{}:
      Bk.nb(a, Bk.take(k, b, cx, cz, W.bit(cx, k), W.bit(cz, k)), c, d)
    case 1n+k BN{a, b, c, d} False{} True{}:
      Bk.nc(a, b, Bk.take(k, c, cx, cz, W.bit(cx, k), W.bit(cz, k)), d)
    case 1n+k BN{a, b, c, d} True{} True{}:
      Bk.nd(a, b, c, Bk.take(k, d, cx, cz, W.bit(cx, k), W.bit(cz, k)))

# bucket (cx, cz) with xs added
def Bk.put(+l: Nat, t: Bk, +cx: U32, +cz: U32, xs: List<&2, P.Body>, bx: Bool, bz: Bool) -> Bk:
  match l t bx bz:
    case 0n BL{ys} _ _:
      BL{List.append(&2, P.Body, xs, ys)}
    case 0n _ _ _:
      BL{xs}
    case 1n+k BN{a, b, c, d} False{} False{}:
      BN{Bk.put(k, a, cx, cz, xs, W.bit(cx, k), W.bit(cz, k)), b, c, d}
    case 1n+k BN{a, b, c, d} True{} False{}:
      BN{a, Bk.put(k, b, cx, cz, xs, W.bit(cx, k), W.bit(cz, k)), c, d}
    case 1n+k BN{a, b, c, d} False{} True{}:
      BN{a, b, Bk.put(k, c, cx, cz, xs, W.bit(cx, k), W.bit(cz, k)), d}
    case 1n+k BN{a, b, c, d} True{} True{}:
      BN{a, b, c, Bk.put(k, d, cx, cz, xs, W.bit(cx, k), W.bit(cz, k))}
    case 1n+k _ False{} False{}:
      BN{Bk.put(k, BE{}, cx, cz, xs, W.bit(cx, k), W.bit(cz, k)), BE{}, BE{}, BE{}}
    case 1n+k _ True{} False{}:
      BN{BE{}, Bk.put(k, BE{}, cx, cz, xs, W.bit(cx, k), W.bit(cz, k)), BE{}, BE{}}
    case 1n+k _ False{} True{}:
      BN{BE{}, BE{}, Bk.put(k, BE{}, cx, cz, xs, W.bit(cx, k), W.bit(cz, k)), BE{}}
    case 1n+k _ True{} True{}:
      BN{BE{}, BE{}, BE{}, Bk.put(k, BE{}, cx, cz, xs, W.bit(cx, k), W.bit(cz, k))}

def W.blk(+x: Nat) -> U32:
  (W.cell_of(x) >> 2n : U32)

def Bk.takeat(t: Bk, +cx: U32, +cz: U32) -> List<&2, P.Body> & Bk:
  Bk.take(Bk.levels(), t, cx, cz, W.bit(cx, Bk.levels()), W.bit(cz, Bk.levels()))

def Bk.putat(t: Bk, +cx: U32, +cz: U32, xs: List<&2, P.Body>) -> Bk:
  match xs:
    case []:
      t
    case +x <> rest:
      Bk.put(Bk.levels(), t, cx, cz, x <> rest, W.bit(cx, Bk.levels()), W.bit(cz, Bk.levels()))

# b into its block's bucket
def Bk.add(t: Bk, +b: P.Body) -> Bk:
  Bk.putat(t, W.blk(P.Body.x(b)), W.blk(P.Body.z(b)), [b])

def Bk.adds(xs: List<&2, P.Body>, t: Bk) -> Bk:
  match xs:
    case []:
      t
    case +b <> rest:
      Bk.adds(rest, Bk.add(t, b))

def Bk.all(t: Bk) -> List<&2, P.Body>:
  match t:
    case BE{}:
      []
    case BL{xs}:
      xs
    case BN{a, b, c, d}:
      List.append(&2, P.Body, Bk.all(a), List.append(&2, P.Body, Bk.all(b), List.append(&2, P.Body, Bk.all(c), Bk.all(d))))

# the body at s's place in xs (if any), and the others
type Got is Data:
  Got{found: Maybe<&2, P.Body>, rest: List<&2, P.Body>}

def W.got1(hit: Bool, +b: P.Body, r: Got) -> Got:
  match hit:
    case True{}:
      Got{f, rest} = r
      Got{Some{b}, rest}
    case False{}:
      Got{f, rest} = r
      Got{f, b <> rest}

def W.pick(+s: P.Body, xs: List<&2, P.Body>) -> Got:
  match xs:
    case []:
      Got{None{}, []}
    case +b <> rest:
      W.got1(W.same(s, b), b, W.pick(s, rest))

# the awake bodies (in buckets) and the sleepers
type Grid is Data:
  Grid{bk: Bk, t: Cells, dirty: List<&2, Cell>}

# the bodies within reach of c in the buckets of blocks x0 .. x0 + nx - 1
# (and z0 on), i counting them down, taken out of their buckets
type Gath is Data:
  Gath{near: List<&2, P.Body>, bk: Bk}

def W.g3(+cx: U32, +cz: U32, near: List<&2, P.Body>, p: Two, bk: Bk) -> Gath:
  Two{nr, far} = p
  Gath{List.append(&2, P.Body, nr, near), Bk.putat(bk, cx, cz, far)}

def W.g2(+cx: U32, +cz: U32, +m: Nat, +c: P.Body, near: List<&2, P.Body>, r: List<&2, P.Body> & Bk) -> Gath:
  (xs, bk) = r
  W.g3(cx, cz, near, W.part_near(m, c, xs), bk)

def W.g1(+cx: U32, +cz: U32, +m: Nat, +c: P.Body, a: Gath) -> Gath:
  Gath{near, bk} = a
  W.g2(cx, cz, m, c, near, Bk.takeat(bk, cx, cz))

def W.gather(+i: Nat, +m: Nat, +c: P.Body, +x0: U32, +z0: U32, +nx: Nat, a: Gath) -> Gath:
  match i:
    case 0n:
      a
    case 1n+j:
      W.gather(j, m, c, x0, z0, nx,
        W.g1((x0 + U32.from_nat(Nat.mod(j, nx)) : U32), (z0 + U32.from_nat(Nat.div(j, nx)) : U32), m, c, a))

# The octree
# ----------
# Many awake cubes tick in an octree, built every tick. Bend forks two ways
# at a time (a parallel let: a b = f(x) g(y)), so each octree level is
# three cuts in two, one per axis -- the same boxes as the 8 octants: a
# node cuts its cubes' box across its longest side, in the middle. A cube
# goes down a side only if all it can touch this tick (its reach, and half
# a cube more) is on that side of the plane, else it stays at the node.
# The two sides' cubes then never meet, nor touch the same body (a cube is
# 1 m, the margin half of it each way): they tick in parallel, and then the
# node's own cubes tick, among what the sides left near the plane. The
# sleepers they push wake at the end of the tick (events), so no two
# branches write to the cells at once; until then, whoever touches a pushed
# sleeper sees it moving.

type Oct is Data:
  OL{bs: List<&2, P.Body>}
  ON{st: List<&2, P.Body>, lo: Oct, hi: Oct, ax: Nat, c: Nat}

type P3 is Data:
  P3{st: List<&2, P.Body>, lo: List<&2, P.Body>, hi: List<&2, P.Body>}

type Bx is Data:
  Bx{x0: Nat, y0: Nat, z0: Nat, x1: Nat, y1: Nat, z1: Nat}

# half a cube: the margin between the sides
def O.half() -> Nat:
  131072n

# a node cuts while it holds more cubes than this and is at least 8 m long
def O.leaf_max() -> Nat:
  24n

def O.min_size() -> Nat:
  2097152n

def O.big() -> Nat:
  Nat.add(Nat.mul(W.size(), U32.to_nat(1073741823)), 262143n)

def O.bb(xs: List<&2, P.Body>, b: Bx) -> Bx:
  match xs:
    case []:
      b
    case +e <> rest:
      Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
      O.bb(rest, Bx{Nat.min(x0, P.Body.x(e)), Nat.min(y0, P.Body.y(e)), Nat.min(z0, P.Body.z(e)),
        Nat.max(x1, P.Body.x(e)), Nat.max(y1, P.Body.y(e)), Nat.max(z1, P.Body.z(e))})

def O.box(xs: List<&2, P.Body>) -> Bx:
  O.bb(xs, Bx{O.big(), O.big(), O.big(), 0n, 0n, 0n})

# the longest side of b (0 x, 1 y, 2 z), and its length
def O.axis(+b: Bx) -> Nat:
  Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
  +dx = Nat.sub(x1, x0)
  +dy = Nat.sub(y1, y0)
  +dz = Nat.sub(z1, z0)
  Pick.n(Bool.and(Nat.is_le(dy, dx), Nat.is_le(dz, dx)), 0n, Pick.n(Nat.is_le(dz, dy), 1n, 2n))

def O.long(+b: Bx) -> Nat:
  Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
  Nat.max(Nat.sub(x1, x0), Nat.max(Nat.sub(y1, y0), Nat.sub(z1, z0)))

def O.at(+ax: Nat, +x: Nat, +y: Nat, +z: Nat) -> Nat:
  match ax:
    case 0n:
      x
    case 1n:
      y
    case _:
      z

# the middle of b on axis ax: where it is cut (a + (b - a) / 2: the sum
# of two places, near 2^47 each, would pass Nat's 2^48)
def O.mid(+b: Bx, +ax: Nat) -> Nat:
  Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
  +a = O.at(ax, x0, y0, z0)
  Nat.add(a, Nat.div(Nat.sub(O.at(ax, x1, y1, z1), a), 2n))

def O.coord(+ax: Nat, +b: P.Body) -> Nat:
  O.at(ax, P.Body.x(b), P.Body.y(b), P.Body.z(b))

# which side of the plane at c a cube at a is, r its reach and the margin:
# 0 below, 1 above, 2 across
def O.side(+a: Nat, +c: Nat, +r: Nat) -> Nat:
  Pick.n(Nat.is_le(Nat.add(Nat.add(a, W.size()), r), c), 0n, Pick.n(Nat.is_le(Nat.add(c, r), a), 1n, 2n))

def O.put3(i: Nat, +b: P.Body, p: P3) -> P3:
  match i:
    case 0n:
      P3{st, lo, hi} = p
      P3{st, b <> lo, hi}
    case 1n:
      P3{st, lo, hi} = p
      P3{st, lo, b <> hi}
    case _:
      P3{st, lo, hi} = p
      P3{b <> st, lo, hi}

# the cubes of xs by side of the plane at c on axis ax
def O.part(xs: List<&2, P.Body>, +ax: Nat, +c: Nat, +r: Nat) -> P3:
  match xs:
    case []:
      P3{[], [], []}
    case +b <> rest:
      O.put3(O.side(O.coord(ax, b), c, r), b, O.part(rest, ax, c, r))

def O.all(p: P3) -> List<&2, P.Body>:
  P3{st, lo, hi} = p
  List.append(&2, P.Body, st, List.append(&2, P.Body, lo, hi))

def O.split(+xs: List<&2, P.Body>, +b: Bx) -> Bool:
  Bool.and(Nat.is_lt(O.leaf_max(), List.length(&2, P.Body, xs)), Nat.is_le(O.min_size(), O.long(b)))

# the node whose cubes, split by the plane at c on axis ax, are p; its two
# sides built in parallel
def O.build(fuel: Nat, split: Bool, p: P3, +ax: Nat, +c: Nat, +r: Nat) -> Oct:
  match fuel split:
    case 0n _:
      OL{O.all(p)}
    case 1n+f False{}:
      OL{O.all(p)}
    case 1n++f True{}:
      P3{st, +lo, +hi} = p
      +blo = O.box(lo)
      +bhi = O.box(hi)
      +alo = O.axis(blo)
      +ahi = O.axis(bhi)
      +clo = O.mid(blo, alo)
      +chi = O.mid(bhi, ahi)
      tlo thi = O.build(f, O.split(lo, blo), O.part(lo, alo, clo, r), alo, clo, r) O.build(f, O.split(hi, bhi), O.part(hi, ahi, chi, r), ahi, chi, r)
      ON{st, tlo, thi, ax, c}

# Bodies by identity (their place: two never share one)

def W.eqz(+a: P.Z, +b: P.Z) -> Bool:
  Bool.and(Nat.is_eq(P.Z.pos(a), P.Z.pos(b)), Nat.is_eq(P.Z.neg(a), P.Z.neg(b)))

def W.eqbool(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def W.eqb(+a: P.Body, +b: P.Body) -> Bool:
  Bool.and(W.same(a, b), Bool.and(W.eqz(P.Body.vx(a), P.Body.vx(b)), Bool.and(W.eqz(P.Body.vy(a), P.Body.vy(b)),
    Bool.and(W.eqz(P.Body.vz(a), P.Body.vz(b)), Bool.and(W.eqbool(P.Body.ground(a), P.Body.ground(b)),
      W.eqbool(P.Body.hit(a), P.Body.hit(b)))))))

def O.pickb(c: Bool, +a: P.Body, +b: P.Body) -> P.Body:
  match c:
    case True{}:
      a
    case False{}:
      b

# e as cs has it (the one at its place), or e
def O.find(+e: P.Body, cs: List<&2, P.Body>) -> P.Body:
  match cs:
    case []:
      e
    case +c <> rest:
      O.pickb(W.same(e, c), c, O.find(e, rest))

def O.apply(xs: List<&2, P.Body>, +cs: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +x <> rest:
      O.find(x, cs) <> O.apply(rest, cs)

def O.has(+x: P.Body, xs: List<&2, P.Body>) -> Bool:
  match xs:
    case []:
      False{}
    case +y <> rest:
      Bool.or(W.same(x, y), O.has(x, rest))

# the ones of now that differ from orig (the same bodies, in order)
def O.changed(orig: List<&2, P.Body>, now: List<&2, P.Body>) -> List<&2, P.Body>:
  match orig now:
    case Nil{} _:
      []
    case _ Nil{}:
      []
    case +o <> os +n <> ns:
      W.keep_if(W.eqb(o, n), n, O.changed(os, ns))

def W.orp(f: Maybe<&2, P.Body>, p: P.Body) -> P.Body:
  match f:
    case None{}:
      p
    case Some{b}:
      b

# the blocks of the cells a body at x (m its reach) can touch
def W.blocks(+x: Nat, +m: Nat) -> Nat:
  +lo = W.lo(x, m)
  Nat.add(U32.to_nat((((lo + U32.from_nat(W.span(x, m)) - 1 : U32) >> 2n) - (lo >> 2n) : U32)), 1n)

# Sequential ticks with events
# ----------------------------
# todo tick in order, among themselves, pool (bodies that may be pushed,
# not ticked) and the sleepers, all in buckets; the sleepers pushed are
# events (ev), seen moving by whoever touches them after.

# Where a tick finds the sleepers: the cells (a walk down their trie, shared
# by every branch), or, for cubes close together, the sleepers of the
# cells they can all reach, read once for them all (a list each one
# filters): the trie is walked a few times per node, not per cube, and the
# branches stop contending for its top nodes.
type Src is Data:
  SCells{t: Cells}
  SList{xs: List<&2, P.Body>}

type Rc is Data:
  Rc{x0: U32, z0: U32, x1: U32, z1: U32}

def Q.umin(+a: U32, +b: U32) -> U32:
  Pick.u((a < b : U32), a, b)

def Q.umax(+a: U32, +b: U32) -> U32:
  Pick.u((a < b : U32), b, a)

# the cells every cube of xs can reach, as one rectangle
def Q.rect(xs: List<&2, P.Body>, +k: P.K, r: Rc) -> Rc:
  match xs:
    case []:
      r
    case +c <> rest:
      Rc{+x0, +z0, +x1, +z1} = r
      +m = W.reach(k, c)
      +lx = W.lo(P.Body.x(c), m)
      +lz = W.lo(P.Body.z(c), m)
      Q.rect(rest, k, Rc{Q.umin(x0, lx), Q.umin(z0, lz),
        Q.umax(x1, (lx + U32.from_nat(W.span(P.Body.x(c), m)) - 1 : U32)), Q.umax(z1, (lz + U32.from_nat(W.span(P.Body.z(c), m)) - 1 : U32))})

def Q.src3(small: Bool, +t: Cells, +seed: U32, +area: Nat, +x0: U32, +z0: U32, +nx: Nat) -> Src:
  match small:
    case True{}:
      SList{W.rect(area, t, seed, x0, z0, nx)}
    case False{}:
      SCells{t}

def Q.src2(+t: Cells, +seed: U32, +n: Nat, r: Rc) -> Src:
  Rc{+x0, +z0, +x1, +z1} = r
  +nx = U32.to_nat((x1 - x0 + 1 : U32))
  +area = Nat.mul(nx, U32.to_nat((z1 - z0 + 1 : U32)))
  Q.src3(Bool.and(Nat.is_lt(0n, n), Nat.is_le(area, Nat.add(64n, Nat.mul(16n, n)))), t, seed, area, x0, z0, nx)

def Q.source(+k: P.K, +t: Cells, +seed: U32, +xs: List<&2, P.Body>) -> Src:
  Q.src2(t, seed, List.length(&2, P.Body, xs), Q.rect(xs, k, Rc{4294967295, 4294967295, 0, 0}))

# the sleepers of xs homed in the nx x nz cells from (x0, z0)
def Q.inrect(xs: List<&2, P.Body>, +x0: U32, +z0: U32, +nx: U32, +nz: U32) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +o <> rest:
      W.take_if(Bool.and(((W.cell_of(P.Body.x(o)) - x0 : U32) < nx : U32), ((W.cell_of(P.Body.z(o)) - z0 : U32) < nz : U32)), o,
        Q.inrect(rest, x0, z0, nx, nz))

# the sleepers c can touch (as W.around finds them)
def Q.around(+k: P.K, +src: Src, +seed: U32, +c: P.Body) -> List<&2, P.Body>:
  match src:
    case SCells{t}:
      W.around(k, t, seed, c)
    case SList{xs}:
      +m = W.reach(k, c)
      Q.inrect(xs, W.lo(P.Body.x(c), m), W.lo(P.Body.z(c), m), U32.from_nat(W.span(P.Body.x(c), m)), U32.from_nat(W.span(P.Body.z(c), m)))

type Sq is Data:
  Sq{bk: Bk, ev: List<&2, P.Body>}

type Sq3 is Data:
  Sq3{todo: List<&2, P.Body>, pool: List<&2, P.Body>, ev: List<&2, P.Body>}

type Pl is Data:
  Pl{got: List<&2, P.Body>, bk: Bk}

# the sleepers xs as the events have them
def Q.shadow(xs: List<&2, P.Body>, +ev: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +x <> rest:
      O.find(x, ev) <> Q.shadow(rest, ev)

def Q.repl(+x: P.Body, xs: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +e <> rest:
      O.pickb(W.same(e, x), x, e) <> Q.repl(x, rest)

def Q.up2(has: Bool, mv: Bool, +x: P.Body, ev: List<&2, P.Body>) -> List<&2, P.Body>:
  match has mv:
    case True{} _:
      Q.repl(x, ev)
    case False{} True{}:
      x <> ev
    case False{} False{}:
      ev

# the sleepers after a tick into the events: the known ones updated, the
# ones just pushed added
def Q.upsert(xs: List<&2, P.Body>, +ev: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      ev
    case +x <> rest:
      Q.upsert(rest, Q.up2(O.has(x, ev), W.moving(x), x, ev))

def Q.q6(+c: P.Body, sp: Two, bk: Bk, +ev: List<&2, P.Body>) -> Sq:
  Two{near, sl} = sp
  Sq{Bk.adds(near, Bk.add(bk, c)), Q.upsert(sl, ev)}

def Q.q5(+nn: Nat, r: P.Body & List<&2, P.Body>, bk: Bk, +ev: List<&2, P.Body>) -> Sq:
  (c, obs) = r
  Q.q6(c, W.split(nn, obs), bk, ev)

def Q.q4(+k: P.K, +seed: U32, +src: Src, +c: P.Body, g: Gath, +ev: List<&2, P.Body>) -> Sq:
  Gath{+near, bk} = g
  Q.q5(List.length(&2, P.Body, near),
    P.Body.tick(k, List.append(&2, P.Body, near, Q.shadow(Q.around(k, src, seed, c), ev)), P.In.idle(), c), bk, ev)

def Q.q3(+k: P.K, +seed: U32, +src: Src, f: Maybe<&2, P.Body>, bk: Bk, +ev: List<&2, P.Body>) -> Sq:
  match f:
    case None{}:
      Sq{bk, ev}
    case Some{+c}:
      +m = W.reach(k, c)
      +x = P.Body.x(c)
      +z = P.Body.z(c)
      +nx = W.blocks(x, m)
      Q.q4(k, seed, src, c, W.gather(Nat.mul(nx, W.blocks(z, m)), m, c, (W.lo(x, m) >> 2n : U32), (W.lo(z, m) >> 2n : U32), nx,
        Gath{[], bk}), ev)

def Q.q2(+k: P.K, +seed: U32, +src: Src, +cx: U32, +cz: U32, g: Got, bk: Bk, +ev: List<&2, P.Body>) -> Sq:
  Got{f, rest} = g
  Q.q3(k, seed, src, f, Bk.putat(bk, cx, cz, rest), ev)

def Q.q1(+k: P.K, +seed: U32, +src: Src, +s: P.Body, +cx: U32, +cz: U32, r: List<&2, P.Body> & Bk, +ev: List<&2, P.Body>) -> Sq:
  (xs, bk) = r
  Q.q2(k, seed, src, cx, cz, W.pick(s, xs), bk, ev)

# the tick of the cube that was at s's place (as it is now)
def Q.step(+k: P.K, +seed: U32, +src: Src, +s: P.Body, q: Sq) -> Sq:
  Sq{bk, +ev} = q
  +cx = W.blk(P.Body.x(s))
  +cz = W.blk(P.Body.z(s))
  Q.q1(k, seed, src, s, cx, cz, Bk.takeat(bk, cx, cz), ev)

def Q.steps(xs: List<&2, P.Body>, +k: P.K, +seed: U32, +src: Src, q: Sq) -> Sq:
  match xs:
    case []:
      q
    case +s <> rest:
      Q.steps(rest, k, seed, src, Q.step(k, seed, src, s, q))

def Q.pl3(+p: P.Body, +cx: U32, +cz: U32, got: List<&2, P.Body>, g: Got, bk: Bk) -> Pl:
  Got{f, rest} = g
  Pl{W.orp(f, p) <> got, Bk.putat(bk, cx, cz, rest)}

def Q.pl2(+p: P.Body, +cx: U32, +cz: U32, got: List<&2, P.Body>, r: List<&2, P.Body> & Bk) -> Pl:
  (xs, bk) = r
  Q.pl3(p, cx, cz, got, W.pick(p, xs), bk)

def Q.pl1(+p: P.Body, a: Pl) -> Pl:
  Pl{got, bk} = a
  +cx = W.blk(P.Body.x(p))
  +cz = W.blk(P.Body.z(p))
  Q.pl2(p, cx, cz, got, Bk.takeat(bk, cx, cz))

# the pool's bodies out of the buckets (as they are now), reversed
def Q.pull(xs: List<&2, P.Body>, a: Pl) -> Pl:
  match xs:
    case []:
      a
    case +p <> rest:
      Q.pull(rest, Q.pl1(p, a))

def Q.end2(a: Pl, ev: List<&2, P.Body>) -> Sq3:
  Pl{got, bk} = a
  Sq3{Bk.all(bk), List.reverse(&2, P.Body, got), ev}

def Q.end(+pool: List<&2, P.Body>, q: Sq) -> Sq3:
  Sq{bk, ev} = q
  Q.end2(Q.pull(pool, Pl{[], bk}), ev)

def Q.seq(+k: P.K, +seed: U32, +cells: Cells, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq3:
  Q.end(pool, Q.steps(todo, k, seed, Q.source(k, cells, seed, todo), Sq{Bk.adds(todo, Bk.adds(pool, BE{})), ev}))

# The octree's tick
# -----------------

type Res is Data:
  Res{done: List<&2, P.Body>, chg: List<&2, P.Body>, ev: List<&2, P.Body>}

def O.l2(+ext: List<&2, P.Body>, q: Sq3) -> Res:
  Sq3{bs, ext2, ev} = q
  Res{bs, O.changed(ext, ext2), ev}

def O.leaf(+k: P.K, +seed: U32, +cells: Cells, bs: List<&2, P.Body>, +ext: List<&2, P.Body>, ev: List<&2, P.Body>) -> Res:
  O.l2(ext, Q.seq(k, seed, cells, bs, ext, ev))

# the bodies of xs the cubes below the plane at c could touch (below: side
# 0), or above it (1)
def O.on(+s: Nat, +a: Nat, +c: Nat) -> Bool:
  match s:
    case 0n:
      Nat.is_lt(a, c)
    case _:
      Nat.is_lt(c, Nat.add(a, W.size()))

def O.near(xs: List<&2, P.Body>, +s: Nat, +ax: Nat, +c: Nat) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +e <> rest:
      W.take_if(O.on(s, O.coord(ax, e), c), e, O.near(rest, s, ax, c))

# is a within d of the plane at c?
def O.nearp(+a: Nat, +c: Nat, +d: Nat) -> Bool:
  Bool.and(Nat.is_lt(c, Nat.add(a, d)), Nat.is_lt(a, Nat.add(c, d)))

# the sides' cubes the node's own could touch (near the plane), and the rest
def O.band(xs: List<&2, P.Body>, +ax: Nat, +c: Nat, +d: Nat) -> Two:
  match xs:
    case []:
      Two{[], []}
    case +o <> rest:
      W.near1(O.nearp(O.coord(ax, o), c, d), o, O.band(rest, ax, c, d))

def O.j4(+ext: List<&2, P.Body>, far: List<&2, P.Body>, st: List<&2, P.Body>, ev: List<&2, P.Body>, sp: Two) -> Res:
  Two{near, ext2} = sp
  Res{List.append(&2, P.Body, far, List.append(&2, P.Body, near, st)), O.changed(ext, ext2), ev}

def O.j3(+ext: List<&2, P.Body>, +nn: Nat, far: List<&2, P.Body>, q: Sq3) -> Res:
  Sq3{st, pool, ev} = q
  O.j4(ext, far, st, ev, W.split(nn, pool))

def O.j2(+k: P.K, +seed: U32, +cells: Cells, +ext: List<&2, P.Body>, sp: Two, ev: List<&2, P.Body>, bd: Two) -> Res:
  Two{ext1, st1} = sp
  Two{+near, far} = bd
  O.j3(ext, List.length(&2, P.Body, near), far, Q.seq(k, seed, cells, st1, List.append(&2, P.Body, near, ext1), ev))

# both sides done: what they changed of the node's cubes and of those
# around applied, then the node's cubes' ticks, among what the sides left
# near the plane
def O.join(+k: P.K, +seed: U32, +cells: Cells, +r: Nat, +ext: List<&2, P.Body>, exts: List<&2, P.Body>, +ax: Nat, +c: Nat,
  rl: Res, rh: Res) -> Res:
  Res{dl, cl, el} = rl
  Res{dh, ch, eh} = rh
  O.j2(k, seed, cells, ext, W.split(List.length(&2, P.Body, ext), O.apply(exts, List.append(&2, P.Body, cl, ch))),
    List.append(&2, P.Body, el, eh),
    O.band(List.append(&2, P.Body, dl, dh), ax, c, Nat.add(Nat.add(Nat.mul(2n, W.size()), Nat.mul(2n, r)), Nat.add(O.half(), 1n))))

# a node's tick, ext the bodies around it its cubes may touch (and push:
# chg, what changed of them); the two sides in parallel
def O.tick(t: Oct, +ext: List<&2, P.Body>, +k: P.K, +seed: U32, +cells: Cells, +r: Nat) -> Res:
  match t:
    case OL{bs}:
      O.leaf(k, seed, cells, bs, ext, [])
    case ON{st, lo, hi, +ax, +c}:
      +exts = List.append(&2, P.Body, ext, st)
      rl rh = O.tick(lo, O.near(exts, 0n, ax, c), k, seed, cells, r) O.tick(hi, O.near(exts, 1n, ax, c), k, seed, cells, r)
      O.join(k, seed, cells, r, ext, exts, ax, c, rl, rh)

# The farthest reach

def O.reach(xs: List<&2, P.Body>, +k: P.K, +m: Nat) -> Nat:
  match xs:
    case []:
      m
    case +e <> rest:
      O.reach(rest, k, Nat.max(m, W.reach(k, e)))

def O.w3(+seed: U32, p: P.Body, done: List<&2, P.Body>, st: St) -> World:
  St{t, dirty, fresh, work} = st
  World{seed, t, List.append(&2, P.Body, fresh, done), dirty, p}

# after the tree: the player as pushed, the sleepers pushed woken (and what
# stood on them)
def O.w2(+seed: U32, t: Cells, dirty: List<&2, Cell>, +p: P.Body, res: Res) -> World:
  Res{done, chg, +ev} = res
  O.w3(seed, O.find(p, chg), done,
    W.wake(Nat.add(1024n, Nat.mul(16n, List.length(&2, P.Body, ev))), seed, St{t, dirty, [], ev}))

def O.w1(+k: P.K, +seed: U32, +t: Cells, dirty: List<&2, Cell>, +p: P.Body, +awake: List<&2, P.Body>, +b: Bx, +r: Nat) -> World:
  +ax = O.axis(b)
  +c = O.mid(b, ax)
  +rh = Nat.add(r, O.half())
  O.w2(seed, t, dirty, p, O.tick(O.build(40n, O.split(awake, b), O.part(awake, ax, c, rh), ax, c, rh), [p], k, seed, t, r))

def W.cubes_oct(+k: P.K, w: World) -> World:
  World{+seed, +t, +awake, dirty, +p} = w
  O.w1(k, seed, t, dirty, p, awake, O.box(awake), O.reach(awake, k, 0n))

# every awake cube's tick (no input), in order, each among the bodies
# within its reach (the player, the other awake ones) and the sleepers
# around; what they push wakes. A few cubes look at each other directly
# (cheaper: no map to build); many, through the buckets (measured: the
# buckets win from about a hundred on)
def W.cubes_by(few: Bool, +k: P.K, w: World) -> World:
  match few:
    case True{}:
      W.cubes_list(k, w)
    case False{}:
      W.cubes_oct(k, w)

def W.cubes_all(+k: P.K, w: World) -> World:
  World{seed, t, +awake, dirty, p} = w
  W.cubes_by(Nat.is_lt(List.length(&2, P.Body, awake), 128n), k, World{seed, t, awake, dirty, p})

# Sleep
# -----

type Sl is Data:
  Sl{t: Cells, dirty: List<&2, Cell>, keep: List<&2, P.Body>}

def W.fits7(xs: List<&2, P.Body>) -> Bool:
  Nat.is_lt(List.length(&2, P.Body, xs), 7n)

def W.still.on(quiet: Bool, +k: P.K, +t: Cells, +seed: U32, +c: P.Body) -> Bool:
  match quiet:
    case True{}:
      Bool.or(Nat.is_eq(P.Body.y(c), 0n), P.Geo.rests(W.size(), P.Body.x(c), P.Body.y(c), P.Body.z(c), W.around(k, t, seed, c)))
    case False{}:
      False{}

# at rest: on the ground, still, and on the floor or on sleeping cubes
# (the cells looked at only for a body already still)
def W.still(+k: P.K, +t: Cells, +seed: U32, +c: P.Body) -> Bool:
  W.still.on(Bool.and(P.Body.ground(c), Bool.not(W.moving(c))), k, t, seed, c)

def W.sleep1(ok: Bool, +c: P.Body, +cx: U32, +cz: U32, cubes: List<&2, P.Body>, s: Sl) -> Sl:
  match ok:
    case True{}:
      Sl{t, dirty, keep} = s
      Sl{Cells.set(t, cx, cz, W.cube(P.Body.x(c), P.Body.y(c), P.Body.z(c)) <> cubes), Cell{cx, cz} <> dirty, keep}
    case False{}:
      Sl{t, dirty, keep} = s
      Sl{t, dirty, c <> keep}

# (the cell read only for a cube at rest)
def W.sleep2(still: Bool, +seed: U32, +c: P.Body, s: Sl) -> Sl:
  match still:
    case True{}:
      Sl{+t, dirty, keep} = s
      +cx = W.cell_of(P.Body.x(c))
      +cz = W.cell_of(P.Body.z(c))
      +cubes = Cells.at(t, seed, cx, cz)
      W.sleep1(W.fits7(cubes), c, cx, cz, cubes, Sl{t, dirty, keep})
    case False{}:
      Sl{t, dirty, keep} = s
      Sl{t, dirty, c <> keep}

def W.sleep_one(+k: P.K, +seed: U32, +c: P.Body, s: Sl) -> Sl:
  Sl{+t, dirty, keep} = s
  W.sleep2(W.still(k, t, seed, c), seed, c, Sl{t, dirty, keep})

def W.sleep(xs: List<&2, P.Body>, +k: P.K, +seed: U32, s: Sl) -> Sl:
  match xs:
    case []:
      s
    case +c <> rest:
      W.sleep(rest, k, seed, W.sleep_one(k, seed, c, s))

def W.slept(+seed: U32, p: P.Body, s: Sl) -> World:
  Sl{t, dirty, keep} = s
  World{seed, t, keep, dirty, p}

def W.sleep_all(+k: P.K, w: World) -> World:
  World{+seed, t, awake, dirty, p} = w
  W.slept(seed, p, W.sleep(awake, k, seed, Sl{t, dirty, []}))

# a tick of the whole world
def W.tick(+k: P.K, inp: P.In, w: World) -> World:
  W.sleep_all(k, W.cubes_all(k, W.player_step(k, inp, w)))

# a new world of seed, the player standing at the start
def W.new(+seed: U32) -> World:
  +o = W.base(W.origin())
  World{seed, CGen{}, [], [], W.cube(Nat.add(o, 131072n), 0n, Nat.add(o, 131072n))}
