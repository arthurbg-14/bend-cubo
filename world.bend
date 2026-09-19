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

# the sleeping cubes of the 25 cells from (cx - 2, cz - 2) to (cx + 2,
# cz + 2): all that a body in cell (cx, cz) can touch in a tick (a cube
# homed in cell h, anywhere in it, reaches into h + 1; the body reaches
# into c + 1, and a tick's move less than a cube further)
def W.near(+n: Nat, +t: Cells, +seed: U32, +cx: U32, +cz: U32) -> List<&2, P.Body>:
  match n:
    case 0n:
      []
    case 1n+k:
      +i = U32.from_nat(k)
      List.append(&2, P.Body, Cells.at(t, seed, (cx - 2 + i % 5 : U32), (cz - 2 + i / 5 : U32)),
        W.near(k, t, seed, cx, cz))

def W.around(+t: Cells, +seed: U32, +b: P.Body) -> List<&2, P.Body>:
  W.near(25n, t, seed, W.cell_of(P.Body.x(b)), W.cell_of(P.Body.z(b)))

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

def W.p2(+seed: U32, p: P.Body, sp: Two, t: Cells, dirty: List<&2, Cell>) -> World:
  Two{awake, sl} = sp
  W.p3(seed, p, awake, W.wake(256n, seed, St{t, dirty, [], W.woken(sl)}))

def W.p1(+seed: U32, +n: Nat, r: P.Body & List<&2, P.Body>, t: Cells, dirty: List<&2, Cell>) -> World:
  (p, obs) = r
  W.p2(seed, p, W.split(n, obs), t, dirty)

def W.player_step(+k: P.K, inp: P.In, w: World) -> World:
  World{+seed, +t, +awake, dirty, +p} = w
  W.p1(seed, List.length(&2, P.Body, awake),
    P.Body.tick(k, List.append(&2, P.Body, awake, W.around(t, seed, p)), inp, p), t, dirty)

type Zip is Data:
  Zip{done: List<&2, P.Body>, todo: List<&2, P.Body>, ps: List<&2, P.Body>, t: Cells, dirty: List<&2, Cell>}

def W.ce(c: P.Body, ps: List<&2, P.Body>, done: List<&2, P.Body>, todo: List<&2, P.Body>, st: St) -> Zip:
  St{t, dirty, fresh, work} = st
  Zip{c <> List.append(&2, P.Body, fresh, done), todo, ps, t, dirty}

def W.cd(+seed: U32, c: P.Body, ps: List<&2, P.Body>, done: List<&2, P.Body>, sp: Two, t: Cells, dirty: List<&2, Cell>) -> Zip:
  Two{todo, sl} = sp
  W.ce(c, ps, done, todo, W.wake(256n, seed, St{t, dirty, [], W.woken(sl)}))

def W.cc(+seed: U32, +nr: Nat, c: P.Body, ps: List<&2, P.Body>, sp: Two, t: Cells, dirty: List<&2, Cell>) -> Zip:
  Two{done, rest} = sp
  W.cd(seed, c, ps, done, W.split(nr, rest), t, dirty)

def W.cb(+seed: U32, +nd: Nat, +nr: Nat, c: P.Body, sp: Two, t: Cells, dirty: List<&2, Cell>) -> Zip:
  Two{ps, rest} = sp
  W.cc(seed, nr, c, ps, W.split(nd, rest), t, dirty)

def W.ca(+seed: U32, +nd: Nat, +nr: Nat, r: P.Body & List<&2, P.Body>, t: Cells, dirty: List<&2, Cell>) -> Zip:
  (c, obs) = r
  W.cb(seed, nd, nr, c, W.split(1n, obs), t, dirty)

def W.cube_go(+k: P.K, +seed: U32, +done: List<&2, P.Body>, todo: List<&2, P.Body>, ps: List<&2, P.Body>, +t: Cells,
  dirty: List<&2, Cell>) -> Zip:
  match todo:
    case []:
      Zip{done, [], ps, t, dirty}
    case +c <> +rest:
      W.ca(seed, List.length(&2, P.Body, done), List.length(&2, P.Body, rest),
        P.Body.tick(k, List.append(&2, P.Body, ps, List.append(&2, P.Body, done, List.append(&2, P.Body, rest,
          W.around(t, seed, c)))), P.In.idle(), c), t, dirty)

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

def W.cubes_all(+k: P.K, w: World) -> World:
  World{+seed, t, +awake, dirty, p} = w
  W.unzip(seed, W.cubes(List.length(&2, P.Body, awake), k, seed, Zip{[], awake, [p], t, dirty}))

# Sleep
# -----

type Sl is Data:
  Sl{t: Cells, dirty: List<&2, Cell>, keep: List<&2, P.Body>}

def W.fits7(xs: List<&2, P.Body>) -> Bool:
  Nat.is_lt(List.length(&2, P.Body, xs), 7n)

# at rest: on the ground, still, and on the floor or on sleeping cubes
def W.still(+t: Cells, +seed: U32, +c: P.Body) -> Bool:
  Bool.and(Bool.and(P.Body.ground(c), Bool.not(W.moving(c))),
    Bool.or(Nat.is_eq(P.Body.y(c), 0n), P.Geo.rests(W.size(), P.Body.x(c), P.Body.y(c), P.Body.z(c), W.around(t, seed, c))))

def W.sleep1(ok: Bool, +c: P.Body, +cx: U32, +cz: U32, cubes: List<&2, P.Body>, s: Sl) -> Sl:
  match ok:
    case True{}:
      Sl{t, dirty, keep} = s
      Sl{Cells.set(t, cx, cz, W.cube(P.Body.x(c), P.Body.y(c), P.Body.z(c)) <> cubes), Cell{cx, cz} <> dirty, keep}
    case False{}:
      Sl{t, dirty, keep} = s
      Sl{t, dirty, c <> keep}

def W.sleep_one(+seed: U32, +c: P.Body, s: Sl) -> Sl:
  Sl{+t, dirty, keep} = s
  +cx = W.cell_of(P.Body.x(c))
  +cz = W.cell_of(P.Body.z(c))
  +cubes = Cells.at(t, seed, cx, cz)
  W.sleep1(Bool.and(W.still(t, seed, c), W.fits7(cubes)), c, cx, cz, cubes, Sl{t, dirty, keep})

def W.sleep(xs: List<&2, P.Body>, +seed: U32, s: Sl) -> Sl:
  match xs:
    case []:
      s
    case +c <> rest:
      W.sleep(rest, seed, W.sleep_one(seed, c, s))

def W.slept(+seed: U32, p: P.Body, s: Sl) -> World:
  Sl{t, dirty, keep} = s
  World{seed, t, keep, dirty, p}

def W.sleep_all(w: World) -> World:
  World{+seed, t, awake, dirty, p} = w
  W.slept(seed, p, W.sleep(awake, seed, Sl{t, dirty, []}))

# a tick of the whole world
def W.tick(+k: P.K, inp: P.In, w: World) -> World:
  W.sleep_all(W.cubes_all(k, W.player_step(k, inp, w)))

# a new world of seed, the player standing at the start
def W.new(+seed: U32) -> World:
  +o = W.base(W.origin())
  World{seed, CGen{}, [], [], W.cube(Nat.add(o, 131072n), 0n, Nat.add(o, 131072n))}
