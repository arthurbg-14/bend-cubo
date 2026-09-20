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
  # the runway: a straight lane 8 m wide down the z axis, with no end and
  # nothing generated in it -- room to get up to speed (the player starts
  # in the middle of it, facing down it, and the motor has no top speed)
  +lane = ((cx - W.origin() + 3 : U32) < 8 : U32)
  Pick.u(Bool.or(Bool.or(near, lane), ((h .&. 255 : U32) >= dens : U32)), 0, Pick.u((hh < 150 : U32), 1, Pick.u((hh < 225 : U32), 2, 3)))

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
# A trie over the low 8 bits of a cell's x and z (a node splits on one bit
# of each: 8 levels, 256 x 256 slots). A leaf holds the changed cells of
# its slot (cells 256 m apart share one), each with its sleeping cubes;
# CGen, nothing changed below. Shallow on purpose: the ticks read it for
# every awake cube's neighbourhood, and 30 levels (one per bit of a cell)
# were half their time.

type Ce is Data:
  Ce{cx: U32, cz: U32, cubes: List<&2, P.Body>}

type Cells is Data:
  CGen{}
  CLeaf{es: List<&2, Ce>}
  CNode{a: Cells, b: Cells, c: Cells, d: Cells}

def W.bit(+c: U32, l: Nat) -> Bool:
  match l:
    case 0n:
      False{}
    case 1n+k:
      U32.is_eq(((c >> k) .&. 1 : U32), 1)

def Cells.pickl(c: Bool, a: List<&2, P.Body>, b: List<&2, P.Body>) -> List<&2, P.Body>:
  match c:
    case True{}:
      a
    case False{}:
      b

# the cubes of cell (cx, cz) among a slot's changed cells, or as generated
def Cells.find(es: List<&2, Ce>, +seed: U32, +cx: U32, +cz: U32) -> List<&2, P.Body>:
  match es:
    case []:
      Gen.cubes(seed, cx, cz)
    case Ce{+x, +z, cubes} <> rest:
      Cells.pickl(Bool.and(U32.is_eq(x, cx), U32.is_eq(z, cz)), cubes, Cells.find(rest, seed, cx, cz))

def Cells.pickc(c: Bool, a: List<&2, Ce>, b: List<&2, Ce>) -> List<&2, Ce>:
  match c:
    case True{}:
      a
    case False{}:
      b

# a slot's changed cells with (cx, cz) set to cubes
def Cells.upd(es: List<&2, Ce>, +cx: U32, +cz: U32, +cubes: List<&2, P.Body>) -> List<&2, Ce>:
  match es:
    case []:
      [Ce{cx, cz, cubes}]
    case Ce{+x, +z, cs} <> +rest:
      Cells.pickc(Bool.and(U32.is_eq(x, cx), U32.is_eq(z, cz)), Ce{cx, cz, cubes} <> rest, Ce{x, z, cs} <> Cells.upd(rest, cx, cz, cubes))

# the sleeping cubes of cell (cx, cz); l levels left, (bx, bz) the bits
# that choose among the node's children
def Cells.get(+l: Nat, t: Cells, +seed: U32, +cx: U32, +cz: U32, bx: Bool, bz: Bool) -> List<&2, P.Body>:
  match l t bx bz:
    case _ CGen{} _ _:
      Gen.cubes(seed, cx, cz)
    case _ CLeaf{es} _ _:
      Cells.find(es, seed, cx, cz)
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
  8n

def Cells.at(+t: Cells, +seed: U32, +cx: U32, +cz: U32) -> List<&2, P.Body>:
  Cells.get(Cells.levels(), t, seed, cx, cz, W.bit(cx, Cells.levels()), W.bit(cz, Cells.levels()))

# cell (cx, cz) set to cubes
def Cells.put(+l: Nat, t: Cells, +cx: U32, +cz: U32, +cubes: List<&2, P.Body>, bx: Bool, bz: Bool) -> Cells:
  match l t bx bz:
    case 0n CLeaf{es} _ _:
      CLeaf{Cells.upd(es, cx, cz, cubes)}
    case 0n _ _ _:
      CLeaf{[Ce{cx, cz, cubes}]}
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
# quarter of a metre to spare (the player: a jump, a push of the motor).
def W.reach(+k: P.K, b: P.Body) -> Nat:
  P.K{+g, mu, jump, +acc, size} = k
  P.Body{x, y, z, vx, vy, vz, gr, h} = b
  Nat.add(Nat.mul(2n, Nat.add(Nat.add(P.Z.mag(vx), P.Z.mag(vy)), P.Z.mag(vz))),
    Nat.add(Nat.mul(2n, Nat.add(acc, g)), 65536n))

# the sleeping cubes of the cells in (x0 .. x0 + nx - 1, z0 .. z0 + nz - 1),
# i counting them down
def W.rect(+i: Nat, +t: Cells, +seed: U32, +x0: U32, +z0: U32, +nx: Nat) -> List<&2, P.Body>:
  match i:
    case 0n:
      []
    case 1n+k:
      List.append(&2, P.Body, Cells.at(t, seed, (x0 + U32.from_nat(Nat.mod(k, nx)) : U32), (z0 + U32.from_nat(Nat.div(k, nx)) : U32)),
        W.rect(k, t, seed, x0, z0, nx))

def W.reachz(+k: P.K, +vx: P.Z, +vy: P.Z, +vz: P.Z) -> Nat:
  P.K{+g, mu, jump, +acc, size} = k
  Nat.add(Nat.mul(2n, Nat.add(Nat.add(P.Z.mag(vx), P.Z.mag(vy)), P.Z.mag(vz))),
    Nat.add(Nat.mul(2n, Nat.add(acc, g)), 65536n))

# How far a cube (no input) can reach in a tick: it moves by v + v' on each
# axis, and without a motor v' only loses speed (friction) or gains g
# (falling); a push changes its velocity, not where it is, until its own
# next tick. So 2 |v| + 2 g bounds it (and a few units to spare): a cube is
# handed exactly the bodies it may touch, not every one within a quarter
# of a metre more.
def W.creachz(+k: P.K, +vx: P.Z, +vy: P.Z, +vz: P.Z) -> Nat:
  Nat.add(Nat.mul(2n, Nat.add(Nat.add(P.Z.mag(vx), P.Z.mag(vy)), P.Z.mag(vz))), Nat.add(Nat.mul(2n, P.K.g(k)), 16n))

def W.creach(+k: P.K, b: P.Body) -> Nat:
  P.Body{x, y, z, +vx, +vy, +vz, gr, h} = b
  W.creachz(k, vx, vy, vz)

# the cells whose cubes a body at x (m its reach) can touch: a cube homed
# in cell h spans [h, h + 2) cubes, the body [x - m, x + S + m): h from
# cell(x - m) - 1 to cell(x + S + m - 1)
def W.lo(+x: Nat, +m: Nat) -> U32:
  (W.cell_of(Nat.sub(x, m)) - 1 : U32)

def W.span(+x: Nat, +m: Nat) -> Nat:
  Nat.add(U32.to_nat((W.cell_of(Nat.sub(Nat.add(Nat.add(x, W.size()), m), 1n)) - W.lo(x, m) : U32)), 1n)

def W.take_if(take: Bool, b: P.Body, rest: List<&2, P.Body>) -> List<&2, P.Body>:
  match take:
    case True{}:
      b <> rest
    case False{}:
      rest

# is o within a tick's reach of b (m the reach)? Their boxes (a cube each)
# can meet only if every coordinate differs by less than a cube and the
# reach: what is farther can neither stop a move nor be pushed, so a tick
# with it or without it is the same (and costs less: every move checks
# every obstacle)
def W.dist(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.sub(a, b), Nat.sub(b, a))

def W.closep(+r: Nat, +ax: Nat, +ay: Nat, +az: Nat, +bx: Nat, +by: Nat, +bz: Nat) -> Bool:
  Bool.and(Nat.is_lt(W.dist(ax, bx), r), Bool.and(Nat.is_lt(W.dist(az, bz), r), Nat.is_lt(W.dist(ay, by), r)))

def W.close(+m: Nat, +b: P.Body, +o: P.Body) -> Bool:
  +r = Nat.add(W.size(), m)
  Bool.and(Nat.is_lt(W.dist(P.Body.x(b), P.Body.x(o)), r),
    Bool.and(Nat.is_lt(W.dist(P.Body.z(b), P.Body.z(o)), r), Nat.is_lt(W.dist(P.Body.y(b), P.Body.y(o)), r)))

# the sleeping cubes a body can touch in a tick
# the bodies of xs within r of (x, y, z), each taken apart once (its
# coordinates are plain numbers; sharing a body would count references on
# every read)
def W.nof(+r: Nat, +x: Nat, +y: Nat, +z: Nat, xs: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case P.Body{+ox, +oy, +oz, vx, vy, vz, g, h} <> rest:
      W.take_if(W.closep(r, x, y, z, ox, oy, oz), P.Body{ox, oy, oz, vx, vy, vz, g, h}, W.nof(r, x, y, z, rest))

def W.near_of(xs: List<&2, P.Body>, +m: Nat, +b: P.Body) -> List<&2, P.Body>:
  W.nof(Nat.add(W.size(), m), P.Body.x(b), P.Body.y(b), P.Body.z(b), xs)

def W.around3(+t: Cells, +seed: U32, +m: Nat, +x: Nat, +y: Nat, +z: Nat) -> List<&2, P.Body>:
  +nx = W.span(x, m)
  W.nof(Nat.add(W.size(), m), x, y, z, W.rect(Nat.mul(nx, W.span(z, m)), t, seed, W.lo(x, m), W.lo(z, m), nx))

def W.around(+k: P.K, +t: Cells, +seed: U32, +b: P.Body) -> List<&2, P.Body>:
  W.around3(t, seed, W.reach(k, b), P.Body.x(b), P.Body.y(b), P.Body.z(b))

def W.moving(b: P.Body) -> Bool:
  P.Body{x, y, z, vx, vy, vz, g, h} = b
  Bool.or(Nat.is_lt(0n, P.Z.mag(vx)), Bool.or(Nat.is_lt(0n, P.Z.mag(vy)), Nat.is_lt(0n, P.Z.mag(vz))))

def W.same(+a: P.Body, +b: P.Body) -> Bool:
  Bool.and(Nat.is_eq(P.Body.x(a), P.Body.x(b)), Bool.and(Nat.is_eq(P.Body.y(a), P.Body.y(b)), Nat.is_eq(P.Body.z(a), P.Body.z(b))))

def W.keep_if(drop: Bool, b: P.Body, rest: List<&2, P.Body>) -> List<&2, P.Body>:
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

def W.near1(n: Bool, o: P.Body, r: Two) -> Two:
  match n:
    case True{}:
      Two{a, b} = r
      Two{o <> a, b}
    case False{}:
      Two{a, b} = r
      Two{a, o <> b}

# the bodies within a tick's reach of b (a), and the others (b)
def W.pn(+r: Nat, +x: Nat, +y: Nat, +z: Nat, xs: List<&2, P.Body>) -> Two:
  match xs:
    case []:
      Two{[], []}
    case P.Body{+ox, +oy, +oz, vx, vy, vz, g, h} <> rest:
      W.near1(W.closep(r, x, y, z, ox, oy, oz), P.Body{ox, oy, oz, vx, vy, vz, g, h}, W.pn(r, x, y, z, rest))

# the same, counting the near ones
type Pc is Data:
  Pc{a: List<&2, P.Body>, n: Nat, b: List<&2, P.Body>}

def W.tn1(c: Bool, o: P.Body, r: Pc) -> Pc:
  match c:
    case True{}:
      Pc{a, n, b} = r
      Pc{o <> a, Nat.add(n, 1n), b}
    case False{}:
      Pc{a, n, b} = r
      Pc{a, n, o <> b}

def W.pnc(+r: Nat, +x: Nat, +y: Nat, +z: Nat, xs: List<&2, P.Body>) -> Pc:
  match xs:
    case []:
      Pc{[], 0n, []}
    case P.Body{+ox, +oy, +oz, vx, vy, vz, g, h} <> rest:
      W.tn1(W.closep(r, x, y, z, ox, oy, oz), P.Body{ox, oy, oz, vx, vy, vz, g, h}, W.pnc(r, x, y, z, rest))

def W.part_near(+m: Nat, +b: P.Body, xs: List<&2, P.Body>) -> Two:
  W.pn(Nat.add(W.size(), m), P.Body.x(b), P.Body.y(b), P.Body.z(b), xs)

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

type Bx is Data:
  Bx{x0: Nat, y0: Nat, z0: Nat, x1: Nat, y1: Nat, z1: Nat}

type World is Data:
  World{seed: U32, t: Cells, awake: List<&2, P.Body>, dirty: List<&2, Cell>, player: P.Body}

type Sl is Data:
  Sl{t: Cells, dirty: List<&2, Cell>, keep: List<&2, P.Body>}

# The flat world
# --------------
# For a crowd, the awake cubes (with the sleepers around them and the
# player) go into one array of words, in a grid of cells chained by index,
# and the proven tick runs on top of it. Lists and trees cost a heap node
# and a reference count per body per step; an array read is a read. Every
# read hands the array back, so a walk down a cell's chain is one function
# with a phase, not a chain of them (Bend has no mutual recursion).

# the array's origin: a cell's corner on each axis (x and z are far apart in
# an endless world, so one origin for both would not fit in 32 bits)
type Og is Data:
  Og{x: Nat, z: Nat}

def F.ox(+o: Og) -> Nat:
  Og{x, z} = o
  x

def F.oz(+o: Og) -> Nat:
  Og{x, z} = o
  z

# A body is 6 words: x, y, z (from the patch's origin), vx, vy, and vz
# with the flags on top (ground, hit, sleeper, woken)
def F.w() -> U32:
  6

def F.pz(c: Bool, +a: P.Z, +b: P.Z) -> P.Z:
  match c:
    case True{}:
      a
    case False{}:
      b

def F.zof(+w: U32) -> P.Z:
  F.pz(U32.is_eq((w >> 31n : U32), 0), P.Pos{U32.to_nat((w .&. 2147483647 : U32))},
    P.Neg{U32.to_nat((w .&. 2147483647 : U32))})

def F.wof(+z: P.Z) -> U32:
  Pick.u(Nat.is_lt(0n, P.Z.neg(z)), (U32.from_nat(P.Z.neg(z)) .|. 2147483648 : U32), U32.from_nat(P.Z.pos(z)))

# vz keeps its sign in bit 30 and the flags above it
def F.vzw(+z: P.Z, +g: Bool, +h: Bool, +sl: Bool) -> U32:
  (Pick.u(Nat.is_lt(0n, P.Z.neg(z)), (U32.from_nat(P.Z.neg(z)) .|. 1073741824 : U32), U32.from_nat(P.Z.pos(z)))
    .|. (Pick.u(g, 2147483648, 0) .|. (Pick.u(h, 1, 0) << 29n) .|. (Pick.u(sl, 1, 0) << 28n) : U32) : U32)

def F.vzof(+w: U32) -> P.Z:
  F.pz(U32.is_eq(((w >> 30n) .&. 1 : U32), 0), P.Pos{U32.to_nat((w .&. 268435455 : U32))},
    P.Neg{U32.to_nat((w .&. 268435455 : U32))})

def F.ground(+w: U32) -> Bool:
  U32.is_eq((w >> 31n : U32), 1)

def F.hit(+w: U32) -> Bool:
  U32.is_eq(((w >> 29n) .&. 1 : U32), 1)

def F.sleeper(+w: U32) -> Bool:
  U32.is_eq(((w >> 28n) .&. 1 : U32), 1)

def F.body(+o: Og, +x: U32, +y: U32, +z: U32, +vx: U32, +vy: U32, +vz: U32) -> P.Body:
  P.Body{Nat.add(F.ox(o), U32.to_nat(x)), U32.to_nat(y), Nat.add(F.oz(o), U32.to_nat(z)), F.zof(vx), F.zof(vy), F.vzof(vz),
    F.ground(vz), F.hit(vz)}

# body i into the array (its flags kept as they are, but for a sleeper)
def F.put(a: Array<U32>, +i: U32, +o: Og, +sl: Bool, b: P.Body) -> Array<U32>:
  P.Body{+x, +y, +z, +vx, +vy, +vz, +g, +h} = b
  a[(i * 6 : U32)] <- U32.from_nat(Nat.sub(x, F.ox(o)))
  a[(i * 6 + 1 : U32)] <- U32.from_nat(y)
  a[(i * 6 + 2 : U32)] <- U32.from_nat(Nat.sub(z, F.oz(o)))
  a[(i * 6 + 3 : U32)] <- F.wof(vx)
  a[(i * 6 + 4 : U32)] <- F.wof(vy)
  a[(i * 6 + 5 : U32)] <- F.vzw(vz, g, h, sl)

# the array's layout: bodies at 0, the chain links at 6*cap, the cells'
# heads at 7*cap (cap slots, a power of two)
def F.nx(+cap: U32) -> U32:
  (cap * 6 : U32)

def F.hd(+cap: U32) -> U32:
  (cap * 7 : U32)

def F.putw(a: Array<U32>, +i: U32, +v: U32) -> Array<U32>:
  a[i] <- v

# the cell of a place (cells of 1 m: 2^18 units), hashed into a slot
def F.slot(+x: U32, +z: U32, +msk: U32) -> U32:
  ((((x >> 18n) * 73856093 : U32) .^. ((z >> 18n) * 19349663 : U32) : U32) .&. msk : U32)

def F.pack(xs: List<&2, P.Body>, a: Array<U32>, +i: U32, +o: Og, +sl: Bool) -> Array<U32>:
  match xs:
    case []:
      a
    case b <> rest:
      F.pack(rest, F.put(a, i, o, sl, b), (i + 1 : U32), o, sl)

def F.fin(r: Array<U32> & U32) -> Array<U32>:
  (a, v) = r
  a

# every body into its cell's chain: read its x and z, then its slot's head,
# then link it in (one function, a phase per read, the reads handed on)
def F.grid(n: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +cap: U32, +msk: U32, +x: U32, +s: U32) -> Array<U32>:
  match n ph:
    case 0n _:
      F.fin(r)
    case 1n+m 2n:
      (a, v) = r
      F.grid(n, 1n, a[(i * 6 + 2 : U32)], i, cap, msk, v, s)
    case 1n+m 1n:
      (a, v) = r
      +sl = F.slot(x, v, msk)
      F.grid(n, 0n, a[(F.hd(cap) + sl : U32)], i, cap, msk, x, sl)
    case 1n+m _:
      (a, v) = r
      F.grid(m, 2n, F.putw(F.putw(a, (F.nx(cap) + i : U32), v), (F.hd(cap) + s : U32), (i + 1 : U32))[((i + 1) * 6 : U32)],
        (i + 1 : U32), cap, msk, x, s)

# the cell a body is homed in, as one word (two cells hashing to the same
# slot share a chain, so a walk has to tell them apart)
def F.key2(+cx: U32, +cz: U32) -> U32:
  (((cx .&. 65535) << 16n) .|. (cz .&. 65535) : U32)

def F.cell(+x: U32) -> U32:
  (x >> 18n : U32)

# the same build, keeping each body's cell at 8 cap + i (the array must
# have room for nine parts, not eight)
def F.grid2(n: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +cap: U32, +msk: U32, +x: U32, +s: U32) -> Array<U32>:
  match n ph:
    case 0n _:
      F.fin(r)
    case 1n+m 2n:
      (a, v) = r
      F.grid2(n, 1n, a[(i * 6 + 2 : U32)], i, cap, msk, v, s)
    case 1n+m 1n:
      (a, +v) = r
      +sl = F.slot(x, v, msk)
      F.grid2(n, 0n, F.putw(a, (F.hd(cap) + cap + i : U32), F.key2(F.cell(x), F.cell(v)))[(F.hd(cap) + sl : U32)],
        i, cap, msk, x, sl)
    case 1n+m _:
      (a, v) = r
      F.grid2(m, 2n, F.putw(F.putw(a, (F.nx(cap) + i : U32), v), (F.hd(cap) + s : U32), (i + 1 : U32))[((i + 1) * 6 : U32)],
        (i + 1 : U32), cap, msk, x, s)

def F.build2(+n: U32, a: Array<U32>, +cap: U32, +msk: U32) -> Array<U32>:
  F.grid2(U32.to_nat(n), 2n, a[0], 0, cap, msk, 0, 0)

def F.build(+n: U32, a: Array<U32>, +cap: U32, +msk: U32) -> Array<U32>:
  F.grid(U32.to_nat(n), 2n, a[0], 0, cap, msk, 0, 0)

def F.d(+a: U32, +b: U32) -> U32:
  Pick.u((a < b : U32), (b - a : U32), (a - b : U32))

def F.keep(c: Bool, +j: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match c:
    case True{}:
      j <> acc
    case False{}:
      acc

def F.pair(a: Array<U32>, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, acc)

def F.pfin(r: Array<U32> & U32, acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, v) = r
  (a, acc)

# the slot of a cell (cx, cz), already in cells
def F.slot2(+cx: U32, +cz: U32, +msk: U32) -> U32:
  (((cx * 73856093 : U32) .^. (cz * 19349663 : U32) : U32) .&. msk : U32)

# the bodies within rad of (sx, sy, sz), walking the chains of the 9 cells
# around it: one function, a phase per read (3: a chain link, 2: x, 1: y,
# 0: z and the test)
# a body's neighbourhood, cell by cell over the rectangle its reach spans,
# and inside a cell down the chain of the cubes homed in it. A read of the
# array is a step, so a step is a phase: 3 takes the chain's next link, 2, 1
# and 0 the cube's x, y and z. The cell walks on when a chain ends (a link
# of 0). Nothing here matches on a number -- Bend takes a u32 apart bit by
# bit for that -- so the next cell and the next address are picked.
def F.scan(fuel: Nat, cn: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +sx: U32, +sy: U32, +sz: U32, +rad: U32,
  +cap: U32, +msk: U32, +lox: U32, +hix: U32, +cx: U32, +cz: U32, +j: U32, +jx: U32, +jy: U32,
  acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match fuel cn ph:
    case 0n _ _:
      F.pfin(r, acc)
    case _ 0n _:
      F.pfin(r, acc)
    case 1n+f 1n++c 3n:
      (a, +v) = r
      +e = U32.is_eq(v, 0)
      +w = U32.is_eq(cx, hix)
      +ncx = Pick.u(w, lox, (cx + 1 : U32))
      +ncz = Pick.u(w, (cz + 1 : U32), cz)
      F.scan(f, Pick.n(e, c, 1n+c), Pick.n(e, 3n, 2n),
        a[Pick.u(e, (F.hd(cap) + F.slot2(ncx, ncz, msk) : U32), ((v - 1) * 6 : U32))], i, sx, sy, sz, rad, cap, msk,
        lox, hix, Pick.u(e, ncx, cx), Pick.u(e, ncz, cz), Pick.u(e, 0, (v - 1 : U32)), 0, 0, acc)
    case 1n+f 1n+c 2n:
      (a, v) = r
      F.scan(f, 1n+c, 1n, a[(j * 6 + 1 : U32)], i, sx, sy, sz, rad, cap, msk, lox, hix, cx, cz, j, v, jy, acc)
    case 1n+f 1n+c 1n:
      (a, v) = r
      F.scan(f, 1n+c, 0n, a[(j * 6 + 2 : U32)], i, sx, sy, sz, rad, cap, msk, lox, hix, cx, cz, j, jx, v, acc)
    case 1n+f 1n+c _:
      (a, v) = r
      F.scan(f, 1n+c, 3n, a[(F.nx(cap) + j : U32)], i, sx, sy, sz, rad, cap, msk, lox, hix, cx, cz, j, jx, jy,
        F.keep(Bool.and(Bool.not(U32.is_eq(j, i)),
          Bool.and((F.d(sx, jx) < rad : U32), Bool.and((F.d(sz, v) < rad : U32), (F.d(sy, jy) < rad : U32)))), j, acc))

def F.lfin(r: Array<U32> & U32, acc: List<&2, P.Body>) -> Array<U32> & List<&2, P.Body>:
  (a, v) = r
  (a, acc)

# the bodies of the indexes idxs out of the array, one word per call (5: x,
# 4: y, 3: z, 2: vx, 1: vy, 0: vz and the body)
def F.load(idxs: List<&2, U32>, ph: Nat, r: Array<U32> & U32, +o: Og, +j: U32, +x: U32, +y: U32, +z: U32, +vx: U32,
  +vy: U32, acc: List<&2, P.Body>) -> Array<U32> & List<&2, P.Body>:
  match idxs ph:
    case _ 5n:
      (a, v) = r
      F.load(idxs, 4n, a[(j * 6 + 1 : U32)], o, j, v, y, z, vx, vy, acc)
    case _ 4n:
      (a, v) = r
      F.load(idxs, 3n, a[(j * 6 + 2 : U32)], o, j, x, v, z, vx, vy, acc)
    case _ 3n:
      (a, v) = r
      F.load(idxs, 2n, a[(j * 6 + 3 : U32)], o, j, x, y, v, vx, vy, acc)
    case _ 2n:
      (a, v) = r
      F.load(idxs, 1n, a[(j * 6 + 4 : U32)], o, j, x, y, z, v, vy, acc)
    case _ 1n:
      (a, v) = r
      F.load(idxs, 0n, a[(j * 6 + 5 : U32)], o, j, x, y, z, vx, v, acc)
    case Nil{} _:
      (a, v) = r
      (a, F.body(o, x, y, z, vx, vy, v) <> acc)
    case +j2 <> rest _:
      (a, v) = r
      F.load(rest, 5n, a[(j2 * 6 : U32)], o, j2, 0, 0, 0, 0, 0, F.body(o, x, y, z, vx, vy, v) <> acc)

def F.load0(idxs: List<&2, U32>, a: Array<U32>, +o: Og) -> Array<U32> & List<&2, P.Body>:
  match idxs:
    case []:
      (a, [])
    case +j <> rest:
      F.load(rest, 5n, a[(j * 6 : U32)], o, j, 0, 0, 0, 0, 0, [])

# what a tick pushed, back into the array (only the velocities and flags
# change: a push moves no one)
def F.wb(idxs: List<&2, U32>, obs: List<&2, P.Body>, a: Array<U32>, +o: Og, +na: U32) -> Array<U32>:
  match idxs obs:
    case +j <> ir b <> br:
      P.Body{x, y, z, vx, vy, +vz, +g, +h} = b
      F.wb(ir, br, F.putw(F.putw(F.putw(a, (j * 6 + 3 : U32), F.wof(vx)), (j * 6 + 4 : U32), F.wof(vy)),
        (j * 6 + 5 : U32), F.vzw(vz, g, h, (j >= na : U32))), o, na)
    case _ _:
      a

# read body i: each read hands the array on
def F.g5(r: Array<U32> & U32, +o: Og, +x: U32, +y: U32, +z: U32, +vx: U32, +vy: U32) -> Array<U32> & P.Body:
  (a, v) = r
  (a, F.body(o, x, y, z, vx, vy, v))

def F.g4(r: Array<U32> & U32, +i: U32, +o: Og, +x: U32, +y: U32, +z: U32, +vx: U32) -> Array<U32> & P.Body:
  (a, v) = r
  F.g5(a[(i * 6 + 5 : U32)], o, x, y, z, vx, v)

def F.g3(r: Array<U32> & U32, +i: U32, +o: Og, +x: U32, +y: U32, +z: U32) -> Array<U32> & P.Body:
  (a, v) = r
  F.g4(a[(i * 6 + 4 : U32)], i, o, x, y, z, v)

def F.g2(r: Array<U32> & U32, +i: U32, +o: Og, +x: U32, +y: U32) -> Array<U32> & P.Body:
  (a, v) = r
  F.g3(a[(i * 6 + 3 : U32)], i, o, x, y, v)

def F.g1(r: Array<U32> & U32, +i: U32, +o: Og, +x: U32) -> Array<U32> & P.Body:
  (a, v) = r
  F.g2(a[(i * 6 + 2 : U32)], i, o, x, v)

def F.g0(r: Array<U32> & U32, +i: U32, +o: Og) -> Array<U32> & P.Body:
  (a, v) = r
  F.g1(a[(i * 6 + 1 : U32)], i, o, v)

def F.get(a: Array<U32>, +i: U32, +o: Og) -> Array<U32> & P.Body:
  F.g0(a[(i * 6 : U32)], i, o)

def F.four(a: Array<U32>, +i: U32, +o: Og, +na: U32, idxs: List<&2, U32>, r: P.Body & List<&2, P.Body>) -> Array<U32>:
  (b, obs) = r
  F.wb(idxs, obs, F.put(a, i, o, False{}, b), o, na)

def F.three(rl: Array<U32> & List<&2, P.Body>, self: P.Body, +i: U32, +o: Og, +k: P.K, +na: U32,
  idxs: List<&2, U32>) -> Array<U32>:
  (a, obs) = rl
  F.four(a, i, o, na, idxs, P.Body.tick(k, obs, P.In.idle(), self))

def F.two(rs: Array<U32> & List<&2, U32>, self: P.Body, +i: U32, +o: Og, +k: P.K, +na: U32) -> Array<U32>:
  (a, +idxs) = rs
  F.three(F.load0(List.reverse(&2, U32, idxs), a, o), self, i, o, k, na, idxs)

def F.three2(rl: Array<U32> & List<&2, P.Body>, self: P.Body, +i: U32, +o: Og, +k: P.K, +na: U32, idxs: List<&2, U32>,
  inp: P.In) -> Array<U32>:
  (a, obs) = rl
  F.four(a, i, o, na, idxs, P.Body.tick(k, obs, inp, self))

def F.two2(rs: Array<U32> & List<&2, U32>, self: P.Body, +i: U32, +o: Og, +k: P.K, +na: U32, inp: P.In) -> Array<U32>:
  (a, +idxs) = rs
  F.three2(F.load0(List.reverse(&2, U32, idxs), a, o), self, i, o, k, na, idxs, inp)

# the cubes a body can touch live in the cells of W.lo .. W.lo + W.span,
# worked out from its reach and the cube's size
def F.one2(a: Array<U32>, +i: U32, +o: Og, +k: P.K, +cap: U32, +msk: U32, +na: U32, +self: P.Body, +m: Nat,
  +mm: Nat, inp: P.In) -> Array<U32>:
  +mr = Nat.add(m, mm)
  +lox = (W.lo(P.Body.x(self), mr) - W.cell_of(F.ox(o)) : U32)
  +loz = (W.lo(P.Body.z(self), mr) - W.cell_of(F.oz(o)) : U32)
  +nx = W.span(P.Body.x(self), mr)
  F.two2(F.scan(8192n, Nat.mul(nx, W.span(P.Body.z(self), mr)), 3n,
    a[(F.hd(cap) + F.slot2(lox, loz, msk) : U32)], i,
    U32.from_nat(Nat.sub(P.Body.x(self), F.ox(o))), U32.from_nat(P.Body.y(self)),
    U32.from_nat(Nat.sub(P.Body.z(self), F.oz(o))),
    U32.from_nat(Nat.add(W.size(), m)), cap, msk, lox, (lox + U32.from_nat(nx) - 1 : U32), lox, loz, 0, 0, 0, []),
    self, i, o, k, na, inp)

# one cube's tick: itself, the bodies within reach out of the grid, the
# proven tick, then back into the array
def F.one(r: Array<U32> & P.Body, +i: U32, +o: Og, +k: P.K, +cap: U32, +msk: U32, +na: U32, +mm: Nat) -> Array<U32>:
  (a, +self) = r
  F.one2(a, i, o, k, cap, msk, na, self, W.creach(k, self), mm, P.In.idle())

def F.ticks(n: Nat, a: Array<U32>, +i: U32, +o: Og, +k: P.K, +cap: U32, +msk: U32, +na: U32,
  +mm: Nat) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+m:
      F.ticks(m, F.one(F.get(a, i, o), i, o, k, cap, msk, na, mm), (i + 1 : U32), o, k, cap, msk, na, mm)

def F.ufin(r: Array<U32> & U32, acc: List<&2, P.Body>) -> Array<U32> & List<&2, P.Body>:
  (a, v) = r
  (a, acc)

# the bodies 0 .. n-1 back out of the array
def F.unp(n: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +o: Og, +x: U32, +y: U32, +z: U32, +vx: U32, +vy: U32,
  acc: List<&2, P.Body>) -> Array<U32> & List<&2, P.Body>:
  match n ph:
    case 0n _:
      F.ufin(r, acc)
    case 1n+m 5n:
      (a, v) = r
      F.unp(n, 4n, a[(i * 6 + 1 : U32)], i, o, v, y, z, vx, vy, acc)
    case 1n+m 4n:
      (a, v) = r
      F.unp(n, 3n, a[(i * 6 + 2 : U32)], i, o, x, v, z, vx, vy, acc)
    case 1n+m 3n:
      (a, v) = r
      F.unp(n, 2n, a[(i * 6 + 3 : U32)], i, o, x, y, v, vx, vy, acc)
    case 1n+m 2n:
      (a, v) = r
      F.unp(n, 1n, a[(i * 6 + 4 : U32)], i, o, x, y, z, v, vy, acc)
    case 1n+m 1n:
      (a, v) = r
      F.unp(n, 0n, a[(i * 6 + 5 : U32)], i, o, x, y, z, vx, v, acc)
    case 1n+m _:
      (a, v) = r
      F.unp(m, 5n, a[((i + 1) * 6 : U32)], (i + 1 : U32), o, 0, 0, 0, 0, 0, F.body(o, x, y, z, vx, vy, v) <> acc)

def F.unpack(+n: U32, a: Array<U32>, +i: U32, +o: Og) -> Array<U32> & List<&2, P.Body>:
  F.unp(U32.to_nat(n), 5n, a[(i * 6 : U32)], i, o, 0, 0, 0, 0, 0, [])

def F.cap(fuel: Nat, done: Bool, +n: U32, +c: U32, +b: Nat) -> U32 & Nat:
  match fuel done:
    case _ True{}:
      (c, b)
    case 0n _:
      (c, b)
    case 1n+f _:
      F.cap(f, (n <= c * 2 : U32), n, (c * 2 : U32), Nat.add(b, 1n))

def F.cap0(+n: U32) -> U32 & Nat:
  F.cap(30n, (n <= 16 : U32), n, 16, 4n)


# The crowd in chunks: bodies sorted by cell
# -----------------------------------------
# A chunk keeps its bodies in one array, sorted by the cell they are in, so
# the neighbours of a cube are a handful of words side by side: no chain to
# follow, no hash, and the cells of a row are one run of the array. The
# array holds two body areas (the sort writes into the other one), the
# cells' first indexes (off) and the cursors the sort walks with (cur).
#
#   0        bodies A (6 words each)
#   6 cap    bodies B
#   12 cap   off: the first body of each cell, gg + 1 of them
#   ...      cur: the same, for the sort to walk

def C.rb(+cap: U32) -> U32:
  (cap * 6 : U32)

# which bodies are the chunk's own (one word each, beside each body area):
# the tick rewrites a body's words, so the mark cannot live inside it
def C.roa(+cap: U32) -> U32:
  (cap * 12 : U32)

def C.rob(+cap: U32) -> U32:
  (cap * 13 : U32)

def C.roff(+cap: U32) -> U32:
  (cap * 14 : U32)

def C.rcur(+cap: U32, +gg: U32) -> U32:
  (cap * 14 + gg + 1 : U32)

# a body that left the chunk's grid (before the tick that moves it out has
# been carried over) falls into the last cell instead of a place of its own
def C.clamp(+c: U32, +gg: U32) -> U32:
  Pick.u((c < gg : U32), c, (gg - 1 : U32))

# the cell of a body inside the chunk's grid (g cells a side, the first at
# (ox, oz)), as one number
def C.ci(+x: U32, +z: U32, +ox: U32, +oz: U32, +g: U32) -> U32:
  C.clamp(((F.cell(z) - oz) * g + (F.cell(x) - ox) : U32), (g * g : U32))

# how many bodies each cell holds, into off (a cell's count at off + c + 1)
def C.cnt(n: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +src: U32, +off: U32, +ox: U32, +oz: U32, +g: U32,
  +x: U32, +c: U32) -> Array<U32>:
  match n ph:
    case 0n _:
      F.fin(r)
    case 1n+m 2n:
      (a, +v) = r
      C.cnt(n, 1n, a[(src + i * 6 + 2 : U32)], i, src, off, ox, oz, g, v, c)
    case 1n+m 1n:
      (a, +v) = r
      +cc = C.ci(x, v, ox, oz, g)
      C.cnt(n, 0n, a[(off + cc + 1 : U32)], i, src, off, ox, oz, g, x, cc)
    case 1n+m _:
      (a, v) = r
      C.cnt(m, 2n, (a[(off + c + 1 : U32)] <- (v + 1 : U32))[(src + (i + 1) * 6 : U32)], (i + 1 : U32), src, off,
        ox, oz, g, x, c)

# the counts added up: off + c is then the first body of cell c, and cur
# gets a copy for the sort to walk
def C.pre(n: Nat, r: Array<U32> & U32, +i: U32, +off: U32, +cur: U32, +s: U32) -> Array<U32>:
  match n:
    case 0n:
      F.fin(r)
    case 1n+m:
      (a, +v) = r
      +t = (s + v : U32)
      C.pre(m, ((a[(off + i : U32)] <- t)[(cur + i : U32)] <- t)[(off + i + 1 : U32)], (i + 1 : U32), off, cur, t)

# every body into its cell's place in the other area, carrying the mark
# that says whether the chunk owns it
def C.sc(n: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +src: U32, +dst: U32, +cur: U32, +sown: U32,
  +down: U32, +ox: U32, +oz: U32, +g: U32, +x: U32, +c: U32, +pos: U32) -> Array<U32>:
  match n ph:
    case 0n _:
      F.fin(r)
    case 1n+m 9n:
      (a, +v) = r
      C.sc(n, 8n, a[(src + i * 6 + 2 : U32)], i, src, dst, cur, sown, down, ox, oz, g, v, c, pos)
    case 1n+m 8n:
      (a, +v) = r
      +cc = C.ci(x, v, ox, oz, g)
      C.sc(n, 7n, a[(cur + cc : U32)], i, src, dst, cur, sown, down, ox, oz, g, x, cc, pos)
    case 1n+m 7n:
      (a, +v) = r
      C.sc(n, 6n, (a[(cur + c : U32)] <- (v + 1 : U32))[(sown + i : U32)], i, src, dst, cur, sown, down, ox, oz,
        g, x, c, v)
    case 1n+m 6n:
      (a, v) = r
      C.sc(n, 5n, (a[(down + pos : U32)] <- v)[(src + i * 6 : U32)], i, src, dst, cur, sown, down, ox, oz, g, x,
        c, pos)
    case 1n+m 5n:
      (a, v) = r
      C.sc(n, 4n, (a[(dst + pos * 6 : U32)] <- v)[(src + i * 6 + 1 : U32)], i, src, dst, cur, sown, down, ox, oz,
        g, x, c, pos)
    case 1n+m 4n:
      (a, v) = r
      C.sc(n, 3n, (a[(dst + pos * 6 + 1 : U32)] <- v)[(src + i * 6 + 2 : U32)], i, src, dst, cur, sown, down, ox,
        oz, g, x, c, pos)
    case 1n+m 3n:
      (a, v) = r
      C.sc(n, 2n, (a[(dst + pos * 6 + 2 : U32)] <- v)[(src + i * 6 + 3 : U32)], i, src, dst, cur, sown, down, ox,
        oz, g, x, c, pos)
    case 1n+m 2n:
      (a, v) = r
      C.sc(n, 1n, (a[(dst + pos * 6 + 3 : U32)] <- v)[(src + i * 6 + 4 : U32)], i, src, dst, cur, sown, down, ox,
        oz, g, x, c, pos)
    case 1n+m 1n:
      (a, v) = r
      C.sc(n, 0n, (a[(dst + pos * 6 + 4 : U32)] <- v)[(src + i * 6 + 5 : U32)], i, src, dst, cur, sown, down, ox,
        oz, g, x, c, pos)
    case 1n+m _:
      (a, v) = r
      C.sc(m, 9n, (a[(dst + pos * 6 + 5 : U32)] <- v)[(src + (i + 1) * 6 : U32)], (i + 1 : U32), src, dst, cur,
        sown, down, ox, oz, g, x, c, pos)

# the cells' counts back to zero before counting again
def C.clr(n: Nat, a: Array<U32>, +i: U32, +off: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+m:
      C.clr(m, a[(off + i : U32)] <- 0, (i + 1 : U32), off)

# only the chunk's own cubes kept, packed from the start: the copies it
# was given last round and the cubes that walked out of it are dropped
def C.pk0(r: Array<U32> & U32, +j: U32) -> Array<U32> & U32:
  (a, v) = r
  (a, j)

def C.pk(fuel: Nat, n: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +j: U32, +cap: U32, +ov: U32) -> Array<U32> & U32:
  match fuel n ph:
    case 0n _ _:
      C.pk0(r, j)
    case _ 0n _:
      C.pk0(r, j)
    case 1n+f 1n++m 7n:
      (a, +v) = r
      +own = Bool.not(U32.is_eq(v, 0))
      C.pk(f, Pick.n(own, n, m), Pick.n(own, 6n, 7n),
        a[Pick.u(own, (i * 6 : U32), (C.roa(cap) + i + 1 : U32))], Pick.u(own, i, (i + 1 : U32)), j, cap, v)
    case 1n+f 1n+m 6n:
      (a, v) = r
      C.pk(f, n, 5n, (a[(j * 6 : U32)] <- v)[(i * 6 + 1 : U32)], i, j, cap, ov)
    case 1n+f 1n+m 5n:
      (a, v) = r
      C.pk(f, n, 4n, (a[(j * 6 + 1 : U32)] <- v)[(i * 6 + 2 : U32)], i, j, cap, ov)
    case 1n+f 1n+m 4n:
      (a, v) = r
      C.pk(f, n, 3n, (a[(j * 6 + 2 : U32)] <- v)[(i * 6 + 3 : U32)], i, j, cap, ov)
    case 1n+f 1n+m 3n:
      (a, v) = r
      C.pk(f, n, 2n, (a[(j * 6 + 3 : U32)] <- v)[(i * 6 + 4 : U32)], i, j, cap, ov)
    case 1n+f 1n+m 2n:
      (a, v) = r
      C.pk(f, n, 1n, (a[(j * 6 + 4 : U32)] <- v)[(i * 6 + 5 : U32)], i, j, cap, ov)
    case 1n+f 1n+m _:
      (a, v) = r
      C.pk(f, m, 7n, ((a[(j * 6 + 5 : U32)] <- v)[(C.roa(cap) + j : U32)] <- ov)[(C.roa(cap) + i + 1 : U32)],
        (i + 1 : U32), (j + 1 : U32), cap, ov)

def C.keepown(+nall: U32, a: Array<U32>, +cap: U32) -> Array<U32> & U32:
  C.pk(Nat.add(Nat.mul(8n, U32.to_nat(nall)), 16n), U32.to_nat(nall), 7n, a[(C.roa(cap) : U32)], 0, 0, cap, 0)

# every body of a fresh chunk marked as its own (or not)
def C.mark(n: Nat, a: Array<U32>, +i: U32, +cap: U32, +v: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+m:
      C.mark(m, a[(C.roa(cap) + i : U32)] <- v, (i + 1 : U32), cap, v)

# how many of the chunk's bodies are its own (the rest are copies)
def C.nown(n: Nat, r: Array<U32> & U32, +i: U32, +cap: U32, +s: U32) -> Array<U32> & U32:
  match n:
    case 0n:
      C.pk0(r, s)
    case 1n+m:
      (a, +v) = r
      C.nown(m, a[(C.roa(cap) + i + 1 : U32)], (i + 1 : U32), cap, Pick.u(Bool.not(U32.is_eq(v, 0)), (s + 1 : U32), s))

def C.ro2(a: Array<U32>, +cap: U32, +gg: U32) -> Array<U32>:
  C.pre(U32.to_nat(gg), a[(C.roff(cap) + 1 : U32)], 1, C.roff(cap), C.rcur(cap, gg), 0)

def C.hm0(r: Array<U32> & U32, +yes: Bool) -> Array<U32> & Bool:
  (a, v) = r
  (a, yes)

# did a cube walk into the chunk since it last sorted? (the copies it was
# given sit past the sorted part too, but they are not its own)
def C.hm(fuel: Nat, n: Nat, r: Array<U32> & U32, +i: U32, +cap: U32, +yes: Bool) -> Array<U32> & Bool:
  match fuel n:
    case 0n _:
      C.hm0(r, yes)
    case _ 0n:
      C.hm0(r, yes)
    case 1n+f 1n+m:
      (a, +v) = r
      C.hm(f, m, a[(C.roa(cap) + i + 1 : U32)], (i + 1 : U32), cap, Bool.or(yes, U32.is_eq(v, 1)))

def Nat.min2(+a: U32, +b: U32) -> U32:
  Pick.u((a < b : U32), a, b)

def C.hm1(r: Array<U32> & U32, +n: U32, +cap: U32) -> Array<U32> & Bool:
  (a, +v) = r
  C.hm(Nat.add(U32.to_nat((n - Nat.min2(v, n) : U32)), 8n), U32.to_nat((n - Nat.min2(v, n) : U32)),
    a[(C.roa(cap) + v : U32)], v, cap, False{})

def C.hasmig(+n: U32, a: Array<U32>, +cap: U32, +gg: U32) -> Array<U32> & Bool:
  C.hm1(a[(C.roff(cap) + gg : U32)], n, cap)

# the cells' runs worked out again for the bodies as they lie now (they
# are still in order; only their places changed)
def C.reoff(+n: U32, a: Array<U32>, +cap: U32, +gg: U32, +ox: U32, +oz: U32, +g: U32) -> Array<U32>:
  C.ro2(C.cnt(U32.to_nat(n), 2n, C.clr(U32.to_nat((gg + 1 : U32)), a, 0, C.roff(cap))[0], 0, 0, C.roff(cap),
    ox, oz, g, 0, 0), cap, gg)

# a chunk's bodies sorted by cell, from area src into area dst: the counts,
# added up, then every body to its place
def C.sort3(a: Array<U32>, +n: U32, +src: U32, +dst: U32, +cap: U32, +gg: U32, +ox: U32, +oz: U32,
  +g: U32) -> Array<U32>:
  C.sc(U32.to_nat(n), 9n, a[src], 0, src, dst, C.rcur(cap, gg), C.roa(cap), C.rob(cap), ox, oz, g, 0, 0, 0)

def C.sort2(a: Array<U32>, +n: U32, +src: U32, +dst: U32, +cap: U32, +gg: U32, +ox: U32, +oz: U32,
  +g: U32) -> Array<U32>:
  C.sort3(C.pre(U32.to_nat(gg), a[(C.roff(cap) + 1 : U32)], 1, C.roff(cap), C.rcur(cap, gg), 0), n, src, dst,
    cap, gg, ox, oz, g)

def C.sort1(a: Array<U32>, +n: U32, +src: U32, +dst: U32, +cap: U32, +gg: U32, +ox: U32, +oz: U32,
  +g: U32) -> Array<U32>:
  C.sort2(C.cnt(U32.to_nat(n), 2n, a[src], 0, src, C.roff(cap), ox, oz, g, 0, 0), n, src, dst, cap, gg, ox, oz, g)

def C.sort(+n: U32, a: Array<U32>, +src: U32, +dst: U32, +cap: U32, +gg: U32, +ox: U32, +oz: U32,
  +g: U32) -> Array<U32>:
  C.sort1(C.clr(U32.to_nat((gg + 1 : U32)), a, 0, C.roff(cap)), n, src, dst, cap, gg, ox, oz, g)

# a chunk of the world: its cubes in one array, sorted by cell, and the
# first cell of its grid (the chunk's cells plus two of band on each side,
# where the cubes of the chunks around it are copied)
type Chk is Type:
  ChE{}
  ChL{a: Array<U32>, n: U32, cap: U32, ox: U32, oz: U32}
  ChN{lo: Chk, hi: Chk}

# a chunk is C.side() cells across, C.g() counting the band. The band is
# one cell wide: a cube reaches at most the cell next to its own (W.lo and
# W.span give three cells for a tick's reach), so one cell of the chunk
# next door is all a cube needs to see
def C.side() -> Nat:
  16n

def C.g() -> Nat:
  18n

def C.gg() -> Nat:
  324n

# the bodies a cube can touch, out of the sorted array: for each row of
# cells in reach, the cells it spans are one run, so the whole row costs
# two reads (its first and its last body) whatever its width -- no chain,
# no hash, and the run is side by side in memory
def C.scan(fuel: Nat, rows: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +sx: U32, +sy: U32, +sz: U32, +rad: U32,
  +off: U32, +cb: U32, +g: U32, +w: U32, +j: U32, +hi: U32, +jx: U32, +jy: U32,
  acc: List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match fuel rows ph:
    case 0n _ _:
      F.pfin(r, acc)
    case _ 0n _:
      F.pfin(r, acc)
    case 1n+f 1n++v 4n:
      (a, +lo) = r
      C.scan(f, 1n+v, 3n, a[(off + cb + w : U32)], i, sx, sy, sz, rad, off, cb, g, w, lo, hi, jx, jy, acc)
    case 1n+f 1n++v 3n:
      (a, +e) = r
      +done = U32.is_eq(j, e)
      C.scan(f, Pick.n(done, v, 1n+v), Pick.n(done, 4n, 2n),
        a[Pick.u(done, (off + cb + g : U32), (j * 6 : U32))], i, sx, sy, sz, rad, off,
        Pick.u(done, (cb + g : U32), cb), g, w, j, e, jx, jy, acc)
    case 1n+f 1n+v 2n:
      (a, v2) = r
      C.scan(f, 1n+v, 1n, a[(j * 6 + 1 : U32)], i, sx, sy, sz, rad, off, cb, g, w, j, hi, v2, jy, acc)
    case 1n+f 1n+v 1n:
      (a, v2) = r
      C.scan(f, 1n+v, 0n, a[(j * 6 + 2 : U32)], i, sx, sy, sz, rad, off, cb, g, w, j, hi, jx, v2, acc)
    case 1n+f 1n++v _:
      (a, +z) = r
      +last = U32.is_eq((j + 1 : U32), hi)
      C.scan(f, Pick.n(last, v, 1n+v), Pick.n(last, 4n, 2n),
        a[Pick.u(last, (off + cb + g : U32), ((j + 1) * 6 : U32))], i, sx, sy, sz, rad, off,
        Pick.u(last, (cb + g : U32), cb), g, w, (j + 1 : U32), hi, jx, jy,
        F.keep(Bool.and(Bool.not(U32.is_eq(j, i)),
          Bool.and((F.d(sx, jx) < rad : U32), Bool.and((F.d(sz, z) < rad : U32), (F.d(sy, jy) < rad : U32)))), j, acc))

# a run of cells that does not leave the chunk's grid
def C.fit(+w: U32, +l: U32, +g: U32) -> U32:
  Pick.u((l + w <= g : U32), w, (g - l : U32))

# one cube's tick inside its chunk: the cells it reaches (from its own size
# and the tick's reach, never a fixed number), the proven tick, and back
def C.one2(a: Array<U32>, +i: U32, +o: Og, +k: P.K, +cap: U32, +g: U32, +ox: U32, +oz: U32, +na: U32,
  +self: P.Body, +m: Nat, +mm: Nat) -> Array<U32>:
  +mr = Nat.add(m, mm)
  +sx = U32.from_nat(Nat.sub(P.Body.x(self), F.ox(o)))
  +sz = U32.from_nat(Nat.sub(P.Body.z(self), F.oz(o)))
  +lx0 = (W.lo(P.Body.x(self), mr) - W.cell_of(F.ox(o)) - ox : U32)
  +lz0 = (W.lo(P.Body.z(self), mr) - W.cell_of(F.oz(o)) - oz : U32)
  +lx = Pick.u((lx0 < g : U32), lx0, 0)
  +lz = Pick.u((lz0 < g : U32), lz0, 0)
  +wx = C.fit(U32.from_nat(W.span(P.Body.x(self), mr)), lx, g)
  +cb = (lz * g + lx : U32)
  F.two2(C.scan(Nat.add(Nat.mul(8n, U32.to_nat(cap)), 64n),
    U32.to_nat(C.fit(U32.from_nat(W.span(P.Body.z(self), mr)), lz, g)), 4n,
    a[(C.roff(cap) + cb : U32)], i, sx, U32.from_nat(P.Body.y(self)), sz,
    U32.from_nat(Nat.add(W.size(), m)), C.roff(cap), cb, g, wx, 0, 0, 0, 0, []), self, i, o, k, na, P.In.idle())

def C.one(r: Array<U32> & P.Body, +i: U32, +o: Og, +k: P.K, +cap: U32, +g: U32, +ox: U32, +oz: U32, +na: U32,
  +mm: Nat) -> Array<U32>:
  (a, +self) = r
  C.one2(a, i, o, k, cap, g, ox, oz, na, self, W.creach(k, self), mm)

def C.step(own: Bool, a: Array<U32>, +i: U32, +o: Og, +k: P.K, +cap: U32, +g: U32, +ox: U32, +oz: U32,
  +na: U32, +mm: Nat) -> Array<U32>:
  match own:
    case True{}:
      C.one(F.get(a, i, o), i, o, k, cap, g, ox, oz, na, mm)
    case False{}:
      a

# every cube of the chunk that belongs to it, in order: the sort mixes the
# chunk's own cubes with the copies of the ones around, so each body says
# which it is (the flag in its last word)
def C.ticks(n: Nat, r: Array<U32> & U32, +i: U32, +o: Og, +k: P.K, +cap: U32, +g: U32, +ox: U32, +oz: U32,
  +na: U32, +mm: Nat) -> Array<U32>:
  match n:
    case 0n:
      F.fin(r)
    case 1n+m:
      (a, +v) = r
      C.ticks(m, C.step(U32.is_eq(v, 1), a, i, o, k, cap, g, ox, oz, na, mm)[(C.roa(cap) + i + 1 : U32)],
        (i + 1 : U32), o, k, cap, g, ox, oz, na, mm)

# the sorted bodies back into the first area
def C.cp(n: Nat, r: Array<U32> & U32, +i: U32, +from: U32, +to: U32) -> Array<U32>:
  match n:
    case 0n:
      F.fin(r)
    case 1n+m:
      (a, v) = r
      C.cp(m, (a[(to + i : U32)] <- v)[(from + i + 1 : U32)], (i + 1 : U32), from, to)

# the sorted bodies, and their marks, back into the first areas
def C.copy(+n: U32, a: Array<U32>, +cap: U32) -> Array<U32>:
  C.cp(U32.to_nat(n), C.cp(U32.to_nat((n * 6 : U32)), a[(C.rb(cap) : U32)], 0, C.rb(cap), 0)[(C.rob(cap) : U32)],
    0, C.rob(cap), C.roa(cap))

# the constants as a record of this task's own: one record shared by every
# task is a reference count that every core bumps at every read
def Fb.og(o: Og) -> Og:
  Og{x, z} = o
  Og{x, z}

def Fb.kc(k: P.K) -> P.K:
  P.K{g, mu, j, acc, size} = k
  P.K{g, mu, j, acc, size}

# What a chunk sends to the ones around it
# ---------------------------------------
# After its cubes tick, a chunk sends: the cubes that left it (they belong
# to the chunk they walked into now) and copies of the cubes near its
# border (the chunk next door has to see them to not walk into them). Each
# message carries the chunk it goes to, and the walk that ticks the chunks
# splits the messages along the way -- so handing them out is parallel too.

type Msg is Data:
  Msg{d: U32, own: Bool, x: U32, y: U32, z: U32, vx: U32, vy: U32, vz: U32}

# the chunk (ix, iz) of the grid, as one number -- or one past the last
# chunk, when it falls outside the grid (a message there is dropped)
def C.ix(+ix: U32, +iz: U32, +nbx: U32, +nbz: U32) -> U32:
  Pick.u(Bool.and((ix < nbx : U32), (iz < nbz : U32)), (iz * nbx + ix : U32), (nbx * nbz : U32))

# the colour of the chunk (ix, iz)
def C.col(+ix: U32, +iz: U32) -> Nat:
  U32.to_nat(((ix .&. 1) + ((iz .&. 1) * 2) : U32))

def C.next(+ix: U32, +iz: U32, +nc: Nat) -> Bool:
  Nat.is_eq(C.col(ix, iz), nc)

def C.mv(c: Bool, +d: U32, +own: Bool, +x: U32, +y: U32, +z: U32, +vx: U32, +vy: U32, +vz: U32,
  ms: List<&2, Msg>) -> List<&2, Msg>:
  match c:
    case True{}:
      Msg{d, own, x, y, z, vx, vy, vz} <> ms
    case False{}:
      ms

# where a cube of the chunk goes: out of it (it moved away and is the next
# chunk's now), or as a copy to the sides it is near, and only to the
# chunks that tick next round -- a copy is only worth sending to a chunk
# that is about to look at it
def C.tag(+x: U32, +y: U32, +z: U32, +vx: U32, +vy: U32, +vz: U32, +ox: U32, +oz: U32, +ix: U32, +iz: U32,
  +nbx: U32, +nbz: U32, +side: U32, +nc: Nat, ms: List<&2, Msg>) -> List<&2, Msg>:
  +cx = (F.cell(x) - ox : U32)
  +cz = (F.cell(z) - oz : U32)
  +out = Bool.or(Bool.or((cx < 1 : U32), (cx >= side + 1 : U32)), Bool.or((cz < 1 : U32), (cz >= side + 1 : U32)))
  +dx = Pick.u((cx < 2 : U32), (ix - 1 : U32), Pick.u((cx >= side + 2 : U32), (ix + 1 : U32), ix))
  +dz = Pick.u((cz < 2 : U32), (iz - 1 : U32), Pick.u((cz >= side + 2 : U32), (iz + 1 : U32), iz))
  +lx = Bool.and(Bool.not(out), (cx < 2 : U32))
  +hx = Bool.and(Bool.not(out), (cx >= side : U32))
  +lz = Bool.and(Bool.not(out), (cz < 2 : U32))
  +hz = Bool.and(Bool.not(out), (cz >= side : U32))
  C.mv(out, C.ix(dx, dz, nbx, nbz), True{}, x, y, z, vx, vy, vz,
    C.mv(lx, C.ix((ix - 1 : U32), iz, nbx, nbz), False{}, x, y, z, vx, vy, vz,
      C.mv(hx, C.ix((ix + 1 : U32), iz, nbx, nbz), False{}, x, y, z, vx, vy, vz,
        C.mv(lz, C.ix(ix, (iz - 1 : U32), nbx, nbz), False{}, x, y, z, vx, vy, vz,
          C.mv(hz, C.ix(ix, (iz + 1 : U32), nbx, nbz), False{}, x, y, z, vx, vy, vz,
            C.mv(Bool.and(lx, lz),
              C.ix((ix - 1 : U32), (iz - 1 : U32), nbx, nbz), False{}, x, y, z, vx, vy, vz,
              C.mv(Bool.and(lx, hz),
                C.ix((ix - 1 : U32), (iz + 1 : U32), nbx, nbz), False{}, x, y, z, vx, vy, vz,
                C.mv(Bool.and(hx, lz),
                  C.ix((ix + 1 : U32), (iz - 1 : U32), nbx, nbz), False{}, x, y, z, vx, vy, vz,
                  C.mv(Bool.and(hx, hz),
                    C.ix((ix + 1 : U32), (iz + 1 : U32), nbx, nbz), False{}, x, y, z, vx, vy, vz, ms)))))))))

# the chunk's own cubes into messages, read straight as words: one read a
# step, and a cube that walked out loses its mark here (the next round's
# tidy-up drops it)
def F.pfinM(r: Array<U32> & U32, ms: List<&2, Msg>) -> Array<U32> & List<&2, Msg>:
  (a, v) = r
  (a, ms)

def C.emit(fuel: Nat, n: Nat, ph: Nat, r: Array<U32> & U32, +i: U32, +cap: U32, +ox: U32, +oz: U32, +ix: U32,
  +iz: U32, +nbx: U32, +nbz: U32, +side: U32, +nc: Nat, +x: U32, +y: U32, +z: U32, +vx: U32, +vy: U32,
  ms: List<&2, Msg>) -> Array<U32> & List<&2, Msg>:
  match fuel n ph:
    case 0n _ _:
      F.pfinM(r, ms)
    case _ 0n _:
      F.pfinM(r, ms)
    case 1n+f 1n++m 6n:
      (a, +v) = r
      +own = U32.is_eq(v, 1)
      C.emit(f, Pick.n(own, n, m), Pick.n(own, 5n, 6n),
        a[Pick.u(own, (i * 6 : U32), (C.roa(cap) + i + 1 : U32))], Pick.u(own, i, (i + 1 : U32)), cap, ox, oz,
        ix, iz, nbx, nbz, side, nc, x, y, z, vx, vy, ms)
    case 1n+f 1n+m 5n:
      (a, v) = r
      C.emit(f, n, 4n, a[(i * 6 + 1 : U32)], i, cap, ox, oz, ix, iz, nbx, nbz, side, nc, v, y, z, vx, vy, ms)
    case 1n+f 1n+m 4n:
      (a, v) = r
      C.emit(f, n, 3n, a[(i * 6 + 2 : U32)], i, cap, ox, oz, ix, iz, nbx, nbz, side, nc, x, v, z, vx, vy, ms)
    case 1n+f 1n+m 3n:
      (a, v) = r
      C.emit(f, n, 2n, a[(i * 6 + 3 : U32)], i, cap, ox, oz, ix, iz, nbx, nbz, side, nc, x, y, v, vx, vy, ms)
    case 1n+f 1n+m 2n:
      (a, v) = r
      C.emit(f, n, 1n, a[(i * 6 + 4 : U32)], i, cap, ox, oz, ix, iz, nbx, nbz, side, nc, x, y, z, v, vy, ms)
    case 1n+f 1n+m 1n:
      (a, v) = r
      C.emit(f, n, 0n, a[(i * 6 + 5 : U32)], i, cap, ox, oz, ix, iz, nbx, nbz, side, nc, x, y, z, vx, v, ms)
    case 1n+f 1n+m _:
      (a, +v) = r
      +gone = Bool.or(Bool.or(((F.cell(x) - ox) < 1 : U32), ((F.cell(x) - ox) >= side + 1 : U32)),
        Bool.or(((F.cell(z) - oz) < 1 : U32), ((F.cell(z) - oz) >= side + 1 : U32)))
      C.emit(f, m, 6n,
        (a[(C.roa(cap) + i : U32)] <- Pick.u(gone, 0, 1))[(C.roa(cap) + i + 1 : U32)], (i + 1 : U32), cap, ox, oz,
        ix, iz, nbx, nbz, side, nc, x, y, z, vx, vy,
        C.tag(x, y, z, vx, vy, v, ox, oz, ix, iz, nbx, nbz, side, nc, ms))

def C.w3(a: Array<U32>, +i: U32, +p: U32, +q: U32, +t: U32) -> Array<U32>:
  ((a[i] <- p)[(i + 1 : U32)] <- q)[(i + 2 : U32)] <- t

def C.put_if(c: Bool, a: Array<U32>, +i: U32, +cap: U32, +own: Bool, +x: U32, +y: U32, +z: U32, +vx: U32,
  +vy: U32, +vz: U32) -> Array<U32>:
  match c:
    case True{}:
      C.w3(C.w3(a, (i * 6 : U32), x, y, z), (i * 6 + 3 : U32), vx, vy, vz)[(C.roa(cap) + i : U32)] <- Pick.u(own, 1, 0)
    case False{}:
      a

# the cubes that came in, written from j on: the run is made twice, first
# for the ones that moved in (they are the chunk's own now), then for the
# copies, which go after them and are seen but never ticked
def C.take(ms: List<&2, Msg>, a: Array<U32>, +cap: U32, +want: Bool, +j: U32) -> Array<U32> & U32:
  match ms:
    case []:
      (a, j)
    case Msg{d, +own, +x, +y, +z, +vx, +vy, +vz} <> rest:
      +hit = Bool.or(Bool.and(own, want), Bool.and(Bool.not(own), Bool.not(want)))
      C.take(rest, C.put_if(hit, a, j, cap, own, x, y, z, vx, vy, vz), cap, want,
        Pick.u(hit, (j + 1 : U32), j))

type Mz is Data:
  Mz{a: List<&2, Msg>, b: List<&2, Msg>}

type Cr is Type:
  Cr{t: Chk, ms: List<&2, Msg>}

def Msg.d(m: Msg) -> U32:
  Msg{d, own, x, y, z, vx, vy, vz} = m
  d

def C.p2(c: Bool, +m: Msg, r: Mz) -> Mz:
  match c:
    case True{}:
      Mz{a, b} = r
      Mz{m <> a, b}
    case False{}:
      Mz{a, b} = r
      Mz{a, m <> b}

# the messages for the chunks before mid, and the rest
def C.part(ms: List<&2, Msg>, +mid: U32) -> Mz:
  match ms:
    case []:
      Mz{[], []}
    case +m <> rest:
      C.p2((Msg.d(m) < mid : U32), m, C.part(rest, mid))

def C.l5(r: Array<U32> & List<&2, Msg>, +n: U32, +cap: U32, +ox: U32, +oz: U32) -> Cr:
  (a, ms) = r
  Cr{ChL{a, n, cap, ox, oz}, ms}

# the chunk's cubes sorted and ticked, then what it sends out
def C.l4c(a: Array<U32>, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +nbx: U32, +nbz: U32,
  +side: U32, +nc: Nat) -> Cr:
  C.l5(C.emit(Nat.add(Nat.mul(8n, U32.to_nat(nall)), 16n), U32.to_nat(nall), 6n, a[(C.roa(cap) : U32)], 0, cap,
    ox, oz, ((ox + 1) / side : U32), ((oz + 1) / side : U32), nbx, nbz, side, nc, 0, 0, 0, 0, 0, []),
    nall, cap, ox, oz)

def C.l4b(a: Array<U32>, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +nbx: U32, +nbz: U32,
  +side: U32, +nc: Nat) -> Cr:
  C.l4c(a, nall, cap, ox, oz, o, nbx, nbz, side, nc)

def C.l4x(a: Array<U32>, +n: U32, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +nbx: U32, +nbz: U32,
  +side: U32, +nc: Nat) -> Cr:
  C.l5(C.emit(Nat.add(Nat.mul(8n, U32.to_nat(nall)), 16n), U32.to_nat(nall), 6n, a[(C.roa(cap) : U32)], 0, cap,
    ox, oz, ((ox + 1) / side : U32), ((oz + 1) / side : U32), nbx, nbz, side, nc, 0, 0, 0, 0, 0, []), n, cap,
    ox, oz)

def C.l4z(r: Array<U32> & U32, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +nbx: U32, +nbz: U32,
  +side: U32, +nc: Nat) -> Cr:
  (a, +n) = r
  C.l4x(a, n, n, cap, ox, oz, o, nbx, nbz, side, nc)

# a chunk that ticked: sorted, ticked, and its own cubes packed back to
# the start so the next round knows where to write what comes in
def C.l4(a: Array<U32>, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat, +nbx: U32,
  +nbz: U32, +side: U32, +nc: Nat) -> Cr:
  C.l4z(C.keepown(nall, C.ticks(U32.to_nat(nall),
    C.copy(nall, C.sort(nall, a, 0, C.rb(cap), cap, U32.from_nat(C.gg()), ox, oz, U32.from_nat(C.g())),
      cap)[(C.roa(cap) : U32)], 0, Fb.og(o), Fb.kc(k), cap, U32.from_nat(C.g()), ox, oz, nall, mm), cap),
    nall, cap, ox, oz, o, nbx, nbz, side, nc)

# only the chunks of this round's colour tick, but every chunk sends its
# border cubes every round: that is what keeps each chunk's copies of the
# ones around it up to date, whatever colour they are
# a chunk that did not tick sends its border cubes too, and counts how
# many of the bodies it holds are its own
def C.l4y(r: Array<U32> & U32, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +nbx: U32, +nbz: U32,
  +side: U32, +nc: Nat) -> Cr:
  (a, n) = r
  C.l4x(a, n, nall, cap, ox, oz, o, nbx, nbz, side, nc)

def C.l2(mine: Bool, a: Array<U32>, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K,
  +mm: Nat, +nbx: U32, +nbz: U32, +side: U32, +nc: Nat) -> Cr:
  match mine:
    case True{}:
      C.l4(a, nall, cap, ox, oz, o, k, mm, nbx, nbz, side, nc)
    case False{}:
      C.l4y(C.nown(U32.to_nat(nall), a[(C.roa(cap) : U32)], 0, cap, 0), nall, cap, ox, oz, o, nbx, nbz, side, nc)

def C.l3(r: Array<U32> & U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat, +nbx: U32, +nbz: U32,
  +side: U32, +nc: Nat, +mine: Bool) -> Cr:
  (a, nall) = r
  C.l2(mine, a, nall, cap, ox, oz, o, k, mm, nbx, nbz, side, nc)

def C.l1(r: Array<U32> & U32, +ms: List<&2, Msg>, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat,
  +nbx: U32, +nbz: U32, +side: U32, +nc: Nat, +mine: Bool) -> Cr:
  (a, n) = r
  C.l3(C.take(ms, a, cap, False{}, n), cap, ox, oz, o, k, mm, nbx, nbz, side, nc, mine)

def C.l0(r: Array<U32> & U32, +ms: List<&2, Msg>, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat,
  +nbx: U32, +nbz: U32, +side: U32, +nc: Nat, +mine: Bool) -> Cr:
  (a, n) = r
  C.l1(C.take(ms, a, cap, True{}, n), ms, cap, ox, oz, o, k, mm, nbx, nbz, side, nc, mine)

# a chunk's round: what came in is added to what it already holds, then
# its tick if this is its colour. A chunk clears the copies when it ticks
# and gathers them again from the other colours before its next tick, so
# only the chunks that just ticked have to send -- a quarter of them
def C.leaf(a: Array<U32>, +nall: U32, +cap: U32, +ox: U32, +oz: U32, +ms: List<&2, Msg>, +o: Og, +k: P.K,
  +mm: Nat, +nbx: U32, +nbz: U32, +side: U32, +nc: Nat, +mine: Bool) -> Cr:
  C.l0(C.keepown(nall, a, cap), ms, cap, ox, oz, o, k, mm, nbx, nbz, side, nc, mine)

def C.join(ra: Cr, rb: Cr) -> Cr:
  Cr{ta, ma} = ra
  Cr{tb, mb} = rb
  Cr{ChN{ta, tb}, List.append(&2, Msg, ma, mb)}

# is the chunk at (ix, iz) of this round's colour?
def C.mine(+ox: U32, +oz: U32, +side: U32, +c: Nat) -> Bool:
  U32.is_eq(((((ox + 1) / side) .&. 1) + ((((oz + 1) / side) .&. 1) * 2) : U32), U32.from_nat(c))

# Handing cubes over, array to array
# ---------------------------------
# Two chunks side by side hand each other the cubes near the border they
# share: copies, so each sees what it could touch, and the ones that
# walked across, which change owner. No list, no message -- the words go
# straight from one array to the other.

type Ck2 is Type:
  Ck2{a: Chk, b: Chk}

# which colour a chunk ticks in, and whether either of a pair is the one
# the round is preparing (an empty chunk never is)
def C.colr(t: Chk, +side: U32, +cn: Nat) -> Chk & Bool:
  match t:
    case ChE{}:
      (ChE{}, False{})
    case ChL{a, +n, +cap, +ox, +oz}:
      (ChL{a, n, cap, ox, oz}, C.mine(ox, oz, side, cn))
    case ChN{lo, hi}:
      (ChN{lo, hi}, False{})

# a cube that crossed the border changes owner along the axis of this
# pass: a cube that left by a corner crosses in x first and in z after,
# and the pass of the other axis finishes the move
def C.owns(+dx: Nat, +inx: Bool, +inz: Bool) -> Bool:
  match dx:
    case 0n:
      inz
    case _:
      inx

# is the cube (its cell cx, cz in the grid of the chunk that holds it)
# near the border towards (dx, dz), or already across it?
def C.atb(+cx: U32, +cz: U32, +dx: Nat, +dz: Nat, +side: U32) -> Bool:
  match dx dz:
    case 1n _:
      (cx >= side : U32)
    case 2n _:
      (cx < 2 : U32)
    case _ 1n:
      (cz >= side : U32)
    case _ _:
      (cz < 2 : U32)

# the first and the last cell of the run of border cells of segment seg,
# for the side (dx, dz): towards x it is two columns of each row (one run
# a row), towards z it is two whole rows (one run for all of them)
def C.sa(+seg: Nat, +dx: Nat, +dz: Nat, +side: U32, +g: U32) -> U32:
  match dx dz:
    case 1n _:
      (U32.from_nat(Nat.sub(seg, 1n)) * g + side : U32)
    case 2n _:
      (U32.from_nat(Nat.sub(seg, 1n)) * g : U32)
    case _ 1n:
      (side * g : U32)
    case _ _:
      0

def C.sb(+seg: Nat, +dx: Nat, +dz: Nat, +side: U32, +g: U32) -> U32:
  match dx dz:
    case 1n _:
      (U32.from_nat(Nat.sub(seg, 1n)) * g + side + 2 : U32)
    case 2n _:
      (U32.from_nat(Nat.sub(seg, 1n)) * g + 2 : U32)
    case _ 1n:
      ((side + 2) * g : U32)
    case _ _:
      (2 * g : U32)

# how many runs a side has: one a row towards x, one in all towards z
def C.nseg(+dx: Nat, +g: U32) -> Nat:
  match dx:
    case 0n:
      1n
    case _:
      U32.to_nat(g)

def C.gfin(r: Array<U32> & U32, b: Array<U32>, +j: U32) -> Array<U32> & Array<U32> & U32:
  (a, v) = r
  (a, (b, j))

def C.gm(a: Array<U32>, +cap: U32, +i: U32, +v: U32) -> Array<U32>:
  a[(C.roa(cap) + i : U32)] <- v

# the border cubes from one array into the other, run by run: the cubes
# are sorted by cell, so the cells of a border are one stretch of the
# array -- two reads find it, whatever it holds
def C.give2(fuel: Nat, seg: Nat, ph: Nat, r: Array<U32> & U32, b: Array<U32>, +i: U32, +j: U32, +cap: U32,
  +capb: U32, +oxa: U32, +oza: U32, +oxb: U32, +ozb: U32, +side: U32, +g: U32, +dx: Nat, +dz: Nat, +en: U32,
  +fl: U32, +x: U32, +y: U32, +z: U32, +vx: U32, +vy: U32) -> Array<U32> & Array<U32> & U32:
  match fuel seg ph:
    case 0n _ _:
      C.gfin(r, b, j)
    case _ 0n _:
      C.gfin(r, b, j)
    case 1n+f 1n++sg 9n:
      (a, +v) = r
      C.give2(f, 1n+sg, 8n, a[(C.roff(cap) + C.sb(1n+sg, dx, dz, side, g) : U32)], b, v, j, cap, capb, oxa, oza,
        oxb, ozb, side, g, dx, dz, en, fl, x, y, z, vx, vy)
    case 1n+f 1n++sg 8n:
      (a, +v) = r
      +empty = U32.is_eq(i, v)
      C.give2(f, Pick.n(empty, sg, 1n+sg), Pick.n(empty, 9n, 7n),
        a[Pick.u(empty, (C.roff(cap) + C.sa(sg, dx, dz, side, g) : U32), (C.roa(cap) + i : U32))], b, i, j, cap,
        capb, oxa, oza, oxb, ozb, side, g, dx, dz, v, fl, x, y, z, vx, vy)
    case 1n+f 1n++sg 7n:
      (a, v) = r
      C.give2(f, 1n+sg, 6n, a[(i * 6 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, g, dx, dz, en, v, x,
        y, z, vx, vy)
    case 1n+f 1n++sg 6n:
      (a, v) = r
      C.give2(f, 1n+sg, 5n, a[(i * 6 + 1 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, g, dx, dz, en,
        fl, v, y, z, vx, vy)
    case 1n+f 1n++sg 5n:
      (a, v) = r
      C.give2(f, 1n+sg, 4n, a[(i * 6 + 2 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, g, dx, dz, en,
        fl, x, v, z, vx, vy)
    case 1n+f 1n++sg 4n:
      (a, v) = r
      C.give2(f, 1n+sg, 3n, a[(i * 6 + 3 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, g, dx, dz, en,
        fl, x, y, v, vx, vy)
    case 1n+f 1n++sg 3n:
      (a, v) = r
      C.give2(f, 1n+sg, 2n, a[(i * 6 + 4 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, g, dx, dz, en,
        fl, x, y, z, v, vy)
    case 1n+f 1n++sg 2n:
      (a, v) = r
      C.give2(f, 1n+sg, 1n, a[(i * 6 + 5 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, g, dx, dz, en,
        fl, x, y, z, vx, v)
    case 1n+f 1n++sg _:
      (a, +v) = r
      # anything that is not a copy goes over the border: the chunk's own
      # cubes and the sleepers it stands on, because the neighbour has to
      # see both. It lands as the neighbour's own only if it is a cube of
      # its own that moved in (the test below), never a sleeper.
      +take = Bool.and(Bool.not(U32.is_eq(fl, 0)), C.atb((F.cell(x) - oxa : U32), (F.cell(z) - oza : U32), dx, dz, side))
      +inx = Bool.and(((F.cell(x) - oxb) >= 1 : U32), ((F.cell(x) - oxb) < side + 1 : U32))
      +inz = Bool.and(((F.cell(z) - ozb) >= 1 : U32), ((F.cell(z) - ozb) < side + 1 : U32))
      +mine = C.owns(dx, inx, inz)
      +gone = Bool.not(Bool.and(Bool.and(((F.cell(x) - oxa) >= 1 : U32), ((F.cell(x) - oxa) < side + 1 : U32)),
        Bool.and(((F.cell(z) - oza) >= 1 : U32), ((F.cell(z) - oza) < side + 1 : U32))))
      +last = U32.is_eq((i + 1 : U32), en)
      C.give2(f, Pick.n(last, sg, 1n+sg), Pick.n(last, 9n, 7n),
        C.gm(a, cap, i, Pick.u(Bool.and(gone, take), 0, fl))[Pick.u(last,
          (C.roff(cap) + C.sa(sg, dx, dz, side, g) : U32), (C.roa(cap) + i + 1 : U32))],
        C.put_if(take, b, j, capb, Bool.and(mine, U32.is_eq(fl, 1)), x, y, z, vx, vy, v), (i + 1 : U32),
        Pick.u(take, (j + 1 : U32), j), cap, capb, oxa, oza, oxb, ozb, side, g, dx, dz, en, fl, x, y, z, vx, vy)

# the cube's words from one array into the other: it lands as the second
# chunk's own if it is inside it, as a copy if it only touches it
def C.give(fuel: Nat, n: Nat, ph: Nat, r: Array<U32> & U32, b: Array<U32>, +i: U32, +j: U32, +cap: U32,
  +capb: U32, +oxa: U32, +oza: U32, +oxb: U32, +ozb: U32, +side: U32, +dx: Nat, +dz: Nat, +fl: U32, +x: U32,
  +y: U32, +z: U32, +vx: U32, +vy: U32) -> Array<U32> & Array<U32> & U32:
  match fuel n ph:
    case 0n _ _:
      C.gfin(r, b, j)
    case _ 0n _:
      C.gfin(r, b, j)
    case 1n+f 1n+m 7n:
      (a, v) = r
      C.give(f, n, 6n, a[(i * 6 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, dx, dz, v, x, y, z, vx, vy)
    case 1n+f 1n+m 6n:
      (a, v) = r
      C.give(f, n, 5n, a[(i * 6 + 1 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, dx, dz, fl, v, y, z,
        vx, vy)
    case 1n+f 1n+m 5n:
      (a, v) = r
      C.give(f, n, 4n, a[(i * 6 + 2 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, dx, dz, fl, x, v, z,
        vx, vy)
    case 1n+f 1n+m 4n:
      (a, v) = r
      C.give(f, n, 3n, a[(i * 6 + 3 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, dx, dz, fl, x, y, v,
        vx, vy)
    case 1n+f 1n+m 3n:
      (a, v) = r
      C.give(f, n, 2n, a[(i * 6 + 4 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, dx, dz, fl, x, y, z,
        v, vy)
    case 1n+f 1n+m 2n:
      (a, v) = r
      C.give(f, n, 1n, a[(i * 6 + 5 : U32)], b, i, j, cap, capb, oxa, oza, oxb, ozb, side, dx, dz, fl, x, y, z,
        vx, v)
    case 1n+f 1n+m _:
      (a, +v) = r
      # anything that is not a copy goes over the border: the chunk's own
      # cubes and the sleepers it stands on, because the neighbour has to
      # see both. It lands as the neighbour's own only if it is a cube of
      # its own that moved in (the test below), never a sleeper.
      +take = Bool.and(Bool.not(U32.is_eq(fl, 0)), C.atb((F.cell(x) - oxa : U32), (F.cell(z) - oza : U32), dx, dz, side))
      +inx = Bool.and(((F.cell(x) - oxb) >= 1 : U32), ((F.cell(x) - oxb) < side + 1 : U32))
      +inz = Bool.and(((F.cell(z) - ozb) >= 1 : U32), ((F.cell(z) - ozb) < side + 1 : U32))
      +mine = C.owns(dx, inx, inz)
      +gone = Bool.not(Bool.and(Bool.and(((F.cell(x) - oxa) >= 1 : U32), ((F.cell(x) - oxa) < side + 1 : U32)),
        Bool.and(((F.cell(z) - oza) >= 1 : U32), ((F.cell(z) - oza) < side + 1 : U32))))
      C.give(f, m, 7n,
        (a[(C.roa(cap) + i : U32)] <- Pick.u(Bool.and(gone, take), 0, fl))[(C.roa(cap) + i + 1 : U32)],
        C.put_if(take, b, j, capb, Bool.and(mine, U32.is_eq(fl, 1)), x, y, z, vx, vy, v), (i + 1 : U32),
        Pick.u(take, (j + 1 : U32), j), cap, capb, oxa, oza, oxb, ozb, side, dx, dz, fl, x, y, z, vx, vy)

# the cube's words from one array into the other: it lands as the second
# chunk's own if it is inside it, as a copy if it only touches it
def C.flip(+d: Nat) -> Nat:
  match d:
    case 1n:
      2n
    case 2n:
      1n
    case _:
      0n

def C.xp4(ab: Array<U32>, q: Array<U32> & U32, +nb: U32, +capa: U32, +oxa: U32, +oza: U32, +capb: U32,
  +oxb: U32, +ozb: U32) -> Ck2:
  (aa, na) = q
  Ck2{ChL{aa, na, capa, oxa, oza}, ChL{ab, nb, capb, oxb, ozb}}

def C.xp3(r: Array<U32> & Array<U32> & U32, +nb: U32, +capa: U32, +oxa: U32, +oza: U32, +capb: U32, +oxb: U32,
  +ozb: U32) -> Ck2:
  (ab, q) = r
  C.xp4(ab, q, nb, capa, oxa, oza, capb, oxb, ozb)

def C.xp2(aa: Array<U32>, q: Array<U32> & U32, +na: U32, +nb: U32, +capa: U32, +oxa: U32, +oza: U32,
  +capb: U32, +oxb: U32, +ozb: U32, +side: U32, +dx: Nat, +dz: Nat) -> Ck2:
  (ab, nb2) = q
  C.xp3(C.give2(Nat.add(Nat.mul(10n, Nat.add(U32.to_nat(nb), C.g())), 64n),
    C.nseg(C.flip(dx), U32.from_nat(C.g())), 9n,
    ab[(C.roff(capb) + C.sa(C.nseg(C.flip(dx), U32.from_nat(C.g())), C.flip(dx), C.flip(dz), side,
      U32.from_nat(C.g())) : U32)], aa, 0, na, capb, capa, oxb, ozb, oxa, oza, side, U32.from_nat(C.g()),
    C.flip(dx), C.flip(dz), 0, 0, 0, 0, 0, 0, 0), nb2, capa, oxa, oza, capb, oxb, ozb)

def C.xp1(r: Array<U32> & Array<U32> & U32, +na: U32, +nb: U32, +capa: U32, +oxa: U32, +oza: U32, +capb: U32,
  +oxb: U32, +ozb: U32, +side: U32, +dx: Nat, +dz: Nat) -> Ck2:
  (aa, q) = r
  C.xp2(aa, q, na, nb, capa, oxa, oza, capb, oxb, ozb, side, dx, dz)

# two chunks side by side: each hands the other what is near their border
# The handover happens for a pair only when one of the two is the one
# about to tick: a chunk needs fresh copies of its neighbours right before
# its own round, and the cubes that walked into it before it ticks. Doing
# it in every round was four times the work (and it is the part that does
# not spread over the cores).
def C.xpair2(a: Chk, b: Chk, +dx: Nat, +dz: Nat, +side: U32) -> Ck2:
  match a b:
    case ChL{aa, +na, +capa, +oxa, +oza} ChL{ab, +nb, +capb, +oxb, +ozb}:
      C.xp1(C.give2(Nat.add(Nat.mul(10n, Nat.add(U32.to_nat(na), U32.to_nat(U32.from_nat(C.g())))), 64n),
        C.nseg(dx, U32.from_nat(C.g())), 9n,
        aa[(C.roff(capa) + C.sa(C.nseg(dx, U32.from_nat(C.g())), dx, dz, side, U32.from_nat(C.g())) : U32)], ab,
        0, nb, capa, capb, oxa, oza, oxb, ozb, side, U32.from_nat(C.g()), dx, dz, 0, 0, 0, 0, 0, 0, 0),
        na, nb, capa, oxa, oza, capb, oxb, ozb, side, dx, dz)
    case _ _:
      Ck2{a, b}

def C.xskip(go: Bool, a: Chk, b: Chk, +dx: Nat, +dz: Nat, +side: U32) -> Ck2:
  match go:
    case False{}:
      Ck2{a, b}
    case True{}:
      C.xpair2(a, b, dx, dz, side)

def C.pg2(rb: Chk & Bool, a: Chk, +ba: Bool, +dx: Nat, +dz: Nat, +side: U32) -> Ck2:
  (b, +bb) = rb
  C.xskip(Bool.or(ba, bb), a, b, dx, dz, side)

def C.pg1(ra: Chk & Bool, b: Chk, +side: U32, +cn: Nat, +dx: Nat, +dz: Nat) -> Ck2:
  (a, +ba) = ra
  C.pg2(C.colr(b, side, cn), a, ba, dx, dz, side)

def C.xpair(a: Chk, b: Chk, +dx: Nat, +dz: Nat, +side: U32, +cn: Nat) -> Ck2:
  C.pg1(C.colr(a, side, cn), b, side, cn, dx, dz)

# The grid: rows of chunks
# -----------------------
# Kept as rows so that two chunks side by side can be held at once -- that
# is what lets them hand cubes over array to array, with no message in
# between.

type Rw is Type:
  RwE{}
  RwC{c: Chk, rest: Rw}

type Gr is Type:
  GrE{}
  GrC{r: Rw, rest: Gr}

type Rw2 is Type:
  Rw2{a: Rw, b: Rw}

# a row: each chunk hands over with the one on its right
def C.xrow(rest: Rw, p: Ck2, +side: U32) -> Rw:
  match rest:
    case RwE{}:
      Ck2{c, d} = p
      RwC{c, RwC{d, RwE{}}}
    case RwC{e, more}:
      Ck2{c, d} = p
      RwC{c, C.xrow(more, C.xpair2(d, e, 1n, 0n, side), side)}

def C.xr1(c: Chk, rest: Rw, +side: U32) -> Rw:
  match rest:
    case RwE{}:
      RwC{c, RwE{}}
    case RwC{d, more}:
      C.xrow(more, C.xpair2(c, d, 1n, 0n, side), side)

def C.xr0(r: Rw, +side: U32) -> Rw:
  match r:
    case RwE{}:
      RwE{}
    case RwC{c, rest}:
      C.xr1(c, rest, side)

# two rows: the chunks above and below hand over, one pair at a time
def C.zr2(c: Chk, d: Chk, p: Rw2) -> Rw2:
  Rw2{a, b} = p
  Rw2{RwC{c, a}, RwC{d, b}}

def C.zrow(ra: Rw, rb: Rw, p: Ck2, +side: U32) -> Rw2:
  match ra rb:
    case RwC{x, moreA} RwC{y, moreB}:
      Ck2{c, d} = p
      C.zr2(c, d, C.zrow(moreA, moreB, C.xpair2(x, y, 0n, 1n, side), side))
    case _ _:
      Ck2{c, d} = p
      Rw2{RwC{c, RwE{}}, RwC{d, RwE{}}}

def C.zr0(ra: Rw, rb: Rw, +side: U32) -> Rw2:
  match ra rb:
    case RwC{x, mA} RwC{y, mB}:
      C.zrow(mA, mB, C.xpair2(x, y, 0n, 1n, side), side)
    case _ _:
      Rw2{ra, rb}

def C.kill(a: Chk) -> Rw:
  match a:
    case ChE{}:
      RwE{}
    case ChL{ar, n, cap, ox, oz}:
      RwE{}
    case ChN{lo, hi}:
      RwE{}

def C.kill2(a: Chk, rest: Rw) -> Rw:
  match a:
    case ChE{}:
      rest
    case ChL{ar, n, cap, ox, oz}:
      rest
    case ChN{lo, hi}:
      rest

def C.xcons(p: Ck2, rest: Rw) -> Rw:
  Ck2{a, b} = p
  RwC{a, RwC{b, rest}}

# the row's chunks handed over two by two, every pair at the same time:
# first (0,1), (2,3) ... and then, in another run, (1,2), (3,4) ...
def C.xeven(r: Rw, have: Bool, a: Chk, +side: U32, +cn: Nat) -> Rw:
  match r have:
    case RwE{} False{}:
      C.kill(a)
    case RwC{b, more} False{}:
      C.kill2(a, C.xeven(more, True{}, b, side, cn))
    case RwE{} True{}:
      RwC{a, RwE{}}
    case RwC{b, more} True{}:
      C.xcons(C.xpair(a, b, 1n, 0n, side, cn), C.xeven(more, False{}, ChE{}, side, cn))

def C.xodd(r: Rw, +side: U32, +cn: Nat) -> Rw:
  match r:
    case RwE{}:
      RwE{}
    case RwC{a, rest}:
      RwC{a, C.xeven(rest, False{}, ChE{}, side, cn)}

def C.zjoin(p: Ck2, q: Rw2) -> Rw2:
  Ck2{c, d} = p
  Rw2{a, b} = q
  Rw2{RwC{c, a}, RwC{d, b}}

# the same for two rows, one above the other, chunk by chunk
def C.zpar(ra: Rw, rb: Rw, +side: U32, +cn: Nat) -> Rw2:
  match ra rb:
    case RwC{x, moreA} RwC{y, moreB}:
      C.zjoin(C.xpair(x, y, 0n, 1n, side, cn), C.zpar(moreA, moreB, side, cn))
    case _ _:
      Rw2{ra, rb}

def C.gcons(p: Rw2, rest: Gr) -> Gr:
  Rw2{a, b} = p
  GrC{a, GrC{b, rest}}

def C.gkill(r: Rw) -> Gr:
  match r:
    case RwE{}:
      GrE{}
    case RwC{c, rest}:
      GrE{}

def C.gkill2(r: Rw, rest: Gr) -> Gr:
  match r:
    case RwE{}:
      rest
    case RwC{c, more}:
      rest

# the rows handed over two by two, all pairs at the same time
def C.geven(g: Gr, have: Bool, r: Rw, +side: U32, +cn: Nat) -> Gr:
  match g have:
    case GrE{} False{}:
      C.gkill(r)
    case GrC{r2, more} False{}:
      C.gkill2(r, C.geven(more, True{}, r2, side, cn))
    case GrE{} True{}:
      GrC{r, GrE{}}
    case GrC{r2, more} True{}:
      p q = C.zpar(r, r2, side, cn) C.geven(more, False{}, RwE{}, side, cn)
      C.gcons(p, q)

def C.godd(g: Gr, +side: U32, +cn: Nat) -> Gr:
  match g:
    case GrE{}:
      GrE{}
    case GrC{r, rest}:
      GrC{r, C.geven(rest, False{}, RwE{}, side, cn)}

# every row's chunks hand over inside the row (two runs), and then the
# rows with each other (two more) -- every pair of a run at once
def C.gxr(g: Gr, +side: U32, +cn: Nat) -> Gr:
  match g:
    case GrE{}:
      GrE{}
    case GrC{r, rest}:
      a b = C.xodd(C.xeven(r, False{}, ChE{}, side, cn), side, cn) C.gxr(rest, side, cn)
      GrC{a, b}

def C.gzr2(g: Gr, +side: U32, +cn: Nat) -> Gr:
  C.godd(C.geven(g, False{}, RwE{}, side, cn), side, cn)

# the whole grid: every row hands over inside itself, all rows at once
def C.gx(g: Gr, +side: U32) -> Gr:
  match g:
    case GrE{}:
      GrE{}
    case GrC{r, rest}:
      a b = C.xr0(r, side) C.gx(rest, side)
      GrC{a, b}

# then each row with the one below it
def C.gzr(rest: Gr, p: Rw2, +side: U32) -> Gr:
  match rest:
    case GrE{}:
      Rw2{a, b} = p
      GrC{a, GrC{b, GrE{}}}
    case GrC{r2, more}:
      Rw2{a, b} = p
      GrC{a, C.gzr(more, C.zr0(b, r2, side), side)}

def C.gz1(r: Rw, rest: Gr, +side: U32) -> Gr:
  match rest:
    case GrE{}:
      GrC{r, GrE{}}
    case GrC{r2, more}:
      C.gzr(more, C.zr0(r, r2, side), side)

def C.gz(g: Gr, +side: U32) -> Gr:
  match g:
    case GrE{}:
      GrE{}
    case GrC{r, rest}:
      C.gz1(r, rest, side)

# Between the two shapes
# ----------------------
# The grid is kept as rows so that two chunks side by side can be held at
# once (that is how they hand cubes over). The tick wants the other shape:
# a balanced tree, which is what Bend's scheduler spreads over the cores.
# Going from one to the other is a walk over the chunks, and costs nothing
# next to the tick.

def C.rcat(a: Rw, b: Rw) -> Rw:
  match a:
    case RwE{}:
      b
    case RwC{c, rest}:
      RwC{c, C.rcat(rest, b)}

def C.gcat(g: Gr) -> Rw:
  match g:
    case GrE{}:
      RwE{}
    case GrC{r, rest}:
      C.rcat(r, C.gcat(rest))

# the chunks paired into nodes, over and over, until one tree is left
def C.pairup(r: Rw, have: Bool, a: Chk) -> Rw:
  match r have:
    case RwE{} False{}:
      C.kill(a)
    case RwC{b, more} False{}:
      C.kill2(a, C.pairup(more, True{}, b))
    case RwE{} True{}:
      RwC{a, RwE{}}
    case RwC{b, more} True{}:
      RwC{ChN{a, b}, C.pairup(more, False{}, ChE{})}

def C.build(lv: Nat, r: Rw) -> Rw:
  match lv:
    case 0n:
      r
    case 1n+m:
      C.build(m, C.pairup(r, False{}, ChE{}))

def C.kill3(c: Chk, rest: Rw) -> Chk:
  match rest:
    case RwE{}:
      c
    case RwC{d, more}:
      c

def C.one1(r: Rw) -> Chk:
  match r:
    case RwE{}:
      ChE{}
    case RwC{c, rest}:
      C.kill3(c, rest)

def C.mktree(lv: Nat, r: Rw) -> Chk:
  C.one1(C.build(lv, r))

# and the tree back into a list
def C.unt(t: Chk, acc: Rw) -> Rw:
  match t:
    case ChE{}:
      acc
    case ChL{a, n, cap, ox, oz}:
      RwC{ChL{a, n, cap, ox, oz}, acc}
    case ChN{lo, hi}:
      C.unt(lo, C.unt(hi, acc))

def C.rev(r: Rw, acc: Rw) -> Rw:
  match r:
    case RwE{}:
      acc
    case RwC{c, rest}:
      C.rev(rest, RwC{c, acc})

# the list back into rows of nbx chunks
def C.rsplit(n: Nat, r: Rw, acc: Rw) -> Rw2:
  match n r:
    case 0n _:
      Rw2{C.rev(acc, RwE{}), r}
    case _ RwE{}:
      Rw2{C.rev(acc, RwE{}), RwE{}}
    case 1n+m RwC{c, rest}:
      C.rsplit(m, rest, RwC{c, acc})

# the list back into rows of nbx chunks
def C.grows(rows: Nat, p: Rw2, +nbx: Nat) -> Gr:
  match rows:
    case 0n:
      Rw2{a, b} = p
      C.gkill2(a, C.gkill(b))
    case 1n+m:
      Rw2{a, b} = p
      GrC{a, C.grows(m, C.rsplit(nbx, b, RwE{}), nbx)}

def C.rows0(r: Rw, +nbx: Nat, rows: Nat) -> Gr:
  C.grows(rows, C.rsplit(nbx, r, RwE{}), nbx)

type ChL2 is Type:
  ChL2{c: Chk, bs: List<&2, P.Body>}

type Gr2 is Type:
  Gr2{g: Gr, bs: List<&2, P.Body>}

type Rw2b is Type:
  Rw2b{r: Rw, bs: List<&2, P.Body>}

# the chunk's own cubes as bodies again (the copies it holds of the ones
# around it are not its to give back)
def C.bw2(r: Array<U32> & P.Body, acc: List<&2, P.Body>) -> Array<U32> & List<&2, P.Body>:
  (a, b) = r
  (a, b <> acc)

def C.bw(own: Bool, a: Array<U32>, +i: U32, +o: Og, acc: List<&2, P.Body>) -> Array<U32> & List<&2, P.Body>:
  match own:
    case True{}:
      C.bw2(F.get(a, i, o), acc)
    case False{}:
      (a, acc)

def C.bw1(r: Array<U32> & U32, +i: U32, +o: Og, acc: List<&2, P.Body>, +want: U32) -> Array<U32> & List<&2, P.Body>:
  (a, +v) = r
  C.bw(U32.is_eq(v, want), a, i, o, acc)

def C.bw0(a: Array<U32>, +i: U32, +cap: U32, +o: Og, acc: List<&2, P.Body>, +want: U32) -> Array<U32> & List<&2, P.Body>:
  C.bw1(a[(C.roa(cap) + i : U32)], i, o, acc, want)

def C.bodies(n: Nat, r: Array<U32> & List<&2, P.Body>, +i: U32, +cap: U32, +o: Og, +want: U32) -> Array<U32> & List<&2, P.Body>:
  match n:
    case 0n:
      r
    case 1n+m:
      (a, acc) = r
      C.bodies(m, C.bw0(a, i, cap, o, acc, want), (i + 1 : U32), cap, o, want)

def C.cb2(r: Array<U32> & List<&2, P.Body>, +n: U32, +cap: U32, +ox: U32, +oz: U32) -> ChL2:
  (a, bs) = r
  ChL2{ChL{a, n, cap, ox, oz}, bs}

def C.cbj(x: ChL2, y: ChL2) -> ChL2:
  ChL2{ta, ba} = x
  ChL2{tb, bb} = y
  ChL2{ChN{ta, tb}, List.append(&2, P.Body, ba, bb)}

def C.cbodies(t: Chk, +o: Og, +want: U32) -> ChL2:
  match t:
    case ChE{}:
      ChL2{ChE{}, []}
    case ChL{a, +n, +cap, +ox, +oz}:
      C.cb2(C.bodies(U32.to_nat(n), (a, []), 0, cap, o, want), n, cap, ox, oz)
    case ChN{lo, hi}:
      C.cbj(C.cbodies(lo, o, want), C.cbodies(hi, o, want))

def C.rbj(x: ChL2, y: Rw2b) -> Rw2b:
  ChL2{c, ba} = x
  Rw2b{r, bb} = y
  Rw2b{RwC{c, r}, List.append(&2, P.Body, ba, bb)}

def C.rbodies(r: Rw, +o: Og, +want: U32) -> Rw2b:
  match r:
    case RwE{}:
      Rw2b{RwE{}, []}
    case RwC{c, rest}:
      C.rbj(C.cbodies(c, o, want), C.rbodies(rest, o, want))

def C.gbj(x: Rw2b, y: Gr2) -> Gr2:
  Rw2b{r, ba} = x
  Gr2{g, bb} = y
  Gr2{GrC{r, g}, List.append(&2, P.Body, ba, bb)}

# every cube of the grid, to count them and look for overlaps
def C.gbodies(g: Gr, +o: Og, +want: U32) -> Gr2:
  match g:
    case GrE{}:
      Gr2{GrE{}, []}
    case GrC{r, rest}:
      C.gbj(C.rbodies(r, o, want), C.gbodies(rest, o, want))

# a chunk tidied: only its own cubes kept, packed from the start (the
# copies of the round before and the ones that walked out are dropped)
def C.tidy1(r: Array<U32> & U32, +cap: U32, +ox: U32, +oz: U32) -> Chk:
  (a, +n) = r
  ChL{C.reoff(n, a, cap, U32.from_nat(C.gg()), ox, oz, U32.from_nat(C.g())), n, cap, ox, oz}

def C.tidy(t: Chk) -> Chk:
  match t:
    case ChE{}:
      ChE{}
    case ChL{a, +n, +cap, +ox, +oz}:
      C.tidy1(C.keepown(n, a, cap), cap, ox, oz)
    case ChN{lo, hi}:
      ChN{C.tidy(lo), C.tidy(hi)}

def C.rtidy(r: Rw) -> Rw:
  match r:
    case RwE{}:
      RwE{}
    case RwC{c, rest}:
      a b = C.tidy(c) C.rtidy(rest)
      RwC{a, b}

def C.gtidy(g: Gr) -> Gr:
  match g:
    case GrE{}:
      GrE{}
    case GrC{r, rest}:
      a b = C.rtidy(r) C.gtidy(rest)
      GrC{a, b}

# every chunk's tick at the same time, each on its own array: sort by cell,
# then every cube of the chunk in order. Nothing shared is read inside, so
# the cores fill up (a shared list or trie would count references atomically)
def C.r2(a: Array<U32>, +n: U32, +o: Og, +k: P.K, +cap: U32, +ox: U32, +oz: U32, +mm: Nat) -> Array<U32>:
  C.ticks(U32.to_nat(n), a[(C.roa(cap) : U32)], 0, Fb.og(o), Fb.kc(k), cap, U32.from_nat(C.g()), ox, oz, n, mm)

# the chunk's own cubes sorted and ticked, if this round is its colour
def C.ct2(mine: Bool, a: Array<U32>, +n: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat) -> Chk:
  match mine:
    case True{}:
      ChL{C.r2(C.copy(n, C.sort(n, a, 0, C.rb(cap), cap, U32.from_nat(C.gg()), ox, oz, U32.from_nat(C.g())), cap),
        n, o, k, cap, ox, oz, mm), n, cap, ox, oz}
    case False{}:
      ChL{a, n, cap, ox, oz}

def C.ctick(t: Chk, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +side: U32) -> Chk:
  match t:
    case ChE{}:
      ChE{}
    case ChL{a, +n, +cap, +ox, +oz}:
      C.ct2(C.mine(ox, oz, side, c), a, n, cap, ox, oz, o, k, mm)
    case ChN{lo, hi}:
      ChN{C.ctick(lo, c, o, k, mm, side), C.ctick(hi, c, o, k, mm, side)}

def C.rtick(r: Rw, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +side: U32) -> Rw:
  match r:
    case RwE{}:
      RwE{}
    case RwC{ch, rest}:
      a b = C.ctick(ch, c, o, k, mm, side) C.rtick(rest, c, o, k, mm, side)
      RwC{a, b}

def C.gtick(g: Gr, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +side: U32) -> Gr:
  match g:
    case GrE{}:
      GrE{}
    case GrC{r, rest}:
      a b = C.rtick(r, c, o, k, mm, side) C.gtick(rest, c, o, k, mm, side)
      GrC{a, b}

# the tick over the tree: the chunks of this colour sort and tick, and
# every chunk then keeps only its own cubes (the copies of the round
# before go, and so do the ones that walked out). Both halves at once --
# the walk does nothing but fork, which is what fills the cores
def C.ft3(mine: Bool, a: Array<U32>, +n: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat) -> Chk:
  match mine:
    case True{}:
      C.tidy1(C.keepown(n, C.r2(C.copy(n, C.sort(n, a, 0, C.rb(cap), cap, U32.from_nat(C.gg()), ox, oz,
        U32.from_nat(C.g())), cap), n, o, k, cap, ox, oz, mm), cap), cap, ox, oz)
    case False{}:
      C.tidy1(C.keepown(n, C.copy(n, C.sort(n, a, 0, C.rb(cap), cap, U32.from_nat(C.gg()), ox, oz,
        U32.from_nat(C.g())), cap), cap), cap, ox, oz)

def C.ft4(sorted: Bool, a: Array<U32>, +n: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K,
  +mm: Nat) -> Chk:
  match sorted:
    case True{}:
      C.tidy1(C.keepown(n, a, cap), cap, ox, oz)
    case False{}:
      C.ft3(False{}, a, n, cap, ox, oz, o, k, mm)

def C.ft1(r: Array<U32> & Bool, +n: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat) -> Chk:
  (a, +mig) = r
  C.ft4(Bool.not(mig), a, n, cap, ox, oz, o, k, mm)

# a chunk sorts when it is its turn to tick, and also when cubes walked
# into it (they arrive at the end of the array, outside the order): the
# border runs are read from the order, so it has to hold
def C.ft2(mine: Bool, a: Array<U32>, +n: U32, +cap: U32, +ox: U32, +oz: U32, +o: Og, +k: P.K, +mm: Nat) -> Chk:
  match mine:
    case True{}:
      C.ft3(True{}, a, n, cap, ox, oz, o, k, mm)
    case False{}:
      C.ft1(C.hasmig(n, a, cap, U32.from_nat(C.gg())), n, cap, ox, oz, o, k, mm)

def C.ftick(t: Chk, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +side: U32) -> Chk:
  match t:
    case ChE{}:
      ChE{}
    case ChL{a, +n, +cap, +ox, +oz}:
      C.ft2(C.mine(ox, oz, side, c), a, n, cap, ox, oz, o, k, mm)
    case ChN{lo, hi}:
      x y = C.ftick(lo, c, o, k, mm, side) C.ftick(hi, c, o, k, mm, side)
      ChN{x, y}

# a round the other way round: the cubes tick in the tree shape (all
# cores), then the grid goes back to rows so that neighbours can hand
# cubes over array to array. Measured slower than the messages above (the
# handover walks every cube of every chunk, four ways a round), kept for
# the record
def C.round3(g: Gr, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +side: U32, +lv: Nat, +nbx: Nat, +rows: Nat) -> Gr:
  C.gzr2(C.gxr(C.rows0(C.unt(C.ftick(C.mktree(lv, C.gcat(g)), c, o, k, mm, side), RwE{}), nbx, rows), side,
    Nat.mod(Nat.add(c, 1n), 4n)), side, Nat.mod(Nat.add(c, 1n), 4n))

def C.tick3(g: Gr, +o: Og, +k: P.K, +mm: Nat, +side: U32, +lv: Nat, +nbx: Nat, +rows: Nat) -> Gr:
  C.round3(C.round3(C.round3(C.round3(g, 0n, o, k, mm, side, lv, nbx, rows), 1n, o, k, mm, side, lv, nbx, rows),
    2n, o, k, mm, side, lv, nbx, rows), 3n, o, k, mm, side, lv, nbx, rows)

# a round: every chunk tidied, the borders handed over (along the rows,
# then between them), and the chunks of this colour ticked -- two chunks
# of a colour are two chunks apart, so no cube is pushed by two of them
def C.round2(g: Gr, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +side: U32) -> Gr:
  C.gtick(C.gzr2(C.gxr(C.gtidy(g), side, Nat.mod(Nat.add(c, 1n), 4n)), side, Nat.mod(Nat.add(c, 1n), 4n)),
    c, o, k, mm, side)

# a tick: the four colours
def C.tick2(g: Gr, +o: Og, +k: P.K, +mm: Nat, +side: U32) -> Gr:
  C.round2(C.round2(C.round2(C.round2(g, 0n, o, k, mm, side), 1n, o, k, mm, side), 2n, o, k, mm, side), 3n, o, k,
    mm, side)

def C.keep(c: Bool, +m: Msg, ms: List<&2, Msg>) -> List<&2, Msg>:
  match c:
    case True{}:
      m <> ms
    case False{}:
      ms

# the messages for the chunks from lo to hi - 1
def C.only(ms: List<&2, Msg>, +lo: U32, +hi: U32) -> List<&2, Msg>:
  match ms:
    case []:
      []
    case +m <> rest:
      C.keep(Bool.and((Msg.d(m) >= lo : U32), (Msg.d(m) < hi : U32)), m, C.only(rest, lo, hi))

# a round: the messages walk down the tree with the halves, so handing
# them out runs at the same time as the ticks. Only the chunks of this
# round's colour tick; the rest just take in what came to them
# each half is handed its own list, split by the one above it: two tasks
# reading one list would count references on every cell, atomically
def C.round(t: Chk, z: Mz, +lo: U32, +hi: U32, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +nbx: U32, +nbz: U32,
  +side: U32) -> Cr:
  match t:
    case ChE{}:
      Mz{ma, mb} = z
      Cr{ChE{}, []}
    case ChL{a, +n, +cap, +ox, +oz}:
      Mz{ma, mb} = z
      C.leaf(a, n, cap, ox, oz, List.append(&2, Msg, ma, mb), o, k, mm, nbx, nbz, side,
        Nat.mod(Nat.add(c, 1n), 4n), C.mine(ox, oz, side, c))
    case ChN{l, h}:
      Mz{ma, mb} = z
      +mid = ((lo + hi) / 2 : U32)
      x y = C.round(l, C.part(ma, ((lo + mid) / 2 : U32)), lo, mid, c, o, k, mm, nbx, nbz, side)
            C.round(h, C.part(mb, ((mid + hi) / 2 : U32)), mid, hi, c, o, k, mm, nbx, nbz, side)
      C.join(x, y)

# (The way below hands the border cubes over as messages down the tree.
# It is faster on paper -- 3,8 mil instructions a cube-tick against 6,5
# mil -- but the collision test still finds an overlap in it, so the tick
# the game would use is the one above, which hands cubes over array to
# array. Kept for the measurement.)
#
# Handing the messages out and ticking are two walks, not one: the tick's
# walk then forks and does nothing else, which is what fills the cores
# (measured: one walk that also splits lists stops at five of them).

def C.dl(+cap: U32, +ox: U32, +oz: U32, r: Array<U32> & U32) -> Chk:
  (a, n) = r
  ChL{a, n, cap, ox, oz}

def C.dl1(r: Array<U32> & U32, +cap: U32, +ox: U32, +oz: U32, +ms: List<&2, Msg>) -> Chk:
  (a, +n) = r
  C.dl(cap, ox, oz, C.take(ms, a, cap, False{}, n))

def C.dl0(+ms: List<&2, Msg>, a: Array<U32>, +n: U32, +cap: U32, +ox: U32, +oz: U32) -> Chk:
  C.dl1(C.take(ms, a, cap, True{}, n), cap, ox, oz, ms)

# what came in, written from the cubes the chunk already holds on
def C.deliver(t: Chk, z: Mz, +lo: U32, +hi: U32) -> Chk:
  match t:
    case ChE{}:
      Mz{ma, mb} = z
      ChE{}
    case ChL{a, +n, +cap, +ox, +oz}:
      Mz{ma, mb} = z
      C.dl0(List.append(&2, Msg, ma, mb), a, n, cap, ox, oz)
    case ChN{l, h}:
      Mz{ma, mb} = z
      +mid = ((lo + hi) / 2 : U32)
      x y = C.deliver(l, C.part(ma, ((lo + mid) / 2 : U32)), lo, mid)
            C.deliver(h, C.part(mb, ((mid + hi) / 2 : U32)), mid, hi)
      ChN{x, y}

# the chunks of this colour tick, and say what they send; nothing else
def C.tickall(t: Chk, +c: Nat, +o: Og, +k: P.K, +mm: Nat, +nbx: U32, +nbz: U32, +side: U32) -> Cr:
  match t:
    case ChE{}:
      Cr{ChE{}, []}
    case ChL{a, +n, +cap, +ox, +oz}:
      C.l2(C.mine(ox, oz, side, c), a, n, cap, ox, oz, o, k, mm, nbx, nbz, side, Nat.mod(Nat.add(c, 1n), 4n))
    case ChN{l, h}:
      x y = C.tickall(l, c, o, k, mm, nbx, nbz, side) C.tickall(h, c, o, k, mm, nbx, nbz, side)
      C.join(x, y)

def C.t2(r: Cr, +c: Nat, +nch: U32, +o: Og, +k: P.K, +mm: Nat, +nbx: U32, +nbz: U32, +side: U32) -> Cr:
  Cr{t, ms} = r
  C.tickall(C.deliver(t, C.part(C.only(ms, 0, nch), ((nch) / 2 : U32)), 0, nch), c, o, k, mm, nbx, nbz, side)

# a tick of the whole crowd: four rounds, one per colour. What a round's
# chunks send is handed out at the start of the next one -- and what the
# last round sends waits for the next tick, when it is still fresh (those
# chunks have not moved since)
def C.tick(r: Cr, +nch: U32, +o: Og, +k: P.K, +mm: Nat, +nbx: U32, +nbz: U32, +side: U32) -> Cr:
  C.t2(C.t2(C.t2(C.t2(r, 0n, nch, o, k, mm, nbx, nbz, side), 1n, nch, o, k, mm, nbx, nbz, side), 2n, nch, o, k,
    mm, nbx, nbz, side), 3n, nch, o, k, mm, nbx, nbz, side)

def C.run(t: Chk, +o: Og, +k: P.K, +mm: Nat) -> Chk:
  match t:
    case ChE{}:
      ChE{}
    case ChL{a, +n, +cap, +ox, +oz}:
      ChL{C.r2(C.copy(n, C.sort(n, a, 0, C.rb(cap), cap, U32.from_nat(C.gg()), ox, oz, U32.from_nat(C.g())), cap),
        n, o, k, cap, ox, oz, mm), n, cap, ox, oz}
    case ChN{lo, hi}:
      x y = C.run(lo, o, k, mm) C.run(hi, o, k, mm)
      ChN{x, y}

# The crowd's tick, block by block, all at once
# --------------------------------------------
# The cubes of a block of 4 x 4 m tick together, and blocks two apart never
# touch the same cube, so a tick runs four rounds (the colours of a 2 x 2
# checkerboard) and every block of a round runs at the same time as the
# others. A task gets its own little array -- its cubes first, then the
# ones around it that they can touch, copied straight out of the crowd's
# array -- so it reads nothing shared while it runs: what Bend needs to
# fill the cores (a shared list or trie makes every read count references
# atomically, and the cores go idle).

type Fa is Type:
  FaE{}
  FaL{a: Array<U32>, nown: U32, nall: U32, cap: U32}
  FaN{lo: Fa, hi: Fa}

def Fb.lg() -> Nat:
  2n

# the block a cell belongs to
def Fb.of(+c: U32) -> U32:
  (c >> Fb.lg() : U32)

# the first cell of block b, and the one after its last
def Fb.c0(+b: U32) -> U32:
  (b << Fb.lg() : U32)

def Fb.c1(+b: U32) -> U32:
  ((b + 1 << Fb.lg()) - 1 : U32)

# is the cell (cx, cz) inside the block (bx, bz)?
def Fb.in(+cx: U32, +cz: U32, +bx: U32, +bz: U32) -> Bool:
  Bool.and(U32.is_eq(Fb.of(cx), bx), U32.is_eq(Fb.of(cz), bz))

def Fb.ct(r: Array<U32> & U32, +own: U32, +all: U32) -> Array<U32> & U32 & U32:
  (a, v) = r
  (a, (own, all))

# how many bodies the cells of a block and the two cells around it hold:
# own (awake and homed in the block) and all of them. One read a step: the
# chain's next link -- the cell alone says whether a body is the block's.
def Fb.cnt(fuel: Nat, cn: Nat, ph: Nat, r: Array<U32> & U32, +na: U32, +cap: U32, +msk: U32, +lox: U32,
  +hix: U32, +cx: U32, +cz: U32, +bx: U32, +bz: U32, +j: U32, +own: U32, +all: U32) -> Array<U32> & U32 & U32:
  match fuel cn ph:
    case 0n _ _:
      Fb.ct(r, own, all)
    case _ 0n _:
      Fb.ct(r, own, all)
    case 1n+f 1n++c 0n:
      (a, +v) = r
      +e = U32.is_eq(v, 0)
      +w = U32.is_eq(cx, hix)
      +ncx = Pick.u(w, lox, (cx + 1 : U32))
      +ncz = Pick.u(w, (cz + 1 : U32), cz)
      Fb.cnt(f, Pick.n(e, c, 1n+c), Pick.n(e, 0n, 1n),
        a[Pick.u(e, (F.hd(cap) + F.slot2(ncx, ncz, msk) : U32), (F.hd(cap) + cap + v - 1 : U32))], na, cap, msk,
        lox, hix, Pick.u(e, ncx, cx), Pick.u(e, ncz, cz), bx, bz, (v - 1 : U32), own, all)
    case 1n+f 1n+c _:
      (a, +v) = r
      +here = U32.is_eq(v, F.key2(cx, cz))
      Fb.cnt(f, 1n+c, 0n, a[(F.nx(cap) + j : U32)], na, cap, msk, lox, hix, cx, cz, bx, bz, j,
        Pick.u(Bool.and(here, Bool.and((j < na : U32), Fb.in(cx, cz, bx, bz))), (own + 1 : U32), own),
        Pick.u(here, (all + 1 : U32), all))

def Fb.cf(r: Array<U32> & U32, d: Array<U32>) -> Array<U32> & Array<U32>:
  (a, v) = r
  (a, d)

# the same walk, copying what it finds into the block's own array: its
# cubes first (slots 0 .. nown - 1), then the ones around, and the body's
# place in the crowd's array kept at 8 cap + slot, to write the tick back
def Fb.cpy(fuel: Nat, cn: Nat, ph: Nat, r: Array<U32> & U32, d: Array<U32>, +na: U32, +cap: U32, +msk: U32,
  +lox: U32, +hix: U32, +cx: U32, +cz: U32, +bx: U32, +bz: U32, +nown: U32, +dcap: U32, +j: U32, +slot: U32,
  +io: U32, +ih: U32) -> Array<U32> & Array<U32>:
  match fuel cn ph:
    case 0n _ _:
      Fb.cf(r, d)
    case _ 0n _:
      Fb.cf(r, d)
    case 1n+f 1n++c 0n:
      (a, +v) = r
      +e = U32.is_eq(v, 0)
      +w = U32.is_eq(cx, hix)
      +ncx = Pick.u(w, lox, (cx + 1 : U32))
      +ncz = Pick.u(w, (cz + 1 : U32), cz)
      Fb.cpy(f, Pick.n(e, c, 1n+c), Pick.n(e, 0n, 1n),
        a[Pick.u(e, (F.hd(cap) + F.slot2(ncx, ncz, msk) : U32), (F.hd(cap) + cap + v - 1 : U32))], d, na, cap, msk,
        lox, hix, Pick.u(e, ncx, cx), Pick.u(e, ncz, cz), bx, bz, nown, dcap, (v - 1 : U32), slot, io, ih)
    case 1n+f 1n+c 1n:
      (a, +v) = r
      +here = U32.is_eq(v, F.key2(cx, cz))
      +mine = Bool.and((j < na : U32), Fb.in(cx, cz, bx, bz))
      Fb.cpy(f, 1n+c, Pick.n(here, 2n, 0n),
        a[Pick.u(here, (j * 6 : U32), (F.nx(cap) + j : U32))], d, na, cap, msk, lox, hix, cx, cz, bx, bz, nown,
        dcap, j, Pick.u(mine, io, (nown + ih : U32)),
        Pick.u(Bool.and(here, mine), (io + 1 : U32), io),
        Pick.u(Bool.and(here, Bool.not(mine)), (ih + 1 : U32), ih))
    case 1n+f 1n+c 2n:
      (a, v) = r
      Fb.cpy(f, 1n+c, 3n, a[(j * 6 + 1 : U32)], d[(slot * 6 : U32)] <- v, na, cap, msk, lox, hix, cx, cz, bx, bz,
        nown, dcap, j, slot, io, ih)
    case 1n+f 1n+c 3n:
      (a, v) = r
      Fb.cpy(f, 1n+c, 4n, a[(j * 6 + 2 : U32)], d[(slot * 6 + 1 : U32)] <- v, na, cap, msk, lox, hix, cx, cz, bx, bz,
        nown, dcap, j, slot, io, ih)
    case 1n+f 1n+c 4n:
      (a, v) = r
      Fb.cpy(f, 1n+c, 5n, a[(j * 6 + 3 : U32)], d[(slot * 6 + 2 : U32)] <- v, na, cap, msk, lox, hix, cx, cz, bx, bz,
        nown, dcap, j, slot, io, ih)
    case 1n+f 1n+c 5n:
      (a, v) = r
      Fb.cpy(f, 1n+c, 6n, a[(j * 6 + 4 : U32)], d[(slot * 6 + 3 : U32)] <- v, na, cap, msk, lox, hix, cx, cz, bx, bz,
        nown, dcap, j, slot, io, ih)
    case 1n+f 1n+c 6n:
      (a, v) = r
      Fb.cpy(f, 1n+c, 7n, a[(j * 6 + 5 : U32)], d[(slot * 6 + 4 : U32)] <- v, na, cap, msk, lox, hix, cx, cz, bx, bz,
        nown, dcap, j, slot, io, ih)
    case 1n+f 1n+c _:
      (a, v) = r
      Fb.cpy(f, 1n+c, 0n, a[(F.nx(cap) + j : U32)],
        (d[(slot * 6 + 5 : U32)] <- v)[(F.hd(dcap) + dcap + slot : U32)] <- j, na, cap, msk, lox, hix, cx, cz,
        bx, bz, nown, dcap, j, slot, io, ih)

def Fb.mk6(r: Array<U32> & Array<U32>, +own: U32, +all: U32, +dcap: U32) -> Array<U32> & Fa:
  (a, d) = r
  (a, FaL{F.build(all, d, dcap, (dcap - 1 : U32)), own, all, dcap})

def Fb.mk5(a: Array<U32>, +own: U32, +all: U32, +bx: U32, +bz: U32, +na: U32, +cap: U32, +msk: U32, +lox: U32,
  +hix: U32, +loz: U32, +cells: Nat, rc: U32 & Nat) -> Array<U32> & Fa:
  (+dcap, b) = rc
  Fb.mk6(Fb.cpy(Nat.add(Nat.mul(16n, Nat.add(U32.to_nat(all), cells)), 64n), cells, 0n,
    a[(F.hd(cap) + F.slot2(lox, loz, msk) : U32)], Array.new(U32, Nat.add(b, 4n), 0), na, cap, msk, lox, hix,
    lox, loz, bx, bz, own, dcap, 0, 0, 0, 0), own, all, dcap)

def Fb.mk4(empty: Bool, a: Array<U32>, +own: U32, +all: U32, +bx: U32, +bz: U32, +na: U32, +cap: U32, +msk: U32,
  +lox: U32, +hix: U32, +loz: U32, +cells: Nat) -> Array<U32> & Fa:
  match empty:
    case True{}:
      (a, FaE{})
    case False{}:
      Fb.mk5(a, own, all, bx, bz, na, cap, msk, lox, hix, loz, cells, F.cap0(all))

def Fb.mk3(a: Array<U32>, p: U32 & U32, +bx: U32, +bz: U32, +na: U32, +cap: U32, +msk: U32, +lox: U32, +hix: U32,
  +loz: U32, +cells: Nat) -> Array<U32> & Fa:
  (+own, +all) = p
  Fb.mk4(Bool.or(U32.is_eq(own, 0), U32.is_eq(all, 0)), a, own, all, bx, bz, na, cap, msk, lox, hix, loz, cells)

def Fb.mk2(r: Array<U32> & U32 & U32, +bx: U32, +bz: U32, +na: U32, +cap: U32, +msk: U32, +lox: U32, +hix: U32,
  +loz: U32, +cells: Nat) -> Array<U32> & Fa:
  (a, p) = r
  Fb.mk3(a, p, bx, bz, na, cap, msk, lox, hix, loz, cells)

# the block (bx, bz) into an array of its own: count what the cells of the
# block and the two around it hold, then copy it
def Fb.mk(a: Array<U32>, +bx: U32, +bz: U32, +na: U32, +cap: U32, +msk: U32) -> Array<U32> & Fa:
  +lox = (Fb.c0(bx) - 2 : U32)
  +hix = (Fb.c1(bx) + 2 : U32)
  +loz = (Fb.c0(bz) - 2 : U32)
  +side = Nat.add(Nat.pow(2n, Fb.lg()), 4n)
  +cells = Nat.mul(side, side)
  Fb.mk2(Fb.cnt(Nat.add(Nat.mul(16n, Nat.add(U32.to_nat(cap), cells)), 64n), cells, 0n,
    a[(F.hd(cap) + F.slot2(lox, loz, msk) : U32)], na, cap, msk, lox, hix, lox, loz, bx, bz, 0, 0, 0),
    bx, bz, na, cap, msk, lox, hix, loz, cells)

# the blocks of a colour (every other block on each axis), each with its
# own array, gathered in a tree: the tree is what the tick forks over. The
# step ahead takes the pair the block's build gives back, so the loop is a
# single function (Bend has no mutual recursion).
def Fb.tree(n: Nat, r: Array<U32> & Fa, t: Fa, +i: Nat, +nbx: Nat, +cx: U32, +cz: U32, +na: U32, +cap: U32,
  +msk: U32) -> Array<U32> & Fa:
  match n:
    case 0n:
      (a, leaf) = r
      (a, FaN{t, leaf})
    case 1n+m:
      (a, leaf) = r
      Fb.tree(m, Fb.mk(a, (cx + U32.from_nat(Nat.mul(2n, Nat.mod(i, nbx))) : U32),
        (cz + U32.from_nat(Nat.mul(2n, Nat.div(i, nbx))) : U32), na, cap, msk), FaN{t, leaf}, Nat.add(i, 1n),
        nbx, cx, cz, na, cap, msk)

# every block of the round at the same time, each on its own array
def Fb.run(t: Fa, +o: Og, +k: P.K, +mm: Nat) -> Fa:
  match t:
    case FaE{}:
      FaE{}
    case FaL{a, +nown, +nall, +cap}:
      FaL{F.ticks(U32.to_nat(nown), a, 0, Fb.og(o), Fb.kc(k), cap, (cap - 1 : U32), nown, mm), nown, nall, cap}
    case FaN{lo, hi}:
      x y = Fb.run(lo, o, k, mm) Fb.run(hi, o, k, mm)
      FaN{x, y}

def Fb.bf(r: Array<U32> & U32, a: Array<U32>) -> Array<U32> & Array<U32>:
  (d, v) = r
  (d, a)

# the round's results back into the crowd's array: the block's own cubes
# whole, the ones it only had around it just their velocity and flags (a
# push moves no one), each at the place 8 cap + slot kept for it
def Fb.bk(fuel: Nat, n: Nat, ph: Nat, r: Array<U32> & U32, a: Array<U32>, +i: U32, +nown: U32, +dcap: U32,
  +orig: U32) -> Array<U32> & Array<U32>:
  match fuel n ph:
    case 0n _ _:
      Fb.bf(r, a)
    case _ 0n _:
      Fb.bf(r, a)
    case 1n+f 1n+m 0n:
      (d, +v) = r
      +own = (i < nown : U32)
      Fb.bk(f, n, Pick.n(own, 1n, 4n), d[(i * 6 + Pick.u(own, 0, 3) : U32)], a, i, nown, dcap, v)
    case 1n+f 1n+m 1n:
      (d, v) = r
      Fb.bk(f, n, 2n, d[(i * 6 + 1 : U32)], a[(orig * 6 : U32)] <- v, i, nown, dcap, orig)
    case 1n+f 1n+m 2n:
      (d, v) = r
      Fb.bk(f, n, 3n, d[(i * 6 + 2 : U32)], a[(orig * 6 + 1 : U32)] <- v, i, nown, dcap, orig)
    case 1n+f 1n+m 3n:
      (d, v) = r
      Fb.bk(f, n, 4n, d[(i * 6 + 3 : U32)], a[(orig * 6 + 2 : U32)] <- v, i, nown, dcap, orig)
    case 1n+f 1n+m 4n:
      (d, v) = r
      Fb.bk(f, n, 5n, d[(i * 6 + 4 : U32)], a[(orig * 6 + 3 : U32)] <- v, i, nown, dcap, orig)
    case 1n+f 1n+m 5n:
      (d, v) = r
      Fb.bk(f, n, 6n, d[(i * 6 + 5 : U32)], a[(orig * 6 + 4 : U32)] <- v, i, nown, dcap, orig)
    case 1n+f 1n+m _:
      (d, v) = r
      Fb.bk(f, m, 0n, d[(F.hd(dcap) + dcap + i + 1 : U32)], a[(orig * 6 + 5 : U32)] <- v, (i + 1 : U32), nown,
        dcap, orig)

def Fb.drop(r: Array<U32> & Array<U32>) -> Array<U32>:
  (d, a) = r
  a

def Fb.back(t: Fa, a: Array<U32>) -> Array<U32>:
  match t:
    case FaE{}:
      a
    case FaL{d, +nown, +nall, +cap}:
      Fb.drop(Fb.bk(Nat.add(Nat.mul(8n, U32.to_nat(nall)), 16n), U32.to_nat(nall), 0n,
        d[(F.hd(cap) + cap : U32)], a, 0, nown, cap, 0))
    case FaN{lo, hi}:
      Fb.back(hi, Fb.back(lo, a))

def Fb.rd2(r: Array<U32> & Fa, +o: Og, +k: P.K, +mm: Nat) -> Array<U32>:
  (a, t) = r
  Fb.back(Fb.run(t, o, k, mm), a)

# one round: the blocks of a colour built one by one (cheap array copies),
# then ticked all at once, then written back
def Fb.round(a: Array<U32>, +c: Nat, +nbx: Nat, +nbz: Nat, +na: U32, +cap: U32, +msk: U32, +o: Og, +k: P.K,
  +mm: Nat) -> Array<U32>:
  +cx = Nat.mod(c, 2n)
  +cz = Nat.div(c, 2n)
  +ni = Nat.div(Nat.add(Nat.sub(nbx, Nat.min(cx, nbx)), 1n), 2n)
  +nj = Nat.div(Nat.add(Nat.sub(nbz, Nat.min(cz, nbz)), 1n), 2n)
  Fb.rd2(Fb.tree(Nat.mul(ni, nj), (a, FaE{}), FaE{}, 0n, ni, U32.from_nat(cx), U32.from_nat(cz), na, cap, msk),
    o, k, mm)

# the four rounds of a tick
def Fb.all(a: Array<U32>, +nbx: Nat, +nbz: Nat, +na: U32, +cap: U32, +msk: U32, +o: Og, +k: P.K,
  +mm: Nat) -> Array<U32>:
  Fb.round(Fb.round(Fb.round(Fb.round(a, 0n, nbx, nbz, na, cap, msk, o, k, mm),
    1n, nbx, nbz, na, cap, msk, o, k, mm), 2n, nbx, nbz, na, cap, msk, o, k, mm),
    3n, nbx, nbz, na, cap, msk, o, k, mm)

# The flat tick: the crowd, the sleepers around it and the player in one
# array; the player ticks first (with the input), then every cube, in
# order; then the pushed sleepers wake and the cubes at rest sleep.

def F.bx0(+b: Bx) -> Nat:
  Bx{x0, y0, z0, x1, y1, z1} = b
  x0

def F.bz0(+b: Bx) -> Nat:
  Bx{x0, y0, z0, x1, y1, z1} = b
  z0

def F.bx1(+b: Bx) -> Nat:
  Bx{x0, y0, z0, x1, y1, z1} = b
  x1

def F.bz1(+b: Bx) -> Nat:
  Bx{x0, y0, z0, x1, y1, z1} = b
  z1

# the cells whose sleeping cubes the crowd can touch: from its box less the
# tick's greatest reach up to its far side plus the cube's size and that
# same reach, the very range of W.lo and W.span
def F.cx0(+b: Bx, +mm: Nat) -> U32:
  W.lo(F.bx0(b), mm)

def F.cz0(+b: Bx, +mm: Nat) -> U32:
  W.lo(F.bz0(b), mm)

def F.gnx(+b: Bx, +mm: Nat) -> Nat:
  Nat.add(U32.to_nat((W.cell_of(Nat.sub(Nat.add(Nat.add(F.bx1(b), W.size()), mm), 1n)) - F.cx0(b, mm) : U32)), 1n)

def F.gnz(+b: Bx, +mm: Nat) -> Nat:
  Nat.add(U32.to_nat((W.cell_of(Nat.sub(Nat.add(Nat.add(F.bz1(b), W.size()), mm), 1n)) - F.cz0(b, mm) : U32)), 1n)

# the array's origin: the first of those cells on each axis, so every cube
# of the array is above it (places are kept as 32 bit numbers from it)
def F.org(+b: Bx, +mm: Nat) -> Og:
  Og{W.base(F.cx0(b, mm)), W.base(F.cz0(b, mm))}

# the greatest reach of the tick: the player's (it has a motor) and the
# cubes', so that no cube of the array moves further than it in a tick
def F.mx(+k: P.K, xs: List<&2, P.Body>, +m: Nat) -> Nat:
  match xs:
    case []:
      m
    case +b <> rest:
      F.mx(k, rest, Nat.max(m, W.creach(k, b)))

# one body's tick with a reach and an input of its own (the player's)
# the player's own tick: its reach (a jump, the motor) and its input
def F.oneR(r: Array<U32> & P.Body, +i: U32, +o: Og, +k: P.K, +cap: U32, +msk: U32, +na: U32, +mm: Nat,
  inp: P.In) -> Array<U32>:
  (a, +self) = r
  F.one2(a, i, o, k, cap, msk, na, self, W.reach(k, self), mm, inp)

# the sleepers a tick pushed (they are awake from now on)
def F.woken(xs: List<&2, P.Body>) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +b <> rest:
      W.take_if(W.moving(b), b, F.woken(rest))

def W.slept(+seed: U32, p: P.Body, s: Sl) -> World:
  Sl{t, dirty, keep} = s
  World{seed, t, keep, dirty, p}

def W.sleep1(ok: Bool, +c: P.Body, +cx: U32, +cz: U32, cubes: List<&2, P.Body>, s: Sl) -> Sl:
  match ok:
    case True{}:
      Sl{t, dirty, keep} = s
      Sl{Cells.set(t, cx, cz, W.cube(P.Body.x(c), P.Body.y(c), P.Body.z(c)) <> cubes), Cell{cx, cz} <> dirty, keep}
    case False{}:
      Sl{t, dirty, keep} = s
      Sl{t, dirty, c <> keep}

def W.fits7(xs: List<&2, P.Body>) -> Bool:
  Nat.is_lt(List.length(&2, P.Body, xs), 7n)

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

def W.sleep_one(+k: P.K, +seed: U32, +c: P.Body, s: Sl) -> Sl:
  Sl{+t, dirty, keep} = s
  W.sleep2(W.still(k, t, seed, c), seed, c, Sl{t, dirty, keep})

def W.sleep(xs: List<&2, P.Body>, +k: P.K, +seed: U32, s: Sl) -> Sl:
  match xs:
    case []:
      s
    case +c <> rest:
      W.sleep(rest, k, seed, W.sleep_one(k, seed, c, s))

def F.f5(+k: P.K, +seed: U32, p: P.Body, awake: List<&2, P.Body>, st: St) -> World:
  St{t, dirty, fresh, work} = st
  W.slept(seed, p, W.sleep(List.append(&2, P.Body, fresh, awake), k, seed, Sl{t, dirty, []}))

def F.f3(+k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, p: P.Body, awake: List<&2, P.Body>,
  +wk: List<&2, P.Body>) -> World:
  F.f5(k, seed, p, awake, W.wake(Nat.add(1024n, Nat.mul(16n, List.length(&2, P.Body, wk))), seed, St{t, dirty, [], wk}))

def F.u3(r: Array<U32> & P.Body, +k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, awake: List<&2, P.Body>,
  +wk: List<&2, P.Body>) -> World:
  (a, p) = r
  F.f3(k, seed, t, dirty, p, awake, wk)

def F.u2(r: Array<U32> & List<&2, P.Body>, +k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, +o: Og, +na: U32,
  +m: U32, awake: List<&2, P.Body>) -> World:
  (a, sl) = r
  F.u3(F.get(a, (na + m : U32), o), k, seed, t, dirty, awake, F.woken(sl))

def F.u1(r: Array<U32> & List<&2, P.Body>, +k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, +o: Og, +na: U32,
  +m: U32) -> World:
  (a, awake) = r
  F.u2(F.unpack(m, a, na, o), k, seed, t, dirty, o, na, m, awake)

def F.f2(+k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, +o: Og, +na: U32, +m: U32, a: Array<U32>) -> World:
  F.u1(F.unpack(na, a, 0, o), k, seed, t, dirty, o, na, m)

# the crowd, the sleepers of its cells and the player into the array; the
# player ticks first, then every cube, in order
def W.fl2(+k: P.K, inp: P.In, +seed: U32, t: Cells, dirty: List<&2, Cell>, +p: P.Body, awake: List<&2, P.Body>,
  sl: List<&2, P.Body>, +na: U32, +m: U32, +o: Og, +mm: Nat, r: U32 & Nat) -> World:
  (+cap, b) = r
  F.f2(k, seed, t, dirty, o, na, m,
    F.ticks(U32.to_nat(na),
      F.oneR(F.get(F.build((na + m + 1 : U32), F.put(F.pack(sl, F.pack(awake, Array.new(U32, Nat.add(b, 3n), 0), 0, o, False{}),
        na, o, True{}), (na + m : U32), o, True{}, p), cap, (cap - 1 : U32)), (na + m : U32), o),
        (na + m : U32), o, k, cap, (cap - 1 : U32), na, mm, inp),
      0, o, k, cap, (cap - 1 : U32), na, mm))

# the same tick, but the cubes run block by block, every block of a colour
# at the same time (four rounds)
def W.flp2(+k: P.K, inp: P.In, +seed: U32, t: Cells, dirty: List<&2, Cell>, +p: P.Body, awake: List<&2, P.Body>,
  sl: List<&2, P.Body>, +na: U32, +m: U32, +o: Og, +mm: Nat, +nbx: Nat, +nbz: Nat, r: U32 & Nat) -> World:
  (+cap, b) = r
  F.f2(k, seed, t, dirty, o, na, m,
    Fb.all(
      F.oneR(F.get(F.build2((na + m + 1 : U32), F.put(F.pack(sl, F.pack(awake, Array.new(U32, Nat.add(b, 4n), 0), 0, o,
        False{}), na, o, True{}), (na + m : U32), o, True{}, p), cap, (cap - 1 : U32)), (na + m : U32), o),
        (na + m : U32), o, k, cap, (cap - 1 : U32), na, mm, inp),
      nbx, nbz, na, cap, (cap - 1 : U32), o, k, mm))

def W.flp1(+k: P.K, inp: P.In, +seed: U32, +t: Cells, dirty: List<&2, Cell>, +p: P.Body, +awake: List<&2, P.Body>,
  +na: U32, +bx: Bx, +mm: Nat) -> World:
  +sl = W.rect(Nat.mul(F.gnx(bx, mm), F.gnz(bx, mm)), t, seed, F.cx0(bx, mm), F.cz0(bx, mm), F.gnx(bx, mm))
  W.flp2(k, inp, seed, t, dirty, p, awake, sl, na, U32.from_nat(List.length(&2, P.Body, sl)), F.org(bx, mm), mm,
    Nat.add(Nat.div(Nat.sub(F.gnx(bx, mm), 1n), Nat.pow(2n, Fb.lg())), 1n),
    Nat.add(Nat.div(Nat.sub(F.gnz(bx, mm), 1n), Nat.pow(2n, Fb.lg())), 1n),
    F.cap0((na + U32.from_nat(List.length(&2, P.Body, sl)) + 1 : U32)))

def W.fl1(+k: P.K, inp: P.In, +seed: U32, +t: Cells, dirty: List<&2, Cell>, +p: P.Body, +awake: List<&2, P.Body>,
  +na: U32, +bx: Bx, +mm: Nat) -> World:
  +sl = W.rect(Nat.mul(F.gnx(bx, mm), F.gnz(bx, mm)), t, seed, F.cx0(bx, mm), F.cz0(bx, mm), F.gnx(bx, mm))
  W.fl2(k, inp, seed, t, dirty, p, awake, sl, na, U32.from_nat(List.length(&2, P.Body, sl)), F.org(bx, mm), mm,
    F.cap0((na + U32.from_nat(List.length(&2, P.Body, sl)) + 1 : U32)))

def O.bb(xs: List<&2, P.Body>, b: Bx) -> Bx:
  match xs:
    case []:
      b
    case +e <> rest:
      Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
      O.bb(rest, Bx{Nat.min(x0, P.Body.x(e)), Nat.min(y0, P.Body.y(e)), Nat.min(z0, P.Body.z(e)),
        Nat.max(x1, P.Body.x(e)), Nat.max(y1, P.Body.y(e)), Nat.max(z1, P.Body.z(e))})

def O.big() -> Nat:
  Nat.add(Nat.mul(W.size(), U32.to_nat(1073741823)), 262143n)

def O.box(xs: List<&2, P.Body>) -> Bx:
  O.bb(xs, Bx{O.big(), O.big(), O.big(), 0n, 0n, 0n})

def W.sleep_all(+k: P.K, w: World) -> World:
  World{+seed, t, awake, dirty, p} = w
  W.slept(seed, p, W.sleep(awake, k, seed, Sl{t, dirty, []}))


# the crowd's tick with the blocks of a colour running at the same time
def W.tick_fpar(+k: P.K, inp: P.In, w: World) -> World:
  World{+seed, +t, +awake, dirty, +p} = w
  W.flp1(k, inp, seed, t, dirty, p, awake, U32.from_nat(List.length(&2, P.Body, awake)), O.bb(awake, O.box([p])),
    F.mx(k, awake, W.reach(k, p)))

def W.tick_flat(+k: P.K, inp: P.In, w: World) -> World:
  World{+seed, +t, +awake, dirty, +p} = w
  W.fl1(k, inp, seed, t, dirty, p, awake, U32.from_nat(List.length(&2, P.Body, awake)), O.bb(awake, O.box([p])),
    F.mx(k, awake, W.reach(k, p)))

# The world's tick
# ----------------
# The player first (with the input), then every awake cube (no input),
# each among the sleepers around it and every other awake body; what they
# pushed wakes. Then the awake cubes that came to rest on the ground or on
# sleeping cubes go to sleep in their cells.

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
      +m = W.creach(k, c)
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
    case 1n++j:
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

# half a cube: the margin between the sides
def O.half() -> Nat:
  131072n

# a node cuts while it holds more cubes than this and is at least 8 m long
def O.leaf_max() -> Nat:
  24n

def O.min_size() -> Nat:
  2097152n

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
      +m = W.creach(k, c)
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
      W.near_of(xs, W.creach(k, c), c)

def Q.around3(+src: Src, +seed: U32, +m: Nat, +x: Nat, +y: Nat, +z: Nat) -> List<&2, P.Body>:
  match src:
    case SCells{t}:
      W.around3(t, seed, m, x, y, z)
    case SList{xs}:
      W.nof(Nat.add(W.size(), m), x, y, z, xs)

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
      +m = W.creach(k, c)
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

def Q.bseq(+k: P.K, +seed: U32, +src: Src, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq3:
  Q.end(pool, Q.steps(todo, k, seed, src, Sq{Bk.adds(todo, Bk.adds(pool, BE{})), ev}))

# The same for a few: each cube among the others, split by distance (n^2,
# but no map to build: cheaper under about a hundred, measured)

type Lz is Data:
  Lz{done: List<&2, P.Body>, todo: List<&2, P.Body>, pool: List<&2, P.Body>, ev: List<&2, P.Body>}

def Q.le(c: P.Body, pn: List<&2, P.Body>, dn: List<&2, P.Body>, sp: Two, far: Far, +ev: List<&2, P.Body>) -> Lz:
  Two{rn, sl} = sp
  Far{pf, df, rf} = far
  Lz{c <> List.append(&2, P.Body, dn, df), List.append(&2, P.Body, rn, rf), List.append(&2, P.Body, pn, pf), Q.upsert(sl, ev)}

def Q.ld(+nr: Nat, c: P.Body, pn: List<&2, P.Body>, sp: Two, far: Far, +ev: List<&2, P.Body>) -> Lz:
  Two{dn, rest} = sp
  Q.le(c, pn, dn, W.split(nr, rest), far, ev)

def Q.lc(+nd: Nat, +nr: Nat, c: P.Body, sp: Two, far: Far, +ev: List<&2, P.Body>) -> Lz:
  Two{pn, rest} = sp
  Q.ld(nr, c, pn, W.split(nd, rest), far, ev)

def Q.lb(+np: Nat, +nd: Nat, +nr: Nat, r: P.Body & List<&2, P.Body>, far: Far, +ev: List<&2, P.Body>) -> Lz:
  (c, obs) = r
  Q.lc(nd, nr, c, W.split(np, obs), far, ev)

def Q.la(+k: P.K, +src: Src, +seed: U32, +c: P.Body, pp: Two, dd: Two, rr: Two, +ev: List<&2, P.Body>) -> Lz:
  Two{+pn, pf} = pp
  Two{+dn, df} = dd
  Two{+rn, rf} = rr
  Q.lb(List.length(&2, P.Body, pn), List.length(&2, P.Body, dn), List.length(&2, P.Body, rn),
    P.Body.tick(k, List.append(&2, P.Body, pn, List.append(&2, P.Body, dn, List.append(&2, P.Body, rn,
      Q.shadow(Q.around(k, src, seed, c), ev)))), P.In.idle(), c), Far{pf, df, rf}, ev)

def Q.lgo(+k: P.K, +seed: U32, +src: Src, done: List<&2, P.Body>, todo: List<&2, P.Body>, pool: List<&2, P.Body>,
  ev: List<&2, P.Body>) -> Lz:
  match todo:
    case []:
      Lz{done, [], pool, ev}
    case +c <> rest:
      +m = W.creach(k, c)
      Q.la(k, src, seed, c, W.part_near(m, c, pool), W.part_near(m, c, done), W.part_near(m, c, rest), ev)

def Q.lsteps(n: Nat, +k: P.K, +seed: U32, +src: Src, z: Lz) -> Lz:
  match n:
    case 0n:
      z
    case 1n+m:
      Lz{done, todo, pool, ev} = z
      Q.lsteps(m, k, seed, src, Q.lgo(k, seed, src, done, todo, pool, ev))

# the pool back in its first order (as the steps left it)
def Q.lend(+pool0: List<&2, P.Body>, z: Lz) -> Sq3:
  Lz{done, todo, +pool, ev} = z
  Sq3{List.append(&2, P.Body, todo, done), O.apply(pool0, pool), ev}

def Q.lseq(+k: P.K, +seed: U32, +src: Src, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq3:
  Q.lend(pool, Q.lsteps(List.length(&2, P.Body, todo), k, seed, src, Lz{[], todo, pool, ev}))

def Q.seq2(few: Bool, +k: P.K, +seed: U32, +src: Src, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq3:
  match few:
    case True{}:
      Q.lseq(k, seed, src, todo, pool, ev)
    case False{}:
      Q.bseq(k, seed, src, todo, pool, ev)

# The same, telling what changed of the pool instead of giving it back in
# order: each step compares the pool cubes it met before and after its
# tick (pushes are rare; restoring the order was n^2)

type Sq4 is Data:
  Sq4{todo: List<&2, P.Body>, chg: List<&2, P.Body>, ev: List<&2, P.Body>}

type Lc is Data:
  Lc{done: List<&2, P.Body>, todo: List<&2, P.Body>, pool: List<&2, P.Body>, ev: List<&2, P.Body>, chg: List<&2, P.Body>}

def Q.upch(same: Bool, +n: P.Body, +chg: List<&2, P.Body>) -> List<&2, P.Body>:
  match same:
    case True{}:
      chg
    case False{}:
      Q.up2(O.has(n, chg), True{}, n, chg)

def Q.chg2(os: List<&2, P.Body>, ns: List<&2, P.Body>, +chg: List<&2, P.Body>) -> List<&2, P.Body>:
  match os ns:
    case +o <> or +n <> nr:
      Q.chg2(or, nr, Q.upch(W.eqb(o, n), n, chg))
    case _ _:
      chg

def Q.ce(c: P.Body, +pn0: List<&2, P.Body>, +pn: List<&2, P.Body>, dn: List<&2, P.Body>, sp: Two, far: Far, +ev: List<&2, P.Body>,
  +chg: List<&2, P.Body>) -> Lc:
  Two{rn, sl} = sp
  Far{pf, df, rf} = far
  Lc{c <> List.append(&2, P.Body, dn, df), List.append(&2, P.Body, rn, rf), List.append(&2, P.Body, pn, pf), Q.upsert(sl, ev),
    Q.chg2(pn0, pn, chg)}

def Q.cd(+nr: Nat, c: P.Body, +pn0: List<&2, P.Body>, +pn: List<&2, P.Body>, sp: Two, far: Far, +ev: List<&2, P.Body>,
  +chg: List<&2, P.Body>) -> Lc:
  Two{dn, rest} = sp
  Q.ce(c, pn0, pn, dn, W.split(nr, rest), far, ev, chg)

def Q.cc(+nd: Nat, +nr: Nat, c: P.Body, +pn0: List<&2, P.Body>, sp: Two, far: Far, +ev: List<&2, P.Body>, +chg: List<&2, P.Body>) -> Lc:
  Two{+pn, rest} = sp
  Q.cd(nr, c, pn0, pn, W.split(nd, rest), far, ev, chg)

def Q.cb(+np: Nat, +nd: Nat, +nr: Nat, +pn0: List<&2, P.Body>, r: P.Body & List<&2, P.Body>, far: Far, +ev: List<&2, P.Body>,
  +chg: List<&2, P.Body>) -> Lc:
  (c, obs) = r
  Q.cc(nd, nr, c, pn0, W.split(np, obs), far, ev, chg)

def Q.ca(+k: P.K, +src: Src, +seed: U32, +m: Nat, +x: Nat, +y: Nat, +z: Nat, c: P.Body, pp: Pc, dd: Pc, rr: Pc,
  +ev: List<&2, P.Body>, +chg: List<&2, P.Body>) -> Lc:
  Pc{+pn, np, pf} = pp
  Pc{dn, nd, df} = dd
  Pc{rn, nr, rf} = rr
  Q.cb(np, nd, nr, pn,
    P.Body.tick(k, List.append(&2, P.Body, pn, List.append(&2, P.Body, dn, List.append(&2, P.Body, rn,
      Q.shadow(Q.around3(src, seed, m, x, y, z), ev)))), P.In.idle(), c), Far{pf, df, rf}, ev, chg)

def Q.cgo(+k: P.K, +seed: U32, +src: Src, done: List<&2, P.Body>, todo: List<&2, P.Body>, pool: List<&2, P.Body>,
  ev: List<&2, P.Body>, chg: List<&2, P.Body>) -> Lc:
  match todo:
    case []:
      Lc{done, [], pool, ev, chg}
    case P.Body{+x, +y, +z, +vx, +vy, +vz, g, h} <> rest:
      +m = W.creachz(k, vx, vy, vz)
      +r = Nat.add(W.size(), m)
      Q.ca(k, src, seed, m, x, y, z, P.Body{x, y, z, vx, vy, vz, g, h}, W.pnc(r, x, y, z, pool), W.pnc(r, x, y, z, done),
        W.pnc(r, x, y, z, rest), ev, chg)

def Q.csteps(n: Nat, +k: P.K, +seed: U32, +src: Src, z: Lc) -> Lc:
  match n:
    case 0n:
      z
    case 1n+m:
      Lc{done, todo, pool, ev, chg} = z
      Q.csteps(m, k, seed, src, Q.cgo(k, seed, src, done, todo, pool, ev, chg))

def Q.cend(z: Lc) -> Sq4:
  Lc{done, todo, pool, ev, chg} = z
  Sq4{List.append(&2, P.Body, todo, done), chg, ev}

def Q.cb3(+pool: List<&2, P.Body>, q: Sq3) -> Sq4:
  Sq3{todo, pool2, ev} = q
  Sq4{todo, O.changed(pool, pool2), ev}

def Q.cseq2(few: Bool, +k: P.K, +seed: U32, +src: Src, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq4:
  match few:
    case True{}:
      Q.cend(Q.csteps(List.length(&2, P.Body, todo), k, seed, src, Lc{[], todo, pool, ev, []}))
    case False{}:
      Q.cb3(pool, Q.bseq(k, seed, src, todo, pool, ev))

# todo tick in order among themselves, pool and the sleepers; what changed
# of the pool
def Q.cseq(+k: P.K, +seed: U32, +cells: Cells, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq4:
  Q.cseq2(Nat.is_lt(Nat.add(List.length(&2, P.Body, todo), List.length(&2, P.Body, pool)), 96n), k, seed,
    Q.source(k, cells, seed, todo), todo, pool, ev)

# todo tick in order among themselves, pool (pushed, not ticked) and the
# sleepers (read once for them all when they are close together)
def Q.seq(+k: P.K, +seed: U32, +cells: Cells, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq3:
  Q.seq2(Nat.is_lt(Nat.add(List.length(&2, P.Body, todo), List.length(&2, P.Body, pool)), 96n), k, seed,
    Q.source(k, cells, seed, todo), todo, pool, ev)

# A block's tick on a flat array
# ------------------------------
# The same contract as Q.cseq -- the block's cubes tick in order, among
# themselves, the pool (the cubes of the blocks around and the player:
# pushed, never ticked) and the sleepers of the cells they reach -- but
# through one array. Two blocks of a colour never touch the same body, so
# every block of a phase runs this at the same time, each on its own array.

def F.b5(r: Array<U32> & List<&2, P.Body>, todo: List<&2, P.Body>, chg: List<&2, P.Body>,
  ev: List<&2, P.Body>) -> Sq4:
  (a, sl) = r
  Sq4{todo, chg, Q.upsert(F.woken(sl), ev)}

def F.b4(r: Array<U32> & List<&2, P.Body>, +o: Og, +nt: U32, +np: U32, +ns: U32, +pool: List<&2, P.Body>,
  todo: List<&2, P.Body>, ev: List<&2, P.Body>) -> Sq4:
  (a, pl) = r
  F.b5(F.unpack(ns, a, (nt + np : U32), o), todo, Q.chg2(pool, List.reverse(&2, P.Body, pl), []), ev)

def F.b3(r: Array<U32> & List<&2, P.Body>, +o: Og, +nt: U32, +np: U32, +ns: U32, +pool: List<&2, P.Body>,
  ev: List<&2, P.Body>) -> Sq4:
  (a, todo) = r
  F.b4(F.unpack(np, a, nt, o), o, nt, np, ns, pool, todo, ev)

def F.b2(+k: P.K, todo: List<&2, P.Body>, +pool: List<&2, P.Body>, ev: List<&2, P.Body>, +nt: U32, +np: U32,
  +o: Og, sl: List<&2, P.Body>, +ns: U32, +mm: Nat, r: U32 & Nat) -> Sq4:
  (+cap, b) = r
  F.b3(F.unpack(nt,
    F.ticks(U32.to_nat(nt),
      F.build((nt + np + ns : U32),
        F.pack(sl, F.pack(pool, F.pack(todo, Array.new(U32, Nat.add(b, 3n), 0), 0, o, False{}), nt, o, False{}),
          (nt + np : U32), o, True{}), cap, (cap - 1 : U32)),
      0, o, k, cap, (cap - 1 : U32), (nt + np : U32), mm), 0, o), o, nt, np, ns, pool, ev)

def F.b1(+k: P.K, +seed: U32, +cells: Cells, todo: List<&2, P.Body>, +pool: List<&2, P.Body>, +ev: List<&2, P.Body>,
  +nt: U32, +np: U32, +bx: Bx, +mm: Nat) -> Sq4:
  +sl = Q.shadow(W.rect(Nat.mul(F.gnx(bx, mm), F.gnz(bx, mm)), cells, seed, F.cx0(bx, mm), F.cz0(bx, mm),
    F.gnx(bx, mm)), ev)
  +ns = U32.from_nat(List.length(&2, P.Body, sl))
  F.b2(k, todo, pool, ev, nt, np, F.org(bx, mm), sl, ns, mm, F.cap0((nt + np + ns + 1 : U32)))

def F.blk0(none: Bool, +k: P.K, +seed: U32, +cells: Cells, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>,
  +ev: List<&2, P.Body>, +nt: U32, +np: U32) -> Sq4:
  match none:
    case True{}:
      Sq4{todo, [], ev}
    case False{}:
      F.b1(k, seed, cells, todo, pool, ev, nt, np, O.bb(todo, O.box(pool)), F.mx(k, todo, 0n))

def F.blk(+k: P.K, +seed: U32, +cells: Cells, +todo: List<&2, P.Body>, +pool: List<&2, P.Body>,
  +ev: List<&2, P.Body>) -> Sq4:
  +nt = U32.from_nat(List.length(&2, P.Body, todo))
  F.blk0(U32.is_eq(nt, 0), k, seed, cells, todo, pool, ev, nt, U32.from_nat(List.length(&2, P.Body, pool)))

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
      O.reach(rest, k, Nat.max(m, W.creach(k, e)))

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

# The crowd's tick, both sides of a cut at once
# ---------------------------------------------
# The crowd's box is cut in half across its longest side. A cube farther
# from the plane than a cube and the tick's reach only touches cubes of its
# own side, so the two sides tick at the same time, each on its own flat
# array, and neither can push what the other pushes. The cubes across the
# plane tick after both, among what the sides left near it.

# a side stops cutting under this many cubes: a task smaller than this
# costs more to hand out than to run
def F.least() -> Nat:
  32n

def F.p7(far: List<&2, P.Body>, +near: List<&2, P.Body>, chs: List<&2, P.Body>, q: Sq4) -> Sq4:
  Sq4{st, +c2, ev} = q
  Sq4{List.append(&2, P.Body, far, List.append(&2, P.Body, O.apply(near, c2), st)),
    List.append(&2, P.Body, c2, chs), ev}

def F.p6(+k: P.K, +seed: U32, +cells: Cells, sp: Two, chs: List<&2, P.Body>, bd: Two, ev: List<&2, P.Body>) -> Sq4:
  Two{pool, st} = sp
  Two{+near, far} = bd
  F.p7(far, near, chs, F.blk(k, seed, cells, st, List.append(&2, P.Body, near, pool), ev))

def F.p5(+k: P.K, +seed: U32, +cells: Cells, +pool: List<&2, P.Body>, st: List<&2, P.Body>, ev: List<&2, P.Body>,
  +ax: Nat, +c: Nat, +r: Nat, rl: Sq4, rh: Sq4) -> Sq4:
  Sq4{dl, cl, el} = rl
  Sq4{dh, ch, eh} = rh
  +chs = List.append(&2, P.Body, cl, ch)
  F.p6(k, seed, cells,
    W.split(List.length(&2, P.Body, pool), O.apply(List.append(&2, P.Body, pool, st), chs)), chs,
    O.band(List.append(&2, P.Body, dl, dh), ax, c, Nat.add(Nat.mul(2n, W.size()), Nat.mul(2n, r))),
    Q.upsert(List.append(&2, P.Body, el, eh), ev))

# the box cut at c across the axis ax: the side below, and the side above
def O.blo(+b: Bx, +ax: Nat, +c: Nat) -> Bx:
  Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
  match ax:
    case 0n:
      Bx{x0, y0, z0, c, y1, z1}
    case 1n:
      Bx{x0, y0, z0, x1, c, z1}
    case _:
      Bx{x0, y0, z0, x1, y1, c}

def O.bhi(+b: Bx, +ax: Nat, +c: Nat) -> Bx:
  Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
  match ax:
    case 0n:
      Bx{c, y0, z0, x1, y1, z1}
    case 1n:
      Bx{x0, c, z0, x1, y1, z1}
    case _:
      Bx{x0, y0, c, x1, y1, z1}

# how many cuts a crowd of n cubes is worth: one while a side still holds
# more than F.least() of them, five at the most
def F.dep(fuel: Nat, +n: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      Pick.n(Nat.is_lt(n, F.least()), 0n, Nat.add(1n, F.dep(f, Nat.div(n, 2n))))

def T.win(xs: List<&2, P.Body>, +x0: Nat, +z0: Nat, +x1: Nat, +z1: Nat, +d: Nat) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case P.Body{+ex, ey, +ez, vx, vy, vz, g, h} <> rest:
      W.take_if(Bool.and(Bool.and(Nat.is_lt(x0, Nat.add(ex, d)), Nat.is_lt(ex, Nat.add(x1, d))),
          Bool.and(Nat.is_lt(z0, Nat.add(ez, d)), Nat.is_lt(ez, Nat.add(z1, d)))),
        P.Body{ex, ey, ez, vx, vy, vz, g, h}, T.win(rest, x0, z0, x1, z1, d))

def T.within(xs: List<&2, P.Body>, +b: Bx, +r: Nat) -> List<&2, P.Body>:
  Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
  T.win(xs, x0, z0, x1, z1, Nat.add(W.size(), r))

# the cubes of the two sides tick at once, each on its own array; then the
# ones across the plane, among what the sides left near it
def F.par(d: Nat, +k: P.K, +seed: U32, +cells: Cells, p3: P3, +pool: List<&2, P.Body>, ev: List<&2, P.Body>,
  +b: Bx, +ax: Nat, +c: Nat, +r: Nat) -> Sq4:
  match d:
    case 0n:
      F.blk(k, seed, cells, O.all(p3), pool, ev)
    case 1n++j:
      P3{+st, lo, hi} = p3
      +blo = O.blo(b, ax, c)
      +bhi = O.bhi(b, ax, c)
      +alo = O.axis(blo)
      +ahi = O.axis(bhi)
      +clo = O.mid(blo, alo)
      +chi = O.mid(bhi, ahi)
      rl rh = F.par(j, k, seed, cells, O.part(lo, alo, clo, r),
                T.within(List.append(&2, P.Body, O.near(pool, 0n, ax, c), st), blo, r), [], blo, alo, clo, r)
              F.par(j, k, seed, cells, O.part(hi, ahi, chi, r),
                T.within(List.append(&2, P.Body, O.near(pool, 1n, ax, c), st), bhi, r), [], bhi, ahi, chi, r)
      F.p5(k, seed, cells, pool, st, ev, ax, c, r, rl, rh)

# the player as the cubes pushed it, the sleepers they pushed woken (and
# what stood on those)
def F.w2(+seed: U32, t: Cells, dirty: List<&2, Cell>, +p: P.Body, q: Sq4) -> World:
  Sq4{done, chg, +ev} = q
  O.w3(seed, O.find(p, chg), done,
    W.wake(Nat.add(1024n, Nat.mul(16n, List.length(&2, P.Body, ev))), seed, St{t, dirty, [], ev}))

def F.w1(+k: P.K, +seed: U32, +t: Cells, dirty: List<&2, Cell>, +p: P.Body, +awake: List<&2, P.Body>, +b: Bx,
  +mm: Nat, +d: Nat) -> World:
  +ax = O.axis(b)
  +c = O.mid(b, ax)
  +r = Nat.add(W.size(), mm)
  F.w2(seed, t, dirty, p, F.par(d, k, seed, t, O.part(awake, ax, c, r), [p], [], b, ax, c, r))

def W.cubes_par(+k: P.K, w: World) -> World:
  World{+seed, +t, +awake, dirty, +p} = w
  F.w1(k, seed, t, dirty, p, awake, O.box(awake), O.reach(awake, k, 0n),
    F.dep(8n, List.length(&2, P.Body, awake)))
# Many awake cubes: colored blocks
# --------------------------------
# The floor in blocks of 4 x 4 m, each of 4 colors (the parity of its x and
# z: a checkerboard of 2 x 2). Two blocks of a color have a whole block
# between them, 4 m: more than a cube and twice what anything reaches in a
# tick (2 S + 2 R, R under 1 m), so no two of their cubes touch the same
# body. A tick runs 4 phases; in each, every block of that color ticks its
# cubes (in order, among the cubes of the 8 blocks around, which rest this
# phase, and the sleepers) -- all those blocks at once, Bend forking down a
# tree of the blocks. Every cube ticks once, in its block's phase, and
# keeps its block for the whole tick (it moves centimetres in one).
#
# The tree: 64 x 64 buckets (a block's low 6 bits on each axis; far blocks
# sharing one are told apart by distance, and keep its color), cut in two
# by one bit at a time, the highest first, x and z in turn: 12 levels,
# every subtree a rectangle. It is built from the awake list every tick,
# in parallel as well.

type Bt is Data:
  TE{}
  TL{xs: List<&2, P.Body>}
  TN{lo: Bt, hi: Bt}

type Ch is Data:
  Ch{bx: U32, bz: U32, b: P.Body}

type Nb is Data:
  Nb{bx: U32, bz: U32, xs: List<&2, P.Body>}

type PR is Data:
  PR{t: Bt, ch: List<&2, Ch>, ev: List<&2, P.Body>, pl: List<&2, P.Body>}

type Tk is Data:
  Tk{t: Bt, ev: List<&2, P.Body>, pl: P.Body}

# a block is 4 m << T.lg() a side: wide enough that two blocks of a colour
# (a block apart) never reach the same cube, and wide enough that its own
# cubes outnumber the ones it has to copy from around it
def T.lg() -> Nat:
  0n

def T.key(+x: Nat) -> U32:
  ((W.blk(x) >> T.lg()) .&. 63 : U32)

# the half a bucket (bx, bz) is in at level l: bit l/2 of x (from 1) at an
# even level, bit (l + 1)/2 of z at an odd one
def T.side2(xl: Bool, +l: Nat, +bx: U32, +bz: U32) -> Bool:
  match xl:
    case True{}:
      W.bit(bx, Nat.div(l, 2n))
    case False{}:
      W.bit(bz, Nat.div(Nat.add(l, 1n), 2n))

def T.side(+l: Nat, +bx: U32, +bz: U32) -> Bool:
  T.side2(Nat.is_eq(Nat.mod(l, 2n), 0n), l, bx, bz)

def T.put(l: Nat, t: Bt, s: Bool, +bx: U32, +bz: U32, +b: P.Body) -> Bt:
  match l t s:
    case 0n TL{xs} _:
      TL{b <> xs}
    case 0n _ _:
      TL{[b]}
    case 1n++j TN{lo, hi} False{}:
      TN{T.put(j, lo, T.side(j, bx, bz), bx, bz, b), hi}
    case 1n++j TN{lo, hi} True{}:
      TN{lo, T.put(j, hi, T.side(j, bx, bz), bx, bz, b)}
    case 1n++j _ False{}:
      TN{T.put(j, TE{}, T.side(j, bx, bz), bx, bz, b), TE{}}
    case 1n++j _ True{}:
      TN{TE{}, T.put(j, TE{}, T.side(j, bx, bz), bx, bz, b)}

def T.add(t: Bt, +b: P.Body) -> Bt:
  +bx = T.key(P.Body.x(b))
  +bz = T.key(P.Body.z(b))
  T.put(12n, t, T.side(12n, bx, bz), bx, bz, b)

def T.adds(xs: List<&2, P.Body>, t: Bt) -> Bt:
  match xs:
    case []:
      t
    case +b <> rest:
      T.adds(rest, T.add(t, b))

def T.half_a(p: Two) -> List<&2, P.Body>:
  Two{a, b} = p
  a

def T.half_b(p: Two) -> List<&2, P.Body>:
  Two{a, b} = p
  b

# the cubes of xs by their half at level l
def T.side_of(+l: Nat, +b: P.Body) -> Bool:
  T.side(l, T.key(P.Body.x(b)), T.key(P.Body.z(b)))

def T.part(xs: List<&2, P.Body>, +l: Nat) -> Two:
  match xs:
    case []:
      Two{[], []}
    case P.Body{+x, y, +z, vx, vy, vz, g, h} <> rest:
      W.near1(Bool.not(T.side(l, T.key(x), T.key(z))), P.Body{x, y, z, vx, vy, vz, g, h}, T.part(rest, l))

# the bucket coordinates of the upper half at level l: x's bit l/2 - 1 set
# at an even level, z's bit (l + 1)/2 - 1 at an odd one
# Above this level of the tree a step forks; below it, it runs straight
# through. One fork per node made tasks so small that making them cost
# more than they saved (measured).
def T.fork() -> Nat:
  5n

# the tree at level l of the cubes p, already split by the level's bit:
# each half split by the next bit and built, both in parallel (a radix
# partition: no inserts, no merges; the split is handed down, not shared)
def T.rad(l: Nat, par: Bool, p: Two) -> Bt:
  match l par p:
    case _ _ Two{Nil{}, Nil{}}:
      TE{}
    case 0n _ Two{lo, hi}:
      TL{List.append(&2, P.Body, lo, hi)}
    case 1n++j True{} Two{lo, hi}:
      a b = T.rad(j, Nat.is_le(T.fork(), j), T.part(lo, j)) T.rad(j, Nat.is_le(T.fork(), j), T.part(hi, j))
      TN{a, b}
    case 1n++j False{} Two{lo, hi}:
      TN{T.rad(j, False{}, T.part(lo, j)), T.rad(j, False{}, T.part(hi, j))}

def T.radix(+l: Nat, xs: List<&2, P.Body>) -> Bt:
  T.rad(l, True{}, T.part(xs, l))

def T.get(l: Nat, t: Bt, s: Bool, +bx: U32, +bz: U32) -> List<&2, P.Body>:
  match l t s:
    case _ TE{} _:
      []
    case _ TL{xs} _:
      xs
    case 0n TN{lo, hi} _:
      []
    case 1n++j TN{lo, hi} False{}:
      T.get(j, lo, T.side(j, bx, bz), bx, bz)
    case 1n++j TN{lo, hi} True{}:
      T.get(j, hi, T.side(j, bx, bz), bx, bz)

def T.at(+t: Bt, +bx: U32, +bz: U32) -> List<&2, P.Body>:
  T.get(12n, t, T.side(12n, bx, bz), bx, bz)

def T.all(t: Bt) -> List<&2, P.Body>:
  match t:
    case TE{}:
      []
    case TL{xs}:
      xs
    case TN{lo, hi}:
      List.append(&2, P.Body, T.all(lo), T.all(hi))

# is e within reach of the box b (its cubes' corners), r their reach?
def T.inb(+e: P.Body, +b: Bx, +r: Nat) -> Bool:
  Bx{+x0, +y0, +z0, +x1, +y1, +z1} = b
  +d = Nat.add(W.size(), r)
  Bool.and(Bool.and(Nat.is_lt(x0, Nat.add(P.Body.x(e), d)), Nat.is_lt(P.Body.x(e), Nat.add(x1, d))),
    Bool.and(Nat.is_lt(z0, Nat.add(P.Body.z(e), d)), Nat.is_lt(P.Body.z(e), Nat.add(z1, d))))

def T.nb(+t: Bt, +bx: U32, +bz: U32, +dx: U32, +dz: U32, +b: Bx, +r: Nat) -> Nb:
  +x = ((bx + dx) .&. 63 : U32)
  +z = ((bz + dz) .&. 63 : U32)
  Nb{x, z, T.within(T.at(t, x, z), b, r)}

# the cubes of the 8 buckets around (bx, bz) that the box b of its cubes
# can reach (r their reach), bucket by bucket
def T.nbs(+t: Bt, +bx: U32, +bz: U32, +b: Bx, +r: Nat) -> List<&2, Nb>:
  [T.nb(t, bx, bz, 63, 63, b, r), T.nb(t, bx, bz, 0, 63, b, r), T.nb(t, bx, bz, 1, 63, b, r), T.nb(t, bx, bz, 63, 0, b, r),
   T.nb(t, bx, bz, 1, 0, b, r), T.nb(t, bx, bz, 63, 1, b, r), T.nb(t, bx, bz, 0, 1, b, r), T.nb(t, bx, bz, 1, 1, b, r)]

def T.cat(ns: List<&2, Nb>) -> List<&2, P.Body>:
  match ns:
    case []:
      []
    case Nb{bx, bz, xs} <> rest:
      List.append(&2, P.Body, xs, T.cat(rest))

def T.d2(+ev: List<&2, P.Body>, sp: Two) -> List<&2, P.Body>:
  Two{nw, old} = sp
  List.append(&2, P.Body, nw, O.changed(ev, old))

# the events after a task: its new ones, and those it changed
def T.delta(+ev: List<&2, P.Body>, +ev2: List<&2, P.Body>) -> List<&2, P.Body>:
  T.d2(ev, W.split(Nat.sub(List.length(&2, P.Body, ev2), List.length(&2, P.Body, ev)), ev2))

# is the player within a bucket of (bx, bz)?
def T.near(+p: P.Body, +bx: U32, +bz: U32) -> Bool:
  Bool.and((((T.key(P.Body.x(p)) - bx + 1 : U32) .&. 63 : U32) <= 2 : U32), (((T.key(P.Body.z(p)) - bz + 1 : U32) .&. 63 : U32) <= 2 : U32))

# the bucket a changed body came from (it is in one of the groups)
def T.kx(+c: P.Body, ns: List<&2, Nb>) -> U32:
  match ns:
    case []:
      0
    case Nb{+bx, bz, +xs} <> rest:
      Pick.u(O.has(c, xs), bx, T.kx(c, rest))

def T.kz(+c: P.Body, ns: List<&2, Nb>) -> U32:
  match ns:
    case []:
      0
    case Nb{bx, +bz, +xs} <> rest:
      Pick.u(O.has(c, xs), bz, T.kz(c, rest))

def T.kc(pl: Bool, +c: P.Body, +ns: List<&2, Nb>, rest: List<&2, Ch>) -> List<&2, Ch>:
  match pl:
    case True{}:
      rest
    case False{}:
      Ch{T.kx(c, ns), T.kz(c, ns), c} <> rest

def T.keyed(cs: List<&2, P.Body>, +ns: List<&2, Nb>, +p: P.Body) -> List<&2, Ch>:
  match cs:
    case []:
      []
    case +c <> rest:
      T.kc(W.same(c, p), c, ns, T.keyed(rest, ns, p))

def T.plch(cs: List<&2, P.Body>, +p: P.Body) -> List<&2, P.Body>:
  match cs:
    case []:
      []
    case +c <> rest:
      W.take_if(W.same(c, p), c, T.plch(rest, p))

def T.opt(c: Bool, +p: P.Body) -> List<&2, P.Body>:
  match c:
    case True{}:
      [p]
    case False{}:
      []

def T.t2(+ns: List<&2, Nb>, +p: P.Body, q: Sq4, +ev: List<&2, P.Body>) -> PR:
  Sq4{xs, +chg, ev2} = q
  PR{TL{xs}, T.keyed(chg, ns, p), T.delta(ev, ev2), T.plch(chg, p)}

# a bucket of the phase's color: its cubes' ticks, among the buckets around
# (and the player, if near)
# the constants, as a record of this task's own: one shared by every
# task is a reference count that every core bumps at every read
def T.kcopy(k: P.K) -> P.K:
  P.K{g, mu, j, acc, size} = k
  P.K{g, mu, j, acc, size}

# is the player (its bucket pk) within a bucket of (bx, bz)?
def T.nearp(+pkx: U32, +pkz: U32, +bx: U32, +bz: U32) -> Bool:
  Bool.and((((pkx - bx + 1 : U32) .&. 63 : U32) <= 2 : U32), (((pkz - bz + 1 : U32) .&. 63 : U32) <= 2 : U32))

def T.task2(+xs: List<&2, P.Body>, +bx: U32, +bz: U32, +all: Bt, +p: P.Body, +pn: Bool, +k: P.K, +seed: U32, +cells: Cells,
  +ev: List<&2, P.Body>) -> PR:
  +ns = T.nbs(all, bx, bz, O.box(xs), O.reach(xs, k, 0n))
  T.t2(ns, p, F.blk(k, seed, cells, xs, List.append(&2, P.Body, T.cat(ns), T.opt(pn, p)), ev), ev)

def T.task(on: Bool, +xs: List<&2, P.Body>, +bx: U32, +bz: U32, +all: Bt, +p: P.Body, +pkx: U32, +pkz: U32, +k: P.K,
  +seed: U32, +cells: Cells, +ev: List<&2, P.Body>) -> PR:
  match on:
    case False{}:
      PR{TL{xs}, [], [], []}
    case True{}:
      T.task2(xs, bx, bz, all, p, T.nearp(pkx, pkz, bx, bz), T.kcopy(k), seed, cells, ev)

def T.color(+bx: U32, +bz: U32, +c: Nat) -> Bool:
  U32.is_eq(((bx .&. 1) + (bz .&. 1) * 2 : U32), U32.from_nat(c))

def T.hix(+l: Nat, +bx: U32) -> U32:
  Pick.u(Nat.is_eq(Nat.mod(l, 2n), 0n), (bx .|. (1 << Nat.sub(Nat.div(l, 2n), 1n)) : U32), bx)

def T.hiz(+l: Nat, +bz: U32) -> U32:
  Pick.u(Nat.is_eq(Nat.mod(l, 2n), 1n), (bz .|. (1 << Nat.sub(Nat.div(Nat.add(l, 1n), 2n), 1n)) : U32), bz)

def T.pjoin(ra: PR, rb: PR) -> PR:
  PR{ta, ca, ea, pa} = ra
  PR{tb, cb, eb, pb} = rb
  PR{TN{ta, tb}, List.append(&2, Ch, ca, cb), List.append(&2, P.Body, ea, eb), List.append(&2, P.Body, pa, pb)}

# a phase over a subtree whose buckets' coordinates so far are (bx, bz):
# the two halves in parallel
def T.phase(l: Nat, par: Bool, t: Bt, +bx: U32, +bz: U32, +all: Bt, +c: Nat, +p: P.Body, +pkx: U32, +pkz: U32, +k: P.K,
  +seed: U32, +cells: Cells, +ev: List<&2, P.Body>) -> PR:
  match l par t:
    case _ _ TE{}:
      PR{TE{}, [], [], []}
    case _ _ TL{xs}:
      T.task(T.color(bx, bz, c), xs, bx, bz, all, p, pkx, pkz, k, seed, cells, ev)
    case 0n _ TN{lo, hi}:
      PR{TN{lo, hi}, [], [], []}
    case 1n++j True{} TN{lo, hi}:
      ra rb = T.phase(j, Nat.is_le(T.fork(), j), lo, bx, bz, all, c, p, pkx, pkz, k, seed, cells, ev) T.phase(j, Nat.is_le(T.fork(), j), hi, T.hix(Nat.add(j, 1n), bx), T.hiz(Nat.add(j, 1n), bz), all, c, p, pkx, pkz, k, seed, cells, ev)
      T.pjoin(ra, rb)
    case 1n++j False{} TN{lo, hi}:
      T.pjoin(T.phase(j, False{}, lo, bx, bz, all, c, p, pkx, pkz, k, seed, cells, ev),
        T.phase(j, False{}, hi, T.hix(Nat.add(j, 1n), bx), T.hiz(Nat.add(j, 1n), bz), all, c, p, pkx, pkz, k, seed, cells, ev))

def T.rp(l: Nat, t: Bt, s: Bool, +bx: U32, +bz: U32, +b: P.Body) -> Bt:
  match l t s:
    case _ TE{} _:
      TE{}
    case _ TL{xs} _:
      TL{Q.repl(b, xs)}
    case 0n TN{lo, hi} _:
      TN{lo, hi}
    case 1n++j TN{lo, hi} False{}:
      TN{T.rp(j, lo, T.side(j, bx, bz), bx, bz, b), hi}
    case 1n++j TN{lo, hi} True{}:
      TN{lo, T.rp(j, hi, T.side(j, bx, bz), bx, bz, b)}

# what the phase's cubes pushed of the buckets around, into them
def T.apply(cs: List<&2, Ch>, t: Bt) -> Bt:
  match cs:
    case []:
      t
    case Ch{+bx, +bz, +b} <> rest:
      T.apply(rest, T.rp(12n, t, T.side(12n, bx, bz), bx, bz, b))

def T.after(r: PR, +ev: List<&2, P.Body>, p: P.Body) -> Tk:
  PR{t, ch, dev, pl} = r
  Tk{T.apply(ch, t), Q.upsert(dev, ev), W.first(List.append(&2, P.Body, pl, [p]))}

def T.run(+c: Nat, tk: Tk, +k: P.K, +seed: U32, +cells: Cells) -> Tk:
  Tk{+t, +ev, +p} = tk
  T.after(T.phase(12n, True{}, t, 0, 0, t, c, p, T.key(P.Body.x(p)), T.key(P.Body.z(p)), k, seed, cells, ev), ev, p)

def W.cubes_by(few: Bool, +k: P.K, w: World) -> World:
  match few:
    case True{}:
      W.cubes_list(k, w)
    case False{}:
      W.cubes_oct(k, w)

# every awake cube's tick (no input), in order, each among the bodies
# within its reach (the player, the other awake ones) and the sleepers
# around; what they push wakes. A few cubes look at each other directly;
# many (from a hundred on), through the octree
def W.cubes_all(+k: P.K, w: World) -> World:
  World{seed, t, +awake, dirty, p} = w
  W.cubes_by(Nat.is_lt(List.length(&2, P.Body, awake), 128n), k, World{seed, t, awake, dirty, p})

# Sleep
# -----

# Many cubes, whole tick on the block tree
# ----------------------------------------
# The player among the 9 buckets around it, the 4 phases, the sleepers the
# cubes pushed woken, then which cubes rest decided bucket by bucket in
# parallel (their cells written after, one by one: they are few).

def T.chs(+bx: U32, +bz: U32, xs: List<&2, P.Body>) -> List<&2, Ch>:
  match xs:
    case []:
      []
    case b <> rest:
      Ch{bx, bz, b} <> T.chs(bx, bz, rest)

# what changed of the groups ns, pool being theirs in order after a tick
def T.regroup(ns: List<&2, Nb>, pool: List<&2, P.Body>) -> List<&2, Ch>:
  match ns:
    case []:
      []
    case Nb{+bx, +bz, +xs} <> rest:
      +sp = W.split(List.length(&2, P.Body, xs), pool)
      List.append(&2, Ch, T.chs(bx, bz, O.changed(xs, T.half_a(sp))), T.regroup(rest, T.half_b(sp)))

def T.nc2(xs: List<&2, P.Body>, +m: Nat, +p: P.Body) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +e <> rest:
      W.take_if(W.close(m, p, e), e, T.nc2(rest, m, p))

def T.nclose(ns: List<&2, Nb>, +m: Nat, +p: P.Body) -> List<&2, Nb>:
  match ns:
    case []:
      []
    case Nb{bx, bz, xs} <> rest:
      Nb{bx, bz, T.nc2(xs, m, p)} <> T.nclose(rest, m, p)

type Ps is Data:
  Ps{bt: Bt, t: Cells, dirty: List<&2, Cell>, p: P.Body}

def T.ps3(bt: Bt, p: P.Body, st: St) -> Ps:
  St{t, dirty, fresh, work} = st
  Ps{T.adds(fresh, bt), t, dirty, p}

def T.ps2(+seed: U32, +ns: List<&2, Nb>, bt: Bt, p: P.Body, sp: Two, t: Cells, dirty: List<&2, Cell>) -> Ps:
  Two{near, sl} = sp
  T.ps3(T.apply(T.regroup(ns, near), bt), p, W.wake(256n, seed, St{t, dirty, [], W.woken(sl)}))

def T.ps1(+seed: U32, +ns: List<&2, Nb>, +nn: Nat, bt: Bt, r: P.Body & List<&2, P.Body>, t: Cells, dirty: List<&2, Cell>) -> Ps:
  (p, obs) = r
  T.ps2(seed, ns, bt, p, W.split(nn, obs), t, dirty)

# the player's tick among the cubes of the 9 buckets around it within reach
def T.player(+k: P.K, inp: P.In, +seed: U32, +bt: Bt, +t: Cells, dirty: List<&2, Cell>, +p: P.Body) -> Ps:
  +bx = T.key(P.Body.x(p))
  +bz = T.key(P.Body.z(p))
  +ns = T.nclose(Nb{bx, bz, T.at(bt, bx, bz)} <> T.nbs(bt, bx, bz, Bx{0n, 0n, 0n, Nat.sub(O.big(), 1048576n), Nat.sub(O.big(), 1048576n), Nat.sub(O.big(), 1048576n)}, 0n),
    W.reach(k, p), p)
  +near = T.cat(ns)
  T.ps1(seed, ns, List.length(&2, P.Body, near), bt,
    P.Body.tick(k, List.append(&2, P.Body, near, W.around(k, t, seed, p)), inp, p), t, dirty)

# which cubes of a bucket rest (a), and the others (b)
def T.rests(xs: List<&2, P.Body>, +k: P.K, +t: Cells, +seed: U32) -> Two:
  match xs:
    case []:
      Two{[], []}
    case +c <> rest:
      W.near1(W.still(k, t, seed, c), c, T.rests(rest, k, t, seed))

type SR is Data:
  SR{bt: Bt, rest: List<&2, P.Body>}

def T.sr1(sp: Two) -> SR:
  Two{r, keep} = sp
  SR{TL{keep}, r}

def T.sjoin(a: SR, b: SR) -> SR:
  SR{ta, ra} = a
  SR{tb, rb} = b
  SR{TN{ta, tb}, List.append(&2, P.Body, ra, rb)}

def T.m4(+seed: U32, bt: Bt, p: P.Body, fresh: List<&2, P.Body>, s: Sl) -> World:
  Sl{t, dirty, keep} = s
  World{seed, t, List.append(&2, P.Body, fresh, List.append(&2, P.Body, keep, T.all(bt))), dirty, p}

# the cubes at rest out of the tree, block by block (in parallel down to
# the fork cutoff)
def T.sleep(t: Bt, +l: Nat, par: Bool, +k: P.K, +cells: Cells, +seed: U32) -> SR:
  match t par:
    case TE{} _:
      SR{TE{}, []}
    case TL{xs} _:
      T.sr1(T.rests(xs, k, cells, seed))
    case TN{lo, hi} True{}:
      a b = T.sleep(lo, Nat.sub(l, 1n), Nat.is_le(T.fork(), l), k, cells, seed) T.sleep(hi, Nat.sub(l, 1n), Nat.is_le(T.fork(), l), k, cells, seed)
      T.sjoin(a, b)
    case TN{lo, hi} False{}:
      T.sjoin(T.sleep(lo, Nat.sub(l, 1n), False{}, k, cells, seed), T.sleep(hi, Nat.sub(l, 1n), False{}, k, cells, seed))

def T.m3(+k: P.K, +seed: U32, p: P.Body, fresh: List<&2, P.Body>, sr: SR, t: Cells, dirty: List<&2, Cell>) -> World:
  SR{bt, rest} = sr
  T.m4(seed, bt, p, fresh, W.sleep(rest, k, seed, Sl{t, dirty, []}))

def T.m2b(+k: P.K, +seed: U32, bt: Bt, p: P.Body, st: St) -> World:
  St{+t, dirty, fresh, work} = st
  T.m3(k, seed, p, fresh, T.sleep(bt, 12n, True{}, k, t, seed), t, dirty)

def T.m2(+k: P.K, +seed: U32, tk: Tk, t: Cells, dirty: List<&2, Cell>) -> World:
  Tk{bt, +ev, p} = tk
  T.m2b(k, seed, bt, p, W.wake(Nat.add(1024n, Nat.mul(16n, List.length(&2, P.Body, ev))), seed, St{t, dirty, [], ev}))

def T.m1(+k: P.K, +seed: U32, ps: Ps) -> World:
  Ps{bt, +t, dirty, p} = ps
  T.m2(k, seed, T.run(3n, T.run(2n, T.run(1n, T.run(0n, Tk{bt, [], p}, k, seed, t), k, seed, t), k, seed, t), k, seed, t), t, dirty)

def W.tick_many(+k: P.K, inp: P.In, w: World) -> World:
  World{+seed, +t, awake, dirty, +p} = w
  T.m1(k, seed, T.player(k, inp, seed, T.radix(12n, awake), t, dirty, p))

def W.tick_few(+k: P.K, inp: P.In, w: World) -> World:
  W.sleep_all(k, W.cubes_all(k, W.player_step(k, inp, w)))

# many cubes on the block tree, unless something reaches a metre in a tick
# (the blocks' separation): then a tick of few, or through the octree
def W.tick_by(few: Bool, +k: P.K, inp: P.In, w: World) -> World:
  match few:
    case True{}:
      W.tick_few(k, inp, w)
    case False{}:
      W.tick_many(k, inp, w)

# the crowd cut in halves that tick at once, each on its own array
def W.tick_par(+k: P.K, inp: P.In, w: World) -> World:
  W.sleep_all(k, W.cubes_par(k, W.player_step(k, inp, w)))

def W.tick_dense(flat: Bool, few: Bool, +k: P.K, inp: P.In, w: World) -> World:
  match flat:
    case True{}:
      W.tick_flat(k, inp, w)
    case False{}:
      W.tick_by(few, k, inp, w)

# the flat array holds the cubes and the sleepers of the cells of their box,
# so it is the way when that box is not much wider than the crowd itself
# (the cells are counted only once both sides are small, to stay in a Nat)
# The crowd in chunks: the tick that uses more than one core
# ----------------------------------------------------------
# The crowd goes into a grid of chunks of 16 x 16 m, each chunk with its
# own array, and the chunks tick at the same time -- four colour rounds (a
# 2 x 2 chessboard), so that two chunks never push the same cube. The grid
# is built from the list every tick, exactly as the single array is; what
# the chunks buy is that each of them is a private array, which is what
# Bend can hand to another core (a shared list pays an atomic count).
#
# The player ticks first, alone, the way he always did. The sleepers under
# the crowd are lifted out of the trie so they tick with it (a chunk knows
# only its own array), and whatever came to rest is put back to sleep.

# the chunk levels for n cells: 2^lv chunks of 16 cells cover them
def W.lg3(fuel: Nat, ok: Bool, +n: Nat, +c: Nat, +lv: Nat) -> Nat:
  match fuel ok:
    case 0n _:
      lv
    case _ True{}:
      lv
    case 1n+f False{}:
      W.lg3(f, Nat.is_le(n, Nat.mul(2n, c)), n, Nat.mul(2n, c), Nat.add(lv, 1n))

def W.lg2(+n: Nat) -> Nat:
  W.lg3(24n, Nat.is_le(n, C.side()), n, C.side(), 0n)

# the bodies on each side of a line of cells (along x if onx, else z)
def C.cut1(lo: Bool, +b: P.Body, r: Two) -> Two:
  match lo:
    case True{}:
      Two{a, c} = r
      Two{b <> a, c}
    case False{}:
      Two{a, c} = r
      Two{a, b <> c}

def C.cut(xs: List<&2, P.Body>, +line: U32, +onx: Bool, acc: Two) -> Two:
  match xs:
    case []:
      acc
    case +e <> rest:
      C.cut1((W.cell_of(Pick.n(onx, P.Body.x(e), P.Body.z(e))) < line : U32), e, C.cut(rest, line, onx, acc))

# a chunk with this crowd and these sleepers, its 16 cells starting at
# (ox + 1, oz + 1): the crowd is marked 1 (it ticks and it is given back),
# the sleepers 2 (they are only there to be stood on and pushed). Room for
# three times what it starts with, for the copies of its neighbours.
def C.mkl2(+n1: Nat, +n2: Nat, xs: List<&2, P.Body>, ss: List<&2, P.Body>, +o: Og, +ox: U32, +oz: U32,
  r: U32 & Nat) -> Chk:
  (+cap, b) = r
  ChL{C.mark(n2, C.mark(n1, F.pack(ss, F.pack(xs, Array.new(U32, Nat.add(b, 6n), 0), 0, o, False{}),
      U32.from_nat(n1), o, True{}), 0, cap, 1), U32.from_nat(n1), cap, 2),
    U32.from_nat(Nat.add(n1, n2)), cap, ox, oz}

def C.mkl1(+n1: Nat, +n2: Nat, xs: List<&2, P.Body>, ss: List<&2, P.Body>, +o: Og, +ox: U32, +oz: U32) -> Chk:
  C.mkl2(n1, n2, xs, ss, o, ox, oz, F.cap0(U32.from_nat(Nat.add(Nat.mul(3n, Nat.add(n1, n2)), 64n))))

def C.mkl(+xs: List<&2, P.Body>, +ss: List<&2, P.Body>, +o: Og, +ox: U32, +oz: U32) -> Chk:
  C.mkl1(List.length(&2, P.Body, xs), List.length(&2, P.Body, ss), xs, ss, o, ox, oz)

# A part of the crowd waiting for its turn to be split: its bodies, its
# sleepers, the cell its chunks start at and how many levels are left.
type Job is Data:
  Job{xs: List<&2, P.Body>, ss: List<&2, P.Body>, cx: U32, cz: U32, lx: Nat, lz: Nat}

def C.jxs(j: Job) -> List<&2, P.Body>:
  Job{xs, ss, cx, cz, lx, lz} = j
  xs

def C.jss(j: Job) -> List<&2, P.Body>:
  Job{xs, ss, cx, cz, lx, lz} = j
  ss

def C.jcx(j: Job) -> U32:
  Job{xs, ss, cx, cz, lx, lz} = j
  cx

def C.jcz(j: Job) -> U32:
  Job{xs, ss, cx, cz, lx, lz} = j
  cz

def C.jlx(j: Job) -> Nat:
  Job{xs, ss, cx, cz, lx, lz} = j
  lx

def C.jlz(j: Job) -> Nat:
  Job{xs, ss, cx, cz, lx, lz} = j
  lz

def C.ta(t: Two) -> List<&2, P.Body>:
  Two{a, b} = t
  a

def C.tb(t: Two) -> List<&2, P.Body>:
  Two{a, b} = t
  b

# how many cells 2^m chunks span
def C.st(+m: Nat) -> U32:
  U32.from_nat(Nat.mul(C.side(), Nat.pow(2n, m)))

# what to do next: split by z while there are z levels left, then by x,
# and when there is only one chunk left, pack it
def C.nph(+nz: Nat, +nx: Nat) -> Nat:
  Pick.n(Nat.is_lt(0n, nz), 0n, Pick.n(Nat.is_lt(0n, nx), 3n, 4n))

# The crowd into chunks, halving: cut by z, keep the near half going and
# leave the far one on the pile, then the same by x, and pack what is
# left. One recursion (Bend has no mutual recursion), the phase says which
# step it is on: 0 and 5 cut by z (the crowd, then the sleepers), 1 takes
# the halves, 3 and 6 cut by x, 2 takes those halves, 4 packs a chunk.
def C.jobs(fuel: Nat, ph: Nat, todo: List<&2, Job>, +t: Two, +u: Two, +xs: List<&2, P.Body>,
  +ss: List<&2, P.Body>, +nz: Nat, +nx: Nat, +cx: U32, +cz: U32, +cx0: U32, +cz0: U32, acc: Rw, +o: Og) -> Rw:
  match fuel ph todo:
    case 0n _ _:
      acc
    case 1n+f 0n _:
      C.jobs(f, 5n, todo, C.cut(xs, (cz0 + cz + C.st(Nat.sub(nz, 1n)) : U32), False{}, Two{[], []}), u, [], ss,
        Nat.sub(nz, 1n), nx, cx, cz, cx0, cz0, acc, o)
    case 1n+f 5n _:
      C.jobs(f, 1n, todo, t, C.cut(ss, (cz0 + cz + C.st(nz) : U32), False{}, Two{[], []}), [], [],
        nz, nx, cx, cz, cx0, cz0, acc, o)
    case 1n+f 1n _:
      C.jobs(f, C.nph(nz, nx), Job{C.tb(t), C.tb(u), cx, (cz + C.st(nz) : U32), nx, nz} <> todo, Two{[], []},
        Two{[], []}, C.ta(t), C.ta(u), nz, nx, cx, cz, cx0, cz0, acc, o)
    case 1n+f 3n _:
      C.jobs(f, 6n, todo, C.cut(xs, (cx0 + cx + C.st(Nat.sub(nx, 1n)) : U32), True{}, Two{[], []}), u, [], ss,
        nz, Nat.sub(nx, 1n), cx, cz, cx0, cz0, acc, o)
    case 1n+f 6n _:
      C.jobs(f, 2n, todo, t, C.cut(ss, (cx0 + cx + C.st(nx) : U32), True{}, Two{[], []}), [], [],
        nz, nx, cx, cz, cx0, cz0, acc, o)
    case 1n+f 2n _:
      C.jobs(f, C.nph(nz, nx), Job{C.tb(t), C.tb(u), (cx + C.st(nx) : U32), cz, nx, nz} <> todo, Two{[], []},
        Two{[], []}, C.ta(t), C.ta(u), nz, nx, cx, cz, cx0, cz0, acc, o)
    case 1n+f 4n Nil{}:
      RwC{C.mkl(xs, ss, o, (cx - 1 : U32), (cz - 1 : U32)), acc}
    case 1n+f 4n +j <> rest:
      C.jobs(f, C.nph(C.jlz(j), C.jlx(j)), rest, Two{[], []}, Two{[], []}, C.jxs(j), C.jss(j), C.jlz(j),
        C.jlx(j), C.jcx(j), C.jcz(j), cx0, cz0,
        RwC{C.mkl(xs, ss, o, (cx - 1 : U32), (cz - 1 : U32)), acc}, o)
    case 1n+f _ _:
      acc

def C.mkgrid(+xs: List<&2, P.Body>, +ss: List<&2, P.Body>, +lx: Nat, +lz: Nat, +cx0: U32, +cz0: U32,
  +o: Og) -> Gr:
  C.rows0(C.rev(C.jobs(Nat.add(Nat.mul(16n, Nat.pow(2n, Nat.add(lx, lz))), 32n), C.nph(lz, lx), [],
    Two{[], []}, Two{[], []}, xs, ss, lz, lx, 0, 0, cx0, cz0, RwE{}, o), RwE{}),
    Nat.pow(2n, lx), Nat.pow(2n, lz))

# every chunk sorted by cell, without ticking: a chunk just built is in no
# order at all, and the border runs the handover reads come from the order
def C.fsort(t: Chk, +o: Og, +k: P.K, +mm: Nat) -> Chk:
  match t:
    case ChE{}:
      ChE{}
    case ChL{a, +n, +cap, +ox, +oz}:
      C.ft3(False{}, a, n, cap, ox, oz, o, k, mm)
    case ChN{lo, hi}:
      a b = C.fsort(lo, o, k, mm) C.fsort(hi, o, k, mm)
      ChN{a, b}

def C.rsort(r: Rw, +o: Og, +k: P.K, +mm: Nat) -> Rw:
  match r:
    case RwE{}:
      RwE{}
    case RwC{c, rest}:
      a b = C.fsort(c, o, k, mm) C.rsort(rest, o, k, mm)
      RwC{a, b}

def C.gsort(g: Gr, +o: Og, +k: P.K, +mm: Nat) -> Gr:
  match g:
    case GrE{}:
      GrE{}
    case GrC{r, rest}:
      a b = C.rsort(r, o, k, mm) C.gsort(rest, o, k, mm)
      GrC{a, b}

# the borders are handed over BEFORE the first round: a round ticks and
# then hands over, which is enough when the grid lives between ticks, but
# this one is built fresh every tick and would start with no copies of the
# neighbours at all -- and two cubes on opposite sides of a chunk line
# would not see each other
# the first tick of a grid just built: it is in no order at all yet, and
# the border runs the handover reads come from the order
def C.tickg0(g: Gr, +o: Og, +k: P.K, +mm: Nat, +lx: Nat, +lz: Nat) -> Gr:
  C.tick3(C.gzr2(C.gxr(C.gsort(g, o, k, mm), U32.from_nat(C.side()), 0n), U32.from_nat(C.side()), 0n), o, k, mm,
    U32.from_nat(C.side()), Nat.add(lx, lz), Nat.pow(2n, lx), Nat.pow(2n, lz))

# every tick after that: the chunks are already in order and already hold
# their neighbours' copies, so it is only the four rounds
def C.tickg(g: Gr, +o: Og, +k: P.K, +mm: Nat, +lx: Nat, +lz: Nat) -> Gr:
  C.tick3(g, o, k, mm, U32.from_nat(C.side()), Nat.add(lx, lz), Nat.pow(2n, lx), Nat.pow(2n, lz))

# the grid dropped: it is built again from the list every tick, and a
# chunk's array belongs to that chunk alone
def C.ckil(c: Chk, bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match c:
    case ChE{}:
      bs
    case ChL{a, n, cap, ox, oz}:
      bs
    case ChN{lo, hi}:
      C.ckil(lo, C.ckil(hi, bs))

def C.rkil(r: Rw, bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match r:
    case RwE{}:
      bs
    case RwC{c, rest}:
      C.rkil(rest, C.ckil(c, bs))

def C.gkil(g: Gr, bs: List<&2, P.Body>) -> List<&2, P.Body>:
  match g:
    case GrE{}:
      bs
    case GrC{r, rest}:
      C.gkil(rest, C.rkil(r, bs))

# is this the body standing exactly here? The player rides in the chunks
# as an obstacle, so this is how he is told apart from the sleepers when
# they come back: nothing else can be where he is (that would be an
# overlap), and an obstacle never moves -- only what pushed it changes.
def W.samep(+b: P.Body, +x: Nat, +y: Nat, +z: Nat) -> Bool:
  Bool.and(Nat.is_eq(P.Body.x(b), x), Bool.and(Nat.is_eq(P.Body.y(b), y), Nat.is_eq(P.Body.z(b), z)))

def W.pat(xs: List<&2, P.Body>, +x: Nat, +y: Nat, +z: Nat, acc: Two) -> Two:
  match xs:
    case []:
      acc
    case +e <> rest:
      C.cut1(W.samep(e, x, y, z), e, W.pat(rest, x, y, z, acc))

def W.head1(xs: List<&2, P.Body>, b: P.Body) -> P.Body:
  match xs:
    case []:
      b
    case +e <> rest:
      e

# the crowd back as a list, then the obstacles: the player (with whatever
# pushed him) and the sleepers that moved, which wake up -- exactly what
# the single array does
def W.cp7(r: Two, +k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, p: P.Body,
  bs: List<&2, P.Body>) -> World:
  Two{me, others} = r
  F.f3(k, seed, t, dirty, W.head1(me, p), bs, F.woken(others))

def W.cp6(r: Gr2, +k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, +p: P.Body,
  bs: List<&2, P.Body>) -> World:
  Gr2{g, sls} = r
  W.cp7(W.pat(C.gkil(g, sls), P.Body.x(p), P.Body.y(p), P.Body.z(p), Two{[], []}), k, seed, t, dirty, p, bs)

def W.cp5(r: Gr2, +k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, p: P.Body, +o: Og) -> World:
  Gr2{g, bs} = r
  W.cp6(C.gbodies(g, o, 2), k, seed, t, dirty, p, bs)

def W.cp4(+k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, p: P.Body, awake: List<&2, P.Body>,
  sl: List<&2, P.Body>, +mm: Nat, +o: Og, +cx0: U32, +cz0: U32, +lx: Nat, +lz: Nat) -> World:
  W.cp5(C.gbodies(C.tickg0(C.mkgrid(awake, sl, lx, lz, cx0, cz0, o), o, k, mm, lx, lz), o, 1),
    k, seed, t, dirty, p, o)

def W.cp2(+k: P.K, +seed: U32, +t: Cells, dirty: List<&2, Cell>, +p: P.Body, awake: List<&2, P.Body>,
  +bx: Bx, +mm: Nat) -> World:
  W.cp4(k, seed, t, dirty, p, awake,
    p <> W.rect(Nat.mul(F.gnx(bx, mm), F.gnz(bx, mm)), t, seed, F.cx0(bx, mm), F.cz0(bx, mm), F.gnx(bx, mm)),
    mm, F.org(bx, mm), F.cx0(bx, mm), F.cz0(bx, mm), W.lg2(F.gnx(bx, mm)), W.lg2(F.gnz(bx, mm)))

def W.cp1(+k: P.K, w: World) -> World:
  World{+seed, +t, +awake, dirty, +p} = w
  W.cp2(k, seed, t, dirty, p, awake, O.bb(awake, O.box([p])), F.mx(k, awake, W.reach(k, p)))

# the player first, alone, then the crowd in chunks, all at the same time
def W.tick_cpar(+k: P.K, inp: P.In, w: World) -> World:
  W.cp1(k, W.player_step(k, inp, w))

# The crowd's grid kept alive between ticks
# ----------------------------------------
# Building the grid out of the list costs more than the rounds do, so the
# grid is kept: it is built once and then ticks by itself, and only every
# few ticks does the crowd come back as a list (to sleep, to be drawn, to
# be handed to the player). The rebuild also re-centres the grid on the
# crowd, which is what keeps a cube from walking off its edge.

type Crowd is Type:
  CNil{}
  CGr{g: Gr, cx0: U32, cz0: U32, lx: Nat, lz: Nat, mm: Nat, left: Nat}

type Wc is Type:
  Wc{w: World, c: Crowd}

def W.ogof(+cx0: U32, +cz0: U32) -> Og:
  Og{W.base(cx0), W.base(cz0)}

# how many ticks a grid lives before the crowd comes back as a list
def W.cglife() -> Nat:
  32n

# the crowd out of the grid and back into the world, the sleepers that
# moved woken, the player taken out of the obstacles
def W.cgend(+k: P.K, w: World, g: Gr, +cx0: U32, +cz0: U32) -> Wc:
  World{+seed, +t, awake, dirty, +p} = w
  Wc{W.cp5(C.gbodies(g, W.ogof(cx0, cz0), 1), k, seed, t, dirty, p, W.ogof(cx0, cz0)), CNil{}}

def W.cg3(left: Nat, +k: P.K, w: World, g: Gr, +cx0: U32, +cz0: U32, +lx: Nat, +lz: Nat, +mm: Nat) -> Wc:
  match left:
    case 0n:
      W.cgend(k, w, g, cx0, cz0)
    case 1n+m:
      Wc{w, CGr{g, cx0, cz0, lx, lz, mm, m}}

# one tick of a grid that is already alive: the four colour rounds, and
# nothing else at all
def W.cg2(+k: P.K, w: World, g: Gr, +cx0: U32, +cz0: U32, +lx: Nat, +lz: Nat, +mm: Nat, +left: Nat) -> Wc:
  W.cg3(left, k, w, C.tickg(g, W.ogof(cx0, cz0), k, mm, lx, lz), cx0, cz0, lx, lz, mm)

# the grid built from the crowd: the cubes are its own, the sleepers under
# them and the player are obstacles (they are seen and pushed, they do not
# tick and they do not come back as cubes)
def W.cgb(+k: P.K, +seed: U32, t: Cells, dirty: List<&2, Cell>, p: P.Body, awake: List<&2, P.Body>,
  sl: List<&2, P.Body>, +cx0: U32, +cz0: U32, +lx: Nat, +lz: Nat, +mm: Nat) -> Wc:
  Wc{World{seed, t, [], dirty, p},
    CGr{C.tickg0(C.mkgrid(awake, sl, lx, lz, cx0, cz0, W.ogof(cx0, cz0)), W.ogof(cx0, cz0), k, mm, lx, lz),
      cx0, cz0, lx, lz, mm, W.cglife()}}

# The grid is built wider than the crowd: it has to hold every cube for as
# long as it lives, and a cube walks at most mm a tick. Without that
# margin a cube reaches the outer edge, where there is no neighbour to
# take it, its cell is clamped and it stops seeing who is next to it.
def W.cgmg(+mm: Nat) -> Nat:
  Nat.add(Nat.mul(mm, Nat.add(W.cglife(), 2n)), Nat.mul(2n, W.size()))

def W.cg1(+k: P.K, w: World, +bx: Bx, +mm: Nat) -> Wc:
  World{+seed, +t, +awake, dirty, +p} = w
  W.cgb(k, seed, t, dirty, p, awake,
    p <> W.rect(Nat.mul(F.gnx(bx, W.cgmg(mm)), F.gnz(bx, W.cgmg(mm))), t, seed, F.cx0(bx, W.cgmg(mm)),
      F.cz0(bx, W.cgmg(mm)), F.gnx(bx, W.cgmg(mm))),
    F.cx0(bx, W.cgmg(mm)), F.cz0(bx, W.cgmg(mm)), W.lg2(F.gnx(bx, W.cgmg(mm))), W.lg2(F.gnz(bx, W.cgmg(mm))),
    Nat.add(mm, 8192n))

def W.cgnew(+k: P.K, w: World) -> Wc:
  World{seed, t, +awake, dirty, +p} = w
  W.cg1(k, World{seed, t, awake, dirty, p}, O.bb(awake, O.box([p])), F.mx(k, awake, W.reach(k, p)))

# the crowd back into the world whatever state the grid is in: what the
# GPU, the HUD and anything else that needs the cubes as a list asks for
def W.cgw(r: Wc) -> World:
  Wc{w, c} = r
  w

def W.cgf2(+k: P.K, w: World, c: Crowd) -> World:
  match c:
    case CNil{}:
      w
    case CGr{g, +cx0, +cz0, lx, lz, mm, left}:
      W.cgw(W.cgend(k, w, g, cx0, cz0))

def W.cgflush(+k: P.K, r: Wc) -> World:
  Wc{w, c} = r
  W.cgf2(k, w, c)

# the crowd's tick with the grid kept alive: the player first, alone, then
# the chunks, all of them at the same time
def W.tick_cg(+k: P.K, inp: P.In, w: World, c: Crowd) -> Wc:
  match c:
    case CNil{}:
      W.cgnew(k, W.player_step(k, inp, w))
    case CGr{g, +cx0, +cz0, +lx, +lz, +mm, +left}:
      W.cg2(k, W.player_step(k, inp, w), g, cx0, cz0, lx, lz, mm, left)

def W.dense1(ok: Bool, +gx: Nat, +gz: Nat, +lim: Nat) -> Bool:
  match ok:
    case True{}:
      Nat.is_lt(Nat.mul(gx, gz), lim)
    case False{}:
      False{}

def W.dense(+bx: Bx, +n: Nat, +mm: Nat) -> Bool:
  +lim = Nat.mul(2n, Nat.add(n, 1n))
  +gx = F.gnx(bx, mm)
  +gz = F.gnz(bx, mm)
  W.dense1(Bool.and(Nat.is_lt(gx, lim), Nat.is_lt(gz, lim)), gx, gz, lim)

def W.tick2(+k: P.K, inp: P.In, +awake: List<&2, P.Body>, +p: P.Body, +n: Nat, +mm: Nat, w: World) -> World:
  W.tick_dense(W.dense(O.bb(awake, O.box([p])), n, mm), Bool.or(Nat.is_lt(n, 128n), Nat.is_lt(229376n, mm)), k, inp, w)

# a tick of the whole world
def W.tick(+k: P.K, inp: P.In, w: World) -> World:
  World{seed, t, +awake, dirty, +p} = w
  W.tick2(k, inp, awake, p, List.length(&2, P.Body, awake), F.mx(k, awake, W.reach(k, p)),
    World{seed, t, awake, dirty, p})

# a new world of seed, the player standing at the start
def W.new(+seed: U32) -> World:
  +o = W.base(W.origin())
  World{seed, CGen{}, [], [], W.cube(Nat.add(o, 131072n), 0n, Nat.add(o, 131072n))}
