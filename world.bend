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

def W.reachz(+k: P.K, +vx: P.Z, +vy: P.Z, +vz: P.Z) -> Nat:
  P.K{+g, mu, jump, +acc, +air, vmax, size} = k
  Nat.add(Nat.mul(2n, Nat.add(Nat.add(P.Z.mag(vx), P.Z.mag(vy)), P.Z.mag(vz))),
    Nat.add(Nat.mul(2n, Nat.add(Nat.add(acc, air), g)), 65536n))

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
      W.near_of(xs, W.reach(k, c), c)

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
      +m = W.reach(k, c)
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
      +m = W.reachz(k, vx, vy, vz)
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

def T.key(+x: Nat) -> U32:
  (W.blk(x) .&. 63 : U32)

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

# the tree at level l of the cubes p, already split by the level's bit:
# each half split by the next bit and built, both in parallel (a radix
# partition: no inserts, no merges; the split is handed down, not shared)
def T.rad(l: Nat, p: Two) -> Bt:
  match l p:
    case _ Two{Nil{}, Nil{}}:
      TE{}
    case 0n Two{lo, hi}:
      TL{List.append(&2, P.Body, lo, hi)}
    case 1n++j Two{lo, hi}:
      a b = T.rad(j, T.part(lo, j)) T.rad(j, T.part(hi, j))
      TN{a, b}

def T.radix(+l: Nat, xs: List<&2, P.Body>) -> Bt:
  T.rad(l, T.part(xs, l))

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
def T.task(on: Bool, +xs: List<&2, P.Body>, +bx: U32, +bz: U32, +all: Bt, +p: P.Body, +k: P.K, +seed: U32, +cells: Cells,
  +ev: List<&2, P.Body>) -> PR:
  match on:
    case False{}:
      PR{TL{xs}, [], [], []}
    case True{}:
      +ns = T.nbs(all, bx, bz, O.box(xs), O.reach(xs, k, 0n))
      T.t2(ns, p, Q.cseq(k, seed, cells, xs, List.append(&2, P.Body, T.cat(ns), T.opt(T.near(p, bx, bz), p)), ev), ev)

def T.color(+bx: U32, +bz: U32, +c: Nat) -> Bool:
  U32.is_eq(((bx .&. 1) + (bz .&. 1) * 2 : U32), U32.from_nat(c))

# the bucket coordinates of the upper half at level l: x's bit l/2 - 1 set
# at an even level, z's bit (l + 1)/2 - 1 at an odd one
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
def T.phase(l: Nat, t: Bt, +bx: U32, +bz: U32, +all: Bt, +c: Nat, +p: P.Body, +k: P.K, +seed: U32, +cells: Cells,
  +ev: List<&2, P.Body>) -> PR:
  match l t:
    case _ TE{}:
      PR{TE{}, [], [], []}
    case _ TL{xs}:
      T.task(T.color(bx, bz, c), xs, bx, bz, all, p, k, seed, cells, ev)
    case 0n TN{lo, hi}:
      PR{TN{lo, hi}, [], [], []}
    case 1n++j TN{lo, hi}:
      ra rb = T.phase(j, lo, bx, bz, all, c, p, k, seed, cells, ev) T.phase(j, hi, T.hix(Nat.add(j, 1n), bx), T.hiz(Nat.add(j, 1n), bz), all, c, p, k, seed, cells, ev)
      T.pjoin(ra, rb)

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
  T.after(T.phase(12n, t, 0, 0, t, c, p, k, seed, cells, ev), ev, p)

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

# the cubes at rest out of the tree, bucket by bucket in parallel
def T.sleep(t: Bt, +k: P.K, +cells: Cells, +seed: U32) -> SR:
  match t:
    case TE{}:
      SR{TE{}, []}
    case TL{xs}:
      T.sr1(T.rests(xs, k, cells, seed))
    case TN{lo, hi}:
      a b = T.sleep(lo, k, cells, seed) T.sleep(hi, k, cells, seed)
      T.sjoin(a, b)

def T.m4(+seed: U32, bt: Bt, p: P.Body, fresh: List<&2, P.Body>, s: Sl) -> World:
  Sl{t, dirty, keep} = s
  World{seed, t, List.append(&2, P.Body, fresh, List.append(&2, P.Body, keep, T.all(bt))), dirty, p}

def T.m3(+k: P.K, +seed: U32, p: P.Body, fresh: List<&2, P.Body>, sr: SR, t: Cells, dirty: List<&2, Cell>) -> World:
  SR{bt, rest} = sr
  T.m4(seed, bt, p, fresh, W.sleep(rest, k, seed, Sl{t, dirty, []}))

def T.m2b(+k: P.K, +seed: U32, bt: Bt, p: P.Body, st: St) -> World:
  St{+t, dirty, fresh, work} = st
  T.m3(k, seed, p, fresh, T.sleep(bt, k, t, seed), t, dirty)

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

# a tick of the whole world
def W.tick(+k: P.K, inp: P.In, w: World) -> World:
  World{seed, t, +awake, dirty, p} = w
  W.tick_by(Bool.or(Nat.is_lt(List.length(&2, P.Body, awake), 128n), Nat.is_lt(229376n, O.reach(awake, k, 0n))), k, inp,
    World{seed, t, awake, dirty, p})

# a new world of seed, the player standing at the start
def W.new(+seed: U32) -> World:
  +o = W.base(W.origin())
  World{seed, CGen{}, [], [], W.cube(Nat.add(o, 131072n), 0n, Nat.add(o, 131072n))}
