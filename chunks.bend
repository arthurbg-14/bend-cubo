# Cubo -- the collision test of the crowd in chunks: the same 432 cubes as
# clash.bend (columns of three falling on each other, the top ones sliding
# sideways), but held in a grid of chunks that tick at the same time. For
# 300 ticks it checks that no two cubes overlap and that none was made or
# lost.
#
#   ./build.sh chunks

import Base
import ./phys.bend as P
import ./world.bend as W
import ./main.bend as M

def meets(+a: P.Body, xs: List<&2, P.Body>) -> Nat:
  match xs:
    case []:
      0n
    case +b <> rest:
      Nat.add(M.Pick.n(P.Geo.meets(W.W.size(), P.Body.x(a), P.Body.y(a), P.Body.z(a), b), 1n, 0n), meets(a, rest))

def clash(xs: List<&2, P.Body>) -> Nat:
  match xs:
    case []:
      0n
    case +a <> +rest:
      Nat.add(meets(a, rest), clash(rest))

def sgn(c: Bool, +v: Nat) -> P.Z:
  match c:
    case True{}:
      P.Pos{v}
    case False{}:
      P.Neg{v}

# cada cubo entra girando de um jeito: o giro tem que atravessar a
# ordenacao, a troca entre chunks e o sono sem mudar
def spin(+i: Nat, +j: Nat, +l: Nat) -> P.Rot:
  P.Rot{Nat.mod(Nat.add(Nat.add(i, j), l), 3n), U32.from_nat(Nat.add(Nat.mul(i, 977n), Nat.mul(j, 13n))),
    P.Pos{Nat.add(Nat.mul(l, 100n), i)}}

def body(+i: Nat, +j: Nat, +l: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  +x = Nat.add(Nat.add(o, 786432n), Nat.mul(i, 275251n))
  +z = Nat.add(Nat.add(o, 786432n), Nat.mul(j, 275251n))
  +y = Nat.add(Nat.mul(Nat.add(l, 1n), 340000n), Nat.mul(Nat.mod(Nat.add(i, j), 3n), 26000n))
  +v = M.Pick.n(Nat.is_eq(l, 2n), Nat.mul(Nat.mod(i, 3n), 2048n), 0n)
  P.Body{x, y, z, sgn(Nat.is_eq(Nat.mod(j, 2n), 0n), v), P.Pos{0n}, P.Pos{0n}, False{}, False{}, spin(i, j, l)}

def col(+i: Nat, +j: Nat, l: Nat) -> List<&2, P.Body>:
  match l:
    case 0n:
      []
    case 1n++m:
      body(i, j, m) <> col(i, j, m)

def row(+i: Nat, j: Nat) -> List<&2, P.Body>:
  match j:
    case 0n:
      []
    case 1n++m:
      List.append(&2, P.Body, col(i, m, 3n), row(i, m))

def scene(i: Nat) -> List<&2, P.Body>:
  match i:
    case 0n:
      []
    case 1n++m:
      List.append(&2, P.Body, row(m, 12n), scene(m))

# the array's origin, and the first own cell of chunk (bx, bz)
# the array's origin: one cell below the first chunk's first cell, so the
# first chunk is number zero of the grid
def oar() -> W.Og:
  +o = W.W.base((W.W.origin() - 33 : U32))
  W.Og{o, o}

def first(+b: Nat) -> U32:
  (W.W.origin() - 32 + U32.from_nat(Nat.mul(b, 16n)) : U32)

# the bodies whose cell is inside chunk (bx, bz)
def mine(xs: List<&2, P.Body>, +bx: Nat, +bz: Nat) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +b <> rest:
      W.W.take_if(Bool.and(((W.W.cell_of(P.Body.x(b)) - first(bx)) < 16 : U32),
        ((W.W.cell_of(P.Body.z(b)) - first(bz)) < 16 : U32)), b, mine(rest, bx, bz))

def chunk(+bx: Nat, +bz: Nat, +xs: List<&2, P.Body>, +n: Nat, r: U32 & Nat) -> W.Chk:
  (+cap, b) = r
  W.ChL{W.C.mark(n, W.F.pack(xs, Array.new(U32, Nat.add(b, 6n), 0), 0, oar(), True{}), 0, cap, 1),
    U32.from_nat(n), cap, (first(bx) - 1 - (W.W.origin() - 32) : U32),
    (first(bz) - 1 - (W.W.origin() - 32) : U32)}

def mk2(+bx: Nat, +bz: Nat, +ys: List<&2, P.Body>) -> W.Chk:
  chunk(bx, bz, ys, List.length(&2, P.Body, ys),
    W.F.cap0(U32.from_nat(Nat.add(Nat.mul(3n, List.length(&2, P.Body, ys)), 64n))))

def mk(+bx: Nat, +bz: Nat, +xs: List<&2, P.Body>) -> W.Chk:
  mk2(bx, bz, mine(xs, bx, bz))

# the rows go left to right and the grid top to bottom: the handover
# takes the chunk next in the list as the one to the right (or below)
def line(+i: Nat, +n: Nat, +bz: Nat, +xs: List<&2, P.Body>) -> W.Rw:
  match i:
    case 0n:
      W.RwE{}
    case 1n++m:
      W.RwC{mk(Nat.sub(n, i), bz, xs), line(m, n, bz, xs)}

def grid(+j: Nat, +n: Nat, +xs: List<&2, P.Body>) -> W.Gr:
  match j:
    case 0n:
      W.GrE{}
    case 1n++m:
      W.GrC{line(n, n, Nat.sub(n, j), xs), grid(m, n, xs)}

def ticks(t: Nat, g: W.Gr) -> W.Gr:
  match t:
    case 0n:
      g
    case 1n+m:
      ticks(m, W.C.tick3(g, oar(), M.Knob.defaults(), 32768n, 16, 6n, 6n, 6n))

def spins(xs: List<&2, P.Body>, +s: Nat) -> Nat:
  match xs:
    case []:
      s
    case +b <> rest:
      spins(rest, Nat.add(s, Nat.add(Nat.add(P.Z.pos(P.Rot.w(P.Body.rot(b))), P.Z.neg(P.Rot.w(P.Body.rot(b)))),
        Nat.mul(P.Rot.ax(P.Body.rot(b)), 1000000n))))

def out(+bs: List<&2, P.Body>) -> IO(Unit):
  IO.print("chunks: " ++ Nat.show(clash(bs)) ++ " overlaps, " ++ Nat.show(List.length(&2, P.Body, bs))
    ++ " cubes (432 at the start)")

def fin(r: W.Gr2) -> IO(Unit):
  W.Gr2{g, bs} = r
  out(bs)

def gyr(r: W.Gr2) -> IO(Unit):
  W.Gr2{g, +bs} = r
  IO.print("giro: soma " ++ Nat.show(spins(bs, 0n)) ++ " (tem que bater com a do inicio)")

def fin2(r: W.Gr2) -> IO(Unit):
  W.Gr2{g, +bs} = r
  IO.print("no inicio: " ++ Nat.show(List.length(&2, P.Body, bs)) ++ " cubos, " ++ Nat.show(clash(bs))
    ++ " overlaps")

def start() -> IO(Unit):
  fin2(W.C.gbodies(grid(6n, 6n, scene(12n)), oar(), 1))

def start2() -> IO(Unit):
  gyr(W.C.gbodies(grid(6n, 6n, scene(12n)), oar(), 1))

# The second test: the world's own tick with the grid kept alive
# (W.tick_cg), on a crowd wide enough to have chunks in BOTH directions --
# 4096 cubes over 73 m are 8 x 8 chunks, so the handover along z (between
# rows of chunks) is exercised, which two chunks side by side never do.
def one(+i: Nat, +j: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  P.Body{Nat.add(o, Nat.mul(Nat.add(i, 5n), 300000n)), Nat.mul(Nat.add(Nat.mod(Nat.add(i, j), 5n), 12n), 70000n),
    Nat.add(o, Nat.mul(j, 300000n)), P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}, P.Rot.rest()}

def wrow(+i: Nat, +j: Nat) -> List<&2, P.Body>:
  match j:
    case 0n:
      []
    case 1n+m:
      one(i, m) <> wrow(i, m)

def wall(+i: Nat, +n: Nat) -> List<&2, P.Body>:
  match i:
    case 0n:
      []
    case 1n+m:
      List.append(&2, P.Body, wrow(m, n), wall(m, n))

def wld(bs: List<&2, P.Body>) -> W.World:
  W.World{12345, W.CGen{}, bs, [], W.W.cube(W.W.base(W.W.origin()), 0n, W.W.base(W.W.origin()))}

def wticks(n: Nat, r: W.Wc) -> W.Wc:
  match n:
    case 0n:
      r
    case 1n+m:
      W.Wc{w, c} = r
      wticks(m, W.W.tick_cg(M.Knob.defaults(), P.In.idle(), w, c))

# every cube of the region: the ones still moving and the ones that
# landed and went to sleep in the cells
def wbodies(w: W.World) -> List<&2, P.Body>:
  W.World{+seed, +t, awake, dirty, p} = w
  +c0 = (W.W.origin() - 5 : U32)
  List.append(&2, P.Body, awake, W.W.rect(8100n, t, seed, c0, c0, 90n))

def wfin(+n0: Nat, +w: W.World) -> IO(Unit):
  IO.print("grade viva: " ++ Nat.show(clash(wbodies(w))) ++ " overlaps, "
    ++ Nat.show(List.length(&2, P.Body, wbodies(w))) ++ " cubos (" ++ Nat.show(n0)
    ++ " no inicio, 4096 deles caindo em 8 x 8 chunks)")

def wtest2(+n0: Nat) -> IO(Unit):
  wfin(n0, W.W.cgflush(M.Knob.defaults(), wticks(80n, W.Wc{wld(wall(64n, 64n)), W.CNil{}})))

def wtest() -> IO(Unit):
  wtest2(List.length(&2, P.Body, wbodies(wld(wall(64n, 64n)))))

# the same scene held in a balanced tree of 8 x 8 chunks, ticked through
# the messages (the faster of the two ways to hand cubes over)
def main() -> IO(Unit):
  do IO<Unit>:
    a : Unit <- start()
    a2 : Unit <- start2()
    b : Unit <- fin(W.C.gbodies(ticks(300n, grid(6n, 6n, scene(12n))), oar(), 1))
    b2 : Unit <- gyr(W.C.gbodies(ticks(300n, grid(6n, 6n, scene(12n))), oar(), 1))
    wtest()
