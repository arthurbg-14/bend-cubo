# Cubo -- the collision test: 432 cubes in columns of 3 fall on each
# other, the top ones sliding sideways into their neighbours, among the
# world's cubes. For 300 ticks, five ways (the list of few cubes, the
# octree, the colored blocks, the flat array, the cut halves, and the game's
# mix), it checks after every tick that no two cubes overlap (awake, asleep, the player) and, at the end,
# that no cube was made or lost.
#
#   ./build.sh test

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

# every body in the region: awake, player, sleepers of its cells
def region(w: W.World) -> List<&2, P.Body>:
  W.World{seed, +t, awake, dirty, p} = w
  +c0 = (W.W.origin() - 10 : U32)
  p <> List.append(&2, P.Body, awake, W.W.rect(1600n, t, seed, c0, c0, 40n))

def sgn(c: Bool, +v: Nat) -> P.Z:
  match c:
    case True{}:
      P.Pos{v}
    case False{}:
      P.Neg{v}

def cells(w: W.World) -> W.Cells:
  W.World{seed, t, awake, dirty, p} = w
  t

def awk(w: W.World) -> List<&2, P.Body>:
  W.World{seed, t, awake, dirty, p} = w
  awake

def body(+i: Nat, +j: Nat, +l: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  +x = Nat.add(Nat.add(o, 786432n), Nat.mul(i, 275251n))
  +z = Nat.add(Nat.sub(o, 1572864n), Nat.mul(j, 275251n))
  +y = Nat.add(Nat.mul(Nat.add(l, 1n), 340000n), Nat.mul(Nat.mod(Nat.add(i, j), 3n), 26000n))
  +v = M.Pick.n(Nat.is_eq(l, 2n), Nat.mul(Nat.mod(i, 3n), 2048n), 0n)
  P.Body{x, y, z, sgn(Nat.is_eq(Nat.mod(j, 2n), 0n), v), P.Pos{0n}, P.Pos{0n}, False{}, False{}}

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

def grid(i: Nat) -> List<&2, P.Body>:
  match i:
    case 0n:
      []
    case 1n++m:
      List.append(&2, P.Body, row(m, 12n), grid(m))

# drop the ones placed inside a generated cube
def clean(xs: List<&2, P.Body>, +w: W.World) -> List<&2, P.Body>:
  match xs:
    case []:
      []
    case +b <> rest:
      W.W.take_if(P.Geo.free(W.W.size(), P.Body.x(b), P.Body.y(b), P.Body.z(b), W.W.around(M.Knob.defaults(), cells(w), 12345, b)), b,
        clean(rest, w))

def start2(+w: W.World) -> W.World:
  W.World{seed, t, awake, dirty, p} = w
  W.World{seed, t, clean(grid(12n), w), dirty, p}

def start() -> W.World:
  start2(W.W.new(12345))

def tick(v: Nat, +w: W.World) -> W.World:
  match v:
    case 0n:
      W.W.sleep_all(M.Knob.defaults(), W.W.cubes_list(M.Knob.defaults(), W.W.player_step(M.Knob.defaults(), P.In.idle(), w)))
    case 1n:
      W.W.sleep_all(M.Knob.defaults(), W.W.cubes_oct(M.Knob.defaults(), W.W.player_step(M.Knob.defaults(), P.In.idle(), w)))
    case 2n:
      W.W.tick_many(M.Knob.defaults(), P.In.idle(), w)
    case 3n:
      W.W.tick_flat(M.Knob.defaults(), P.In.idle(), w)
    case 4n:
      W.W.tick_par(M.Knob.defaults(), P.In.idle(), w)
    case 5n:
      W.W.tick_fpar(M.Knob.defaults(), P.In.idle(), w)
    case 6n:
      W.W.tick_cpar(M.Knob.defaults(), P.In.idle(), w)
    case _:
      W.W.tick(M.Knob.defaults(), P.In.idle(), w)

# n0 = the cubes the scene started with: the count is taken from the world
# the test was handed, not written down here, so changing the generator
# (the runway, say) cannot turn conservation into a false alarm
def run(n: Nat, +v: Nat, +bad: Nat, +w: W.World, +i: Nat, +n0: Nat) -> String:
  match n:
    case 0n:
      M.Pick.s(Bool.and(Nat.is_eq(bad, 0n), Nat.is_eq(List.length(&2, P.Body, region(w)), n0)), "OK", "FAIL") ++ ": " ++ Nat.show(i) ++ " ticks, "
        ++ Nat.show(bad) ++ " overlaps, " ++ Nat.show(List.length(&2, P.Body, region(w))) ++ " cubes (" ++ Nat.show(n0) ++ " at the start), "
        ++ Nat.show(List.length(&2, P.Body, awk(w))) ++ " awake"
    case 1n+m:
      +w2 = tick(v, w)
      run(m, v, Nat.add(bad, clash(region(w2))), w2, Nat.add(i, 1n), n0)

def main2(+w: W.World) -> IO(Unit):
  +n0 = List.length(&2, P.Body, region(w))
  do IO<Unit>:
    a : Unit <- IO.print("start: " ++ Nat.show(List.length(&2, P.Body, region(w))) ++ " cubes, "
      ++ Nat.show(List.length(&2, P.Body, awk(w))) ++ " awake, " ++ Nat.show(clash(region(w))) ++ " overlaps")
    b : Unit <- IO.print("list:   " ++ run(300n, 0n, 0n, w, 0n, n0))
    c : Unit <- IO.print("octree: " ++ run(300n, 1n, 0n, w, 0n, n0))
    d : Unit <- IO.print("blocks: " ++ run(300n, 2n, 0n, w, 0n, n0))
    e : Unit <- IO.print("flat:   " ++ run(300n, 3n, 0n, w, 0n, n0))
    f : Unit <- IO.print("par:    " ++ run(300n, 4n, 0n, w, 0n, n0))
    g : Unit <- IO.print("blocos: " ++ run(300n, 5n, 0n, w, 0n, n0))
    h : Unit <- IO.print("chunks: " ++ run(300n, 6n, 0n, w, 0n, n0))
    IO.print("game:   " ++ run(300n, 7n, 0n, w, 0n, n0))

def main() -> IO(Unit):
  main2(start())

