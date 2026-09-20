# um cubo a 100 m/s contra uma parede parada: nao pode atravessar nem se
# sobrepor. A 100 m/s ele anda 0,78 m por tick, menos que um cubo, entao
# atravessar apareceria como sobreposicao.
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

# a parede: 5 x 5 cubos a 6 m do comeco
def wcube(+i: Nat, +j: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  W.W.cube(Nat.add(o, 1572864n), Nat.mul(j, 262144n), Nat.add(o, Nat.mul(Nat.add(i, 1n), 262144n)))

def wrow(+i: Nat, +n: Nat) -> List<&2, P.Body>:
  match n:
    case 0n:
      []
    case 1n+m:
      wcube(i, m) <> wrow(i, m)

def wall(+n: Nat) -> List<&2, P.Body>:
  match n:
    case 0n:
      []
    case 1n+m:
      List.append(&2, P.Body, wrow(m, 5n), wall(m))

# o veloz: 100 m/s para +x, na altura do meio da parede
def fast() -> P.Body:
  +o = W.W.base(W.W.origin())
  P.Body{o, 262144n, Nat.add(o, 786432n), P.Pos{102400n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}}

def wld() -> W.World:
  W.World{12345, W.CLeaf{[]}, fast() <> wall(5n), [], W.W.cube(Nat.sub(W.W.base(W.W.origin()), 5242880n), 0n,
    W.W.base(W.W.origin()))}

def awake(w: W.World) -> List<&2, P.Body>:
  W.World{seed, t, awake, dirty, p} = w
  awake

def maxx(xs: List<&2, P.Body>, +m: Nat) -> Nat:
  match xs:
    case []:
      m
    case +b <> rest:
      maxx(rest, Nat.max(m, P.Body.x(b)))

def run(n: Nat, +bad: Nat, +w: W.World) -> String:
  match n:
    case 0n:
      M.Pick.s(Nat.is_eq(bad, 0n), "OK", "FAIL") ++ ": " ++ Nat.show(bad) ++ " overlaps, "
        ++ Nat.show(List.length(&2, P.Body, awake(w))) ++ " cubos, o mais longe a "
        ++ M.Fmt.dec2(Nat.sub(maxx(awake(w), 0n), W.W.base(W.W.origin())), 262144n) ++ " m do inicio"
    case 1n+m:
      run(m, Nat.add(bad, clash(awake(w))), W.W.tick_flat(M.Knob.defaults(), P.In.idle(), w))

def main() -> IO(Unit):
  IO.print("veloz x parede: " ++ run(40n, 0n, wld()))
