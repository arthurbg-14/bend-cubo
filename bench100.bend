# Cubo -- 100 mil cubos de verdade, medidos: a multidao numa grade de
# chunks que fica viva entre os ticks, todos os chunks ticando ao mesmo
# tempo. Nada de conta: o programa monta os cubos, roda os ticks e diz
# quanto levou.
#
#   ./build.sh cem && ./cem

import Base
import ./phys.bend as P
import ./world.bend as W
import ./main.bend as M

# troca o tick pelo de medicao com TICKX

def k0() -> P.K:
  M.Knob.defaults()

# um cubo da multidao: 1,14 m de distancia do vizinho, caindo de uns
# 10 m de altura, para que todos os 100 mil estejam em movimento durante
# a medida inteira (de 10 m se cai 1,4 s, e a medida sao 0,5 s)
def one(+i: Nat, +j: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  P.Body{Nat.add(o, Nat.mul(Nat.add(i, 5n), 300000n)), Nat.mul(Nat.add(Nat.mod(Nat.add(i, j), 5n), 40n), 70000n),
    Nat.add(o, Nat.mul(j, 300000n)), P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}}

def row(+i: Nat, +j: Nat) -> List<&2, P.Body>:
  match j:
    case 0n:
      []
    case 1n+m:
      one(i, m) <> row(i, m)

def all(+i: Nat, +n: Nat) -> List<&2, P.Body>:
  match i:
    case 0n:
      []
    case 1n+m:
      List.append(&2, P.Body, row(m, n), all(m, n))

def wld(bs: List<&2, P.Body>) -> W.World:
  W.World{12345, W.CGen{}, bs, [], W.W.cube(W.W.base(W.W.origin()), 0n, W.W.base(W.W.origin()))}

def awake(+w: W.World) -> Nat:
  W.World{seed, t, awake, dirty, p} = w
  List.length(&2, P.Body, awake)

def tks(n: Nat, r: W.Wc) -> W.Wc:
  match n:
    case 0n:
      r
    case 1n+m:
      W.Wc{+w, c} = r
      tks(m, W.W.tick_cg(k0(), P.In.idle(), w, c))

def say(+t0: Nat, +t1: Nat, +n: Nat, +ticks: Nat, +left: Nat) -> String:
  Nat.show(n) ++ " cubos, " ++ Nat.show(ticks) ++ " ticks em " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms ("
    ++ M.Fmt.dec2(Nat.sub(t1, t0), ticks) ++ " ms a tick), " ++ Nat.show(left) ++ " acordados no fim"

def fin(+t0: Nat, +n: Nat, +ticks: Nat, +w: W.World) -> IO(Unit):
  do IO<Unit>:
    t1 : Nat <- IO.now()
    IO.print(say(t0, t1, n, ticks, awake(w)))

def run(+n: Nat, +ticks: Nat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    fin(t0, Nat.mul(n, n), ticks, W.W.cgflush(k0(), tks(ticks, W.Wc{wld(all(n, n)), W.CNil{}})))

def main() -> IO(Unit):
  do IO<Unit>:
    a : Unit <- IO.print("montando a multidao...")
    run(320n, 64n)
