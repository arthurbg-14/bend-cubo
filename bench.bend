# Cubo -- the headless benchmark: the simulation's cost, measured.
#
#   ./build.sh bench && ./bench
#
# walk:  the player walking east for 20 s of game time (2560 ticks),
#        pushing what it meets, on the world of seed 12345
# rain:  64 cubes dropped from 2 to 9 m over a 8 x 8 patch, all awake,
#        until they rest: every one ticks among the others and the
#        sleepers around
# frame: the frame's header written 1000 times (the HUD, the bodies)

import Base
import ./phys.bend as P
import ./world.bend as W
import ./main.bend as M

def k0() -> P.K:
  M.Knob.defaults()

def east() -> P.In:
  P.In{Some{P.Wish{P.Pos{4096n}, P.Pos{0n}}}, False{}}

def ticks(n: Nat, +inp: P.In, w: W.World) -> W.World:
  match n:
    case 0n:
      w
    case 1n+m:
      ticks(m, inp, W.W.tick(k0(), inp, w))

def awake(w: W.World) -> Nat:
  W.World{seed, t, awake, dirty, p} = w
  List.length(&2, P.Body, awake)

# a cube falling at (i, j) of the patch, 3 m east of the start, from
# 2 m up, a metre and a bit apart in height by its place
def drop(+i: Nat, +j: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  P.Body{Nat.add(o, Nat.mul(Nat.add(i, 5n), 300000n)), Nat.mul(Nat.add(Nat.add(i, j), 8n), 70000n),
    Nat.add(o, Nat.mul(j, 300000n)), P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}}

def rain.row(+i: Nat, +j: Nat) -> List<&2, P.Body>:
  match j:
    case 0n:
      []
    case 1n+m:
      drop(i, m) <> rain.row(i, m)

def rain.all(+i: Nat) -> List<&2, P.Body>:
  match i:
    case 0n:
      []
    case 1n+m:
      List.append(&2, P.Body, rain.row(m, 8n), rain.all(m))

def rain(w: W.World) -> W.World:
  W.World{seed, t, awake, dirty, p} = w
  W.World{seed, t, rain.all(8n), dirty, p}

def frames.next(r: M.Play & Array<U32>) -> M.Play & Array<U32>:
  (+s, hdr) = r
  M.Play.view(s, 1000n, hdr)

def frames.hdr(r: M.Play & Array<U32>) -> Array<U32>:
  (s, hdr) = r
  hdr

def frames(n: Nat, r: M.Play & Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      frames.hdr(r)
    case 1n+m:
      frames(m, frames.next(r))

def sum.snd(r: Array<U32> & U32) -> U32:
  (a2, v) = r
  v

def sum(a: Array<U32>) -> U32:
  sum.snd(Array.get(U32, a, 1056))

def ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a)) ++ " ms"

def bench.frames(+t5: Nat) -> IO(Unit):
  do IO<Unit>:
    h : Array<U32> = frames(1000n, (M.Play.start(1000n), Array.new(U32, 13n, 0)))
    t6 : Nat <- IO.now()
    IO.print("frame: 1000 headers in " ++ ms(t5, t6) ++ " (" ++ U32.show(sum(h)) ++ ")")

def bench.rain3(+t3: Nat, +w4: W.World) -> IO(Unit):
  do IO<Unit>:
    t4 : Nat <- IO.now()
    IO.print("rain: next 512 ticks in " ++ ms(t3, t4) ++ ", awake after " ++ Nat.show(awake(w4)))
    t5 : Nat <- IO.now()
    bench.frames(t5)

def bench.rain2(+t2: Nat, +w3: W.World) -> IO(Unit):
  do IO<Unit>:
    t3 : Nat <- IO.now()
    IO.print("rain: 64 awake, first 128 ticks in " ++ ms(t2, t3) ++ ", awake after " ++ Nat.show(awake(w3)))
    t3b : Nat <- IO.now()
    bench.rain3(t3b, ticks(512n, P.In.idle(), w3))

def bench.rain() -> IO(Unit):
  do IO<Unit>:
    t2 : Nat <- IO.now()
    bench.rain2(t2, ticks(128n, P.In.idle(), rain(W.W.new(12345))))

def bench.walk(+t0: Nat, +w1: W.World) -> IO(Unit):
  do IO<Unit>:
    t1 : Nat <- IO.now()
    IO.print("walk: 2560 ticks in " ++ ms(t0, t1) ++ ", awake at the end " ++ Nat.show(awake(w1)))
    bench.rain()

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    bench.walk(t0, ticks(2560n, east(), W.W.new(12345)))
